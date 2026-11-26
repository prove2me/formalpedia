-- Prove2me | solution 1 for RHHeight1000.rs_main_0313_0324
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:16:57.26781+00:00
-- url     : https://prove2.me/submissions/862ef3d4-ec77-45e6-998c-f4b17ce6c547

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

noncomputable def RS313to324.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS313to324.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS313to324.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS313to324.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS313to324.d2 a b h 

theorem RS313to324.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS313to324.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS313to324.d3 a b h)) 

noncomputable def Ns312p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns312p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns312p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns312p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns312p0 Ns312p1 Ns312p2 Ns312p1 307286088 268435456 1 70560000 307286088 268435456 1 70560000 153643044 134217728 2 134217728 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns312p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns312p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns312p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns312p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns312p8 := nat_lit 167537954069964697925743468333314178468718661948561187618563575975392713740913527107727581163208035826476740967700482432525301063254420572874757592895482956004842597348203117269212172556829666669574421653274845612596416189641484794702002223261246862056663160605878293700340502480877986491439034432953223334258717026053687371824342493299510132312376251152844516906794910572262907940062760396663270105627554083664899640691826599584783763757814813433640133591539937449421955686657622469485188711283992428713614179785896055117030632677201478317872225272595773536303110412989181984739022579128493081560758017763072115692678596043664844667144619713966763611484179303468167142547433165016751768184247559143333542643815355903304572487929375 

noncomputable def Ns312p9 := nat_lit 17907736863639440849562382641391758203535690054199171304015283257442503423240620144819838407313611418261944516207295868563739563278604805791797182761045687776939279949642059267526948014748996956777332184087524644234759874591635243045607722412471722018588244283882362848653445974523544951031470230725674276297342086185092985546835544820091590454230569790847977790484558207349923322458845585052164126500435851662252152223728079705692133047658564669873831757357628115566356048471439549797170528303905720944834637690907185213991407615774042056720704508980680095051114888612186461088301140868302968264130481206655302741383410655080008578156649725227045954510069588220729495895148666460653631514375880874422615237249871322129146554264800 

noncomputable def Ns312p10 := nat_lit 55164646516618494962085419356369025784335016154267579706247610053041231157772817011486486467101704279863254798704146668052276438579475100451766223896220272709675360577301802978530276301158911649961092601279696986330335403118086533522541958716560166657634553390183479955483588238249446822384543398154260439705049143284278540285021213103458182619368483938376641172730818250587232036579805400979202432024046862170503602539341971086573372247299262086029843105216008583038025403798224342134620653974939981235680083776396058604459065501719125356177784467570909658245422960948263734871602033841948787585406240093531041217463298165642337705122589129757920995868559518021463265498464182174549661735402095023640043996665674913376875 

noncomputable def Ns312p11 := BSN.log_dyadic_bound Ns312p6 Ns312p7 15 14 Ns312p8 268435456 70560000 Ns312p9 Ns312p10 307286088 Ns312p4 Ns312p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns312p6) (BSN.artanhQ Ns312p7) 0 14 Ns312p9 Ns312p8 Ns312p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns312p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns312p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns312p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns312p15 := nat_lit 167537954069966963268140139327979112712430526945422964221951926912223381190141639739514890494967825643602350173964944759828460064784215684919760383437959917620844610857567326816719640593037578236900835917107172977527392439886629774248115214831425484905681376157923696414882114961796820014026232307332015059110330001516939277521159573995394989771587717775443426002499543257897301982481613760098955890450106043861450716722534643739571053080256776912576113428445260435254713579381797931690799491102381747484553243404562568585572234105168360737285205910186933811836504830286397217473365026331067977496463917110493303316865058355012304571237619413071097245713770677768486493924969821719264401216877841676972336093778875903304572487929375 

noncomputable def Ns312p16 := nat_lit 17907736863639702486765313263906285882628955290251965205176678923530777959693011244026517850256414903756943142851250712732214241881959351517241344993825585048584379523049477943740273636414656012170312373198803997844271825165684859407921203335666024680974464565759223251918458072775203410604089667122984485578465112081892102496937045858735135721609691262763214794451343726045584198128451069547586972080574568545086657023793200560105564573365716615162566961587407171758966967827997201380802107846920231945878242774600967607639551032178207663699700360114112068650063802902647517702890145150192721997537569966984346993833704449560383184487996362781528900358997452380059737141488304159449328022742959995775545894292303322129146554264800 

noncomputable def Ns312p17 := nat_lit 55164646516619937449385584700664297411818070214438189962773666351465523500358685366424500506990751111492356556545320273548942244833046464529601272738875466881799996765940232256588350019911833156887888425998391295014189841212513610526066550079316346993943774342801096070086869790972589246312728227659319758310961510342377923950694747797317942483020440897997204711883064182772445608288320382376665481938194224815739627075458138172195220395246294556718284728034954178416253903237031389214179719385823921869528509431462690683227358218086518156757026652846493301460983550768858152506145788622699720737745394141184245149692548799188169247529408201840608223422296381897323845616153036586108326210125693898345963996665674913376875 

noncomputable def Ns312p18 := BSN.log_dyadic_bound Ns312p13 Ns312p14 15 14 Ns312p15 268435456 70560000 Ns312p16 Ns312p17 307286088 Ns312p12 Ns312p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns312p13) (BSN.artanhQ Ns312p14) 0 14 Ns312p16 Ns312p15 Ns312p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns312p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 153643044 134217728 2 134217728 38410761 33554432 1 67108864 (Ns312p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns312p0 Ns312p1 307286088 268435456 1 70560000 Bool.false (BSN.logfrac_isNear Ns312p4 Ns312p5 1 Ns312p0 Ns312p1 307286088 268435456 70560000 rfl rfl rfl (Ns312p11 rfl))) (BSN.isNear_log_sfrac Ns312p2 Ns312p1 307286088 268435456 1 70560000 Bool.false (BSN.logfrac_isNear Ns312p12 Ns312p5 1 Ns312p2 Ns312p1 307286088 268435456 70560000 rfl rfl rfl (Ns312p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS313to324.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 67108864 := Ns312p19 

noncomputable def Ns312p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 16777216 4410000 385100712855 135135 11629079 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz316 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz0 := qz316

theorem RS313to324.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 11629079 16777216 1 4410000 := BSN.isNear_log_sfrac 2 1 11629079 16777216 1 4410000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 11629079 16777216 4410000 rfl rfl rfl (Ns312p20 rfl)) 

theorem RS313to324.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 186065264 268435456 61 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 11629079 16777216 1 4410000 186065264 268435456 61 268435456 RS313to324.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz577 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz319 := qz577

noncomputable def Ns312p21 := @Enclosure.Real.IsNear.inv_image qz317 47453133 33554432 1 33554432 11863282 11863284 16777216 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 47453133 33554432 1 33554432 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 47453133 33554432 1 33554432 47453133 33554432 1 33554432 (BSN.sqrt_enclosure 2 1 23726566 23726567 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS313to324.d8 : Enclosure.Real.IsNear qz320 Bool.false 11863283 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 23726566 33554432 2 33554432 11863283 16777216 1 16777216 (Ns312p21 rfl rfl) rfl 

theorem RS313to324.d9 : Enclosure.Real.IsNear qz320 Bool.false 189812528 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 11863283 16777216 1 16777216 189812528 268435456 16 268435456 RS313to324.d8 rfl 

noncomputable def Ns312p22 := BSN.log_dyadic_bound 1 2 13 12 132638213186519040000 16777216 4410000 13079757671720842725 316234143225 18431655 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 1) (BSN.artanhQ 2) 0 12 13079757671720842725 132638213186519040000 316234143225 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS313to324.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 18431655 16777216 1 4410000 := BSN.isNear_log_sfrac 3 1 18431655 16777216 1 4410000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 18431655 16777216 4410000 rfl rfl rfl (Ns312p22 rfl)) 

theorem RS313to324.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 294906480 268435456 61 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 18431655 16777216 1 4410000 294906480 268435456 61 268435456 RS313to324.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns312p23 := @Enclosure.Real.IsNear.inv_image qz321 58117981 33554432 1 33554432 9686330 9686331 16777216 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 58117981 33554432 1 33554432 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 58117981 33554432 1 33554432 58117981 33554432 1 33554432 (BSN.sqrt_enclosure 3 1 29058990 29058991 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS313to324.d12 : Enclosure.Real.IsNear qz323 Bool.false 19372661 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 19372661 33554432 1 33554432 19372661 33554432 1 33554432 (Ns312p23 rfl rfl) rfl 

theorem RS313to324.d13 : Enclosure.Real.IsNear qz323 Bool.false 154981288 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 19372661 33554432 1 33554432 154981288 268435456 8 268435456 RS313to324.d12 rfl 

noncomputable def Ns312p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns312p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns312p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns312p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns312p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns312p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns312p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns312p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns312p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns312p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns312p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns312p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns312p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns312p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns312p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns312p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns312p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns312p25 Ns312p26 Ns312p27 Ns312p28 200200021673987500790625 Ns312p29 Ns312p30 Ns312p31 Ns312p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns312p32 Ns312p33 151412625 Ns312p34 Ns312p35 1322214852783825 Ns312p27 Ns312p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns312p32 Ns312p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns312p34 Ns312p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns312p36 Ns312p37 1267389585 Ns312p38 Ns312p39 1927077560082675 Ns312p29 Ns312p30 Ns312p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns312p36 Ns312p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns312p38 Ns312p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS313to324.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns312p24 Ns312p25 1 Ns312p26 := Ns312p40 rfl rfl rfl 

noncomputable def Ns312p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns312p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns312p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns312p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns312p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns312p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns312p25 Ns312p26 Ns312p42 Ns312p43 9945 Ns312p44 Ns312p45 65835 Ns312p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns312p42 Ns312p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns312p44 Ns312p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS313to324.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns312p41 Ns312p25 1 Ns312p26 := Ns312p46 rfl 

noncomputable def Ns312p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns312p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS313to324.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns312p47 Ns312p25 1 Ns312p48 := BSN.pi_combine Ns312p24 Ns312p41 Ns312p25 Ns312p26 Ns312p48 Ns312p47 rfl rfl rfl rfl RS313to324.d14 RS313to324.d15 

theorem RS313to324.d17 : Enclosure.Real.IsNear Real.pi Bool.false 14148475504056880 4503599627370496 1 4503599627370496 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns312p47 Ns312p25 1 Ns312p48 14148475504056880 4503599627370496 1 4503599627370496 RS313to324.d16 rfl 

noncomputable def Ns312p49 := nat_lit 147443727375074537121690809726715087890625 

noncomputable def Ns312p50 := nat_lit 22889945643899497138335355216896171420000 

noncomputable def Ns312p51 := nat_lit 355592320898650075318906513310625 

noncomputable def Ns312p52 := BSN.log_dyadic_bound 3 5 17 16 Ns312p49 16777216 4410000 Ns312p50 Ns312p51 23258159 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 3) (BSN.artanhQ 5) 0 16 Ns312p50 Ns312p49 Ns312p51 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS313to324.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 23258159 16777216 1 4410000 := BSN.isNear_log_sfrac 4 1 23258159 16777216 1 4410000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 23258159 16777216 4410000 rfl rfl rfl (Ns312p52 rfl)) 

theorem RS313to324.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 372130544 268435456 61 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 23258159 16777216 1 4410000 372130544 268435456 61 268435456 RS313to324.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns312p53 := @Enclosure.Real.IsNear.inv_image qz325 67108865 33554432 1 33554432 8388607 8388608 16777216 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 67108865 33554432 1 33554432 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 67108865 33554432 1 33554432 67108865 33554432 1 33554432 (BSN.sqrt_enclosure 4 1 33554432 33554433 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS313to324.d20 : Enclosure.Real.IsNear qz327 Bool.false 16777215 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 16777215 33554432 1 33554432 16777215 33554432 1 33554432 (Ns312p53 rfl rfl) rfl 

theorem RS313to324.d21 : Enclosure.Real.IsNear qz327 Bool.false 134217720 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 16777215 33554432 1 33554432 134217720 268435456 8 268435456 RS313to324.d20 rfl 

noncomputable def Ns312p54 := nat_lit 159424323765613091421820433543167414255940625 

noncomputable def Ns312p55 := nat_lit 33013339099500162583200499609923570567289500 

noncomputable def Ns312p56 := nat_lit 351657888879851162997374110924800000 

noncomputable def Ns312p57 := nat_lit 2289063575687431840984260 

noncomputable def Ns312p58 := nat_lit 3325435793429257756623375 

noncomputable def Ns312p59 := BSN.log_dyadic_bound 2 3 21 20 Ns312p54 16777216 4410000 Ns312p55 Ns312p56 27001887 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 20 10 9927050056596826020 47940881637414340575 686533194547200 Ns312p57 Ns312p58 512222703392784384000 Ns312p55 Ns312p54 Ns312p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 10 20 Ns312p57 Ns312p58 512222703392784384000 rfl rfl rfl rfl)) rfl rfl 

theorem RS313to324.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 4410000 := BSN.isNear_log_sfrac 5 1 27001887 16777216 1 4410000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 27001887 16777216 4410000 rfl rfl rfl (Ns312p59 rfl rfl)) 

theorem RS313to324.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 432030192 268435456 61 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 4410000 432030192 268435456 61 268435456 RS313to324.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns312p60 := @Enclosure.Real.IsNear.inv_image qz328 75029991 33554432 1 33554432 7502998 7503000 16777216 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 75029991 33554432 1 33554432 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 75029991 33554432 1 33554432 75029991 33554432 1 33554432 (BSN.sqrt_enclosure 5 1 37514995 37514996 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS313to324.d24 : Enclosure.Real.IsNear qz329 Bool.false 7502999 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 15005998 33554432 2 33554432 7502999 16777216 1 16777216 (Ns312p60 rfl rfl) rfl 

theorem RS313to324.d25 : Enclosure.Real.IsNear qz329 Bool.false 120047984 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 7502999 16777216 1 16777216 120047984 268435456 16 268435456 RS313to324.d24 rfl 

noncomputable def Ns312p61 := BSN.log_dyadic_bound 2 10 5 4 94500000000 16777216 4410000 1291130880 26880 6802575 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 10) 0 4 1291130880 94500000000 26880 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz577)

theorem RS313to324.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 50000000441 220500000000000000 := BSN.isNear_log_sfrac 6 1 4034683545132279 2251799813685248 50000000441 220500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 1083052117253279893684224 604462909807314587353088 1000000008820000 4410000000000000000000 4034683545132279 2251799813685248 50000000441 220500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 6802575 16777216 24973259072661432 36028797018963968 4410000 1000000000000000 rfl rfl rfl rfl (Ns312p61 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS313to324.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 480971758 268435456 62 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 50000000441 220500000000000000 480971758 268435456 62 268435456 RS313to324.d26 rfl 

noncomputable abbrev qz331 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns312p62 := @Enclosure.Real.IsNear.inv_image qz331 82191237 33554432 1 33554432 6849269 6849270 16777216 (@Enclosure.Real.IsNear.of_eq qz331 (Real.sqrt qz330) Bool.false 82191237 33554432 1 33554432 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 82191237 33554432 1 33554432 82191237 33554432 1 33554432 (BSN.sqrt_enclosure 6 1 41095618 41095619 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS313to324.d28 : Enclosure.Real.IsNear qz332 Bool.false 13698539 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 13698539 33554432 1 33554432 13698539 33554432 1 33554432 (Ns312p62 rfl rfl) rfl 

theorem RS313to324.d29 : Enclosure.Real.IsNear qz332 Bool.false 109588312 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 13698539 33554432 1 33554432 109588312 268435456 8 268435456 RS313to324.d28 rfl 

noncomputable def Ns312p63 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 16777216 4410000 11010900719820672 5524329195 9388794 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz577)

theorem RS313to324.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 50000000441 220500000000000000 := BSN.isNear_log_sfrac 7 1 4381799983422711 2251799813685248 50000000441 220500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 1176230476650867868041216 604462909807314587353088 1000000008820000 4410000000000000000000 4381799983422711 2251799813685248 50000000441 220500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 9388794 16777216 24973259072661432 36028797018963968 4410000 1000000000000000 rfl rfl rfl rfl (Ns312p63 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS313to324.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 522351262 268435456 62 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 50000000441 220500000000000000 522351262 268435456 62 268435456 RS313to324.d30 rfl 

noncomputable abbrev qz334 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns312p64 := @Enclosure.Real.IsNear.inv_image qz334 88776683 33554432 1 33554432 6341191 6341192 16777216 (@Enclosure.Real.IsNear.of_eq qz334 (Real.sqrt qz333) Bool.false 88776683 33554432 1 33554432 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 88776683 33554432 1 33554432 88776683 33554432 1 33554432 (BSN.sqrt_enclosure 7 1 44388341 44388342 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz335 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS313to324.d32 : Enclosure.Real.IsNear qz335 Bool.false 12682383 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 12682383 33554432 1 33554432 12682383 33554432 1 33554432 (Ns312p64 rfl rfl) rfl 

theorem RS313to324.d33 : Enclosure.Real.IsNear qz335 Bool.false 101459064 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 12682383 33554432 1 33554432 101459064 268435456 8 268435456 RS313to324.d32 rfl 

noncomputable def Ns312p65 := nat_lit 1256945285058001618599936 

noncomputable def Ns312p66 := BSN.log_dyadic_bound 0 16 1 0 1 16777216 4410000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz577)

theorem RS313to324.d34 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 100000001323 441000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 100000001323 441000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false Ns312p65 604462909807314587353088 1000000013230000 4410000000000000000000 9364972152248037 4503599627370496 100000001323 441000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 16777216 24973259072661432 36028797018963968 4410000 1000000000000000 rfl rfl rfl rfl (Ns312p66 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS313to324.d35 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 558195838 268435456 62 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 100000001323 441000000000000000 558195838 268435456 62 268435456 RS313to324.d34 rfl 

noncomputable abbrev qz337 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns312p67 := @Enclosure.Real.IsNear.inv_image qz337 94906265 33554432 1 33554432 5931641 5931642 16777216 (@Enclosure.Real.IsNear.of_eq qz337 (Real.sqrt qz336) Bool.false 94906265 33554432 1 33554432 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 94906265 33554432 1 33554432 94906265 33554432 1 33554432 (BSN.sqrt_enclosure 8 1 47453132 47453133 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz338 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS313to324.d36 : Enclosure.Real.IsNear qz338 Bool.false 11863283 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 11863283 33554432 1 33554432 11863283 33554432 1 33554432 (Ns312p67 rfl rfl) rfl 

theorem RS313to324.d37 : Enclosure.Real.IsNear qz338 Bool.false 94906264 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 11863283 33554432 1 33554432 94906264 268435456 8 268435456 RS313to324.d36 rfl 

noncomputable def Ns312p68 := nat_lit 1328140746012062765809664 

noncomputable def Ns312p69 := BSN.log_dyadic_bound 1 17 3 2 1252815 16777216 4410000 1448 3 1976071 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz577)

theorem RS313to324.d38 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 100000001323 441000000000000000 := BSN.isNear_log_sfrac 9 1 9895419672221413 4503599627370496 100000001323 441000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false Ns312p68 604462909807314587353088 1000000013230000 4410000000000000000000 9895419672221413 4503599627370496 100000001323 441000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 1976071 16777216 24973259072661432 36028797018963968 4410000 1000000000000000 rfl rfl rfl rfl (Ns312p69 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS313to324.d39 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 589812974 268435456 62 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 100000001323 441000000000000000 589812974 268435456 62 268435456 RS313to324.d38 rfl 

noncomputable abbrev qz340 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable def Ns312p70 := @Enclosure.Real.IsNear.inv_image qz340 100663297 33554432 1 33554432 5592405 5592406 16777216 (@Enclosure.Real.IsNear.of_eq qz340 (Real.sqrt qz339) Bool.false 100663297 33554432 1 33554432 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz339) Bool.false 100663297 33554432 1 33554432 100663297 33554432 1 33554432 (BSN.sqrt_enclosure 9 1 50331648 50331649 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz341 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS313to324.d40 : Enclosure.Real.IsNear qz341 Bool.false 11184811 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 11184811 33554432 1 33554432 11184811 33554432 1 33554432 (Ns312p70 rfl rfl) rfl 

theorem RS313to324.d41 : Enclosure.Real.IsNear qz341 Bool.false 89478488 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 11184811 33554432 1 33554432 89478488 268435456 8 268435456 RS313to324.d40 rfl 

noncomputable def Ns312p71 := nat_lit 1391827265235416537628672 

noncomputable def Ns312p72 := BSN.log_dyadic_bound 2 18 4 3 3571283520 16777216 4410000 14806464 960 3743727 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 18) 0 3 14806464 3571283520 960 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz710 := (Enclosure.sfrac Bool.false 10 1)

noncomputable abbrev qz578 := qz710

noncomputable abbrev qz342 := qz578

noncomputable abbrev qz1 := qz342

noncomputable abbrev qz343 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10) qz577)

theorem RS313to324.d42 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 10369921216632549 4503599627370496 100000001323 441000000000000000 := BSN.isNear_log_sfrac 10 1 10369921216632549 4503599627370496 100000001323 441000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz343) Bool.false Ns312p71 604462909807314587353088 1000000013230000 4410000000000000000000 10369921216632549 4503599627370496 100000001323 441000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 3743727 16777216 24973259072661432 36028797018963968 4410000 1000000000000000 rfl rfl rfl rfl (Ns312p72 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS313to324.d43 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 618095470 268435456 62 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 10369921216632549 4503599627370496 100000001323 441000000000000000 618095470 268435456 62 268435456 RS313to324.d42 rfl 

noncomputable abbrev qz344 := (Real.sqrt (@Nat.cast Real Real.instNatCast 10))

noncomputable def Ns312p73 := @Enclosure.Real.IsNear.inv_image qz344 106108431 33554432 1 33554432 5305421 5305422 16777216 (@Enclosure.Real.IsNear.of_eq qz344 (Real.sqrt qz343) Bool.false 106108431 33554432 1 33554432 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz343) Bool.false 106108431 33554432 1 33554432 106108431 33554432 1 33554432 (BSN.sqrt_enclosure 10 1 53054215 53054216 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz345 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

theorem RS313to324.d44 : Enclosure.Real.IsNear qz345 Bool.false 10610843 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz345 Bool.false 10610843 33554432 1 33554432 10610843 33554432 1 33554432 (Ns312p73 rfl rfl) rfl 

theorem RS313to324.d45 : Enclosure.Real.IsNear qz345 Bool.false 84886744 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz345 Bool.false 10610843 33554432 1 33554432 84886744 268435456 8 268435456 RS313to324.d44 rfl 

theorem RS313to324.d46 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz711 := (@instHMul Real Real.instMul)

noncomputable abbrev qz579 := qz711

noncomputable abbrev qz346 := (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz2 := qz346

theorem RS313to324.d47 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS313to324.d46 rfl 

noncomputable abbrev qz347 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 2 1) Real.pi))

noncomputable abbrev qz3 := qz347

theorem RS313to324.d48 : Enclosure.Real.IsNear qz3 Bool.false 5340353 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 5340353 33554432 1 33554432 5340353 33554432 1 33554432 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 2670176 2670177 16777216 RS313to324.d47 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns312p74 := nat_lit 3283043056885944201295819 

noncomputable def Ns312p75 := nat_lit 2603204523681891924049920000 

noncomputable def Ns312p76 := nat_lit 1324216174014400404118331981824 

noncomputable abbrev qz712 := (Enclosure.sfrac Bool.false 631875 1000)

noncomputable abbrev qz580 := qz712

noncomputable abbrev qz348 := qz580

noncomputable abbrev qz4 := qz348

noncomputable abbrev qz349 := qz579

noncomputable abbrev qz5 := qz349

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 10)

noncomputable abbrev qz350 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz713 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 631875 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz581 := qz713

noncomputable abbrev qz351 := qz581

noncomputable abbrev qz352 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz7 := (@HPow.hPow Real Real Real qz350 qz351 qz352)

noncomputable abbrev qz714 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 631875 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz582 := qz714

noncomputable abbrev qz353 := qz582

noncomputable abbrev qz8 := qz353

noncomputable def Ns312p77 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz7) (Zeta.RiemannSiegel.correction qz8)) 103844093 134217728 84375 67108864 2558800917565850281881 9444732965739290427392 10071818903736201295819 Ns312p75 Ns312p76 

noncomputable def Ns312p78 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos BSN.quadSignPos 9 10 631875 1000 200 268435456 134217728 4503599627370496 Bool.false 306123538538 2481 618095470 62 84886744 8 

noncomputable def Ns312p79 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 631875 1000 110 157 268435456 134217728 4503599627370496 Bool.false 306123538538 2481 

noncomputable def Ns312p80 := Ns312p79 558195838 62 94906264 8 589812974 62 89478488 8 Bool.true 26228133 126933 Bool.true 204139488 Bool.true 364318170 14148475504056880 1 Bool.false 194483107 Bool.true Bool.false 262334718 Bool.true Bool.true 182433203 

noncomputable def Ns312p81 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 631875 1000 5 56 268435456 134217728 4503599627370496 Bool.false 306123538538 2481 

noncomputable def Ns312p82 := Ns312p81 480971758 62 109588312 8 522351262 62 101459064 8 Bool.true 21855703 94162 Bool.false 101221810 Bool.true 324349155 14148475504056880 1 Bool.false 98840021 Bool.true Bool.false 95191061 Bool.false Bool.true 26228133 

noncomputable def Ns312p83 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 631875 1000 168 78 268435456 134217728 4503599627370496 Bool.false 306123538538 2481 

noncomputable def Ns312p84 := Ns312p83 372130544 61 134217720 8 432030192 61 120047984 16 Bool.true 63578473 55274 Bool.false 145103099 Bool.false 245181563 14148475504056880 1 Bool.false 230163318 Bool.false Bool.false 164035448 Bool.true Bool.true 21855703 

noncomputable def Ns312p85 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 631875 1000 447 284 268435456 134217728 4503599627370496 Bool.false 306123538538 2481 

noncomputable def Ns312p86 := Ns312p85 186065264 61 189812528 16 294906480 61 154981288 8 Bool.true 268435336 2549 Bool.false 72679412 Bool.false 28796860 14148475504056880 1 Bool.false 71794681 Bool.false Bool.false 266892321 Bool.false Bool.true 63578473 

noncomputable def Ns312p87 := nat_lit 171385624664198252939137746067425457244333 

noncomputable def Ns312p88 := nat_lit 150285660907669704957309714886276677632 

noncomputable def Ns312p89 := nat_lit 48350146123985497954101562500000000 

noncomputable def Ns312p90 := nat_lit 183307545055704757850694580078125000000 

noncomputable abbrev qz354 := (@Eq.refl Real qz580)

noncomputable abbrev qz9 := qz354

noncomputable def Ns312p91 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 631875 1000 1597065062500 16000000 1263750 4000 2000 Ns312p89 Ns312p90 qz9 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns312p92 := nat_lit 1882898708468974946841112932869664447264400634765625000000 

noncomputable abbrev qz715 := (@instHSub Real Real.instSub)

noncomputable abbrev qz583 := qz715

noncomputable abbrev qz355 := qz583

noncomputable abbrev qz584 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz716 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz717 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz585 := (@HSub.hSub Real Real Real qz715 qz716 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz717 (@Nat.cast Real Real.instNatCast 1263750))))

noncomputable abbrev qz356 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 631875 4000) (Real.log (Enclosure.sfrac Bool.false 1597065062500 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz585))

noncomputable abbrev qz586 := (Enclosure.sfrac Bool.false 631875 2000)

noncomputable abbrev qz10 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz356 qz586) (@HMul.hMul Real Real Real qz349 qz586 (Real.log Real.pi)))

noncomputable def Ns312p93 := @Enclosure.Real.IsNear.addLit_ft_p qz10 (Enclosure.sfrac Bool.true Ns312p89 Ns312p90) 10271803833258400445 9007199254740992 133554700148967131 14450688000000000000000 Ns312p89 Ns312p90 0 1 Ns312p92 

noncomputable def Ns312p94 := nat_lit 5514632691846533378568355840 

noncomputable abbrev qz11 := (@HSub.hSub Real Real Real qz355 qz356 qz586)

noncomputable def Ns312p95 := @Enclosure.Real.IsNear.subLit_ff_p qz11 (@HMul.hMul Real Real Real qz5 qz586 (Real.log Real.pi)) 13529375413236456125 9007199254740992 15996883917461 3528000000000000000 194166396855 536870912 5055 1073741824 Ns312p94 10271803833258400445 9007199254740992 

noncomputable abbrev qz12 := qz356

noncomputable def Ns312p96 := @Enclosure.Real.IsNear.subLit_ff_p qz12 qz586 16375087427781188285 9007199254740992 15996883917461 3528000000000000000 631875 2000 0 1 27058750826472912250000 13529375413236456125 9007199254740992 15996883917461 3528000000000000000 

noncomputable def Ns312p97 := nat_lit 36873418818957326694792994414919680 

noncomputable def Ns312p98 := nat_lit 55664212960505657015926784 

noncomputable def Ns312p99 := nat_lit 4835703278458516698824704 

noncomputable def Ns312p100 := nat_lit 174635977436481647848920770106346090969246283468142760737165478507065822341304151450458448380231857299804687500000000000000000000 

noncomputable def Ns312p101 := nat_lit 2568567757223790179117012395032987980703387113112642490629932366739567800883037307357881218194961547851562500000000000000000000 

noncomputable def Ns312p102 := nat_lit 2328689179499464102843485673806921272641192733642845629485427366711647323427314404398202896118164062500000000000000000000 

noncomputable def Ns312p103 := BSN.log_dyadic_bound 548489062500 2645641062500 6 5 Ns312p100 134217728 35280000 Ns312p101 Ns312p102 56470036 3194130125000 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 548489062500) (BSN.artanhQ 2645641062500) 0 5 Ns312p101 Ns312p100 Ns312p102 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz357 := (Real.log (Enclosure.sfrac Bool.false 1597065062500 16000000))

noncomputable abbrev qz358 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns312p104 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 631875 4000) qz357 631875 4000 0 1 3240083633020151 281474976710656 781250441 27562500000000000 16378622764916863305 9007199254740992 263281398617 58800000000000000 (Enclosure.Real.IsNear.const Bool.false 631875 4000) (BSN.isNear_log_sfrac 1597065062500 16000000 3240083633020151 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1597065062500) qz358)) Bool.false Ns312p98 Ns312p99 1000000564480000 35280000000000000000000 3240083633020151 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1597065062500 16000000 16 3194130125000 2097152000000 56470036 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns312p103 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns312p105 := BSN.arctan_dyadic_bound_f 1000 1263750 1 0 16777216 4410000 0 1 1 0 1 1 13275 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1263750) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1263750) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz587 := qz716

noncomputable abbrev qz359 := qz587

noncomputable abbrev qz13 := qz359

noncomputable abbrev qz588 := qz717

noncomputable abbrev qz360 := qz588

noncomputable abbrev qz14 := qz360

noncomputable abbrev qz718 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz589 := qz718

noncomputable abbrev qz361 := qz589

noncomputable abbrev qz15 := (@Enclosure.Real.IsNear.mulLit_ff qz361 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz362 := (@Nat.cast Real Real.instNatCast 1263750)

noncomputable def Ns312p106 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz362)) 884279719003555 562949953421312 1 2000000000000000 13275 16777216 1 4410000 14828278689510279086080 883834283918755 562949953421312 200000000441 882000000000000000 qz15 (Ns312p105 rfl) rfl rfl 

noncomputable abbrev qz363 := (@HMul.hMul Real Real Real qz579 qz584 qz585)

noncomputable abbrev qz16 := qz363

noncomputable abbrev qz364 := qz584

noncomputable abbrev qz17 := qz364

noncomputable abbrev qz365 := qz585

noncomputable abbrev qz18 := qz365

noncomputable abbrev qz366 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns312p107 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 631875 4000) qz357) qz16 16378622764916863305 9007199254740992 263281398617 58800000000000000 883834283918755 2251799813685248 200000000441 3528000000000000000 Ns312p97 16375087427781188285 9007199254740992 15996883917461 3528000000000000000 (Ns312p104 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz18 1 4 0 1 883834283918755 562949953421312 200000000441 882000000000000000 883834283918755 2251799813685248 200000000441 3528000000000000000 qz366 Ns312p106 rfl) 

noncomputable def Ns312p108 := @Ns312p93 Ns312p87 Ns312p88 133554700148967131 14450688000000000000000 (@Ns312p95 133554700148967131 14450688000000000000000 (Ns312p96 (Ns312p107 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 631875 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz586 (Real.log Real.pi) 631875 2000 0 1 38410761 33554432 1 67108864 194166396855 536870912 5055 1073741824 (Enclosure.Real.IsNear.const Bool.false 631875 2000) RS313to324.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns312p89 Ns312p90) 

noncomputable abbrev qz367 := (@instHAdd Real Real.instAdd)

noncomputable def Ns312p109 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns312p87 Ns312p88 133554700148967131 14450688000000000000000 38265442317 33554432 311 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz367 qz10 (Enclosure.sfrac Bool.true Ns312p89 Ns312p90)) Bool.false Ns312p87 Ns312p88 133554700148967131 14450688000000000000000 Ns312p91 (Ns312p108 rfl rfl)) 

noncomputable def Ns312p110 := BSN.cos_dyadic_bound_f 62877352 68719476736 1 0 33554432 8828614 0 1 1 0 1 1 33554417 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 62877352) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 62877352) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable abbrev qz368 := (@Nat.cast Real Real.instNatCast 33554432)

noncomputable abbrev qz369 := (@Nat.cast Real Real.instNatCast Ns312p99)

noncomputable def Ns312p111 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 38265442317) qz368) Bool.false 38265442317 33554432 311 33554432 Bool.true 33554417 33554432 1 4410000 (Ns312p109 rfl) (Enclosure.sfrac_false_div 38265442317 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 38265442317) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4424600305686087204864) qz369) 226375608064910080 72057594037927936 Bool.false 33554417 33554432 181 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q2 38265442317 33554432 226375608064910080 72057594037927936 181 4424600305686087204864 Ns312p99 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554417 33554432 4424600305686087204864 Ns312p99 62877352 68719476736 8828614 8820000 (Ns312p110 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns312p112 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns312p87 Ns312p88 133554700148967131 14450688000000000000000 306123538538 268435456 2481 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz367 qz10 (Enclosure.sfrac Bool.true Ns312p89 Ns312p90)) Bool.false Ns312p87 Ns312p88 133554700148967131 14450688000000000000000 Ns312p91 (Ns312p108 rfl rfl)) 

noncomputable def Ns312p113 := Ns312p86 55274 BSN.abs_quadSignPos (BSN.cos_quad_nat3 447 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 71794681 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 284 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 266892321 268435456) qz9 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 33554417 33554432 87816527 9248440320000 268435336 268435456 2549 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 33554417 33554432 87816527 9248440320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 33554417 33554432 1405064432 147975045120000 33554417 33554432 87816527 9248440320000 (Ns312p111 rfl rfl) rfl)) rfl) (Ns312p112 rfl) RS313to324.d7 

noncomputable def Ns312p114 := nat_lit 27902660842591552156512079073536 

noncomputable def Ns312p115 := nat_lit 623075623024179315423659559506411520 

noncomputable def Ns312p116 := nat_lit 4361529361169255207965616916544880640 

noncomputable abbrev qz370 := (BSN.sinEvenQ 268435456)

noncomputable abbrev qz371 := (BSN.sinOddQ 268435456)

noncomputable def Ns312p117 := BSN.sin_dyadic_bound_f 72679412 268435456 2 1 268435456 134217728 Ns312p114 Ns312p115 Ns312p114 Ns312p114 Ns312p116 Ns312p114 71794681 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 72679412) qz370 0 1 Ns312p114 Ns312p115 Ns312p114 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 72679412) qz371 0 1 Ns312p114 Ns312p116 Ns312p114 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p118 := nat_lit 687670730991793347822912160000 

noncomputable def Ns312p119 := nat_lit 124615124604835863084731911901282304 

noncomputable def Ns312p120 := nat_lit 1869226869072537946270978678519234560 

noncomputable abbrev qz372 := (BSN.cosEvenQ 268435456)

noncomputable abbrev qz373 := (BSN.cosOddQ 268435456)

noncomputable def Ns312p121 := BSN.cos_dyadic_bound_f 28796860 268435456 2 1 268435456 134217728 Ns312p118 Ns312p119 Ns312p118 Ns312p118 Ns312p120 Ns312p118 266892321 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 28796860) qz372 0 1 Ns312p118 Ns312p119 Ns312p118 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 28796860) qz373 0 1 Ns312p118 Ns312p120 Ns312p118 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p122 := nat_lit 3867208770401752262518753324681933469975698407672988301390187394944481 

noncomputable def Ns312p123 := nat_lit 1087025049619513796520974048308631508761049663116835882438097565248389120 

noncomputable def Ns312p124 := nat_lit 196523053268543382418961854226295750519816165859129222839172255201 

noncomputable def Ns312p125 := nat_lit 11601233265098719700791422050337347818426055590687246645724883840323041 

noncomputable def Ns312p126 := nat_lit 48916127232878120843443832173888417894247234840257614709714390436177510400 

noncomputable def Ns312p127 := BSN.cos_dyadic_bound_f 145103099 268435456 3 2 268435456 134217728 Ns312p122 Ns312p123 Ns312p124 Ns312p125 Ns312p126 Ns312p124 230163318 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 145103099) qz372 0 2 Ns312p122 Ns312p123 Ns312p124 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 145103099) qz373 0 2 Ns312p125 Ns312p126 Ns312p124 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p128 := nat_lit 31535513762996869929247784828833911335359174928979324477067136477061601 

noncomputable def Ns312p129 := nat_lit 13058776057138037453655068424374277321690140304578328315597217751521 

noncomputable def Ns312p130 := nat_lit 94580423736876333712836044349652985451434144506328816774570214995681761 

noncomputable def Ns312p131 := BSN.cos_dyadic_bound_f 245181563 268435456 3 2 268435456 134217728 Ns312p128 Ns312p123 Ns312p129 Ns312p130 Ns312p126 Ns312p129 164035448 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 245181563) qz372 0 2 Ns312p128 Ns312p123 Ns312p129 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 245181563) qz373 0 2 Ns312p130 Ns312p126 Ns312p129 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p132 := Ns312p84 94162 BSN.abs_quadSignPos (BSN.cos_quad_nat0 168 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 230163318 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 78 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 164035448 268435456) qz9 rfl rfl (Ns312p113 RS313to324.d9 RS313to324.d11 RS313to324.d13 RS313to324.d17 (Ns312p117 rfl rfl) (Ns312p121 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns312p112 rfl) RS313to324.d19 RS313to324.d21 RS313to324.d23 RS313to324.d25 RS313to324.d17 (Ns312p127 rfl rfl) (Ns312p131 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns312p133 := nat_lit 104977540985879967647708911210000 

noncomputable def Ns312p134 := BSN.sin_dyadic_bound_f 101221810 268435456 2 1 268435456 134217728 Ns312p133 Ns312p115 Ns312p133 Ns312p133 Ns312p116 Ns312p133 98840021 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 101221810) qz370 0 1 Ns312p133 Ns312p115 Ns312p133 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 101221810) qz371 0 1 Ns312p133 Ns312p116 Ns312p133 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p135 := nat_lit 5962750025773649152221913127164970040837331120288786867775316500953248084880208738409720580007612260420640625 

noncomputable def Ns312p136 := nat_lit 67052582193422231333984484018745857420694574238012043916021913709013615522643186318434558042568065189255577600 

noncomputable def Ns312p137 := nat_lit 1355667704110843094080854735500867971296380487181507800801287034597136359277566265880333797695556640625 

noncomputable def Ns312p138 := nat_lit 36143451105070186148696828492858528843721626165360472658952065897108770963384329297190541313917939333598240625 

noncomputable def Ns312p139 := nat_lit 6101784979601423051392588045705873025283206255659095996357994147520239012560529954977544781873693932222257561600 

noncomputable def Ns312p140 := BSN.cos_dyadic_bound_f 324349155 268435456 4 3 268435456 134217728 Ns312p135 Ns312p136 Ns312p137 Ns312p138 Ns312p139 Ns312p137 95191061 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 324349155) qz372 0 3 Ns312p135 Ns312p136 Ns312p137 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 324349155) qz373 0 3 Ns312p138 Ns312p139 Ns312p137 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p141 := Ns312p82 126933 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 5 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 98840021 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 56 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 95191061 268435456) qz9 rfl rfl (Ns312p132 rfl rfl) (Ns312p112 rfl) RS313to324.d27 RS313to324.d29 RS313to324.d31 RS313to324.d33 RS313to324.d17 (Ns312p134 rfl rfl) (Ns312p140 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p142 := nat_lit 15151768767426571138838895425068476928939684052290312581785328367435776 

noncomputable def Ns312p143 := nat_lit 3015894668273457761784277623317863811030120692220261038461284253696 

noncomputable def Ns312p144 := nat_lit 45449274512943166500993117719958795059196991915486497223279062533799936 

noncomputable def Ns312p145 := BSN.cos_dyadic_bound_f 204139488 268435456 3 2 268435456 134217728 Ns312p142 Ns312p123 Ns312p143 Ns312p144 Ns312p126 Ns312p143 194483107 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 204139488) qz372 0 2 Ns312p142 Ns312p123 Ns312p143 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 204139488) qz373 0 2 Ns312p144 Ns312p126 Ns312p143 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p146 := nat_lit 24673372505436125896746634685865849111643289321937399928363519799189753827667111186386153252410829889702400000 

noncomputable def Ns312p147 := nat_lit 871683568514489007341798292243696146469029465094156570908284878217177001794361422139649254553384847460322508800 

noncomputable def Ns312p148 := nat_lit 5467263194383255277202600229120248423068126968887937051847922439769001950664883352650542561000000000000 

noncomputable def Ns312p149 := nat_lit 123281371449259777845577432109985100263665598680678069228188953985392387755287173622900145784793006504512000000 

noncomputable def Ns312p150 := nat_lit 30508924898007115256962940228529365126416031278295479981789970737601195062802649774887723909368469661111287808000 

noncomputable def Ns312p151 := BSN.sin_dyadic_bound_f 364318170 268435456 4 3 268435456 134217728 Ns312p146 Ns312p147 Ns312p148 Ns312p149 Ns312p150 Ns312p148 262334718 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 364318170) qz370 0 3 Ns312p146 Ns312p147 Ns312p148 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 364318170) qz371 0 3 Ns312p149 Ns312p150 Ns312p148 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz590 := (BSN.cos_quad_nat1 157 rfl)

noncomputable def Ns312p152 := Ns312p80 155566 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 110 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 194483107 268435456) BSN.abs_quadSignNeg qz590 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 262334718 268435456) qz9 rfl rfl (Ns312p141 rfl) (Ns312p112 rfl) RS313to324.d35 RS313to324.d37 RS313to324.d39 RS313to324.d41 RS313to324.d17 (Ns312p145 rfl rfl) (Ns312p151 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p153 := nat_lit 1022488023423283424886235609744438167559842180873615072084622833582336 

noncomputable def Ns312p154 := nat_lit 13739381914649198391836366340388463965913823561412012074355097856 

noncomputable def Ns312p155 := nat_lit 3067436591506020976261923156500633725751594714973722392229719790551296 

noncomputable def Ns312p156 := BSN.cos_dyadic_bound_f 104050914 268435456 3 2 268435456 134217728 Ns312p153 Ns312p123 Ns312p154 Ns312p155 Ns312p126 Ns312p154 248520589 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 104050914) qz372 0 2 Ns312p153 Ns312p123 Ns312p154 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 104050914) qz373 0 2 Ns312p155 Ns312p126 Ns312p154 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz374 := (BSN.cos_quad_nat0 200 rfl)

noncomputable def Ns312p157 := Ns312p78 Bool.true 182433203 155566 Bool.true 104050914 14148475504056880 1 Bool.false 248520589 Bool.false Bool.true 103844093 168750 BSN.abs_quadSignPos qz374 (BSN.sfrac_eq_quadSignPos_mul Bool.false 248520589 268435456) qz9 rfl (Ns312p152 rfl) (Ns312p112 rfl) RS313to324.d43 RS313to324.d45 RS313to324.d17 (Ns312p156 rfl rfl) rfl 

noncomputable def Ns312p158 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) 103844093 268435456 168750 268435456 103844093 268435456 168750 268435456 55750872914722816 103844093 134217728 84375 67108864 (Ns312p157 rfl rfl rfl rfl) 

noncomputable def Ns312p159 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz7) (Zeta.RiemannSiegel.correction qz8) 10595881 33554432 1 33554432 241490152406001 281474976710656 944259116936117 77581540455874560000 2558800917565850281881 9444732965739290427392 

noncomputable def Ns312p160 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz7 1 1 0 1 10595881 33554432 1 33554432 10595881 33554432 1 33554432 

noncomputable abbrev qz19 := qz351

noncomputable abbrev qz20 := (@Enclosure.Real.IsNear.of_eq qz351 (@HMul.hMul Real Real Real qz349 qz348 qz347) Bool.false 26995484415 268435456 5055 268435456 (BSN.t_div_two_pi_mk qz348 631875 1000 qz354) (@Enclosure.Real.IsNear.mulLit_ff qz348 qz347 631875 1000 0 1 5340353 33554432 1 33554432 26995484415 268435456 5055 268435456 (Enclosure.Real.IsNear.const Bool.false 631875 1000) RS313to324.d48 rfl))

noncomputable def Ns312p161 := @Enclosure.Real.IsNear.sqrt_image qz19 26995484415 268435456 5055 268435456 168246283 168246315 16777216 qz20 

noncomputable abbrev qz719 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 631875 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz591 := qz719

noncomputable abbrev qz375 := qz591

noncomputable abbrev qz21 := qz375

noncomputable def Ns312p162 := @Enclosure.Real.IsNear.sqrt_image qz21 168246299 16777216 1 1048576 53129127 53129133 16777216 (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 336492598 33554432 32 33554432 168246299 16777216 1 1048576 (Ns312p161 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz592 := (Real.sqrt qz719)

noncomputable abbrev qz376 := qz592

noncomputable abbrev qz22 := qz376

noncomputable def Ns312p163 := @Enclosure.Real.IsNear.inv_image qz22 26564565 8388608 3 16777216 5297940 5297941 16777216 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 106258260 33554432 6 33554432 26564565 8388608 3 16777216 (Ns312p162 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns312p164 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz22) Bool.false 10595881 33554432 1 33554432 10595881 33554432 1 33554432 (Ns312p163 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz23 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz353))

noncomputable abbrev qz593 := (@HMul.hMul Real Real Real qz711 qz714 qz714)

noncomputable abbrev qz594 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz377 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz593 qz582) qz594)

noncomputable abbrev qz24 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz377))

noncomputable def Ns312p165 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz8) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz23) qz24) Bool.false 241490152406001 

noncomputable def Ns312p166 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz23) qz24 34090467 33554432 217 

noncomputable def Ns312p167 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz23) Bool.false 34090467 33554432 217 33554432 34090467 33554432 217 

noncomputable def Ns312p168 := @Enclosure.Real.IsNear.recentre' qz23 Bool.false 16513413 16777216 462187216 73987522560000 16513413 16777216 28886701 4624220160000 

noncomputable abbrev qz25 := (@HMul.hMul Real Real Real qz349 qz346 qz353)

noncomputable abbrev qz378 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable def Ns312p169 := @Enclosure.Real.IsNear.cos_image qz25 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2979103) qz378) Bool.false 2979103 16777216 101 16777216 Bool.false 16513413 16777216 1 

noncomputable def Ns312p170 := nat_lit 5397215081859719378502747 

noncomputable def Ns312p171 := nat_lit 900719925474099200000000000000 

noncomputable def Ns312p172 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz8 884279719003555 140737488355328 1 500000000000000 474139 16777216 1 1048576 419271501688626564145 2361183241434822606848 Ns312p170 

noncomputable def Ns312p173 := @Enclosure.Real.IsNear.subLit_ff_p qz21 qz1 168246299 16777216 1 1048576 10 1 0 1 474139 474139 16777216 1 

noncomputable abbrev qz379 := (Enclosure.Real.IsNear.const Bool.false 10 1)

noncomputable def Ns312p174 := @Ns312p173 1048576 (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 336492598 33554432 32 33554432 168246299 16777216 1 1048576 (Ns312p161 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns312p175 := @Enclosure.Real.IsNear.recentre' qz25 Bool.false 419271501688626564145 2361183241434822606848 Ns312p170 Ns312p171 2979103 16777216 101 16777216 (@Ns312p172 Ns312p171 RS313to324.d47 (Ns312p174 rfl rfl) rfl) 

noncomputable def Ns312p176 := nat_lit 78766595654800156461482881 

noncomputable def Ns312p177 := nat_lit 1901475900342344102245054808064 

noncomputable def Ns312p178 := nat_lit 28522138505135161533675822120960 

noncomputable def Ns312p179 := BSN.cos_dyadic_bound_f 2979103 16777216 2 1 16777216 4410000 Ns312p176 Ns312p177 Ns312p176 Ns312p176 Ns312p178 Ns312p176 16513413 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 2979103) (BSN.cosEvenQ 16777216) 0 1 Ns312p176 Ns312p177 Ns312p176 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 2979103) (BSN.cosOddQ 16777216) 0 1 Ns312p176 Ns312p178 Ns312p176 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p180 := @Enclosure.Real.IsNear.inv_image qz23 16513413 16777216 28886701 4624220160000 17045125 17045342 16777216 (Ns312p168 (@Ns312p169 4410000 (Ns312p175 rfl) (Enclosure.sfrac_false_div 2979103 16777216) (Ns312p179 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns312p181 := @Enclosure.Real.IsNear.recentre' qz24 Bool.false 14167606 16777216 

noncomputable abbrev qz26 := (@HMul.hMul Real Real Real qz349 qz346 qz377)

noncomputable abbrev qz595 := (@Nat.cast Real Real.instNatCast 4194304)

noncomputable def Ns312p182 := @Enclosure.Real.IsNear.cos_image qz26 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 2370827)) qz595) Bool.true 2370827 4194304 

noncomputable def Ns312p183 := nat_lit 22391828907949751119993273045 

noncomputable def Ns312p184 := nat_lit 39614081257132168796771975168 

noncomputable def Ns312p185 := nat_lit 239170974768679511402641897463349 

noncomputable def Ns312p186 := @Enclosure.Real.IsNear.recentre' qz26 Bool.true Ns312p183 Ns312p184 Ns312p185 

noncomputable def Ns312p187 := nat_lit 37778931862957161709568000000000000000 

noncomputable abbrev qz27 := qz377

noncomputable def Ns312p188 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz27 884279719003555 140737488355328 1 500000000000000 25322110670119 

noncomputable abbrev qz380 := (@HSub.hSub Real Real Real qz583 qz593 qz582)

noncomputable abbrev qz28 := qz380

noncomputable abbrev qz381 := qz594

noncomputable abbrev qz29 := qz381

noncomputable def Ns312p189 := @Enclosure.Real.IsNear.subLit_tf qz28 qz29 7729924625703 281474976710656 8862755 8796093022208 1 16 

noncomputable abbrev qz382 := qz593

noncomputable abbrev qz30 := qz382

noncomputable def Ns312p190 := @Enclosure.Real.IsNear.subLit_ff_n qz30 qz8 224807791321 281474976710656 474147 8796093022208 474139 16777216 1 1048576 

noncomputable def Ns312p191 := @Enclosure.Real.IsNear.mulLit_ff qz8 qz8 474139 16777216 1 1048576 474139 16777216 1 1048576 224807791321 281474976710656 

noncomputable def Ns312p192 := nat_lit 16427623740827795753584499003442537028984163620364292961 

noncomputable def Ns312p193 := nat_lit 3861888762982039923063034508418779142719222587902677483520 

noncomputable def Ns312p194 := nat_lit 998157136599878994384348446612076538937225749795681 

noncomputable def Ns312p195 := nat_lit 49280874908210187502764728313434386933874616409593287521 

noncomputable def Ns312p196 := nat_lit 173784994334191796537836552878845061422365016455620486758400 

noncomputable def Ns312p197 := BSN.cos_dyadic_bound_f 2370827 4194304 3 2 16777216 4410000 Ns312p192 Ns312p193 Ns312p194 Ns312p195 Ns312p196 Ns312p194 14167606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2370827) (BSN.cosEvenQ 4194304) 0 2 Ns312p192 Ns312p193 Ns312p194 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2370827) (BSN.cosOddQ 4194304) 0 2 Ns312p195 Ns312p196 Ns312p194 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz383 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns312p198 := @Ns312p181 488647216 73987522560000 7083803 8388608 30540451 4624220160000 (@Ns312p182 107 16777216 Bool.false 14167606 16777216 1 4410000 (@Ns312p186 Ns312p187 2370827 4194304 107 16777216 (@Ns312p188 281474976710656 8862755 8796093022208 Ns312p183 Ns312p184 Ns312p185 Ns312p187 RS313to324.d47 (@Ns312p189 0 1 405153770721904 25322110670119 281474976710656 8862755 8796093022208 (@Ns312p190 129686615109138382848 7729924625703 281474976710656 8862755 8796093022208 (@Ns312p191 474147 8796093022208 (Ns312p174 rfl rfl) (Ns312p174 rfl rfl) rfl) (Ns312p174 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 2370827 4194304) (BSN.cos_neg_of_bound 2370827 4194304 Bool.false 14167606 16777216 1 4410000 (Ns312p197 rfl rfl)) rfl rfl) 

noncomputable abbrev qz31 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 10) (Enclosure.sfrac Bool.false 1 1) Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 10 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1))

noncomputable def Ns312p199 := @Ns312p159 10071818903736201295819 Ns312p75 (Ns312p160 qz31 (@Enclosure.Real.IsNear.of_eq qz7 (@Inv.inv Real Real.instInv qz22) Bool.false 10595881 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz19 (BSN.t_div_two_pi_nonneg qz4 631875 1000 qz9)) Ns312p164) rfl) (@Ns312p165 281474976710656 944259116936117 77581540455874560000 (BSN.correction_mk qz8 (BSN.cos_two_pi_p_ne_zero_mk qz4 631875 1000 10 qz9 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 631875 1000 10 qz9 rfl rfl rfl))) (@Ns312p166 33554432 7083803 8388608 30540451 4624220160000 241490152406001 281474976710656 944259116936117 77581540455874560000 (@Ns312p167 33554432 (Ns312p180 rfl rfl rfl rfl rfl) rfl) (Ns312p198 rfl) rfl)) 

noncomputable abbrev qz32 := qz355

noncomputable def Ns312p200 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 9866179332244399220633 9444732965739290427392 Ns312p74 Ns312p75 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz7) (Zeta.RiemannSiegel.correction qz8))) Bool.true 9866179332244399220633 9444732965739290427392 Ns312p74 Ns312p75 (BSN.hardyZApproximantRS₀_eq qz4 10 (@BSN.floor_sqrt_eq_dec qz4 631875 1000 10 qz9 rfl rfl rfl)) (@Ns312p77 9866179332244399220633 9444732965739290427392 Ns312p74 Ns312p75 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10)) Bool.true 103844093 134217728 84375 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (Ns312p158 (Ns312p157 rfl rfl rfl rfl) rfl rfl)) (Ns312p199 rfl) rfl rfl)) 

theorem RS313to324.d49 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 9866179332244399220633 9444732965739290427392 Ns312p74 Ns312p75 := Ns312p200 

theorem RS313to324.d50 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS313to324.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS313to324.d3 a b h)) 

noncomputable def Ns312p201 := nat_lit 21693371030682432700416000 

noncomputable def Ns312p202 := nat_lit 16098240161017132407041556480 

noncomputable abbrev qz720 := (Enclosure.sfrac Bool.false 633237 1000)

noncomputable abbrev qz596 := qz720

noncomputable abbrev qz384 := qz596

noncomputable abbrev qz33 := qz384

noncomputable abbrev qz721 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 633237 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz597 := qz721

noncomputable abbrev qz385 := qz597

noncomputable abbrev qz34 := (@HPow.hPow Real Real Real qz350 qz385 qz352)

noncomputable abbrev qz722 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 633237 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz598 := qz722

noncomputable abbrev qz386 := qz598

noncomputable abbrev qz35 := qz386

noncomputable def Ns312p203 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz34) (Zeta.RiemannSiegel.correction qz35)) 7921725 4194304 84559 67108864 621415174541029383705 2361183241434822606848 84967636549514873663 Ns312p201 Ns312p202 

noncomputable def Ns312p204 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.cos BSN.quadSignPos 9 10 633237 1000 200 268435456 134217728 4503599627370496 Bool.false 306966613004 2487 618095470 62 84886744 8 

noncomputable def Ns312p205 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 633237 1000 110 157 268435456 134217728 4503599627370496 Bool.false 306966613004 2487 

noncomputable def Ns312p206 := Ns312p205 558195838 62 94906264 8 589812974 62 89478488 8 Bool.false 343825675 127211 Bool.true 121327754 Bool.true 324568975 14148475504056880 1 Bool.false 241480140 Bool.true Bool.false 251068416 Bool.true Bool.false 174760079 

noncomputable def Ns312p207 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 633237 1000 5 56 268435456 134217728 4503599627370496 Bool.false 306966613004 2487 

noncomputable def Ns312p208 := Ns312p207 480971758 62 109588312 8 522351262 62 101459064 8 Bool.false 363927380 94369 Bool.false 289212742 Bool.true 192717108 14148475504056880 1 Bool.false 236419171 Bool.true Bool.false 202177774 Bool.false Bool.false 343825675 

noncomputable def Ns312p209 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 633237 1000 169 79 268435456 134217728 4503599627370496 Bool.false 306966613004 2487 

noncomputable def Ns312p210 := Ns312p209 372130544 61 134217720 8 432030192 61 120047984 16 Bool.false 359053170 55396 Bool.false 59678336 Bool.false 78173479 14148475504056880 1 Bool.false 59187941 Bool.true Bool.false 77073193 Bool.false Bool.false 363927380 

noncomputable def Ns312p211 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz33) qz33 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 633237 1000 448 285 268435456 134217728 4503599627370496 Bool.false 306966613004 2487 

noncomputable def Ns312p212 := Ns312p211 186065264 61 189812528 16 294906480 61 154981288 8 Bool.false 268435448 2557 Bool.false 240675561 Bool.false 48551272 14148475504056880 1 Bool.false 167578982 Bool.false Bool.false 48286994 Bool.true Bool.false 359053170 

noncomputable def Ns312p213 := nat_lit 16602731758209727586930680404207886776051824649460891011 

noncomputable def Ns312p214 := nat_lit 14518718588779059536034134571389436187194292384563200 

noncomputable def Ns312p215 := nat_lit 1806336000000000000000000 

noncomputable def Ns312p216 := nat_lit 48873488240574368620885041579360000 

noncomputable def Ns312p217 := nat_lit 185691060464437691485254633708031129920 

noncomputable abbrev qz599 := (@Eq.refl Real qz720)

noncomputable abbrev qz387 := qz599

noncomputable abbrev qz36 := qz387

noncomputable def Ns312p218 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz33 633237 1000 1603957392676 16000000 1266474 4000 2000 Ns312p216 Ns312p217 qz36 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns312p219 := nat_lit 47815867463644015450360359564118713915029254990447366111680 

noncomputable abbrev qz600 := (@HSub.hSub Real Real Real qz715 qz716 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz717 (@Nat.cast Real Real.instNatCast 1266474))))

noncomputable abbrev qz388 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 633237 4000) (Real.log (Enclosure.sfrac Bool.false 1603957392676 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz600))

noncomputable abbrev qz601 := (Enclosure.sfrac Bool.false 633237 2000)

noncomputable abbrev qz37 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz388 qz601) (@HMul.hMul Real Real Real qz349 qz601 (Real.log Real.pi)))

noncomputable def Ns312p220 := @Enclosure.Real.IsNear.addLit_ft_p qz37 (Enclosure.sfrac Bool.true Ns312p216 Ns312p217) 257502317825001401979 225179981368524800 16730101267621966153 Ns312p215 Ns312p216 Ns312p217 0 1 Ns312p219 

noncomputable def Ns312p221 := nat_lit 86403440133013974426090209280000 

noncomputable abbrev qz38 := (@HSub.hSub Real Real Real qz355 qz388 qz601)

noncomputable def Ns312p222 := @Enclosure.Real.IsNear.subLit_ff_p qz38 (@HMul.hMul Real Real Real qz5 qz601 (Real.log Real.pi)) 1695585744335801084007 1125899906842624000 2003866742085193 441000000000000000000 24323115063357 67108864000 633237 134217728000 Ns312p221 257502317825001401979 225179981368524800 

noncomputable def Ns312p223 := nat_lit 3391171488671602168014000 

noncomputable abbrev qz39 := qz388

noncomputable def Ns312p224 := @Enclosure.Real.IsNear.subLit_ff_p qz39 qz601 2052066483990452430951 1125899906842624000 2003866742085193 441000000000000000000 633237 2000 0 1 Ns312p223 1695585744335801084007 1125899906842624000 2003866742085193 441000000000000000000 

noncomputable def Ns312p225 := nat_lit 4620842926319442731822346759567310848 

noncomputable def Ns312p226 := nat_lit 55685037100779459923935232 

noncomputable def Ns312p227 := nat_lit 179239239667358878612586069958631004552417852583642520702707401008961234601311104039293651624381028693291891348851643893830123520 

noncomputable def Ns312p228 := nat_lit 2690352863795226709616337265353023101858719351596653823317049511772166770689930550302066748411213031228016243913298274501525504 

noncomputable def Ns312p229 := nat_lit 2638426865182403879281625288860504708729403703056469932632818158653282989004299161089969211894302258150693508551220920320 

noncomputable def Ns312p230 := BSN.log_dyadic_bound 555381392676 2652533392676 6 5 Ns312p227 134217728 35280000 Ns312p228 Ns312p229 57048022 3207914785352 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 555381392676) (BSN.artanhQ 2652533392676) 0 5 Ns312p228 Ns312p227 Ns312p229 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz389 := (Real.log (Enclosure.sfrac Bool.false 1603957392676 16000000))

noncomputable def Ns312p231 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 633237 4000) qz389 633237 4000 0 1 3241295757516023 281474976710656 781250441 27562500000000000 2052508401602173856451 1125899906842624000 164905561835839 36750000000000000000 (Enclosure.Real.IsNear.const Bool.false 633237 4000) (BSN.isNear_log_sfrac 1603957392676 16000000 3241295757516023 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1603957392676) qz358)) Bool.false Ns312p226 Ns312p99 1000000564480000 35280000000000000000000 3241295757516023 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1603957392676 16000000 16 3207914785352 2097152000000 57048022 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns312p230 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns312p232 := BSN.arctan_dyadic_bound_f 1000 1266474 1 0 16777216 4410000 0 1 1 0 1 1 13247 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1266474) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1266474) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz390 := (@Nat.cast Real Real.instNatCast 1266474)

noncomputable def Ns312p233 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz390)) 884279719003555 562949953421312 1 2000000000000000 13247 16777216 1 4410000 14828294452108974882816 883835223442851 562949953421312 200000000441 882000000000000000 qz15 (Ns312p232 rfl) rfl rfl 

noncomputable abbrev qz391 := (@HMul.hMul Real Real Real qz579 qz584 qz600)

noncomputable abbrev qz40 := qz391

noncomputable abbrev qz392 := qz600

noncomputable abbrev qz41 := qz392

noncomputable def Ns312p234 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 633237 4000) qz389) qz40 2052508401602173856451 1125899906842624000 164905561835839 36750000000000000000 883835223442851 2251799813685248 200000000441 3528000000000000000 Ns312p225 2052066483990452430951 1125899906842624000 2003866742085193 441000000000000000000 (Ns312p231 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz41 1 4 0 1 883835223442851 562949953421312 200000000441 882000000000000000 883835223442851 2251799813685248 200000000441 3528000000000000000 qz366 Ns312p233 rfl) 

noncomputable def Ns312p235 := @Ns312p220 Ns312p213 Ns312p214 16730101267621966153 Ns312p215 (@Ns312p222 16730101267621966153 Ns312p215 (Ns312p224 (Ns312p234 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 633237 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz601 (Real.log Real.pi) 633237 2000 0 1 38410761 33554432 1 67108864 24323115063357 67108864000 633237 134217728000 (Enclosure.Real.IsNear.const Bool.false 633237 2000) RS313to324.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns312p216 Ns312p217) 

noncomputable def Ns312p236 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz33) Bool.false Ns312p213 Ns312p214 16730101267621966153 Ns312p215 38370826625 33554432 39 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz33) (@HAdd.hAdd Real Real Real qz367 qz37 (Enclosure.sfrac Bool.true Ns312p216 Ns312p217)) Bool.false Ns312p213 Ns312p214 16730101267621966153 Ns312p215 Ns312p218 (Ns312p235 rfl rfl)) 

noncomputable def Ns312p237 := nat_lit 7595999020696931800186880 

noncomputable def Ns312p238 := nat_lit 3511009761781481661744954340519313616283029045574127132704473879603910267322338351733537675183243374882289127868443734930695366951112799601 

noncomputable def Ns312p239 := nat_lit 69061887427279807374175457422696049589758900585025510522285359577850094671315332446731519433112496475662717985575392155893264493730122956800 

noncomputable def Ns312p240 := nat_lit 2503001986745050621330061529846369220544579114785276405505855861213863442551071822037698157752322732189712875022578523001381680838001 

noncomputable def Ns312p241 := nat_lit 17533233415506174299076631949583899031764678628541890179015679805132504455744818337333871758577989642096832770799119143355733350711900501361 

noncomputable def Ns312p242 := nat_lit 2417166059954793258096141009794361735641561520475892868279987585224753313496036635635603180158937376648195129495138725456264257280554303488000 

noncomputable abbrev qz602 := (BSN.sinEvenQ 68719476736)

noncomputable abbrev qz603 := (BSN.sinOddQ 68719476736)

noncomputable def Ns312p243 := BSN.sin_dyadic_bound_f 107945638499 68719476736 4 3 33554432 8828614 Ns312p238 Ns312p239 Ns312p240 Ns312p241 Ns312p242 Ns312p240 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107945638499) qz602 0 3 Ns312p238 Ns312p239 Ns312p240 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107945638499) qz603 0 3 Ns312p241 Ns312p242 Ns312p240 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p244 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz33) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 38370826625) qz368) Bool.false 38370826625 33554432 39 4194304 Bool.false 33554431 33554432 1 4410000 (Ns312p236 rfl) (Enclosure.sfrac_false_div 38370826625 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 38370826625) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns312p237) qz369) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 181 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q3 38370826625 33554432 226375608064910080 72057594037927936 181 Ns312p237 Ns312p99 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554431 33554432 Ns312p237 Ns312p99 107945638499 68719476736 8828614 8820000 (Ns312p243 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns312p245 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz33) Bool.false Ns312p213 Ns312p214 16730101267621966153 Ns312p215 306966613004 268435456 2487 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz33) (@HAdd.hAdd Real Real Real qz367 qz37 (Enclosure.sfrac Bool.true Ns312p216 Ns312p217)) Bool.false Ns312p213 Ns312p214 16730101267621966153 Ns312p215 Ns312p218 (Ns312p235 rfl rfl)) 

noncomputable def Ns312p246 := Ns312p212 55396 BSN.abs_quadSignPos (BSN.cos_quad_nat0 448 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 167578982 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 285 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 48286994 268435456) qz36 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 1) Bool.false 33554431 33554432 11011519 1156055040000 268435448 268435456 2557 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz33)) Bool.false 33554431 33554432 11011519 1156055040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz33) qz33) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz33)) Bool.false 33554431 33554432 176184304 18496880640000 33554431 33554432 11011519 1156055040000 (Ns312p244 rfl rfl) rfl)) rfl) (Ns312p245 rfl) RS313to324.d7 

noncomputable def Ns312p247 := nat_lit 29279508625405980375663628029764155291665714849846166919017789475677761 

noncomputable def Ns312p248 := nat_lit 11257862562157281990393001487162050550817363356867131284906417481281 

noncomputable def Ns312p249 := nat_lit 87816010151093626563010098086318141773895509822824766494483555592070721 

noncomputable def Ns312p250 := BSN.cos_dyadic_bound_f 240675561 268435456 3 2 268435456 134217728 Ns312p247 Ns312p123 Ns312p248 Ns312p249 Ns312p126 Ns312p248 167578982 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 240675561) qz372 0 2 Ns312p247 Ns312p123 Ns312p248 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 240675561) qz373 0 2 Ns312p249 Ns312p126 Ns312p248 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p251 := nat_lit 5556514475505770469068713824256 

noncomputable def Ns312p252 := BSN.sin_dyadic_bound_f 48551272 268435456 2 1 268435456 134217728 Ns312p251 Ns312p115 Ns312p251 Ns312p251 Ns312p116 Ns312p251 48286994 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 48551272) qz370 0 1 Ns312p251 Ns312p115 Ns312p251 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 48551272) qz371 0 1 Ns312p251 Ns312p116 Ns312p251 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p253 := nat_lit 12684309230007273098189593378816 

noncomputable def Ns312p254 := BSN.sin_dyadic_bound_f 59678336 268435456 2 1 268435456 134217728 Ns312p253 Ns312p115 Ns312p253 Ns312p253 Ns312p116 Ns312p253 59187941 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 59678336) qz370 0 1 Ns312p253 Ns312p115 Ns312p253 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 59678336) qz371 0 1 Ns312p253 Ns312p116 Ns312p253 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p255 := nat_lit 37345455441986535876261694560481 

noncomputable def Ns312p256 := BSN.sin_dyadic_bound_f 78173479 268435456 2 1 268435456 134217728 Ns312p255 Ns312p115 Ns312p255 Ns312p255 Ns312p116 Ns312p255 77073193 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 78173479) qz370 0 1 Ns312p255 Ns312p115 Ns312p255 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 78173479) qz371 0 1 Ns312p255 Ns312p116 Ns312p255 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p257 := Ns312p210 94369 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 169 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 59187941 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 79 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 77073193 268435456) qz36 rfl rfl (Ns312p246 RS313to324.d9 RS313to324.d11 RS313to324.d13 RS313to324.d17 (Ns312p250 rfl rfl) (Ns312p252 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns312p245 rfl) RS313to324.d19 RS313to324.d21 RS313to324.d23 RS313to324.d25 RS313to324.d17 (Ns312p254 rfl rfl) (Ns312p256 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns312p258 := nat_lit 109901713635119232474099840023757405317092674508025140282885252195590400 

noncomputable def Ns312p259 := nat_lit 9783225446575624168688766434777683578849446968051522941942878087235502080 

noncomputable def Ns312p260 := nat_lit 48948499580091536103136223555265764161663190336802784624286892073216 

noncomputable def Ns312p261 := nat_lit 287758571473611174945142122366941821736123835689044353375307767448903936 

noncomputable def Ns312p262 := nat_lit 179359133187219776425960717970924198945573194414277920602286098265984204800 

noncomputable def Ns312p263 := BSN.sin_dyadic_bound_f 289212742 268435456 3 2 268435456 134217728 Ns312p258 Ns312p259 Ns312p260 Ns312p261 Ns312p262 Ns312p260 236419171 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 289212742) qz370 0 2 Ns312p258 Ns312p259 Ns312p260 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 289212742) qz371 0 2 Ns312p261 Ns312p262 Ns312p260 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p264 := nat_lit 12034236569411892659765453462297833913288479501877129569805754863517696 

noncomputable def Ns312p265 := nat_lit 1902664251993300415035889491081202389163593214313940228432755490816 

noncomputable def Ns312p266 := nat_lit 36098904379731691378466288607911339335087111319202760828960399079571456 

noncomputable def Ns312p267 := BSN.cos_dyadic_bound_f 192717108 268435456 3 2 268435456 134217728 Ns312p264 Ns312p123 Ns312p265 Ns312p266 Ns312p126 Ns312p265 202177774 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 192717108) qz372 0 2 Ns312p264 Ns312p123 Ns312p265 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 192717108) qz373 0 2 Ns312p266 Ns312p126 Ns312p265 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p268 := Ns312p208 127211 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 5 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 236419171 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 56 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 202177774 268435456) qz36 rfl rfl (Ns312p257 rfl rfl) (Ns312p245 rfl) RS313to324.d27 RS313to324.d29 RS313to324.d31 RS313to324.d33 RS313to324.d17 (Ns312p263 rfl rfl) (Ns312p267 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p269 := nat_lit 1890254221597928698504422413719470716831458913302786241149905274921216 

noncomputable def Ns312p270 := nat_lit 46954937267773259109493129862843732488801898545013455797298913536 

noncomputable def Ns312p271 := nat_lit 5670668754919250548995048254898686463029399136111268696538121226936576 

noncomputable def Ns312p272 := BSN.cos_dyadic_bound_f 121327754 268435456 3 2 268435456 134217728 Ns312p269 Ns312p123 Ns312p270 Ns312p271 Ns312p126 Ns312p270 241480140 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 121327754) qz372 0 2 Ns312p269 Ns312p123 Ns312p270 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 121327754) qz373 0 2 Ns312p271 Ns312p126 Ns312p270 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p273 := nat_lit 15536493126627769469355268837052872504771334047521015449900223948359164253966930104706711162141308185337890625 

noncomputable def Ns312p274 := nat_lit 1366734155965051904054423305441931599391187230368356493611068221591338871835874906091749668121337890625 

noncomputable def Ns312p275 := nat_lit 77648543038877497887890540012164043942969343654291862062347360475004945233137780468286493261307868441337890625 

noncomputable def Ns312p276 := BSN.sin_dyadic_bound_f 324568975 268435456 4 3 268435456 134217728 Ns312p273 Ns312p147 Ns312p274 Ns312p275 Ns312p150 Ns312p274 251068416 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 324568975) qz370 0 3 Ns312p273 Ns312p147 Ns312p274 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 324568975) qz371 0 3 Ns312p275 Ns312p150 Ns312p274 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p277 := Ns312p206 155906 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 110 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 241480140 268435456) BSN.abs_quadSignNeg qz590 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 251068416 268435456) qz36 rfl rfl (Ns312p268 rfl) (Ns312p245 rfl) RS313to324.d35 RS313to324.d37 RS313to324.d39 RS313to324.d41 RS313to324.d17 (Ns312p272 rfl rfl) (Ns312p276 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p278 := nat_lit 975049451277695158724906453408126193938073331877518280529057842375041 

noncomputable def Ns312p279 := nat_lit 12494088051452343818152170843797044665717602518469447198942079361 

noncomputable def Ns312p280 := nat_lit 2925123365656982571487083055882690987724888560427517902692775642966401 

noncomputable def Ns312p281 := BSN.cos_dyadic_bound_f 102822479 268435456 3 2 268435456 134217728 Ns312p278 Ns312p123 Ns312p279 Ns312p280 Ns312p126 Ns312p279 248982316 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 102822479) qz372 0 2 Ns312p278 Ns312p123 Ns312p279 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 102822479) qz373 0 2 Ns312p280 Ns312p126 Ns312p279 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p282 := Ns312p204 Bool.false 174760079 155906 Bool.true 102822479 14148475504056880 1 Bool.false 248982316 Bool.false Bool.false 253495200 169118 BSN.abs_quadSignPos qz374 (BSN.sfrac_eq_quadSignPos_mul Bool.false 248982316 268435456) qz36 rfl (Ns312p277 rfl) (Ns312p245 rfl) RS313to324.d43 RS313to324.d45 RS313to324.d17 (Ns312p281 rfl rfl) rfl 

noncomputable def Ns312p283 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) 253495200 268435456 169118 268435456 253495200 268435456 169118 268435456 136094199211622400 7921725 4194304 84559 67108864 (Ns312p282 rfl rfl rfl rfl) 

noncomputable def Ns312p284 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz34) (Zeta.RiemannSiegel.correction qz35) 10590179 33554432 1 33554432 58678439197395 70368744177664 956680944679567 77581540455874560000 621415174541029383705 2361183241434822606848 

noncomputable def Ns312p285 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz34 1 1 0 1 10590179 33554432 1 33554432 10590179 33554432 1 33554432 

noncomputable abbrev qz42 := qz385

noncomputable def Ns312p286 := @Enclosure.Real.IsNear.sqrt_image qz42 3381709112661 33554432000 633237 33554432000 168427512 168427544 16777216 (@Enclosure.Real.IsNear.of_eq qz42 (@HMul.hMul Real Real Real qz5 qz33 qz3) Bool.false 3381709112661 33554432000 633237 33554432000 (BSN.t_div_two_pi_mk qz33 633237 1000 qz36) (@Enclosure.Real.IsNear.mulLit_ff qz33 qz3 633237 1000 0 1 5340353 33554432 1 33554432 3381709112661 33554432000 633237 33554432000 (Enclosure.Real.IsNear.const Bool.false 633237 1000) RS313to324.d48 rfl)) 

noncomputable abbrev qz723 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 633237 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz604 := qz723

noncomputable abbrev qz393 := qz604

noncomputable abbrev qz43 := qz393

noncomputable def Ns312p287 := @Enclosure.Real.IsNear.sqrt_image qz43 21053441 2097152 1 1048576 53157734 53157740 16777216 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 336855056 33554432 32 33554432 21053441 2097152 1 1048576 (Ns312p286 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns312p288 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz43) 53157737 16777216 3 16777216 5295089 5295090 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz43) Bool.false 106315474 33554432 6 33554432 53157737 16777216 3 16777216 (Ns312p287 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns312p289 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz43)) Bool.false 10590179 33554432 1 33554432 10590179 33554432 1 33554432 (Ns312p288 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz44 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz386))

noncomputable abbrev qz605 := (@HMul.hMul Real Real Real qz711 qz722 qz722)

noncomputable abbrev qz394 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz605 qz598) qz594)

noncomputable abbrev qz45 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz394))

noncomputable def Ns312p290 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz35) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz44) qz45) Bool.false 58678439197395 

noncomputable def Ns312p291 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz44) qz45 17295555 16777216 7 

noncomputable def Ns312p292 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz44) Bool.false 34591110 33554432 224 33554432 17295555 16777216 7 

noncomputable def Ns312p293 := @Enclosure.Real.IsNear.recentre' qz44 Bool.false 16274411 16777216 462187216 73987522560000 16274411 16777216 28886701 4624220160000 

noncomputable abbrev qz46 := (@HMul.hMul Real Real Real qz349 qz346 qz386)

noncomputable def Ns312p294 := @Enclosure.Real.IsNear.cos_image qz46 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8235597) qz368) Bool.false 8235597 33554432 101 16777216 Bool.false 16274411 16777216 1 

noncomputable def Ns312p295 := nat_lit 26986075409395893471024583 

noncomputable def Ns312p296 := nat_lit 4503599627370496000000000000000 

noncomputable def Ns312p297 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz35 884279719003555 140737488355328 1 500000000000000 81921 2097152 1 1048576 72441078860490229155 295147905179352825856 Ns312p295 

noncomputable def Ns312p298 := @Enclosure.Real.IsNear.subLit_ff_p qz43 qz1 21053441 2097152 1 1048576 10 1 0 1 81921 81921 2097152 1 

noncomputable def Ns312p299 := @Ns312p298 1048576 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 336855056 33554432 32 33554432 21053441 2097152 1 1048576 (Ns312p286 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns312p300 := @Enclosure.Real.IsNear.recentre' qz46 Bool.false 72441078860490229155 295147905179352825856 Ns312p295 Ns312p296 8235597 33554432 101 16777216 (@Ns312p297 Ns312p296 RS313to324.d47 (Ns312p299 rfl rfl) rfl) 

noncomputable def Ns312p301 := nat_lit 4600238485433738636315995281 

noncomputable def Ns312p302 := nat_lit 30423614405477505635920876929024 

noncomputable def Ns312p303 := nat_lit 456354216082162584538813153935360 

noncomputable abbrev qz395 := (BSN.cosEvenQ 33554432)

noncomputable def Ns312p304 := BSN.cos_dyadic_bound_f 8235597 33554432 2 1 16777216 4410000 Ns312p301 Ns312p302 Ns312p301 Ns312p301 Ns312p303 Ns312p301 16274411 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 8235597) qz395 0 1 Ns312p301 Ns312p302 Ns312p301 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 8235597) (BSN.cosOddQ 33554432) 0 1 Ns312p301 Ns312p303 Ns312p301 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p305 := @Enclosure.Real.IsNear.inv_image qz44 16274411 16777216 28886701 4624220160000 17295443 17295667 16777216 (Ns312p293 (@Ns312p294 4410000 (Ns312p300 rfl) (Enclosure.sfrac_false_div 8235597 33554432) (Ns312p304 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns312p306 := @Enclosure.Real.IsNear.recentre' qz45 Bool.false 13570756 16777216 

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz349 qz346 qz394)

noncomputable def Ns312p307 := @Enclosure.Real.IsNear.cos_image qz47 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 5272671)) (@Nat.cast Real Real.instNatCast 8388608)) Bool.true 5272671 8388608 

noncomputable def Ns312p308 := nat_lit 389054466105830244685445725 

noncomputable def Ns312p309 := nat_lit 618970019642690137449562112 

noncomputable def Ns312p310 := nat_lit 15253852139359149311878338475463 

noncomputable def Ns312p311 := @Enclosure.Real.IsNear.recentre' qz47 Bool.true Ns312p308 Ns312p309 Ns312p310 

noncomputable def Ns312p312 := nat_lit 2361183241434822606848000000000000000 

noncomputable abbrev qz48 := qz394

noncomputable def Ns312p313 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz48 884279719003555 140737488355328 1 500000000000000 439967645695 

noncomputable abbrev qz396 := (@HSub.hSub Real Real Real qz583 qz605 qz598)

noncomputable abbrev qz49 := qz396

noncomputable def Ns312p314 := @Enclosure.Real.IsNear.subLit_tf qz49 qz29 165089738751 4398046511104 565249 549755813888 1 16 

noncomputable abbrev qz397 := qz605

noncomputable abbrev qz50 := qz397

noncomputable def Ns312p315 := @Enclosure.Real.IsNear.subLit_ff_n qz50 qz35 6711050241 4398046511104 40961 549755813888 81921 2097152 1 1048576 

noncomputable def Ns312p316 := @Enclosure.Real.IsNear.mulLit_ff qz35 qz35 81921 2097152 1 1048576 81921 2097152 1 1048576 6711050241 4398046511104 

noncomputable def Ns312p317 := nat_lit 6430310202271857145090683241692237391815370813164280106241 

noncomputable def Ns312p318 := nat_lit 988643523323402220304136834155207460536120982503085435781120 

noncomputable def Ns312p319 := nat_lit 597372721817995669887090262494940070072421370165218561 

noncomputable def Ns312p320 := nat_lit 19289735861371935443932275544551722295305967596752509881601 

noncomputable def Ns312p321 := nat_lit 44488958549553099913686157536984335724125444212638844610150400 

noncomputable def Ns312p322 := BSN.cos_dyadic_bound_f 5272671 8388608 3 2 16777216 4410000 Ns312p317 Ns312p318 Ns312p319 Ns312p320 Ns312p321 Ns312p319 13570756 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 5272671) (BSN.cosEvenQ 8388608) 0 2 Ns312p317 Ns312p318 Ns312p319 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 5272671) (BSN.cosOddQ 8388608) 0 2 Ns312p320 Ns312p321 Ns312p319 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p323 := @Ns312p306 497467216 73987522560000 3392689 4194304 31091701 4624220160000 (@Ns312p307 109 16777216 Bool.false 13570756 16777216 1 4410000 (@Ns312p311 Ns312p312 5272671 8388608 109 16777216 (@Ns312p313 4398046511104 565249 549755813888 Ns312p308 Ns312p309 Ns312p310 Ns312p312 RS313to324.d47 (@Ns312p314 0 1 7039482331120 439967645695 4398046511104 565249 549755813888 (@Ns312p315 346218275801137152 165089738751 4398046511104 565249 549755813888 (@Ns312p316 40961 549755813888 (Ns312p299 rfl rfl) (Ns312p299 rfl rfl) rfl) (Ns312p299 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 5272671 8388608) (BSN.cos_neg_of_bound 5272671 8388608 Bool.false 13570756 16777216 1 4410000 (Ns312p322 rfl rfl)) rfl rfl) 

noncomputable def Ns312p324 := @Ns312p284 84967636549514873663 Ns312p201 (Ns312p285 qz31 (@Enclosure.Real.IsNear.of_eq qz34 (@Inv.inv Real Real.instInv (Real.sqrt qz43)) Bool.false 10590179 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz42 (BSN.t_div_two_pi_nonneg qz33 633237 1000 qz36)) Ns312p289) rfl) (@Ns312p290 70368744177664 956680944679567 77581540455874560000 (BSN.correction_mk qz35 (BSN.cos_two_pi_p_ne_zero_mk qz33 633237 1000 10 qz36 rfl rfl (@BSN.floor_sqrt_eq_dec qz33 633237 1000 10 qz36 rfl rfl rfl))) (@Ns312p291 1048576 3392689 4194304 31091701 4624220160000 58678439197395 70368744177664 956680944679567 77581540455874560000 (@Ns312p292 1048576 (Ns312p305 rfl rfl rfl rfl rfl) rfl) (Ns312p323 rfl) rfl)) 

noncomputable def Ns312p325 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz33) (hardyZApproximantRS₀ qz33) Bool.false 3838119545225413419495 2361183241434822606848 27419207134084085369663 Ns312p201 (@Eq.refl Real (hardyZApproximantRS₀ qz33)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz33) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz34) (Zeta.RiemannSiegel.correction qz35))) Bool.false 3838119545225413419495 2361183241434822606848 27419207134084085369663 Ns312p201 (BSN.hardyZApproximantRS₀_eq qz33 10 (@BSN.floor_sqrt_eq_dec qz33 633237 1000 10 qz36 rfl rfl rfl)) (@Ns312p203 3838119545225413419495 2361183241434822606848 27419207134084085369663 Ns312p201 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz33) qz33 10)) Bool.false 7921725 4194304 84559 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz33) qz33 10) (Ns312p283 (Ns312p282 rfl rfl rfl rfl) rfl rfl)) (Ns312p324 rfl) rfl rfl)) 

theorem RS313to324.d51 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz33) Bool.false 3838119545225413419495 2361183241434822606848 27419207134084085369663 Ns312p201 := Ns312p325 

noncomputable abbrev qz606 := (@HMul.hMul Real Real Real qz711 (Real.sqrt qz719) qz713)

noncomputable abbrev qz398 := qz606

noncomputable abbrev qz51 := (@Inv.inv Real Real.instInv qz398)

noncomputable abbrev qz399 := (@HMul.hMul Real Real Real qz579 (@HMul.hMul Real Real Real qz579 qz606 qz606) qz606)

noncomputable abbrev qz52 := (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz399))

noncomputable abbrev qz400 := (@HMul.hMul Real Real Real qz579 qz592 qz592)

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz349 qz400 qz376))

noncomputable abbrev qz607 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) qz51)

noncomputable def Ns312p326 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz367 (@HAdd.hAdd Real Real Real qz367 qz607 qz52) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz53)) Bool.false 

noncomputable def Ns312p327 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz367 qz607 qz52) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz53) 21072601 1073741824 

noncomputable def Ns312p328 := @Enclosure.Real.IsNear.addLit_ff qz607 qz52 2634075 134217728 25 134217728 

noncomputable def Ns312p329 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) qz51 25 4 0 1 105363 33554432 1 33554432 2634075 

noncomputable def Ns312p330 := @Enclosure.Real.IsNear.recentre' qz51 Bool.false 105363 33554432 1 33554432 105363 33554432 1 33554432 

noncomputable def Ns312p331 := @Enclosure.Real.IsNear.mulLit_ff qz22 qz19 26564565 8388608 3 16777216 26995484415 268435456 5055 268435456 717123300448754475 2251799813685248 21847138785 

noncomputable def Ns312p332 := @Enclosure.Real.IsNear.sqrt_image qz19 26995484415 268435456 5055 268435456 168246283 168246315 16777216 qz20 

noncomputable def Ns312p333 := @Enclosure.Real.IsNear.sqrt_image qz21 168246299 16777216 1 1048576 53129127 53129133 16777216 (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 336492598 33554432 32 33554432 168246299 16777216 1 1048576 (Ns312p332 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz401 := (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 106258260 33554432 6 33554432 26564565 8388608 3 16777216 (Ns312p333 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns312p334 := @Ns312p331 281474976710656 qz401 

noncomputable def Ns312p335 := Ns312p334 qz20 

noncomputable abbrev qz54 := qz398

noncomputable def Ns312p336 := @Enclosure.Real.IsNear.inv_image qz54 717123300448754475 2251799813685248 21847138785 281474976710656 52681 52682 16777216 (Ns312p335 rfl) rfl rfl 

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv qz399)

noncomputable def Ns312p337 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz55 1 32 0 1 1 

noncomputable def Ns312p338 := @Enclosure.Real.IsNear.recentre' qz55 Bool.false 1 33554432 1 33554432 

noncomputable def Ns312p339 := nat_lit 368792007916728180930117662133493206532873649770921875 

noncomputable def Ns312p340 := nat_lit 11417981541647679048466287755595961091061972992 

noncomputable def Ns312p341 := nat_lit 33705718967893456546899586725536717947184905875 

noncomputable def Ns312p342 := nat_lit 1427247692705959881058285969449495136382746624 

noncomputable abbrev qz56 := qz399

noncomputable def Ns312p343 := @Enclosure.Real.IsNear.inv_image qz56 Ns312p339 Ns312p340 Ns312p341 Ns312p342 0 1 

noncomputable def Ns312p344 := nat_lit 514265828046514580204915578832525625 

noncomputable def Ns312p345 := nat_lit 5070602400912917605986812821504 

noncomputable def Ns312p346 := nat_lit 15667094180051084159919917775 

noncomputable def Ns312p347 := nat_lit 316912650057057350374175801344 

noncomputable abbrev qz402 := (@HMul.hMul Real Real Real qz579 qz606 qz606)

noncomputable abbrev qz57 := qz402

noncomputable def Ns312p348 := @Enclosure.Real.IsNear.mulLit_ff qz57 qz54 Ns312p344 Ns312p345 Ns312p346 Ns312p347 717123300448754475 2251799813685248 21847138785 

noncomputable def Ns312p349 := @Enclosure.Real.IsNear.mulLit_ff qz54 qz54 717123300448754475 2251799813685248 21847138785 281474976710656 717123300448754475 2251799813685248 21847138785 281474976710656 Ns312p344 

noncomputable def Ns312p350 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz53 13 10 0 1 528301 16777216 1 

noncomputable def Ns312p351 := @Enclosure.Real.IsNear.recentre' qz53 Bool.false 1056602 33554432 2 33554432 528301 16777216 

noncomputable abbrev qz58 := qz400

noncomputable def Ns312p352 := @Enclosure.Real.IsNear.mulLit_ff qz58 qz22 705676113639225 70368744177664 318774789 281474976710656 26564565 8388608 3 16777216 18745978989716579062125 

noncomputable def Ns312p353 := @Enclosure.Real.IsNear.mulLit_ff qz22 qz22 26564565 8388608 3 16777216 26564565 8388608 3 16777216 705676113639225 70368744177664 318774789 

noncomputable def Ns312p354 := @Ns312p353 281474976710656 qz401 

noncomputable def Ns312p355 := Ns312p354 qz401 

noncomputable def Ns312p356 := @Ns312p352 590295810358705651712 25404341525498637 4722366482869645213696 (Ns312p355 rfl) qz401 

noncomputable abbrev qz59 := (@HMul.hMul Real Real Real qz349 qz400 qz376)

noncomputable def Ns312p357 := @Enclosure.Real.IsNear.inv_image qz59 18745978989716579062125 590295810358705651712 25404341525498637 4722366482869645213696 528300 528302 16777216 (Ns312p356 rfl) 

noncomputable def Ns312p358 := @Ns312p327 201 1073741824 6867913 167772160 13 167772160 10909761218281472 325136221 5368709120 1421 5368709120 (@Ns312p328 1 1073741824 1 1073741824 2828316629270528 21072601 1073741824 201 1073741824 (@Ns312p329 134217728 25 134217728 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns312p330 (Ns312p336 rfl rfl rfl rfl) rfl) rfl) (@Ns312p337 33554432 1 33554432 1 1073741824 1 1073741824 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns312p338 1 33554432 1 33554432 (@Ns312p343 16777216 (@Ns312p348 281474976710656 Ns312p339 Ns312p340 Ns312p341 Ns312p342 (@Ns312p349 Ns312p345 Ns312p346 Ns312p347 (Ns312p335 rfl) (Ns312p335 rfl) rfl) (Ns312p335 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns312p350 16777216 6867913 167772160 13 167772160 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns312p351 1 16777216 (Ns312p357 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS313to324.d52 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 := @Ns312p326 325136221 5368709120 1421 5368709120 (BSN.hardyZErrorBoundRS₀_mk qz4 631875 1000 qz9 rfl rfl) (Ns312p358 rfl rfl) 

noncomputable def Ns312p359 := nat_lit 23242897532874035036160000 

noncomputable def Ns312p360 := nat_lit 1803281093925981176480036552704 

noncomputable abbrev qz724 := (Enclosure.sfrac Bool.false 634599 1000)

noncomputable abbrev qz608 := qz724

noncomputable abbrev qz403 := qz608

noncomputable abbrev qz60 := qz403

noncomputable abbrev qz725 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 634599 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz609 := qz725

noncomputable abbrev qz404 := qz609

noncomputable abbrev qz61 := (@HPow.hPow Real Real Real qz350 qz404 qz352)

noncomputable abbrev qz726 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 634599 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz610 := qz726

noncomputable abbrev qz405 := qz610

noncomputable abbrev qz62 := qz405

noncomputable def Ns312p361 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz61) (Zeta.RiemannSiegel.correction qz62)) 729405227 134217728 42369 33554432 603658674051006043161 2361183241434822606848 92946318113086559809 Ns312p359 Ns312p360 

noncomputable def Ns312p362 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.cos BSN.quadSignPos 9 10 634599 1000 200 268435456 134217728 4503599627370496 Bool.false 307810080914 2492 618095470 62 84886744 8 

noncomputable def Ns312p363 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 634599 1000 110 157 268435456 134217728 4503599627370496 Bool.false 307810080914 2492 

noncomputable def Ns312p364 := Ns312p363 558195838 62 94906264 8 589812974 62 89478488 8 Bool.true 636341546 127478 Bool.true 38122575 Bool.true 284426335 14148475504056880 1 Bool.false 265732963 Bool.true Bool.false 234114778 Bool.true Bool.true 808330597 

noncomputable def Ns312p365 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 634599 1000 6 56 268435456 134217728 4503599627370496 Bool.false 307810080914 2492 

noncomputable def Ns312p366 := Ns312p365 480971758 62 109588312 8 522351262 62 101459064 8 Bool.true 628001060 94565 Bool.false 55939689 Bool.true 60691617 14148475504056880 1 Bool.false 262627838 Bool.true Bool.false 261603631 Bool.false Bool.true 636341546 

noncomputable def Ns312p367 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 634599 1000 169 79 268435456 134217728 4503599627370496 Bool.false 307810080914 2492 

noncomputable def Ns312p368 := Ns312p367 372130544 61 134217720 8 432030192 61 120047984 16 Bool.true 607972640 55509 Bool.false 396304445 Bool.false 333216267 14148475504056880 1 Bool.false 267239086 Bool.true Bool.false 253997460 Bool.false Bool.true 628001060 

noncomputable def Ns312p369 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz60) qz60 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 634599 1000 449 286 268435456 134217728 4503599627370496 Bool.false 307810080914 2492 

noncomputable def Ns312p370 := Ns312p369 186065264 61 189812528 16 294906480 61 154981288 8 Bool.true 268435408 2557 Bool.false 409065153 Bool.false 68699128 14148475504056880 1 Bool.false 268140159 Bool.true Bool.false 259692448 Bool.true Bool.true 607972640 

noncomputable def Ns312p371 := nat_lit 3372871876862374689280389232685512437454873905985164877 

noncomputable def Ns312p372 := nat_lit 2941418934707566547609935228770266952353633492008960 

noncomputable def Ns312p373 := nat_lit 49401352304568155411886851039520000 

noncomputable def Ns312p374 := nat_lit 188100347119530645503640308354906114880 

noncomputable abbrev qz611 := (@Eq.refl Real qz724)

noncomputable abbrev qz406 := qz611

noncomputable abbrev qz63 := qz406

noncomputable def Ns312p375 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz60 634599 1000 1610864563204 16000000 1269198 4000 2000 Ns312p373 Ns312p374 qz63 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns312p376 := nat_lit 9713871005363639105127520990134275819870036849237274845760 

noncomputable abbrev qz612 := (@HSub.hSub Real Real Real qz715 qz716 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz717 (@Nat.cast Real Real.instNatCast 1269198))))

noncomputable abbrev qz407 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 634599 4000) (Real.log (Enclosure.sfrac Bool.false 1610864563204 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz612))

noncomputable abbrev qz613 := (Enclosure.sfrac Bool.false 634599 2000)

noncomputable abbrev qz64 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz407 qz613) (@HMul.hMul Real Real Real qz349 qz613 (Real.log Real.pi)))

noncomputable def Ns312p377 := @Enclosure.Real.IsNear.addLit_ft_p qz64 (Enclosure.sfrac Bool.true Ns312p373 Ns312p374) 51641973972700640077 45035996273704960 16765865016623040931 Ns312p215 Ns312p373 Ns312p374 0 1 Ns312p376 

noncomputable def Ns312p378 := nat_lit 86640855200637674191008563200000 

noncomputable abbrev qz65 := (@HSub.hSub Real Real Real qz355 qz407 qz613)

noncomputable def Ns312p379 := @Enclosure.Real.IsNear.subLit_ff_p qz65 (@HMul.hMul Real Real Real qz5 qz613 (Real.log Real.pi)) 1700001212241847190149 1125899906842624000 2008122994487761 441000000000000000000 24375430519839 67108864000 634599 134217728000 Ns312p378 51641973972700640077 45035996273704960 

noncomputable def Ns312p380 := nat_lit 3400002424483694380298000 

noncomputable abbrev qz66 := qz407

noncomputable def Ns312p381 := @Enclosure.Real.IsNear.subLit_ff_p qz66 qz613 2057248689733058364037 1125899906842624000 2008122994487761 441000000000000000000 634599 2000 0 1 Ns312p380 1700001212241847190149 1125899906842624000 2008122994487761 441000000000000000000 

noncomputable def Ns312p382 := nat_lit 4632512216245121394198801302920626176 

noncomputable def Ns312p383 := nat_lit 55705816529316162297659392 

noncomputable def Ns312p384 := nat_lit 183961685182576069846126543430530604704611858459107083587231030391259458035287960783045462231789423600607165800661817407984107520 

noncomputable def Ns312p385 := nat_lit 2817177993695130866733255429315799991296472877834279912353969870946436775284244206502187653667472311419501350410519409987682304 

noncomputable def Ns312p386 := nat_lit 2985549734202447238178277522678504375612670178722431366038420166157717049831598892510285387338287817708672486275489464320 

noncomputable def Ns312p387 := BSN.log_dyadic_bound 562288563204 2659440563204 6 5 Ns312p384 134217728 35280000 Ns312p385 Ns312p386 57624767 3221729126408 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 562288563204) (BSN.artanhQ 2659440563204) 0 5 Ns312p385 Ns312p384 Ns312p386 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz408 := (Real.log (Enclosure.sfrac Bool.false 1610864563204 16000000))

noncomputable def Ns312p388 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 634599 4000) qz408 634599 4000 0 1 3242505279446263 281474976710656 781250441 27562500000000000 2057690607831319053537 1125899906842624000 1124219384599 250000000000000000 (Enclosure.Real.IsNear.const Bool.false 634599 4000) (BSN.isNear_log_sfrac 1610864563204 16000000 3242505279446263 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1610864563204) qz358)) Bool.false Ns312p383 Ns312p99 1000000564480000 35280000000000000000000 3242505279446263 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1610864563204 16000000 16 3221729126408 2097152000000 57624767 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns312p387 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns312p389 := BSN.arctan_dyadic_bound_f 1000 1269198 1 0 16777216 4410000 0 1 1 0 1 1 13218 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1269198) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1269198) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz409 := (@Nat.cast Real Real.instNatCast 1269198)

noncomputable def Ns312p390 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz409)) 884279719003555 562949953421312 1 2000000000000000 13218 16777216 1 4410000 14828310777657624100864 883836196521379 562949953421312 200000000441 882000000000000000 qz15 (Ns312p389 rfl) rfl rfl 

noncomputable abbrev qz410 := (@HMul.hMul Real Real Real qz579 qz584 qz612)

noncomputable abbrev qz67 := qz410

noncomputable abbrev qz411 := qz612

noncomputable abbrev qz68 := qz411

noncomputable def Ns312p391 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 634599 4000) qz408) qz67 2057690607831319053537 1125899906842624000 1124219384599 250000000000000000 883836196521379 2251799813685248 200000000441 3528000000000000000 Ns312p382 2057248689733058364037 1125899906842624000 2008122994487761 441000000000000000000 (Ns312p388 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz68 1 4 0 1 883836196521379 562949953421312 200000000441 882000000000000000 883836196521379 2251799813685248 200000000441 3528000000000000000 qz366 Ns312p390 rfl) 

noncomputable def Ns312p392 := @Ns312p377 Ns312p371 Ns312p372 16765865016623040931 Ns312p215 (@Ns312p379 16765865016623040931 Ns312p215 (Ns312p381 (Ns312p391 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 634599 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz613 (Real.log Real.pi) 634599 2000 0 1 38410761 33554432 1 67108864 24375430519839 67108864000 634599 134217728000 (Enclosure.Real.IsNear.const Bool.false 634599 2000) RS313to324.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns312p373 Ns312p374) 

noncomputable def Ns312p393 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz60) Bool.false Ns312p371 Ns312p372 16765865016623040931 Ns312p215 19238130057 16777216 39 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz60) (@HAdd.hAdd Real Real Real qz367 qz64 (Enclosure.sfrac Bool.true Ns312p373 Ns312p374)) Bool.false Ns312p371 Ns312p372 16765865016623040931 Ns312p215 Ns312p375 (Ns312p392 rfl rfl)) 

noncomputable def Ns312p394 := nat_lit 2417851639229258349412352 

noncomputable def Ns312p395 := BSN.cos_dyadic_bound_f 40519063 68719476736 1 0 33554432 8828614 0 1 1 0 1 1 33554426 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 40519063) (BSN.cosEvenQ 68719476736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 40519063) (BSN.cosOddQ 68719476736) 0 0 rfl) rfl rfl 

noncomputable abbrev qz614 := (@Nat.cast Real Real.instNatCast Ns312p394)

noncomputable def Ns312p396 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz60) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 19238130057) qz378) Bool.false 19238130057 16777216 39 4194304 Bool.true 33554426 33554432 1 4410000 (Ns312p393 rfl) (Enclosure.sfrac_false_div 19238130057 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 19238130057) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1425637803791224930304) qz614) 226375608064910080 72057594037927936 Bool.false 33554426 33554432 182 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q2 19238130057 16777216 226375608064910080 72057594037927936 182 1425637803791224930304 Ns312p394 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554426 33554432 1425637803791224930304 Ns312p394 40519063 68719476736 8828614 8820000 (Ns312p395 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns312p397 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz60) Bool.false Ns312p371 Ns312p372 16765865016623040931 Ns312p215 307810080914 268435456 2492 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz60) (@HAdd.hAdd Real Real Real qz367 qz64 (Enclosure.sfrac Bool.true Ns312p373 Ns312p374)) Bool.false Ns312p371 Ns312p372 16765865016623040931 Ns312p215 Ns312p375 (Ns312p392 rfl rfl)) 

noncomputable def Ns312p398 := Ns312p370 55509 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 449 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268140159 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 286 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 259692448 268435456) qz63 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 1) Bool.true 16777213 16777216 11011519 1156055040000 268435408 268435456 2557 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz60)) Bool.true 16777213 16777216 11011519 1156055040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz60) qz60) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz60)) Bool.true 33554426 33554432 176184304 18496880640000 16777213 16777216 11011519 1156055040000 (Ns312p396 rfl rfl) rfl)) rfl) (Ns312p397 rfl) RS313to324.d7 

noncomputable def Ns312p399 := nat_lit 39242988817630679218942190102736237797289936202765094576697921466190766673454090612516462524556706015180304641 

noncomputable def Ns312p400 := nat_lit 21953805810038957353849211983419901155099467589512262476856259661937762769288887315484387067926142071041 

noncomputable def Ns312p401 := nat_lit 195998931282667477700335048118146436725791529919025523770393641929008547346199240241590436937203083815945580801 

noncomputable def Ns312p402 := BSN.sin_dyadic_bound_f 409065153 268435456 4 3 268435456 134217728 Ns312p399 Ns312p147 Ns312p400 Ns312p401 Ns312p150 Ns312p400 268140159 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 409065153) qz370 0 3 Ns312p399 Ns312p147 Ns312p400 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 409065153) qz371 0 3 Ns312p401 Ns312p150 Ns312p400 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p403 := nat_lit 22274342759084414358865953427456 

noncomputable def Ns312p404 := BSN.cos_dyadic_bound_f 68699128 268435456 2 1 268435456 134217728 Ns312p403 Ns312p119 Ns312p403 Ns312p403 Ns312p120 Ns312p403 259692448 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 68699128) qz372 0 1 Ns312p403 Ns312p119 Ns312p403 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 68699128) qz373 0 1 Ns312p403 Ns312p120 Ns312p403 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p405 := nat_lit 34563347685070468308031908939504423201405247016136292913981736296476969072983327389184181545838632974441040625 

noncomputable def Ns312p406 := nat_lit 15008846693004791959813290286373465987787837297657503129578337284130564012593704900769880106914306640625 

noncomputable def Ns312p407 := nat_lit 172649109042888937413516351453188680031194361548017990521374714008191595680360416318967631662452752830978640625 

noncomputable def Ns312p408 := BSN.sin_dyadic_bound_f 396304445 268435456 4 3 268435456 134217728 Ns312p405 Ns312p147 Ns312p406 Ns312p407 Ns312p150 Ns312p406 267239086 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 396304445) qz370 0 3 Ns312p405 Ns312p147 Ns312p406 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 396304445) qz371 0 3 Ns312p407 Ns312p150 Ns312p406 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p409 := nat_lit 17260913892934053477703794456706411132892100019100270815540968901271116656893009861280499861352836733139631761 

noncomputable def Ns312p410 := nat_lit 1873761608469117409660639343069443548570807675979671593368829821137276559868709703808875006245272239761 

noncomputable def Ns312p411 := nat_lit 86262704536947458585572604153615108129661514692607908610311736434566282616449392092613975252437568071266418321 

noncomputable def Ns312p412 := BSN.sin_dyadic_bound_f 333216267 268435456 4 3 268435456 134217728 Ns312p409 Ns312p147 Ns312p410 Ns312p411 Ns312p150 Ns312p410 253997460 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 333216267) qz370 0 3 Ns312p409 Ns312p147 Ns312p410 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 333216267) qz371 0 3 Ns312p411 Ns312p150 Ns312p410 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p413 := Ns312p368 94565 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 169 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 267239086 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 79 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 253997460 268435456) qz63 rfl rfl (Ns312p398 RS313to324.d9 RS313to324.d11 RS313to324.d13 RS313to324.d17 (Ns312p402 rfl rfl) (Ns312p404 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns312p397 rfl) RS313to324.d19 RS313to324.d21 RS313to324.d23 RS313to324.d25 RS313to324.d17 (Ns312p408 rfl rfl) (Ns312p412 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns312p414 := nat_lit 9792198086201975407710466391841 

noncomputable def Ns312p415 := BSN.cos_dyadic_bound_f 55939689 268435456 2 1 268435456 134217728 Ns312p414 Ns312p119 Ns312p414 Ns312p414 Ns312p120 Ns312p414 262627838 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 55939689) qz372 0 1 Ns312p414 Ns312p119 Ns312p414 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 55939689) qz373 0 1 Ns312p414 Ns312p120 Ns312p414 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p416 := nat_lit 13567968730571425612288950446721 

noncomputable def Ns312p417 := BSN.cos_dyadic_bound_f 60691617 268435456 2 1 268435456 134217728 Ns312p416 Ns312p119 Ns312p416 Ns312p416 Ns312p120 Ns312p416 261603631 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 60691617) qz372 0 1 Ns312p416 Ns312p119 Ns312p416 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 60691617) qz373 0 1 Ns312p416 Ns312p120 Ns312p416 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p418 := Ns312p366 127478 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 6 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 262627838 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 56 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 261603631 268435456) qz63 rfl rfl (Ns312p413 rfl rfl) (Ns312p397 rfl) RS313to324.d27 RS313to324.d29 RS313to324.d31 RS313to324.d33 RS313to324.d17 (Ns312p415 rfl rfl) (Ns312p417 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p419 := nat_lit 2112170195155377552042687890625 

noncomputable def Ns312p420 := BSN.cos_dyadic_bound_f 38122575 268435456 2 1 268435456 134217728 Ns312p419 Ns312p119 Ns312p419 Ns312p419 Ns312p120 Ns312p419 265732963 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 38122575) qz372 0 1 Ns312p419 Ns312p119 Ns312p419 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 38122575) qz373 0 1 Ns312p419 Ns312p120 Ns312p419 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p421 := nat_lit 102801985456969022711365429028830046937156584164017685736761803683130625 

noncomputable def Ns312p422 := nat_lit 42831022417406936653584203447814270986761712779820363918044312890625 

noncomputable def Ns312p423 := nat_lit 269173949779576400632327463508020328396669630037450420149937414092090625 

noncomputable def Ns312p424 := BSN.sin_dyadic_bound_f 284426335 268435456 3 2 268435456 134217728 Ns312p421 Ns312p259 Ns312p422 Ns312p423 Ns312p262 Ns312p422 234114778 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 284426335) qz370 0 2 Ns312p421 Ns312p259 Ns312p422 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 284426335) qz371 0 2 Ns312p423 Ns312p262 Ns312p422 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p425 := Ns312p364 156235 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 110 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 265732963 268435456) BSN.abs_quadSignNeg qz590 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 234114778 268435456) qz63 rfl rfl (Ns312p418 rfl) (Ns312p397 rfl) RS313to324.d35 RS313to324.d37 RS313to324.d39 RS313to324.d41 RS313to324.d17 (Ns312p420 rfl rfl) (Ns312p424 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p426 := nat_lit 914968937786573791202368818227705448101372011678187222917460587964481 

noncomputable def Ns312p427 := nat_lit 11001823277409929834826873533500417784962863615007689643424475201 

noncomputable def Ns312p428 := nat_lit 2744884809713166553747436800936049343468546109307331653373094914943041 

noncomputable def Ns312p429 := BSN.cos_dyadic_bound_f 101200599 268435456 3 2 268435456 134217728 Ns312p426 Ns312p123 Ns312p427 Ns312p428 Ns312p126 Ns312p427 249583938 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 101200599) qz372 0 2 Ns312p426 Ns312p123 Ns312p427 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 101200599) qz373 0 2 Ns312p428 Ns312p126 Ns312p427 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p430 := Ns312p362 Bool.true 808330597 156235 Bool.true 101200599 14148475504056880 1 Bool.false 249583938 Bool.false Bool.true 729405227 169476 BSN.abs_quadSignPos qz374 (BSN.sfrac_eq_quadSignPos_mul Bool.false 249583938 268435456) qz63 rfl (Ns312p425 rfl) (Ns312p397 rfl) RS313to324.d43 RS313to324.d45 RS313to324.d17 (Ns312p429 rfl rfl) rfl 

noncomputable def Ns312p431 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) 729405227 268435456 169476 268435456 729405227 268435456 169476 268435456 391596449437057024 729405227 134217728 42369 33554432 (Ns312p430 rfl rfl rfl rfl) 

noncomputable def Ns312p432 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz61) (Zeta.RiemannSiegel.correction qz62) 2646123 8388608 1 16777216 228129483796107 281474976710656 138804546817301 11083077207982080000 603658674051006043161 2361183241434822606848 

noncomputable def Ns312p433 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz61 1 1 0 1 2646123 8388608 1 16777216 2646123 8388608 1 16777216 

noncomputable abbrev qz69 := qz404

noncomputable def Ns312p434 := @Enclosure.Real.IsNear.sqrt_image qz69 3388982673447 33554432000 634599 33554432000 168608546 168608578 16777216 (@Enclosure.Real.IsNear.of_eq qz69 (@HMul.hMul Real Real Real qz5 qz60 qz3) Bool.false 3388982673447 33554432000 634599 33554432000 (BSN.t_div_two_pi_mk qz60 634599 1000 qz63) (@Enclosure.Real.IsNear.mulLit_ff qz60 qz3 634599 1000 0 1 5340353 33554432 1 33554432 3388982673447 33554432000 634599 33554432000 (Enclosure.Real.IsNear.const Bool.false 634599 1000) RS313to324.d48 rfl)) 

noncomputable abbrev qz727 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 634599 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz615 := qz727

noncomputable abbrev qz412 := qz615

noncomputable abbrev qz70 := qz412

noncomputable def Ns312p435 := @Enclosure.Real.IsNear.sqrt_image qz70 84304281 8388608 1 1048576 53186295 53186301 16777216 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 337217124 33554432 32 33554432 84304281 8388608 1 1048576 (Ns312p434 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns312p436 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz70) 26593149 8388608 3 16777216 5292245 5292247 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz70) Bool.false 106372596 33554432 6 33554432 26593149 8388608 3 16777216 (Ns312p435 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns312p437 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz70)) Bool.false 10584492 33554432 2 33554432 2646123 8388608 1 16777216 (Ns312p436 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz71 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz405))

noncomputable abbrev qz616 := (@HMul.hMul Real Real Real qz711 qz726 qz726)

noncomputable abbrev qz413 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz616 qz610) qz594)

noncomputable abbrev qz72 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz413))

noncomputable def Ns312p438 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz62) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz71) qz72) Bool.false 228129483796107 

noncomputable def Ns312p439 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz71) qz72 17635341 16777216 29 

noncomputable def Ns312p440 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz71) Bool.false 35270682 33554432 232 33554432 17635341 16777216 29 

noncomputable def Ns312p441 := @Enclosure.Real.IsNear.recentre' qz71 Bool.false 15960847 16777216 462187216 73987522560000 15960847 16777216 28886701 4624220160000 

noncomputable abbrev qz73 := (@HMul.hMul Real Real Real qz349 qz346 qz405)

noncomputable def Ns312p442 := @Enclosure.Real.IsNear.cos_image qz73 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10510537) qz368) Bool.false 10510537 33554432 101 16777216 Bool.false 15960847 16777216 1 

noncomputable def Ns312p443 := nat_lit 26986075409493085359707591 

noncomputable def Ns312p444 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz62 884279719003555 140737488355328 1 500000000000000 418201 8388608 1 1048576 369806662767005704555 1180591620717411303424 Ns312p443 

noncomputable def Ns312p445 := @Enclosure.Real.IsNear.subLit_ff_p qz70 qz1 84304281 8388608 1 1048576 10 1 0 1 418201 418201 8388608 1 

noncomputable def Ns312p446 := @Ns312p445 1048576 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 337217124 33554432 32 33554432 84304281 8388608 1 1048576 (Ns312p434 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns312p447 := @Enclosure.Real.IsNear.recentre' qz73 Bool.false 369806662767005704555 1180591620717411303424 Ns312p443 Ns312p296 10510537 33554432 101 16777216 (@Ns312p444 Ns312p296 RS313to324.d47 (Ns312p446 rfl rfl) rfl) 

noncomputable def Ns312p448 := nat_lit 12203927572914469613148800161 

noncomputable def Ns312p449 := BSN.cos_dyadic_bound_f 10510537 33554432 2 1 16777216 4410000 Ns312p448 Ns312p302 Ns312p448 Ns312p448 Ns312p303 Ns312p448 15960847 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 10510537) qz395 0 1 Ns312p448 Ns312p302 Ns312p448 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 10510537) (BSN.cosOddQ 33554432) 0 1 Ns312p448 Ns312p303 Ns312p448 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p450 := @Enclosure.Real.IsNear.inv_image qz71 15960847 16777216 28886701 4624220160000 17635225 17635457 16777216 (Ns312p441 (@Ns312p442 4410000 (Ns312p447 rfl) (Enclosure.sfrac_false_div 10510537 33554432) (Ns312p449 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns312p451 := @Enclosure.Real.IsNear.recentre' qz72 Bool.false 12935927 16777216 

noncomputable abbrev qz74 := (@HMul.hMul Real Real Real qz349 qz346 qz413)

noncomputable def Ns312p452 := @Enclosure.Real.IsNear.cos_image qz74 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 23163345)) qz368) Bool.true 23163345 33554432 

noncomputable def Ns312p453 := nat_lit 6836612946568392191748078605 

noncomputable def Ns312p454 := nat_lit 9903520314283042199192993792 

noncomputable def Ns312p455 := nat_lit 24894703140609007939803553933007 

noncomputable def Ns312p456 := @Enclosure.Real.IsNear.recentre' qz74 Bool.true Ns312p453 Ns312p454 Ns312p455 

noncomputable def Ns312p457 := nat_lit 3777893186295716170956800000000000000 

noncomputable abbrev qz75 := qz413

noncomputable def Ns312p458 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz75 884279719003555 140737488355328 1 500000000000000 7731278688911 

noncomputable abbrev qz414 := (@HSub.hSub Real Real Real qz583 qz616 qz610)

noncomputable abbrev qz76 := qz414

noncomputable def Ns312p459 := @Enclosure.Real.IsNear.subLit_tf qz76 qz29 3333232177807 70368744177664 4612509 4398046511104 1 16 

noncomputable abbrev qz415 := qz616

noncomputable abbrev qz77 := qz415

noncomputable def Ns312p460 := @Enclosure.Real.IsNear.subLit_ff_n qz77 qz62 174892076401 70368744177664 418205 4398046511104 418201 8388608 1 1048576 

noncomputable def Ns312p461 := @Enclosure.Real.IsNear.mulLit_ff qz62 qz62 418201 8388608 1 1048576 418201 8388608 1 1048576 174892076401 70368744177664 

noncomputable def Ns312p462 := nat_lit 613158358232500640068233277611666930996966518401022657963690625 

noncomputable def Ns312p463 := nat_lit 64791741944522487909851911563195676133695224709322207119351480320 

noncomputable def Ns312p464 := nat_lit 82872455210394261351363941225347616373752954065828062890625 

noncomputable def Ns312p465 := nat_lit 1839309329787081131681997104952550097758152049294936317765290625 

noncomputable def Ns312p466 := nat_lit 2915628387503511955943336020343805426016285111919499320370816614400 

noncomputable def Ns312p467 := BSN.cos_dyadic_bound_f 23163345 33554432 3 2 16777216 4410000 Ns312p462 Ns312p463 Ns312p464 Ns312p465 Ns312p466 Ns312p464 12935927 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 23163345) qz395 0 2 Ns312p462 Ns312p463 Ns312p464 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 23163345) (BSN.cosOddQ 33554432) 0 2 Ns312p465 Ns312p466 Ns312p464 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p468 := @Ns312p451 506287216 73987522560000 12935927 16777216 31642951 4624220160000 (@Ns312p452 111 16777216 Bool.false 12935927 16777216 1 4410000 (@Ns312p456 Ns312p457 23163345 33554432 111 16777216 (@Ns312p458 70368744177664 4612509 4398046511104 Ns312p453 Ns312p454 Ns312p455 Ns312p457 RS313to324.d47 (@Ns312p459 0 1 123700459022576 7731278688911 70368744177664 4612509 4398046511104 (@Ns312p460 27961178112609222656 3333232177807 70368744177664 4612509 4398046511104 (@Ns312p461 418205 4398046511104 (Ns312p446 rfl rfl) (Ns312p446 rfl rfl) rfl) (Ns312p446 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 23163345 33554432) (BSN.cos_neg_of_bound 23163345 33554432 Bool.false 12935927 16777216 1 4410000 (Ns312p467 rfl rfl)) rfl rfl) 

noncomputable def Ns312p469 := @Ns312p432 92946318113086559809 Ns312p359 (Ns312p433 qz31 (@Enclosure.Real.IsNear.of_eq qz61 (@Inv.inv Real Real.instInv (Real.sqrt qz70)) Bool.false 2646123 8388608 1 16777216 (BSN.rpow_neg_quarter_mk qz69 (BSN.t_div_two_pi_nonneg qz60 634599 1000 qz63)) Ns312p437) rfl) (@Ns312p438 281474976710656 138804546817301 11083077207982080000 (BSN.correction_mk qz62 (BSN.cos_two_pi_p_ne_zero_mk qz60 634599 1000 10 qz63 rfl rfl (@BSN.floor_sqrt_eq_dec qz60 634599 1000 10 qz63 rfl rfl rfl))) (@Ns312p439 4194304 12935927 16777216 31642951 4624220160000 228129483796107 281474976710656 138804546817301 11083077207982080000 (@Ns312p440 4194304 (Ns312p450 rfl rfl rfl rfl rfl) rfl) (Ns312p468 rfl) rfl)) 

noncomputable def Ns312p470 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz60) (hardyZApproximantRS₀ qz60) Bool.true 13435491129204490605593 2361183241434822606848 29441627457175133279809 Ns312p359 (@Eq.refl Real (hardyZApproximantRS₀ qz60)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz60) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz61) (Zeta.RiemannSiegel.correction qz62))) Bool.true 13435491129204490605593 2361183241434822606848 29441627457175133279809 Ns312p359 (BSN.hardyZApproximantRS₀_eq qz60 10 (@BSN.floor_sqrt_eq_dec qz60 634599 1000 10 qz63 rfl rfl rfl)) (@Ns312p361 13435491129204490605593 2361183241434822606848 29441627457175133279809 Ns312p359 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz60) qz60 10)) Bool.true 729405227 134217728 42369 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz60) qz60 10) (Ns312p431 (Ns312p430 rfl rfl rfl rfl) rfl rfl)) (Ns312p469 rfl) rfl rfl)) 

theorem RS313to324.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz60) Bool.true 13435491129204490605593 2361183241434822606848 29441627457175133279809 Ns312p359 := Ns312p470 

noncomputable def Ns312p471 := nat_lit 6941878729818378464133120 

noncomputable def Ns312p472 := nat_lit 1698257999110294909054921736192 

noncomputable abbrev qz728 := (Enclosure.sfrac Bool.false 636640 1000)

noncomputable abbrev qz617 := qz728

noncomputable abbrev qz416 := qz617

noncomputable abbrev qz78 := qz416

noncomputable abbrev qz729 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 636640 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz618 := qz729

noncomputable abbrev qz417 := qz618

noncomputable abbrev qz79 := (@HPow.hPow Real Real Real qz350 qz417 qz352)

noncomputable abbrev qz730 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 636640 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz619 := qz730

noncomputable abbrev qz418 := qz619

noncomputable abbrev qz80 := qz418

noncomputable def Ns312p473 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz79) (Zeta.RiemannSiegel.correction qz80)) 196239481 67108864 170031 134217728 2312235478609416272115 9444732965739290427392 28653693250980838099 Ns312p471 Ns312p472 

noncomputable def Ns312p474 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.cos BSN.quadSignPos 9 10 636640 1000 200 268435456 134217728 4503599627370496 Bool.false 309074778623 2501 618095470 62 84886744 8 

noncomputable def Ns312p475 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 636640 1000 109 157 268435456 134217728 4503599627370496 Bool.false 309074778623 2501 

noncomputable def Ns312p476 := Ns312p475 558195838 62 94906264 8 589812974 62 89478488 8 Bool.false 469316516 127898 Bool.true 334360000 Bool.true 223536906 14148475504056880 1 Bool.false 254365198 Bool.true Bool.false 198582555 Bool.true Bool.false 313190652 

noncomputable def Ns312p477 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 636640 1000 6 55 268435456 134217728 4503599627370496 Bool.false 309074778623 2501 

noncomputable def Ns312p478 := Ns312p477 480971758 62 109588312 8 522351262 62 101459064 8 Bool.false 414175147 94879 Bool.false 338974040 Bool.true 283770262 14148475504056880 1 Bool.false 81382130 Bool.true Bool.false 233793097 Bool.false Bool.false 469316516 

noncomputable def Ns312p479 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 636640 1000 171 80 268435456 134217728 4503599627370496 Bool.false 309074778623 2501 

noncomputable def Ns312p480 := Ns312p479 372130544 61 134217720 8 432030192 61 120047984 16 Bool.false 330547464 55697 Bool.false 58168857 Bool.false 294482926 14148475504056880 1 Bool.false 57714684 Bool.false Bool.false 122470213 Bool.false Bool.false 414175147 

noncomputable def Ns312p481 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz78) qz78 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 636640 1000 452 287 268435456 134217728 4503599627370496 Bool.false 309074778623 2501 

noncomputable def Ns312p482 := Ns312p481 186065264 61 189812528 16 294906480 61 154981288 8 Bool.false 116296 2573 Bool.false 29031373 Bool.false 309835283 14148475504056880 1 Bool.false 266867109 Bool.false Bool.false 245479447 Bool.false Bool.false 330547464 

noncomputable def Ns312p483 := nat_lit 606904483288389755999035127127056181907295288117 

noncomputable def Ns312p484 := nat_lit 527104419342892170538629642228720068670259200 

noncomputable def Ns312p485 := nat_lit 50200902517431255238807552000000000 

noncomputable def Ns312p486 := nat_lit 191759470669382488463681381191680000000 

noncomputable abbrev qz620 := (@Eq.refl Real qz728)

noncomputable abbrev qz419 := qz620

noncomputable abbrev qz81 := qz419

noncomputable def Ns312p487 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz78 636640 1000 1621242958400 16000000 1273280 4000 2000 Ns312p485 Ns312p486 qz81 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns312p488 := nat_lit 12429403817746222202860239403562110605461407500636160000000 

noncomputable abbrev qz621 := (@HSub.hSub Real Real Real qz715 qz716 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz717 (@Nat.cast Real Real.instNatCast 1273280))))

noncomputable abbrev qz420 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 636640 4000) (Real.log (Enclosure.sfrac Bool.false 1621242958400 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz621))

noncomputable abbrev qz622 := (Enclosure.sfrac Bool.false 636640 2000)

noncomputable abbrev qz82 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz420 qz622) (@HMul.hMul Real Real Real qz349 qz622 (Real.log Real.pi)))

noncomputable def Ns312p489 := @Enclosure.Real.IsNear.addLit_ft_p qz82 (Enclosure.sfrac Bool.true Ns312p485 Ns312p486) 64817693751541795837 56294995342131200 35040537757513117 3763200000000000000000 Ns312p485 Ns312p486 0 1 Ns312p488 

noncomputable def Ns312p490 := nat_lit 27186511217286676044631244800 

noncomputable abbrev qz83 := (@HSub.hSub Real Real Real qz355 qz420 qz622)

noncomputable def Ns312p491 := @Enclosure.Real.IsNear.subLit_ff_p qz83 (@HMul.hMul Real Real Real qz5 qz622 (Real.log Real.pi)) 85331050533710236669 56294995342131200 134300074872539 29400000000000000000 152836418019 419430400 3979 838860800 Ns312p490 64817693751541795837 56294995342131200 

noncomputable abbrev qz84 := qz420

noncomputable def Ns312p492 := @Enclosure.Real.IsNear.subLit_ff_p qz84 qz622 103250873451017440253 56294995342131200 134300074872539 29400000000000000000 636640 2000 0 1 170662101067420473338000 85331050533710236669 56294995342131200 134300074872539 29400000000000000000 

noncomputable def Ns312p493 := nat_lit 29062537199980023894000858948435968 

noncomputable def Ns312p494 := nat_lit 55736871839137034441588736 

noncomputable def Ns312p495 := nat_lit 191268133717100259593032353936010522370781610775994572075888015949200814304381409143256587537884677670961152000000000000000000000 

noncomputable def Ns312p496 := nat_lit 3017072703653625773990371583781203111947337701954740896352639180765538913621064547728321348127303538206310400000000000000000000 

noncomputable def Ns312p497 := nat_lit 3584702086962748536580863417512129965955268634378571762054639683828225024039277969386055085255032832000000000000000000000 

noncomputable def Ns312p498 := BSN.log_dyadic_bound 572666958400 2669818958400 6 5 Ns312p495 134217728 35280000 Ns312p496 Ns312p497 58486725 3242485916800 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 572666958400) (BSN.artanhQ 2669818958400) 0 5 Ns312p496 Ns312p495 Ns312p497 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz421 := (Real.log (Enclosure.sfrac Bool.false 1621242958400 16000000))

noncomputable def Ns312p499 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 636640 4000) qz421 636640 4000 0 1 3244312936389879 281474976710656 781250441 27562500000000000 12909121173895328541 7036874417766400 3108595504739 689062500000000000 (Enclosure.Real.IsNear.const Bool.false 636640 4000) (BSN.isNear_log_sfrac 1621242958400 16000000 3244312936389879 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1621242958400) qz358)) Bool.false Ns312p494 Ns312p99 1000000564480000 35280000000000000000000 3244312936389879 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1621242958400 16000000 16 3242485916800 2097152000000 58486725 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns312p498 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns312p500 := BSN.arctan_dyadic_bound_f 1000 1273280 1 0 16777216 4410000 0 1 1 0 1 1 13176 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1273280) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1273280) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz422 := (@Nat.cast Real Real.instNatCast 1273280)

noncomputable def Ns312p501 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz422)) 884279719003555 562949953421312 1 2000000000000000 13176 16777216 1 4410000 14828334421555667795968 883837605807523 562949953421312 200000000441 882000000000000000 qz15 (Ns312p500 rfl) rfl rfl 

noncomputable abbrev qz423 := (@HMul.hMul Real Real Real qz579 qz584 qz621)

noncomputable abbrev qz85 := qz423

noncomputable abbrev qz424 := qz621

noncomputable abbrev qz86 := qz424

noncomputable def Ns312p502 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 636640 4000) qz421) qz85 12909121173895328541 7036874417766400 3108595504739 689062500000000000 883837605807523 2251799813685248 200000000441 3528000000000000000 Ns312p493 103250873451017440253 56294995342131200 134300074872539 29400000000000000000 (Ns312p499 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz86 1 4 0 1 883837605807523 562949953421312 200000000441 882000000000000000 883837605807523 2251799813685248 200000000441 3528000000000000000 qz366 Ns312p501 rfl) 

noncomputable def Ns312p503 := @Ns312p489 Ns312p483 Ns312p484 35040537757513117 3763200000000000000000 (@Ns312p491 35040537757513117 3763200000000000000000 (Ns312p492 (Ns312p502 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 636640 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz622 (Real.log Real.pi) 636640 2000 0 1 38410761 33554432 1 67108864 152836418019 419430400 3979 838860800 (Enclosure.Real.IsNear.const Bool.false 636640 2000) RS313to324.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns312p485 Ns312p486) 

noncomputable def Ns312p504 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz78) Bool.false Ns312p483 Ns312p484 35040537757513117 3763200000000000000000 38634347327 33554432 157 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz78) (@HAdd.hAdd Real Real Real qz367 qz82 (Enclosure.sfrac Bool.true Ns312p485 Ns312p486)) Bool.false Ns312p483 Ns312p484 35040537757513117 3763200000000000000000 Ns312p487 (Ns312p503 rfl rfl)) 

noncomputable def Ns312p505 := nat_lit 7593809814945116113076224 

noncomputable def Ns312p506 := nat_lit 1350996368945058801928142050555840094087681056997053098148433912649129714416503365430838610563545518506320730006296457850550914999601890625 

noncomputable def Ns312p507 := nat_lit 5312452879021523644167342878668926891519915429617346963252719967526930359331948649748578417931730498127901383505799396607174191825394073600 

noncomputable def Ns312p508 := nat_lit 2494359159905434383732578607510432149742731075372220736668573777956630595037060741055584933003947925088726276063065790685996337890625 

noncomputable def Ns312p509 := nat_lit 8176324387640287917398404737285726575735455691605942929710739390381362507830470364016238565422677064705460169405272101236454958235339490625 

noncomputable def Ns312p510 := nat_lit 483433211990958651619228201958872347128312304095178573655997517044950662699207327127120636031787475329639025899027745091252851456110860697600 

noncomputable def Ns312p511 := BSN.cos_dyadic_bound_f 107914528015 68719476736 4 3 33554432 8828614 Ns312p506 Ns312p507 Ns312p508 Ns312p509 Ns312p510 Ns312p508 14537 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 107914528015) (BSN.cosEvenQ 68719476736) 0 3 Ns312p506 Ns312p507 Ns312p508 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 107914528015) (BSN.cosOddQ 68719476736) 0 3 Ns312p509 Ns312p510 Ns312p508 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p512 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz78) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 38634347327) qz368) Bool.false 38634347327 33554432 157 16777216 Bool.false 14537 33554432 1 4410000 (Ns312p504 rfl) (Enclosure.sfrac_false_div 38634347327 33554432) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 38634347327) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns312p505) qz369) 226375608064910080 72057594037927936 Bool.false 14537 33554432 183 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q0 38634347327 33554432 226375608064910080 72057594037927936 183 Ns312p505 Ns312p99 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 14537 33554432 Ns312p505 Ns312p99 107914528015 68719476736 8828614 8820000 (Ns312p511 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns312p513 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz78) Bool.false Ns312p483 Ns312p484 35040537757513117 3763200000000000000000 309074778623 268435456 2501 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz78) (@HAdd.hAdd Real Real Real qz367 qz82 (Enclosure.sfrac Bool.true Ns312p485 Ns312p486)) Bool.false Ns312p483 Ns312p484 35040537757513117 3763200000000000000000 Ns312p487 (Ns312p503 rfl rfl)) 

noncomputable def Ns312p514 := Ns312p482 55697 BSN.abs_quadSignPos (BSN.cos_quad_nat0 452 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 266867109 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 287 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 245479447 268435456) qz81 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 1) Bool.false 14537 33554432 44321701 4624220160000 116296 268435456 2573 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz78)) Bool.false 14537 33554432 44321701 4624220160000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz78) qz78) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz78)) Bool.false 14537 33554432 709147216 73987522560000 14537 33554432 44321701 4624220160000 (Ns312p512 rfl rfl) rfl)) rfl) (Ns312p513 rfl) RS313to324.d7 

noncomputable def Ns312p515 := nat_lit 710346594572814299329737386641 

noncomputable def Ns312p516 := BSN.cos_dyadic_bound_f 29031373 268435456 2 1 268435456 134217728 Ns312p515 Ns312p119 Ns312p515 Ns312p515 Ns312p120 Ns312p515 266867109 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 29031373) qz372 0 1 Ns312p515 Ns312p119 Ns312p515 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 29031373) qz373 0 1 Ns312p515 Ns312p120 Ns312p515 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p517 := nat_lit 144783680801876134212327487062423179824988816412025866894006263620840225 

noncomputable def Ns312p518 := nat_lit 84927233632696376287416165435660990046238375588592868020853093182241 

noncomputable def Ns312p519 := nat_lit 379057853245698843089725697086117257938705371328162405793220737808476961 

noncomputable def Ns312p520 := BSN.sin_dyadic_bound_f 309835283 268435456 3 2 268435456 134217728 Ns312p517 Ns312p259 Ns312p518 Ns312p519 Ns312p262 Ns312p518 245479447 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 309835283) qz370 0 2 Ns312p517 Ns312p259 Ns312p518 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 309835283) qz371 0 2 Ns312p519 Ns312p262 Ns312p518 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p521 := nat_lit 11448856725791733311298964229601 

noncomputable def Ns312p522 := BSN.sin_dyadic_bound_f 58168857 268435456 2 1 268435456 134217728 Ns312p521 Ns312p115 Ns312p521 Ns312p521 Ns312p116 Ns312p521 57714684 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 58168857) qz370 0 1 Ns312p521 Ns312p115 Ns312p521 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 58168857) qz371 0 1 Ns312p521 Ns312p116 Ns312p521 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p523 := nat_lit 4050042040464975695393063378359880104469541142688438917247427278199520874834248666737385743792731646388473856 

noncomputable def Ns312p524 := nat_lit 425325514113275848583094838880002434070391299421232890620241402562059727202686736160995137485460606976 

noncomputable def Ns312p525 := nat_lit 24556143255274006208723021691106779141399781972371598662946559564721931607444246768988185231115238849003786240 

noncomputable def Ns312p526 := BSN.cos_dyadic_bound_f 294482926 268435456 4 3 268435456 134217728 Ns312p523 Ns312p136 Ns312p524 Ns312p525 Ns312p139 Ns312p524 122470213 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 294482926) qz372 0 3 Ns312p523 Ns312p136 Ns312p524 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 294482926) qz373 0 3 Ns312p525 Ns312p139 Ns312p524 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p527 := Ns312p480 94879 BSN.abs_quadSignPos (BSN.cos_quad_nat3 171 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 57714684 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 80 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 122470213 268435456) qz81 rfl rfl (Ns312p514 RS313to324.d9 RS313to324.d11 RS313to324.d13 RS313to324.d17 (Ns312p516 rfl rfl) (Ns312p520 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns312p513 rfl) RS313to324.d19 RS313to324.d21 RS313to324.d23 RS313to324.d25 RS313to324.d17 (Ns312p522 rfl rfl) (Ns312p526 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns312p528 := nat_lit 7114878353549457803555345530061162677794344113989387920290365931981797914169762159019329769266913214464000000 

noncomputable def Ns312p529 := nat_lit 2301427368633896139181174013172124192223942000626699971235977029422602977605491868529852416000000000000 

noncomputable def Ns312p530 := nat_lit 43120095993738075792183499768571156649173059253095144891145379687322099990975751851197628005396053072281600000 

noncomputable def Ns312p531 := BSN.cos_dyadic_bound_f 338974040 268435456 4 3 268435456 134217728 Ns312p528 Ns312p136 Ns312p529 Ns312p530 Ns312p139 Ns312p529 81382130 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 338974040) qz372 0 3 Ns312p528 Ns312p136 Ns312p529 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 338974040) qz373 0 3 Ns312p530 Ns312p139 Ns312p529 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p532 := nat_lit 101856357818055125967253829206917880615277446219137930655462345162973440 

noncomputable def Ns312p533 := nat_lit 42047003333379019636389746202920859544118421028068996800081634877696 

noncomputable def Ns312p534 := nat_lit 266698575327604621025301112143313529743607595987506278102820295637033216 

noncomputable def Ns312p535 := BSN.sin_dyadic_bound_f 283770262 268435456 3 2 268435456 134217728 Ns312p532 Ns312p259 Ns312p533 Ns312p534 Ns312p262 Ns312p533 233793097 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 283770262) qz370 0 2 Ns312p532 Ns312p259 Ns312p533 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 283770262) qz371 0 2 Ns312p534 Ns312p262 Ns312p533 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p536 := Ns312p478 127898 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 6 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 81382130 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 55 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 233793097 268435456) qz81 rfl rfl (Ns312p527 rfl rfl) (Ns312p513 rfl) RS313to324.d27 RS313to324.d29 RS313to324.d31 RS313to324.d33 RS313to324.d17 (Ns312p531 rfl rfl) (Ns312p535 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p537 := nat_lit 17499312104282210623974127265599727927888508627545931031061658485486779367988649310489568870400000000000000000 

noncomputable def Ns312p538 := nat_lit 1952413485506174381101232084168251787342793872502685696000000000000000000000000000000000000000000000000 

noncomputable def Ns312p539 := nat_lit 87453532002879710174831475760001486248573644530603614010877831701117105343239246552447844352000000000000000000 

noncomputable def Ns312p540 := BSN.sin_dyadic_bound_f 334360000 268435456 4 3 268435456 134217728 Ns312p537 Ns312p147 Ns312p538 Ns312p539 Ns312p150 Ns312p538 254365198 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 334360000) qz370 0 3 Ns312p537 Ns312p147 Ns312p538 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 334360000) qz371 0 3 Ns312p539 Ns312p150 Ns312p538 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p541 := nat_lit 39210944169066429555366597263807060444360377012224601287065808681427200 

noncomputable def Ns312p542 := nat_lit 6234388815912877517181777993403821079572477109850438998615843266816 

noncomputable def Ns312p543 := nat_lit 102685236194233932748075174717029171167767393878600864564888882800353536 

noncomputable def Ns312p544 := BSN.sin_dyadic_bound_f 223536906 268435456 3 2 268435456 134217728 Ns312p541 Ns312p259 Ns312p542 Ns312p543 Ns312p262 Ns312p542 198582555 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 223536906) qz370 0 2 Ns312p541 Ns312p259 Ns312p542 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 223536906) qz371 0 2 Ns312p543 Ns312p262 Ns312p542 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p545 := Ns312p476 156748 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 109 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 254365198 268435456) BSN.abs_quadSignNeg qz590 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 198582555 268435456) qz81 rfl rfl (Ns312p536 rfl) (Ns312p513 rfl) RS313to324.d35 RS313to324.d37 RS313to324.d39 RS313to324.d41 RS313to324.d17 (Ns312p540 rfl rfl) (Ns312p544 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p546 := nat_lit 805770180593391789468816169651367782024802108980067136473042041962496 

noncomputable def Ns312p547 := nat_lit 8532486162087637987715917594084707095114754081445579405567983616 

noncomputable def Ns312p548 := nat_lit 2417293476807851193130473077118915176660216097432038518260314989920256 

noncomputable def Ns312p549 := BSN.cos_dyadic_bound_f 98035744 268435456 3 2 268435456 134217728 Ns312p546 Ns312p123 Ns312p547 Ns312p548 Ns312p126 Ns312p547 250731656 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 98035744) qz372 0 2 Ns312p546 Ns312p123 Ns312p547 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 98035744) qz373 0 2 Ns312p548 Ns312p126 Ns312p547 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p550 := Ns312p474 Bool.false 313190652 156748 Bool.true 98035744 14148475504056880 1 Bool.false 250731656 Bool.false Bool.false 392478962 170031 BSN.abs_quadSignPos qz374 (BSN.sfrac_eq_quadSignPos_mul Bool.false 250731656 268435456) qz81 rfl (Ns312p545 rfl) (Ns312p513 rfl) RS313to324.d43 RS313to324.d45 RS313to324.d17 (Ns312p549 rfl rfl) rfl 

noncomputable def Ns312p551 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) 392478962 268435456 170031 268435456 392478962 268435456 170031 268435456 210710538269753344 196239481 67108864 170031 134217728 (Ns312p550 rfl rfl rfl rfl) 

noncomputable def Ns312p552 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz79) (Zeta.RiemannSiegel.correction qz80) 10575999 33554432 1 33554432 218630455487885 281474976710656 168382421675239 12930256742645760000 2312235478609416272115 9444732965739290427392 

noncomputable def Ns312p553 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz79 1 1 0 1 10575999 33554432 1 33554432 10575999 33554432 1 33554432 

noncomputable abbrev qz87 := qz417

noncomputable def Ns312p554 := @Enclosure.Real.IsNear.sqrt_image qz87 21249264587 209715200 3979 209715200 168879468 168879500 16777216 (@Enclosure.Real.IsNear.of_eq qz87 (@HMul.hMul Real Real Real qz5 qz78 qz3) Bool.false 21249264587 209715200 3979 209715200 (BSN.t_div_two_pi_mk qz78 636640 1000 qz81) (@Enclosure.Real.IsNear.mulLit_ff qz78 qz3 636640 1000 0 1 5340353 33554432 1 33554432 21249264587 209715200 3979 209715200 (Enclosure.Real.IsNear.const Bool.false 636640 1000) RS313to324.d48 rfl)) 

noncomputable abbrev qz731 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 636640 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz623 := qz731

noncomputable abbrev qz425 := qz623

noncomputable abbrev qz88 := qz425

noncomputable def Ns312p555 := @Enclosure.Real.IsNear.sqrt_image qz88 42219871 4194304 1 1048576 53229008 53229014 16777216 (@Enclosure.Real.IsNear.recentre' qz88 Bool.false 337758968 33554432 32 33554432 42219871 4194304 1 1048576 (Ns312p554 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns312p556 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz88) 53229011 16777216 3 16777216 5287999 5288000 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz88) Bool.false 106458022 33554432 6 33554432 53229011 16777216 3 16777216 (Ns312p555 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns312p557 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz88)) Bool.false 10575999 33554432 1 33554432 10575999 33554432 1 33554432 (Ns312p556 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz89 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz418))

noncomputable abbrev qz624 := (@HMul.hMul Real Real Real qz711 qz730 qz730)

noncomputable abbrev qz426 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz624 qz619) qz594)

noncomputable abbrev qz90 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz426))

noncomputable def Ns312p558 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz80) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz89) qz90) Bool.false 218630455487885 

noncomputable def Ns312p559 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz89) qz90 36662017 33554432 251 

noncomputable def Ns312p560 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz89) Bool.false 36662017 33554432 251 33554432 36662017 33554432 251 

noncomputable def Ns312p561 := @Enclosure.Real.IsNear.recentre' qz89 Bool.false 15355128 16777216 462187216 73987522560000 1919391 2097152 28886701 4624220160000 

noncomputable abbrev qz91 := (@HMul.hMul Real Real Real qz349 qz346 qz418)

noncomputable def Ns312p562 := @Enclosure.Real.IsNear.cos_image qz91 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13915043) qz368) Bool.false 13915043 33554432 101 16777216 Bool.false 15355128 16777216 1 

noncomputable def Ns312p563 := nat_lit 5397215081927707100185691 

noncomputable def Ns312p564 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz80 884279719003555 140737488355328 1 500000000000000 276831 4194304 1 1048576 244796038891473134205 590295810358705651712 Ns312p563 

noncomputable def Ns312p565 := @Enclosure.Real.IsNear.subLit_ff_p qz88 qz1 42219871 4194304 1 1048576 10 1 0 1 276831 276831 4194304 1 

noncomputable def Ns312p566 := @Ns312p565 1048576 (@Enclosure.Real.IsNear.recentre' qz88 Bool.false 337758968 33554432 32 33554432 42219871 4194304 1 1048576 (Ns312p554 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns312p567 := @Enclosure.Real.IsNear.recentre' qz91 Bool.false 244796038891473134205 590295810358705651712 Ns312p563 Ns312p171 13915043 33554432 101 16777216 (@Ns312p564 Ns312p171 RS313to324.d47 (Ns312p566 rfl rfl) rfl) 

noncomputable def Ns312p568 := nat_lit 37491965686876500359513038801 

noncomputable def Ns312p569 := BSN.cos_dyadic_bound_f 13915043 33554432 2 1 16777216 4410000 Ns312p568 Ns312p302 Ns312p568 Ns312p568 Ns312p303 Ns312p568 15355128 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 13915043) qz395 0 1 Ns312p568 Ns312p302 Ns312p568 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 13915043) (BSN.cosOddQ 33554432) 0 1 Ns312p568 Ns312p303 Ns312p568 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p570 := @Enclosure.Real.IsNear.inv_image qz89 1919391 2097152 28886701 4624220160000 18330883 18331134 16777216 (Ns312p561 (@Ns312p562 4410000 (Ns312p567 rfl) (Enclosure.sfrac_false_div 13915043 33554432) (Ns312p569 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns312p571 := @Enclosure.Real.IsNear.recentre' qz90 Bool.false 11926810 16777216 

noncomputable abbrev qz92 := (@HMul.hMul Real Real Real qz349 qz346 qz426)

noncomputable def Ns312p572 := @Enclosure.Real.IsNear.cos_image qz92 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 13086711)) qz378) Bool.true 13086711 16777216 

noncomputable def Ns312p573 := nat_lit 1931257706115198572254207645 

noncomputable def Ns312p574 := nat_lit 2475880078570760549798248448 

noncomputable def Ns312p575 := nat_lit 64064538232284469222122490793831 

noncomputable def Ns312p576 := @Enclosure.Real.IsNear.recentre' qz92 Bool.true Ns312p573 Ns312p574 Ns312p575 

noncomputable def Ns312p577 := nat_lit 9444732965739290427392000000000000000 

noncomputable abbrev qz93 := qz426

noncomputable def Ns312p578 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz93 884279719003555 140737488355328 1 500000000000000 2183989595839 

noncomputable abbrev qz427 := (@HSub.hSub Real Real Real qz583 qz624 qz619)

noncomputable abbrev qz94 := qz427

noncomputable def Ns312p579 := @Enclosure.Real.IsNear.subLit_tf qz94 qz29 1084477968063 17592186044416 2373985 2199023255552 1 16 

noncomputable abbrev qz428 := qz624

noncomputable abbrev qz95 := qz428

noncomputable def Ns312p580 := @Enclosure.Real.IsNear.subLit_ff_n qz95 qz80 76635402561 17592186044416 276833 2199023255552 276831 4194304 1 1048576 

noncomputable def Ns312p581 := @Enclosure.Real.IsNear.mulLit_ff qz80 qz80 276831 4194304 1 1048576 276831 4194304 1 1048576 76635402561 17592186044416 

noncomputable def Ns312p582 := nat_lit 3904870209316060951993409933799864889512448604719338078820161 

noncomputable def Ns312p583 := nat_lit 253092741970790968397859029543733109897246971520789871559966720 

noncomputable def Ns312p584 := nat_lit 860288454145693096378117255623151156158998467808256284481 

noncomputable def Ns312p585 := nat_lit 11712890051039891469787473566888348366225027817222397723891521 

noncomputable def Ns312p586 := nat_lit 11389173388685593577903656329467989945376113718435544220198502400 

noncomputable def Ns312p587 := BSN.cos_dyadic_bound_f 13086711 16777216 3 2 16777216 4410000 Ns312p582 Ns312p583 Ns312p584 Ns312p585 Ns312p586 Ns312p584 11926810 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 13086711) (BSN.cosEvenQ 16777216) 0 2 Ns312p582 Ns312p583 Ns312p584 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 13086711) (BSN.cosOddQ 16777216) 0 2 Ns312p585 Ns312p586 Ns312p584 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p588 := @Ns312p571 1043444432 147975045120000 5963405 8388608 65215277 9248440320000 (@Ns312p572 229 33554432 Bool.false 11926810 16777216 1 4410000 (@Ns312p576 Ns312p577 13086711 16777216 229 33554432 (@Ns312p578 17592186044416 2373985 2199023255552 Ns312p573 Ns312p574 Ns312p575 Ns312p577 RS313to324.d47 (@Ns312p579 0 1 34943833533424 2183989595839 17592186044416 2373985 2199023255552 (@Ns312p580 4548630279358513152 1084477968063 17592186044416 2373985 2199023255552 (@Ns312p581 276833 2199023255552 (Ns312p566 rfl rfl) (Ns312p566 rfl rfl) rfl) (Ns312p566 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 13086711 16777216) (BSN.cos_neg_of_bound 13086711 16777216 Bool.false 11926810 16777216 1 4410000 (Ns312p587 rfl rfl)) rfl rfl) 

noncomputable def Ns312p589 := @Ns312p552 28653693250980838099 Ns312p471 (Ns312p553 qz31 (@Enclosure.Real.IsNear.of_eq qz79 (@Inv.inv Real Real.instInv (Real.sqrt qz88)) Bool.false 10575999 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz87 (BSN.t_div_two_pi_nonneg qz78 636640 1000 qz81)) Ns312p557) rfl) (@Ns312p558 281474976710656 168382421675239 12930256742645760000 (BSN.correction_mk qz80 (BSN.cos_two_pi_p_ne_zero_mk qz78 636640 1000 10 qz81 rfl rfl (@BSN.floor_sqrt_eq_dec qz78 636640 1000 10 qz81 rfl rfl rfl))) (@Ns312p559 33554432 5963405 8388608 65215277 9248440320000 218630455487885 281474976710656 168382421675239 12930256742645760000 (@Ns312p560 33554432 (Ns312p570 rfl rfl rfl rfl rfl) rfl) (Ns312p588 rfl) rfl)) 

noncomputable def Ns312p590 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz78) (hardyZApproximantRS₀ qz78) Bool.false 25306016193483694032653 9444732965739290427392 8822831630086185712339 Ns312p471 (@Eq.refl Real (hardyZApproximantRS₀ qz78)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz78) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz79) (Zeta.RiemannSiegel.correction qz80))) Bool.false 25306016193483694032653 9444732965739290427392 8822831630086185712339 Ns312p471 (BSN.hardyZApproximantRS₀_eq qz78 10 (@BSN.floor_sqrt_eq_dec qz78 636640 1000 10 qz81 rfl rfl rfl)) (@Ns312p473 25306016193483694032653 9444732965739290427392 8822831630086185712339 Ns312p471 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz78) qz78 10)) Bool.false 196239481 67108864 170031 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz78) qz78 10) (Ns312p551 (Ns312p550 rfl rfl rfl rfl) rfl rfl)) (Ns312p589 rfl) rfl rfl)) 

theorem RS313to324.d54 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz78) Bool.false 25306016193483694032653 9444732965739290427392 8822831630086185712339 Ns312p471 := Ns312p590 

noncomputable def Ns312p591 := nat_lit 61981060087664093429760000 

noncomputable def Ns312p592 := nat_lit 134824047580902047187709460480 

noncomputable abbrev qz732 := (Enclosure.sfrac Bool.false 637660 1000)

noncomputable abbrev qz625 := qz732

noncomputable abbrev qz429 := qz625

noncomputable abbrev qz96 := qz429

noncomputable abbrev qz733 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 637660 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz626 := qz733

noncomputable abbrev qz430 := qz626

noncomputable abbrev qz97 := (@HPow.hPow Real Real Real qz350 qz430 qz352)

noncomputable abbrev qz734 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 637660 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz627 := qz734

noncomputable abbrev qz431 := qz627

noncomputable abbrev qz98 := qz431

noncomputable def Ns312p593 := @Enclosure.Real.IsNear.subLit_ff_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz97) (Zeta.RiemannSiegel.correction qz98)) 3607591 134217728 170287 134217728 1131448256993325303747 4722366482869645213696 261209043239095165379 Ns312p591 Ns312p592 

noncomputable def Ns312p594 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.cos BSN.quadSignPos 9 10 637660 1000 200 268435456 134217728 4503599627370496 Bool.false 309707146688 2504 618095470 62 84886744 8 

noncomputable def Ns312p595 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 637660 1000 109 157 268435456 134217728 4503599627370496 Bool.false 309707146688 2504 

noncomputable def Ns312p596 := Ns312p595 558195838 62 94906264 8 589812974 62 89478488 8 Bool.false 63395200 128087 Bool.true 271351690 Bool.true 192778075 14148475504056880 1 Bool.false 227442935 Bool.true Bool.false 176629439 Bool.true Bool.true 75894501 

noncomputable def Ns312p597 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 637660 1000 7 55 268435456 134217728 4503599627370496 Bool.false 309707146688 2504 

noncomputable def Ns312p598 := Ns312p597 480971758 62 109588312 8 522351262 62 101459064 8 Bool.true 24819901 95016 Bool.false 59093483 Bool.true 184200484 14148475504056880 1 Bool.false 58617342 Bool.false Bool.false 170081261 Bool.false Bool.false 63395200 

noncomputable def Ns312p599 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 637660 1000 171 81 268435456 134217728 4503599627370496 Bool.false 309707146688 2504 

noncomputable def Ns312p600 := Ns312p599 372130544 61 134217720 8 432030192 61 120047984 16 Bool.true 119208437 55772 Bool.false 310963767 Bool.false 64522767 14148475504056880 1 Bool.false 245933890 Bool.false Bool.false 63903249 Bool.true Bool.true 24819901 

noncomputable def Ns312p601 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz96) qz96 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 637660 1000 453 288 268435456 134217728 4503599627370496 Bool.false 309707146688 2504 

noncomputable def Ns312p602 := Ns312p601 186065264 61 189812528 16 294906480 61 154981288 8 Bool.true 189978184 2565 Bool.false 49955441 Bool.false 219741310 14148475504056880 1 Bool.false 49667591 Bool.true Bool.false 183406919 Bool.false Bool.true 119208437 

noncomputable def Ns312p603 := nat_lit 7675197056014233669158020331410996404195289993 

noncomputable def Ns312p604 := nat_lit 6652397413660007799471700837117038365245440 

noncomputable def Ns312p605 := nat_lit 50604342676396856956315648000000000 

noncomputable def Ns312p606 := nat_lit 193610246457974653442847217582080000000 

noncomputable abbrev qz628 := (@Eq.refl Real qz732)

noncomputable abbrev qz432 := qz628

noncomputable abbrev qz99 := qz432

noncomputable def Ns312p607 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz96 637660 1000 1626442102400 16000000 1275320 4000 2000 Ns312p605 Ns312p606 qz99 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns312p608 := nat_lit 1257504285657372044354850051098377650863356312453120000000 

noncomputable abbrev qz629 := (@HSub.hSub Real Real Real qz715 qz716 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz717 (@Nat.cast Real Real.instNatCast 1275320))))

noncomputable abbrev qz433 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 637660 4000) (Real.log (Enclosure.sfrac Bool.false 1626442102400 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz629))

noncomputable abbrev qz630 := (Enclosure.sfrac Bool.false 637660 2000)

noncomputable abbrev qz100 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz433 qz630) (@HMul.hMul Real Real Real qz349 qz630 (Real.log Real.pi)))

noncomputable def Ns312p609 := @Enclosure.Real.IsNear.addLit_ft_p qz100 (Enclosure.sfrac Bool.true Ns312p605 Ns312p606) 6495031092310765189 5629499534213120 93590230822046303 10035200000000000000000 Ns312p605 Ns312p606 0 1 Ns312p608 

noncomputable def Ns312p610 := nat_lit 108968539562413646701133824000 

noncomputable abbrev qz101 := (@HSub.hSub Real Real Real qz355 qz433 qz630)

noncomputable def Ns312p611 := @Enclosure.Real.IsNear.subLit_ff_p qz101 (@HMul.hMul Real Real Real qz5 qz630 (Real.log Real.pi)) 42748266706305591449 28147497671065600 44837524997497 9800000000000000000 1224650292963 3355443200 31883 6710886400 Ns312p610 6495031092310765189 5629499534213120 

noncomputable abbrev qz102 := qz433

noncomputable def Ns312p612 := @Enclosure.Real.IsNear.subLit_ff_p qz102 qz630 51722533388771436697 28147497671065600 44837524997497 9800000000000000000 637660 2000 0 1 85496533412611182898000 42748266706305591449 28147497671065600 44837524997497 9800000000000000000 

noncomputable def Ns312p613 := nat_lit 232937582096329080027269574229491712 

noncomputable def Ns312p614 := nat_lit 55752354566137587865485312 

noncomputable def Ns312p615 := nat_lit 195025655797540162371787093417936617598759631136859595608857898982596948996842718344919534555369014508388352000000000000000000000 

noncomputable def Ns312p616 := nat_lit 3121572263047334106922272793527740748102113439128747653981866778211050950269762094692174679812645920859750400000000000000000000 

noncomputable def Ns312p617 := nat_lit 3923774167951053189792603113418761411733042866764395010573750749242729853133157762833421208001708032000000000000000000000 

noncomputable def Ns312p618 := BSN.log_dyadic_bound 577866102400 2675018102400 6 5 Ns312p615 134217728 35280000 Ns312p616 Ns312p617 58916457 3252884204800 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 577866102400) (BSN.artanhQ 2675018102400) 0 5 Ns312p616 Ns312p615 Ns312p617 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz434 := (Real.log (Enclosure.sfrac Bool.false 1626442102400 16000000))

noncomputable def Ns312p619 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 637660 4000) qz434 637660 4000 0 1 3245214149713143 281474976710656 781250441 27562500000000000 103467162735304138269 56294995342131200 24908607810403 5512500000000000000 (Enclosure.Real.IsNear.const Bool.false 637660 4000) (BSN.isNear_log_sfrac 1626442102400 16000000 3245214149713143 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1626442102400) qz358)) Bool.false Ns312p614 Ns312p99 1000000564480000 35280000000000000000000 3245214149713143 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1626442102400 16000000 16 3252884204800 2097152000000 58916457 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns312p618 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns312p620 := BSN.arctan_dyadic_bound_f 1000 1275320 1 0 16777216 4410000 0 1 1 0 1 1 13155 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1275320) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1275320) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz435 := (@Nat.cast Real Real.instNatCast 1275320)

noncomputable def Ns312p621 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz435)) 884279719003555 562949953421312 1 2000000000000000 13155 16777216 1 4410000 14828346243504689643520 883838310450595 562949953421312 200000000441 882000000000000000 qz15 (Ns312p620 rfl) rfl rfl 

noncomputable abbrev qz436 := (@HMul.hMul Real Real Real qz579 qz584 qz629)

noncomputable abbrev qz103 := qz436

noncomputable abbrev qz437 := qz629

noncomputable abbrev qz104 := qz437

noncomputable def Ns312p622 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 637660 4000) qz434) qz103 103467162735304138269 56294995342131200 24908607810403 5512500000000000000 883838310450595 2251799813685248 200000000441 3528000000000000000 Ns312p613 51722533388771436697 28147497671065600 44837524997497 9800000000000000000 (Ns312p619 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz104 1 4 0 1 883838310450595 562949953421312 200000000441 882000000000000000 883838310450595 2251799813685248 200000000441 3528000000000000000 qz366 Ns312p621 rfl) 

noncomputable def Ns312p623 := @Ns312p609 Ns312p603 Ns312p604 93590230822046303 10035200000000000000000 (@Ns312p611 93590230822046303 10035200000000000000000 (Ns312p612 (Ns312p622 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 637660 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz630 (Real.log Real.pi) 637660 2000 0 1 38410761 33554432 1 67108864 1224650292963 3355443200 31883 6710886400 (Enclosure.Real.IsNear.const Bool.false 637660 2000) RS313to324.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns312p605 Ns312p606) 

noncomputable def Ns312p624 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz96) Bool.false Ns312p603 Ns312p604 93590230822046303 10035200000000000000000 4839174167 4194304 313 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz96) (@HAdd.hAdd Real Real Real qz367 qz100 (Enclosure.sfrac Bool.true Ns312p605 Ns312p606)) Bool.false Ns312p603 Ns312p604 93590230822046303 10035200000000000000000 Ns312p607 (Ns312p623 rfl rfl)) 

noncomputable def Ns312p625 := nat_lit 316572523336695485334572999529270895461740813952769861788576753141071737481452903964057856 

noncomputable def Ns312p626 := nat_lit 20052072892042597411705012245279816272850392000149059967199507548332190919545345701492817920 

noncomputable def Ns312p627 := nat_lit 71366317753670244020897682633755897477478631277417021766182024402324621999406942494976 

noncomputable def Ns312p628 := nat_lit 949574837374579115515677203222545174590267484595754751322197895374410563200359898007183616 

noncomputable def Ns312p629 := nat_lit 902343280141916883526725551037591732278267640006707698523977839674948591379540556567176806400 

noncomputable def Ns312p630 := BSN.cos_dyadic_bound_f 53912151174 68719476736 3 2 33554432 8828614 Ns312p625 Ns312p626 Ns312p627 Ns312p628 Ns312p629 Ns312p627 23747273 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 53912151174) (BSN.cosEvenQ 68719476736) 0 2 Ns312p625 Ns312p626 Ns312p627 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 53912151174) (BSN.cosOddQ 68719476736) 0 2 Ns312p628 Ns312p629 Ns312p627 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p631 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz96) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4839174167) qz595) Bool.false 4839174167 4194304 313 33554432 Bool.true 23747273 33554432 1 4410000 (Ns312p624 rfl) (Enclosure.sfrac_false_div 4839174167 4194304) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4839174167) qz595) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474216296760069790367744) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 23747273 33554432 183 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q2 4839174167 4194304 226375608064910080 72057594037927936 183 474216296760069790367744 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 23747273 33554432 474216296760069790367744 604462909807314587353088 53912151174 68719476736 8828614 8820000 (Ns312p630 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns312p632 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz96) Bool.false Ns312p603 Ns312p604 93590230822046303 10035200000000000000000 309707146688 268435456 2504 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz96) (@HAdd.hAdd Real Real Real qz367 qz100 (Enclosure.sfrac Bool.true Ns312p605 Ns312p606)) Bool.false Ns312p603 Ns312p604 93590230822046303 10035200000000000000000 Ns312p607 (Ns312p623 rfl rfl)) 

noncomputable def Ns312p633 := Ns312p602 55772 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 453 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 49667591 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 288 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 183406919 268435456) qz99 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 1) Bool.true 23747273 33554432 88367777 9248440320000 189978184 268435456 2565 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz96)) Bool.true 23747273 33554432 88367777 9248440320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz96) qz96) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz96)) Bool.true 23747273 33554432 1413884432 147975045120000 23747273 33554432 88367777 9248440320000 (Ns312p631 rfl rfl) rfl)) rfl) (Ns312p632 rfl) RS313to324.d7 

noncomputable def Ns312p634 := nat_lit 6227750264876738394268271079361 

noncomputable def Ns312p635 := BSN.sin_dyadic_bound_f 49955441 268435456 2 1 268435456 134217728 Ns312p634 Ns312p115 Ns312p634 Ns312p634 Ns312p116 Ns312p634 49667591 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 49955441) qz370 0 1 Ns312p634 Ns312p115 Ns312p634 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 49955441) qz371 0 1 Ns312p634 Ns312p116 Ns312p634 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p636 := nat_lit 20343782260431812595850551753584633922899828645492762530422573488800000 

noncomputable def Ns312p637 := nat_lit 5436178067716658965895102354085842094811077933869360431824100000000 

noncomputable def Ns312p638 := nat_lit 61020474425160004469619865056045730084509863780610548870404072266400000 

noncomputable def Ns312p639 := BSN.cos_dyadic_bound_f 219741310 268435456 3 2 268435456 134217728 Ns312p636 Ns312p123 Ns312p637 Ns312p638 Ns312p126 Ns312p637 183406919 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 219741310) qz372 0 2 Ns312p636 Ns312p123 Ns312p637 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 219741310) qz373 0 2 Ns312p638 Ns312p126 Ns312p637 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p640 := nat_lit 146905823111493526557839395655156299934316687724116484462465313627157825 

noncomputable def Ns312p641 := nat_lit 87433589727885821308155152246210597798129881471847662754075640837441 

noncomputable def Ns312p642 := nat_lit 384611787099114087750318546945582158860108638516969705947712079890724161 

noncomputable def Ns312p643 := BSN.sin_dyadic_bound_f 310963767 268435456 3 2 268435456 134217728 Ns312p640 Ns312p259 Ns312p641 Ns312p642 Ns312p262 Ns312p641 245933890 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 310963767) qz370 0 2 Ns312p640 Ns312p259 Ns312p641 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 310963767) qz371 0 2 Ns312p642 Ns312p262 Ns312p641 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p644 := nat_lit 17332129838227694817257548291521 

noncomputable def Ns312p645 := BSN.sin_dyadic_bound_f 64522767 268435456 2 1 268435456 134217728 Ns312p644 Ns312p115 Ns312p644 Ns312p644 Ns312p116 Ns312p644 63903249 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 64522767) qz370 0 1 Ns312p644 Ns312p115 Ns312p644 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 64522767) qz371 0 1 Ns312p644 Ns312p116 Ns312p644 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p646 := Ns312p600 95016 BSN.abs_quadSignPos (BSN.cos_quad_nat3 171 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 245933890 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 81 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 63903249 268435456) qz99 rfl rfl (Ns312p633 RS313to324.d9 RS313to324.d11 RS313to324.d13 RS313to324.d17 (Ns312p635 rfl rfl) (Ns312p639 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns312p632 rfl) RS313to324.d19 RS313to324.d21 RS313to324.d23 RS313to324.d25 RS313to324.d17 (Ns312p643 rfl rfl) (Ns312p645 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns312p647 := nat_lit 12194341497348599330056756121521 

noncomputable def Ns312p648 := BSN.sin_dyadic_bound_f 59093483 268435456 2 1 268435456 134217728 Ns312p647 Ns312p115 Ns312p647 Ns312p647 Ns312p116 Ns312p647 58617342 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 59093483) qz370 0 1 Ns312p647 Ns312p115 Ns312p647 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 59093483) qz371 0 1 Ns312p647 Ns312p116 Ns312p647 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p649 := nat_lit 18077410100743597359677371808344268495288123324808875672934157809418240 

noncomputable def Ns312p650 := nat_lit 1325336430843391287165934003268359177127314075515949275412703543296 

noncomputable def Ns312p651 := nat_lit 47343452100107103784690086081086840144229735913615267606476887980834816 

noncomputable def Ns312p652 := BSN.sin_dyadic_bound_f 184200484 268435456 3 2 268435456 134217728 Ns312p649 Ns312p259 Ns312p650 Ns312p651 Ns312p262 Ns312p650 170081261 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 184200484) qz370 0 2 Ns312p649 Ns312p259 Ns312p650 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 184200484) qz371 0 2 Ns312p651 Ns312p262 Ns312p650 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p653 := Ns312p598 128087 BSN.abs_quadSignPos (BSN.cos_quad_nat3 7 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 58617342 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 55 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 170081261 268435456) qz99 rfl rfl (Ns312p646 rfl rfl) (Ns312p632 rfl) RS313to324.d27 RS313to324.d29 RS313to324.d31 RS313to324.d33 RS313to324.d17 (Ns312p648 rfl rfl) (Ns312p652 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p654 := nat_lit 85157196913054754587165571720742946439891649982530798204396259591840000 

noncomputable def Ns312p655 := nat_lit 29394105321599810575219382473206467568471796443898513929984100000000 

noncomputable def Ns312p656 := nat_lit 222983163363670338511168999316036811156986319426671492941341658007200000 

noncomputable def Ns312p657 := BSN.sin_dyadic_bound_f 271351690 268435456 3 2 268435456 134217728 Ns312p654 Ns312p259 Ns312p655 Ns312p656 Ns312p262 Ns312p655 227442935 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 271351690) qz370 0 2 Ns312p654 Ns312p259 Ns312p655 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 271351690) qz371 0 2 Ns312p656 Ns312p262 Ns312p655 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p658 := nat_lit 21687528233766598995501094468173213893732232417922752853245387300390625 

noncomputable def Ns312p659 := nat_lit 1907484924272694333660479785944964390908009932375671215972900390625 

noncomputable def Ns312p660 := nat_lit 56797580874749413006915035211276411207903900507050030195578724900390625 

noncomputable def Ns312p661 := BSN.sin_dyadic_bound_f 192778075 268435456 3 2 268435456 134217728 Ns312p658 Ns312p259 Ns312p659 Ns312p660 Ns312p262 Ns312p659 176629439 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 192778075) qz370 0 2 Ns312p658 Ns312p259 Ns312p659 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 192778075) qz371 0 2 Ns312p660 Ns312p262 Ns312p659 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p662 := Ns312p596 156983 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 109 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 227442935 268435456) BSN.abs_quadSignNeg qz590 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 176629439 268435456) qz99 rfl rfl (Ns312p653 rfl) (Ns312p632 rfl) RS313to324.d35 RS313to324.d37 RS313to324.d39 RS313to324.d41 RS313to324.d17 (Ns312p657 rfl rfl) (Ns312p661 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p663 := nat_lit 744765424065701215475624335492858533343884540804923946176823655792896 

noncomputable def Ns312p664 := nat_lit 7289419073730121785323084841546472387705192018976620910569718016 

noncomputable def Ns312p665 := nat_lit 2234281693358956186183302360308892507086878212030733885288649827942656 

noncomputable def Ns312p666 := BSN.cos_dyadic_bound_f 96125058 268435456 3 2 268435456 134217728 Ns312p663 Ns312p123 Ns312p664 Ns312p665 Ns312p126 Ns312p664 251407694 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 96125058) qz372 0 2 Ns312p663 Ns312p123 Ns312p664 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 96125058) qz373 0 2 Ns312p665 Ns312p126 Ns312p664 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p667 := Ns312p594 Bool.true 75894501 156983 Bool.true 96125058 14148475504056880 1 Bool.false 251407694 Bool.false Bool.false 3607591 170287 BSN.abs_quadSignPos qz374 (BSN.sfrac_eq_quadSignPos_mul Bool.false 251407694 268435456) qz99 rfl (Ns312p662 rfl) (Ns312p632 rfl) RS313to324.d43 RS313to324.d45 RS313to324.d17 (Ns312p666 rfl rfl) rfl 

noncomputable def Ns312p668 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) 3607591 268435456 170287 268435456 3607591 268435456 170287 268435456 1936810670292992 3607591 134217728 170287 134217728 (Ns312p667 rfl rfl rfl rfl) 

noncomputable def Ns312p669 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz97) (Zeta.RiemannSiegel.correction qz98) 10571767 33554432 1 33554432 107025462913941 140737488355328 98301186343987 7388718138654720000 1131448256993325303747 4722366482869645213696 

noncomputable def Ns312p670 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz97 1 1 0 1 10571767 33554432 1 33554432 10571767 33554432 1 33554432 

noncomputable abbrev qz105 := qz430

noncomputable def Ns312p671 := @Enclosure.Real.IsNear.sqrt_image qz105 170266474699 1677721600 31883 1677721600 169014700 169014732 16777216 (@Enclosure.Real.IsNear.of_eq qz105 (@HMul.hMul Real Real Real qz5 qz96 qz3) Bool.false 170266474699 1677721600 31883 1677721600 (BSN.t_div_two_pi_mk qz96 637660 1000 qz99) (@Enclosure.Real.IsNear.mulLit_ff qz96 qz3 637660 1000 0 1 5340353 33554432 1 33554432 170266474699 1677721600 31883 1677721600 (Enclosure.Real.IsNear.const Bool.false 637660 1000) RS313to324.d48 rfl)) 

noncomputable abbrev qz735 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 637660 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz631 := qz735

noncomputable abbrev qz438 := qz631

noncomputable abbrev qz106 := qz438

noncomputable def Ns312p672 := @Enclosure.Real.IsNear.sqrt_image qz106 42253679 4194304 1 1048576 53250315 53250321 16777216 (@Enclosure.Real.IsNear.recentre' qz106 Bool.false 338029432 33554432 32 33554432 42253679 4194304 1 1048576 (Ns312p671 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns312p673 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz106) 26625159 8388608 3 16777216 5285883 5285884 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz106) Bool.false 106500636 33554432 6 33554432 26625159 8388608 3 16777216 (Ns312p672 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns312p674 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz106)) Bool.false 10571767 33554432 1 33554432 10571767 33554432 1 33554432 (Ns312p673 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz107 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz431))

noncomputable abbrev qz632 := (@HMul.hMul Real Real Real qz711 qz734 qz734)

noncomputable abbrev qz439 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz632 qz627) qz594)

noncomputable abbrev qz108 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz439))

noncomputable def Ns312p675 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz98) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz107) qz108) Bool.false 107025462913941 

noncomputable def Ns312p676 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz107) qz108 18773469 16777216 33 

noncomputable def Ns312p677 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz107) Bool.false 37546938 33554432 264 33554432 18773469 16777216 33 

noncomputable def Ns312p678 := @Enclosure.Real.IsNear.recentre' qz107 Bool.false 14993232 16777216 462187216 73987522560000 937077 1048576 28886701 4624220160000 

noncomputable abbrev qz109 := (@HMul.hMul Real Real Real qz349 qz346 qz431)

noncomputable def Ns312p679 := @Enclosure.Real.IsNear.cos_image qz109 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15614419) qz368) Bool.false 15614419 33554432 101 16777216 Bool.false 14993232 16777216 1 

noncomputable def Ns312p680 := nat_lit 26986075409711137628100039 

noncomputable def Ns312p681 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz98 884279719003555 140737488355328 1 500000000000000 310639 4194304 1 1048576 274691767631545321645 590295810358705651712 Ns312p680 

noncomputable def Ns312p682 := @Enclosure.Real.IsNear.subLit_ff_p qz106 qz1 42253679 4194304 1 1048576 10 1 0 1 310639 310639 4194304 1 

noncomputable def Ns312p683 := @Ns312p682 1048576 (@Enclosure.Real.IsNear.recentre' qz106 Bool.false 338029432 33554432 32 33554432 42253679 4194304 1 1048576 (Ns312p671 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns312p684 := @Enclosure.Real.IsNear.recentre' qz109 Bool.false 274691767631545321645 590295810358705651712 Ns312p680 Ns312p296 15614419 33554432 101 16777216 (@Ns312p681 Ns312p296 RS313to324.d47 (Ns312p683 rfl rfl) rfl) 

noncomputable def Ns312p685 := nat_lit 59443355454627408530402568721 

noncomputable def Ns312p686 := BSN.cos_dyadic_bound_f 15614419 33554432 2 1 16777216 4410000 Ns312p685 Ns312p302 Ns312p685 Ns312p685 Ns312p303 Ns312p685 14993232 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 15614419) qz395 0 1 Ns312p685 Ns312p302 Ns312p685 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 15614419) (BSN.cosOddQ 33554432) 0 1 Ns312p685 Ns312p303 Ns312p685 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p687 := @Enclosure.Real.IsNear.inv_image qz107 937077 1048576 28886701 4624220160000 18773337 18773601 16777216 (Ns312p678 (@Ns312p679 4410000 (Ns312p684 rfl) (Enclosure.sfrac_false_div 15614419 33554432) (Ns312p686 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns312p688 := @Enclosure.Real.IsNear.recentre' qz108 Bool.false 11401778 16777216 

noncomputable abbrev qz110 := (@HMul.hMul Real Real Real qz349 qz346 qz439)

noncomputable def Ns312p689 := @Enclosure.Real.IsNear.cos_image qz110 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 27634777)) qz368) Bool.true 27634777 33554432 

noncomputable def Ns312p690 := nat_lit 2039086636989668100367172605 

noncomputable def Ns312p691 := nat_lit 12995376693968872444249647946539 

noncomputable def Ns312p692 := @Enclosure.Real.IsNear.recentre' qz110 Bool.true Ns312p690 Ns312p574 Ns312p691 

noncomputable def Ns312p693 := nat_lit 1888946593147858085478400000000000000 

noncomputable abbrev qz111 := qz439

noncomputable def Ns312p694 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz111 884279719003555 140737488355328 1 500000000000000 2305929439711 

noncomputable abbrev qz440 := (@HSub.hSub Real Real Real qz583 qz632 qz627)

noncomputable abbrev qz112 := qz440

noncomputable def Ns312p695 := @Enclosure.Real.IsNear.subLit_tf qz112 qz29 1206417811935 17592186044416 2407793 2199023255552 1 16 

noncomputable abbrev qz441 := qz632

noncomputable abbrev qz113 := qz441

noncomputable def Ns312p696 := @Enclosure.Real.IsNear.subLit_ff_n qz113 qz98 96496588321 17592186044416 310641 2199023255552 310639 4194304 1 1048576 

noncomputable def Ns312p697 := @Enclosure.Real.IsNear.mulLit_ff qz98 qz98 310639 4194304 1 1048576 310639 4194304 1 1048576 96496588321 17592186044416 

noncomputable def Ns312p698 := nat_lit 1242371904449445931886098835414290203033641880846783550401831361 

noncomputable def Ns312p699 := nat_lit 340132174044748766833366470854081689092409485658321000620481 

noncomputable def Ns312p700 := nat_lit 3726435449000248298124629773301162445722740823569034009204253121 

noncomputable def Ns312p701 := BSN.cos_dyadic_bound_f 27634777 33554432 3 2 16777216 4410000 Ns312p698 Ns312p463 Ns312p699 Ns312p700 Ns312p466 Ns312p699 11401778 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 27634777) qz395 0 2 Ns312p698 Ns312p463 Ns312p699 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 27634777) (BSN.cosOddQ 33554432) 0 2 Ns312p700 Ns312p466 Ns312p699 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p702 := @Ns312p688 1052264432 147975045120000 5700889 8388608 65766527 9248440320000 (@Ns312p689 231 33554432 Bool.false 11401778 16777216 1 4410000 (@Ns312p692 Ns312p693 27634777 33554432 231 33554432 (@Ns312p694 17592186044416 2407793 2199023255552 Ns312p690 Ns312p574 Ns312p691 Ns312p693 RS313to324.d47 (@Ns312p695 0 1 36894871035376 2305929439711 17592186044416 2407793 2199023255552 (@Ns312p696 5060083054270218240 1206417811935 17592186044416 2407793 2199023255552 (@Ns312p697 310641 2199023255552 (Ns312p683 rfl rfl) (Ns312p683 rfl rfl) rfl) (Ns312p683 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 27634777 33554432) (BSN.cos_neg_of_bound 27634777 33554432 Bool.false 11401778 16777216 1 4410000 (Ns312p701 rfl rfl)) rfl rfl) 

noncomputable def Ns312p703 := @Ns312p669 261209043239095165379 Ns312p591 (Ns312p670 qz31 (@Enclosure.Real.IsNear.of_eq qz97 (@Inv.inv Real Real.instInv (Real.sqrt qz106)) Bool.false 10571767 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz105 (BSN.t_div_two_pi_nonneg qz96 637660 1000 qz99)) Ns312p674) rfl) (@Ns312p675 140737488355328 98301186343987 7388718138654720000 (BSN.correction_mk qz98 (BSN.cos_two_pi_p_ne_zero_mk qz96 637660 1000 10 qz99 rfl rfl (@BSN.floor_sqrt_eq_dec qz96 637660 1000 10 qz99 rfl rfl rfl))) (@Ns312p676 4194304 5700889 8388608 65766527 9248440320000 107025462913941 140737488355328 98301186343987 7388718138654720000 (@Ns312p677 4194304 (Ns312p687 rfl rfl rfl rfl rfl) rfl) (Ns312p702 rfl) rfl)) 

noncomputable def Ns312p704 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz96) (hardyZApproximantRS₀ qz96) Bool.true 1004517432905003780035 4722366482869645213696 78898874398057614205379 Ns312p591 (@Eq.refl Real (hardyZApproximantRS₀ qz96)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz96) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz97) (Zeta.RiemannSiegel.correction qz98))) Bool.true 1004517432905003780035 4722366482869645213696 78898874398057614205379 Ns312p591 (BSN.hardyZApproximantRS₀_eq qz96 10 (@BSN.floor_sqrt_eq_dec qz96 637660 1000 10 qz99 rfl rfl rfl)) (@Ns312p593 1004517432905003780035 4722366482869645213696 78898874398057614205379 Ns312p591 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz96) qz96 10)) Bool.false 3607591 134217728 170287 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz96) qz96 10) (Ns312p668 (Ns312p667 rfl rfl rfl rfl) rfl rfl)) (Ns312p703 rfl) rfl rfl)) 

theorem RS313to324.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz96) Bool.true 1004517432905003780035 4722366482869645213696 78898874398057614205379 Ns312p591 := Ns312p704 

noncomputable def Ns312p705 := nat_lit 72311236768941442334720000 

noncomputable def Ns312p706 := nat_lit 43673174485125945758893211648 

noncomputable abbrev qz736 := (Enclosure.sfrac Bool.false 638340 1000)

noncomputable abbrev qz633 := qz736

noncomputable abbrev qz442 := qz633

noncomputable abbrev qz114 := qz442

noncomputable abbrev qz737 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 638340 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz634 := qz737

noncomputable abbrev qz443 := qz634

noncomputable abbrev qz115 := (@HPow.hPow Real Real Real qz350 qz443 qz352)

noncomputable abbrev qz738 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 638340 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz635 := qz738

noncomputable abbrev qz444 := qz635

noncomputable abbrev qz116 := qz444

noncomputable def Ns312p707 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz115) (Zeta.RiemannSiegel.correction qz116)) 26421301 33554432 170477 134217728 557671745210265344925 2361183241434822606848 320563433481652260853 Ns312p705 Ns312p706 

noncomputable def Ns312p708 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.cos BSN.quadSignPos 9 10 638340 1000 200 268435456 134217728 4503599627370496 Bool.false 310128847308 2507 618095470 62 84886744 8 

noncomputable def Ns312p709 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 638340 1000 109 157 268435456 134217728 4503599627370496 Bool.false 310128847308 2507 

noncomputable def Ns312p710 := Ns312p709 558195838 62 94906264 8 589812974 62 89478488 8 Bool.false 151106226 128231 Bool.true 229224239 Bool.true 172150277 14148475504056880 1 Bool.false 202364430 Bool.true Bool.false 160590298 Bool.true Bool.false 26029495 

noncomputable def Ns312p711 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 638340 1000 7 55 268435456 134217728 4503599627370496 Bool.false 310128847308 2507 

noncomputable def Ns312p712 := Ns312p711 480971758 62 109588312 8 522351262 62 101459064 8 Bool.false 48645679 95124 Bool.false 153733308 Bool.true 117698722 14148475504056880 1 Bool.false 145466306 Bool.false Bool.false 113963566 Bool.false Bool.false 151106226 

noncomputable def Ns312p713 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 638340 1000 172 81 268435456 134217728 4503599627370496 Bool.false 310128847308 2507 

noncomputable def Ns312p714 := Ns312p713 372130544 61 134217720 8 432030192 61 120047984 16 Bool.true 3577586 55838 Bool.false 57958189 Bool.false 192442857 14148475504056880 1 Bool.false 262202817 Bool.false Bool.false 176376875 Bool.true Bool.false 48645679 

noncomputable def Ns312p715 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 638340 1000 453 289 268435456 134217728 4503599627370496 Bool.false 310128847308 2507 

noncomputable def Ns312p716 := Ns312p715 186065264 61 189812528 16 294906480 61 154981288 8 Bool.false 189677288 2573 Bool.false 345131681 Bool.false 19248095 14148475504056880 1 Bool.false 257601127 Bool.true Bool.false 19231605 Bool.true Bool.true 3577586 

noncomputable def Ns312p717 := nat_lit 16785926105949238586907220759736146861270297 

noncomputable def Ns312p718 := nat_lit 14529244111708799295665352196706061516800 

noncomputable def Ns312p719 := nat_lit 50874740705286022824548352000000000 

noncomputable def Ns312p720 := nat_lit 194852347680001249404233947054080000000 

noncomputable abbrev qz636 := (@Eq.refl Real qz736)

noncomputable abbrev qz445 := qz636

noncomputable abbrev qz117 := qz445

noncomputable def Ns312p721 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz114 638340 1000 1629912822400 16000000 1276680 4000 2000 Ns312p719 Ns312p720 qz117 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns312p722 := nat_lit 24751855198788509250709911443476532715754729144320000000 

noncomputable abbrev qz637 := (@HSub.hSub Real Real Real qz715 qz716 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz717 (@Nat.cast Real Real.instNatCast 1276680))))

noncomputable abbrev qz446 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 638340 4000) (Real.log (Enclosure.sfrac Bool.false 1629912822400 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz637))

noncomputable abbrev qz638 := (Enclosure.sfrac Bool.false 638340 2000)

noncomputable abbrev qz118 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz446 qz638) (@HMul.hMul Real Real Real qz349 qz638 (Real.log Real.pi)))

noncomputable def Ns312p723 := @Enclosure.Real.IsNear.addLit_ft_p qz118 (Enclosure.sfrac Bool.true Ns312p719 Ns312p720) 127028804565262229 109951162777600 843204858210484673 90316800000000000000000 Ns312p719 Ns312p720 0 1 Ns312p722 

noncomputable def Ns312p724 := nat_lit 85247587696527620502978560 

noncomputable abbrev qz119 := (@HSub.hSub Real Real Real qz355 qz446 qz638)

noncomputable def Ns312p725 := @Enclosure.Real.IsNear.subLit_ff_p qz119 (@HMul.hMul Real Real Real qz5 qz638 (Real.log Real.pi)) 33440187850966609 21990232555520 403962725217377 88200000000000000000 1225956258837 3355443200 31917 6710886400 Ns312p724 127028804565262229 109951162777600 

noncomputable abbrev qz120 := qz446

noncomputable def Ns312p726 := @Enclosure.Real.IsNear.subLit_ff_p qz120 qz638 202294051878559637 109951162777600 403962725217377 88200000000000000000 638340 2000 0 1 334401878509666090000 33440187850966609 21990232555520 403962725217377 88200000000000000000 

noncomputable def Ns312p727 := nat_lit 233229162664844535689025082949107712 

noncomputable def Ns312p728 := nat_lit 55762662657166292589477888 

noncomputable def Ns312p729 := nat_lit 197570854074184785578062552253579109766186488507304378051754715282350329303593315724090896795032277171044352000000000000000000000 

noncomputable def Ns312p730 := nat_lit 3192999173698954808212499767045686959650465346189096720197901000128498786962228633663616798386994566030950400000000000000000000 

noncomputable def Ns312p731 := nat_lit 4165912394149873125752441462762608330323586336847173796343043957413642197544038687533423425887404032000000000000000000000 

noncomputable def Ns312p732 := BSN.log_dyadic_bound 581336822400 2678488822400 6 5 Ns312p729 134217728 35280000 Ns312p730 Ns312p731 59202564 3259825644800 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 581336822400) (BSN.artanhQ 2678488822400) 0 5 Ns312p730 Ns312p729 Ns312p731 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz447 := (Real.log (Enclosure.sfrac Bool.false 1629912822400 16000000))

noncomputable def Ns312p733 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 638340 4000) qz447 638340 4000 0 1 3245814159580407 281474976710656 781250441 27562500000000000 103596650531327850219 56294995342131200 8311723441799 1837500000000000000 (Enclosure.Real.IsNear.const Bool.false 638340 4000) (BSN.isNear_log_sfrac 1629912822400 16000000 3245814159580407 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1629912822400) qz358)) Bool.false Ns312p728 Ns312p99 1000000564480000 35280000000000000000000 3245814159580407 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1629912822400 16000000 16 3259825644800 2097152000000 59202564 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns312p732 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns312p734 := BSN.arctan_dyadic_bound_f 1000 1276680 1 0 16777216 4410000 0 1 1 0 1 1 13141 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1276680) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1276680) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz448 := (@Nat.cast Real Real.instNatCast 1276680)

noncomputable def Ns312p735 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz448)) 884279719003555 562949953421312 1 2000000000000000 13141 16777216 1 4410000 14828354124804037541888 883838780212643 562949953421312 200000000441 882000000000000000 qz15 (Ns312p734 rfl) rfl rfl 

noncomputable abbrev qz449 := (@HMul.hMul Real Real Real qz579 qz584 qz637)

noncomputable abbrev qz121 := qz449

noncomputable abbrev qz450 := qz637

noncomputable abbrev qz122 := qz450

noncomputable def Ns312p736 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 638340 4000) qz447) qz121 103596650531327850219 56294995342131200 8311723441799 1837500000000000000 883838780212643 2251799813685248 200000000441 3528000000000000000 Ns312p727 202294051878559637 109951162777600 403962725217377 88200000000000000000 (Ns312p733 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz122 1 4 0 1 883838780212643 562949953421312 200000000441 882000000000000000 883838780212643 2251799813685248 200000000441 3528000000000000000 qz366 Ns312p735 rfl) 

noncomputable def Ns312p737 := @Ns312p723 Ns312p717 Ns312p718 843204858210484673 90316800000000000000000 (@Ns312p725 843204858210484673 90316800000000000000000 (Ns312p726 (Ns312p736 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 638340 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz638 (Real.log Real.pi) 638340 2000 0 1 38410761 33554432 1 67108864 1225956258837 3355443200 31917 6710886400 (Enclosure.Real.IsNear.const Bool.false 638340 2000) RS313to324.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns312p719 Ns312p720) 

noncomputable def Ns312p738 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz114) Bool.false Ns312p717 Ns312p718 843204858210484673 90316800000000000000000 38766105913 33554432 157 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz114) (@HAdd.hAdd Real Real Real qz367 qz118 (Enclosure.sfrac Bool.true Ns312p719 Ns312p720)) Bool.false Ns312p717 Ns312p718 843204858210484673 90316800000000000000000 Ns312p721 (Ns312p737 rfl rfl)) 

noncomputable def Ns312p739 := nat_lit 3794508375125915951169536 

noncomputable def Ns312p740 := nat_lit 570241037595988174302004376216732630896306073441015375574638031789811845767280331276222720 

noncomputable def Ns312p741 := nat_lit 180468656028383376705345110207518346455653528001341539704795567934989718275908111313435361280 

noncomputable def Ns312p742 := nat_lit 71483485678730292569882767477138808819471425273370578258137164374871491845328552919296 

noncomputable def Ns312p743 := nat_lit 1493372696631727274126803079896479618085570095752216716997348337373852661260841764256809216 

noncomputable def Ns312p744 := nat_lit 3308592027187028572931327020471169685020314680024594894587918745474811501724982040746314956800 

noncomputable def Ns312p745 := BSN.sin_dyadic_bound_f 53923207234 68719476736 3 2 33554432 8828614 Ns312p740 Ns312p741 Ns312p742 Ns312p743 Ns312p744 Ns312p742 23709661 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 53923207234) qz602 0 2 Ns312p740 Ns312p741 Ns312p742 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 53923207234) qz603 0 2 Ns312p743 Ns312p744 Ns312p742 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p746 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz114) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 38766105913) qz368) Bool.false 38766105913 33554432 157 16777216 Bool.false 23709661 33554432 1 4410000 (Ns312p738 rfl) (Enclosure.sfrac_false_div 38766105913 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 38766105913) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns312p739) qz369) 226375608064910080 72057594037927936 Bool.false 23709661 33554432 183 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q3 38766105913 33554432 226375608064910080 72057594037927936 183 Ns312p739 Ns312p99 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 23709661 33554432 Ns312p739 Ns312p99 53923207234 68719476736 8828614 8820000 (Ns312p745 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns312p747 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz114) Bool.false Ns312p717 Ns312p718 843204858210484673 90316800000000000000000 310128847308 268435456 2507 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz114) (@HAdd.hAdd Real Real Real qz367 qz118 (Enclosure.sfrac Bool.true Ns312p719 Ns312p720)) Bool.false Ns312p717 Ns312p718 843204858210484673 90316800000000000000000 Ns312p721 (Ns312p737 rfl rfl)) 

noncomputable def Ns312p748 := Ns312p716 55838 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 453 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 257601127 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 289 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 19231605 268435456) qz117 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 1) Bool.false 23709661 33554432 44321701 4624220160000 189677288 268435456 2573 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz114)) Bool.false 23709661 33554432 44321701 4624220160000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz114) qz114) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz114)) Bool.false 23709661 33554432 709147216 73987522560000 23709661 33554432 44321701 4624220160000 (Ns312p746 rfl rfl) rfl)) rfl) (Ns312p747 rfl) RS313to324.d7 

noncomputable def Ns312p749 := nat_lit 19867798164848113457488185140657080537922216234252791381959537830612797960802510950810439573783794453472626561 

noncomputable def Ns312p750 := nat_lit 2856392740993674704325159160804742078597910096348971190507773519377967977915410858290742208764208498561 

noncomputable def Ns312p751 := nat_lit 99283537046956748780024398754400778381362633478218511252019754851672088726298862155720622842833778449799989121 

noncomputable def Ns312p752 := BSN.sin_dyadic_bound_f 345131681 268435456 4 3 268435456 134217728 Ns312p749 Ns312p147 Ns312p750 Ns312p751 Ns312p150 Ns312p750 257601127 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 345131681) qz370 0 3 Ns312p749 Ns312p147 Ns312p750 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 345131681) qz371 0 3 Ns312p751 Ns312p150 Ns312p750 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p753 := nat_lit 137262218514088649012697450625 

noncomputable def Ns312p754 := BSN.sin_dyadic_bound_f 19248095 268435456 2 1 268435456 134217728 Ns312p753 Ns312p115 Ns312p753 Ns312p753 Ns312p116 Ns312p753 19231605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 19248095) qz370 0 1 Ns312p753 Ns312p115 Ns312p753 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 19248095) qz371 0 1 Ns312p753 Ns312p116 Ns312p753 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p755 := nat_lit 11283899956573449712432534797841 

noncomputable def Ns312p756 := BSN.cos_dyadic_bound_f 57958189 268435456 2 1 268435456 134217728 Ns312p755 Ns312p119 Ns312p755 Ns312p755 Ns312p120 Ns312p755 262202817 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 57958189) qz372 0 1 Ns312p755 Ns312p119 Ns312p755 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 57958189) qz373 0 1 Ns312p755 Ns312p120 Ns312p755 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p757 := nat_lit 21537060032949364686325380150057330757868355006382712801490485798755905 

noncomputable def Ns312p758 := nat_lit 1881110754740931134905681575906046583294842879564096493286584475201 

noncomputable def Ns312p759 := nat_lit 56403540192693041242348053099027256480901309556816382133390713098067521 

noncomputable def Ns312p760 := BSN.sin_dyadic_bound_f 192442857 268435456 3 2 268435456 134217728 Ns312p757 Ns312p259 Ns312p758 Ns312p759 Ns312p262 Ns312p758 176376875 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 192442857) qz370 0 2 Ns312p757 Ns312p259 Ns312p758 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 192442857) qz371 0 2 Ns312p759 Ns312p262 Ns312p758 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p761 := Ns312p714 95124 BSN.abs_quadSignPos (BSN.cos_quad_nat0 172 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 262202817 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 81 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 176376875 268435456) qz117 rfl rfl (Ns312p748 RS313to324.d9 RS313to324.d11 RS313to324.d13 RS313to324.d17 (Ns312p752 rfl rfl) (Ns312p754 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns312p747 rfl) RS313to324.d19 RS313to324.d21 RS313to324.d23 RS313to324.d25 RS313to324.d17 (Ns312p756 rfl rfl) (Ns312p760 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns312p762 := nat_lit 8770586573426256943643275681771014630381360435224948998456936459468800 

noncomputable def Ns312p763 := nat_lit 311992230296470916384905644755234795322527734258195011357617750016 

noncomputable def Ns312p764 := nat_lit 22970078752505431042343955985975434604187326571162257918321206965108736 

noncomputable def Ns312p765 := BSN.sin_dyadic_bound_f 153733308 268435456 3 2 268435456 134217728 Ns312p762 Ns312p259 Ns312p763 Ns312p764 Ns312p262 Ns312p763 145466306 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 153733308) qz370 0 2 Ns312p762 Ns312p259 Ns312p763 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 153733308) qz371 0 2 Ns312p764 Ns312p262 Ns312p763 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p766 := nat_lit 191905308679082062710590615024656 

noncomputable def Ns312p767 := BSN.sin_dyadic_bound_f 117698722 268435456 2 1 268435456 134217728 Ns312p766 Ns312p115 Ns312p766 Ns312p766 Ns312p116 Ns312p766 113963566 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 117698722) qz370 0 1 Ns312p766 Ns312p115 Ns312p766 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 117698722) qz371 0 1 Ns312p766 Ns312p116 Ns312p766 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p768 := Ns312p712 128231 BSN.abs_quadSignPos (BSN.cos_quad_nat3 7 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 145466306 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 55 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 113963566 268435456) qz117 rfl rfl (Ns312p761 rfl rfl) (Ns312p747 rfl) RS313to324.d27 RS313to324.d29 RS313to324.d31 RS313to324.d33 RS313to324.d17 (Ns312p765 rfl rfl) (Ns312p767 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p769 := nat_lit 43357059080987835504010252066546345038223507519250528106601919130927745 

noncomputable def Ns312p770 := nat_lit 7622269793402667739580226987156926246819695255676236519391405834881 

noncomputable def Ns312p771 := nat_lit 113541861537207393429400863616308840076661954472385050181973630685840001 

noncomputable def Ns312p772 := BSN.sin_dyadic_bound_f 229224239 268435456 3 2 268435456 134217728 Ns312p769 Ns312p259 Ns312p770 Ns312p771 Ns312p262 Ns312p770 202364430 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 229224239) qz370 0 2 Ns312p769 Ns312p259 Ns312p770 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 229224239) qz371 0 2 Ns312p771 Ns312p262 Ns312p770 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p773 := nat_lit 13791023436068843387697604202265322810878275378234224663706905454552545 

noncomputable def Ns312p774 := nat_lit 771368334738567137017012705425731642449360062082394107208625792481 

noncomputable def Ns312p775 := nat_lit 36118098212400251192414745366314679986783898455274835957344509843973601 

noncomputable def Ns312p776 := BSN.sin_dyadic_bound_f 172150277 268435456 3 2 268435456 134217728 Ns312p773 Ns312p259 Ns312p774 Ns312p775 Ns312p262 Ns312p774 160590298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 172150277) qz370 0 2 Ns312p773 Ns312p259 Ns312p774 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 172150277) qz371 0 2 Ns312p775 Ns312p262 Ns312p774 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p777 := Ns312p710 157158 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 109 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 202364430 268435456) BSN.abs_quadSignNeg qz590 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 160590298 268435456) qz117 rfl rfl (Ns312p768 rfl) (Ns312p747 rfl) RS313to324.d35 RS313to324.d37 RS313to324.d39 RS313to324.d41 RS313to324.d17 (Ns312p772 rfl rfl) (Ns312p776 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p778 := nat_lit 702443149247272507791463280786397322148602698303800654136460411453696 

noncomputable def Ns312p779 := nat_lit 6484503845066190753806263455401334076219093625564452030606786816 

noncomputable def Ns312p780 := nat_lit 2107316478734127390992882229832281163777655656724150833505320020787456 

noncomputable def Ns312p781 := BSN.cos_dyadic_bound_f 94729358 268435456 3 2 268435456 134217728 Ns312p778 Ns312p123 Ns312p779 Ns312p780 Ns312p126 Ns312p779 251893472 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 94729358) qz372 0 2 Ns312p778 Ns312p123 Ns312p779 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 94729358) qz373 0 2 Ns312p780 Ns312p126 Ns312p779 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p782 := Ns312p708 Bool.false 26029495 157158 Bool.true 94729358 14148475504056880 1 Bool.false 251893472 Bool.false Bool.false 105685204 170477 BSN.abs_quadSignPos qz374 (BSN.sfrac_eq_quadSignPos_mul Bool.false 251893472 268435456) qz117 rfl (Ns312p777 rfl) (Ns312p747 rfl) RS313to324.d43 RS313to324.d45 RS313to324.d17 (Ns312p781 rfl rfl) rfl 

noncomputable def Ns312p783 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) 105685204 268435456 170477 268435456 105685204 268435456 170477 268435456 56739311856386048 26421301 33554432 170477 134217728 (Ns312p782 rfl rfl rfl rfl) 

noncomputable def Ns312p784 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz115) (Zeta.RiemannSiegel.correction qz116) 5284475 16777216 1 16777216 105530207865543 140737488355328 1080895868499329 77581540455874560000 557671745210265344925 2361183241434822606848 

noncomputable def Ns312p785 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz115 1 1 0 1 5284475 16777216 1 16777216 5284475 16777216 1 16777216 

noncomputable abbrev qz123 := qz443

noncomputable def Ns312p786 := @Enclosure.Real.IsNear.sqrt_image qz123 170448046701 1677721600 31917 1677721600 169104794 169104827 16777216 (@Enclosure.Real.IsNear.of_eq qz123 (@HMul.hMul Real Real Real qz5 qz114 qz3) Bool.false 170448046701 1677721600 31917 1677721600 (BSN.t_div_two_pi_mk qz114 638340 1000 qz117) (@Enclosure.Real.IsNear.mulLit_ff qz114 qz3 638340 1000 0 1 5340353 33554432 1 33554432 170448046701 1677721600 31917 1677721600 (Enclosure.Real.IsNear.const Bool.false 638340 1000) RS313to324.d48 rfl)) 

noncomputable abbrev qz739 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 638340 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz639 := qz739

noncomputable abbrev qz451 := qz639

noncomputable abbrev qz124 := qz451

noncomputable def Ns312p787 := @Enclosure.Real.IsNear.sqrt_image qz124 338209621 33554432 33 33554432 53264506 53264512 16777216 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 338209621 33554432 33 33554432 338209621 33554432 33 33554432 (Ns312p786 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns312p788 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz124) 53264509 16777216 3 16777216 5284474 5284476 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz124) Bool.false 106529018 33554432 6 33554432 53264509 16777216 3 16777216 (Ns312p787 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns312p789 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz124)) Bool.false 10568950 33554432 2 33554432 5284475 16777216 1 16777216 (Ns312p788 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz125 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz444))

noncomputable abbrev qz640 := (@HMul.hMul Real Real Real qz711 qz738 qz738)

noncomputable abbrev qz452 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz640 qz635) qz594)

noncomputable abbrev qz126 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz452))

noncomputable def Ns312p790 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz116) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz125) qz126) Bool.false 105530207865543 

noncomputable def Ns312p791 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz125) qz126 9554007 8388608 35 

noncomputable def Ns312p792 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz125) Bool.false 38216028 33554432 280 33554432 9554007 8388608 35 

noncomputable def Ns312p793 := @Enclosure.Real.IsNear.recentre' qz125 Bool.false 14730729 16777216 59427152 9248440320000 14730729 16777216 3714197 578027520000 

noncomputable abbrev qz127 := (@HMul.hMul Real Real Real qz349 qz346 qz444)

noncomputable def Ns312p794 := @Enclosure.Real.IsNear.cos_image qz127 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4186645) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false 4186645 8388608 13 2097152 Bool.false 14730729 16777216 1 

noncomputable def Ns312p795 := nat_lit 890540488521348261278568103 

noncomputable def Ns312p796 := nat_lit 144115188075855872000000000000000 

noncomputable def Ns312p797 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz116 884279719003555 140737488355328 1 500000000000000 2665301 33554432 33 33554432 2356871619339894145055 4722366482869645213696 Ns312p795 

noncomputable def Ns312p798 := @Enclosure.Real.IsNear.subLit_ff_p qz124 qz1 338209621 33554432 33 33554432 10 1 0 1 2665301 2665301 33554432 33 

noncomputable def Ns312p799 := @Ns312p798 33554432 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 338209621 33554432 33 33554432 338209621 33554432 33 33554432 (Ns312p786 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns312p800 := @Enclosure.Real.IsNear.recentre' qz127 Bool.false 2356871619339894145055 4722366482869645213696 Ns312p795 Ns312p796 4186645 8388608 13 2097152 (@Ns312p797 Ns312p796 RS313to324.d47 (Ns312p799 rfl rfl) rfl) 

noncomputable def Ns312p801 := nat_lit 2555933028820530181208968741439479463253793756882055190625 

noncomputable def Ns312p802 := nat_lit 94390676143999779465418023788540126291592632250390625 

noncomputable def Ns312p803 := nat_lit 7667610305109302544067975388270861309508798085381664790625 

noncomputable def Ns312p804 := BSN.cos_dyadic_bound_f 4186645 8388608 3 2 16777216 4410000 Ns312p801 Ns312p318 Ns312p802 Ns312p803 Ns312p321 Ns312p802 14730729 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 4186645) (BSN.cosEvenQ 8388608) 0 2 Ns312p801 Ns312p318 Ns312p802 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 4186645) (BSN.cosOddQ 8388608) 0 2 Ns312p803 Ns312p321 Ns312p802 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p805 := @Enclosure.Real.IsNear.inv_image qz125 14730729 16777216 3714197 578027520000 19107874 19108154 16777216 (Ns312p793 (@Ns312p794 4410000 (Ns312p800 rfl) (Enclosure.sfrac_false_div 4186645 8388608) (Ns312p804 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns312p806 := @Enclosure.Real.IsNear.recentre' qz126 Bool.false 11045649 16777216 

noncomputable abbrev qz128 := (@HMul.hMul Real Real Real qz349 qz346 qz452)

noncomputable def Ns312p807 := @Enclosure.Real.IsNear.cos_image qz128 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 28593157)) qz368) Bool.true 28593157 33554432 

noncomputable def Ns312p808 := nat_lit 135027369528029892654704492725 

noncomputable def Ns312p809 := nat_lit 158456325028528675187087900672 

noncomputable def Ns312p810 := nat_lit 34628726562786755934203755880839277 

noncomputable def Ns312p811 := @Enclosure.Real.IsNear.recentre' qz128 Bool.true Ns312p808 Ns312p809 Ns312p810 

noncomputable def Ns312p812 := nat_lit 4835703278458516698824704000000000000000 

noncomputable abbrev qz129 := qz452

noncomputable def Ns312p813 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz129 884279719003555 140737488355328 1 500000000000000 152697575921095 

noncomputable abbrev qz453 := (@HSub.hSub Real Real Real qz583 qz640 qz635)

noncomputable abbrev qz130 := qz453

noncomputable def Ns312p814 := @Enclosure.Real.IsNear.subLit_tf qz130 qz29 82328831743431 1125899906842624 1283207211 1125899906842624 1 16 

noncomputable abbrev qz454 := qz640

noncomputable abbrev qz131 := qz454

noncomputable def Ns312p815 := @Enclosure.Real.IsNear.subLit_ff_n qz131 qz116 7103829420601 1125899906842624 175910955 1125899906842624 2665301 33554432 33 33554432 

noncomputable def Ns312p816 := @Enclosure.Real.IsNear.mulLit_ff qz116 qz116 2665301 33554432 33 33554432 2665301 33554432 33 33554432 7103829420601 1125899906842624 

noncomputable def Ns312p817 := nat_lit 1423946167915727504052969136767273931814313826957267693053466081 

noncomputable def Ns312p818 := nat_lit 446783237969917313787803746711419813949423908028614100178401 

noncomputable def Ns312p819 := nat_lit 4270944937271242677531331802808398955815042633055745850960041441 

noncomputable def Ns312p820 := BSN.cos_dyadic_bound_f 28593157 33554432 3 2 16777216 4410000 Ns312p817 Ns312p463 Ns312p818 Ns312p819 Ns312p466 Ns312p818 11045649 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 28593157) qz395 0 2 Ns312p817 Ns312p463 Ns312p818 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 28593157) (BSN.cosOddQ 33554432) 0 2 Ns312p819 Ns312p466 Ns312p818 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p821 := @Ns312p806 1096364432 147975045120000 11045649 16777216 68522777 9248440320000 (@Ns312p807 241 33554432 Bool.false 11045649 16777216 1 4410000 (@Ns312p811 Ns312p812 28593157 33554432 241 33554432 (@Ns312p813 1125899906842624 1283207211 1125899906842624 Ns312p808 Ns312p809 Ns312p810 Ns312p812 RS313to324.d47 (@Ns312p814 0 1 2443161214737520 152697575921095 1125899906842624 1283207211 1125899906842624 (@Ns312p815 2762497186374396936192 82328831743431 1125899906842624 1283207211 1125899906842624 (@Ns312p816 175910955 1125899906842624 (Ns312p799 rfl rfl) (Ns312p799 rfl rfl) rfl) (Ns312p799 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 28593157 33554432) (BSN.cos_neg_of_bound 28593157 33554432 Bool.false 11045649 16777216 1 4410000 (Ns312p820 rfl rfl)) rfl rfl) 

noncomputable def Ns312p822 := @Ns312p784 320563433481652260853 Ns312p705 (Ns312p785 qz31 (@Enclosure.Real.IsNear.of_eq qz115 (@Inv.inv Real Real.instInv (Real.sqrt qz124)) Bool.false 5284475 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz123 (BSN.t_div_two_pi_nonneg qz114 638340 1000 qz117)) Ns312p789) rfl) (@Ns312p790 140737488355328 1080895868499329 77581540455874560000 (BSN.correction_mk qz116 (BSN.cos_two_pi_p_ne_zero_mk qz114 638340 1000 10 qz117 rfl rfl (@BSN.floor_sqrt_eq_dec qz114 638340 1000 10 qz117 rfl rfl rfl))) (@Ns312p791 4194304 11045649 16777216 68522777 9248440320000 105530207865543 140737488355328 1080895868499329 77581540455874560000 (@Ns312p792 4194304 (Ns312p805 rfl rfl rfl rfl rfl) rfl) (Ns312p821 rfl) rfl)) 

noncomputable def Ns312p823 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz114) (hardyZApproximantRS₀ qz114) Bool.false 1301562025699792675939 2361183241434822606848 92166870879982536740853 Ns312p705 (@Eq.refl Real (hardyZApproximantRS₀ qz114)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz114) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz115) (Zeta.RiemannSiegel.correction qz116))) Bool.false 1301562025699792675939 2361183241434822606848 92166870879982536740853 Ns312p705 (BSN.hardyZApproximantRS₀_eq qz114 10 (@BSN.floor_sqrt_eq_dec qz114 638340 1000 10 qz117 rfl rfl rfl)) (@Ns312p707 1301562025699792675939 2361183241434822606848 92166870879982536740853 Ns312p705 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 10)) Bool.false 26421301 33554432 170477 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz114) qz114 10) (Ns312p783 (Ns312p782 rfl rfl rfl rfl) rfl rfl)) (Ns312p822 rfl) rfl rfl)) 

theorem RS313to324.d56 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz114) Bool.false 1301562025699792675939 2361183241434822606848 92166870879982536740853 Ns312p705 := Ns312p823 

noncomputable def Ns312p824 := nat_lit 144622473537882884669440000 

noncomputable def Ns312p825 := nat_lit 98809765636817389252599873536 

noncomputable abbrev qz740 := (Enclosure.sfrac Bool.false 640039 1000)

noncomputable abbrev qz641 := qz740

noncomputable abbrev qz455 := qz641

noncomputable abbrev qz132 := qz455

noncomputable abbrev qz741 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 640039 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz642 := qz741

noncomputable abbrev qz456 := qz642

noncomputable abbrev qz133 := (@HPow.hPow Real Real Real qz350 qz456 qz352)

noncomputable abbrev qz742 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 640039 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz643 := qz742

noncomputable abbrev qz457 := qz643

noncomputable abbrev qz134 := qz457

noncomputable def Ns312p826 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz133) (Zeta.RiemannSiegel.correction qz134)) 76047539 33554432 42733 33554432 269075581945086871875 1180591620717411303424 653889470294202096637 Ns312p824 Ns312p825 

noncomputable def Ns312p827 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.cos BSN.quadSignPos 9 10 640039 1000 200 268435456 134217728 4503599627370496 Bool.false 311182903154 2514 618095470 62 84886744 8 

noncomputable def Ns312p828 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 640039 1000 109 157 268435456 134217728 4503599627370496 Bool.false 311182903154 2514 

noncomputable def Ns312p829 := Ns312p828 558195838 62 94906264 8 589812974 62 89478488 8 Bool.true 303374471 128574 Bool.true 123543122 Bool.true 120186674 14148475504056880 1 Bool.false 119227692 Bool.true Bool.false 116211245 Bool.true Bool.true 384264908 

noncomputable def Ns312p830 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 640039 1000 7 54 268435456 134217728 4503599627370496 Bool.false 311182903154 2514 

noncomputable def Ns312p831 := Ns312p830 480971758 62 109588312 8 522351262 62 101459064 8 Bool.true 393857138 95379 Bool.false 390618137 Bool.true 372775098 14148475504056880 1 Bool.false 266642912 Bool.false Bool.false 48612615 Bool.true Bool.true 303374471 

noncomputable def Ns312p832 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 640039 1000 173 82 268435456 134217728 4503599627370496 Bool.false 311182903154 2514 

noncomputable def Ns312p833 := Ns312p832 372130544 61 134217720 8 432030192 61 120047984 16 Bool.true 251787927 55988 Bool.false 58106812 Bool.false 90821978 14148475504056880 1 Bool.false 57654088 Bool.true Bool.false 253217189 Bool.true Bool.true 393857138 

noncomputable def Ns312p834 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz132) qz132 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 640039 1000 455 290 268435456 134217728 4503599627370496 Bool.false 311182903154 2514 

noncomputable def Ns312p835 := Ns312p834 186065264 61 189812528 16 294906480 61 154981288 8 Bool.true 268435304 2581 Bool.false 239747787 Bool.false 150600404 14148475504056880 1 Bool.false 209121437 Bool.false Bool.false 227286292 Bool.true Bool.true 251787927 

noncomputable def Ns312p836 := nat_lit 807527954405555025867138479466536011213071165138015937261 

noncomputable def Ns312p837 := nat_lit 696597186016021523466645514226724638110935234379776000 

noncomputable def Ns312p838 := nat_lit 51555392646487564546321659615520000 

noncomputable def Ns312p839 := nat_lit 197984828109844535068374828548122831680 

noncomputable abbrev qz644 := (@Eq.refl Real qz740)

noncomputable abbrev qz458 := qz644

noncomputable abbrev qz135 := qz458

noncomputable def Ns312p840 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz132 640039 1000 1638600686084 16000000 1280078 4000 2000 Ns312p838 Ns312p839 qz135 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns312p841 := nat_lit 258408945409777608277484313429291523588182772844165099923520 

noncomputable abbrev qz645 := (@HSub.hSub Real Real Real qz715 qz716 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz717 (@Nat.cast Real Real.instNatCast 1280078))))

noncomputable abbrev qz459 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 640039 4000) (Real.log (Enclosure.sfrac Bool.false 1638600686084 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz645))

noncomputable abbrev qz646 := (Enclosure.sfrac Bool.false 640039 2000)

noncomputable abbrev qz136 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz459 qz646) (@HMul.hMul Real Real Real qz349 qz646 (Real.log Real.pi)))

noncomputable def Ns312p842 := @Enclosure.Real.IsNear.addLit_ft_p qz136 (Enclosure.sfrac Bool.true Ns312p838 Ns312p839) 1305195988616969880389 1125899906842624000 805176664121614871 86016000000000000000000 Ns312p838 Ns312p839 0 1 Ns312p841 

noncomputable def Ns312p843 := nat_lit 87590220093441779795121668096000 

noncomputable abbrev qz137 := (@HSub.hSub Real Real Real qz355 qz459 qz646)

noncomputable def Ns312p844 := @Enclosure.Real.IsNear.subLit_ff_p qz137 (@HMul.hMul Real Real Real qz5 qz646 (Real.log Real.pi)) 1717653526990377354053 1125899906842624000 96434428765901 21000000000000000000 24584385059679 67108864000 640039 134217728000 Ns312p843 1305195988616969880389 1125899906842624000 

noncomputable def Ns312p845 := nat_lit 3435307053980754708106000 

noncomputable abbrev qz138 := qz459

noncomputable def Ns312p846 := @Enclosure.Real.IsNear.subLit_ff_p qz138 qz646 2077963452228200465221 1125899906842624000 96434428765901 21000000000000000000 640039 2000 0 1 Ns312p845 1717653526990377354053 1125899906842624000 96434428765901 21000000000000000000 

noncomputable def Ns312p847 := nat_lit 4679157714572216540623630716064759808 

noncomputable def Ns312p848 := nat_lit 55788369780300075684069376 

noncomputable def Ns312p849 := nat_lit 204073551610151883367335281406425292002670667571806386778693691971932587602791857383299244233500419215118398447636023685304811520 

noncomputable def Ns312p850 := nat_lit 3377804072056528725608879024743474584717388601586648591764688866060240119164860674322120723361603797944598223754903716551983104 

noncomputable def Ns312p851 := nat_lit 4832074633173771366154015249687111419872075261491224440421366130494813076637242020357756688517452414771142661583609528320 

noncomputable def Ns312p852 := BSN.log_dyadic_bound 590024686084 2687176686084 6 5 Ns312p849 134217728 35280000 Ns312p850 Ns312p851 59916080 3277201372168 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 590024686084) (BSN.artanhQ 2687176686084) 0 5 Ns312p850 Ns312p849 Ns312p851 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz460 := (Real.log (Enclosure.sfrac Bool.false 1638600686084 16000000))

noncomputable def Ns312p853 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 640039 4000) qz460 640039 4000 0 1 3247310511086839 281474976710656 781250441 27562500000000000 2078405372205509346721 1125899906842624000 500030751007199 110250000000000000000 (Enclosure.Real.IsNear.const Bool.false 640039 4000) (BSN.isNear_log_sfrac 1638600686084 16000000 3247310511086839 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1638600686084) qz358)) Bool.false Ns312p848 Ns312p99 1000000564480000 35280000000000000000000 3247310511086839 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1638600686084 16000000 16 3277201372168 2097152000000 59916080 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns312p852 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns312p854 := BSN.arctan_dyadic_bound_f 1000 1280078 1 0 16777216 4410000 0 1 1 0 1 1 13106 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1280078) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1280078) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz461 := (@Nat.cast Real Real.instNatCast 1280078)

noncomputable def Ns312p855 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz461)) 884279719003555 562949953421312 1 2000000000000000 13106 16777216 1 4410000 14828373828052407287808 883839954617763 562949953421312 200000000441 882000000000000000 qz15 (Ns312p854 rfl) rfl rfl 

noncomputable abbrev qz462 := (@HMul.hMul Real Real Real qz579 qz584 qz645)

noncomputable abbrev qz139 := qz462

noncomputable abbrev qz463 := qz645

noncomputable abbrev qz140 := qz463

noncomputable def Ns312p856 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 640039 4000) qz460) qz139 2078405372205509346721 1125899906842624000 500030751007199 110250000000000000000 883839954617763 2251799813685248 200000000441 3528000000000000000 Ns312p847 2077963452228200465221 1125899906842624000 96434428765901 21000000000000000000 (Ns312p853 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz140 1 4 0 1 883839954617763 562949953421312 200000000441 882000000000000000 883839954617763 2251799813685248 200000000441 3528000000000000000 qz366 Ns312p855 rfl) 

noncomputable def Ns312p857 := @Ns312p842 Ns312p836 Ns312p837 805176664121614871 86016000000000000000000 (@Ns312p844 805176664121614871 86016000000000000000000 (Ns312p846 (Ns312p856 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 640039 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz646 (Real.log Real.pi) 640039 2000 0 1 38410761 33554432 1 67108864 24584385059679 67108864000 640039 134217728000 (Enclosure.Real.IsNear.const Bool.false 640039 2000) RS313to324.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns312p838 Ns312p839) 

noncomputable def Ns312p858 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz132) Bool.false Ns312p836 Ns312p837 805176664121614871 86016000000000000000000 19448931447 16777216 315 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz132) (@HAdd.hAdd Real Real Real qz367 qz136 (Enclosure.sfrac Bool.true Ns312p838 Ns312p839)) Bool.false Ns312p836 Ns312p837 805176664121614871 86016000000000000000000 Ns312p840 (Ns312p857 rfl rfl)) 

noncomputable def Ns312p859 := nat_lit 3795440288851265453031424 

noncomputable def Ns312p860 := nat_lit 3501537012771562406143000855465432137750865738658288088230907998981749102884276957827055116282496158671861757496667888612869292264000000000 

noncomputable def Ns312p861 := nat_lit 2482837530911572711331112001634938261714232231920689274976282602016336432617671280292814047729624034885045410801025390625000000000000 

noncomputable def Ns312p862 := nat_lit 17485987019936969166718522650353798313817772963893612236531265515546017701410307389826792518555186991275275139885788417804383961320000000000 

noncomputable def Ns312p863 := BSN.sin_dyadic_bound_f 107872901050 68719476736 4 3 33554432 8828614 Ns312p860 Ns312p239 Ns312p861 Ns312p862 Ns312p242 Ns312p861 33554413 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107872901050) qz602 0 3 Ns312p860 Ns312p239 Ns312p861 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107872901050) qz603 0 3 Ns312p862 Ns312p242 Ns312p861 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p864 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz132) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 19448931447) qz378) Bool.false 19448931447 16777216 315 33554432 Bool.true 33554413 33554432 1 4410000 (Ns312p858 rfl) (Enclosure.sfrac_false_div 19448931447 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 19448931447) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns312p859) qz614) 226375608064910080 72057594037927936 Bool.false 33554413 33554432 184 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q1 19448931447 16777216 226375608064910080 72057594037927936 184 Ns312p859 Ns312p394 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554413 33554432 Ns312p859 Ns312p394 107872901050 68719476736 8828614 8820000 (Ns312p863 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns312p865 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz132) Bool.false Ns312p836 Ns312p837 805176664121614871 86016000000000000000000 311182903154 268435456 2514 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz132) (@HAdd.hAdd Real Real Real qz367 qz136 (Enclosure.sfrac Bool.true Ns312p838 Ns312p839)) Bool.false Ns312p836 Ns312p837 805176664121614871 86016000000000000000000 Ns312p840 (Ns312p857 rfl rfl)) 

noncomputable def Ns312p866 := Ns312p835 55988 BSN.abs_quadSignPos (BSN.cos_quad_nat3 455 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 209121437 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 290 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 227286292 268435456) qz135 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 1) Bool.true 33554413 33554432 88919027 9248440320000 268435304 268435456 2581 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz132)) Bool.true 33554413 33554432 88919027 9248440320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz132) qz132) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz132)) Bool.true 33554413 33554432 1422704432 147975045120000 33554413 33554432 88919027 9248440320000 (Ns312p864 rfl rfl) rfl)) rfl) (Ns312p865 rfl) RS313to324.d7 

noncomputable def Ns312p867 := nat_lit 51886108814469054030609489127000327628751894229804826502080712113216865 

noncomputable def Ns312p868 := nat_lit 10915329662927491800474202967333266909523404881092126406286323309921 

noncomputable def Ns312p869 := nat_lit 135874517313678973188681227575434699452687161279681348824601211011161441 

noncomputable def Ns312p870 := BSN.sin_dyadic_bound_f 239747787 268435456 3 2 268435456 134217728 Ns312p867 Ns312p259 Ns312p868 Ns312p869 Ns312p262 Ns312p868 209121437 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 239747787) qz370 0 2 Ns312p867 Ns312p259 Ns312p868 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 239747787) qz371 0 2 Ns312p869 Ns312p262 Ns312p868 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p871 := nat_lit 4487443086808938877949852125256045765272804028719791018280323624534016 

noncomputable def Ns312p872 := nat_lit 264611731864514022617482111289989292012082902807521538702101774336 

noncomputable def Ns312p873 := nat_lit 13461800036963087605804321411545557317234387920353758011763566670053376 

noncomputable def Ns312p874 := BSN.cos_dyadic_bound_f 150600404 268435456 3 2 268435456 134217728 Ns312p871 Ns312p123 Ns312p872 Ns312p873 Ns312p126 Ns312p872 227286292 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 150600404) qz372 0 2 Ns312p871 Ns312p123 Ns312p872 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 150600404) qz373 0 2 Ns312p873 Ns312p126 Ns312p872 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p875 := nat_lit 11400087769907383934546161582336 

noncomputable def Ns312p876 := BSN.sin_dyadic_bound_f 58106812 268435456 2 1 268435456 134217728 Ns312p875 Ns312p115 Ns312p875 Ns312p875 Ns312p116 Ns312p875 57654088 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 58106812) qz370 0 1 Ns312p875 Ns312p115 Ns312p875 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 58106812) qz371 0 1 Ns312p875 Ns312p116 Ns312p875 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p877 := nat_lit 593520888240615967104409108658185021644648189396547932508106412073216 

noncomputable def Ns312p878 := nat_lit 4629431356109315617367506486242553714044154325280995303452385536 

noncomputable def Ns312p879 := nat_lit 1780553405859135682681992590961582579826516479880993235533712331448576 

noncomputable def Ns312p880 := BSN.cos_dyadic_bound_f 90821978 268435456 3 2 268435456 134217728 Ns312p877 Ns312p123 Ns312p878 Ns312p879 Ns312p126 Ns312p878 253217189 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 90821978) qz372 0 2 Ns312p877 Ns312p123 Ns312p878 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 90821978) qz373 0 2 Ns312p879 Ns312p126 Ns312p878 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p881 := Ns312p833 95379 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 173 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 57654088 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 82 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 253217189 268435456) qz135 rfl rfl (Ns312p866 RS313to324.d9 RS313to324.d11 RS313to324.d13 RS313to324.d17 (Ns312p870 rfl rfl) (Ns312p874 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns312p865 rfl) RS313to324.d19 RS313to324.d21 RS313to324.d23 RS313to324.d25 RS313to324.d17 (Ns312p876 rfl rfl) (Ns312p880 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns312p882 := nat_lit 32619053749425191006980023621597741427671366630587573304619257950613516586966022524993691064508323389764517281 

noncomputable def Ns312p883 := nat_lit 12619113674782716433186189100951280287327043679965528007965680019247846327631287899290275490584694078881 

noncomputable def Ns312p884 := nat_lit 162945944925684372911235100132384140490325783176171424421206574227430558224906579221138311716206614298972110241 

noncomputable def Ns312p885 := BSN.sin_dyadic_bound_f 390618137 268435456 4 3 268435456 134217728 Ns312p882 Ns312p147 Ns312p883 Ns312p884 Ns312p150 Ns312p883 266642912 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 390618137) qz370 0 3 Ns312p882 Ns312p147 Ns312p883 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 390618137) qz371 0 3 Ns312p884 Ns312p150 Ns312p883 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p886 := nat_lit 10413409781183190671951927368582561553516941221756438985245167381975853370238949484401978930312591948988747776 

noncomputable def Ns312p887 := nat_lit 7200501026536197866249725923573020563509440751091932596466535550433915494754891481514440338123834986496 

noncomputable def Ns312p888 := nat_lit 63081622318121973541194462751779362040015286954761969918052203471652686521825862107031643738855442340100116480 

noncomputable def Ns312p889 := BSN.cos_dyadic_bound_f 372775098 268435456 4 3 268435456 134217728 Ns312p886 Ns312p136 Ns312p887 Ns312p888 Ns312p139 Ns312p887 48612615 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 372775098) qz372 0 3 Ns312p886 Ns312p136 Ns312p887 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 372775098) qz373 0 3 Ns312p888 Ns312p139 Ns312p887 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p890 := Ns312p831 128574 BSN.abs_quadSignPos (BSN.cos_quad_nat3 7 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 266642912 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 54 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 48612615 268435456) qz135 rfl rfl (Ns312p881 rfl rfl) (Ns312p865 rfl) RS313to324.d27 RS313to324.d29 RS313to324.d31 RS313to324.d33 RS313to324.d17 (Ns312p885 rfl rfl) (Ns312p889 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p891 := nat_lit 3657817493096039818882597602378709051038938261346011650708041480290560 

noncomputable def Ns312p892 := nat_lit 54268594747525579350807641117845023671273968948114935015835975936 

noncomputable def Ns312p893 := nat_lit 9579910332764798769944997174810999575063656240908876422911987761561856 

noncomputable def Ns312p894 := BSN.sin_dyadic_bound_f 123543122 268435456 3 2 268435456 134217728 Ns312p891 Ns312p259 Ns312p892 Ns312p893 Ns312p262 Ns312p892 119227692 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 123543122) qz370 0 2 Ns312p891 Ns312p259 Ns312p892 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 123543122) qz371 0 2 Ns312p893 Ns312p262 Ns312p892 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p895 := nat_lit 3276214587874580238945757067774186803898892151287929903434179518644480 

noncomputable def Ns312p896 := nat_lit 43536201523919443700720169807058589599304490486278668809166110976 

noncomputable def Ns312p897 := nat_lit 8580491528678576184806229249609849248685366284198076724482874375127296 

noncomputable def Ns312p898 := BSN.sin_dyadic_bound_f 120186674 268435456 3 2 268435456 134217728 Ns312p895 Ns312p259 Ns312p896 Ns312p897 Ns312p262 Ns312p896 116211245 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 120186674) qz370 0 2 Ns312p895 Ns312p259 Ns312p896 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 120186674) qz371 0 2 Ns312p897 Ns312p262 Ns312p896 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p899 := Ns312p829 157578 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 109 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 119227692 268435456) BSN.abs_quadSignNeg qz590 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 116211245 268435456) qz135 rfl rfl (Ns312p890 rfl) (Ns312p865 rfl) RS313to324.d35 RS313to324.d37 RS313to324.d39 RS313to324.d41 RS313to324.d17 (Ns312p894 rfl rfl) (Ns312p898 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p900 := nat_lit 593409486672238097447784150643025092204902550425773805400306158206976 

noncomputable def Ns312p901 := nat_lit 4627693680138629084137543987872788637369817948663161197019856896 

noncomputable def Ns312p902 := nat_lit 1780219204629354015085184176841099531037432911641424089878524434907136 

noncomputable def Ns312p903 := BSN.cos_dyadic_bound_f 90817716 268435456 3 2 268435456 134217728 Ns312p900 Ns312p123 Ns312p901 Ns312p902 Ns312p126 Ns312p901 253218604 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 90817716) qz372 0 2 Ns312p900 Ns312p123 Ns312p901 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 90817716) qz373 0 2 Ns312p902 Ns312p126 Ns312p901 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p904 := Ns312p827 Bool.true 384264908 157578 Bool.true 90817716 14148475504056880 1 Bool.false 253218604 Bool.false Bool.true 304190156 170932 BSN.abs_quadSignPos qz374 (BSN.sfrac_eq_quadSignPos_mul Bool.false 253218604 268435456) qz135 rfl (Ns312p899 rfl) (Ns312p865 rfl) RS313to324.d43 RS313to324.d45 RS313to324.d17 (Ns312p903 rfl rfl) rfl 

noncomputable def Ns312p905 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) 304190156 268435456 170932 268435456 304190156 268435456 170932 268435456 163310846473142272 76047539 33554432 42733 33554432 (Ns312p904 rfl rfl rfl rfl) 

noncomputable def Ns312p906 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz133) (Zeta.RiemannSiegel.correction qz134) 5280965 16777216 1 16777216 50951972214375 70368744177664 2207486540637251 155163080911749120000 269075581945086871875 1180591620717411303424 

noncomputable def Ns312p907 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz133 1 1 0 1 5280965 16777216 1 16777216 5280965 16777216 1 16777216 

noncomputable abbrev qz141 := qz456

noncomputable def Ns312p908 := @Enclosure.Real.IsNear.sqrt_image qz141 3418034193767 33554432000 640039 33554432000 169329689 169329721 16777216 (@Enclosure.Real.IsNear.of_eq qz141 (@HMul.hMul Real Real Real qz5 qz132 qz3) Bool.false 3418034193767 33554432000 640039 33554432000 (BSN.t_div_two_pi_mk qz132 640039 1000 qz135) (@Enclosure.Real.IsNear.mulLit_ff qz132 qz3 640039 1000 0 1 5340353 33554432 1 33554432 3418034193767 33554432000 640039 33554432000 (Enclosure.Real.IsNear.const Bool.false 640039 1000) RS313to324.d48 rfl)) 

noncomputable abbrev qz743 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 640039 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz647 := qz743

noncomputable abbrev qz464 := qz647

noncomputable abbrev qz142 := qz464

noncomputable def Ns312p909 := @Enclosure.Real.IsNear.sqrt_image qz142 169329705 16777216 1 1048576 53299913 53299919 16777216 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 338659410 33554432 32 33554432 169329705 16777216 1 1048576 (Ns312p908 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns312p910 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz142) 13324979 4194304 3 16777216 5280964 5280966 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz142) Bool.false 106599832 33554432 6 33554432 13324979 4194304 3 16777216 (Ns312p909 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns312p911 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz142)) Bool.false 10561930 33554432 2 33554432 5280965 16777216 1 16777216 (Ns312p910 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz143 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz457))

noncomputable abbrev qz648 := (@HMul.hMul Real Real Real qz711 qz742 qz742)

noncomputable abbrev qz465 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz648 qz643) qz594)

noncomputable abbrev qz144 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz465))

noncomputable def Ns312p912 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz134) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz143) qz144) Bool.false 50951972214375 

noncomputable def Ns312p913 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz143) qz144 40202125 33554432 301 

noncomputable def Ns312p914 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz143) Bool.false 40202125 33554432 301 33554432 40202125 33554432 301 

noncomputable def Ns312p915 := @Enclosure.Real.IsNear.recentre' qz143 Bool.false 14002990 16777216 462187216 73987522560000 7001495 8388608 28886701 4624220160000 

noncomputable abbrev qz145 := (@HMul.hMul Real Real Real qz349 qz346 qz457)

noncomputable def Ns312p916 := @Enclosure.Real.IsNear.cos_image qz145 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 19572687) qz368) Bool.false 19572687 33554432 101 16777216 Bool.false 14002990 16777216 1 

noncomputable def Ns312p917 := nat_lit 26986075409880246059800007 

noncomputable def Ns312p918 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz134 884279719003555 140737488355328 1 500000000000000 1557545 16777216 1 1048576 1377305454935392072475 2361183241434822606848 Ns312p917 

noncomputable def Ns312p919 := @Enclosure.Real.IsNear.subLit_ff_p qz142 qz1 169329705 16777216 1 1048576 10 1 0 1 1557545 1557545 16777216 1 

noncomputable def Ns312p920 := @Ns312p919 1048576 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 338659410 33554432 32 33554432 169329705 16777216 1 1048576 (Ns312p908 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns312p921 := @Enclosure.Real.IsNear.recentre' qz145 Bool.false 1377305454935392072475 2361183241434822606848 Ns312p917 Ns312p296 19572687 33554432 101 16777216 (@Ns312p918 Ns312p296 RS313to324.d47 (Ns312p920 rfl rfl) rfl) 

noncomputable def Ns312p922 := nat_lit 312565168249509474579615019751428747566899298745983225062768001 

noncomputable def Ns312p923 := nat_lit 21537912511811576241281352772649938627816181365495871323521 

noncomputable def Ns312p924 := nat_lit 937652428923504800586362496548740942823442263875218683445656961 

noncomputable def Ns312p925 := BSN.cos_dyadic_bound_f 19572687 33554432 3 2 16777216 4410000 Ns312p922 Ns312p463 Ns312p923 Ns312p924 Ns312p466 Ns312p923 14002990 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 19572687) qz395 0 2 Ns312p922 Ns312p463 Ns312p923 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 19572687) (BSN.cosOddQ 33554432) 0 2 Ns312p924 Ns312p466 Ns312p923 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p926 := @Enclosure.Real.IsNear.inv_image qz143 7001495 8388608 28886701 4624220160000 20100912 20101213 16777216 (Ns312p915 (@Ns312p916 4410000 (Ns312p921 rfl) (Enclosure.sfrac_false_div 19572687 33554432) (Ns312p925 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns312p927 := @Enclosure.Real.IsNear.recentre' qz144 Bool.false 10139160 16777216 

noncomputable abbrev qz146 := (@HMul.hMul Real Real Real qz349 qz346 qz465)

noncomputable def Ns312p928 := @Enclosure.Real.IsNear.cos_image qz146 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 15466207)) qz378) Bool.true 15466207 16777216 

noncomputable def Ns312p929 := nat_lit 36518549222636435819569554605 

noncomputable def Ns312p930 := nat_lit 268407850787578647717541225793303 

noncomputable def Ns312p931 := @Enclosure.Real.IsNear.recentre' qz146 Bool.true Ns312p929 Ns312p184 Ns312p930 

noncomputable abbrev qz147 := qz465

noncomputable def Ns312p932 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz147 884279719003555 140737488355328 1 500000000000000 41297508512111 

noncomputable abbrev qz466 := (@HSub.hSub Real Real Real qz583 qz648 qz643)

noncomputable abbrev qz148 := qz466

noncomputable def Ns312p933 := @Enclosure.Real.IsNear.subLit_tf qz148 qz29 23705322467695 281474976710656 9946161 8796093022208 1 16 

noncomputable abbrev qz467 := qz648

noncomputable abbrev qz149 := qz467

noncomputable def Ns312p934 := @Enclosure.Real.IsNear.subLit_ff_n qz149 qz134 2425946427025 281474976710656 1557553 8796093022208 1557545 16777216 1 1048576 

noncomputable def Ns312p935 := @Enclosure.Real.IsNear.mulLit_ff qz134 qz134 1557545 16777216 1 1048576 1557545 16777216 1 1048576 2425946427025 281474976710656 

noncomputable def Ns312p936 := nat_lit 7619224907515094481535636961486116789094666322751333481806081 

noncomputable def Ns312p937 := nat_lit 3273938732455135437417676656821193752083608011170287417601 

noncomputable def Ns312p938 := nat_lit 22851126845080373173732075531144707979779831752231659870583041 

noncomputable def Ns312p939 := BSN.cos_dyadic_bound_f 15466207 16777216 3 2 16777216 4410000 Ns312p936 Ns312p583 Ns312p937 Ns312p938 Ns312p586 Ns312p937 10139160 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 15466207) (BSN.cosEvenQ 16777216) 0 2 Ns312p936 Ns312p583 Ns312p937 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 15466207) (BSN.cosOddQ 16777216) 0 2 Ns312p938 Ns312p586 Ns312p937 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p940 := @Ns312p927 1087544432 147975045120000 1267395 2097152 67971527 9248440320000 (@Ns312p928 239 33554432 Bool.false 10139160 16777216 1 4410000 (@Ns312p931 Ns312p187 15466207 16777216 239 33554432 (@Ns312p932 281474976710656 9946161 8796093022208 Ns312p929 Ns312p184 Ns312p930 Ns312p187 RS313to324.d47 (@Ns312p933 0 1 660760136193776 41297508512111 281474976710656 9946161 8796093022208 (@Ns312p934 397709315390172037120 23705322467695 281474976710656 9946161 8796093022208 (@Ns312p935 1557553 8796093022208 (Ns312p920 rfl rfl) (Ns312p920 rfl rfl) rfl) (Ns312p920 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 15466207 16777216) (BSN.cos_neg_of_bound 15466207 16777216 Bool.false 10139160 16777216 1 4410000 (Ns312p939 rfl rfl)) rfl rfl) 

noncomputable def Ns312p941 := @Ns312p906 653889470294202096637 Ns312p824 (Ns312p907 qz31 (@Enclosure.Real.IsNear.of_eq qz133 (@Inv.inv Real Real.instInv (Real.sqrt qz142)) Bool.false 5280965 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz141 (BSN.t_div_two_pi_nonneg qz132 640039 1000 qz135)) Ns312p911) rfl) (@Ns312p912 70368744177664 2207486540637251 155163080911749120000 (BSN.correction_mk qz134 (BSN.cos_two_pi_p_ne_zero_mk qz132 640039 1000 10 qz135 rfl rfl (@BSN.floor_sqrt_eq_dec qz132 640039 1000 10 qz135 rfl rfl rfl))) (@Ns312p913 33554432 1267395 2097152 67971527 9248440320000 50951972214375 70368744177664 2207486540637251 155163080911749120000 (@Ns312p914 33554432 (Ns312p926 rfl rfl rfl rfl rfl) rfl) (Ns312p940 rfl) rfl)) 

noncomputable def Ns312p942 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz132) (hardyZApproximantRS₀ qz132) Bool.true 2944760490561049856323 1180591620717411303424 184836776598121289456637 Ns312p824 (@Eq.refl Real (hardyZApproximantRS₀ qz132)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz132) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz133) (Zeta.RiemannSiegel.correction qz134))) Bool.true 2944760490561049856323 1180591620717411303424 184836776598121289456637 Ns312p824 (BSN.hardyZApproximantRS₀_eq qz132 10 (@BSN.floor_sqrt_eq_dec qz132 640039 1000 10 qz135 rfl rfl rfl)) (@Ns312p826 2944760490561049856323 1180591620717411303424 184836776598121289456637 Ns312p824 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz132) qz132 10)) Bool.true 76047539 33554432 42733 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz132) qz132 10) (Ns312p905 (Ns312p904 rfl rfl rfl rfl) rfl rfl)) (Ns312p941 rfl) rfl rfl)) 

theorem RS313to324.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz132) Bool.true 2944760490561049856323 1180591620717411303424 184836776598121289456637 Ns312p824 := Ns312p942 

noncomputable def Ns312p943 := nat_lit 433867420613648654008320000 

noncomputable def Ns312p944 := nat_lit 142945895172616123248478781440 

noncomputable abbrev qz744 := (Enclosure.sfrac Bool.false 641398 1000)

noncomputable abbrev qz649 := qz744

noncomputable abbrev qz468 := qz649

noncomputable abbrev qz150 := qz468

noncomputable abbrev qz745 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 641398 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz650 := qz745

noncomputable abbrev qz469 := qz650

noncomputable abbrev qz151 := (@HPow.hPow Real Real Real qz350 qz469 qz352)

noncomputable abbrev qz746 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 641398 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz651 := qz746

noncomputable abbrev qz470 := qz651

noncomputable abbrev qz152 := qz470

noncomputable def Ns312p945 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz150) qz150 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz151) (Zeta.RiemannSiegel.correction qz152)) 33987185 16777216 171295 134217728 1046302802471747369395 4722366482869645213696 2117644759826789619899 Ns312p943 Ns312p944 

noncomputable def Ns312p946 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz150) qz150 Real.cos BSN.quadSignPos 9 10 641398 1000 200 268435456 134217728 4503599627370496 Bool.false 312026459343 2519 618095470 62 84886744 8 

noncomputable def Ns312p947 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz150) qz150 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 641398 1000 109 157 268435456 134217728 4503599627370496 Bool.false 312026459343 2519 

noncomputable def Ns312p948 := Ns312p947 558195838 62 94906264 8 589812974 62 89478488 8 Bool.false 230742304 128848 Bool.true 38575077 Bool.true 78186316 14148475504056880 1 Bool.false 38442447 Bool.true Bool.false 77085489 Bool.true Bool.false 191455682 

noncomputable def Ns312p949 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz150) qz150 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 641398 1000 8 54 268435456 134217728 4503599627370496 Bool.false 312026459343 2519 

noncomputable def Ns312p950 := Ns312p949 480971758 62 109588312 8 522351262 62 101459064 8 Bool.false 203599196 95583 Bool.false 158876279 Bool.true 239094274 14148475504056880 1 Bool.false 222775729 Bool.false Bool.false 168811369 Bool.true Bool.false 230742304 

noncomputable def Ns312p951 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz150) qz150 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 641398 1000 173 82 268435456 134217728 4503599627370496 Bool.false 312026459343 2519 

noncomputable def Ns312p952 := Ns312p951 372130544 61 134217720 8 432030192 61 120047984 16 Bool.false 370053206 56109 Bool.false 395937592 Bool.false 347249136 14148475504056880 1 Bool.false 267204239 Bool.true Bool.false 73459077 Bool.true Bool.false 203599196 

noncomputable def Ns312p953 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz150) qz150 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 641398 1000 456 291 268435456 134217728 4503599627370496 Bool.false 312026459343 2519 

noncomputable def Ns312p954 := Ns312p953 186065264 61 189812528 16 294906480 61 154981288 8 Bool.false 268435448 2589 Bool.false 408783854 Bool.false 171721258 14148475504056880 1 Bool.false 12868640 Bool.false Bool.false 160246314 Bool.false Bool.false 370053206 

noncomputable def Ns312p955 := nat_lit 6406934255267294653686566254387081239409471275789302003 

noncomputable def Ns312p956 := nat_lit 5511866916644433211294939170453239811071916638208000 

noncomputable def Ns312p957 := nat_lit 52105061505427694664926133744640000 

noncomputable def Ns312p958 := nat_lit 200520550302623931613013671101843640320 

noncomputable abbrev qz652 := (@Eq.refl Real qz744)

noncomputable abbrev qz471 := qz652

noncomputable abbrev qz153 := qz471

noncomputable def Ns312p959 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz150 641398 1000 1645566577616 16000000 1282796 4000 2000 Ns312p957 Ns312p958 qz153 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns312p960 := nat_lit 131214013547874194507500876889847423783105971728164905021440 

noncomputable abbrev qz653 := (@HSub.hSub Real Real Real qz715 qz716 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz717 (@Nat.cast Real Real.instNatCast 1282796))))

noncomputable abbrev qz472 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 641398 4000) (Real.log (Enclosure.sfrac Bool.false 1645566577616 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz653))

noncomputable abbrev qz654 := (Enclosure.sfrac Bool.false 641398 2000)

noncomputable abbrev qz154 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz472 qz654) (@HMul.hMul Real Real Real qz349 qz654 (Real.log Real.pi)))

noncomputable def Ns312p961 := @Enclosure.Real.IsNear.addLit_ft_p qz154 (Enclosure.sfrac Bool.true Ns312p957 Ns312p958) 654367059547707253567 562949953421312000 2824065820129575277 301056000000000000000000 Ns312p957 Ns312p958 0 1 Ns312p960 

noncomputable def Ns312p962 := nat_lit 21956915002633493795720658944000 

noncomputable abbrev qz155 := (@HSub.hSub Real Real Real qz355 qz472 qz654)

noncomputable def Ns312p963 := @Enclosure.Real.IsNear.subLit_ff_p qz155 (@HMul.hMul Real Real Real qz5 qz654 (Real.log Real.pi)) 861033715952728515391 562949953421312000 676456627160399 147000000000000000000 12318292641939 33554432000 320699 67108864000 Ns312p962 654367059547707253567 562949953421312000 

noncomputable def Ns312p964 := nat_lit 1722067431905457030782000 

noncomputable abbrev qz156 := qz472

noncomputable def Ns312p965 := @Enclosure.Real.IsNear.subLit_ff_p qz156 qz654 1041571203064989852479 562949953421312000 676456627160399 147000000000000000000 641398 2000 0 1 Ns312p964 861033715952728515391 562949953421312000 676456627160399 147000000000000000000 

noncomputable def Ns312p966 := nat_lit 2345409841001663760416987952858529792 

noncomputable def Ns312p967 := nat_lit 55808883352343575122673664 

noncomputable def Ns312p968 := nat_lit 209425831314536315114258330699546367885877566678272911388116047282883527136814679367630837596580836422322815064151706742313451520 

noncomputable def Ns312p969 := nat_lit 3532365240340912565927890556885757560118398766609051030653477562442476356520489921844727986830389570543540967764176922795311104 

noncomputable def Ns312p970 := nat_lit 5433836604636060622461668228152114444167809021761790543538381108972993328090462895182647815954186840049340775844355768320 

noncomputable def Ns312p971 := BSN.log_dyadic_bound 596990577616 2694142577616 6 5 Ns312p968 134217728 35280000 Ns312p969 Ns312p970 60485446 3291133155232 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 596990577616) (BSN.artanhQ 2694142577616) 0 5 Ns312p969 Ns312p968 Ns312p970 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz473 := (Real.log (Enclosure.sfrac Bool.false 1645566577616 16000000))

noncomputable def Ns312p972 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 641398 4000) qz473 641398 4000 0 1 3248504558132471 281474976710656 781250441 27562500000000000 1041792163288525317229 562949953421312000 250546235178259 55125000000000000000 (Enclosure.Real.IsNear.const Bool.false 641398 4000) (BSN.isNear_log_sfrac 1645566577616 16000000 3248504558132471 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1645566577616) qz358)) Bool.false Ns312p967 Ns312p99 1000000564480000 35280000000000000000000 3248504558132471 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1645566577616 16000000 16 3291133155232 2097152000000 60485446 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns312p971 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns312p973 := BSN.arctan_dyadic_bound_f 1000 1282796 1 0 16777216 4410000 0 1 1 0 1 1 13078 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1282796) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1282796) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz474 := (@Nat.cast Real Real.instNatCast 1282796)

noncomputable def Ns312p974 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz474)) 884279719003555 562949953421312 1 2000000000000000 13078 16777216 1 4410000 14828389590651103084544 883840894141859 562949953421312 200000000441 882000000000000000 qz15 (Ns312p973 rfl) rfl rfl 

noncomputable abbrev qz475 := (@HMul.hMul Real Real Real qz579 qz584 qz653)

noncomputable abbrev qz157 := qz475

noncomputable abbrev qz476 := qz653

noncomputable abbrev qz158 := qz476

noncomputable def Ns312p975 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 641398 4000) qz473) qz157 1041792163288525317229 562949953421312000 250546235178259 55125000000000000000 883840894141859 2251799813685248 200000000441 3528000000000000000 Ns312p966 1041571203064989852479 562949953421312000 676456627160399 147000000000000000000 (Ns312p972 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz158 1 4 0 1 883840894141859 562949953421312 200000000441 882000000000000000 883840894141859 2251799813685248 200000000441 3528000000000000000 qz366 Ns312p974 rfl) 

noncomputable def Ns312p976 := @Ns312p961 Ns312p955 Ns312p956 2824065820129575277 301056000000000000000000 (@Ns312p963 2824065820129575277 301056000000000000000000 (Ns312p965 (Ns312p975 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 641398 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz654 (Real.log Real.pi) 641398 2000 0 1 38410761 33554432 1 67108864 12318292641939 33554432000 320699 67108864000 (Enclosure.Real.IsNear.const Bool.false 641398 2000) RS313to324.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns312p957 Ns312p958) 

noncomputable def Ns312p977 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz150) Bool.false Ns312p955 Ns312p956 2824065820129575277 301056000000000000000000 39003307417 33554432 79 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz150) (@HAdd.hAdd Real Real Real qz367 qz154 (Enclosure.sfrac Bool.true Ns312p957 Ns312p958)) Bool.false Ns312p955 Ns312p956 2824065820129575277 301056000000000000000000 Ns312p959 (Ns312p976 rfl rfl)) 

noncomputable def Ns312p978 := nat_lit 7595227946871087414902784 

noncomputable def Ns312p979 := nat_lit 3509581496189371783258185374770616917467561261706306316205704671564619982188910432470747816174980277221263599966304123618964615623202973761 

noncomputable def Ns312p980 := nat_lit 2499954716006647272038636306775799696894583491674140741175982057159585043421916093290012542535980386711828089398965668690431904720961 

noncomputable def Ns312p981 := nat_lit 17526109801249635879727627278759563599629249741001290563377634237160516489850313295831300419039025371123914002576611984124418859806307526721 

noncomputable def Ns312p982 := BSN.sin_dyadic_bound_f 107934680881 68719476736 4 3 33554432 8828614 Ns312p979 Ns312p239 Ns312p980 Ns312p981 Ns312p242 Ns312p980 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107934680881) qz602 0 3 Ns312p979 Ns312p239 Ns312p980 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107934680881) qz603 0 3 Ns312p981 Ns312p242 Ns312p980 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p983 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz150) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 39003307417) qz368) Bool.false 39003307417 33554432 79 8388608 Bool.false 33554431 33554432 1 4410000 (Ns312p977 rfl) (Enclosure.sfrac_false_div 39003307417 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 39003307417) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns312p978) qz369) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 184 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q3 39003307417 33554432 226375608064910080 72057594037927936 184 Ns312p978 Ns312p99 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554431 33554432 Ns312p978 Ns312p99 107934680881 68719476736 8828614 8820000 (Ns312p982 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns312p984 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz150) Bool.false Ns312p955 Ns312p956 2824065820129575277 301056000000000000000000 312026459343 268435456 2519 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz150) (@HAdd.hAdd Real Real Real qz367 qz154 (Enclosure.sfrac Bool.true Ns312p957 Ns312p958)) Bool.false Ns312p955 Ns312p956 2824065820129575277 301056000000000000000000 Ns312p959 (Ns312p976 rfl rfl)) 

noncomputable def Ns312p985 := Ns312p954 56109 BSN.abs_quadSignPos (BSN.cos_quad_nat0 456 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 12868640 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 291 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 160246314 268435456) qz153 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 1) Bool.false 33554431 33554432 22298663 2312110080000 268435448 268435456 2589 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz150)) Bool.false 33554431 33554432 22298663 2312110080000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz150) qz150) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz150)) Bool.false 33554431 33554432 356778608 36993761280000 33554431 33554432 22298663 2312110080000 (Ns312p983 rfl rfl) rfl)) rfl) (Ns312p984 rfl) RS313to324.d7 

noncomputable def Ns312p986 := nat_lit 15073299745761299560294632739418464337758125242493294742712184159515110205418329004744438990478091335129501696 

noncomputable def Ns312p987 := nat_lit 21773327563950573431530844215851411222420898223447479779468675998037593711322187297686131797742811222016 

noncomputable def Ns312p988 := nat_lit 91250045651196049250998919169724477297919161345798825279341373737481319979612404060124170528297581726212689920 

noncomputable def Ns312p989 := BSN.cos_dyadic_bound_f 408783854 268435456 4 3 268435456 134217728 Ns312p986 Ns312p136 Ns312p987 Ns312p988 Ns312p139 Ns312p987 12868640 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 408783854) qz372 0 3 Ns312p986 Ns312p136 Ns312p987 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 408783854) qz373 0 3 Ns312p988 Ns312p139 Ns312p987 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p990 := nat_lit 13654053412385784182967323838891448001298006285152401650547426688262400 

noncomputable def Ns312p991 := nat_lit 756123073647856828517372579006907742832205958507143193542219817216 

noncomputable def Ns312p992 := nat_lit 35759391880795909663382534308159209771815907175275849900548953922887936 

noncomputable def Ns312p993 := BSN.sin_dyadic_bound_f 171721258 268435456 3 2 268435456 134217728 Ns312p990 Ns312p259 Ns312p991 Ns312p992 Ns312p262 Ns312p991 160246314 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 171721258) qz370 0 2 Ns312p990 Ns312p259 Ns312p991 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 171721258) qz371 0 2 Ns312p992 Ns312p262 Ns312p991 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p994 := nat_lit 34435346386336290357108498008918719662125634794066935011112856895286688219337731833070707747152819442035982336 

noncomputable def Ns312p995 := nat_lit 14842971368474918753649704245161520359554796692232200452770528124769241072437082642071746265560001806336 

noncomputable def Ns312p996 := nat_lit 172010340130842413740127875997076479094729258614354784573313313181049005729423745920190164676958189602415312896 

noncomputable def Ns312p997 := BSN.sin_dyadic_bound_f 395937592 268435456 4 3 268435456 134217728 Ns312p994 Ns312p147 Ns312p995 Ns312p996 Ns312p150 Ns312p995 267204239 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 395937592) qz370 0 3 Ns312p994 Ns312p147 Ns312p995 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 395937592) qz371 0 3 Ns312p996 Ns312p150 Ns312p995 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p998 := nat_lit 7836694499571891654998214110051750357641964668680056352622644585201263982215627517833448751576264455934181376 

noncomputable def Ns312p999 := nat_lit 3073930796392177435225261710522036612215563363068424870368497853094452532379197476381396317697365508096 

noncomputable def Ns312p1000 := nat_lit 47489854796753564556890194519048702124225518409992851890053793821810159520990191505459447645448370071986503680 

noncomputable def Ns312p1001 := BSN.cos_dyadic_bound_f 347249136 268435456 4 3 268435456 134217728 Ns312p998 Ns312p136 Ns312p999 Ns312p1000 Ns312p139 Ns312p999 73459077 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 347249136) qz372 0 3 Ns312p998 Ns312p136 Ns312p999 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 347249136) qz373 0 3 Ns312p1000 Ns312p139 Ns312p999 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1002 := Ns312p952 95583 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 173 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 267204239 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 82 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 73459077 268435456) qz153 rfl rfl (Ns312p985 RS313to324.d9 RS313to324.d11 RS313to324.d13 RS313to324.d17 (Ns312p989 rfl rfl) (Ns312p993 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns312p984 rfl) RS313to324.d19 RS313to324.d21 RS313to324.d23 RS313to324.d25 RS313to324.d17 (Ns312p997 rfl rfl) (Ns312p1001 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns312p1003 := nat_lit 5558233089842557647307562308549756649537801477319072528211061002232641 

noncomputable def Ns312p1004 := nat_lit 405949936846764595706206433188927706332551770159312461862104752961 

noncomputable def Ns312p1005 := nat_lit 16673887369653979412731274512782892093200739328416898959709458797192001 

noncomputable def Ns312p1006 := BSN.cos_dyadic_bound_f 158876279 268435456 3 2 268435456 134217728 Ns312p1003 Ns312p123 Ns312p1004 Ns312p1005 Ns312p126 Ns312p1004 222775729 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 158876279) qz372 0 2 Ns312p1003 Ns312p123 Ns312p1004 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 158876279) qz373 0 2 Ns312p1005 Ns312p126 Ns312p1004 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1007 := nat_lit 28517284553205721233230712575823205689742856199366562622919849816883456 

noncomputable def Ns312p1008 := nat_lit 10679561070465677581164439063800671699507418329024942303527549010176 

noncomputable def Ns312p1009 := nat_lit 85530494537476232344529808849342015725829553761441637984152494352630016 

noncomputable def Ns312p1010 := BSN.cos_dyadic_bound_f 239094274 268435456 3 2 268435456 134217728 Ns312p1007 Ns312p123 Ns312p1008 Ns312p1009 Ns312p126 Ns312p1008 168811369 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 239094274) qz372 0 2 Ns312p1007 Ns312p123 Ns312p1008 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 239094274) qz373 0 2 Ns312p1009 Ns312p126 Ns312p1008 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1011 := Ns312p950 128848 BSN.abs_quadSignPos (BSN.cos_quad_nat0 8 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 222775729 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 54 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 168811369 268435456) qz153 rfl rfl (Ns312p1002 rfl rfl) (Ns312p984 rfl) RS313to324.d27 RS313to324.d29 RS313to324.d31 RS313to324.d33 RS313to324.d17 (Ns312p1006 rfl rfl) (Ns312p1010 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p1012 := nat_lit 2214252820431484584396827053041 

noncomputable def Ns312p1013 := BSN.sin_dyadic_bound_f 38575077 268435456 2 1 268435456 134217728 Ns312p1012 Ns312p115 Ns312p1012 Ns312p1012 Ns312p116 Ns312p1012 38442447 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 38575077) qz370 0 1 Ns312p1012 Ns312p115 Ns312p1012 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 38575077) qz371 0 1 Ns312p1012 Ns312p116 Ns312p1012 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1014 := nat_lit 37369991728005521920358324244736 

noncomputable def Ns312p1015 := BSN.sin_dyadic_bound_f 78186316 268435456 2 1 268435456 134217728 Ns312p1014 Ns312p115 Ns312p1014 Ns312p1014 Ns312p116 Ns312p1014 77085489 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 78186316) qz370 0 1 Ns312p1014 Ns312p115 Ns312p1014 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 78186316) qz371 0 1 Ns312p1014 Ns312p116 Ns312p1014 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1016 := Ns312p948 157913 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 109 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 38442447 268435456) BSN.abs_quadSignNeg qz590 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 77085489 268435456) qz153 rfl rfl (Ns312p1011 rfl) (Ns312p984 rfl) RS313to324.d35 RS313to324.d37 RS313to324.d39 RS313to324.d41 RS313to324.d17 (Ns312p1013 rfl rfl) (Ns312p1015 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p1017 := nat_lit 505590063289316402949017500608957646981661478234404187465311024800000 

noncomputable def Ns312p1018 := nat_lit 3359337951147073750442593328429971301025610566398290368100000000 

noncomputable def Ns312p1019 := nat_lit 1516763471192046914699551616640216081002382383482079765815196874400000 

noncomputable def Ns312p1020 := BSN.cos_dyadic_bound_f 87253270 268435456 3 2 268435456 134217728 Ns312p1017 Ns312p123 Ns312p1018 Ns312p1019 Ns312p126 Ns312p1018 254379303 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 87253270) qz372 0 2 Ns312p1017 Ns312p123 Ns312p1018 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 87253270) qz373 0 2 Ns312p1019 Ns312p126 Ns312p1018 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1021 := Ns312p946 Bool.false 191455682 157913 Bool.true 87253270 14148475504056880 1 Bool.false 254379303 Bool.false Bool.false 271897480 171295 BSN.abs_quadSignPos qz374 (BSN.sfrac_eq_quadSignPos_mul Bool.false 254379303 268435456) qz153 rfl (Ns312p1016 rfl) (Ns312p984 rfl) RS313to324.d43 RS313to324.d45 RS313to324.d17 (Ns312p1020 rfl rfl) rfl 

noncomputable def Ns312p1022 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 10) 271897480 268435456 171295 268435456 271897480 268435456 171295 268435456 145973848058101760 33987185 16777216 171295 134217728 (Ns312p1021 rfl rfl rfl rfl) 

noncomputable def Ns312p1023 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz151) (Zeta.RiemannSiegel.correction qz152) 5278165 16777216 1 16777216 198232302793063 281474976710656 397757889200089 25860513485291520000 1046302802471747369395 4722366482869645213696 

noncomputable def Ns312p1024 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz151 1 1 0 1 5278165 16777216 1 16777216 5278165 16777216 1 16777216 

noncomputable abbrev qz159 := qz469

noncomputable def Ns312p1025 := @Enclosure.Real.IsNear.sqrt_image qz159 1712645866747 16777216000 320699 16777216000 169509363 169509396 16777216 (@Enclosure.Real.IsNear.of_eq qz159 (@HMul.hMul Real Real Real qz5 qz150 qz3) Bool.false 1712645866747 16777216000 320699 16777216000 (BSN.t_div_two_pi_mk qz150 641398 1000 qz153) (@Enclosure.Real.IsNear.mulLit_ff qz150 qz3 641398 1000 0 1 5340353 33554432 1 33554432 1712645866747 16777216000 320699 16777216000 (Enclosure.Real.IsNear.const Bool.false 641398 1000) RS313to324.d48 rfl)) 

noncomputable abbrev qz747 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 641398 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz655 := qz747

noncomputable abbrev qz477 := qz655

noncomputable abbrev qz160 := qz477

noncomputable def Ns312p1026 := @Enclosure.Real.IsNear.sqrt_image qz160 339018759 33554432 33 33554432 53328183 53328190 16777216 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 339018759 33554432 33 33554432 339018759 33554432 33 33554432 (Ns312p1025 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns312p1027 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz160) 106656373 33554432 7 33554432 5278164 5278166 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz160) Bool.false 106656373 33554432 7 33554432 106656373 33554432 7 33554432 (Ns312p1026 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns312p1028 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz160)) Bool.false 10556330 33554432 2 33554432 5278165 16777216 1 16777216 (Ns312p1027 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz161 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz470))

noncomputable abbrev qz656 := (@HMul.hMul Real Real Real qz711 qz746 qz746)

noncomputable abbrev qz478 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz656 qz651) qz594)

noncomputable abbrev qz162 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz478))

noncomputable def Ns312p1029 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz152) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz161) qz162) Bool.false 198232302793063 

noncomputable def Ns312p1030 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz161) qz162 42168643 33554432 341 

noncomputable def Ns312p1031 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz161) Bool.false 42168643 33554432 341 33554432 42168643 33554432 341 

noncomputable def Ns312p1032 := @Enclosure.Real.IsNear.recentre' qz161 Bool.false 13349966 16777216 59427152 9248440320000 6674983 8388608 3714197 578027520000 

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz349 qz346 qz470)

noncomputable def Ns312p1033 := @Enclosure.Real.IsNear.cos_image qz163 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1364409) (@Nat.cast Real Real.instNatCast 2097152)) Bool.false 1364409 2097152 13 2097152 Bool.false 13349966 16777216 1 

noncomputable def Ns312p1034 := nat_lit 890540488528298703774469799 

noncomputable def Ns312p1035 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz152 884279719003555 140737488355328 1 500000000000000 3474439 33554432 33 33554432 3072375942614992630645 4722366482869645213696 Ns312p1034 

noncomputable def Ns312p1036 := @Enclosure.Real.IsNear.subLit_ff_p qz160 qz1 339018759 33554432 33 33554432 10 1 0 1 3474439 3474439 33554432 33 

noncomputable def Ns312p1037 := @Ns312p1036 33554432 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 339018759 33554432 33 33554432 339018759 33554432 33 33554432 (Ns312p1025 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns312p1038 := @Enclosure.Real.IsNear.recentre' qz163 Bool.false 3072375942614992630645 4722366482869645213696 Ns312p1034 Ns312p796 1364409 2097152 13 2097152 (@Ns312p1035 Ns312p796 RS313to324.d47 (Ns312p1037 rfl rfl) rfl) 

noncomputable def Ns312p1039 := nat_lit 112629857119490636821191024924368427596528562405291201 

noncomputable def Ns312p1040 := nat_lit 15085502980398593449464978548510856026246963233994833920 

noncomputable def Ns312p1041 := nat_lit 12010375999129721755577402584311954515736403555521 

noncomputable def Ns312p1042 := nat_lit 337865550606473651020061919967936658880554214408762561 

noncomputable def Ns312p1043 := nat_lit 678847634117936705225924034682988521181113345529767526400 

noncomputable def Ns312p1044 := BSN.cos_dyadic_bound_f 1364409 2097152 3 2 16777216 4410000 Ns312p1039 Ns312p1040 Ns312p1041 Ns312p1042 Ns312p1043 Ns312p1041 13349966 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1364409) (BSN.cosEvenQ 2097152) 0 2 Ns312p1039 Ns312p1040 Ns312p1041 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1364409) (BSN.cosOddQ 2097152) 0 2 Ns312p1042 Ns312p1043 Ns312p1041 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1045 := @Enclosure.Real.IsNear.inv_image qz161 6674983 8388608 3714197 578027520000 21084151 21084492 16777216 (Ns312p1032 (@Ns312p1033 4410000 (Ns312p1038 rfl) (Enclosure.sfrac_false_div 1364409 2097152) (Ns312p1044 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns312p1046 := @Enclosure.Real.IsNear.recentre' qz162 Bool.false 9401882 16777216 

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz349 qz346 qz478)

noncomputable def Ns312p1047 := @Enclosure.Real.IsNear.cos_image qz164 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32746865)) qz368) Bool.true 32746865 33554432 

noncomputable def Ns312p1048 := nat_lit 154642700175285148906820781005 

noncomputable def Ns312p1049 := nat_lit 7213973372508524702138381928381269 

noncomputable def Ns312p1050 := @Enclosure.Real.IsNear.recentre' qz164 Bool.true Ns312p1048 Ns312p809 Ns312p1049 

noncomputable def Ns312p1051 := nat_lit 967140655691703339764940800000000000000 

noncomputable abbrev qz165 := qz478

noncomputable def Ns312p1052 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz165 884279719003555 140737488355328 1 500000000000000 174879844976591 

noncomputable abbrev qz479 := (@HSub.hSub Real Real Real qz583 qz656 qz651)

noncomputable abbrev qz166 := qz479

noncomputable def Ns312p1053 := @Enclosure.Real.IsNear.subLit_tf qz166 qz29 104511100798927 1125899906842624 1336610319 1125899906842624 1 16 

noncomputable abbrev qz480 := qz656

noncomputable abbrev qz167 := qz480

noncomputable def Ns312p1054 := @Enclosure.Real.IsNear.subLit_ff_n qz167 qz152 12071726364721 1125899906842624 229314063 1125899906842624 3474439 33554432 33 33554432 

noncomputable def Ns312p1055 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz152 3474439 33554432 33 33554432 3474439 33554432 33 33554432 12071726364721 1125899906842624 

noncomputable def Ns312p1056 := nat_lit 2450316636688694525469303991042590358813709097239234490879690625 

noncomputable def Ns312p1057 := nat_lit 1322384759447073074927099501682009132486840623737824562890625 

noncomputable def Ns312p1058 := nat_lit 7348305140547189430258057774124407058176153610470227823513290625 

noncomputable def Ns312p1059 := BSN.cos_dyadic_bound_f 32746865 33554432 3 2 16777216 4410000 Ns312p1056 Ns312p463 Ns312p1057 Ns312p1058 Ns312p466 Ns312p1057 9401882 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 32746865) qz395 0 2 Ns312p1056 Ns312p463 Ns312p1057 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 32746865) (BSN.cosOddQ 33554432) 0 2 Ns312p1058 Ns312p466 Ns312p1057 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1060 := @Ns312p1046 1140464432 147975045120000 4700941 8388608 71279027 9248440320000 (@Ns312p1047 251 33554432 Bool.false 9401882 16777216 1 4410000 (@Ns312p1050 Ns312p1051 32746865 33554432 251 33554432 (@Ns312p1052 1125899906842624 1336610319 1125899906842624 Ns312p1048 Ns312p809 Ns312p1049 Ns312p1051 RS313to324.d47 (@Ns312p1053 0 1 2798077519625456 174879844976591 1125899906842624 1336610319 1125899906842624 (@Ns312p1054 3506810625002741694464 104511100798927 1125899906842624 1336610319 1125899906842624 (@Ns312p1055 229314063 1125899906842624 (Ns312p1037 rfl rfl) (Ns312p1037 rfl rfl) rfl) (Ns312p1037 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 32746865 33554432) (BSN.cos_neg_of_bound 32746865 33554432 Bool.false 9401882 16777216 1 4410000 (Ns312p1059 rfl rfl)) rfl rfl) 

noncomputable def Ns312p1061 := @Ns312p1023 2117644759826789619899 Ns312p943 (Ns312p1024 qz31 (@Enclosure.Real.IsNear.of_eq qz151 (@Inv.inv Real Real.instInv (Real.sqrt qz160)) Bool.false 5278165 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz159 (BSN.t_div_two_pi_nonneg qz150 641398 1000 qz153)) Ns312p1028) rfl) (@Ns312p1029 281474976710656 397757889200089 25860513485291520000 (BSN.correction_mk qz152 (BSN.cos_two_pi_p_ne_zero_mk qz150 641398 1000 10 qz153 rfl rfl (@BSN.floor_sqrt_eq_dec qz150 641398 1000 10 qz153 rfl rfl rfl))) (@Ns312p1030 33554432 4700941 8388608 71279027 9248440320000 198232302793063 281474976710656 397757889200089 25860513485291520000 (@Ns312p1031 33554432 (Ns312p1045 rfl rfl rfl rfl rfl) rfl) (Ns312p1060 rfl) rfl)) 

noncomputable def Ns312p1062 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz150) (hardyZApproximantRS₀ qz150) Bool.false 8520239303864009573965 4722366482869645213696 555839726942703154419899 Ns312p943 (@Eq.refl Real (hardyZApproximantRS₀ qz150)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz150) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz150) qz150 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz151) (Zeta.RiemannSiegel.correction qz152))) Bool.false 8520239303864009573965 4722366482869645213696 555839726942703154419899 Ns312p943 (BSN.hardyZApproximantRS₀_eq qz150 10 (@BSN.floor_sqrt_eq_dec qz150 641398 1000 10 qz153 rfl rfl rfl)) (@Ns312p945 8520239303864009573965 4722366482869645213696 555839726942703154419899 Ns312p943 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz150) qz150 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 10)) Bool.false 33987185 16777216 171295 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz150) qz150 10) (Ns312p1022 (Ns312p1021 rfl rfl rfl rfl) rfl rfl)) (Ns312p1061 rfl) rfl rfl)) 

theorem RS313to324.d58 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz150) Bool.false 8520239303864009573965 4722366482869645213696 555839726942703154419899 Ns312p943 := Ns312p1062 

noncomputable def Ns312p1063 := nat_lit 3342722122586575088274211 

noncomputable def Ns312p1064 := nat_lit 699535707751714510988485066752 

noncomputable abbrev qz748 := (Enclosure.sfrac Bool.false 642756 1000)

noncomputable abbrev qz657 := qz748

noncomputable abbrev qz481 := qz657

noncomputable abbrev qz168 := qz481

noncomputable abbrev qz749 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 642756 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz658 := qz749

noncomputable abbrev qz482 := qz658

noncomputable abbrev qz169 := (@HPow.hPow Real Real Real qz350 qz482 qz352)

noncomputable abbrev qz750 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 642756 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz659 := qz750

noncomputable abbrev qz483 := qz659

noncomputable abbrev qz170 := qz483

noncomputable def Ns312p1065 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz169) (Zeta.RiemannSiegel.correction qz170)) 66837081 33554432 42913 33554432 2034822866237978095125 9444732965739290427392 13465477003630094994211 Ns312p75 Ns312p1064 

noncomputable def Ns312p1066 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.cos BSN.quadSignPos 9 10 642756 1000 200 268435456 134217728 4503599627370496 Bool.false 312869781098 2524 618095470 62 84886744 8 

noncomputable def Ns312p1067 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 642756 1000 108 157 268435456 134217728 4503599627370496 Bool.false 312869781098 2524 

noncomputable def Ns312p1068 := Ns312p1067 558195838 62 94906264 8 589812974 62 89478488 8 Bool.true 352705631 129115 Bool.true 374940698 Bool.true 35830580 14148475504056880 1 Bool.false 46481264 Bool.false Bool.false 35724277 Bool.true Bool.true 348180116 

noncomputable def Ns312p1069 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 642756 1000 8 54 268435456 134217728 4503599627370496 Bool.false 312869781098 2524 

noncomputable def Ns312p1070 := Ns312p1069 480971758 62 109588312 8 522351262 62 101459064 8 Bool.true 288214262 95779 Bool.false 349038386 Bool.true 105125533 14148475504056880 1 Bool.false 71736508 Bool.false Bool.false 248112408 Bool.true Bool.true 352705631 

noncomputable def Ns312p1071 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 642756 1000 174 83 268435456 134217728 4503599627370496 Bool.false 312869781098 2524 

noncomputable def Ns312p1072 := Ns312p1071 372130544 61 134217720 8 432030192 61 120047984 16 Bool.true 310386058 56221 Bool.false 312248640 Bool.false 182216462 14148475504056880 1 Bool.false 106404665 Bool.true Bool.false 168541672 Bool.false Bool.true 288214262 

noncomputable def Ns312p1073 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 642756 1000 458 292 268435456 134217728 4503599627370496 Bool.false 312869781098 2524 

noncomputable def Ns312p1074 := Ns312p1073 186065264 61 189812528 16 294906480 61 154981288 8 Bool.true 268435448 2589 Bool.false 156114124 Bool.false 192902585 14148475504056880 1 Bool.false 224304931 Bool.true Bool.false 202055715 Bool.false Bool.true 310386058 

noncomputable def Ns312p1075 := nat_lit 44123630464723369589108548020604807695573897434903 

noncomputable def Ns312p1076 := nat_lit 37857113661170338795113229415505058460598272000 

noncomputable def Ns312p1077 := nat_lit 52658999094162849921689677332480000 

noncomputable def Ns312p1078 := nat_lit 203081383079608112070571818792549089280 

noncomputable abbrev qz660 := (@Eq.refl Real qz748)

noncomputable abbrev qz484 := qz660

noncomputable abbrev qz171 := qz484

noncomputable def Ns312p1079 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz168 642756 1000 1652542102144 16000000 1285512 4000 2000 Ns312p1077 Ns312p1078 qz171 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns312p1080 := nat_lit 4164028194435999479124217636432833615077468556903076331520 

noncomputable abbrev qz661 := (@HSub.hSub Real Real Real qz715 qz716 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz717 (@Nat.cast Real Real.instNatCast 1285512))))

noncomputable abbrev qz485 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 642756 4000) (Real.log (Enclosure.sfrac Bool.false 1652542102144 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz661))

noncomputable abbrev qz662 := (Enclosure.sfrac Bool.false 642756 2000)

noncomputable abbrev qz172 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz485 qz662) (@HMul.hMul Real Real Real qz349 qz662 (Real.log Real.pi)))

noncomputable def Ns312p1081 := @Enclosure.Real.IsNear.addLit_ft_p qz172 (Enclosure.sfrac Bool.true Ns312p1077 Ns312p1078) 20504238535693863859 17592186044416000 4245013409185453141 451584000000000000000000 Ns312p1077 Ns312p1078 0 1 Ns312p1080 

noncomputable def Ns312p1082 := nat_lit 344004038828859663837036544000 

noncomputable abbrev qz173 := (@HSub.hSub Real Real Real qz355 qz485 qz662)

noncomputable def Ns312p1083 := @Enclosure.Real.IsNear.subLit_ff_p qz173 (@HMul.hMul Real Real Real qz5 qz662 (Real.log Real.pi)) 26976245454772669363 17592186044416000 2033613633876709 441000000000000000000 6172186774329 16777216000 160689 33554432000 Ns312p1082 20504238535693863859 17592186044416000 

noncomputable abbrev qz174 := qz485

noncomputable def Ns312p1084 := @Enclosure.Real.IsNear.subLit_ff_p qz174 qz662 32629987021354994611 17592186044416000 2033613633876709 441000000000000000000 642756 2000 0 1 53952490909545338726000 26976245454772669363 17592186044416000 2033613633876709 441000000000000000000 

noncomputable def Ns312p1085 := nat_lit 1175619179123827795489204401443176448 

noncomputable def Ns312p1086 := nat_lit 55829338485678309801721856 

noncomputable def Ns312p1087 := nat_lit 214911783424861910773629687009683977115522528904400711065178463746760070650465207978343621521283929224155243382008401085616619520 

noncomputable def Ns312p1088 := nat_lit 3693031170962462458400494516524032732268760411315059497345133761991463554554329061989750077527843009822130685295912527230664704 

noncomputable def Ns312p1089 := nat_lit 6103197892541250202704129202789184325558002059527645005399379029578810256208189222391605402943223373461490295229456056320 

noncomputable def Ns312p1090 := BSN.log_dyadic_bound 603966102144 2701118102144 6 5 Ns312p1087 134217728 35280000 Ns312p1088 Ns312p1089 61053190 3305084204288 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 603966102144) (BSN.artanhQ 2701118102144) 0 5 Ns312p1088 Ns312p1087 Ns312p1089 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz486 := (Real.log (Enclosure.sfrac Bool.false 1652542102144 16000000))

noncomputable def Ns312p1091 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 642756 4000) qz486 642756 4000 0 1 3249695203597559 281474976710656 781250441 27562500000000000 522190272570888158151 281474976710656000 41846117371283 9187500000000000000 (Enclosure.Real.IsNear.const Bool.false 642756 4000) (BSN.isNear_log_sfrac 1652542102144 16000000 3249695203597559 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1652542102144) qz358)) Bool.false Ns312p1086 Ns312p99 1000000564480000 35280000000000000000000 3249695203597559 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1652542102144 16000000 16 3305084204288 2097152000000 61053190 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns312p1090 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns312p1092 := BSN.arctan_dyadic_bound_f 1000 1285512 1 0 16777216 4410000 0 1 1 0 1 1 13050 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1285512) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1285512) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz487 := (@Nat.cast Real Real.instNatCast 1285512)

noncomputable def Ns312p1093 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz487)) 884279719003555 562949953421312 1 2000000000000000 13050 16777216 1 4410000 14828405353249798881280 883841833665955 562949953421312 200000000441 882000000000000000 qz15 (Ns312p1092 rfl) rfl rfl 

noncomputable abbrev qz488 := (@HMul.hMul Real Real Real qz579 qz584 qz661)

noncomputable abbrev qz175 := qz488

noncomputable abbrev qz489 := qz661

noncomputable abbrev qz176 := qz489

noncomputable def Ns312p1094 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 642756 4000) qz486) qz175 522190272570888158151 281474976710656000 41846117371283 9187500000000000000 883841833665955 2251799813685248 200000000441 3528000000000000000 Ns312p1085 32629987021354994611 17592186044416000 2033613633876709 441000000000000000000 (Ns312p1091 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz176 1 4 0 1 883841833665955 562949953421312 200000000441 882000000000000000 883841833665955 2251799813685248 200000000441 3528000000000000000 qz366 Ns312p1093 rfl) 

noncomputable def Ns312p1095 := @Ns312p1081 Ns312p1075 Ns312p1076 4245013409185453141 451584000000000000000000 (@Ns312p1083 4245013409185453141 451584000000000000000000 (Ns312p1084 (Ns312p1094 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 642756 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz662 (Real.log Real.pi) 642756 2000 0 1 38410761 33554432 1 67108864 6172186774329 16777216000 160689 33554432000 (Enclosure.Real.IsNear.const Bool.false 642756 2000) RS313to324.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns312p1077 Ns312p1078) 

noncomputable def Ns312p1096 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz168) Bool.false Ns312p1075 Ns312p1076 4245013409185453141 451584000000000000000000 39108722637 33554432 79 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz168) (@HAdd.hAdd Real Real Real qz367 qz172 (Enclosure.sfrac Bool.true Ns312p1077 Ns312p1078)) Bool.false Ns312p1075 Ns312p1076 4245013409185453141 451584000000000000000000 Ns312p1079 (Ns312p1095 rfl rfl)) 

noncomputable def Ns312p1097 := nat_lit 7595352308683457119125504 

noncomputable def Ns312p1098 := nat_lit 3509811822940427851985588938106618755516656006716013717862907494891086968182980973693382588226072919584304422437763888139457191495802840161 

noncomputable def Ns312p1099 := nat_lit 2500445961767412755607746815261240918085888122838048610393036605015303491532651075791205732943182432640967281500593682251909059339361 

noncomputable def Ns312p1100 := nat_lit 17527258578920267407665384186326520794532769997499700966687488385986461009189468188633933432508025788257900600567865254888230243036462081121 

noncomputable def Ns312p1101 := BSN.sin_dyadic_bound_f 107936448169 68719476736 4 3 33554432 8828614 Ns312p1098 Ns312p239 Ns312p1099 Ns312p1100 Ns312p242 Ns312p1099 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107936448169) qz602 0 3 Ns312p1098 Ns312p239 Ns312p1099 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107936448169) qz603 0 3 Ns312p1100 Ns312p242 Ns312p1099 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1102 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz168) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 39108722637) qz368) Bool.false 39108722637 33554432 79 8388608 Bool.true 33554431 33554432 1 4410000 (Ns312p1096 rfl) (Enclosure.sfrac_false_div 39108722637 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 39108722637) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns312p1097) qz369) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 185 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q1 39108722637 33554432 226375608064910080 72057594037927936 185 Ns312p1097 Ns312p99 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554431 33554432 Ns312p1097 Ns312p99 107936448169 68719476736 8828614 8820000 (Ns312p1101 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns312p1103 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz168) Bool.false Ns312p1075 Ns312p1076 4245013409185453141 451584000000000000000000 312869781098 268435456 2524 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz168) (@HAdd.hAdd Real Real Real qz367 qz172 (Enclosure.sfrac Bool.true Ns312p1077 Ns312p1078)) Bool.false Ns312p1075 Ns312p1076 4245013409185453141 451584000000000000000000 Ns312p1079 (Ns312p1095 rfl rfl)) 

noncomputable def Ns312p1104 := Ns312p1074 56221 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 458 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 224304931 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 292 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 202055715 268435456) qz171 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 1) Bool.true 33554431 33554432 22298663 2312110080000 268435448 268435456 2589 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz168)) Bool.true 33554431 33554432 22298663 2312110080000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz168) qz168) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz168)) Bool.true 33554431 33554432 356778608 36993761280000 33554431 33554432 22298663 2312110080000 (Ns312p1102 rfl rfl) rfl)) rfl) (Ns312p1103 rfl) RS313to324.d7 

noncomputable def Ns312p1105 := nat_lit 5181639003831366200932793032399469781075584028276864440836737592262656 

noncomputable def Ns312p1106 := nat_lit 352807307294969334569721846634147644044043885189404329465966821376 

noncomputable def Ns312p1107 := nat_lit 15544211396879508664129239653505141047938663997060214513851280843145216 

noncomputable def Ns312p1108 := BSN.cos_dyadic_bound_f 156114124 268435456 3 2 268435456 134217728 Ns312p1105 Ns312p123 Ns312p1106 Ns312p1107 Ns312p126 Ns312p1106 224304931 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 156114124) qz372 0 2 Ns312p1105 Ns312p123 Ns312p1106 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 156114124) qz373 0 2 Ns312p1107 Ns312p126 Ns312p1106 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1109 := nat_lit 12080639367534112693743255259131208019657351152481223803091187404690625 

noncomputable def Ns312p1110 := nat_lit 1917363164852039922764010333684951732335153976419786995378687890625 

noncomputable def Ns312p1111 := nat_lit 36238083376272634001384237756726254155507383149490831835282804838290625 

noncomputable def Ns312p1112 := BSN.cos_dyadic_bound_f 192902585 268435456 3 2 268435456 134217728 Ns312p1109 Ns312p123 Ns312p1110 Ns312p1111 Ns312p126 Ns312p1110 202055715 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 192902585) qz372 0 2 Ns312p1109 Ns312p123 Ns312p1110 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 192902585) qz373 0 2 Ns312p1111 Ns312p126 Ns312p1110 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1113 := nat_lit 5120590754404115996421977128901317823717833583273011671373127724183008181509090608149969766488477794304000000 

noncomputable def Ns312p1114 := nat_lit 859026706139541576666851522917579026412492665921081264174652307504584315384050920347140096000000000000 

noncomputable def Ns312p1115 := nat_lit 31042368460270920861768826396418800248229771480888398782395433856292392059683721773830361363676982253977600000 

noncomputable def Ns312p1116 := BSN.cos_dyadic_bound_f 312248640 268435456 4 3 268435456 134217728 Ns312p1113 Ns312p136 Ns312p1114 Ns312p1115 Ns312p139 Ns312p1114 106404665 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 312248640) qz372 0 3 Ns312p1113 Ns312p136 Ns312p1114 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 312248640) qz373 0 3 Ns312p1115 Ns312p139 Ns312p1114 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1117 := nat_lit 17311003027563453634714130003342784297427313009553360077832192049987840 

noncomputable def Ns312p1118 := nat_lit 1215348640034154141607400343234365800109459464883569846603222794496 

noncomputable def Ns312p1119 := nat_lit 45336373555344228031831547551056341329585642566839464900285050151158016 

noncomputable def Ns312p1120 := BSN.sin_dyadic_bound_f 182216462 268435456 3 2 268435456 134217728 Ns312p1117 Ns312p259 Ns312p1118 Ns312p1119 Ns312p262 Ns312p1118 168541672 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 182216462) qz370 0 2 Ns312p1117 Ns312p259 Ns312p1118 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 182216462) qz371 0 2 Ns312p1119 Ns312p262 Ns312p1118 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1121 := Ns312p1072 95779 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 174 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 106404665 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 83 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 168541672 268435456) qz171 rfl rfl (Ns312p1104 RS313to324.d9 RS313to324.d11 RS313to324.d13 RS313to324.d17 (Ns312p1108 rfl rfl) (Ns312p1112 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns312p1103 rfl) RS313to324.d19 RS313to324.d21 RS313to324.d23 RS313to324.d25 RS313to324.d17 (Ns312p1116 rfl rfl) (Ns312p1120 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns312p1122 := nat_lit 7999742467337230865217675700742393209624550521030069814368272222144967558501487557853553155837334303062757376 

noncomputable def Ns312p1123 := nat_lit 3269477108588249499474073299722138667351549627774172389277414855251508455042390349602032336189276164096 

noncomputable def Ns312p1124 := nat_lit 48476797739027921511639051397147065126341895401298321227189477640708449476219416146062214547746168357309255680 

noncomputable def Ns312p1125 := BSN.cos_dyadic_bound_f 349038386 268435456 4 3 268435456 134217728 Ns312p1122 Ns312p136 Ns312p1123 Ns312p1124 Ns312p139 Ns312p1123 71736508 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 349038386) qz372 0 3 Ns312p1122 Ns312p136 Ns312p1123 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 349038386) qz373 0 3 Ns312p1124 Ns312p139 Ns312p1123 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1126 := nat_lit 1065387800899559048806268246771609921966584949815614488615811406185121 

noncomputable def Ns312p1127 := nat_lit 14916457186156802855097351881769309534937024705367023764620526241 

noncomputable def Ns312p1128 := nat_lit 3196133569784304832813094545611066227280684975397432731799904977502881 

noncomputable def Ns312p1129 := BSN.cos_dyadic_bound_f 105125533 268435456 3 2 268435456 134217728 Ns312p1126 Ns312p123 Ns312p1127 Ns312p1128 Ns312p126 Ns312p1127 248112408 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 105125533) qz372 0 2 Ns312p1126 Ns312p123 Ns312p1127 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 105125533) qz373 0 2 Ns312p1128 Ns312p126 Ns312p1127 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1130 := Ns312p1070 129115 BSN.abs_quadSignPos (BSN.cos_quad_nat0 8 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 71736508 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 54 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 248112408 268435456) qz171 rfl rfl (Ns312p1121 rfl rfl) (Ns312p1103 rfl) RS313to324.d27 RS313to324.d29 RS313to324.d31 RS313to324.d33 RS313to324.d17 (Ns312p1125 rfl rfl) (Ns312p1129 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p1131 := nat_lit 10658061468550261015002990992328979459849225964524490563156650308849202424839515733789532059032114302035890176 

noncomputable def Ns312p1132 := nat_lit 7718821583498109552797079246836672994986718893000476184521243392790579401908728622930209402608397520896 

noncomputable def Ns312p1133 := nat_lit 64561427532692285113474417548237355617832009123528996778763127437334059008859777799328381702878174938203361280 

noncomputable def Ns312p1134 := BSN.cos_dyadic_bound_f 374940698 268435456 4 3 268435456 134217728 Ns312p1131 Ns312p136 Ns312p1132 Ns312p1133 Ns312p139 Ns312p1132 46481264 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 374940698) qz372 0 3 Ns312p1131 Ns312p136 Ns312p1132 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 374940698) qz373 0 3 Ns312p1133 Ns312p139 Ns312p1132 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1135 := nat_lit 1648220658077023319325004960000 

noncomputable def Ns312p1136 := BSN.sin_dyadic_bound_f 35830580 268435456 2 1 268435456 134217728 Ns312p1135 Ns312p115 Ns312p1135 Ns312p1135 Ns312p116 Ns312p1135 35724277 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 35830580) qz370 0 1 Ns312p1135 Ns312p115 Ns312p1135 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 35830580) qz371 0 1 Ns312p1135 Ns312p116 Ns312p1135 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1137 := Ns312p1068 158241 BSN.abs_quadSignPos (BSN.cos_quad_nat0 108 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 46481264 268435456) BSN.abs_quadSignNeg qz590 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 35724277 268435456) qz171 rfl rfl (Ns312p1130 rfl) (Ns312p1103 rfl) RS313to324.d35 RS313to324.d37 RS313to324.d39 RS313to324.d41 RS313to324.d17 (Ns312p1134 rfl rfl) (Ns312p1136 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p1138 := nat_lit 420106004271363351460372521889766977740589057070658698090448473358336 

noncomputable def Ns312p1139 := nat_lit 2319398594296473781600374063031914835972231416040642634653433856 

noncomputable def Ns312p1140 := nat_lit 1260313374016901461433554364921174869392095226749144012986076113207296 

noncomputable def Ns312p1141 := BSN.cos_dyadic_bound_f 83305164 268435456 3 2 268435456 134217728 Ns312p1138 Ns312p123 Ns312p1139 Ns312p1140 Ns312p126 Ns312p1139 255612573 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 83305164) qz372 0 2 Ns312p1138 Ns312p123 Ns312p1139 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 83305164) qz373 0 2 Ns312p1140 Ns312p126 Ns312p1139 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1142 := Ns312p1066 Bool.true 348180116 158241 Bool.true 83305164 14148475504056880 1 Bool.false 255612573 Bool.false Bool.true 267348324 171652 BSN.abs_quadSignPos qz374 (BSN.sfrac_eq_quadSignPos_mul Bool.false 255612573 268435456) qz171 rfl (Ns312p1137 rfl) (Ns312p1103 rfl) RS313to324.d43 RS313to324.d45 RS313to324.d17 (Ns312p1141 rfl rfl) rfl 

noncomputable def Ns312p1143 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) 267348324 268435456 171652 268435456 267348324 268435456 171652 268435456 143531538527551488 66837081 33554432 42913 33554432 (Ns312p1142 rfl rfl rfl rfl) 

noncomputable def Ns312p1144 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz169) (Zeta.RiemannSiegel.correction qz170) 5275375 16777216 1 16777216 385720989737787 562949953421312 2532362177754461 155163080911749120000 2034822866237978095125 9444732965739290427392 

noncomputable def Ns312p1145 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz169 1 1 0 1 5275375 16777216 1 16777216 5275375 16777216 1 16777216 

noncomputable abbrev qz177 := qz482

noncomputable def Ns312p1146 := @Enclosure.Real.IsNear.sqrt_image qz177 858135983217 8388608000 160689 8388608000 169688715 169688748 16777216 (@Enclosure.Real.IsNear.of_eq qz177 (@HMul.hMul Real Real Real qz5 qz168 qz3) Bool.false 858135983217 8388608000 160689 8388608000 (BSN.t_div_two_pi_mk qz168 642756 1000 qz171) (@Enclosure.Real.IsNear.mulLit_ff qz168 qz3 642756 1000 0 1 5340353 33554432 1 33554432 858135983217 8388608000 160689 8388608000 (Enclosure.Real.IsNear.const Bool.false 642756 1000) RS313to324.d48 rfl)) 

noncomputable abbrev qz751 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 642756 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz663 := qz751

noncomputable abbrev qz490 := qz663

noncomputable abbrev qz178 := qz490

noncomputable def Ns312p1147 := @Enclosure.Real.IsNear.sqrt_image qz178 339377463 33554432 33 33554432 53356388 53356394 16777216 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 339377463 33554432 33 33554432 339377463 33554432 33 33554432 (Ns312p1146 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns312p1148 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz178) 53356391 16777216 3 16777216 5275374 5275376 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz178) Bool.false 106712782 33554432 6 33554432 53356391 16777216 3 16777216 (Ns312p1147 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns312p1149 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz178)) Bool.false 10550750 33554432 2 33554432 5275375 16777216 1 16777216 (Ns312p1148 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz179 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz483))

noncomputable abbrev qz664 := (@HMul.hMul Real Real Real qz711 qz750 qz750)

noncomputable abbrev qz491 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz664 qz659) qz594)

noncomputable abbrev qz180 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz491))

noncomputable def Ns312p1150 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz170) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz179) qz180) Bool.false 385720989737787 

noncomputable def Ns312p1151 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz179) qz180 44544753 33554432 383 

noncomputable def Ns312p1152 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz179) Bool.false 44544753 33554432 383 33554432 44544753 33554432 383 

noncomputable def Ns312p1153 := @Enclosure.Real.IsNear.recentre' qz179 Bool.false 12637851 16777216 955244432 147975045120000 12637851 16777216 59702777 9248440320000 

noncomputable abbrev qz181 := (@HMul.hMul Real Real Real qz349 qz346 qz483)

noncomputable def Ns312p1154 := @Enclosure.Real.IsNear.cos_image qz181 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24084347) qz368) Bool.false 24084347 33554432 209 33554432 Bool.false 12637851 16777216 1 

noncomputable def Ns312p1155 := nat_lit 890540488531379947672358567 

noncomputable def Ns312p1156 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz170 884279719003555 140737488355328 1 500000000000000 3833143 33554432 33 33554432 3389570614940443823365 4722366482869645213696 Ns312p1155 

noncomputable def Ns312p1157 := @Enclosure.Real.IsNear.subLit_ff_p qz178 qz1 339377463 33554432 33 33554432 10 1 0 1 3833143 3833143 33554432 33 

noncomputable def Ns312p1158 := @Ns312p1157 33554432 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 339377463 33554432 33 33554432 339377463 33554432 33 33554432 (Ns312p1146 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns312p1159 := @Enclosure.Real.IsNear.recentre' qz181 Bool.false 3389570614940443823365 4722366482869645213696 Ns312p1155 Ns312p796 24084347 33554432 209 33554432 (@Ns312p1156 Ns312p796 RS313to324.d47 (Ns312p1158 rfl rfl) rfl) 

noncomputable def Ns312p1160 := nat_lit 716666262233013804810484886883657445846532377796034045841091041 

noncomputable def Ns312p1161 := nat_lit 113208492188256956362711080031760943810164483774657152788961 

noncomputable def Ns312p1162 := nat_lit 2149772369714664900518729238490908815651976804420552823217695201 

noncomputable def Ns312p1163 := BSN.cos_dyadic_bound_f 24084347 33554432 3 2 16777216 4410000 Ns312p1160 Ns312p463 Ns312p1161 Ns312p1162 Ns312p466 Ns312p1161 12637851 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 24084347) qz395 0 2 Ns312p1160 Ns312p463 Ns312p1161 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 24084347) (BSN.cosOddQ 33554432) 0 2 Ns312p1162 Ns312p466 Ns312p1161 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1164 := @Enclosure.Real.IsNear.inv_image qz179 12637851 16777216 59702777 9248440320000 22272185 22272568 16777216 (Ns312p1153 (@Ns312p1154 4410000 (Ns312p1159 rfl) (Enclosure.sfrac_false_div 24084347 33554432) (Ns312p1163 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns312p1165 := @Enclosure.Real.IsNear.recentre' qz180 Bool.false 8659179 16777216 

noncomputable abbrev qz182 := (@HMul.hMul Real Real Real qz349 qz346 qz491)

noncomputable def Ns312p1166 := @Enclosure.Real.IsNear.cos_image qz182 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 34509829)) qz368) Bool.true 34509829 33554432 

noncomputable def Ns312p1167 := nat_lit 162968061160610417544463713005 

noncomputable def Ns312p1168 := nat_lit 36708747733396194985635972775445833 

noncomputable def Ns312p1169 := @Enclosure.Real.IsNear.recentre' qz182 Bool.true Ns312p1167 Ns312p809 Ns312p1168 

noncomputable abbrev qz183 := qz491

noncomputable def Ns312p1170 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz183 884279719003555 140737488355328 1 500000000000000 184294695058991 

noncomputable abbrev qz492 := (@HSub.hSub Real Real Real qz583 qz664 qz659)

noncomputable abbrev qz184 := qz492

noncomputable def Ns312p1171 := @Enclosure.Real.IsNear.subLit_tf qz184 qz29 113925950881327 1125899906842624 1360284783 1125899906842624 1 16 

noncomputable abbrev qz493 := qz664

noncomputable abbrev qz185 := qz493

noncomputable def Ns312p1172 := @Enclosure.Real.IsNear.subLit_ff_n qz185 qz170 14692985258449 1125899906842624 252988527 1125899906842624 3833143 33554432 33 33554432 

noncomputable def Ns312p1173 := @Enclosure.Real.IsNear.mulLit_ff qz170 qz170 3833143 33554432 33 33554432 3833143 33554432 33 33554432 14692985258449 1125899906842624 

noncomputable def Ns312p1174 := nat_lit 3022520209498261348925297163232184350575993566246862778557404641 

noncomputable def Ns312p1175 := nat_lit 2011603851921990658998349024846763432579060764941456448558561 

noncomputable def Ns312p1176 := nat_lit 9063537420790940065457894791646859524862822577210705422775096801 

noncomputable def Ns312p1177 := BSN.cos_dyadic_bound_f 34509829 33554432 3 2 16777216 4410000 Ns312p1174 Ns312p463 Ns312p1175 Ns312p1176 Ns312p466 Ns312p1175 8659179 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 34509829) qz395 0 2 Ns312p1174 Ns312p463 Ns312p1175 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 34509829) (BSN.cosOddQ 33554432) 0 2 Ns312p1176 Ns312p466 Ns312p1175 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1178 := @Ns312p1165 4541072 578027520000 8659179 16777216 283817 36126720000 (@Ns312p1166 1 131072 Bool.false 8659179 16777216 1 4410000 (@Ns312p1169 Ns312p812 34509829 33554432 1 131072 (@Ns312p1170 1125899906842624 1360284783 1125899906842624 Ns312p1167 Ns312p809 Ns312p1168 Ns312p812 RS313to324.d47 (@Ns312p1171 0 1 2948715120943856 184294695058991 1125899906842624 1360284783 1125899906842624 (@Ns312p1172 3822720571882826891264 113925950881327 1125899906842624 1360284783 1125899906842624 (@Ns312p1173 252988527 1125899906842624 (Ns312p1158 rfl rfl) (Ns312p1158 rfl rfl) rfl) (Ns312p1158 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 34509829 33554432) (BSN.cos_neg_of_bound 34509829 33554432 Bool.false 8659179 16777216 1 4410000 (Ns312p1177 rfl rfl)) rfl rfl) 

noncomputable def Ns312p1179 := @Ns312p1144 13465477003630094994211 Ns312p75 (Ns312p1145 qz31 (@Enclosure.Real.IsNear.of_eq qz169 (@Inv.inv Real Real.instInv (Real.sqrt qz178)) Bool.false 5275375 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz177 (BSN.t_div_two_pi_nonneg qz168 642756 1000 qz171)) Ns312p1149) rfl) (@Ns312p1150 562949953421312 2532362177754461 155163080911749120000 (BSN.correction_mk qz170 (BSN.cos_two_pi_p_ne_zero_mk qz168 642756 1000 10 qz171 rfl rfl (@BSN.floor_sqrt_eq_dec qz168 642756 1000 10 qz171 rfl rfl rfl))) (@Ns312p1151 33554432 8659179 16777216 283817 36126720000 385720989737787 562949953421312 2532362177754461 155163080911749120000 (@Ns312p1152 33554432 (Ns312p1164 rfl rfl rfl rfl rfl) rfl) (Ns312p1178 rfl) rfl)) 

noncomputable def Ns312p1180 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz168) (hardyZApproximantRS₀ qz168) Bool.true 20847788684121206730261 9444732965739290427392 Ns312p1063 Ns312p75 (@Eq.refl Real (hardyZApproximantRS₀ qz168)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz168) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz169) (Zeta.RiemannSiegel.correction qz170))) Bool.true 20847788684121206730261 9444732965739290427392 Ns312p1063 Ns312p75 (BSN.hardyZApproximantRS₀_eq qz168 10 (@BSN.floor_sqrt_eq_dec qz168 642756 1000 10 qz171 rfl rfl rfl)) (@Ns312p1065 20847788684121206730261 9444732965739290427392 Ns312p1063 Ns312p75 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 10)) Bool.true 66837081 33554432 42913 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz168) qz168 10) (Ns312p1143 (Ns312p1142 rfl rfl rfl rfl) rfl rfl)) (Ns312p1179 rfl) rfl rfl)) 

theorem RS313to324.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz168) Bool.true 20847788684121206730261 9444732965739290427392 Ns312p1063 Ns312p75 := Ns312p1180 

noncomputable def Ns312p1181 := nat_lit 86773484122729730801664000 

noncomputable def Ns312p1182 := nat_lit 2403016494849745200036205035520 

noncomputable abbrev qz752 := (Enclosure.sfrac Bool.false 644113 1000)

noncomputable abbrev qz665 := qz752

noncomputable abbrev qz494 := qz665

noncomputable abbrev qz186 := qz494

noncomputable abbrev qz753 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 644113 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz666 := qz753

noncomputable abbrev qz495 := qz666

noncomputable abbrev qz187 := (@HPow.hPow Real Real Real qz350 qz495 qz352)

noncomputable abbrev qz754 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 644113 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz667 := qz754

noncomputable abbrev qz496 := qz667

noncomputable abbrev qz188 := qz496

noncomputable def Ns312p1183 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz186) qz186 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz187) (Zeta.RiemannSiegel.correction qz188)) 536985157 134217728 86013 67108864 989617499452449720909 4722366482869645213696 460977290590925346641 Ns312p1181 Ns312p1182 

noncomputable def Ns312p1184 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz186) qz186 Real.cos BSN.quadSignPos 9 10 644113 1000 200 268435456 134217728 4503599627370496 Bool.false 313712866519 2530 618095470 62 84886744 8 

noncomputable def Ns312p1185 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz186) qz186 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 644113 1000 108 156 268435456 134217728 4503599627370496 Bool.false 313712866519 2530 

noncomputable def Ns312p1186 := Ns312p1185 558195838 62 94906264 8 589812974 62 89478488 8 Bool.false 408539359 129399 Bool.true 289327029 Bool.true 414778793 14148475504056880 1 Bool.false 127035359 Bool.false Bool.false 6877882 Bool.false Bool.false 455745767 

noncomputable def Ns312p1187 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz186) qz186 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 644113 1000 9 53 268435456 134217728 4503599627370496 Bool.false 313712866519 2530 

noncomputable def Ns312p1188 := Ns312p1187 480971758 62 109588312 8 522351262 62 101459064 8 Bool.false 555959962 95993 Bool.false 117787703 Bool.true 392528203 14148475504056880 1 Bool.false 114044123 Bool.true Bool.false 266856529 Bool.true Bool.false 408539359 

noncomputable def Ns312p1189 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz186) qz186 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 644113 1000 175 84 268435456 134217728 4503599627370496 Bool.false 313712866519 2530 

noncomputable def Ns312p1190 := Ns312p1189 372130544 61 134217720 8 432030192 61 120047984 16 Bool.false 335155186 56351 Bool.false 228695484 Bool.false 17379484 14148475504056880 1 Bool.false 202016631 Bool.false Bool.false 267873047 Bool.false Bool.false 555959962 

noncomputable def Ns312p1191 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz186) qz186 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 644113 1000 459 293 268435456 134217728 4503599627370496 Bool.false 313712866519 2530 

noncomputable def Ns312p1192 := Ns312p1191 186065264 61 189812528 16 294906480 61 154981288 8 Bool.false 268435328 2605 Bool.false 325051553 Bool.false 214142484 14148475504056880 1 Bool.false 251238770 Bool.false Bool.false 192141198 Bool.true Bool.false 335155186 

noncomputable def Ns312p1193 := nat_lit 845683617069907024198033613897853578126997783828817085587 

noncomputable def Ns312p1194 := nat_lit 723628169600551676235772140688572207747564929286144000 

noncomputable def Ns312p1195 := nat_lit 53217224794815452152439138460640000 

noncomputable def Ns312p1196 := nat_lit 205667495720419900702544322453085273920 

noncomputable abbrev qz668 := (@Eq.refl Real qz752)

noncomputable abbrev qz497 := qz668

noncomputable abbrev qz189 := qz497

noncomputable def Ns312p1197 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz186 644113 1000 1659527227076 16000000 1288226 4000 2000 Ns312p1195 Ns312p1196 qz189 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns312p1198 := nat_lit 270618757462370247743370756447313145000639290825221467387840 

noncomputable abbrev qz669 := (@HSub.hSub Real Real Real qz715 qz716 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz717 (@Nat.cast Real Real.instNatCast 1288226))))

noncomputable abbrev qz498 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 644113 4000) (Real.log (Enclosure.sfrac Bool.false 1659527227076 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz669))

noncomputable abbrev qz670 := (Enclosure.sfrac Bool.false 644113 2000)

noncomputable abbrev qz190 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz498 qz670) (@HMul.hMul Real Real Real qz349 qz670 (Real.log Real.pi)))

noncomputable def Ns312p1199 := @Enclosure.Real.IsNear.addLit_ft_p qz190 (Enclosure.sfrac Bool.true Ns312p1195 Ns312p1196) 1315807422226369967627 1125899906842624000 270090255467412619 28672000000000000000000 Ns312p1195 Ns312p1196 0 1 Ns312p1198 

noncomputable def Ns312p1200 := nat_lit 17660468269676007874232949145600 

noncomputable abbrev qz191 := (@HSub.hSub Real Real Real qz355 qz498 qz670)

noncomputable def Ns312p1201 := @Enclosure.Real.IsNear.subLit_ff_p qz191 (@HMul.hMul Real Real Real qz5 qz670 (Real.log Real.pi)) 346178070126556105423 225179981368524800 32346893036039 7000000000000000000 24740870499993 67108864000 644113 134217728000 Ns312p1200 1315807422226369967627 1125899906842624000 

noncomputable def Ns312p1202 := nat_lit 3461780701265561054230000 

noncomputable abbrev qz192 := qz498

noncomputable def Ns312p1203 := @Enclosure.Real.IsNear.subLit_ff_p qz192 qz670 2093493733980842063371 1125899906842624000 32346893036039 7000000000000000000 644113 2000 0 1 Ns312p1202 346178070126556105423 225179981368524800 32346893036039 7000000000000000000 

noncomputable def Ns312p1204 := nat_lit 4714128800129294298104256011863851008 

noncomputable def Ns312p1205 := nat_lit 55849735432505858853961728 

noncomputable def Ns312p1206 := nat_lit 21025698009664245531535089428300507962702538014088912196522822015411810414325837981598571720530928460384168077040462050056534497110583053464162436655349760 

noncomputable def Ns312p1207 := nat_lit 368012472412476455694679113334309069673932664595638145944216793675428212382680550885967445588578000040773840695521316910665748904144745341465027644751872 

noncomputable def Ns312p1208 := nat_lit 28112727993631997451854050164286426271287562980873982469339094848120340697759766024375518053015507592286173255697231984394467785663381375570411520 

noncomputable def Ns312p1209 := BSN.log_dyadic_bound 610951227076 2708103227076 7 6 Ns312p1206 134217728 35280000 Ns312p1207 Ns312p1208 61619319 3319054454152 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 610951227076) (BSN.artanhQ 2708103227076) 0 6 Ns312p1207 Ns312p1206 Ns312p1208 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz499 := (Real.log (Enclosure.sfrac Bool.false 1659527227076 16000000))

noncomputable def Ns312p1210 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 644113 4000) qz499 644113 4000 0 1 3250882462162167 281474976710656 781250441 27562500000000000 2093935655350659872871 1125899906842624000 503213565303833 110250000000000000000 (Enclosure.Real.IsNear.const Bool.false 644113 4000) (BSN.isNear_log_sfrac 1659527227076 16000000 3250882462162167 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1659527227076) qz358)) Bool.false Ns312p1205 Ns312p99 1000000564480000 35280000000000000000000 3250882462162167 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1659527227076 16000000 16 3319054454152 2097152000000 61619319 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns312p1209 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns312p1211 := BSN.arctan_dyadic_bound_f 1000 1288226 1 0 16777216 4410000 0 1 1 0 1 1 13023 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1288226) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1288226) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz500 := (@Nat.cast Real Real.instNatCast 1288226)

noncomputable def Ns312p1212 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz500)) 884279719003555 562949953421312 1 2000000000000000 13023 16777216 1 4410000 14828420552898541256704 883842739635619 562949953421312 200000000441 882000000000000000 qz15 (Ns312p1211 rfl) rfl rfl 

noncomputable abbrev qz501 := (@HMul.hMul Real Real Real qz579 qz584 qz669)

noncomputable abbrev qz193 := qz501

noncomputable abbrev qz502 := qz669

noncomputable abbrev qz194 := qz502

noncomputable def Ns312p1213 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 644113 4000) qz499) qz193 2093935655350659872871 1125899906842624000 503213565303833 110250000000000000000 883842739635619 2251799813685248 200000000441 3528000000000000000 Ns312p1204 2093493733980842063371 1125899906842624000 32346893036039 7000000000000000000 (Ns312p1210 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz194 1 4 0 1 883842739635619 562949953421312 200000000441 882000000000000000 883842739635619 2251799813685248 200000000441 3528000000000000000 qz366 Ns312p1212 rfl) 

noncomputable def Ns312p1214 := @Ns312p1199 Ns312p1193 Ns312p1194 270090255467412619 28672000000000000000000 (@Ns312p1201 270090255467412619 28672000000000000000000 (Ns312p1203 (Ns312p1213 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 644113 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz670 (Real.log Real.pi) 644113 2000 0 1 38410761 33554432 1 67108864 24740870499993 67108864000 644113 134217728000 (Enclosure.Real.IsNear.const Bool.false 644113 2000) RS313to324.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns312p1195 Ns312p1196) 

noncomputable def Ns312p1215 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz186) Bool.false Ns312p1193 Ns312p1194 270090255467412619 28672000000000000000000 19607054157 16777216 159 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz186) (@HAdd.hAdd Real Real Real qz367 qz190 (Enclosure.sfrac Bool.true Ns312p1195 Ns312p1196)) Bool.false Ns312p1193 Ns312p1194 270090255467412619 28672000000000000000000 Ns312p1197 (Ns312p1214 rfl rfl)) 

noncomputable def Ns312p1216 := nat_lit 3795609537747250906660864 

noncomputable def Ns312p1217 := nat_lit 3502162879163975695655256919034338255594832094806359419580944556119708119104625897767700827606784041591250137655649947278021070792262742401 

noncomputable def Ns312p1218 := nat_lit 2484166453708779636782876998890859882456280403965220771993962891510502791287265798757868958240484271167343551866198634120940612284801 

noncomputable def Ns312p1219 := nat_lit 17489108608325172736393795317704823096911509319516056032150975485252117177462947708165529916236888254905302164197237300549337442553802060161 

noncomputable def Ns312p1220 := BSN.sin_dyadic_bound_f 107877711393 68719476736 4 3 33554432 8828614 Ns312p1217 Ns312p239 Ns312p1218 Ns312p1219 Ns312p242 Ns312p1218 33554416 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107877711393) qz602 0 3 Ns312p1217 Ns312p239 Ns312p1218 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107877711393) qz603 0 3 Ns312p1219 Ns312p242 Ns312p1218 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1221 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz186) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 19607054157) qz378) Bool.false 19607054157 16777216 159 16777216 Bool.false 33554416 33554432 1 4410000 (Ns312p1215 rfl) (Enclosure.sfrac_false_div 19607054157 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 19607054157) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns312p1216) qz614) 226375608064910080 72057594037927936 Bool.false 33554416 33554432 185 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q3 19607054157 16777216 226375608064910080 72057594037927936 185 Ns312p1216 Ns312p394 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554416 33554432 Ns312p1216 Ns312p394 107877711393 68719476736 8828614 8820000 (Ns312p1220 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns312p1222 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz186) Bool.false Ns312p1193 Ns312p1194 270090255467412619 28672000000000000000000 313712866519 268435456 2530 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz186) (@HAdd.hAdd Real Real Real qz367 qz190 (Enclosure.sfrac Bool.true Ns312p1195 Ns312p1196)) Bool.false Ns312p1193 Ns312p1194 270090255467412619 28672000000000000000000 Ns312p1197 (Ns312p1214 rfl rfl)) 

noncomputable def Ns312p1223 := Ns312p1192 56351 BSN.abs_quadSignPos (BSN.cos_quad_nat3 459 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 251238770 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 293 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 192141198 268435456) qz189 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 1) Bool.false 2097151 2097152 44872951 4624220160000 268435328 268435456 2605 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz186)) Bool.false 2097151 2097152 44872951 4624220160000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz186) qz186) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz186)) Bool.false 33554416 33554432 717967216 73987522560000 2097151 2097152 44872951 4624220160000 (Ns312p1221 rfl rfl) rfl)) rfl) (Ns312p1222 rfl) RS313to324.d7 

noncomputable def Ns312p1224 := nat_lit 15629165544953037105225267498759556051867231381753275074823274019765820770185073771398228255396471037794746241 

noncomputable def Ns312p1225 := nat_lit 1391319729747455748819207915950938587517338452617717367535471532024451533681316356320983212547309600641 

noncomputable def Ns312p1226 := nat_lit 78111499495216743139402338908689298083913737332421651828583711636458196199929784134583257293471417904081174401 

noncomputable def Ns312p1227 := BSN.sin_dyadic_bound_f 325051553 268435456 4 3 268435456 134217728 Ns312p1224 Ns312p147 Ns312p1225 Ns312p1226 Ns312p150 Ns312p1225 251238770 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 325051553) qz370 0 3 Ns312p1224 Ns312p147 Ns312p1225 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 325051553) qz371 0 3 Ns312p1226 Ns312p150 Ns312p1225 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1228 := nat_lit 33022565146443634699410842886282015974605759777583312867920085415690240 

noncomputable def Ns312p1229 := nat_lit 4422040223040204737814063258397115722895804099891135681594403127296 

noncomputable def Ns312p1230 := nat_lit 86480511127943644833643365742605970317558968115604090910591928007458816 

noncomputable def Ns312p1231 := BSN.sin_dyadic_bound_f 214142484 268435456 3 2 268435456 134217728 Ns312p1228 Ns312p259 Ns312p1229 Ns312p1230 Ns312p262 Ns312p1229 192141198 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 214142484) qz370 0 2 Ns312p1228 Ns312p259 Ns312p1229 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 214142484) qz371 0 2 Ns312p1230 Ns312p262 Ns312p1229 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1232 := nat_lit 42958322190384091239898891054265633019521519842079164139960649283338240 

noncomputable def Ns312p1233 := nat_lit 7482740947049314669194562721583957005861928736657334227488745783296 

noncomputable def Ns312p1234 := nat_lit 112497776537091682928366018707241712454070680273205127539719099677474816 

noncomputable def Ns312p1235 := BSN.sin_dyadic_bound_f 228695484 268435456 3 2 268435456 134217728 Ns312p1232 Ns312p259 Ns312p1233 Ns312p1234 Ns312p262 Ns312p1233 202016631 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 228695484) qz370 0 2 Ns312p1232 Ns312p259 Ns312p1233 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 228695484) qz371 0 2 Ns312p1234 Ns312p262 Ns312p1233 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1236 := nat_lit 91232066479091794168858337536 

noncomputable def Ns312p1237 := BSN.cos_dyadic_bound_f 17379484 268435456 2 1 268435456 134217728 Ns312p1236 Ns312p119 Ns312p1236 Ns312p1236 Ns312p120 Ns312p1236 267873047 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 17379484) qz372 0 1 Ns312p1236 Ns312p119 Ns312p1236 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 17379484) qz373 0 1 Ns312p1236 Ns312p120 Ns312p1236 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1238 := Ns312p1190 95993 BSN.abs_quadSignPos (BSN.cos_quad_nat3 175 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 202016631 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 84 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 267873047 268435456) qz189 rfl rfl (Ns312p1223 RS313to324.d9 RS313to324.d11 RS313to324.d13 RS313to324.d17 (Ns312p1227 rfl rfl) (Ns312p1231 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns312p1222 rfl) RS313to324.d19 RS313to324.d21 RS313to324.d23 RS313to324.d25 RS313to324.d17 (Ns312p1235 rfl rfl) (Ns312p1237 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns312p1239 := nat_lit 192486293757245273967461066731681 

noncomputable def Ns312p1240 := BSN.sin_dyadic_bound_f 117787703 268435456 2 1 268435456 134217728 Ns312p1239 Ns312p115 Ns312p1239 Ns312p1239 Ns312p116 Ns312p1239 114044123 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 117787703) qz370 0 1 Ns312p1239 Ns312p115 Ns312p1239 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 117787703) qz371 0 1 Ns312p1239 Ns312p116 Ns312p1239 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1241 := nat_lit 33262729262393726332197320694964205543398576468899148596350559233071615772184940449984613950163671855839613841 

noncomputable def Ns312p1242 := nat_lit 13379823766434106549152294302475388135641021151172284077481100060716781203105919754476711154868363236241 

noncomputable def Ns312p1243 := nat_lit 166158379126012116574086330859630232462568348348829472072256552630198084687102581349062113158145822834641114001 

noncomputable def Ns312p1244 := BSN.sin_dyadic_bound_f 392528203 268435456 4 3 268435456 134217728 Ns312p1241 Ns312p147 Ns312p1242 Ns312p1243 Ns312p150 Ns312p1242 266856529 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 392528203) qz370 0 3 Ns312p1241 Ns312p147 Ns312p1242 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 392528203) qz371 0 3 Ns312p1243 Ns312p150 Ns312p1242 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1245 := Ns312p1188 129399 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 9 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 114044123 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 53 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 266856529 268435456) qz189 rfl rfl (Ns312p1238 rfl rfl) (Ns312p1222 rfl) RS313to324.d27 RS313to324.d29 RS313to324.d31 RS313to324.d33 RS313to324.d17 (Ns312p1240 rfl rfl) (Ns312p1244 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p1246 := nat_lit 3773545203193407265599270895482450890671610675640910854667201362633553038288304628015460893694612979811192721 

noncomputable def Ns312p1247 := nat_lit 344086860919497037271206953088225734203558233783190986123315622045161696901085516114765246483964465041 

noncomputable def Ns312p1248 := nat_lit 22880588851363605838727259160981919951031147047029691538394517473220399555266580951243638012213343757316755345 

noncomputable def Ns312p1249 := BSN.cos_dyadic_bound_f 289327029 268435456 4 3 268435456 134217728 Ns312p1246 Ns312p136 Ns312p1247 Ns312p1248 Ns312p139 Ns312p1247 127035359 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 289327029) qz372 0 3 Ns312p1246 Ns312p136 Ns312p1247 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 289327029) qz373 0 3 Ns312p1248 Ns312p139 Ns312p1247 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1250 := nat_lit 15980219572464493702888071852998338063891561140505766660732816524751927202078921961306544659358049168384989281 

noncomputable def Ns312p1251 := nat_lit 25929761473192666502657317901079485391033604174574738388788520621700875141974946273561566406121344866401 

noncomputable def Ns312p1252 := nat_lit 96727975792701066573326056109520175457887521278754640522994880668631351510771785064543251133924369282107578465 

noncomputable def Ns312p1253 := BSN.cos_dyadic_bound_f 414778793 268435456 4 3 268435456 134217728 Ns312p1250 Ns312p136 Ns312p1251 Ns312p1252 Ns312p139 Ns312p1251 6877882 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 414778793) qz372 0 3 Ns312p1250 Ns312p136 Ns312p1251 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 414778793) qz373 0 3 Ns312p1252 Ns312p139 Ns312p1251 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1254 := Ns312p1186 158587 BSN.abs_quadSignPos (BSN.cos_quad_nat0 108 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 127035359 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 156 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 6877882 268435456) qz189 rfl rfl (Ns312p1245 rfl) (Ns312p1222 rfl) RS313to324.d35 RS313to324.d37 RS313to324.d39 RS313to324.d41 RS313to324.d17 (Ns312p1249 rfl rfl) (Ns312p1253 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p1255 := nat_lit 38901381735935843781254585850625 

noncomputable def Ns312p1256 := BSN.cos_dyadic_bound_f 78975295 268435456 2 1 268435456 134217728 Ns312p1255 Ns312p119 Ns312p1255 Ns312p1255 Ns312p120 Ns312p1255 256901513 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 78975295) qz372 0 1 Ns312p1255 Ns312p119 Ns312p1255 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 78975295) qz373 0 1 Ns312p1255 Ns312p120 Ns312p1255 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1257 := Ns312p1184 Bool.false 455745767 158587 Bool.true 78975295 14148475504056880 1 Bool.false 256901513 Bool.false Bool.false 536985157 172026 BSN.abs_quadSignPos qz374 (BSN.sfrac_eq_quadSignPos_mul Bool.false 256901513 268435456) qz189 rfl (Ns312p1254 rfl) (Ns312p1222 rfl) RS313to324.d43 RS313to324.d45 RS313to324.d17 (Ns312p1256 rfl rfl) rfl 

noncomputable def Ns312p1258 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 10) 536985157 268435456 172026 268435456 536985157 268435456 172026 268435456 288291710969053184 536985157 134217728 86013 67108864 (Ns312p1257 rfl rfl rfl rfl) 

noncomputable def Ns312p1259 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz187) (Zeta.RiemannSiegel.correction qz188) 10545189 33554432 1 33554432 93845401865481 140737488355328 217754673615007 12930256742645760000 989617499452449720909 4722366482869645213696 

noncomputable def Ns312p1260 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz187 1 1 0 1 10545189 33554432 1 33554432 10545189 33554432 1 33554432 

noncomputable abbrev qz195 := qz495

noncomputable def Ns312p1261 := @Enclosure.Real.IsNear.sqrt_image qz195 3439790791889 33554432000 644113 33554432000 169867746 169867778 16777216 (@Enclosure.Real.IsNear.of_eq qz195 (@HMul.hMul Real Real Real qz5 qz186 qz3) Bool.false 3439790791889 33554432000 644113 33554432000 (BSN.t_div_two_pi_mk qz186 644113 1000 qz189) (@Enclosure.Real.IsNear.mulLit_ff qz186 qz3 644113 1000 0 1 5340353 33554432 1 33554432 3439790791889 33554432000 644113 33554432000 (Enclosure.Real.IsNear.const Bool.false 644113 1000) RS313to324.d48 rfl)) 

noncomputable abbrev qz755 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 644113 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz671 := qz755

noncomputable abbrev qz503 := qz671

noncomputable abbrev qz196 := qz503

noncomputable def Ns312p1262 := @Enclosure.Real.IsNear.sqrt_image qz196 84933881 8388608 1 1048576 53384528 53384534 16777216 (@Enclosure.Real.IsNear.recentre' qz196 Bool.false 339735524 33554432 32 33554432 84933881 8388608 1 1048576 (Ns312p1261 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns312p1263 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz196) 53384531 16777216 3 16777216 5272594 5272595 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz196) Bool.false 106769062 33554432 6 33554432 53384531 16777216 3 16777216 (Ns312p1262 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns312p1264 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz196)) Bool.false 10545189 33554432 1 33554432 10545189 33554432 1 33554432 (Ns312p1263 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz197 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz496))

noncomputable abbrev qz672 := (@HMul.hMul Real Real Real qz711 qz754 qz754)

noncomputable abbrev qz504 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz672 qz667) qz594)

noncomputable abbrev qz198 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz504))

noncomputable def Ns312p1265 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz188) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz197) qz198) Bool.false 93845401865481 

noncomputable def Ns312p1266 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz197) qz198 23712807 16777216 105 

noncomputable def Ns312p1267 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz197) Bool.false 47425614 33554432 420 33554432 23712807 16777216 105 

noncomputable def Ns312p1268 := @Enclosure.Real.IsNear.recentre' qz197 Bool.false 11870167 16777216 462187216 73987522560000 11870167 16777216 28886701 4624220160000 

noncomputable abbrev qz199 := (@HMul.hMul Real Real Real qz349 qz346 qz496)

noncomputable def Ns312p1269 := @Enclosure.Real.IsNear.cos_image qz199 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 26334111) qz368) Bool.false 26334111 33554432 101 16777216 Bool.false 11870167 16777216 1 

noncomputable def Ns312p1270 := nat_lit 26986075410169113212097991 

noncomputable def Ns312p1271 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz188 884279719003555 140737488355328 1 500000000000000 1047801 8388608 1 1048576 926549173851643932555 1180591620717411303424 Ns312p1270 

noncomputable def Ns312p1272 := @Enclosure.Real.IsNear.subLit_ff_p qz196 qz1 84933881 8388608 1 1048576 10 1 0 1 1047801 1047801 8388608 1 

noncomputable def Ns312p1273 := @Ns312p1272 1048576 (@Enclosure.Real.IsNear.recentre' qz196 Bool.false 339735524 33554432 32 33554432 84933881 8388608 1 1048576 (Ns312p1261 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns312p1274 := @Enclosure.Real.IsNear.recentre' qz199 Bool.false 926549173851643932555 1180591620717411303424 Ns312p1270 Ns312p296 26334111 33554432 101 16777216 (@Ns312p1271 Ns312p296 RS313to324.d47 (Ns312p1273 rfl rfl) rfl) 

noncomputable def Ns312p1275 := nat_lit 1024428276479862462691443241392041411457370775445422462187426561 

noncomputable def Ns312p1276 := nat_lit 231285972978633121544039527071950752307585493692523848487681 

noncomputable def Ns312p1277 := nat_lit 3072822257493630121831241645121980332867497155348882338865304321 

noncomputable def Ns312p1278 := BSN.cos_dyadic_bound_f 26334111 33554432 3 2 16777216 4410000 Ns312p1275 Ns312p463 Ns312p1276 Ns312p1277 Ns312p466 Ns312p1276 11870167 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 26334111) qz395 0 2 Ns312p1275 Ns312p463 Ns312p1276 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 26334111) (BSN.cosOddQ 33554432) 0 2 Ns312p1277 Ns312p466 Ns312p1276 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1279 := @Enclosure.Real.IsNear.inv_image qz197 11870167 16777216 28886701 4624220160000 23712597 23713017 16777216 (Ns312p1268 (@Ns312p1269 4410000 (Ns312p1274 rfl) (Enclosure.sfrac_false_div 26334111 33554432) (Ns312p1278 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns312p1280 := @Enclosure.Real.IsNear.recentre' qz198 Bool.false 7915166 16777216 

noncomputable abbrev qz200 := (@HMul.hMul Real Real Real qz349 qz346 qz504)

noncomputable def Ns312p1281 := @Enclosure.Real.IsNear.cos_image qz200 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 36221575)) qz368) Bool.true 36221575 33554432 

noncomputable def Ns312p1282 := nat_lit 10690721994257975296730246605 

noncomputable def Ns312p1283 := nat_lit 28292789756583821590230919995887 

noncomputable def Ns312p1284 := @Enclosure.Real.IsNear.recentre' qz200 Bool.true Ns312p1282 Ns312p454 Ns312p1283 

noncomputable abbrev qz201 := qz504

noncomputable def Ns312p1285 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz201 884279719003555 140737488355328 1 500000000000000 12089751426511 

noncomputable abbrev qz505 := (@HSub.hSub Real Real Real qz583 qz672 qz667)

noncomputable abbrev qz202 := qz505

noncomputable def Ns312p1286 := @Enclosure.Real.IsNear.subLit_tf qz202 qz29 7691704915407 70368744177664 5242109 4398046511104 1 16 

noncomputable abbrev qz506 := qz672

noncomputable abbrev qz203 := qz506

noncomputable def Ns312p1287 := @Enclosure.Real.IsNear.subLit_ff_n qz203 qz188 1097886935601 70368744177664 1047805 4398046511104 1047801 8388608 1 1048576 

noncomputable def Ns312p1288 := @Enclosure.Real.IsNear.mulLit_ff qz188 qz188 1047801 8388608 1 1048576 1047801 8388608 1 1048576 1097886935601 70368744177664 

noncomputable def Ns312p1289 := nat_lit 3668842421054149278073805402046812424684377116904026948087890625 

noncomputable def Ns312p1290 := nat_lit 2963047709607311148613064932951749141037149710742340087890625 

noncomputable def Ns312p1291 := nat_lit 11000601167743233211924190076274533775771057051290596164087890625 

noncomputable def Ns312p1292 := BSN.cos_dyadic_bound_f 36221575 33554432 3 2 16777216 4410000 Ns312p1289 Ns312p463 Ns312p1290 Ns312p1291 Ns312p466 Ns312p1290 7915166 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 36221575) qz395 0 2 Ns312p1289 Ns312p463 Ns312p1290 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 36221575) (BSN.cosOddQ 33554432) 0 2 Ns312p1291 Ns312p466 Ns312p1290 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1293 := @Ns312p1280 286218608 36993761280000 3957583 8388608 17888663 2312110080000 (@Ns312p1281 63 8388608 Bool.false 7915166 16777216 1 4410000 (@Ns312p1284 Ns312p457 36221575 33554432 63 8388608 (@Ns312p1285 70368744177664 5242109 4398046511104 Ns312p1282 Ns312p454 Ns312p1283 Ns312p457 RS313to324.d47 (@Ns312p1286 0 1 193436022824176 12089751426511 70368744177664 5242109 4398046511104 (@Ns312p1287 64522697387022483456 7691704915407 70368744177664 5242109 4398046511104 (@Ns312p1288 1047805 4398046511104 (Ns312p1273 rfl rfl) (Ns312p1273 rfl rfl) rfl) (Ns312p1273 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 36221575 33554432) (BSN.cos_neg_of_bound 36221575 33554432 Bool.false 7915166 16777216 1 4410000 (Ns312p1292 rfl rfl)) rfl rfl) 

noncomputable def Ns312p1294 := @Ns312p1259 460977290590925346641 Ns312p1181 (Ns312p1260 qz31 (@Enclosure.Real.IsNear.of_eq qz187 (@Inv.inv Real Real.instInv (Real.sqrt qz196)) Bool.false 10545189 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz195 (BSN.t_div_two_pi_nonneg qz186 644113 1000 qz189)) Ns312p1264) rfl) (@Ns312p1265 140737488355328 217754673615007 12930256742645760000 (BSN.correction_mk qz188 (BSN.cos_two_pi_p_ne_zero_mk qz186 644113 1000 10 qz189 rfl rfl (@BSN.floor_sqrt_eq_dec qz186 644113 1000 10 qz189 rfl rfl rfl))) (@Ns312p1266 8388608 3957583 8388608 17888663 2312110080000 93845401865481 140737488355328 217754673615007 12930256742645760000 (@Ns312p1267 8388608 (Ns312p1279 rfl rfl rfl rfl rfl) rfl) (Ns312p1293 rfl) rfl)) 

noncomputable def Ns312p1295 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz186) (hardyZApproximantRS₀ qz186) Bool.false 17903868070615419745715 4722366482869645213696 111677994611109900834641 Ns312p1181 (@Eq.refl Real (hardyZApproximantRS₀ qz186)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz186) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz186) qz186 10) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz187) (Zeta.RiemannSiegel.correction qz188))) Bool.false 17903868070615419745715 4722366482869645213696 111677994611109900834641 Ns312p1181 (BSN.hardyZApproximantRS₀_eq qz186 10 (@BSN.floor_sqrt_eq_dec qz186 644113 1000 10 qz189 rfl rfl rfl)) (@Ns312p1183 17903868070615419745715 4722366482869645213696 111677994611109900834641 Ns312p1181 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz186) qz186 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz186) qz186 10)) Bool.false 536985157 134217728 86013 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz186) qz186 10) (Ns312p1258 (Ns312p1257 rfl rfl rfl rfl) rfl rfl)) (Ns312p1294 rfl) rfl rfl)) 

theorem RS313to324.d60 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz186) Bool.false 17903868070615419745715 4722366482869645213696 111677994611109900834641 Ns312p1181 := Ns312p1295 

noncomputable def Ns312p1296 := nat_lit 162700282730118245253120000 

noncomputable def Ns312p1297 := nat_lit 167658737736876864230846889984 

noncomputable abbrev qz756 := (Enclosure.sfrac Bool.false 645470 1000)

noncomputable abbrev qz673 := qz756

noncomputable abbrev qz507 := qz673

noncomputable abbrev qz204 := qz507

noncomputable abbrev qz205 := qz350

noncomputable abbrev qz757 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 645470 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz674 := qz757

noncomputable abbrev qz508 := qz674

noncomputable abbrev qz206 := qz508

noncomputable abbrev qz207 := qz352

noncomputable abbrev qz758 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 645470 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz675 := qz758

noncomputable abbrev qz509 := qz675

noncomputable abbrev qz208 := qz509

noncomputable abbrev qz676 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz205 qz206 qz207))

noncomputable def Ns312p1298 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz204) qz204 10) (@HMul.hMul Real Real Real qz5 qz676 (Zeta.RiemannSiegel.correction qz208)) 256658019 134217728 172381 134217728 120361033277301432627 590295810358705651712 958666337935325785159 Ns312p1296 Ns312p1297 

noncomputable def Ns312p1299 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.cos BSN.quadSignPos 9 10 645470 1000 200 268435456 134217728 4503599627370496 Bool.false 314556335477 2535 618095470 62 84886744 8 

noncomputable def Ns312p1300 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 645470 1000 108 156 268435456 134217728 4503599627370496 Bool.false 314556335477 2535 

noncomputable def Ns312p1301 := Ns312p1300 558195838 62 94906264 8 589812974 62 89478488 8 Bool.true 423835327 129665 Bool.true 203329824 Bool.true 371686041 14148475504056880 1 Bool.false 195040298 Bool.false Bool.false 49683262 Bool.false Bool.true 338317082 

noncomputable def Ns312p1302 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 645470 1000 9 53 268435456 134217728 4503599627370496 Bool.false 314556335477 2535 

noncomputable def Ns312p1303 := Ns312p1302 480971758 62 109588312 8 522351262 62 101459064 8 Bool.true 240671574 96189 Bool.false 308577986 Bool.true 257889908 14148475504056880 1 Bool.false 244968021 Bool.true Bool.false 220010047 Bool.true Bool.true 423835327 

noncomputable def Ns312p1304 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 645470 1000 176 84 268435456 134217728 4503599627370496 Bool.false 314556335477 2535 

noncomputable def Ns312p1305 := Ns312p1304 372130544 61 134217720 8 432030192 61 120047984 16 Bool.true 418176092 56464 Bool.false 145525866 Bool.false 274583472 14148475504056880 1 Bool.false 229945473 Bool.false Bool.false 139825333 Bool.false Bool.true 240671574 

noncomputable def Ns312p1306 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 645470 1000 461 294 268435456 134217728 4503599627370496 Bool.false 314556335477 2535 

noncomputable def Ns312p1307 := Ns312p1306 186065264 61 189812528 16 294906480 61 154981288 8 Bool.true 268435432 2605 Bool.false 72715092 Bool.false 235765921 14148475504056880 1 Bool.false 71829060 Bool.true Bool.false 171386153 Bool.true Bool.true 418176092 

noncomputable def Ns312p1308 := nat_lit 85873270775370829815533639068667036266465612577651 

noncomputable def Ns312p1309 := nat_lit 73282359942845494056813305291583902959691366400 

noncomputable def Ns312p1310 := nat_lit 53780174586792144948632336000000000 

noncomputable def Ns312p1311 := nat_lit 208280994066983265772743451667520000000 

noncomputable abbrev qz759 := (@Eq.refl Real (Enclosure.sfrac Bool.false 645470 1000))

noncomputable abbrev qz677 := qz759

noncomputable abbrev qz510 := qz677

noncomputable abbrev qz209 := qz510

noncomputable def Ns312p1312 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz204 645470 1000 1666527083600 16000000 1290940 4000 2000 Ns312p1310 Ns312p1311 qz209 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns312p1313 := nat_lit 27479446648118665540970764501973451605268996024848320000000 

noncomputable abbrev qz678 := (@HSub.hSub Real Real Real qz715 qz716 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz717 (@Nat.cast Real Real.instNatCast 1290940))))

noncomputable abbrev qz511 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 645470 4000) (Real.log (Enclosure.sfrac Bool.false 1666527083600 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz678))

noncomputable abbrev qz679 := (Enclosure.sfrac Bool.false 645470 2000)

noncomputable abbrev qz210 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz511 qz679) (@HMul.hMul Real Real Real qz349 qz679 (Real.log Real.pi)))

noncomputable def Ns312p1314 := @Enclosure.Real.IsNear.addLit_ft_p qz210 (Enclosure.sfrac Bool.true Ns312p1310 Ns312p1311) 131934518683882487791 112589990684262400 1705131855215217743 180633600000000000000000 Ns312p1310 Ns312p1311 0 1 Ns312p1313 

noncomputable def Ns312p1315 := nat_lit 885397567126212886514787942400 

noncomputable abbrev qz211 := (@HSub.hSub Real Real Real qz355 qz511 qz679)

noncomputable def Ns312p1316 := @Enclosure.Real.IsNear.subLit_ff_p qz211 (@HMul.hMul Real Real Real qz5 qz679 (Real.log Real.pi)) 173530260083060244463 112589990684262400 408418977732841 88200000000000000000 2479299390267 6710886400 64547 13421772800 Ns312p1315 131934518683882487791 112589990684262400 

noncomputable abbrev qz212 := qz511

noncomputable def Ns312p1317 := @Enclosure.Real.IsNear.subLit_ff_p qz212 qz679 209866990726545670127 112589990684262400 408418977732841 88200000000000000000 645470 2000 0 1 347060520166120488926000 173530260083060244463 112589990684262400 408418977732841 88200000000000000000 

noncomputable def Ns312p1318 := nat_lit 472578450616719209789322253614186496 

noncomputable def Ns312p1319 := nat_lit 55870089433007361301151744 

noncomputable def Ns312p1320 := nat_lit 21687211844509110063966299945598233138371085977266455583477664653181905838509345799207406206874252418174669637475895679453715496960000000000000000000000000 

noncomputable def Ns312p1321 := nat_lit 386558315649055804862070891628235829803743174415998912610105898272759211370502126271380364799665137753559009890973936478649843712000000000000000000000000 

noncomputable def Ns312p1322 := nat_lit 32230991911844743498281281848050633378806698349807853469601794833379959327833551624572692832127985238592115529777854545920000000000000000000000000 

noncomputable def Ns312p1323 := BSN.log_dyadic_bound 617951083600 2715103083600 7 6 Ns312p1320 134217728 35280000 Ns312p1321 Ns312p1322 62184256 3333054167200 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 617951083600) (BSN.artanhQ 2715103083600) 0 6 Ns312p1321 Ns312p1320 Ns312p1322 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz512 := (Real.log (Enclosure.sfrac Bool.false 1666527083600 16000000))

noncomputable def Ns312p1324 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 645470 4000) qz512 645470 4000 0 1 3252067220921591 281474976710656 781250441 27562500000000000 209911182908825934277 112589990684262400 7203910316461 1575000000000000000 (Enclosure.Real.IsNear.const Bool.false 645470 4000) (BSN.isNear_log_sfrac 1666527083600 16000000 3252067220921591 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1666527083600) qz358)) Bool.false Ns312p1319 Ns312p99 1000000564480000 35280000000000000000000 3252067220921591 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1666527083600 16000000 16 3333054167200 2097152000000 62184256 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns312p1323 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns312p1325 := BSN.arctan_dyadic_bound_f 1000 1290940 1 0 16777216 4410000 0 1 1 0 1 1 12996 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1290940) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1290940) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns312p1326 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1290940))) 884279719003555 562949953421312 1 2000000000000000 12996 16777216 1 4410000 14828435752547283632128 883843645605283 562949953421312 200000000441 882000000000000000 qz15 (Ns312p1325 rfl) rfl rfl 

noncomputable abbrev qz513 := (@HMul.hMul Real Real Real qz579 qz584 qz678)

noncomputable abbrev qz213 := qz513

noncomputable abbrev qz514 := qz678

noncomputable abbrev qz214 := qz514

noncomputable def Ns312p1327 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 645470 4000) qz512) qz213 209911182908825934277 112589990684262400 7203910316461 1575000000000000000 883843645605283 2251799813685248 200000000441 3528000000000000000 Ns312p1318 209866990726545670127 112589990684262400 408418977732841 88200000000000000000 (Ns312p1324 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz214 1 4 0 1 883843645605283 562949953421312 200000000441 882000000000000000 883843645605283 2251799813685248 200000000441 3528000000000000000 qz366 Ns312p1326 rfl) 

noncomputable def Ns312p1328 := @Ns312p1314 Ns312p1308 Ns312p1309 1705131855215217743 180633600000000000000000 (@Ns312p1316 1705131855215217743 180633600000000000000000 (Ns312p1317 (Ns312p1327 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 645470 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz679 (Real.log Real.pi) 645470 2000 0 1 38410761 33554432 1 67108864 2479299390267 6710886400 64547 13421772800 (Enclosure.Real.IsNear.const Bool.false 645470 2000) RS313to324.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns312p1310 Ns312p1311) 

noncomputable def Ns312p1329 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz204) Bool.false Ns312p1308 Ns312p1309 1705131855215217743 180633600000000000000000 19659770967 16777216 159 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz204) (@HAdd.hAdd Real Real Real qz367 qz210 (Enclosure.sfrac Bool.true Ns312p1310 Ns312p1311)) Bool.false Ns312p1308 Ns312p1309 1705131855215217743 180633600000000000000000 Ns312p1312 (Ns312p1328 rfl rfl)) 

noncomputable def Ns312p1330 := nat_lit 3796997578383733632794624 

noncomputable def Ns312p1331 := nat_lit 3507298898551432838850678434346632563460677124005241316405221432060711471951292864700821918110745123570651807044474734274693283866214400000 

noncomputable def Ns312p1332 := nat_lit 2495089814515206624333614395864618270577280827684544559248942558142787878128492573810790672965970493886290528573436461056000000000000 

noncomputable def Ns312p1333 := nat_lit 17514725107518032513052562552746402455999462527511242865289815926041456748405398758510412108561392146855204813771716114310123667587072000000 

noncomputable def Ns312p1334 := BSN.sin_dyadic_bound_f 107917161880 68719476736 4 3 33554432 8828614 Ns312p1331 Ns312p239 Ns312p1332 Ns312p1333 Ns312p242 Ns312p1332 33554429 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107917161880) qz602 0 3 Ns312p1331 Ns312p239 Ns312p1332 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107917161880) qz603 0 3 Ns312p1333 Ns312p242 Ns312p1332 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1335 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz204) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 19659770967) qz378) Bool.false 19659770967 16777216 159 16777216 Bool.true 33554429 33554432 1 4410000 (Ns312p1329 rfl) (Enclosure.sfrac_false_div 19659770967 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 19659770967) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns312p1330) qz614) 226375608064910080 72057594037927936 Bool.false 33554429 33554432 186 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q1 19659770967 16777216 226375608064910080 72057594037927936 186 Ns312p1330 Ns312p394 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554429 33554432 Ns312p1330 Ns312p394 107917161880 68719476736 8828614 8820000 (Ns312p1334 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns312p1336 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz204) Bool.false Ns312p1308 Ns312p1309 1705131855215217743 180633600000000000000000 314556335477 268435456 2535 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz204) (@HAdd.hAdd Real Real Real qz367 qz210 (Enclosure.sfrac Bool.true Ns312p1310 Ns312p1311)) Bool.false Ns312p1308 Ns312p1309 1705131855215217743 180633600000000000000000 Ns312p1312 (Ns312p1328 rfl rfl)) 

noncomputable def Ns312p1337 := Ns312p1307 56464 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 461 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 71829060 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 294 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 171386153 268435456) qz209 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 1) Bool.true 33554429 33554432 44872951 4624220160000 268435432 268435456 2605 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz204)) Bool.true 33554429 33554432 44872951 4624220160000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz204) qz204) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz204)) Bool.true 33554429 33554432 717967216 73987522560000 33554429 33554432 44872951 4624220160000 (Ns312p1335 rfl rfl) rfl)) rfl) (Ns312p1336 rfl) RS313to324.d7 

noncomputable def Ns312p1338 := nat_lit 27957493443548526112179663319296 

noncomputable def Ns312p1339 := BSN.sin_dyadic_bound_f 72715092 268435456 2 1 268435456 134217728 Ns312p1338 Ns312p115 Ns312p1338 Ns312p1338 Ns312p116 Ns312p1338 71829060 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 72715092) qz370 0 1 Ns312p1338 Ns312p115 Ns312p1338 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 72715092) qz371 0 1 Ns312p1338 Ns312p116 Ns312p1338 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1340 := nat_lit 26961665577882689128290628661008693686939992911318528589288757367338241 

noncomputable def Ns312p1341 := nat_lit 9546589279613364008518225772115576031861434225101367866635235554561 

noncomputable def Ns312p1342 := nat_lit 80865903555088840656854849531481849908756255865505383032133001630905601 

noncomputable def Ns312p1343 := BSN.cos_dyadic_bound_f 235765921 268435456 3 2 268435456 134217728 Ns312p1340 Ns312p123 Ns312p1341 Ns312p1342 Ns312p126 Ns312p1341 171386153 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 235765921) qz372 0 2 Ns312p1340 Ns312p123 Ns312p1341 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 235765921) qz373 0 2 Ns312p1342 Ns312p126 Ns312p1341 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1344 := nat_lit 3912477872818084717165124073380522903438753488060849567582954312786176 

noncomputable def Ns312p1345 := nat_lit 201150695729700764054040876622742162148191057525484055154166948096 

noncomputable def Ns312p1346 := nat_lit 11737031317062794749967264138388323225991964082067497734638554604462336 

noncomputable def Ns312p1347 := BSN.cos_dyadic_bound_f 145525866 268435456 3 2 268435456 134217728 Ns312p1344 Ns312p123 Ns312p1345 Ns312p1346 Ns312p126 Ns312p1345 229945473 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 145525866) qz372 0 2 Ns312p1344 Ns312p123 Ns312p1345 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 145525866) qz373 0 2 Ns312p1346 Ns312p126 Ns312p1345 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1348 := nat_lit 3060731767875189611257519413230482860611267006929187075980088614322231048323299338114941014781243585091076096 

noncomputable def Ns312p1349 := nat_lit 183693042092428379023666581059851819940216696660668188283263782552548447281621178960574644906849468416 

noncomputable def Ns312p1350 := nat_lit 18560376699173761716437254249430708307037026172564651473002344296045953711800758121305618051452479659017502720 

noncomputable def Ns312p1351 := BSN.cos_dyadic_bound_f 274583472 268435456 4 3 268435456 134217728 Ns312p1348 Ns312p136 Ns312p1349 Ns312p1350 Ns312p139 Ns312p1349 139825333 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 274583472) qz372 0 3 Ns312p1348 Ns312p136 Ns312p1349 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 274583472) qz373 0 3 Ns312p1350 Ns312p139 Ns312p1349 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1352 := Ns312p1305 96189 BSN.abs_quadSignPos (BSN.cos_quad_nat0 176 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 229945473 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 84 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 139825333 268435456) qz209 rfl rfl (Ns312p1337 RS313to324.d9 RS313to324.d11 RS313to324.d13 RS313to324.d17 (Ns312p1339 rfl rfl) (Ns312p1343 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns312p1336 rfl) RS313to324.d19 RS313to324.d21 RS313to324.d23 RS313to324.d25 RS313to324.d17 (Ns312p1347 rfl rfl) (Ns312p1351 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns312p1353 := nat_lit 142446497537020454846376066187882857735559396425804904099280325463179520 

noncomputable def Ns312p1354 := nat_lit 82209029560030421935024155350925129425415494459529049560732249293056 

noncomputable def Ns312p1355 := nat_lit 372941059882432570581185372335791701002633460790840273227397762095186176 

noncomputable def Ns312p1356 := BSN.sin_dyadic_bound_f 308577986 268435456 3 2 268435456 134217728 Ns312p1353 Ns312p259 Ns312p1354 Ns312p1355 Ns312p262 Ns312p1354 244968021 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 308577986) qz370 0 2 Ns312p1353 Ns312p259 Ns312p1354 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 308577986) qz371 0 2 Ns312p1355 Ns312p262 Ns312p1354 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1357 := nat_lit 69470594637965912405984181190219393859154551950501646202038704945561600 

noncomputable def Ns312p1358 := nat_lit 19564771400893367093908242801869840816443907821806127600915269615616 

noncomputable def Ns312p1359 := nat_lit 181915119183833086087997004057466813698368631638649958703509412039950336 

noncomputable def Ns312p1360 := BSN.sin_dyadic_bound_f 257889908 268435456 3 2 268435456 134217728 Ns312p1357 Ns312p259 Ns312p1358 Ns312p1359 Ns312p262 Ns312p1358 220010047 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 257889908) qz370 0 2 Ns312p1357 Ns312p259 Ns312p1358 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 257889908) qz371 0 2 Ns312p1359 Ns312p262 Ns312p1358 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1361 := Ns312p1303 129665 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 9 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 244968021 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 53 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 220010047 268435456) qz209 rfl rfl (Ns312p1352 rfl rfl) (Ns312p1336 rfl) RS313to324.d27 RS313to324.d29 RS313to324.d31 RS313to324.d33 RS313to324.d17 (Ns312p1356 rfl rfl) (Ns312p1360 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p1362 := nat_lit 14912766737920589846254473145973448376576473888280049344390279049773056 

noncomputable def Ns312p1363 := nat_lit 2921518749563958036839955003481193525788082456155921937949341515776 

noncomputable def Ns312p1364 := nat_lit 44732457176262641622689739527913382742677845499927836189294938466287616 

noncomputable def Ns312p1365 := BSN.cos_dyadic_bound_f 203329824 268435456 3 2 268435456 134217728 Ns312p1362 Ns312p123 Ns312p1363 Ns312p1364 Ns312p126 Ns312p1363 195040298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 203329824) qz372 0 2 Ns312p1362 Ns312p123 Ns312p1363 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 203329824) qz373 0 2 Ns312p1364 Ns312p126 Ns312p1363 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1366 := nat_lit 10291986854541574124467139733576044611314744741354919877530119065005937142549302671609303306093882149004614561 

noncomputable def Ns312p1367 := nat_lit 6952084033772432024998782908310517106717209582356356283845228098952966110476940967985518527494600498081 

noncomputable def Ns312p1368 := nat_lit 62347143273688768666609840218925410784277618793634794931364265607554463460023573303499851895261959484658129825 

noncomputable def Ns312p1369 := BSN.cos_dyadic_bound_f 371686041 268435456 4 3 268435456 134217728 Ns312p1366 Ns312p136 Ns312p1367 Ns312p1368 Ns312p139 Ns312p1367 49683262 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 371686041) qz372 0 3 Ns312p1366 Ns312p136 Ns312p1367 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 371686041) qz373 0 3 Ns312p1368 Ns312p139 Ns312p1367 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1370 := Ns312p1301 158914 BSN.abs_quadSignPos (BSN.cos_quad_nat0 108 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 195040298 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 156 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 49683262 268435456) qz209 rfl rfl (Ns312p1361 rfl) (Ns312p1336 rfl) RS313to324.d35 RS313to324.d37 RS313to324.d39 RS313to324.d41 RS313to324.d17 (Ns312p1365 rfl rfl) (Ns312p1369 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p1371 := nat_lit 30413331248762964861463658410000 

noncomputable def Ns312p1372 := BSN.cos_dyadic_bound_f 74261890 268435456 2 1 268435456 134217728 Ns312p1371 Ns312p119 Ns312p1371 Ns312p1371 Ns312p120 Ns312p1371 258228634 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 74261890) qz372 0 1 Ns312p1371 Ns312p119 Ns312p1371 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 74261890) qz373 0 1 Ns312p1371 Ns312p120 Ns312p1371 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1373 := Ns312p1299 Bool.true 338317082 158914 Bool.true 74261890 14148475504056880 1 Bool.false 258228634 Bool.false Bool.true 256658019 172381 BSN.abs_quadSignPos qz374 (BSN.sfrac_eq_quadSignPos_mul Bool.false 258228634 268435456) qz209 rfl (Ns312p1370 rfl) (Ns312p1336 rfl) RS313to324.d43 RS313to324.d45 RS313to324.d17 (Ns312p1372 rfl rfl) rfl 

noncomputable def Ns312p1374 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 10) 256658019 268435456 172381 268435456 256658019 268435456 172381 268435456 137792224732643328 256658019 134217728 172381 134217728 (Ns312p1373 rfl rfl rfl rfl) 

noncomputable def Ns312p1375 := @Enclosure.Real.IsNear.mulLit_ff qz676 (Zeta.RiemannSiegel.correction qz208) 5269821 16777216 1 16777216 22839681514287 35184372088832 5647552888871 303052892405760000 120361033277301432627 590295810358705651712 

noncomputable abbrev qz680 := (@HPow.hPow Real Real Real qz205 qz206 qz207)

noncomputable def Ns312p1376 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz680 1 1 0 1 5269821 16777216 1 16777216 5269821 16777216 1 16777216 

noncomputable def Ns312p1377 := @Enclosure.Real.IsNear.sqrt_image qz206 344703765091 3355443200 64547 3355443200 170046588 170046621 16777216 (@Enclosure.Real.IsNear.of_eq qz206 (@HMul.hMul Real Real Real qz5 qz204 qz3) Bool.false 344703765091 3355443200 64547 3355443200 (BSN.t_div_two_pi_mk qz204 645470 1000 qz209) (@Enclosure.Real.IsNear.mulLit_ff qz204 qz3 645470 1000 0 1 5340353 33554432 1 33554432 344703765091 3355443200 64547 3355443200 (Enclosure.Real.IsNear.const Bool.false 645470 1000) RS313to324.d48 rfl)) 

noncomputable abbrev qz760 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 645470 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz681 := qz760

noncomputable abbrev qz515 := qz681

noncomputable abbrev qz215 := qz515

noncomputable def Ns312p1378 := @Enclosure.Real.IsNear.sqrt_image qz215 340093209 33554432 33 33554432 53412623 53412629 16777216 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 340093209 33554432 33 33554432 340093209 33554432 33 33554432 (Ns312p1377 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns312p1379 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz215) 26706313 8388608 3 16777216 5269820 5269822 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz215) Bool.false 106825252 33554432 6 33554432 26706313 8388608 3 16777216 (Ns312p1378 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns312p1380 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 10539642 33554432 2 33554432 5269821 16777216 1 16777216 (Ns312p1379 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz216 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz509))

noncomputable abbrev qz682 := (@HMul.hMul Real Real Real qz711 qz758 qz758)

noncomputable abbrev qz516 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz682 qz675) qz594)

noncomputable abbrev qz217 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz516))

noncomputable def Ns312p1381 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz208) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz216) qz217) Bool.false 22839681514287 

noncomputable def Ns312p1382 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz216) qz217 25472777 16777216 249 

noncomputable def Ns312p1383 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz216) Bool.false 50945554 33554432 498 33554432 25472777 16777216 249 

noncomputable def Ns312p1384 := @Enclosure.Real.IsNear.recentre' qz216 Bool.false 11050031 16777216 59427152 9248440320000 11050031 16777216 3714197 578027520000 

noncomputable abbrev qz218 := (@HMul.hMul Real Real Real qz349 qz346 qz509)

noncomputable def Ns312p1385 := @Enclosure.Real.IsNear.cos_image qz218 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3572689) qz595) Bool.false 3572689 4194304 13 2097152 Bool.false 11050031 16777216 1 

noncomputable def Ns312p1386 := nat_lit 890540488537528158996844199 

noncomputable def Ns312p1387 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz208 884279719003555 140737488355328 1 500000000000000 4548889 33554432 33 33554432 4022490286698362300395 4722366482869645213696 Ns312p1386 

noncomputable def Ns312p1388 := @Enclosure.Real.IsNear.subLit_ff_p qz215 qz1 340093209 33554432 33 33554432 10 1 0 1 4548889 4548889 33554432 33 

noncomputable def Ns312p1389 := @Ns312p1388 33554432 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 340093209 33554432 33 33554432 340093209 33554432 33 33554432 (Ns312p1377 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns312p1390 := @Enclosure.Real.IsNear.recentre' qz218 Bool.false 4022490286698362300395 4722366482869645213696 Ns312p1386 Ns312p796 3572689 4194304 13 2097152 (@Ns312p1387 Ns312p796 RS313to324.d47 (Ns312p1389 rfl rfl) rfl) 

noncomputable def Ns312p1391 := nat_lit 84735582059547093543140150056791324221142515039979346561 

noncomputable def Ns312p1392 := nat_lit 26543714812263988311287153876924764562222102695025281 

noncomputable def Ns312p1393 := nat_lit 254153658749016752652797875862620123134303100914547989121 

noncomputable def Ns312p1394 := BSN.cos_dyadic_bound_f 3572689 4194304 3 2 16777216 4410000 Ns312p1391 Ns312p193 Ns312p1392 Ns312p1393 Ns312p196 Ns312p1392 11050031 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3572689) (BSN.cosEvenQ 4194304) 0 2 Ns312p1391 Ns312p193 Ns312p1392 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3572689) (BSN.cosOddQ 4194304) 0 2 Ns312p1393 Ns312p196 Ns312p1392 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1395 := @Enclosure.Real.IsNear.inv_image qz216 11050031 16777216 3714197 578027520000 25472528 25473026 16777216 (Ns312p1384 (@Ns312p1385 4410000 (Ns312p1390 rfl) (Enclosure.sfrac_false_div 3572689 4194304) (Ns312p1394 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns312p1396 := @Enclosure.Real.IsNear.recentre' qz217 Bool.false 7173048 16777216 

noncomputable abbrev qz219 := (@HMul.hMul Real Real Real qz349 qz346 qz516)

noncomputable def Ns312p1397 := @Enclosure.Real.IsNear.cos_image qz219 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 591931)) (@Nat.cast Real Real.instNatCast 524288)) Bool.true 591931 524288 

noncomputable def Ns312p1398 := nat_lit 178900168305969444615653685005 

noncomputable def Ns312p1399 := nat_lit 7596709863702517683606381830078369 

noncomputable def Ns312p1400 := @Enclosure.Real.IsNear.recentre' qz219 Bool.true Ns312p1398 Ns312p809 Ns312p1399 

noncomputable abbrev qz220 := qz516

noncomputable def Ns312p1401 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz220 884279719003555 140737488355328 1 500000000000000 202311739669391 

noncomputable abbrev qz517 := (@HSub.hSub Real Real Real qz583 qz682 qz675)

noncomputable abbrev qz221 := qz517

noncomputable def Ns312p1402 := @Enclosure.Real.IsNear.subLit_tf qz221 qz29 131942995491727 1125899906842624 1407524019 1125899906842624 1 16 

noncomputable abbrev qz518 := qz682

noncomputable abbrev qz222 := qz518

noncomputable def Ns312p1403 := @Enclosure.Real.IsNear.subLit_ff_n qz222 qz208 20692391134321 1125899906842624 300227763 1125899906842624 4548889 33554432 33 33554432 

noncomputable def Ns312p1404 := @Enclosure.Real.IsNear.mulLit_ff qz208 qz208 4548889 33554432 33 33554432 4548889 33554432 33 33554432 20692391134321 1125899906842624 

noncomputable def Ns312p1405 := nat_lit 15598869276912337410028510905919020305577577290721 

noncomputable def Ns312p1406 := nat_lit 230186507879617209617080361152814575595809375518720 

noncomputable def Ns312p1407 := nat_lit 15071923458354126581054705792939003070464924641 

noncomputable def Ns312p1408 := nat_lit 46766463983820303976923423306171182910591802022881 

noncomputable def Ns312p1409 := nat_lit 10358392854582774432768616251876655901811421898342400 

noncomputable def Ns312p1410 := BSN.cos_dyadic_bound_f 591931 524288 3 2 16777216 4410000 Ns312p1405 Ns312p1406 Ns312p1407 Ns312p1408 Ns312p1409 Ns312p1407 7173048 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 591931) (BSN.cosEvenQ 524288) 0 2 Ns312p1405 Ns312p1406 Ns312p1407 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 591931) (BSN.cosOddQ 524288) 0 2 Ns312p1408 Ns312p1409 Ns312p1407 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1411 := @Ns312p1396 149724304 18496880640000 896631 2097152 9357769 1156055040000 (@Ns312p1397 33 4194304 Bool.false 7173048 16777216 1 4410000 (@Ns312p1400 Ns312p1051 591931 524288 33 4194304 (@Ns312p1401 1125899906842624 1407524019 1125899906842624 Ns312p1398 Ns312p809 Ns312p1399 Ns312p1051 RS313to324.d47 (@Ns312p1402 0 1 3236987834710256 202311739669391 1125899906842624 1407524019 1125899906842624 (@Ns312p1403 4427272270103460184064 131942995491727 1125899906842624 1407524019 1125899906842624 (@Ns312p1404 300227763 1125899906842624 (Ns312p1389 rfl rfl) (Ns312p1389 rfl rfl) rfl) (Ns312p1389 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 591931 524288) (BSN.cos_neg_of_bound 591931 524288 Bool.false 7173048 16777216 1 4410000 (Ns312p1410 rfl rfl)) rfl rfl) 

noncomputable def Ns312p1412 := @Ns312p1375 958666337935325785159 Ns312p1296 (Ns312p1376 qz31 (@Enclosure.Real.IsNear.of_eq qz680 (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 5269821 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz206 (BSN.t_div_two_pi_nonneg qz204 645470 1000 qz209)) Ns312p1380) rfl) (@Ns312p1381 35184372088832 5647552888871 303052892405760000 (BSN.correction_mk qz208 (BSN.cos_two_pi_p_ne_zero_mk qz204 645470 1000 10 qz209 rfl rfl (@BSN.floor_sqrt_eq_dec qz204 645470 1000 10 qz209 rfl rfl rfl))) (@Ns312p1382 16777216 896631 2097152 9357769 1156055040000 22839681514287 35184372088832 5647552888871 303052892405760000 (@Ns312p1383 16777216 (Ns312p1395 rfl rfl rfl rfl rfl) rfl) (Ns312p1411 rfl) rfl)) 

noncomputable def Ns312p1413 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz204) (hardyZApproximantRS₀ qz204) Bool.true 1249154938287115575603 590295810358705651712 209920908921124584025159 Ns312p1296 (@Eq.refl Real (hardyZApproximantRS₀ qz204)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz204) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz204) qz204 10) (@HMul.hMul Real Real Real qz5 qz676 (Zeta.RiemannSiegel.correction qz208))) Bool.true 1249154938287115575603 590295810358705651712 209920908921124584025159 Ns312p1296 (BSN.hardyZApproximantRS₀_eq qz204 10 (@BSN.floor_sqrt_eq_dec qz204 645470 1000 10 qz209 rfl rfl rfl)) (@Ns312p1298 1249154938287115575603 590295810358705651712 209920908921124584025159 Ns312p1296 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz204) qz204 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 10)) Bool.true 256658019 134217728 172381 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz204) qz204 10) (Ns312p1374 (Ns312p1373 rfl rfl rfl rfl) rfl rfl)) (Ns312p1412 rfl) rfl rfl)) 

theorem RS313to324.d61 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz204) Bool.true 1249154938287115575603 590295810358705651712 209920908921124584025159 Ns312p1296 := Ns312p1413 

noncomputable def Ns312p1414 := nat_lit 32575032585323426481075912704 

noncomputable abbrev qz761 := (Enclosure.sfrac Bool.false 646826 1000)

noncomputable abbrev qz683 := qz761

noncomputable abbrev qz519 := qz683

noncomputable abbrev qz223 := qz519

noncomputable abbrev qz762 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 646826 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz684 := qz762

noncomputable abbrev qz520 := qz684

noncomputable abbrev qz224 := qz520

noncomputable abbrev qz763 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 646826 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz685 := qz763

noncomputable abbrev qz521 := qz685

noncomputable abbrev qz225 := qz521

noncomputable abbrev qz686 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz205 qz224 qz207))

noncomputable def Ns312p1415 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (@HMul.hMul Real Real Real qz5 qz686 (Zeta.RiemannSiegel.correction qz225)) 61843667 33554432 172737 134217728 117153672635421645475 590295810358705651712 540149663317650571093 Ns312p1181 Ns312p1414 

noncomputable def Ns312p1416 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos BSN.quadSignPos 9 10 646826 1000 200 268435456 134217728 4503599627370496 Bool.false 315399565491 2540 618095470 62 84886744 8 

noncomputable def Ns312p1417 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 646826 1000 108 156 268435456 134217728 4503599627370496 Bool.false 315399565491 2540 

noncomputable def Ns312p1418 := Ns312p1417 558195838 62 94906264 8 589812974 62 89478488 8 Bool.false 48745563 129931 Bool.true 117013366 Bool.true 328242419 14148475504056880 1 Bool.false 243333172 Bool.false Bool.false 91540925 Bool.false Bool.false 165290472 

noncomputable def Ns312p1419 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 646826 1000 10 53 268435456 134217728 4503599627370496 Bool.false 315399565491 2540 

noncomputable def Ns312p1420 := Ns312p1419 480971758 62 109588312 8 522351262 62 101459064 8 Bool.false 198614481 96385 Bool.false 77952868 Bool.true 122968205 14148475504056880 1 Bool.false 257196132 Bool.true Bool.false 118712323 Bool.true Bool.false 48745563 

noncomputable def Ns312p1421 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 646826 1000 177 85 268435456 134217728 4503599627370496 Bool.false 315399565491 2540 

noncomputable def Ns312p1422 := Ns312p1421 372130544 61 134217720 8 432030192 61 120047984 16 Bool.false 277538499 56577 Bool.false 62489434 Bool.false 110323117 14148475504056880 1 Bool.false 61926559 Bool.true Bool.false 107243476 Bool.true Bool.false 198614481 

noncomputable def Ns312p1423 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 646826 1000 462 295 268435456 134217728 4503599627370496 Bool.false 315399565491 2540 

noncomputable def Ns312p1424 := Ns312p1423 186065264 61 189812528 16 294906480 61 154981288 8 Bool.false 268435384 2605 Bool.false 241983179 Bool.false 257445319 14148475504056880 1 Bool.false 166555486 Bool.true Bool.false 219755025 Bool.false Bool.false 277538499 

noncomputable def Ns312p1425 := nat_lit 272482814550293353153909238707236542816095256098593817 

noncomputable def Ns312p1426 := nat_lit 231909160882762480941855859652128678867091985530880 

noncomputable def Ns312p1427 := nat_lit 54347458280914476621324543380480000 

noncomputable def Ns312p1428 := nat_lit 210920153115478097735700302702870138880 

noncomputable abbrev qz764 := (@Eq.refl Real (Enclosure.sfrac Bool.false 646826 1000))

noncomputable abbrev qz687 := qz764

noncomputable abbrev qz522 := qz687

noncomputable abbrev qz226 := qz522

noncomputable def Ns312p1429 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz223 646826 1000 1673536497104 16000000 1293652 4000 2000 Ns312p1427 Ns312p1428 qz226 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns312p1430 := nat_lit 5580448041990007872592061208724204396873630844899201372160 

noncomputable abbrev qz688 := (@HSub.hSub Real Real Real qz715 qz716 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz717 (@Nat.cast Real Real.instNatCast 1293652))))

noncomputable abbrev qz523 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 646826 4000) (Real.log (Enclosure.sfrac Bool.false 1673536497104 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz688))

noncomputable abbrev qz689 := (Enclosure.sfrac Bool.false 646826 2000)

noncomputable abbrev qz227 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz523 qz689) (@HMul.hMul Real Real Real qz349 qz689 (Real.log Real.pi)))

noncomputable def Ns312p1431 := @Enclosure.Real.IsNear.addLit_ft_p qz227 (Enclosure.sfrac Bool.true Ns312p1427 Ns312p1428) 26457638984979753757 22517998136852480 8543462375799090697 903168000000000000000000 Ns312p1427 Ns312p1428 0 1 Ns312p1430 

noncomputable def Ns312p1432 := nat_lit 22194276205051304220400025600000 

noncomputable abbrev qz228 := (@HSub.hSub Real Real Real qz355 qz523 qz689)

noncomputable def Ns312p1433 := @Enclosure.Real.IsNear.subLit_ff_p qz228 (@HMul.hMul Real Real Real qz5 qz689 (Real.log Real.pi)) 869856602200249120213 562949953421312000 2046332391056189 441000000000000000000 12422539447293 33554432000 323413 67108864000 Ns312p1432 26457638984979753757 22517998136852480 

noncomputable def Ns312p1434 := nat_lit 1739713204400498240426000 

noncomputable abbrev qz229 := qz523

noncomputable def Ns312p1435 := @Enclosure.Real.IsNear.subLit_ff_p qz229 qz689 1051921935486095898069 562949953421312000 2046332391056189 441000000000000000000 646826 2000 0 1 Ns312p1434 869856602200249120213 562949953421312000 2046332391056189 441000000000000000000 

noncomputable def Ns312p1436 := nat_lit 2368717618339016209819817503056986112 

noncomputable def Ns312p1437 := nat_lit 55890385751404836387028992 

noncomputable def Ns312p1438 := nat_lit 22368696580466251506386020271020905318803216559670349501671932667647712322563440069107423046740235993914840767627030115862900583102478271685977146822492160 

noncomputable def Ns312p1439 := nat_lit 405935589623328335383667748182215204511949672977075218594056805262499651748889890341066242991173214848371870508904771887151431280668034439887520008241152 

noncomputable def Ns312p1440 := nat_lit 36902458312786269603432564014726636996490222421210989621953328909970505650456370800889223674560385986511998350080207561109058354400776035835576320 

noncomputable def Ns312p1441 := BSN.log_dyadic_bound 624960497104 2722112497104 7 6 Ns312p1438 134217728 35280000 Ns312p1439 Ns312p1440 62747592 3347072994208 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 624960497104) (BSN.artanhQ 2722112497104) 0 6 Ns312p1439 Ns312p1438 Ns312p1440 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz524 := (Real.log (Enclosure.sfrac Bool.false 1673536497104 16000000))

noncomputable def Ns312p1442 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 646826 4000) qz524 646826 4000 0 1 3253248622140663 281474976710656 781250441 27562500000000000 1052142896632378242819 562949953421312000 252666548875133 55125000000000000000 (Enclosure.Real.IsNear.const Bool.false 646826 4000) (BSN.isNear_log_sfrac 1673536497104 16000000 3253248622140663 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1673536497104) qz358)) Bool.false Ns312p1437 Ns312p99 1000000564480000 35280000000000000000000 3253248622140663 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1673536497104 16000000 16 3347072994208 2097152000000 62747592 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns312p1441 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns312p1443 := BSN.arctan_dyadic_bound_f 1000 1293652 1 0 16777216 4410000 0 1 1 0 1 1 12968 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1293652) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1293652) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns312p1444 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1293652))) 884279719003555 562949953421312 1 2000000000000000 12968 16777216 1 4410000 14828451515145979428864 883844585129379 562949953421312 200000000441 882000000000000000 qz15 (Ns312p1443 rfl) rfl rfl 

noncomputable abbrev qz525 := (@HMul.hMul Real Real Real qz579 qz584 qz688)

noncomputable abbrev qz230 := qz525

noncomputable abbrev qz526 := qz688

noncomputable abbrev qz231 := qz526

noncomputable def Ns312p1445 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 646826 4000) qz524) qz230 1052142896632378242819 562949953421312000 252666548875133 55125000000000000000 883844585129379 2251799813685248 200000000441 3528000000000000000 Ns312p1436 1051921935486095898069 562949953421312000 2046332391056189 441000000000000000000 (Ns312p1442 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz231 1 4 0 1 883844585129379 562949953421312 200000000441 882000000000000000 883844585129379 2251799813685248 200000000441 3528000000000000000 qz366 Ns312p1444 rfl) 

noncomputable def Ns312p1446 := @Ns312p1431 Ns312p1425 Ns312p1426 8543462375799090697 903168000000000000000000 (@Ns312p1433 8543462375799090697 903168000000000000000000 (Ns312p1435 (Ns312p1445 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 646826 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz689 (Real.log Real.pi) 646826 2000 0 1 38410761 33554432 1 67108864 12422539447293 33554432000 323413 67108864000 (Enclosure.Real.IsNear.const Bool.false 646826 2000) RS313to324.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns312p1427 Ns312p1428) 

noncomputable def Ns312p1447 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns312p1425 Ns312p1426 8543462375799090697 903168000000000000000000 19712472843 16777216 159 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz367 qz227 (Enclosure.sfrac Bool.true Ns312p1427 Ns312p1428)) Bool.false Ns312p1425 Ns312p1426 8543462375799090697 903168000000000000000000 Ns312p1429 (Ns312p1446 rfl rfl)) 

noncomputable def Ns312p1448 := nat_lit 3796233402801491527335936 

noncomputable def Ns312p1449 := nat_lit 3504470600057673406143806458144176220478187691320233696914833827612527156263161314988758845655354677460602897414042183824469996421005705216 

noncomputable def Ns312p1450 := nat_lit 2489070603249616166738814399266288450905288438596451813314607914250957679307325464099383276742454289337941512599274698807327709986816 

noncomputable def Ns312p1451 := nat_lit 17500618648466351569846803966793294489529524277497193836576577760672027632710698217809307647094996705792004000715053141233486913272887115776 

noncomputable def Ns312p1452 := BSN.sin_dyadic_bound_f 107895442704 68719476736 4 3 33554432 8828614 Ns312p1449 Ns312p239 Ns312p1450 Ns312p1451 Ns312p242 Ns312p1450 33554423 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107895442704) qz602 0 3 Ns312p1449 Ns312p239 Ns312p1450 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107895442704) qz603 0 3 Ns312p1451 Ns312p242 Ns312p1450 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1453 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz223) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 19712472843) qz378) Bool.false 19712472843 16777216 159 16777216 Bool.false 33554423 33554432 1 4410000 (Ns312p1447 rfl) (Enclosure.sfrac_false_div 19712472843 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 19712472843) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns312p1448) qz614) 226375608064910080 72057594037927936 Bool.false 33554423 33554432 186 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q3 19712472843 16777216 226375608064910080 72057594037927936 186 Ns312p1448 Ns312p394 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554423 33554432 Ns312p1448 Ns312p394 107895442704 68719476736 8828614 8820000 (Ns312p1452 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns312p1454 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns312p1425 Ns312p1426 8543462375799090697 903168000000000000000000 315399565491 268435456 2540 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz367 qz227 (Enclosure.sfrac Bool.true Ns312p1427 Ns312p1428)) Bool.false Ns312p1425 Ns312p1426 8543462375799090697 903168000000000000000000 Ns312p1429 (Ns312p1446 rfl rfl)) 

noncomputable def Ns312p1455 := Ns312p1424 56577 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 462 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 166555486 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 295 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 219755025 268435456) qz226 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) Bool.false 33554423 33554432 44872951 4624220160000 268435384 268435456 2605 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 33554423 33554432 44872951 4624220160000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz223) qz223) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 33554423 33554432 717967216 73987522560000 33554423 33554432 44872951 4624220160000 (Ns312p1453 rfl rfl) rfl)) rfl) (Ns312p1454 rfl) RS313to324.d7 

noncomputable def Ns312p1456 := nat_lit 29921281015458215296281597912451756250339309110849655372465365148761441 

noncomputable def Ns312p1457 := nat_lit 11756591357682298343909253371427971905326203002286254325853487889761 

noncomputable def Ns312p1458 := nat_lit 89740329863659281292156975230612412807207274926544393608744388470504801 

noncomputable def Ns312p1459 := BSN.cos_dyadic_bound_f 241983179 268435456 3 2 268435456 134217728 Ns312p1456 Ns312p123 Ns312p1457 Ns312p1458 Ns312p126 Ns312p1457 166555486 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 241983179) qz372 0 2 Ns312p1456 Ns312p123 Ns312p1457 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 241983179) qz373 0 2 Ns312p1458 Ns312p126 Ns312p1457 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1460 := nat_lit 68992643377811637145170449166972144236106926207014912061613077784287425 

noncomputable def Ns312p1461 := nat_lit 19296564586196710075179814410025322223339490007346520231029614696641 

noncomputable def Ns312p1462 := nat_lit 180663776313509969278181837642548908191918447558360494366707822439815361 

noncomputable def Ns312p1463 := BSN.sin_dyadic_bound_f 257445319 268435456 3 2 268435456 134217728 Ns312p1460 Ns312p259 Ns312p1461 Ns312p1462 Ns312p262 Ns312p1461 219755025 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 257445319) qz370 0 2 Ns312p1460 Ns312p259 Ns312p1461 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 257445319) qz371 0 2 Ns312p1462 Ns312p262 Ns312p1461 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1464 := nat_lit 15248473319400958213195087806736 

noncomputable def Ns312p1465 := BSN.sin_dyadic_bound_f 62489434 268435456 2 1 268435456 134217728 Ns312p1464 Ns312p115 Ns312p1464 Ns312p1464 Ns312p116 Ns312p1464 61926559 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 62489434) qz370 0 1 Ns312p1464 Ns312p115 Ns312p1464 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 62489434) qz371 0 1 Ns312p1464 Ns312p116 Ns312p1464 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1466 := nat_lit 148137869535903228907733277384721 

noncomputable def Ns312p1467 := BSN.sin_dyadic_bound_f 110323117 268435456 2 1 268435456 134217728 Ns312p1466 Ns312p115 Ns312p1466 Ns312p1466 Ns312p116 Ns312p1466 107243476 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 110323117) qz370 0 1 Ns312p1466 Ns312p115 Ns312p1466 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 110323117) qz371 0 1 Ns312p1466 Ns312p116 Ns312p1466 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1468 := Ns312p1422 96385 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 177 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 61926559 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 85 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 107243476 268435456) qz226 rfl rfl (Ns312p1455 RS313to324.d9 RS313to324.d11 RS313to324.d13 RS313to324.d17 (Ns312p1459 rfl rfl) (Ns312p1463 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns312p1454 rfl) RS313to324.d19 RS313to324.d21 RS313to324.d23 RS313to324.d25 RS313to324.d17 (Ns312p1465 rfl rfl) (Ns312p1467 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns312p1469 := nat_lit 36925670718796142824716377579776 

noncomputable def Ns312p1470 := BSN.cos_dyadic_bound_f 77952868 268435456 2 1 268435456 134217728 Ns312p1469 Ns312p119 Ns312p1469 Ns312p1469 Ns312p120 Ns312p1469 257196132 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 77952868) qz372 0 1 Ns312p1469 Ns312p119 Ns312p1469 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 77952868) qz373 0 1 Ns312p1469 Ns312p120 Ns312p1469 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1471 := nat_lit 3590202621955863463045311544136090730961908807407926186409523157230625 

noncomputable def Ns312p1472 := nat_lit 52280853452155206595484675082012220167622811956457303672625390625 

noncomputable def Ns312p1473 := nat_lit 9402826983740719866212756592787247704162823106277591462104709732590625 

noncomputable def Ns312p1474 := BSN.sin_dyadic_bound_f 122968205 268435456 3 2 268435456 134217728 Ns312p1471 Ns312p259 Ns312p1472 Ns312p1473 Ns312p262 Ns312p1472 118712323 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 122968205) qz370 0 2 Ns312p1471 Ns312p259 Ns312p1472 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 122968205) qz371 0 2 Ns312p1473 Ns312p262 Ns312p1472 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1475 := Ns312p1420 129931 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 10 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 257196132 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 53 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 118712323 268435456) qz226 rfl rfl (Ns312p1468 rfl rfl) (Ns312p1454 rfl) RS313to324.d27 RS313to324.d29 RS313to324.d31 RS313to324.d33 RS313to324.d17 (Ns312p1470 rfl rfl) (Ns312p1474 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p1476 := nat_lit 1635385035462058022176458484621797770468843196735832775361668015186176 

noncomputable def Ns312p1477 := nat_lit 35146637274107894610076172101159033207537019109927843581533348096 

noncomputable def Ns312p1478 := nat_lit 4906084813111625850740155301521190993340114516169278470397840978862336 

noncomputable def Ns312p1479 := BSN.cos_dyadic_bound_f 117013366 268435456 3 2 268435456 134217728 Ns312p1476 Ns312p123 Ns312p1477 Ns312p1478 Ns312p126 Ns312p1477 243333172 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 117013366) qz372 0 2 Ns312p1476 Ns312p123 Ns312p1477 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 117013366) qz373 0 2 Ns312p1478 Ns312p126 Ns312p1477 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1480 := nat_lit 6254624605468930229291330295659896286824279774980358162643668003231560444520976916174656721014440209734059441 

noncomputable def Ns312p1481 := nat_lit 1564359105322526138919021862911975661109641023496886708604785411251171959510427796695481834396422653361 

noncomputable def Ns312p1482 := nat_lit 37911095086350437781702590206094714761917122847857818826801374841080512766482617962859249180295639552383665585 

noncomputable def Ns312p1483 := BSN.cos_dyadic_bound_f 328242419 268435456 4 3 268435456 134217728 Ns312p1480 Ns312p136 Ns312p1481 Ns312p1482 Ns312p139 Ns312p1481 91540925 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 328242419) qz372 0 3 Ns312p1480 Ns312p136 Ns312p1481 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 328242419) qz373 0 3 Ns312p1482 Ns312p139 Ns312p1481 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1484 := Ns312p1418 159242 BSN.abs_quadSignPos (BSN.cos_quad_nat0 108 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 243333172 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 156 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 91540925 268435456) qz226 rfl rfl (Ns312p1475 rfl) (Ns312p1454 rfl) RS313to324.d35 RS313to324.d37 RS313to324.d39 RS313to324.d41 RS313to324.d17 (Ns312p1479 rfl rfl) (Ns312p1483 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p1485 := nat_lit 22890451090811162507300883382321 

noncomputable def Ns312p1486 := BSN.cos_dyadic_bound_f 69169333 268435456 2 1 268435456 134217728 Ns312p1485 Ns312p119 Ns312p1485 Ns312p1485 Ns312p120 Ns312p1485 259573022 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 69169333) qz372 0 1 Ns312p1485 Ns312p119 Ns312p1485 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 69169333) qz373 0 1 Ns312p1485 Ns312p120 Ns312p1485 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1487 := Ns312p1416 Bool.false 165290472 159242 Bool.true 69169333 14148475504056880 1 Bool.false 259573022 Bool.false Bool.false 247374668 172737 BSN.abs_quadSignPos qz374 (BSN.sfrac_eq_quadSignPos_mul Bool.false 259573022 268435456) qz226 rfl (Ns312p1484 rfl) (Ns312p1454 rfl) RS313to324.d43 RS313to324.d45 RS313to324.d17 (Ns312p1486 rfl rfl) rfl 

noncomputable def Ns312p1488 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) 247374668 268435456 172737 268435456 247374668 268435456 172737 268435456 132808263614857216 61843667 33554432 172737 134217728 (Ns312p1487 rfl rfl rfl rfl) 

noncomputable def Ns312p1489 := @Enclosure.Real.IsNear.mulLit_ff qz686 (Zeta.RiemannSiegel.correction qz225) 5267057 16777216 1 16777216 22242719726675 35184372088832 611589980802751 31032616182349824000 117153672635421645475 590295810358705651712 

noncomputable abbrev qz690 := (@HPow.hPow Real Real Real qz205 qz224 qz207)

noncomputable def Ns312p1490 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz690 1 1 0 1 5267057 16777216 1 16777216 5267057 16777216 1 16777216 

noncomputable def Ns312p1491 := @Enclosure.Real.IsNear.sqrt_image qz224 1727139584789 16777216000 323413 16777216000 170225111 170225143 16777216 (@Enclosure.Real.IsNear.of_eq qz224 (@HMul.hMul Real Real Real qz5 qz223 qz3) Bool.false 1727139584789 16777216000 323413 16777216000 (BSN.t_div_two_pi_mk qz223 646826 1000 qz226) (@Enclosure.Real.IsNear.mulLit_ff qz223 qz3 646826 1000 0 1 5340353 33554432 1 33554432 1727139584789 16777216000 323413 16777216000 (Enclosure.Real.IsNear.const Bool.false 646826 1000) RS313to324.d48 rfl)) 

noncomputable abbrev qz765 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 646826 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz691 := qz765

noncomputable abbrev qz527 := qz691

noncomputable abbrev qz232 := qz527

noncomputable def Ns312p1492 := @Enclosure.Real.IsNear.sqrt_image qz232 170225127 16777216 1 1048576 53440653 53440659 16777216 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 340450254 33554432 32 33554432 170225127 16777216 1 1048576 (Ns312p1491 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns312p1493 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz232) 3340041 1048576 3 16777216 5267056 5267058 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz232) Bool.false 106881312 33554432 6 33554432 3340041 1048576 3 16777216 (Ns312p1492 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns312p1494 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 10534114 33554432 2 33554432 5267057 16777216 1 16777216 (Ns312p1493 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz233 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz521))

noncomputable abbrev qz692 := (@HMul.hMul Real Real Real qz711 qz763 qz763)

noncomputable abbrev qz528 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz692 qz685) qz594)

noncomputable abbrev qz234 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz528))

noncomputable def Ns312p1495 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz225) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz233) qz234) Bool.false 22242719726675 

noncomputable def Ns312p1496 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz233) qz234 13822265 8388608 285 

noncomputable def Ns312p1497 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz233) Bool.false 55289060 33554432 570 33554432 13822265 8388608 285 

noncomputable def Ns312p1498 := @Enclosure.Real.IsNear.recentre' qz233 Bool.false 10181941 16777216 462187216 73987522560000 10181941 16777216 28886701 4624220160000 

noncomputable abbrev qz235 := (@HMul.hMul Real Real Real qz349 qz346 qz521)

noncomputable def Ns312p1499 := @Enclosure.Real.IsNear.cos_image qz235 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7706223) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false 7706223 8388608 101 16777216 Bool.false 10181941 16777216 1 

noncomputable def Ns312p1500 := nat_lit 26986075410360972085564871 

noncomputable def Ns312p1501 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz225 884279719003555 140737488355328 1 500000000000000 2452967 16777216 1 1048576 2169108969484993297685 2361183241434822606848 Ns312p1500 

noncomputable def Ns312p1502 := @Enclosure.Real.IsNear.subLit_ff_p qz232 qz1 170225127 16777216 1 1048576 10 1 0 1 2452967 2452967 16777216 1 

noncomputable def Ns312p1503 := @Ns312p1502 1048576 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 340450254 33554432 32 33554432 170225127 16777216 1 1048576 (Ns312p1491 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns312p1504 := @Enclosure.Real.IsNear.recentre' qz235 Bool.false 2169108969484993297685 2361183241434822606848 Ns312p1500 Ns312p296 7706223 8388608 101 16777216 (@Ns312p1501 Ns312p296 RS313to324.d47 (Ns312p1503 rfl rfl) rfl) 

noncomputable def Ns312p1505 := nat_lit 29350752815935678956376566641317450873398918648314376824961 

noncomputable def Ns312p1506 := nat_lit 12437485246011579022192683940307307005179227397620836481 

noncomputable def Ns312p1507 := nat_lit 88027383477315013711085314556071738006186397490147888801921 

noncomputable def Ns312p1508 := BSN.cos_dyadic_bound_f 7706223 8388608 3 2 16777216 4410000 Ns312p1505 Ns312p318 Ns312p1506 Ns312p1507 Ns312p321 Ns312p1506 10181941 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 7706223) (BSN.cosEvenQ 8388608) 0 2 Ns312p1505 Ns312p318 Ns312p1506 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 7706223) (BSN.cosOddQ 8388608) 0 2 Ns312p1507 Ns312p321 Ns312p1506 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1509 := @Enclosure.Real.IsNear.inv_image qz233 10181941 16777216 28886701 4624220160000 27644245 27644815 16777216 (Ns312p1498 (@Ns312p1499 4410000 (Ns312p1504 rfl) (Enclosure.sfrac_false_div 7706223 8388608) (Ns312p1508 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns312p1510 := @Enclosure.Real.IsNear.recentre' qz234 Bool.false 6436780 16777216 

noncomputable abbrev qz236 := (@HMul.hMul Real Real Real qz349 qz346 qz528)

noncomputable def Ns312p1511 := @Enclosure.Real.IsNear.cos_image qz236 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 19747417)) qz378) Bool.true 19747417 16777216 

noncomputable def Ns312p1512 := nat_lit 46627270319050887979862962445 

noncomputable def Ns312p1513 := nat_lit 58514355281112865685023545741301 

noncomputable def Ns312p1514 := @Enclosure.Real.IsNear.recentre' qz236 Bool.true Ns312p1512 Ns312p184 Ns312p1513 

noncomputable def Ns312p1515 := nat_lit 7555786372591432341913600000000000000 

noncomputable abbrev qz237 := qz528

noncomputable def Ns312p1516 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz237 884279719003555 140737488355328 1 500000000000000 52729096141199 

noncomputable abbrev qz529 := (@HSub.hSub Real Real Real qz583 qz692 qz685)

noncomputable abbrev qz238 := qz529

noncomputable def Ns312p1517 := @Enclosure.Real.IsNear.subLit_tf qz238 qz29 35136910096783 281474976710656 10841583 8796093022208 1 16 

noncomputable abbrev qz530 := qz692

noncomputable abbrev qz239 := qz530

noncomputable def Ns312p1518 := @Enclosure.Real.IsNear.subLit_ff_n qz239 qz225 6017047103089 281474976710656 2452975 8796093022208 2452967 16777216 1 1048576 

noncomputable def Ns312p1519 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz225 2452967 16777216 1 1048576 2452967 16777216 1 1048576 6017047103089 281474976710656 

noncomputable def Ns312p1520 := nat_lit 20264035973411543030548523193979696907530343845099274380317121 

noncomputable def Ns312p1521 := nat_lit 23125033844075125939511353466408569249569175577255533679041 

noncomputable def Ns312p1522 := nat_lit 60745857852546478839766546875006273584091893184143312073593281 

noncomputable def Ns312p1523 := BSN.cos_dyadic_bound_f 19747417 16777216 3 2 16777216 4410000 Ns312p1520 Ns312p583 Ns312p1521 Ns312p1522 Ns312p586 Ns312p1521 6436780 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 19747417) (BSN.cosEvenQ 16777216) 0 2 Ns312p1520 Ns312p583 Ns312p1521 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 19747417) (BSN.cosOddQ 16777216) 0 2 Ns312p1522 Ns312p586 Ns312p1521 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1524 := @Ns312p1510 1184564432 147975045120000 1609195 4194304 74035277 9248440320000 (@Ns312p1511 261 33554432 Bool.false 6436780 16777216 1 4410000 (@Ns312p1514 Ns312p1515 19747417 16777216 261 33554432 (@Ns312p1516 281474976710656 10841583 8796093022208 Ns312p1512 Ns312p184 Ns312p1513 Ns312p1515 RS313to324.d47 (@Ns312p1517 0 1 843665538259184 52729096141199 281474976710656 10841583 8796093022208 (@Ns312p1518 589499530266309296128 35136910096783 281474976710656 10841583 8796093022208 (@Ns312p1519 2452975 8796093022208 (Ns312p1503 rfl rfl) (Ns312p1503 rfl rfl) rfl) (Ns312p1503 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 19747417 16777216) (BSN.cos_neg_of_bound 19747417 16777216 Bool.false 6436780 16777216 1 4410000 (Ns312p1523 rfl rfl)) rfl rfl) 

noncomputable def Ns312p1525 := @Ns312p1489 540149663317650571093 Ns312p1181 (Ns312p1490 qz31 (@Enclosure.Real.IsNear.of_eq qz690 (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 5267057 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz224 (BSN.t_div_two_pi_nonneg qz223 646826 1000 qz226)) Ns312p1494) rfl) (@Ns312p1495 35184372088832 611589980802751 31032616182349824000 (BSN.correction_mk qz225 (BSN.cos_two_pi_p_ne_zero_mk qz223 646826 1000 10 qz226 rfl rfl (@BSN.floor_sqrt_eq_dec qz223 646826 1000 10 qz226 rfl rfl rfl))) (@Ns312p1496 16777216 1609195 4194304 74035277 9248440320000 22242719726675 35184372088832 611589980802751 31032616182349824000 (@Ns312p1497 16777216 (Ns312p1509 rfl rfl rfl rfl rfl) rfl) (Ns312p1524 rfl) rfl)) 

noncomputable def Ns312p1526 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (hardyZApproximantRS₀ qz223) Bool.false 970811622897488667997 590295810358705651712 112216837611037682827093 Ns312p1181 (@Eq.refl Real (hardyZApproximantRS₀ qz223)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (@HMul.hMul Real Real Real qz5 qz686 (Zeta.RiemannSiegel.correction qz225))) Bool.false 970811622897488667997 590295810358705651712 112216837611037682827093 Ns312p1181 (BSN.hardyZApproximantRS₀_eq qz223 10 (@BSN.floor_sqrt_eq_dec qz223 646826 1000 10 qz226 rfl rfl rfl)) (@Ns312p1415 970811622897488667997 590295810358705651712 112216837611037682827093 Ns312p1181 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10)) Bool.false 61843667 33554432 172737 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (Ns312p1488 (Ns312p1487 rfl rfl rfl rfl) rfl rfl)) (Ns312p1525 rfl) rfl rfl)) 

theorem RS313to324.d62 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz223) Bool.false 970811622897488667997 590295810358705651712 112216837611037682827093 Ns312p1181 := Ns312p1526 

noncomputable def Ns312p1527 := nat_lit 6198106008766409342976000 

noncomputable def Ns312p1528 := nat_lit 32923962438163438401207926784 

noncomputable abbrev qz766 := (Enclosure.sfrac Bool.false 648182 1000)

noncomputable abbrev qz693 := qz766

noncomputable abbrev qz531 := qz693

noncomputable abbrev qz240 := qz531

noncomputable abbrev qz767 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 648182 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz694 := qz767

noncomputable abbrev qz532 := qz694

noncomputable abbrev qz241 := qz532

noncomputable abbrev qz768 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 648182 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz695 := qz768

noncomputable abbrev qz533 := qz695

noncomputable abbrev qz242 := qz533

noncomputable abbrev qz696 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz205 qz241 qz207))

noncomputable def Ns312p1529 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (@HMul.hMul Real Real Real qz5 qz696 (Zeta.RiemannSiegel.correction qz242)) 42806457 67108864 86551 67108864 114075693708112095975 590295810358705651712 43714169022597278341 Ns312p1527 Ns312p1528 

noncomputable def Ns312p1530 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos BSN.quadSignPos 9 10 648182 1000 200 268435456 134217728 4503599627370496 Bool.false 316243176965 2545 618095470 62 84886744 8 

noncomputable def Ns312p1531 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 648182 1000 108 156 268435456 134217728 4503599627370496 Bool.false 316243176965 2545 

noncomputable def Ns312p1532 := Ns312p1531 558195838 62 94906264 8 589812974 62 89478488 8 Bool.true 306202484 130206 Bool.true 30315448 Bool.true 284417338 14148475504056880 1 Bool.false 266725454 Bool.false Bool.false 131338972 Bool.false Bool.true 168121139 

noncomputable def Ns312p1533 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 648182 1000 10 52 268435456 134217728 4503599627370496 Bool.false 316243176965 2545 

noncomputable def Ns312p1534 := Ns312p1533 480971758 62 109588312 8 522351262 62 101459064 8 Bool.true 251972445 96589 Bool.false 269366638 Bool.true 409322470 14148475504056880 1 Bool.false 144251862 Bool.true Bool.false 12330617 Bool.false Bool.true 306202484 

noncomputable def Ns312p1535 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 648182 1000 177 85 268435456 134217728 4503599627370496 Bool.false 316243176965 2545 

noncomputable def Ns312p1536 := Ns312p1535 372130544 61 134217720 8 432030192 61 120047984 16 Bool.true 466598 56698 Bool.false 401491890 Bool.false 368101651 14148475504056880 1 Bool.false 267678369 Bool.true Bool.false 263110675 Bool.true Bool.true 251972445 

noncomputable def Ns312p1537 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 648182 1000 463 296 268435456 134217728 4503599627370496 Bool.false 316243176965 2545 

noncomputable def Ns312p1538 := Ns312p1537 186065264 61 189812528 16 294906480 61 154981288 8 Bool.true 268435432 2613 Bool.false 411632727 Bool.false 279506178 14148475504056880 1 Bool.false 268248291 Bool.false Bool.false 135599918 Bool.false Bool.true 466598 

noncomputable def Ns312p1539 := nat_lit 6916656102662590232776852690040425850539347533031657523 

noncomputable def Ns312p1540 := nat_lit 5871038081300061117205361487463311565426029232128000 

noncomputable def Ns312p1541 := nat_lit 54919518963247592564295164687360000 

noncomputable def Ns312p1542 := nat_lit 213587121153980155839430571630630277120 

noncomputable abbrev qz769 := (@Eq.refl Real (Enclosure.sfrac Bool.false 648182 1000))

noncomputable abbrev qz697 := qz769

noncomputable abbrev qz534 := qz697

noncomputable abbrev qz243 := qz534

noncomputable def Ns312p1543 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz240 648182 1000 1680560620496 16000000 1296364 4000 2000 Ns312p1541 Ns312p1542 qz243 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns312p1544 := nat_lit 141653116982529847967269943092027921419045837476488346071040 

noncomputable abbrev qz698 := (@HSub.hSub Real Real Real qz715 qz716 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz717 (@Nat.cast Real Real.instNatCast 1296364))))

noncomputable abbrev qz535 := (@HSub.hSub Real Real Real qz583 (@HMul.hMul Real Real Real qz579 (Enclosure.sfrac Bool.false 648182 4000) (Real.log (Enclosure.sfrac Bool.false 1680560620496 16000000))) (@HMul.hMul Real Real Real qz579 qz584 qz698))

noncomputable abbrev qz699 := (Enclosure.sfrac Bool.false 648182 2000)

noncomputable abbrev qz244 := (@HSub.hSub Real Real Real qz355 (@HSub.hSub Real Real Real qz355 qz535 qz699) (@HMul.hMul Real Real Real qz349 qz699 (Real.log Real.pi)))

noncomputable def Ns312p1545 := @Enclosure.Real.IsNear.addLit_ft_p qz244 (Enclosure.sfrac Bool.true Ns312p1541 Ns312p1542) 663210155809672096767 562949953421312000 8561265475522092679 903168000000000000000000 Ns312p1541 Ns312p1542 0 1 Ns312p1544 

noncomputable def Ns312p1546 := nat_lit 22253640074825047313265721344000 

noncomputable abbrev qz245 := (@HSub.hSub Real Real Real qz355 qz535 qz699)

noncomputable def Ns312p1547 := @Enclosure.Real.IsNear.subLit_ff_p qz245 (@HMul.hMul Real Real Real qz5 qz699 (Real.log Real.pi)) 872062703965293865983 562949953421312000 2050569893448173 441000000000000000000 12448581943251 33554432000 324091 67108864000 Ns312p1546 663210155809672096767 562949953421312000 

noncomputable abbrev qz246 := qz535

noncomputable def Ns312p1548 := @Enclosure.Real.IsNear.subLit_ff_p qz246 qz699 8436077738556482347 4503599627370496 2050569893448173 441000000000000000000 648182 2000 0 1 13953003263444701855728 872062703965293865983 562949953421312000 2050569893448173 441000000000000000000 

noncomputable def Ns312p1549 := nat_lit 18996358279915755237102753526317056 

noncomputable def Ns312p1550 := nat_lit 55910639555821829095424000 

noncomputable def Ns312p1551 := nat_lit 23071252366023028150077706495659788022231515172676369550511949555762554581237712579157128389914695877584227831553021538263338004702651488208559875985244160 

noncomputable def Ns312p1552 := nat_lit 426193070476198540923843427017251370432672788982677427097903382536894818573153952061341633906918842680784801240202349623650823686011762451821486042775552 

noncomputable def Ns312p1553 := nat_lit 42199043833735288077343725297738578619755076652184639852018696320360732818797297662731335835866503815118745142452955632232779827053479053303480320 

noncomputable def Ns312p1554 := BSN.log_dyadic_bound 631984620496 2729136620496 7 6 Ns312p1551 134217728 35280000 Ns312p1552 Ns312p1553 63309748 3361121240992 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 631984620496) (BSN.artanhQ 2729136620496) 0 6 Ns312p1552 Ns312p1551 Ns312p1553 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz536 := (Real.log (Enclosure.sfrac Bool.false 1680560620496 16000000))

noncomputable def Ns312p1555 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 648182 4000) qz536 648182 4000 0 1 3254427548720375 281474976710656 781250441 27562500000000000 8437845429538680433 4503599627370496 253196236674131 55125000000000000000 (Enclosure.Real.IsNear.const Bool.false 648182 4000) (BSN.isNear_log_sfrac 1680560620496 16000000 3254427548720375 281474976710656 781250441 27562500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1680560620496) qz358)) Bool.false Ns312p1550 Ns312p99 1000000564480000 35280000000000000000000 3254427548720375 281474976710656 781250441 27562500000000000 (BSN.log_rat_reduce_isNear 1680560620496 16000000 16 3361121240992 2097152000000 63309748 134217728 24973259072661432 36028797018963968 35280000 1000000000000000 rfl rfl rfl rfl (Ns312p1554 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns312p1556 := BSN.arctan_dyadic_bound_f 1000 1296364 1 0 16777216 4410000 0 1 1 0 1 1 12941 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1296364) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1296364) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns312p1557 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1296364))) 884279719003555 562949953421312 1 2000000000000000 12941 16777216 1 4410000 14828466714794721804288 883845491099043 562949953421312 200000000441 882000000000000000 qz15 (Ns312p1556 rfl) rfl rfl 

noncomputable abbrev qz537 := (@HMul.hMul Real Real Real qz579 qz584 qz698)

noncomputable abbrev qz247 := qz537

noncomputable abbrev qz538 := qz698

noncomputable abbrev qz248 := qz538

noncomputable def Ns312p1558 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 648182 4000) qz536) qz247 8437845429538680433 4503599627370496 253196236674131 55125000000000000000 883845491099043 2251799813685248 200000000441 3528000000000000000 Ns312p1549 8436077738556482347 4503599627370496 2050569893448173 441000000000000000000 (Ns312p1555 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz248 1 4 0 1 883845491099043 562949953421312 200000000441 882000000000000000 883845491099043 2251799813685248 200000000441 3528000000000000000 qz366 Ns312p1557 rfl) 

noncomputable def Ns312p1559 := @Ns312p1545 Ns312p1539 Ns312p1540 8561265475522092679 903168000000000000000000 (@Ns312p1547 8561265475522092679 903168000000000000000000 (Ns312p1548 (Ns312p1558 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 648182 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz699 (Real.log Real.pi) 648182 2000 0 1 38410761 33554432 1 67108864 12448581943251 33554432000 324091 67108864000 (Enclosure.Real.IsNear.const Bool.false 648182 2000) RS313to324.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns312p1541 Ns312p1542) 

noncomputable def Ns312p1560 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns312p1539 Ns312p1540 8561265475522092679 903168000000000000000000 617662455 524288 319 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz367 qz244 (Enclosure.sfrac Bool.true Ns312p1541 Ns312p1542)) Bool.false Ns312p1539 Ns312p1540 8561265475522092679 903168000000000000000000 Ns312p1543 (Ns312p1559 rfl rfl)) 

noncomputable def Ns312p1561 := nat_lit 3514366258950758600328217977074506129388040573259970716052992607994404169597913026617147921543340685969785547097824551925217420552276279296 

noncomputable def Ns312p1562 := nat_lit 2510172954607598128906477023992340374491972783784746672191216661469676589389643998104114567787067656988471819068282071440710273335296 

noncomputable def Ns312p1563 := nat_lit 17549974245022709694517761789970315877485601815566038963649774107729315517226419724627413141450636567239549638617410463073165633640470675456 

noncomputable def Ns312p1564 := BSN.sin_dyadic_bound_f 107971376264 68719476736 4 3 33554432 8828614 Ns312p1561 Ns312p239 Ns312p1562 Ns312p1563 Ns312p242 Ns312p1562 33554429 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107971376264) qz602 0 3 Ns312p1561 Ns312p239 Ns312p1562 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107971376264) qz603 0 3 Ns312p1563 Ns312p242 Ns312p1562 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1565 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz240) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 617662455) (@Nat.cast Real Real.instNatCast 524288)) Bool.false 617662455 524288 319 33554432 Bool.true 33554429 33554432 1 4410000 (Ns312p1560 rfl) (Enclosure.sfrac_false_div 617662455 524288) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 617662455) (@Nat.cast Real Real.instNatCast 524288)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 118715783669317684428800) (@Nat.cast Real Real.instNatCast 75557863725914323419136)) 226375608064910080 72057594037927936 Bool.false 33554429 33554432 187 1000000000000000 8820000 4410000 (BSN.sin_reduce_arg_pos_rat_q1 617662455 524288 226375608064910080 72057594037927936 187 118715783669317684428800 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554429 33554432 118715783669317684428800 75557863725914323419136 107971376264 68719476736 8828614 8820000 (Ns312p1564 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns312p1566 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns312p1539 Ns312p1540 8561265475522092679 903168000000000000000000 316243176965 268435456 2545 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz367 qz244 (Enclosure.sfrac Bool.true Ns312p1541 Ns312p1542)) Bool.false Ns312p1539 Ns312p1540 8561265475522092679 903168000000000000000000 Ns312p1543 (Ns312p1559 rfl rfl)) 

noncomputable def Ns312p1567 := Ns312p1538 56698 BSN.abs_quadSignPos (BSN.cos_quad_nat3 463 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268248291 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 296 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 135599918 268435456) qz243 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) Bool.true 33554429 33554432 90021527 9248440320000 268435432 268435456 2613 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 33554429 33554432 90021527 9248440320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz240) qz240) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 33554429 33554432 1440344432 147975045120000 33554429 33554432 90021527 9248440320000 (Ns312p1565 rfl rfl) rfl)) rfl) (Ns312p1566 rfl) RS313to324.d7 

noncomputable def Ns312p1568 := nat_lit 40239384361690401974407562195873490075067102865036530712705206772587197046055395334643394955182440974587879521 

noncomputable def Ns312p1569 := nat_lit 23665667276035477147146221254497261679831580635396565882728181861979685988065743000235565492623893684321 

noncomputable def Ns312p1570 := nat_lit 200969818603812372817232539922514106911233574116212464706869902990496703886413012362881284359613943952392413281 

noncomputable def Ns312p1571 := BSN.sin_dyadic_bound_f 411632727 268435456 4 3 268435456 134217728 Ns312p1568 Ns312p147 Ns312p1569 Ns312p1570 Ns312p150 Ns312p1569 268248291 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 411632727) qz370 0 3 Ns312p1568 Ns312p147 Ns312p1569 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 411632727) qz371 0 3 Ns312p1570 Ns312p150 Ns312p1569 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1572 := nat_lit 3286352818274038400511378797870783655173926193035283242546442164257331628791425863468751321414515986635165696 

noncomputable def Ns312p1573 := nat_lit 227351037214143778548705768311528703668784545366235021184845514082684434426732645056550909726341206016 

noncomputable def Ns312p1574 := nat_lit 19927912727670031880223812082357090861669349732692077147579718942879759100369318789246278234622719197733457920 

noncomputable def Ns312p1575 := BSN.cos_dyadic_bound_f 279506178 268435456 4 3 268435456 134217728 Ns312p1572 Ns312p136 Ns312p1573 Ns312p1574 Ns312p139 Ns312p1573 135599918 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 279506178) qz372 0 3 Ns312p1572 Ns312p136 Ns312p1573 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 279506178) qz373 0 3 Ns312p1574 Ns312p139 Ns312p1573 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1576 := nat_lit 36411915549385549765548741320063966257499785467423256553826376762094176029789784399403860825765358869670400000 

noncomputable def Ns312p1577 := nat_lit 17543705372452431723377852665673789530763288272106795278337824672722581972754500652632682321000000000000 

noncomputable def Ns312p1578 := nat_lit 181873565679724752527355037571691365503276760978080162197507802550350428020542737871193010129148317644352000000 

noncomputable def Ns312p1579 := BSN.sin_dyadic_bound_f 401491890 268435456 4 3 268435456 134217728 Ns312p1576 Ns312p147 Ns312p1577 Ns312p1578 Ns312p150 Ns312p1577 267678369 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 401491890) qz370 0 3 Ns312p1576 Ns312p147 Ns312p1577 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 401491890) qz371 0 3 Ns312p1578 Ns312p150 Ns312p1577 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1580 := nat_lit 25715607784669109202354175127353059851499469930041797560771712595042007121743284054286941425815115250279255601 

noncomputable def Ns312p1581 := nat_lit 6188895990095263308191023785195882306796767434188039072953477962954601355010048091175462720495638154801 

noncomputable def Ns312p1582 := nat_lit 128485180576280019152303199705448640216975117849011575710053392439033775942670566458244384253719377026082278961 

noncomputable def Ns312p1583 := BSN.sin_dyadic_bound_f 368101651 268435456 4 3 268435456 134217728 Ns312p1580 Ns312p147 Ns312p1581 Ns312p1582 Ns312p150 Ns312p1581 263110675 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 368101651) qz370 0 3 Ns312p1580 Ns312p147 Ns312p1581 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 368101651) qz371 0 3 Ns312p1582 Ns312p150 Ns312p1581 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1584 := Ns312p1536 96589 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 177 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 267678369 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 85 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 263110675 268435456) qz243 rfl rfl (Ns312p1567 RS313to324.d9 RS313to324.d11 RS313to324.d13 RS313to324.d17 (Ns312p1571 rfl rfl) (Ns312p1575 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns312p1566 rfl) RS313to324.d19 RS313to324.d21 RS313to324.d23 RS313to324.d25 RS313to324.d17 (Ns312p1579 rfl rfl) (Ns312p1583 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns312p1585 := nat_lit 2834536358337844951416098682570722173342687699105556669807664287782559281480226104377170789988820684019470336 

noncomputable def Ns312p1586 := nat_lit 145923645217675238660554000962831534721927508209476793935644101875028811347184835901184953410840825856 

noncomputable def Ns312p1587 := nat_lit 17189271611236980557298464093830909553153013010245640039603400331019395846610463597096219260964944406669824000 

noncomputable def Ns312p1588 := BSN.cos_dyadic_bound_f 269366638 268435456 4 3 268435456 134217728 Ns312p1585 Ns312p136 Ns312p1586 Ns312p1587 Ns312p139 Ns312p1586 144251862 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 269366638) qz372 0 3 Ns312p1585 Ns312p136 Ns312p1586 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 269366638) qz373 0 3 Ns312p1587 Ns312p139 Ns312p1586 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1589 := nat_lit 15153155137690625914104343857872113777277652074333031883278649545332947904869700074637449727331743193664000000 

noncomputable def Ns312p1590 := nat_lit 22120097343938058272354311245704079967092602408930669927952992224206799269923812464115417441000000000000 

noncomputable def Ns312p1591 := nat_lit 91732439955473480877779579819495776561234272556720270938086264099053927148660447085400542936203136332761600000 

noncomputable def Ns312p1592 := BSN.cos_dyadic_bound_f 409322470 268435456 4 3 268435456 134217728 Ns312p1589 Ns312p136 Ns312p1590 Ns312p1591 Ns312p139 Ns312p1590 12330617 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 409322470) qz372 0 3 Ns312p1589 Ns312p136 Ns312p1590 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 409322470) qz373 0 3 Ns312p1591 Ns312p139 Ns312p1590 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1593 := Ns312p1534 130206 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 10 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 144251862 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 52 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 12330617 268435456) qz243 rfl rfl (Ns312p1584 rfl rfl) (Ns312p1566 rfl) RS313to324.d27 RS313to324.d29 RS313to324.d31 RS313to324.d33 RS313to324.d17 (Ns312p1588 rfl rfl) (Ns312p1592 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p1594 := nat_lit 844609500812310978907116015616 

noncomputable def Ns312p1595 := BSN.cos_dyadic_bound_f 30315448 268435456 2 1 268435456 134217728 Ns312p1594 Ns312p119 Ns312p1594 Ns312p1594 Ns312p120 Ns312p1594 266725454 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 30315448) qz372 0 1 Ns312p1594 Ns312p119 Ns312p1594 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 30315448) qz373 0 1 Ns312p1594 Ns312p120 Ns312p1594 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1596 := nat_lit 3523665906031653967433441858015568621446300388899670202079929322480456344226043468196182762460705388299227136 

noncomputable def Ns312p1597 := nat_lit 280203017571303832111935070898712735572521340513197692097281743070387254216551500178476684301653446656 

noncomputable def Ns312p1598 := nat_lit 21366222319447937829761112279598164987609795032987113538932986675091945897572248186555804754289797901558681600 

noncomputable def Ns312p1599 := BSN.cos_dyadic_bound_f 284417338 268435456 4 3 268435456 134217728 Ns312p1596 Ns312p136 Ns312p1597 Ns312p1598 Ns312p139 Ns312p1597 131338972 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 284417338) qz372 0 3 Ns312p1596 Ns312p136 Ns312p1597 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 284417338) qz373 0 3 Ns312p1598 Ns312p139 Ns312p1597 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1600 := Ns312p1532 159578 BSN.abs_quadSignPos (BSN.cos_quad_nat0 108 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 266725454 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 156 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 131338972 268435456) qz243 rfl rfl (Ns312p1593 rfl) (Ns312p1566 rfl) RS313to324.d35 RS313to324.d37 RS313to324.d39 RS313to324.d41 RS313to324.d17 (Ns312p1595 rfl rfl) (Ns312p1599 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns312p1601 := nat_lit 16460006919050191861105660179121 

noncomputable def Ns312p1602 := BSN.cos_dyadic_bound_f 63695317 268435456 2 1 268435456 134217728 Ns312p1601 Ns312p119 Ns312p1601 Ns312p1601 Ns312p120 Ns312p1601 260913920 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 63695317) qz372 0 1 Ns312p1601 Ns312p119 Ns312p1601 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 63695317) qz373 0 1 Ns312p1601 Ns312p120 Ns312p1601 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1603 := Ns312p1530 Bool.true 168121139 159578 Bool.true 63695317 14148475504056880 1 Bool.false 260913920 Bool.false Bool.true 85612914 173102 BSN.abs_quadSignPos qz374 (BSN.sfrac_eq_quadSignPos_mul Bool.false 260913920 268435456) qz243 rfl (Ns312p1600 rfl) (Ns312p1566 rfl) RS313to324.d43 RS313to324.d45 RS313to324.d17 (Ns312p1602 rfl rfl) rfl 

noncomputable def Ns312p1604 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) 85612914 268435456 173102 268435456 85612914 268435456 173102 268435456 45963083218157568 42806457 67108864 86551 67108864 (Ns312p1603 rfl rfl rfl rfl) 

noncomputable def Ns312p1605 := @Enclosure.Real.IsNear.mulLit_ff qz696 (Zeta.RiemannSiegel.correction qz242) 1316075 4194304 1 16777216 86678717936373 140737488355328 10842125397421 484884627849216000 114075693708112095975 590295810358705651712 

noncomputable abbrev qz700 := (@HPow.hPow Real Real Real qz205 qz241 qz207)

noncomputable def Ns312p1606 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz700 1 1 0 1 1316075 4194304 1 16777216 1316075 4194304 1 16777216 

noncomputable def Ns312p1607 := @Enclosure.Real.IsNear.sqrt_image qz241 1730760344123 16777216000 324091 16777216000 170403446 170403479 16777216 (@Enclosure.Real.IsNear.of_eq qz241 (@HMul.hMul Real Real Real qz5 qz240 qz3) Bool.false 1730760344123 16777216000 324091 16777216000 (BSN.t_div_two_pi_mk qz240 648182 1000 qz243) (@Enclosure.Real.IsNear.mulLit_ff qz240 qz3 648182 1000 0 1 5340353 33554432 1 33554432 1730760344123 16777216000 324091 16777216000 (Enclosure.Real.IsNear.const Bool.false 648182 1000) RS313to324.d48 rfl)) 

noncomputable abbrev qz770 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 648182 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz701 := qz770

noncomputable abbrev qz539 := qz701

noncomputable abbrev qz249 := qz539

noncomputable def Ns312p1608 := @Enclosure.Real.IsNear.sqrt_image qz249 340806925 33554432 33 33554432 53468639 53468645 16777216 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 340806925 33554432 33 33554432 340806925 33554432 33 33554432 (Ns312p1607 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns312p1609 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz249) 26734321 8388608 3 16777216 5264299 5264301 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz249) Bool.false 106937284 33554432 6 33554432 26734321 8388608 3 16777216 (Ns312p1608 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns312p1610 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 10528600 33554432 2 33554432 1316075 4194304 1 16777216 (Ns312p1609 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz250 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz533))

noncomputable abbrev qz702 := (@HMul.hMul Real Real Real qz711 qz768 qz768)

noncomputable abbrev qz540 := (@HSub.hSub Real Real Real qz583 (@HSub.hSub Real Real Real qz583 qz702 qz695) qz594)

noncomputable abbrev qz251 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz540))

noncomputable def Ns312p1611 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz242) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz250) qz251) Bool.false 86678717936373 

noncomputable def Ns312p1612 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz250) qz251 60732513 33554432 707 

noncomputable def Ns312p1613 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz250) Bool.false 60732513 33554432 707 33554432 60732513 33554432 707 

noncomputable def Ns312p1614 := @Enclosure.Real.IsNear.recentre' qz250 Bool.false 9269334 16777216 59427152 9248440320000 4634667 8388608 3714197 578027520000 

noncomputable abbrev qz252 := (@HMul.hMul Real Real Real qz349 qz346 qz533)

noncomputable def Ns312p1615 := @Enclosure.Real.IsNear.cos_image qz252 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16532961) qz378) Bool.false 16532961 16777216 13 2097152 Bool.false 9269334 16777216 1 

noncomputable def Ns312p1616 := nat_lit 890540488543658932754108071 

noncomputable def Ns312p1617 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz242 884279719003555 140737488355328 1 500000000000000 5262605 33554432 33 33554432 4653614870626703560775 4722366482869645213696 Ns312p1616 

noncomputable def Ns312p1618 := @Enclosure.Real.IsNear.subLit_ff_p qz249 qz1 340806925 33554432 33 33554432 10 1 0 1 5262605 5262605 33554432 33 

noncomputable def Ns312p1619 := @Ns312p1618 33554432 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 340806925 33554432 33 33554432 340806925 33554432 33 33554432 (Ns312p1607 rfl rfl rfl rfl rfl rfl) rfl) qz379 

noncomputable def Ns312p1620 := @Enclosure.Real.IsNear.recentre' qz252 Bool.false 4653614870626703560775 4722366482869645213696 Ns312p1616 Ns312p796 16532961 16777216 13 2097152 (@Ns312p1617 Ns312p796 RS313to324.d47 (Ns312p1619 rfl rfl) rfl) 

noncomputable def Ns312p1621 := nat_lit 9950276339398338300341476520809377814339738266765834033340161 

noncomputable def Ns312p1622 := nat_lit 5582196630097780475391401840067488501008411849729030004481 

noncomputable def Ns312p1623 := nat_lit 29839664624934819340073646758747998466017197976598044040011521 

noncomputable def Ns312p1624 := BSN.cos_dyadic_bound_f 16532961 16777216 3 2 16777216 4410000 Ns312p1621 Ns312p583 Ns312p1622 Ns312p1623 Ns312p586 Ns312p1622 9269334 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 16532961) (BSN.cosEvenQ 16777216) 0 2 Ns312p1621 Ns312p583 Ns312p1622 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 16532961) (BSN.cosOddQ 16777216) 0 2 Ns312p1623 Ns312p586 Ns312p1622 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1625 := @Enclosure.Real.IsNear.inv_image qz250 4634667 8388608 3714197 578027520000 30365903 30366610 16777216 (Ns312p1614 (@Ns312p1615 4410000 (Ns312p1620 rfl) (Enclosure.sfrac_false_div 16532961 16777216) (Ns312p1624 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns312p1626 := @Enclosure.Real.IsNear.recentre' qz251 Bool.false 5708884 16777216 

noncomputable abbrev qz253 := (@HMul.hMul Real Real Real qz349 qz346 qz540)

noncomputable def Ns312p1627 := @Enclosure.Real.IsNear.cos_image qz253 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 5132091)) qz595) Bool.true 5132091 4194304 

noncomputable def Ns312p1628 := nat_lit 193884920172455847603697881445 

noncomputable def Ns312p1629 := nat_lit 39254735309236475475684023026718333 

noncomputable def Ns312p1630 := @Enclosure.Real.IsNear.recentre' qz253 Bool.true Ns312p1628 Ns312p809 Ns312p1629 

noncomputable abbrev qz254 := qz540

noncomputable def Ns312p1631 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz254 884279719003555 140737488355328 1 500000000000000 219257454406999 

noncomputable abbrev qz541 := (@HSub.hSub Real Real Real qz583 qz702 qz695)

noncomputable abbrev qz255 := qz541

noncomputable def Ns312p1632 := @Enclosure.Real.IsNear.subLit_tf qz255 qz29 148888710229335 1125899906842624 1454629275 1125899906842624 1 16 

noncomputable abbrev qz542 := qz702

noncomputable abbrev qz256 := qz542

noncomputable def Ns312p1633 := @Enclosure.Real.IsNear.subLit_ff_n qz256 qz242 27695011386025 1125899906842624 347333019 1125899906842624 5262605 33554432 33 33554432 

noncomputable def Ns312p1634 := @Enclosure.Real.IsNear.mulLit_ff qz242 qz242 5262605 33554432 33 33554432 5262605 33554432 33 33554432 27695011386025 1125899906842624 

noncomputable def Ns312p1635 := nat_lit 361164747928321513384164190045416629176072301523752338401 

noncomputable def Ns312p1636 := nat_lit 481232320745807914071428121431949844375050513400087521 

noncomputable def Ns312p1637 := nat_lit 1082531779143472924324349713893385987839466803544456840161 

noncomputable def Ns312p1638 := BSN.cos_dyadic_bound_f 5132091 4194304 3 2 16777216 4410000 Ns312p1635 Ns312p193 Ns312p1636 Ns312p1637 Ns312p196 Ns312p1636 5708884 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 5132091) (BSN.cosEvenQ 4194304) 0 2 Ns312p1635 Ns312p193 Ns312p1636 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 5132091) (BSN.cosOddQ 4194304) 0 2 Ns312p1637 Ns312p196 Ns312p1636 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns312p1639 := @Ns312p1626 620947216 73987522560000 1427221 4194304 38809201 4624220160000 (@Ns312p1627 137 16777216 Bool.false 5708884 16777216 1 4410000 (@Ns312p1630 Ns312p812 5132091 4194304 137 16777216 (@Ns312p1631 1125899906842624 1454629275 1125899906842624 Ns312p1628 Ns312p809 Ns312p1629 Ns312p812 RS313to324.d47 (@Ns312p1632 0 1 3508119270511984 219257454406999 1125899906842624 1454629275 1125899906842624 (@Ns312p1633 4995876102957925662720 148888710229335 1125899906842624 1454629275 1125899906842624 (@Ns312p1634 347333019 1125899906842624 (Ns312p1619 rfl rfl) (Ns312p1619 rfl rfl) rfl) (Ns312p1619 rfl rfl) rfl rfl) qz383 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 5132091 4194304) (BSN.cos_neg_of_bound 5132091 4194304 Bool.false 5708884 16777216 1 4410000 (Ns312p1638 rfl rfl)) rfl rfl) 

noncomputable def Ns312p1640 := @Ns312p1605 43714169022597278341 Ns312p1527 (Ns312p1606 qz31 (@Enclosure.Real.IsNear.of_eq qz700 (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 1316075 4194304 1 16777216 (BSN.rpow_neg_quarter_mk qz241 (BSN.t_div_two_pi_nonneg qz240 648182 1000 qz243)) Ns312p1610) rfl) (@Ns312p1611 140737488355328 10842125397421 484884627849216000 (BSN.correction_mk qz242 (BSN.cos_two_pi_p_ne_zero_mk qz240 648182 1000 10 qz243 rfl rfl (@BSN.floor_sqrt_eq_dec qz240 648182 1000 10 qz243 rfl rfl rfl))) (@Ns312p1612 33554432 1427221 4194304 38809201 4624220160000 86678717936373 140737488355328 10842125397421 484884627849216000 (@Ns312p1613 33554432 (Ns312p1625 rfl rfl rfl rfl rfl) rfl) (Ns312p1639 rfl) rfl)) 

noncomputable def Ns312p1641 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (hardyZApproximantRS₀ qz240) Bool.true 490605271431258893031 590295810358705651712 8037475964256405662341 Ns312p1527 (@Eq.refl Real (hardyZApproximantRS₀ qz240)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (@HSub.hSub Real Real Real qz32 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (@HMul.hMul Real Real Real qz5 qz696 (Zeta.RiemannSiegel.correction qz242))) Bool.true 490605271431258893031 590295810358705651712 8037475964256405662341 Ns312p1527 (BSN.hardyZApproximantRS₀_eq qz240 10 (@BSN.floor_sqrt_eq_dec qz240 648182 1000 10 qz243 rfl rfl rfl)) (@Ns312p1529 490605271431258893031 590295810358705651712 8037475964256405662341 Ns312p1527 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (@HAdd.hAdd Real Real Real qz367 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10)) Bool.true 42806457 67108864 86551 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (Ns312p1604 (Ns312p1603 rfl rfl rfl rfl) rfl rfl)) (Ns312p1640 rfl) rfl rfl)) 

theorem RS313to324.d63 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz240) Bool.true 490605271431258893031 590295810358705651712 8037475964256405662341 Ns312p1527 := Ns312p1641 

noncomputable def RS313to324.d64 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz543 := (RS313to324.d3 qz580 qz596 (@Enclosure.dec_le_dec qz580 qz596 631875 1000 633237 1000 (@Eq.refl Real qz580) qz599 rfl rfl rfl))

noncomputable abbrev qz257 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz543)

noncomputable def Ns312p1642 := @Enclosure.Real.IsNear.of_eq qz257 (hardyZApproximantRS₀ qz4) Bool.true 9866179332244399220633 9444732965739290427392 Ns312p74 Ns312p75 

noncomputable abbrev qz544 := (@Enclosure.dec_le_dec qz580 qz596 631875 1000 633237 1000 (@Eq.refl Real qz580) qz599 rfl rfl rfl)

noncomputable abbrev qz258 := qz544

noncomputable def Ns312p1643 := @Enclosure.Real.IsNear.neg_val qz257 9866179332244399220633 9444732965739290427392 Ns312p74 Ns312p75 (Ns312p1642 (RS313to324.d4 qz4 qz33 qz258) RS313to324.d49) rfl 

noncomputable abbrev qz259 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz543)

noncomputable def Ns312p1644 := @Enclosure.Real.IsNear.of_eq qz259 (hardyZApproximantRS₀ qz33) Bool.false 3838119545225413419495 2361183241434822606848 27419207134084085369663 Ns312p201 

noncomputable def Ns312p1645 := @Enclosure.Real.IsNear.pos_val qz259 3838119545225413419495 2361183241434822606848 27419207134084085369663 Ns312p201 (Ns312p1644 (RS313to324.d50 qz4 qz33 qz258) RS313to324.d51) rfl 

noncomputable def Ns312p1646 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz257 qz4 qz4 631875 1000 631875 1000 

noncomputable def Ns312p1647 := @Enclosure.norm_gt_of_isNear qz257 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 9866179332244399220633 9444732965739290427392 Ns312p74 

noncomputable def Ns312p1648 := @Ns312p1647 Ns312p75 325136221 5368709120 1421 5368709120 (Ns312p1642 (RS313to324.d4 qz4 qz33 qz258) RS313to324.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable def Ns312p1649 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz259 qz4 qz33 631875 1000 633237 1000 

noncomputable def Ns312p1650 := @Enclosure.norm_gt_of_isNear qz259 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 3838119545225413419495 2361183241434822606848 27419207134084085369663 

noncomputable def Ns312p1651 := @Ns312p1650 Ns312p201 325136221 5368709120 1421 5368709120 (Ns312p1644 (RS313to324.d50 qz4 qz33 qz258) RS313to324.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable abbrev qz260 := qz543

noncomputable def Ns312p1652 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz260 (@BSN.thirtyTwoPi_le_dec qz4 631875 1000 qz9 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz257 qz259 (Ns312p1643 rfl rfl) (Ns312p1645 rfl rfl)) (Ns312p1646 qz9 qz9 rfl rfl rfl rfl (Ns312p1648 rfl)) (Ns312p1649 qz9 qz36 rfl rfl rfl rfl (Ns312p1651 rfl)) 

noncomputable abbrev qz545 := (RS313to324.d3 qz596 qz608 (@Enclosure.dec_le_dec qz596 qz608 633237 1000 634599 1000 qz599 qz611 rfl rfl rfl))

noncomputable abbrev qz261 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz545)

noncomputable def Ns312p1653 := @Enclosure.Real.IsNear.of_eq qz261 (hardyZApproximantRS₀ qz33) Bool.false 3838119545225413419495 2361183241434822606848 27419207134084085369663 Ns312p201 

noncomputable abbrev qz546 := (@Enclosure.dec_le_dec qz596 qz608 633237 1000 634599 1000 qz599 qz611 rfl rfl rfl)

noncomputable abbrev qz262 := qz546

noncomputable def Ns312p1654 := @Enclosure.Real.IsNear.pos_val qz261 3838119545225413419495 2361183241434822606848 27419207134084085369663 Ns312p201 (Ns312p1653 (RS313to324.d4 qz33 qz60 qz262) RS313to324.d51) rfl 

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz545)

noncomputable def Ns312p1655 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantRS₀ qz60) Bool.true 13435491129204490605593 2361183241434822606848 29441627457175133279809 Ns312p359 

noncomputable def Ns312p1656 := @Enclosure.Real.IsNear.neg_val qz263 13435491129204490605593 2361183241434822606848 29441627457175133279809 Ns312p359 (Ns312p1655 (RS313to324.d50 qz33 qz60 qz262) RS313to324.d53) rfl 

noncomputable def Ns312p1657 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz261 qz4 qz33 631875 1000 633237 1000 

noncomputable def Ns312p1658 := @Enclosure.norm_gt_of_isNear qz261 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 3838119545225413419495 2361183241434822606848 27419207134084085369663 

noncomputable def Ns312p1659 := @Ns312p1658 Ns312p201 325136221 5368709120 1421 5368709120 (Ns312p1653 (RS313to324.d4 qz33 qz60 qz262) RS313to324.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable def Ns312p1660 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz263 qz4 qz60 631875 1000 634599 1000 

noncomputable def Ns312p1661 := @Enclosure.norm_gt_of_isNear qz263 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 13435491129204490605593 2361183241434822606848 29441627457175133279809 

noncomputable def Ns312p1662 := @Ns312p1661 Ns312p359 325136221 5368709120 1421 5368709120 (Ns312p1655 (RS313to324.d50 qz33 qz60 qz262) RS313to324.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable abbrev qz264 := qz545

noncomputable def Ns312p1663 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz264 (@BSN.thirtyTwoPi_le_dec qz33 633237 1000 qz36 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz261 qz263 (Ns312p1654 rfl rfl) (Ns312p1656 rfl rfl)) (Ns312p1657 qz9 qz36 rfl rfl rfl rfl (Ns312p1659 rfl)) (Ns312p1660 qz9 qz63 rfl rfl rfl rfl (Ns312p1662 rfl)) 

noncomputable abbrev qz547 := (RS313to324.d3 qz608 qz617 (@Enclosure.dec_le_dec qz608 qz617 634599 1000 636640 1000 qz611 qz620 rfl rfl rfl))

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz547)

noncomputable def Ns312p1664 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantRS₀ qz60) Bool.true 13435491129204490605593 2361183241434822606848 29441627457175133279809 Ns312p359 

noncomputable abbrev qz548 := (@Enclosure.dec_le_dec qz608 qz617 634599 1000 636640 1000 qz611 qz620 rfl rfl rfl)

noncomputable abbrev qz266 := qz548

noncomputable def Ns312p1665 := @Enclosure.Real.IsNear.neg_val qz265 13435491129204490605593 2361183241434822606848 29441627457175133279809 Ns312p359 (Ns312p1664 (RS313to324.d4 qz60 qz78 qz266) RS313to324.d53) rfl 

noncomputable abbrev qz267 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz547)

noncomputable def Ns312p1666 := @Enclosure.Real.IsNear.of_eq qz267 (hardyZApproximantRS₀ qz78) Bool.false 25306016193483694032653 9444732965739290427392 8822831630086185712339 Ns312p471 

noncomputable def Ns312p1667 := @Enclosure.Real.IsNear.pos_val qz267 25306016193483694032653 9444732965739290427392 8822831630086185712339 Ns312p471 (Ns312p1666 (RS313to324.d50 qz60 qz78 qz266) RS313to324.d54) rfl 

noncomputable def Ns312p1668 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz265 qz4 qz60 631875 1000 634599 1000 

noncomputable def Ns312p1669 := @Enclosure.norm_gt_of_isNear qz265 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 13435491129204490605593 2361183241434822606848 29441627457175133279809 

noncomputable def Ns312p1670 := @Ns312p1669 Ns312p359 325136221 5368709120 1421 5368709120 (Ns312p1664 (RS313to324.d4 qz60 qz78 qz266) RS313to324.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable def Ns312p1671 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz267 qz4 qz78 631875 1000 636640 1000 

noncomputable def Ns312p1672 := @Enclosure.norm_gt_of_isNear qz267 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 25306016193483694032653 9444732965739290427392 8822831630086185712339 

noncomputable def Ns312p1673 := @Ns312p1672 Ns312p471 325136221 5368709120 1421 5368709120 (Ns312p1666 (RS313to324.d50 qz60 qz78 qz266) RS313to324.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable abbrev qz268 := qz547

noncomputable def Ns312p1674 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz268 (@BSN.thirtyTwoPi_le_dec qz60 634599 1000 qz63 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz265 qz267 (Ns312p1665 rfl rfl) (Ns312p1667 rfl rfl)) (Ns312p1668 qz9 qz63 rfl rfl rfl rfl (Ns312p1670 rfl)) (Ns312p1671 qz9 qz81 rfl rfl rfl rfl (Ns312p1673 rfl)) 

noncomputable abbrev qz549 := (RS313to324.d3 qz617 qz625 (@Enclosure.dec_le_dec qz617 qz625 636640 1000 637660 1000 qz620 qz628 rfl rfl rfl))

noncomputable abbrev qz269 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz549)

noncomputable def Ns312p1675 := @Enclosure.Real.IsNear.of_eq qz269 (hardyZApproximantRS₀ qz78) Bool.false 25306016193483694032653 9444732965739290427392 8822831630086185712339 Ns312p471 

noncomputable abbrev qz550 := (@Enclosure.dec_le_dec qz617 qz625 636640 1000 637660 1000 qz620 qz628 rfl rfl rfl)

noncomputable abbrev qz270 := qz550

noncomputable def Ns312p1676 := @Enclosure.Real.IsNear.pos_val qz269 25306016193483694032653 9444732965739290427392 8822831630086185712339 Ns312p471 (Ns312p1675 (RS313to324.d4 qz78 qz96 qz270) RS313to324.d54) rfl 

noncomputable abbrev qz271 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz549)

noncomputable def Ns312p1677 := @Enclosure.Real.IsNear.of_eq qz271 (hardyZApproximantRS₀ qz96) Bool.true 1004517432905003780035 4722366482869645213696 78898874398057614205379 Ns312p591 

noncomputable def Ns312p1678 := @Enclosure.Real.IsNear.neg_val qz271 1004517432905003780035 4722366482869645213696 78898874398057614205379 Ns312p591 (Ns312p1677 (RS313to324.d50 qz78 qz96 qz270) RS313to324.d55) rfl 

noncomputable def Ns312p1679 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz269 qz4 qz78 631875 1000 636640 1000 

noncomputable def Ns312p1680 := @Enclosure.norm_gt_of_isNear qz269 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 25306016193483694032653 9444732965739290427392 8822831630086185712339 

noncomputable def Ns312p1681 := @Ns312p1680 Ns312p471 325136221 5368709120 1421 5368709120 (Ns312p1675 (RS313to324.d4 qz78 qz96 qz270) RS313to324.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable def Ns312p1682 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz271 qz4 qz96 631875 1000 637660 1000 

noncomputable def Ns312p1683 := @Enclosure.norm_gt_of_isNear qz271 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1004517432905003780035 4722366482869645213696 78898874398057614205379 

noncomputable def Ns312p1684 := @Ns312p1683 Ns312p591 325136221 5368709120 1421 5368709120 (Ns312p1677 (RS313to324.d50 qz78 qz96 qz270) RS313to324.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable abbrev qz272 := qz549

noncomputable def Ns312p1685 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz272 (@BSN.thirtyTwoPi_le_dec qz78 636640 1000 qz81 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz269 qz271 (Ns312p1676 rfl rfl) (Ns312p1678 rfl rfl)) (Ns312p1679 qz9 qz81 rfl rfl rfl rfl (Ns312p1681 rfl)) (Ns312p1682 qz9 qz99 rfl rfl rfl rfl (Ns312p1684 rfl)) 

noncomputable abbrev qz551 := (RS313to324.d3 qz625 qz633 (@Enclosure.dec_le_dec qz625 qz633 637660 1000 638340 1000 qz628 qz636 rfl rfl rfl))

noncomputable abbrev qz273 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz551)

noncomputable def Ns312p1686 := @Enclosure.Real.IsNear.of_eq qz273 (hardyZApproximantRS₀ qz96) Bool.true 1004517432905003780035 4722366482869645213696 78898874398057614205379 Ns312p591 

noncomputable abbrev qz552 := (@Enclosure.dec_le_dec qz625 qz633 637660 1000 638340 1000 qz628 qz636 rfl rfl rfl)

noncomputable abbrev qz274 := qz552

noncomputable def Ns312p1687 := @Enclosure.Real.IsNear.neg_val qz273 1004517432905003780035 4722366482869645213696 78898874398057614205379 Ns312p591 (Ns312p1686 (RS313to324.d4 qz96 qz114 qz274) RS313to324.d55) rfl 

noncomputable abbrev qz275 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz551)

noncomputable def Ns312p1688 := @Enclosure.Real.IsNear.of_eq qz275 (hardyZApproximantRS₀ qz114) Bool.false 1301562025699792675939 2361183241434822606848 92166870879982536740853 Ns312p705 

noncomputable def Ns312p1689 := @Enclosure.Real.IsNear.pos_val qz275 1301562025699792675939 2361183241434822606848 92166870879982536740853 Ns312p705 (Ns312p1688 (RS313to324.d50 qz96 qz114 qz274) RS313to324.d56) rfl 

noncomputable def Ns312p1690 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz273 qz4 qz96 631875 1000 637660 1000 

noncomputable def Ns312p1691 := @Enclosure.norm_gt_of_isNear qz273 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1004517432905003780035 4722366482869645213696 78898874398057614205379 

noncomputable def Ns312p1692 := @Ns312p1691 Ns312p591 325136221 5368709120 1421 5368709120 (Ns312p1686 (RS313to324.d4 qz96 qz114 qz274) RS313to324.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable def Ns312p1693 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz275 qz4 qz114 631875 1000 638340 1000 

noncomputable def Ns312p1694 := @Enclosure.norm_gt_of_isNear qz275 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1301562025699792675939 2361183241434822606848 92166870879982536740853 

noncomputable def Ns312p1695 := @Ns312p1694 Ns312p705 325136221 5368709120 1421 5368709120 (Ns312p1688 (RS313to324.d50 qz96 qz114 qz274) RS313to324.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable abbrev qz276 := qz551

noncomputable def Ns312p1696 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz276 (@BSN.thirtyTwoPi_le_dec qz96 637660 1000 qz99 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz273 qz275 (Ns312p1687 rfl rfl) (Ns312p1689 rfl rfl)) (Ns312p1690 qz9 qz99 rfl rfl rfl rfl (Ns312p1692 rfl)) (Ns312p1693 qz9 qz117 rfl rfl rfl rfl (Ns312p1695 rfl)) 

noncomputable abbrev qz553 := (RS313to324.d3 qz633 qz641 (@Enclosure.dec_le_dec qz633 qz641 638340 1000 640039 1000 qz636 qz644 rfl rfl rfl))

noncomputable abbrev qz277 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz553)

noncomputable def Ns312p1697 := @Enclosure.Real.IsNear.of_eq qz277 (hardyZApproximantRS₀ qz114) Bool.false 1301562025699792675939 2361183241434822606848 92166870879982536740853 Ns312p705 

noncomputable abbrev qz554 := (@Enclosure.dec_le_dec qz633 qz641 638340 1000 640039 1000 qz636 qz644 rfl rfl rfl)

noncomputable abbrev qz278 := qz554

noncomputable def Ns312p1698 := @Enclosure.Real.IsNear.pos_val qz277 1301562025699792675939 2361183241434822606848 92166870879982536740853 Ns312p705 (Ns312p1697 (RS313to324.d4 qz114 qz132 qz278) RS313to324.d56) rfl 

noncomputable abbrev qz279 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz553)

noncomputable def Ns312p1699 := @Enclosure.Real.IsNear.of_eq qz279 (hardyZApproximantRS₀ qz132) Bool.true 2944760490561049856323 1180591620717411303424 184836776598121289456637 Ns312p824 

noncomputable def Ns312p1700 := @Enclosure.Real.IsNear.neg_val qz279 2944760490561049856323 1180591620717411303424 184836776598121289456637 Ns312p824 (Ns312p1699 (RS313to324.d50 qz114 qz132 qz278) RS313to324.d57) rfl 

noncomputable def Ns312p1701 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz277 qz4 qz114 631875 1000 638340 1000 

noncomputable def Ns312p1702 := @Enclosure.norm_gt_of_isNear qz277 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1301562025699792675939 2361183241434822606848 92166870879982536740853 

noncomputable def Ns312p1703 := @Ns312p1702 Ns312p705 325136221 5368709120 1421 5368709120 (Ns312p1697 (RS313to324.d4 qz114 qz132 qz278) RS313to324.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable def Ns312p1704 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz279 qz4 qz132 631875 1000 640039 1000 

noncomputable def Ns312p1705 := @Enclosure.norm_gt_of_isNear qz279 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2944760490561049856323 1180591620717411303424 184836776598121289456637 

noncomputable def Ns312p1706 := @Ns312p1705 Ns312p824 325136221 5368709120 1421 5368709120 (Ns312p1699 (RS313to324.d50 qz114 qz132 qz278) RS313to324.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable abbrev qz280 := qz553

noncomputable def Ns312p1707 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz280 (@BSN.thirtyTwoPi_le_dec qz114 638340 1000 qz117 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz277 qz279 (Ns312p1698 rfl rfl) (Ns312p1700 rfl rfl)) (Ns312p1701 qz9 qz117 rfl rfl rfl rfl (Ns312p1703 rfl)) (Ns312p1704 qz9 qz135 rfl rfl rfl rfl (Ns312p1706 rfl)) 

noncomputable abbrev qz555 := (RS313to324.d3 qz641 qz649 (@Enclosure.dec_le_dec qz641 qz649 640039 1000 641398 1000 qz644 qz652 rfl rfl rfl))

noncomputable abbrev qz281 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz555)

noncomputable def Ns312p1708 := @Enclosure.Real.IsNear.of_eq qz281 (hardyZApproximantRS₀ qz132) Bool.true 2944760490561049856323 1180591620717411303424 184836776598121289456637 Ns312p824 

noncomputable abbrev qz556 := (@Enclosure.dec_le_dec qz641 qz649 640039 1000 641398 1000 qz644 qz652 rfl rfl rfl)

noncomputable abbrev qz282 := qz556

noncomputable def Ns312p1709 := @Enclosure.Real.IsNear.neg_val qz281 2944760490561049856323 1180591620717411303424 184836776598121289456637 Ns312p824 (Ns312p1708 (RS313to324.d4 qz132 qz150 qz282) RS313to324.d57) rfl 

noncomputable abbrev qz283 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz555)

noncomputable def Ns312p1710 := @Enclosure.Real.IsNear.of_eq qz283 (hardyZApproximantRS₀ qz150) Bool.false 8520239303864009573965 4722366482869645213696 555839726942703154419899 Ns312p943 

noncomputable def Ns312p1711 := @Enclosure.Real.IsNear.pos_val qz283 8520239303864009573965 4722366482869645213696 555839726942703154419899 Ns312p943 (Ns312p1710 (RS313to324.d50 qz132 qz150 qz282) RS313to324.d58) rfl 

noncomputable def Ns312p1712 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz281 qz4 qz132 631875 1000 640039 1000 

noncomputable def Ns312p1713 := @Enclosure.norm_gt_of_isNear qz281 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2944760490561049856323 1180591620717411303424 184836776598121289456637 

noncomputable def Ns312p1714 := @Ns312p1713 Ns312p824 325136221 5368709120 1421 5368709120 (Ns312p1708 (RS313to324.d4 qz132 qz150 qz282) RS313to324.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable def Ns312p1715 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz283 qz4 qz150 631875 1000 641398 1000 

noncomputable def Ns312p1716 := @Enclosure.norm_gt_of_isNear qz283 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 8520239303864009573965 4722366482869645213696 555839726942703154419899 

noncomputable def Ns312p1717 := @Ns312p1716 Ns312p943 325136221 5368709120 1421 5368709120 (Ns312p1710 (RS313to324.d50 qz132 qz150 qz282) RS313to324.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable abbrev qz284 := qz555

noncomputable def Ns312p1718 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz132 640039 1000 qz135 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz281 qz283 (Ns312p1709 rfl rfl) (Ns312p1711 rfl rfl)) (Ns312p1712 qz9 qz135 rfl rfl rfl rfl (Ns312p1714 rfl)) (Ns312p1715 qz9 qz153 rfl rfl rfl rfl (Ns312p1717 rfl)) 

noncomputable abbrev qz557 := (RS313to324.d3 qz649 qz657 (@Enclosure.dec_le_dec qz649 qz657 641398 1000 642756 1000 qz652 qz660 rfl rfl rfl))

noncomputable abbrev qz285 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz557)

noncomputable def Ns312p1719 := @Enclosure.Real.IsNear.of_eq qz285 (hardyZApproximantRS₀ qz150) Bool.false 8520239303864009573965 4722366482869645213696 555839726942703154419899 Ns312p943 

noncomputable abbrev qz558 := (@Enclosure.dec_le_dec qz649 qz657 641398 1000 642756 1000 qz652 qz660 rfl rfl rfl)

noncomputable abbrev qz286 := qz558

noncomputable def Ns312p1720 := @Enclosure.Real.IsNear.pos_val qz285 8520239303864009573965 4722366482869645213696 555839726942703154419899 Ns312p943 (Ns312p1719 (RS313to324.d4 qz150 qz168 qz286) RS313to324.d58) rfl 

noncomputable abbrev qz287 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz557)

noncomputable def Ns312p1721 := @Enclosure.Real.IsNear.of_eq qz287 (hardyZApproximantRS₀ qz168) Bool.true 20847788684121206730261 9444732965739290427392 Ns312p1063 Ns312p75 

noncomputable def Ns312p1722 := @Enclosure.Real.IsNear.neg_val qz287 20847788684121206730261 9444732965739290427392 Ns312p1063 Ns312p75 (Ns312p1721 (RS313to324.d50 qz150 qz168 qz286) RS313to324.d59) rfl 

noncomputable def Ns312p1723 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz285 qz4 qz150 631875 1000 641398 1000 

noncomputable def Ns312p1724 := @Enclosure.norm_gt_of_isNear qz285 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 8520239303864009573965 4722366482869645213696 555839726942703154419899 

noncomputable def Ns312p1725 := @Ns312p1724 Ns312p943 325136221 5368709120 1421 5368709120 (Ns312p1719 (RS313to324.d4 qz150 qz168 qz286) RS313to324.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable def Ns312p1726 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz287 qz4 qz168 631875 1000 642756 1000 

noncomputable def Ns312p1727 := @Enclosure.norm_gt_of_isNear qz287 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 20847788684121206730261 9444732965739290427392 Ns312p1063 

noncomputable def Ns312p1728 := @Ns312p1727 Ns312p75 325136221 5368709120 1421 5368709120 (Ns312p1721 (RS313to324.d50 qz150 qz168 qz286) RS313to324.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable abbrev qz288 := qz557

noncomputable def Ns312p1729 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz150 641398 1000 qz153 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz285 qz287 (Ns312p1720 rfl rfl) (Ns312p1722 rfl rfl)) (Ns312p1723 qz9 qz153 rfl rfl rfl rfl (Ns312p1725 rfl)) (Ns312p1726 qz9 qz171 rfl rfl rfl rfl (Ns312p1728 rfl)) 

noncomputable abbrev qz703 := (@Enclosure.dec_le_dec qz748 qz752 642756 1000 644113 1000 (@Eq.refl Real qz748) (@Eq.refl Real qz752) rfl rfl rfl)

noncomputable abbrev qz559 := (RS313to324.d3 qz657 qz665 qz703)

noncomputable abbrev qz289 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz559)

noncomputable def Ns312p1730 := @Enclosure.Real.IsNear.of_eq qz289 (hardyZApproximantRS₀ qz168) Bool.true 20847788684121206730261 9444732965739290427392 Ns312p1063 Ns312p75 

noncomputable abbrev qz560 := qz703

noncomputable abbrev qz290 := qz560

noncomputable def Ns312p1731 := @Enclosure.Real.IsNear.neg_val qz289 20847788684121206730261 9444732965739290427392 Ns312p1063 Ns312p75 (Ns312p1730 (RS313to324.d4 qz168 qz186 qz290) RS313to324.d59) rfl 

noncomputable abbrev qz291 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz559)

noncomputable def Ns312p1732 := @Enclosure.Real.IsNear.of_eq qz291 (hardyZApproximantRS₀ qz186) Bool.false 17903868070615419745715 4722366482869645213696 111677994611109900834641 Ns312p1181 

noncomputable def Ns312p1733 := @Enclosure.Real.IsNear.pos_val qz291 17903868070615419745715 4722366482869645213696 111677994611109900834641 Ns312p1181 (Ns312p1732 (RS313to324.d50 qz168 qz186 qz290) RS313to324.d60) rfl 

noncomputable def Ns312p1734 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz289 qz4 qz168 631875 1000 642756 1000 

noncomputable def Ns312p1735 := @Enclosure.norm_gt_of_isNear qz289 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 20847788684121206730261 9444732965739290427392 Ns312p1063 

noncomputable def Ns312p1736 := @Ns312p1735 Ns312p75 325136221 5368709120 1421 5368709120 (Ns312p1730 (RS313to324.d4 qz168 qz186 qz290) RS313to324.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable def Ns312p1737 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz291 qz4 qz186 631875 1000 644113 1000 

noncomputable def Ns312p1738 := @Enclosure.norm_gt_of_isNear qz291 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 17903868070615419745715 4722366482869645213696 111677994611109900834641 

noncomputable def Ns312p1739 := @Ns312p1738 Ns312p1181 325136221 5368709120 1421 5368709120 (Ns312p1732 (RS313to324.d50 qz168 qz186 qz290) RS313to324.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable abbrev qz292 := qz559

noncomputable def Ns312p1740 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz168 642756 1000 qz171 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz289 qz291 (Ns312p1731 rfl rfl) (Ns312p1733 rfl rfl)) (Ns312p1734 qz9 qz171 rfl rfl rfl rfl (Ns312p1736 rfl)) (Ns312p1737 qz9 qz189 rfl rfl rfl rfl (Ns312p1739 rfl)) 

noncomputable abbrev qz704 := (@Enclosure.dec_le_dec qz752 qz756 644113 1000 645470 1000 (@Eq.refl Real qz752) qz759 rfl rfl rfl)

noncomputable abbrev qz561 := (RS313to324.d3 qz665 qz673 qz704)

noncomputable abbrev qz293 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz561)

noncomputable def Ns312p1741 := @Enclosure.Real.IsNear.of_eq qz293 (hardyZApproximantRS₀ qz186) Bool.false 17903868070615419745715 4722366482869645213696 111677994611109900834641 Ns312p1181 

noncomputable abbrev qz562 := qz704

noncomputable abbrev qz294 := qz562

noncomputable def Ns312p1742 := @Enclosure.Real.IsNear.pos_val qz293 17903868070615419745715 4722366482869645213696 111677994611109900834641 Ns312p1181 (Ns312p1741 (RS313to324.d4 qz186 qz204 qz294) RS313to324.d60) rfl 

noncomputable abbrev qz295 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz561)

noncomputable def Ns312p1743 := @Enclosure.Real.IsNear.of_eq qz295 (hardyZApproximantRS₀ qz204) Bool.true 1249154938287115575603 590295810358705651712 209920908921124584025159 Ns312p1296 

noncomputable def Ns312p1744 := @Enclosure.Real.IsNear.neg_val qz295 1249154938287115575603 590295810358705651712 209920908921124584025159 Ns312p1296 (Ns312p1743 (RS313to324.d50 qz186 qz204 qz294) RS313to324.d61) rfl 

noncomputable def Ns312p1745 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz293 qz4 qz186 631875 1000 644113 1000 

noncomputable def Ns312p1746 := @Enclosure.norm_gt_of_isNear qz293 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 17903868070615419745715 4722366482869645213696 111677994611109900834641 

noncomputable def Ns312p1747 := @Ns312p1746 Ns312p1181 325136221 5368709120 1421 5368709120 (Ns312p1741 (RS313to324.d4 qz186 qz204 qz294) RS313to324.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable def Ns312p1748 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz295 qz4 qz204 631875 1000 645470 1000 

noncomputable def Ns312p1749 := @Enclosure.norm_gt_of_isNear qz295 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1249154938287115575603 590295810358705651712 209920908921124584025159 

noncomputable def Ns312p1750 := @Ns312p1749 Ns312p1296 325136221 5368709120 1421 5368709120 (Ns312p1743 (RS313to324.d50 qz186 qz204 qz294) RS313to324.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable abbrev qz296 := qz561

noncomputable def Ns312p1751 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz296 (@BSN.thirtyTwoPi_le_dec qz186 644113 1000 qz189 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz293 qz295 (Ns312p1742 rfl rfl) (Ns312p1744 rfl rfl)) (Ns312p1745 qz9 qz189 rfl rfl rfl rfl (Ns312p1747 rfl)) (Ns312p1748 qz9 qz209 rfl rfl rfl rfl (Ns312p1750 rfl)) 

noncomputable abbrev qz705 := (@Enclosure.dec_le_dec qz756 qz761 645470 1000 646826 1000 qz759 qz764 rfl rfl rfl)

noncomputable abbrev qz563 := (RS313to324.d3 qz673 qz683 qz705)

noncomputable abbrev qz297 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz563)

noncomputable def Ns312p1752 := @Enclosure.Real.IsNear.of_eq qz297 (hardyZApproximantRS₀ qz204) Bool.true 1249154938287115575603 590295810358705651712 209920908921124584025159 Ns312p1296 

noncomputable abbrev qz564 := qz705

noncomputable abbrev qz298 := qz564

noncomputable def Ns312p1753 := @Enclosure.Real.IsNear.neg_val qz297 1249154938287115575603 590295810358705651712 209920908921124584025159 Ns312p1296 (Ns312p1752 (RS313to324.d4 qz204 qz223 qz298) RS313to324.d61) rfl 

noncomputable abbrev qz299 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz563)

noncomputable def Ns312p1754 := @Enclosure.Real.IsNear.of_eq qz299 (hardyZApproximantRS₀ qz223) Bool.false 970811622897488667997 590295810358705651712 112216837611037682827093 Ns312p1181 

noncomputable def Ns312p1755 := @Enclosure.Real.IsNear.pos_val qz299 970811622897488667997 590295810358705651712 112216837611037682827093 Ns312p1181 (Ns312p1754 (RS313to324.d50 qz204 qz223 qz298) RS313to324.d62) rfl 

noncomputable def Ns312p1756 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz297 qz4 qz204 631875 1000 645470 1000 

noncomputable def Ns312p1757 := @Enclosure.norm_gt_of_isNear qz297 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1249154938287115575603 590295810358705651712 209920908921124584025159 

noncomputable def Ns312p1758 := @Ns312p1757 Ns312p1296 325136221 5368709120 1421 5368709120 (Ns312p1752 (RS313to324.d4 qz204 qz223 qz298) RS313to324.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable def Ns312p1759 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz299 qz4 qz223 631875 1000 646826 1000 

noncomputable def Ns312p1760 := @Enclosure.norm_gt_of_isNear qz299 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 970811622897488667997 590295810358705651712 112216837611037682827093 

noncomputable def Ns312p1761 := @Ns312p1760 Ns312p1181 325136221 5368709120 1421 5368709120 (Ns312p1754 (RS313to324.d50 qz204 qz223 qz298) RS313to324.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable abbrev qz300 := qz563

noncomputable def Ns312p1762 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz204 645470 1000 qz209 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz297 qz299 (Ns312p1753 rfl rfl) (Ns312p1755 rfl rfl)) (Ns312p1756 qz9 qz209 rfl rfl rfl rfl (Ns312p1758 rfl)) (Ns312p1759 qz9 qz226 rfl rfl rfl rfl (Ns312p1761 rfl)) 

noncomputable abbrev qz771 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 646826 1000) (Enclosure.sfrac Bool.false 648182 1000) 646826 1000 648182 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 646826 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 648182 1000)) rfl rfl rfl)

noncomputable abbrev qz706 := qz771

noncomputable abbrev qz565 := (RS313to324.d3 qz683 qz693 qz706)

noncomputable abbrev qz301 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz565)

noncomputable def Ns312p1763 := @Enclosure.Real.IsNear.of_eq qz301 (hardyZApproximantRS₀ qz223) Bool.false 970811622897488667997 590295810358705651712 112216837611037682827093 Ns312p1181 

noncomputable abbrev qz566 := qz706

noncomputable abbrev qz302 := qz566

noncomputable def Ns312p1764 := @Enclosure.Real.IsNear.pos_val qz301 970811622897488667997 590295810358705651712 112216837611037682827093 Ns312p1181 (Ns312p1763 (RS313to324.d4 qz223 qz240 qz302) RS313to324.d62) rfl 

noncomputable abbrev qz303 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz565)

noncomputable def Ns312p1765 := @Enclosure.Real.IsNear.of_eq qz303 (hardyZApproximantRS₀ qz240) Bool.true 490605271431258893031 590295810358705651712 8037475964256405662341 Ns312p1527 

noncomputable def Ns312p1766 := @Enclosure.Real.IsNear.neg_val qz303 490605271431258893031 590295810358705651712 8037475964256405662341 Ns312p1527 (Ns312p1765 (RS313to324.d50 qz223 qz240 qz302) RS313to324.d63) rfl 

noncomputable def Ns312p1767 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz301 qz4 qz223 631875 1000 646826 1000 

noncomputable def Ns312p1768 := @Enclosure.norm_gt_of_isNear qz301 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 970811622897488667997 590295810358705651712 112216837611037682827093 

noncomputable def Ns312p1769 := @Ns312p1768 Ns312p1181 325136221 5368709120 1421 5368709120 (Ns312p1763 (RS313to324.d4 qz223 qz240 qz302) RS313to324.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable def Ns312p1770 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz303 qz4 qz240 631875 1000 648182 1000 

noncomputable def Ns312p1771 := @Enclosure.norm_gt_of_isNear qz303 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 490605271431258893031 590295810358705651712 8037475964256405662341 

noncomputable def Ns312p1772 := @Ns312p1771 Ns312p1527 325136221 5368709120 1421 5368709120 (Ns312p1765 (RS313to324.d50 qz223 qz240 qz302) RS313to324.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 325136221 5368709120 1421 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS313to324.d52) rfl rfl rfl rfl 

noncomputable abbrev qz304 := qz565

noncomputable def Ns312p1773 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz304 (@BSN.thirtyTwoPi_le_dec qz223 646826 1000 qz226 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz301 qz303 (Ns312p1764 rfl rfl) (Ns312p1766 rfl rfl)) (Ns312p1767 qz9 qz226 rfl rfl rfl rfl (Ns312p1769 rfl)) (Ns312p1770 qz9 qz243 rfl rfl rfl rfl (Ns312p1772 rfl)) 

noncomputable def Ns312p1774 := @List.cons RS313to324.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns312p1762)) (@List.cons RS313to324.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz304 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz304) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz304) Ns312p1773)) (@List.nil RS313to324.d0)) 

noncomputable def Ns312p1775 := @List.cons RS313to324.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns312p1740)) (@List.cons RS313to324.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns312p1751)) Ns312p1774) 

noncomputable def Ns312p1776 := @List.cons RS313to324.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns312p1718)) (@List.cons RS313to324.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns312p1729)) Ns312p1775) 

noncomputable def Ns312p1777 := @List.cons RS313to324.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz276 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz276) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz276) Ns312p1696)) (@List.cons RS313to324.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz280 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz280) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz280) Ns312p1707)) Ns312p1776) 

noncomputable def Ns312p1778 := @List.cons RS313to324.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz268 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz268) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz268) Ns312p1674)) (@List.cons RS313to324.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz272 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz272) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz272) Ns312p1685)) Ns312p1777) 

noncomputable def Ns312p1779 := @List.cons RS313to324.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz260 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz260) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz260) Ns312p1652)) (@List.cons RS313to324.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz264 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz264) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz264) Ns312p1663)) Ns312p1778) 

noncomputable abbrev qz567 := (RS313to324.d2 qz657 qz665 qz703)

noncomputable abbrev qz707 := (RS313to324.d2 qz756 qz761 (@Enclosure.dec_le_dec qz756 qz761 645470 1000 646826 1000 qz759 qz764 rfl rfl rfl))

noncomputable abbrev qz708 := (@List.cons RS313to324.d1 (RS313to324.d2 qz761 qz766 qz771) (@List.nil RS313to324.d1))

noncomputable abbrev qz568 := (@List.cons RS313to324.d1 (RS313to324.d2 qz665 qz673 qz704) (@List.cons RS313to324.d1 qz707 qz708))

noncomputable abbrev qz305 := (@List.cons RS313to324.d1 (RS313to324.d2 qz468 qz481 qz558) (@List.cons RS313to324.d1 qz567 qz568))

noncomputable def Ns312p1780 := @List.cons RS313to324.d1 (RS313to324.d2 qz114 qz132 qz278) (@List.cons RS313to324.d1 (RS313to324.d2 qz132 qz150 qz282) qz305) 

noncomputable abbrev qz306 := (RS313to324.d2 qz429 qz442 qz552)

noncomputable def Ns312p1781 := @List.IsChain.cons_cons RS313to324.d1 RS313to324.d64 qz306 (RS313to324.d2 qz114 qz132 qz278) (@List.cons RS313to324.d1 (RS313to324.d2 qz132 qz150 qz282) qz305) 

noncomputable def Ns312p1782 := @List.IsChain.cons_cons RS313to324.d1 RS313to324.d64 (RS313to324.d2 qz114 qz132 qz278) (RS313to324.d2 qz132 qz150 qz282) qz305 (@Enclosure.dec_le_dec qz132 qz132 640039 1000 640039 1000 qz135 qz135 rfl rfl rfl) 

noncomputable abbrev qz307 := (RS313to324.d2 qz468 qz481 qz558)

noncomputable abbrev qz308 := qz567

noncomputable abbrev qz309 := qz568

noncomputable abbrev qz569 := (RS313to324.d2 qz665 qz673 qz704)

noncomputable abbrev qz310 := qz569

noncomputable abbrev qz570 := (@List.cons RS313to324.d1 qz707 qz708)

noncomputable abbrev qz311 := qz570

noncomputable abbrev qz571 := qz707

noncomputable abbrev qz312 := qz571

noncomputable abbrev qz572 := qz708

noncomputable abbrev qz313 := qz572

noncomputable abbrev qz709 := (RS313to324.d2 qz761 qz766 qz771)

noncomputable abbrev qz573 := qz709

noncomputable abbrev qz314 := qz573

noncomputable def Ns312p1783 := @List.IsChain.cons_cons RS313to324.d1 RS313to324.d64 qz307 qz308 qz309 (@Enclosure.dec_le_dec qz168 qz168 642756 1000 642756 1000 qz171 qz171 rfl rfl rfl) (@List.IsChain.cons_cons RS313to324.d1 RS313to324.d64 qz308 qz310 qz311 (@Enclosure.dec_le_dec qz186 qz186 644113 1000 644113 1000 qz189 qz189 rfl rfl rfl) (@List.IsChain.cons_cons RS313to324.d1 RS313to324.d64 qz310 qz312 qz313 (@Enclosure.dec_le_dec qz204 qz204 645470 1000 645470 1000 qz209 qz209 rfl rfl rfl) (@List.IsChain.cons_cons RS313to324.d1 RS313to324.d64 qz312 qz314 (@List.nil RS313to324.d1) (@Enclosure.dec_le_dec qz223 qz223 646826 1000 646826 1000 qz226 qz226 rfl rfl rfl) (@List.IsChain.singleton RS313to324.d1 RS313to324.d64 qz314)))) 

noncomputable abbrev qz315 := (@List.cons RS313to324.d1 qz567 qz568)

noncomputable def Ns312p1784 := @List.IsChain.cons_cons RS313to324.d1 RS313to324.d64 (RS313to324.d2 qz132 qz150 qz282) qz307 qz315 (@Enclosure.dec_le_dec qz150 qz150 641398 1000 641398 1000 qz153 qz153 rfl rfl rfl) Ns312p1783 

noncomputable def Ns312p1785 := @List.IsChain.cons_cons RS313to324.d1 RS313to324.d64 (RS313to324.d2 qz4 qz33 qz258) (RS313to324.d2 qz33 qz60 qz262) (@List.cons RS313to324.d1 (RS313to324.d2 qz60 qz78 qz266) (@List.cons RS313to324.d1 (RS313to324.d2 qz78 qz96 qz270) (@List.cons RS313to324.d1 qz306 Ns312p1780))) (@Enclosure.dec_le_dec qz33 qz33 633237 1000 633237 1000 qz36 qz36 rfl rfl rfl) (@List.IsChain.cons_cons RS313to324.d1 RS313to324.d64 (RS313to324.d2 qz33 qz60 qz262) (RS313to324.d2 qz60 qz78 qz266) (@List.cons RS313to324.d1 (RS313to324.d2 qz78 qz96 qz270) (@List.cons RS313to324.d1 qz306 Ns312p1780)) (@Enclosure.dec_le_dec qz60 qz60 634599 1000 634599 1000 qz63 qz63 rfl rfl rfl) (@List.IsChain.cons_cons RS313to324.d1 RS313to324.d64 (RS313to324.d2 qz60 qz78 qz266) (RS313to324.d2 qz78 qz96 qz270) (@List.cons RS313to324.d1 qz306 Ns312p1780) (@Enclosure.dec_le_dec qz78 qz78 636640 1000 636640 1000 qz81 qz81 rfl rfl rfl) (@List.IsChain.cons_cons RS313to324.d1 RS313to324.d64 (RS313to324.d2 qz78 qz96 qz270) qz306 Ns312p1780 (@Enclosure.dec_le_dec qz96 qz96 637660 1000 637660 1000 qz99 qz99 rfl rfl rfl) (Ns312p1781 (@Enclosure.dec_le_dec qz114 qz114 638340 1000 638340 1000 qz117 qz117 rfl rfl rfl) (Ns312p1782 Ns312p1784))))) 

noncomputable abbrev qz574 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz575 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns312p1779 Ns312p1785)

noncomputable abbrev qz576 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns312p1779 Ns312p1785))

theorem RS313to324.d65 : Zeta.Certificates.BatchSpec 12 631875 1000 648182 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz574 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 12) (And (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz574 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz574 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz240)))) qz575 (@And.intro (@Eq Nat (@List.length qz574 qz576) 12) (And (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz574 qz576)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz574 qz576)) (@Option.some Real qz240))) (@Eq.refl Nat 12) (@And.intro (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz574 qz576)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz574 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz574 qz576)) (@Option.some Real qz240)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz240))))

theorem solution : Zeta.Certificates.BatchSpec 12 631875 1000 648182 1000 := RS313to324.d65
#print axioms solution
#check solution
