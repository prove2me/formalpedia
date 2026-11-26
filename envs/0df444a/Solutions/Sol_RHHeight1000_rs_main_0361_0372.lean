-- Prove2me | solution 1 for RHHeight1000.rs_main_0361_0372
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:37:40.765273+00:00
-- url     : https://prove2.me/submissions/702d2025-85a1-434b-bdc2-5dbfc66a2a0e

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

noncomputable def RS361to372.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS361to372.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS361to372.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS361to372.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS361to372.d2 a b h 

theorem RS361to372.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS361to372.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS361to372.d3 a b h)) 

noncomputable def Ns360p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns360p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns360p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns360p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns360p0 Ns360p1 Ns360p2 Ns360p1 307286088 268435456 1 84640000 307286088 268435456 1 84640000 153643044 134217728 2 134217728 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns360p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns360p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns360p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns360p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns360p8 := nat_lit 167537954069964697925743468333314178468718661948561187618563575975392713740913527107727581163208035826476740967700482432525301063254420572874757592895482956004842597348203117269212172556829666669574421653274845612596416189641484794702002223261246862056663160605878293700340502480877986491439034432953223334258717026053687371824342493299510132312376251152844516906794910572262907940062760396663270105627554083664899640691826599584783763757814813433640133591539937449421955686657622469485188711283992428713614179785896055117030632677201478317872225272595773536303110412989181984739022579128493081560758017763072115692678596043664844667144619713966763611484179303468167142547433165016751768184247559143333542643815355903304572487929375 

noncomputable def Ns360p9 := nat_lit 17907736863639440849562382641391758203535690054199171304015283257442503423240620144819838407313611418261944516207295868563739563278604805791797182761045687776939279949642059267526948014748996956777332184087524644234759874591635243045607722412471722018588244283882362848653445974523544951031470230725674276297342086185092985546835544820091590454230569790847977790484558207349923322458845585052164126500435851662252152223728079705692133047658564669873831757357628115566356048471439549797170528303905720944834637690907185213991407615774042056720704508980680095051114888612186461088301140868302968264130481206655302741383410655080008578156649725227045954510069588220729495895148666460653631514375880874422615237249871322129146554264800 

noncomputable def Ns360p10 := nat_lit 55164646516618494962085419356369025784335016154267579706247610053041231157772817011486486467101704279863254798704146668052276438579475100451766223896220272709675360577301802978530276301158911649961092601279696986330335403118086533522541958716560166657634553390183479955483588238249446822384543398154260439705049143284278540285021213103458182619368483938376641172730818250587232036579805400979202432024046862170503602539341971086573372247299262086029843105216008583038025403798224342134620653974939981235680083776396058604459065501719125356177784467570909658245422960948263734871602033841948787585406240093531041217463298165642337705122589129757920995868559518021463265498464182174549661735402095023640043996665674913376875 

noncomputable def Ns360p11 := BSN.log_dyadic_bound Ns360p6 Ns360p7 15 14 Ns360p8 268435456 84640000 Ns360p9 Ns360p10 307286088 Ns360p4 Ns360p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns360p6) (BSN.artanhQ Ns360p7) 0 14 Ns360p9 Ns360p8 Ns360p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns360p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns360p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns360p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns360p15 := nat_lit 167537954069966963268140139327979112712430526945422964221951926912223381190141639739514890494967825643602350173964944759828460064784215684919760383437959917620844610857567326816719640593037578236900835917107172977527392439886629774248115214831425484905681376157923696414882114961796820014026232307332015059110330001516939277521159573995394989771587717775443426002499543257897301982481613760098955890450106043861450716722534643739571053080256776912576113428445260435254713579381797931690799491102381747484553243404562568585572234105168360737285205910186933811836504830286397217473365026331067977496463917110493303316865058355012304571237619413071097245713770677768486493924969821719264401216877841676972336093778875903304572487929375 

noncomputable def Ns360p16 := nat_lit 17907736863639702486765313263906285882628955290251965205176678923530777959693011244026517850256414903756943142851250712732214241881959351517241344993825585048584379523049477943740273636414656012170312373198803997844271825165684859407921203335666024680974464565759223251918458072775203410604089667122984485578465112081892102496937045858735135721609691262763214794451343726045584198128451069547586972080574568545086657023793200560105564573365716615162566961587407171758966967827997201380802107846920231945878242774600967607639551032178207663699700360114112068650063802902647517702890145150192721997537569966984346993833704449560383184487996362781528900358997452380059737141488304159449328022742959995775545894292303322129146554264800 

noncomputable def Ns360p17 := nat_lit 55164646516619937449385584700664297411818070214438189962773666351465523500358685366424500506990751111492356556545320273548942244833046464529601272738875466881799996765940232256588350019911833156887888425998391295014189841212513610526066550079316346993943774342801096070086869790972589246312728227659319758310961510342377923950694747797317942483020440897997204711883064182772445608288320382376665481938194224815739627075458138172195220395246294556718284728034954178416253903237031389214179719385823921869528509431462690683227358218086518156757026652846493301460983550768858152506145788622699720737745394141184245149692548799188169247529408201840608223422296381897323845616153036586108326210125693898345963996665674913376875 

noncomputable def Ns360p18 := BSN.log_dyadic_bound Ns360p13 Ns360p14 15 14 Ns360p15 268435456 84640000 Ns360p16 Ns360p17 307286088 Ns360p12 Ns360p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns360p13) (BSN.artanhQ Ns360p14) 0 14 Ns360p16 Ns360p15 Ns360p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns360p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 153643044 134217728 2 134217728 38410761 33554432 1 67108864 (Ns360p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns360p0 Ns360p1 307286088 268435456 1 84640000 Bool.false (BSN.logfrac_isNear Ns360p4 Ns360p5 1 Ns360p0 Ns360p1 307286088 268435456 84640000 rfl rfl rfl (Ns360p11 rfl))) (BSN.isNear_log_sfrac Ns360p2 Ns360p1 307286088 268435456 1 84640000 Bool.false (BSN.logfrac_isNear Ns360p12 Ns360p5 1 Ns360p2 Ns360p1 307286088 268435456 84640000 rfl rfl rfl (Ns360p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS361to372.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 67108864 := Ns360p19 

noncomputable def Ns360p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 16777216 5290000 385100712855 135135 11629079 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz578 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz316 := qz578

noncomputable abbrev qz0 := qz316

theorem RS361to372.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 11629079 16777216 1 5290000 := BSN.isNear_log_sfrac 2 1 11629079 16777216 1 5290000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 11629079 16777216 5290000 rfl rfl rfl (Ns360p20 rfl)) 

theorem RS361to372.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 186065264 268435456 51 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 11629079 16777216 1 5290000 186065264 268435456 51 268435456 RS361to372.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz579 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz319 := qz579

noncomputable def Ns360p21 := @Enclosure.Real.IsNear.inv_image qz317 47453133 33554432 1 33554432 11863282 11863284 16777216 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 47453133 33554432 1 33554432 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 47453133 33554432 1 33554432 47453133 33554432 1 33554432 (BSN.sqrt_enclosure 2 1 23726566 23726567 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS361to372.d8 : Enclosure.Real.IsNear qz320 Bool.false 11863283 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 23726566 33554432 2 33554432 11863283 16777216 1 16777216 (Ns360p21 rfl rfl) rfl 

theorem RS361to372.d9 : Enclosure.Real.IsNear qz320 Bool.false 189812528 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 11863283 16777216 1 16777216 189812528 268435456 16 268435456 RS361to372.d8 rfl 

noncomputable def Ns360p22 := BSN.log_dyadic_bound 1 2 13 12 132638213186519040000 16777216 5290000 13079757671720842725 316234143225 18431655 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 1) (BSN.artanhQ 2) 0 12 13079757671720842725 132638213186519040000 316234143225 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS361to372.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 18431655 16777216 1 5290000 := BSN.isNear_log_sfrac 3 1 18431655 16777216 1 5290000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 18431655 16777216 5290000 rfl rfl rfl (Ns360p22 rfl)) 

theorem RS361to372.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 294906480 268435456 51 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 18431655 16777216 1 5290000 294906480 268435456 51 268435456 RS361to372.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns360p23 := @Enclosure.Real.IsNear.inv_image qz321 58117981 33554432 1 33554432 9686330 9686331 16777216 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 58117981 33554432 1 33554432 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 58117981 33554432 1 33554432 58117981 33554432 1 33554432 (BSN.sqrt_enclosure 3 1 29058990 29058991 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS361to372.d12 : Enclosure.Real.IsNear qz323 Bool.false 19372661 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 19372661 33554432 1 33554432 19372661 33554432 1 33554432 (Ns360p23 rfl rfl) rfl 

theorem RS361to372.d13 : Enclosure.Real.IsNear qz323 Bool.false 154981288 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 19372661 33554432 1 33554432 154981288 268435456 8 268435456 RS361to372.d12 rfl 

noncomputable def Ns360p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns360p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns360p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns360p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns360p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns360p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns360p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns360p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns360p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns360p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns360p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns360p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns360p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns360p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns360p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns360p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns360p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns360p25 Ns360p26 Ns360p27 Ns360p28 200200021673987500790625 Ns360p29 Ns360p30 Ns360p31 Ns360p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns360p32 Ns360p33 151412625 Ns360p34 Ns360p35 1322214852783825 Ns360p27 Ns360p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns360p32 Ns360p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns360p34 Ns360p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns360p36 Ns360p37 1267389585 Ns360p38 Ns360p39 1927077560082675 Ns360p29 Ns360p30 Ns360p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns360p36 Ns360p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns360p38 Ns360p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS361to372.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns360p24 Ns360p25 1 Ns360p26 := Ns360p40 rfl rfl rfl 

noncomputable def Ns360p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns360p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns360p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns360p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns360p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns360p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns360p25 Ns360p26 Ns360p42 Ns360p43 9945 Ns360p44 Ns360p45 65835 Ns360p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns360p42 Ns360p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns360p44 Ns360p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS361to372.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns360p41 Ns360p25 1 Ns360p26 := Ns360p46 rfl 

noncomputable def Ns360p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns360p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS361to372.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns360p47 Ns360p25 1 Ns360p48 := BSN.pi_combine Ns360p24 Ns360p41 Ns360p25 Ns360p26 Ns360p48 Ns360p47 rfl rfl rfl rfl RS361to372.d14 RS361to372.d15 

theorem RS361to372.d17 : Enclosure.Real.IsNear Real.pi Bool.false 14148475504056880 4503599627370496 1 4503599627370496 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns360p47 Ns360p25 1 Ns360p48 14148475504056880 4503599627370496 1 4503599627370496 RS361to372.d16 rfl 

noncomputable def Ns360p49 := nat_lit 147443727375074537121690809726715087890625 

noncomputable def Ns360p50 := nat_lit 22889945643899497138335355216896171420000 

noncomputable def Ns360p51 := nat_lit 355592320898650075318906513310625 

noncomputable def Ns360p52 := BSN.log_dyadic_bound 3 5 17 16 Ns360p49 16777216 5290000 Ns360p50 Ns360p51 23258159 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 3) (BSN.artanhQ 5) 0 16 Ns360p50 Ns360p49 Ns360p51 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS361to372.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 23258159 16777216 1 5290000 := BSN.isNear_log_sfrac 4 1 23258159 16777216 1 5290000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 23258159 16777216 5290000 rfl rfl rfl (Ns360p52 rfl)) 

theorem RS361to372.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 372130544 268435456 51 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 23258159 16777216 1 5290000 372130544 268435456 51 268435456 RS361to372.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns360p53 := @Enclosure.Real.IsNear.inv_image qz325 67108865 33554432 1 33554432 8388607 8388608 16777216 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 67108865 33554432 1 33554432 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 67108865 33554432 1 33554432 67108865 33554432 1 33554432 (BSN.sqrt_enclosure 4 1 33554432 33554433 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS361to372.d20 : Enclosure.Real.IsNear qz327 Bool.false 16777215 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 16777215 33554432 1 33554432 16777215 33554432 1 33554432 (Ns360p53 rfl rfl) rfl 

theorem RS361to372.d21 : Enclosure.Real.IsNear qz327 Bool.false 134217720 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 16777215 33554432 1 33554432 134217720 268435456 8 268435456 RS361to372.d20 rfl 

noncomputable def Ns360p54 := nat_lit 61697213297292266380244507781205789317049021875 

noncomputable def Ns360p55 := nat_lit 12776162289178456695994184080609776001208236500 

noncomputable def Ns360p56 := nat_lit 57671893776295590731569354191667200000 

noncomputable def Ns360p57 := nat_lit 885951608314392539099884620 

noncomputable def Ns360p58 := nat_lit 1286943652057122751813246125 

noncomputable def Ns360p59 := BSN.log_dyadic_bound 2 3 22 21 Ns360p54 16777216 5290000 Ns360p55 Ns360p56 27001887 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 21 10 9927050056596826020 47940881637414340575 686533194547200 Ns360p57 Ns360p58 84004523356416638976000 Ns360p55 Ns360p54 Ns360p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base11 (BSN.artanhP 2) (BSN.artanhQ 3) 10 21 Ns360p57 Ns360p58 84004523356416638976000 rfl rfl rfl rfl)) rfl rfl 

theorem RS361to372.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 5290000 := BSN.isNear_log_sfrac 5 1 27001887 16777216 1 5290000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 27001887 16777216 5290000 rfl rfl rfl (Ns360p59 rfl rfl)) 

theorem RS361to372.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 432030192 268435456 51 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 5290000 432030192 268435456 51 268435456 RS361to372.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns360p60 := @Enclosure.Real.IsNear.inv_image qz328 75029991 33554432 1 33554432 7502998 7503000 16777216 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 75029991 33554432 1 33554432 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 75029991 33554432 1 33554432 75029991 33554432 1 33554432 (BSN.sqrt_enclosure 5 1 37514995 37514996 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS361to372.d24 : Enclosure.Real.IsNear qz329 Bool.false 7502999 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 15005998 33554432 2 33554432 7502999 16777216 1 16777216 (Ns360p60 rfl rfl) rfl 

theorem RS361to372.d25 : Enclosure.Real.IsNear qz329 Bool.false 120047984 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 7502999 16777216 1 16777216 120047984 268435456 16 268435456 RS361to372.d24 rfl 

noncomputable def Ns360p61 := BSN.log_dyadic_bound 2 10 5 4 94500000000 16777216 5290000 1291130880 26880 6802575 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 10) 0 4 1291130880 94500000000 26880 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz579)

theorem RS361to372.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 50000000529 264500000000000000 := BSN.isNear_log_sfrac 6 1 4034683545132279 2251799813685248 50000000529 264500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 1083052117253279893684224 604462909807314587353088 1000000010580000 5290000000000000000000 4034683545132279 2251799813685248 50000000529 264500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 6802575 16777216 24973259072661432 36028797018963968 5290000 1000000000000000 rfl rfl rfl rfl (Ns360p61 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS361to372.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 480971758 268435456 52 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 50000000529 264500000000000000 480971758 268435456 52 268435456 RS361to372.d26 rfl 

noncomputable abbrev qz331 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns360p62 := @Enclosure.Real.IsNear.inv_image qz331 82191237 33554432 1 33554432 6849269 6849270 16777216 (@Enclosure.Real.IsNear.of_eq qz331 (Real.sqrt qz330) Bool.false 82191237 33554432 1 33554432 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 82191237 33554432 1 33554432 82191237 33554432 1 33554432 (BSN.sqrt_enclosure 6 1 41095618 41095619 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS361to372.d28 : Enclosure.Real.IsNear qz332 Bool.false 13698539 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 13698539 33554432 1 33554432 13698539 33554432 1 33554432 (Ns360p62 rfl rfl) rfl 

theorem RS361to372.d29 : Enclosure.Real.IsNear qz332 Bool.false 109588312 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 13698539 33554432 1 33554432 109588312 268435456 8 268435456 RS361to372.d28 rfl 

noncomputable def Ns360p63 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 16777216 5290000 11010900719820672 5524329195 9388794 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz579)

theorem RS361to372.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 50000000529 264500000000000000 := BSN.isNear_log_sfrac 7 1 4381799983422711 2251799813685248 50000000529 264500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 1176230476650867868041216 604462909807314587353088 1000000010580000 5290000000000000000000 4381799983422711 2251799813685248 50000000529 264500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 9388794 16777216 24973259072661432 36028797018963968 5290000 1000000000000000 rfl rfl rfl rfl (Ns360p63 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS361to372.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 522351262 268435456 52 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 50000000529 264500000000000000 522351262 268435456 52 268435456 RS361to372.d30 rfl 

noncomputable abbrev qz334 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns360p64 := @Enclosure.Real.IsNear.inv_image qz334 88776683 33554432 1 33554432 6341191 6341192 16777216 (@Enclosure.Real.IsNear.of_eq qz334 (Real.sqrt qz333) Bool.false 88776683 33554432 1 33554432 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 88776683 33554432 1 33554432 88776683 33554432 1 33554432 (BSN.sqrt_enclosure 7 1 44388341 44388342 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz335 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS361to372.d32 : Enclosure.Real.IsNear qz335 Bool.false 12682383 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 12682383 33554432 1 33554432 12682383 33554432 1 33554432 (Ns360p64 rfl rfl) rfl 

theorem RS361to372.d33 : Enclosure.Real.IsNear qz335 Bool.false 101459064 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 12682383 33554432 1 33554432 101459064 268435456 8 268435456 RS361to372.d32 rfl 

noncomputable def Ns360p65 := nat_lit 1256945285058001618599936 

noncomputable def Ns360p66 := BSN.log_dyadic_bound 0 16 1 0 1 16777216 5290000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz579)

theorem RS361to372.d34 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 100000001587 529000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 100000001587 529000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false Ns360p65 604462909807314587353088 1000000015870000 5290000000000000000000 9364972152248037 4503599627370496 100000001587 529000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 16777216 24973259072661432 36028797018963968 5290000 1000000000000000 rfl rfl rfl rfl (Ns360p66 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS361to372.d35 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 558195838 268435456 52 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 100000001587 529000000000000000 558195838 268435456 52 268435456 RS361to372.d34 rfl 

noncomputable abbrev qz337 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns360p67 := @Enclosure.Real.IsNear.inv_image qz337 94906265 33554432 1 33554432 5931641 5931642 16777216 (@Enclosure.Real.IsNear.of_eq qz337 (Real.sqrt qz336) Bool.false 94906265 33554432 1 33554432 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 94906265 33554432 1 33554432 94906265 33554432 1 33554432 (BSN.sqrt_enclosure 8 1 47453132 47453133 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz338 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS361to372.d36 : Enclosure.Real.IsNear qz338 Bool.false 11863283 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 11863283 33554432 1 33554432 11863283 33554432 1 33554432 (Ns360p67 rfl rfl) rfl 

theorem RS361to372.d37 : Enclosure.Real.IsNear qz338 Bool.false 94906264 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 11863283 33554432 1 33554432 94906264 268435456 8 268435456 RS361to372.d36 rfl 

noncomputable def Ns360p68 := nat_lit 1328140746012062765809664 

noncomputable def Ns360p69 := BSN.log_dyadic_bound 1 17 3 2 1252815 16777216 5290000 1448 3 1976071 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz579)

theorem RS361to372.d38 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 100000001587 529000000000000000 := BSN.isNear_log_sfrac 9 1 9895419672221413 4503599627370496 100000001587 529000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false Ns360p68 604462909807314587353088 1000000015870000 5290000000000000000000 9895419672221413 4503599627370496 100000001587 529000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 1976071 16777216 24973259072661432 36028797018963968 5290000 1000000000000000 rfl rfl rfl rfl (Ns360p69 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS361to372.d39 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 589812974 268435456 52 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 100000001587 529000000000000000 589812974 268435456 52 268435456 RS361to372.d38 rfl 

noncomputable abbrev qz340 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable def Ns360p70 := @Enclosure.Real.IsNear.inv_image qz340 100663297 33554432 1 33554432 5592405 5592406 16777216 (@Enclosure.Real.IsNear.of_eq qz340 (Real.sqrt qz339) Bool.false 100663297 33554432 1 33554432 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz339) Bool.false 100663297 33554432 1 33554432 100663297 33554432 1 33554432 (BSN.sqrt_enclosure 9 1 50331648 50331649 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz341 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS361to372.d40 : Enclosure.Real.IsNear qz341 Bool.false 11184811 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 11184811 33554432 1 33554432 11184811 33554432 1 33554432 (Ns360p70 rfl rfl) rfl 

theorem RS361to372.d41 : Enclosure.Real.IsNear qz341 Bool.false 89478488 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 11184811 33554432 1 33554432 89478488 268435456 8 268435456 RS361to372.d40 rfl 

noncomputable def Ns360p71 := nat_lit 1391827265235416537628672 

noncomputable def Ns360p72 := BSN.log_dyadic_bound 2 18 4 3 3571283520 16777216 5290000 14806464 960 3743727 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 18) 0 3 14806464 3571283520 960 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz736 := (Enclosure.sfrac Bool.false 10 1)

noncomputable abbrev qz580 := qz736

noncomputable abbrev qz342 := qz580

noncomputable abbrev qz1 := qz342

noncomputable abbrev qz343 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10) qz579)

theorem RS361to372.d42 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 10369921216632549 4503599627370496 100000001587 529000000000000000 := BSN.isNear_log_sfrac 10 1 10369921216632549 4503599627370496 100000001587 529000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz343) Bool.false Ns360p71 604462909807314587353088 1000000015870000 5290000000000000000000 10369921216632549 4503599627370496 100000001587 529000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 3743727 16777216 24973259072661432 36028797018963968 5290000 1000000000000000 rfl rfl rfl rfl (Ns360p72 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS361to372.d43 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 618095470 268435456 52 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 10369921216632549 4503599627370496 100000001587 529000000000000000 618095470 268435456 52 268435456 RS361to372.d42 rfl 

noncomputable abbrev qz344 := (Real.sqrt (@Nat.cast Real Real.instNatCast 10))

noncomputable def Ns360p73 := @Enclosure.Real.IsNear.inv_image qz344 106108431 33554432 1 33554432 5305421 5305422 16777216 (@Enclosure.Real.IsNear.of_eq qz344 (Real.sqrt qz343) Bool.false 106108431 33554432 1 33554432 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz343) Bool.false 106108431 33554432 1 33554432 106108431 33554432 1 33554432 (BSN.sqrt_enclosure 10 1 53054215 53054216 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz345 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

theorem RS361to372.d44 : Enclosure.Real.IsNear qz345 Bool.false 10610843 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz345 Bool.false 10610843 33554432 1 33554432 10610843 33554432 1 33554432 (Ns360p73 rfl rfl) rfl 

theorem RS361to372.d45 : Enclosure.Real.IsNear qz345 Bool.false 84886744 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz345 Bool.false 10610843 33554432 1 33554432 84886744 268435456 8 268435456 RS361to372.d44 rfl 

theorem RS361to372.d46 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz737 := (@instHMul Real Real.instMul)

noncomputable abbrev qz581 := (@HMul.hMul Real Real Real qz737 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz346 := qz581

noncomputable abbrev qz2 := qz346

theorem RS361to372.d47 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS361to372.d46 rfl 

noncomputable abbrev qz347 := (@Inv.inv Real Real.instInv qz581)

noncomputable abbrev qz3 := qz347

theorem RS361to372.d48 : Enclosure.Real.IsNear qz3 Bool.false 5340353 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 5340353 33554432 1 33554432 5340353 33554432 1 33554432 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 2670176 2670177 16777216 RS361to372.d47 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns360p74 := nat_lit 312266483679755289755648000 

noncomputable def Ns360p75 := nat_lit 14440488808215772933549719552 

noncomputable abbrev qz738 := (Enclosure.sfrac Bool.false 696589 1000)

noncomputable abbrev qz582 := qz738

noncomputable abbrev qz348 := qz582

noncomputable abbrev qz4 := qz348

noncomputable abbrev qz583 := qz737

noncomputable abbrev qz349 := qz583

noncomputable abbrev qz5 := qz349

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 10)

noncomputable abbrev qz7 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz739 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 696589 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz584 := qz739

noncomputable abbrev qz350 := qz584

noncomputable abbrev qz8 := qz350

noncomputable abbrev qz9 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz740 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 696589 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz585 := qz740

noncomputable abbrev qz351 := qz585

noncomputable abbrev qz10 := qz351

noncomputable abbrev qz586 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz8 qz9))

noncomputable def Ns360p76 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HMul.hMul Real Real Real qz5 qz586 (Zeta.RiemannSiegel.correction qz10)) 1071525 16777216 19609 16777216 559112731376819392797 4722366482869645213696 1554795161686738916231 Ns360p74 Ns360p75 

noncomputable def Ns360p77 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin BSN.quadSignPos 9 10 696589 1000 199 268435456 134217728 4503599627370496 Bool.false 346602322357 2511 618095470 52 84886744 8 

noncomputable def Ns360p78 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 696589 1000 100 152 268435456 134217728 4503599627370496 Bool.false 346602322357 2511 

noncomputable def Ns360p79 := Ns360p78 558195838 52 94906264 8 589812974 52 89478488 8 Bool.true 188781386 117988 Bool.true 65015412 Bool.true 162978292 14148475504056880 1 Bool.false 260600461 Bool.false Bool.false 220461271 Bool.false Bool.true 23158119 

noncomputable def Ns360p80 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 696589 1000 27 40 268435456 134217728 4503599627370496 Bool.false 346602322357 2511 

noncomputable def Ns360p81 := Ns360p80 480971758 52 109588312 8 522351262 52 101459064 8 Bool.true 266081391 87515 Bool.false 177935860 Bool.true 395523757 14148475504056880 1 Bool.false 165188703 Bool.false Bool.false 26092407 Bool.false Bool.true 188781386 

noncomputable def Ns360p82 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 696589 1000 207 108 268435456 134217728 4503599627370496 Bool.false 346602322357 2511 

noncomputable def Ns360p83 := Ns360p82 372130544 51 134217720 8 432030192 51 120047984 16 Bool.true 422664474 51457 Bool.false 97191191 Bool.false 115840689 14148475504056880 1 Bool.false 95081578 Bool.false Bool.false 243825993 Bool.false Bool.true 266081391 

noncomputable def Ns360p84 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 696589 1000 514 334 268435456 134217728 4503599627370496 Bool.false 346602322357 2511 

noncomputable def Ns360p85 := Ns360p84 186065264 51 189812528 16 294906480 51 154981288 8 Bool.true 268435440 2571 Bool.false 259388043 Bool.false 340131319 14148475504056880 1 Bool.false 152565618 Bool.true Bool.false 80278564 Bool.true Bool.true 422664474 

noncomputable def Ns360p86 := nat_lit 1494838333762314546148375446652443754014605327335394379391 

noncomputable def Ns360p87 := nat_lit 1157717602815949724944464619517125339406938172030976000 

noncomputable def Ns360p88 := nat_lit 2166784000000000000000000 

noncomputable def Ns360p89 := nat_lit 78727210733077210042986180135520000 

noncomputable def Ns360p90 := nat_lit 329043133096987993708485367823506447680 

noncomputable abbrev qz352 := (@Eq.refl Real qz582)

noncomputable abbrev qz11 := qz352

noncomputable def Ns360p91 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 696589 1000 1940945939684 16000000 1393178 4000 2000 Ns360p89 Ns360p90 qz11 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns360p92 := nat_lit 478348266803940654767480142928782001284673704747326201405120 

noncomputable abbrev qz741 := (@instHSub Real Real.instSub)

noncomputable abbrev qz587 := qz741

noncomputable abbrev qz353 := qz587

noncomputable abbrev qz588 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz742 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz743 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz589 := (@HSub.hSub Real Real Real qz741 qz742 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz743 (@Nat.cast Real Real.instNatCast 1393178))))

noncomputable abbrev qz354 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 696589 4000) (Real.log (Enclosure.sfrac Bool.false 1940945939684 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz589))

noncomputable abbrev qz590 := (Enclosure.sfrac Bool.false 696589 2000)

noncomputable abbrev qz12 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz354 qz590) (@HMul.hMul Real Real Real qz349 qz590 (Real.log Real.pi)))

noncomputable def Ns360p93 := @Enclosure.Real.IsNear.addLit_ft_p qz12 (Enclosure.sfrac Bool.true Ns360p89 Ns360p90) 1453755776455918406959 1125899906842624000 20264337919587212729 Ns360p88 Ns360p89 Ns360p90 0 1 Ns360p92 

noncomputable def Ns360p94 := nat_lit 97559898691394630367708184576000 

noncomputable abbrev qz13 := (@HSub.hSub Real Real Real qz353 qz354 qz590)

noncomputable def Ns360p95 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (@HMul.hMul Real Real Real qz5 qz590 (Real.log Real.pi)) 1902655584433234693423 1125899906842624000 2201842099048449 529000000000000000000 26756513594229 67108864000 696589 134217728000 Ns360p94 1453755776455918406959 1125899906842624000 

noncomputable def Ns360p96 := nat_lit 3805311168866469386846000 

noncomputable abbrev qz14 := qz354

noncomputable def Ns360p97 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz590 2294800329537032998191 1125899906842624000 2201842099048449 529000000000000000000 696589 2000 0 1 Ns360p96 1902655584433234693423 1125899906842624000 2201842099048449 529000000000000000000 

noncomputable def Ns360p98 := nat_lit 5167430954496336618115915926227386368 

noncomputable def Ns360p99 := nat_lit 56607213003540683603050496 

noncomputable def Ns360p100 := nat_lit 4835703278458516698824704 

noncomputable def Ns360p101 := nat_lit 9231739368872585915843368351351618168643069341638586663650079683286004343593866822171324597845904282143060311816576562754801121972855287597818051237006261825326406676990153614950400 

noncomputable def Ns360p102 := nat_lit 289849192674789257800899317384820417825867197912734808173202013134623119532583064633087391612490880828056029566201866452342228546450811881920509654041833524368965348715074410250240 

noncomputable def Ns360p103 := nat_lit 27440808142698014072107041937973816741323055864689734909144325063747898841570327956230041585092141181885314905404959471063763327829276890358152051854335442530452479787663360 

noncomputable def Ns360p104 := BSN.log_dyadic_bound 892369939684 2989521939684 8 7 Ns360p101 134217728 42320000 Ns360p102 Ns360p103 82643545 3881891879368 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 892369939684) (BSN.artanhQ 2989521939684) 0 7 Ns360p102 Ns360p101 Ns360p103 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz355 := (Real.log (Enclosure.sfrac Bool.false 1940945939684 16000000))

noncomputable abbrev qz356 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns360p105 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 696589 4000) qz355 696589 4000 0 1 3294973459766519 281474976710656 781250529 33062500000000000 2295242267365299703691 1125899906842624000 544210524745581 132250000000000000000 (Enclosure.Real.IsNear.const Bool.false 696589 4000) (BSN.isNear_log_sfrac 1940945939684 16000000 3294973459766519 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1940945939684) qz356)) Bool.false Ns360p99 Ns360p100 1000000677120000 42320000000000000000000 3294973459766519 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 1940945939684 16000000 16 3881891879368 2097152000000 82643545 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns360p104 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p106 := BSN.arctan_dyadic_bound_f 1000 1393178 1 0 16777216 5290000 0 1 1 0 1 1 12042 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1393178) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1393178) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz591 := qz742

noncomputable abbrev qz357 := qz591

noncomputable abbrev qz15 := qz357

noncomputable abbrev qz592 := qz743

noncomputable abbrev qz358 := qz592

noncomputable abbrev qz16 := qz358

noncomputable abbrev qz744 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz593 := qz744

noncomputable abbrev qz359 := qz593

noncomputable abbrev qz17 := (@Enclosure.Real.IsNear.mulLit_ff qz359 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def Ns360p107 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1393178))) 884279719003555 562949953421312 1 2000000000000000 12042 16777216 1 5290000 14828972806802847563776 883875656533411 562949953421312 200000000529 1058000000000000000 qz17 (Ns360p106 rfl) rfl rfl 

noncomputable abbrev qz360 := (@HMul.hMul Real Real Real qz583 qz588 qz589)

noncomputable abbrev qz18 := qz360

noncomputable abbrev qz361 := qz588

noncomputable abbrev qz19 := qz361

noncomputable abbrev qz362 := qz589

noncomputable abbrev qz20 := qz362

noncomputable abbrev qz363 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns360p108 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 696589 4000) qz355) qz18 2295242267365299703691 1125899906842624000 544210524745581 132250000000000000000 883875656533411 2251799813685248 200000000529 4232000000000000000 Ns360p98 2294800329537032998191 1125899906842624000 2201842099048449 529000000000000000000 (Ns360p105 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz20 1 4 0 1 883875656533411 562949953421312 200000000529 1058000000000000000 883875656533411 2251799813685248 200000000529 4232000000000000000 qz363 Ns360p107 rfl) 

noncomputable def Ns360p109 := @Ns360p93 Ns360p86 Ns360p87 20264337919587212729 Ns360p88 (@Ns360p95 20264337919587212729 Ns360p88 (Ns360p97 (Ns360p108 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 696589 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz590 (Real.log Real.pi) 696589 2000 0 1 38410761 33554432 1 67108864 26756513594229 67108864000 696589 134217728000 (Enclosure.Real.IsNear.const Bool.false 696589 2000) RS361to372.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns360p89 Ns360p90) 

noncomputable abbrev qz364 := (@instHAdd Real Real.instAdd)

noncomputable def Ns360p110 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns360p86 Ns360p87 20264337919587212729 Ns360p88 21662645147 16777216 315 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz364 qz12 (Enclosure.sfrac Bool.true Ns360p89 Ns360p90)) Bool.false Ns360p86 Ns360p87 20264337919587212729 Ns360p88 Ns360p91 (Ns360p109 rfl rfl)) 

noncomputable def Ns360p111 := nat_lit 3797198724997620174946304 

noncomputable def Ns360p112 := nat_lit 2417851639229258349412352 

noncomputable def Ns360p113 := nat_lit 3508043649994986505184799870781888370017296143628806032208215044071731480461842708789417337833871345485862127894362110227725170385454650321 

noncomputable def Ns360p114 := nat_lit 69061887427279807374175457422696049589758900585025510522285359577850094671315332446731519433112496475662717985575392155893264493730122956800 

noncomputable def Ns360p115 := nat_lit 2496676410701827893630894539800490122272943567077926577927112218778697780931948400911148393805159175023774319375452523636626654778321 

noncomputable def Ns360p116 := nat_lit 17518439635012417256056620727325089742712076918965274919578126521671163406168296256041831949060430381287011035009420314641160486839129494481 

noncomputable def Ns360p117 := nat_lit 2417166059954793258096141009794361735641561520475892868279987585224753313496036635635603180158937376648195129495138725456264257280554303488000 

noncomputable abbrev qz594 := (BSN.sinEvenQ 68719476736)

noncomputable abbrev qz595 := (BSN.sinOddQ 68719476736)

noncomputable def Ns360p118 := BSN.sin_dyadic_bound_f 107922878811 68719476736 4 3 33554432 10590333 Ns360p113 Ns360p114 Ns360p115 Ns360p116 Ns360p117 Ns360p115 33554430 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107922878811) qz594 0 3 Ns360p113 Ns360p114 Ns360p115 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107922878811) qz595 0 3 Ns360p116 Ns360p117 Ns360p115 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz365 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable abbrev qz366 := (@Nat.cast Real Real.instNatCast Ns360p112)

noncomputable def Ns360p119 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21662645147) qz365) Bool.false 21662645147 16777216 315 33554432 Bool.true 33554430 33554432 1 5290000 (Ns360p110 rfl) (Enclosure.sfrac_false_div 21662645147 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21662645147) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns360p111) qz366) 226375608064910080 72057594037927936 Bool.false 33554430 33554432 205 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q1 21662645147 16777216 226375608064910080 72057594037927936 205 Ns360p111 Ns360p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554430 33554432 Ns360p111 Ns360p112 107922878811 68719476736 10590333 10580000 (Ns360p118 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p120 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns360p86 Ns360p87 20264337919587212729 Ns360p88 346602322357 268435456 2511 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz364 qz12 (Enclosure.sfrac Bool.true Ns360p89 Ns360p90)) Bool.false Ns360p86 Ns360p87 20264337919587212729 Ns360p88 Ns360p91 (Ns360p109 rfl rfl)) 

noncomputable def Ns360p121 := Ns360p85 51457 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 514 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 152565618 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 334 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 80278564 268435456) qz11 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 16777215 16777216 106244027 11093934080000 268435440 268435456 2571 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 16777215 16777216 106244027 11093934080000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 33554430 33554432 1699904432 177502945280000 16777215 16777216 106244027 11093934080000 (Ns360p119 rfl rfl) rfl)) rfl) (Ns360p120 rfl) RS361to372.d7 

noncomputable def Ns360p122 := nat_lit 39508808074642644191777055626462127751305100428889517237791800808150881 

noncomputable def Ns360p123 := nat_lit 1087025049619513796520974048308631508761049663116835882438097565248389120 

noncomputable def Ns360p124 := nat_lit 20492720673605067910534363646013072735475665670970505518857148405601 

noncomputable def Ns360p125 := nat_lit 118485438782580722439510098152094357108444349955326610702337688127641441 

noncomputable def Ns360p126 := nat_lit 48916127232878120843443832173888417894247234840257614709714390436177510400 

noncomputable abbrev qz367 := (BSN.cosEvenQ 268435456)

noncomputable abbrev qz368 := (BSN.cosOddQ 268435456)

noncomputable def Ns360p127 := BSN.cos_dyadic_bound_f 259388043 268435456 3 2 268435456 134217728 Ns360p122 Ns360p123 Ns360p124 Ns360p125 Ns360p126 Ns360p124 152565618 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 259388043) qz367 0 2 Ns360p122 Ns360p123 Ns360p124 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 259388043) qz368 0 2 Ns360p125 Ns360p126 Ns360p124 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p128 := nat_lit 7212689342846157159661145698641747296382293407212663217161733548462067998993719594945627076255513321045692641 

noncomputable def Ns360p129 := nat_lit 67052582193422231333984484018745857420694574238012043916021913709013615522643186318434558042568065189255577600 

noncomputable def Ns360p130 := nat_lit 2397504764169930453462074438895155028518212433686583757750368466664445020026858362154038514117064462561 

noncomputable def Ns360p131 := nat_lit 43712280127233758388211025279273050288567284950755386891051534899616991479347698473374785493509354203067125985 

noncomputable def Ns360p132 := nat_lit 6101784979601423051392588045705873025283206255659095996357994147520239012560529954977544781873693932222257561600 

noncomputable def Ns360p133 := BSN.cos_dyadic_bound_f 340131319 268435456 4 3 268435456 134217728 Ns360p128 Ns360p129 Ns360p130 Ns360p131 Ns360p132 Ns360p130 80278564 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 340131319) qz367 0 3 Ns360p128 Ns360p129 Ns360p130 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 340131319) qz368 0 3 Ns360p131 Ns360p132 Ns360p130 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p134 := nat_lit 89229326786591104328326898307361 

noncomputable def Ns360p135 := nat_lit 623075623024179315423659559506411520 

noncomputable def Ns360p136 := nat_lit 4361529361169255207965616916544880640 

noncomputable abbrev qz369 := (BSN.sinEvenQ 268435456)

noncomputable abbrev qz370 := (BSN.sinOddQ 268435456)

noncomputable def Ns360p137 := BSN.sin_dyadic_bound_f 97191191 268435456 2 1 268435456 134217728 Ns360p134 Ns360p135 Ns360p134 Ns360p134 Ns360p136 Ns360p134 95081578 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 97191191) qz369 0 1 Ns360p134 Ns360p135 Ns360p134 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 97191191) qz370 0 1 Ns360p134 Ns360p136 Ns360p134 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p138 := nat_lit 1570805050913057364873831806394780284431179275545003620512029152997761 

noncomputable def Ns360p139 := nat_lit 32425677258887046301473623414213662948690931093894319109794001281 

noncomputable def Ns360p140 := nat_lit 4712350301384654320528892471937512425967640444772823072897867870990721 

noncomputable def Ns360p141 := BSN.cos_dyadic_bound_f 115840689 268435456 3 2 268435456 134217728 Ns360p138 Ns360p123 Ns360p139 Ns360p140 Ns360p126 Ns360p139 243825993 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 115840689) qz367 0 2 Ns360p138 Ns360p123 Ns360p139 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 115840689) qz368 0 2 Ns360p140 Ns360p126 Ns360p139 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p142 := Ns360p83 87515 BSN.abs_quadSignPos (BSN.cos_quad_nat3 207 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 95081578 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 108 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 243825993 268435456) qz11 rfl rfl (Ns360p121 RS361to372.d9 RS361to372.d11 RS361to372.d13 RS361to372.d17 (Ns360p127 rfl rfl) (Ns360p133 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns360p120 rfl) RS361to372.d19 RS361to372.d21 RS361to372.d23 RS361to372.d25 RS361to372.d17 (Ns360p137 rfl rfl) (Ns360p141 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns360p143 := nat_lit 15740660562835222287398566047174208568874122079646064795819549040640000 

noncomputable def Ns360p144 := nat_lit 9783225446575624168688766434777683578849446968051522941942878087235502080 

noncomputable def Ns360p145 := nat_lit 1004865309688022099190900789413763308661483039628394127385600000000 

noncomputable def Ns360p146 := nat_lit 41223912644543230145502316284178162063599153521770771350940194611200000 

noncomputable def Ns360p147 := nat_lit 179359133187219776425960717970924198945573194414277920602286098265984204800 

noncomputable def Ns360p148 := BSN.sin_dyadic_bound_f 177935860 268435456 3 2 268435456 134217728 Ns360p143 Ns360p144 Ns360p145 Ns360p146 Ns360p147 Ns360p145 165188703 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 177935860) qz369 0 2 Ns360p143 Ns360p144 Ns360p145 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 177935860) qz370 0 2 Ns360p146 Ns360p147 Ns360p145 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p149 := nat_lit 13205421542429298316653825369898184850945990989659451701074048235182150785527757424406583782199519396737036081 

noncomputable def Ns360p150 := nat_lit 14657870903683134549080008325540873776628109210394077773174379520850353573124303064674814894092950417201 

noncomputable def Ns360p151 := nat_lit 79963394121746025069465528028397140531194622498014464994614416864325852011917919267645119904530591617294774065 

noncomputable def Ns360p152 := BSN.cos_dyadic_bound_f 395523757 268435456 4 3 268435456 134217728 Ns360p149 Ns360p129 Ns360p150 Ns360p151 Ns360p132 Ns360p150 26092407 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 395523757) qz367 0 3 Ns360p149 Ns360p129 Ns360p150 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 395523757) qz368 0 3 Ns360p151 Ns360p132 Ns360p150 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p153 := Ns360p81 117988 BSN.abs_quadSignPos (BSN.cos_quad_nat3 27 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 165188703 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 40 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 26092407 268435456) qz11 rfl rfl (Ns360p142 rfl rfl) (Ns360p120 rfl) RS361to372.d27 RS361to372.d29 RS361to372.d31 RS361to372.d33 RS361to372.d17 (Ns360p148 rfl rfl) (Ns360p152 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p154 := nat_lit 17867561104330877008156564705536 

noncomputable def Ns360p155 := nat_lit 124615124604835863084731911901282304 

noncomputable def Ns360p156 := nat_lit 1869226869072537946270978678519234560 

noncomputable def Ns360p157 := BSN.cos_dyadic_bound_f 65015412 268435456 2 1 268435456 134217728 Ns360p154 Ns360p155 Ns360p154 Ns360p154 Ns360p156 Ns360p154 260600461 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 65015412) qz367 0 1 Ns360p154 Ns360p155 Ns360p154 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 65015412) qz368 0 1 Ns360p154 Ns360p156 Ns360p154 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p158 := nat_lit 6154927896217747621645365641934213391449161515172936917481154423095296 

noncomputable def Ns360p159 := nat_lit 497780749124739730137158527196565159522030916971936000024646844416 

noncomputable def Ns360p160 := nat_lit 18463788127154993385475822608748247044028440483684866880443413975597056 

noncomputable def Ns360p161 := BSN.cos_dyadic_bound_f 162978292 268435456 3 2 268435456 134217728 Ns360p158 Ns360p123 Ns360p159 Ns360p160 Ns360p126 Ns360p159 220461271 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 162978292) qz367 0 2 Ns360p158 Ns360p123 Ns360p159 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 162978292) qz368 0 2 Ns360p160 Ns360p126 Ns360p159 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p162 := Ns360p79 144613 BSN.abs_quadSignPos (BSN.cos_quad_nat0 100 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 260600461 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 152 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 220461271 268435456) qz11 rfl rfl (Ns360p153 rfl) (Ns360p120 rfl) RS361to372.d35 RS361to372.d37 RS361to372.d39 RS361to372.d41 RS361to372.d17 (Ns360p157 rfl rfl) (Ns360p161 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p163 := nat_lit 4617189345077268045423578176321 

noncomputable def Ns360p164 := BSN.sin_dyadic_bound_f 46354769 268435456 2 1 268435456 134217728 Ns360p163 Ns360p135 Ns360p163 Ns360p163 Ns360p136 Ns360p163 46124728 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 46354769) qz369 0 1 Ns360p163 Ns360p135 Ns360p163 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 46354769) qz370 0 1 Ns360p163 Ns360p136 Ns360p163 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p165 := Ns360p77 Bool.true 23158119 144613 Bool.true 46354769 14148475504056880 1 Bool.false 46124728 Bool.false Bool.true 8572200 156872 BSN.abs_quadSignPos (BSN.cos_quad_nat3 199 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 46124728 268435456) qz11 rfl (Ns360p162 rfl) (Ns360p120 rfl) RS361to372.d43 RS361to372.d45 RS361to372.d17 (Ns360p164 rfl rfl) rfl 

noncomputable def Ns360p166 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) 8572200 268435456 156872 268435456 8572200 268435456 156872 268435456 4602164831846400 1071525 16777216 19609 16777216 (Ns360p165 rfl rfl rfl rfl) 

noncomputable def Ns360p167 := @Enclosure.Real.IsNear.mulLit_ff qz586 (Zeta.RiemannSiegel.correction qz10) 10340719 33554432 1 33554432 54069038272563 140737488355328 750054080630249 46531332087480320000 559112731376819392797 4722366482869645213696 

noncomputable abbrev qz596 := (@HPow.hPow Real Real Real qz7 qz8 qz9)

noncomputable def Ns360p168 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz596 1 1 0 1 10340719 33554432 1 33554432 10340719 33554432 1 33554432 

noncomputable abbrev qz21 := (@Enclosure.Real.IsNear.of_eq qz350 (@HMul.hMul Real Real Real qz349 qz348 qz347) Bool.false 3720031155917 33554432000 696589 33554432000 (BSN.t_div_two_pi_mk qz348 696589 1000 qz352) (@Enclosure.Real.IsNear.mulLit_ff qz348 qz347 696589 1000 0 1 5340353 33554432 1 33554432 3720031155917 33554432000 696589 33554432000 (Enclosure.Real.IsNear.const Bool.false 696589 1000) RS361to372.d48 rfl))

noncomputable def Ns360p169 := @Enclosure.Real.IsNear.sqrt_image qz8 3720031155917 33554432000 696589 33554432000 176651853 176651887 16777216 qz21 

noncomputable abbrev qz745 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 696589 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz597 := qz745

noncomputable abbrev qz371 := qz597

noncomputable abbrev qz22 := qz371

noncomputable def Ns360p170 := @Enclosure.Real.IsNear.sqrt_image qz22 88325935 8388608 17 16777216 54440116 54440122 16777216 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 353303740 33554432 34 33554432 88325935 8388608 17 16777216 (Ns360p169 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz598 := (Real.sqrt qz745)

noncomputable abbrev qz372 := qz598

noncomputable abbrev qz23 := qz372

noncomputable def Ns360p171 := @Enclosure.Real.IsNear.inv_image qz23 54440119 16777216 3 16777216 5170359 5170360 16777216 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 108880238 33554432 6 33554432 54440119 16777216 3 16777216 (Ns360p170 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns360p172 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz23) Bool.false 10340719 33554432 1 33554432 10340719 33554432 1 33554432 (Ns360p171 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz373 := (@HMul.hMul Real Real Real qz583 qz581 qz585)

noncomputable abbrev qz24 := (Real.cos qz373)

noncomputable abbrev qz599 := (@HMul.hMul Real Real Real qz737 qz740 qz740)

noncomputable abbrev qz600 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz374 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz599 qz585) qz600)

noncomputable abbrev qz25 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz374))

noncomputable def Ns360p173 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz10) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz24) qz25) Bool.false 54069038272563 

noncomputable def Ns360p174 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz24) qz25 17065033 16777216 115 

noncomputable abbrev qz26 := (@Neg.neg Real Real.instNeg (Real.cos qz373))

noncomputable def Ns360p175 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz24) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz26)) Bool.true 17065033 16777216 115 16777216 (BSN.inv_eq_neg_inv_neg qz24) 

noncomputable def Ns360p176 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz26) Bool.false 34130066 33554432 230 33554432 17065033 16777216 

noncomputable def Ns360p177 := @Enclosure.Real.IsNear.recentre' qz24 Bool.true 32988507 33554432 1170904432 177502945280000 32988507 33554432 73181527 11093934080000 

noncomputable abbrev qz27 := qz373

noncomputable def Ns360p178 := @Enclosure.Real.IsNear.cos_image qz27 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 55792863) qz365) Bool.false 55792863 16777216 215 33554432 Bool.true 32988507 33554432 1 

noncomputable def Ns360p179 := nat_lit 458763282030024900833800759 

noncomputable def Ns360p180 := nat_lit 72057594037927936000000000000000 

noncomputable def Ns360p181 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz10 884279719003555 140737488355328 1 500000000000000 4439855 8388608 17 16777216 3926073731816528684525 1180591620717411303424 Ns360p179 

noncomputable def Ns360p182 := @Enclosure.Real.IsNear.subLit_ff_p qz22 qz1 88325935 8388608 17 16777216 10 1 0 1 4439855 4439855 8388608 17 

noncomputable abbrev qz375 := (Enclosure.Real.IsNear.const Bool.false 10 1)

noncomputable def Ns360p183 := @Ns360p182 16777216 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 353303740 33554432 34 33554432 88325935 8388608 17 16777216 (Ns360p169 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns360p184 := @Enclosure.Real.IsNear.recentre' qz27 Bool.false 3926073731816528684525 1180591620717411303424 Ns360p179 Ns360p180 55792863 16777216 215 33554432 (@Ns360p181 Ns360p180 RS361to372.d47 (Ns360p183 rfl rfl) rfl) 

noncomputable def Ns360p185 := nat_lit 25517953923488179138771671563889375390625 

noncomputable def Ns360p186 := nat_lit 535217884764734955396857238543560676143529984 

noncomputable def Ns360p187 := nat_lit 8028268271471024330952858578153410142152949760 

noncomputable abbrev qz376 := (BSN.cosEvenQ 68719476736)

noncomputable abbrev qz377 := (BSN.cosOddQ 68719476736)

noncomputable def Ns360p188 := BSN.cos_dyadic_bound_f 12638963575 68719476736 2 1 33554432 10590333 Ns360p185 Ns360p186 Ns360p185 Ns360p185 Ns360p187 Ns360p185 32988507 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 12638963575) qz376 0 1 Ns360p185 Ns360p186 Ns360p185 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 12638963575) qz377 0 1 Ns360p185 Ns360p187 Ns360p185 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p189 := @Ns360p178 5290000 (Ns360p184 rfl) (Enclosure.sfrac_false_div 55792863 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 55792863) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 444693997262783408766976) qz366) 226375608064910080 72057594037927936 Bool.false 32988507 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q2 55792863 16777216 226375608064910080 72057594037927936 0 444693997262783408766976 Ns360p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 32988507 33554432 444693997262783408766976 Ns360p112 12638963575 68719476736 10590333 10580000 (Ns360p188 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p190 := @Enclosure.Real.IsNear.inv_image qz26 32988507 33554432 73181527 11093934080000 17064918 17065148 16777216 (@Enclosure.Real.IsNear.neg qz24 Bool.true 32988507 33554432 73181527 11093934080000 (Ns360p177 (Ns360p189 rfl rfl) rfl)) 

noncomputable def Ns360p191 := Ns360p175 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz26) Bool.false 17065033 16777216 115 16777216 (@Ns360p176 115 16777216 (Ns360p190 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p192 := @Enclosure.Real.IsNear.recentre' qz25 Bool.true 6336822 16777216 

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz349 qz346 qz374)

noncomputable abbrev qz378 := (@Nat.cast Real Real.instNatCast 33554432)

noncomputable def Ns360p193 := @Enclosure.Real.IsNear.cos_image qz28 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 65703325)) qz378) Bool.true 65703325 33554432 

noncomputable def Ns360p194 := nat_lit 19392198759735323647727122045 

noncomputable def Ns360p195 := nat_lit 9903520314283042199192993792 

noncomputable def Ns360p196 := nat_lit 15844148278731290319969951513614859 

noncomputable def Ns360p197 := @Enclosure.Real.IsNear.recentre' qz28 Bool.true Ns360p194 Ns360p195 Ns360p196 

noncomputable def Ns360p198 := nat_lit 1208925819614629174706176000000000000000 

noncomputable abbrev qz29 := qz374

noncomputable def Ns360p199 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz29 884279719003555 140737488355328 1 500000000000000 21929937261919 

noncomputable abbrev qz379 := (@HSub.hSub Real Real Real qz587 qz599 qz585)

noncomputable abbrev qz30 := qz379

noncomputable abbrev qz380 := qz600

noncomputable abbrev qz31 := qz380

noncomputable def Ns360p200 := @Enclosure.Real.IsNear.subLit_tf qz30 qz31 17531890750815 70368744177664 587123101 281474976710656 1 16 

noncomputable abbrev qz381 := qz599

noncomputable abbrev qz32 := qz381

noncomputable def Ns360p201 := @Enclosure.Real.IsNear.subLit_ff_n qz32 qz10 19712312421025 70368744177664 301910429 281474976710656 4439855 8388608 17 16777216 

noncomputable def Ns360p202 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz10 4439855 8388608 17 16777216 4439855 8388608 17 16777216 19712312421025 70368744177664 

noncomputable def Ns360p203 := nat_lit 602924232610143746180039173327246173850138526707746481465751466852725907491049288006604510556640625 

noncomputable def Ns360p204 := nat_lit 975743491921780970500323514261193594148711042915413329552712293065467609596717903600577236539801600 

noncomputable def Ns360p205 := nat_lit 6472144093077475538449514268995199529417478656077570019256675888497227955899298191070556640625 

noncomputable def Ns360p206 := nat_lit 3636554469651357385055376403502721573971634618933981971784009331853936783099965641249232606556640625 

noncomputable def Ns360p207 := nat_lit 88792657764882068315529439797768617067532704905302612989296818668957552473301329227652528525121945600 

noncomputable abbrev qz601 := (BSN.cosEvenQ 33554432)

noncomputable def Ns360p208 := BSN.cos_dyadic_bound_t 65703325 33554432 4 3 16777216 5290000 Ns360p203 Ns360p204 Ns360p205 Ns360p206 Ns360p207 Ns360p205 6336822 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 65703325) qz601 0 3 Ns360p203 Ns360p204 Ns360p205 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 65703325) (BSN.cosOddQ 33554432) 0 3 Ns360p206 Ns360p207 Ns360p205 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz382 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns360p209 := @Ns360p192 295144304 22187868160000 3168411 8388608 18446519 1386741760000 (@Ns360p193 55 4194304 Bool.true 6336822 16777216 1 5290000 (@Ns360p197 Ns360p198 65703325 33554432 55 4194304 (@Ns360p199 70368744177664 587123101 281474976710656 Ns360p194 Ns360p195 Ns360p196 Ns360p198 RS361to372.d47 (@Ns360p200 0 1 350878996190704 21929937261919 70368744177664 587123101 281474976710656 (@Ns360p201 147068159007412715520 17531890750815 70368744177664 587123101 281474976710656 (@Ns360p202 301910429 281474976710656 (Ns360p183 rfl rfl) (Ns360p183 rfl rfl) rfl) (Ns360p183 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 65703325 33554432) (BSN.cos_neg_of_bound 65703325 33554432 Bool.true 6336822 16777216 1 5290000 (Ns360p208 rfl rfl)) rfl rfl) 

noncomputable abbrev qz33 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 10) (Enclosure.sfrac Bool.false 1 1) Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 10 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1))

noncomputable def Ns360p210 := @Ns360p167 1554795161686738916231 Ns360p74 (Ns360p168 qz33 (@Enclosure.Real.IsNear.of_eq qz596 (@Inv.inv Real Real.instInv qz23) Bool.false 10340719 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz8 (BSN.t_div_two_pi_nonneg qz4 696589 1000 qz11)) Ns360p172) rfl) (@Ns360p173 140737488355328 750054080630249 46531332087480320000 (BSN.correction_mk qz10 (BSN.cos_two_pi_p_ne_zero_mk qz4 696589 1000 10 qz11 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 696589 1000 10 qz11 rfl rfl rfl))) (@Ns360p174 16777216 3168411 8388608 18446519 1386741760000 54069038272563 140737488355328 750054080630249 46531332087480320000 Ns360p191 (Ns360p209 rfl) rfl)) 

noncomputable abbrev qz34 := qz353

noncomputable def Ns360p211 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 860720205796705063197 4722366482869645213696 366527951523047376868231 Ns360p74 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HMul.hMul Real Real Real qz5 qz586 (Zeta.RiemannSiegel.correction qz10))) Bool.true 860720205796705063197 4722366482869645213696 366527951523047376868231 Ns360p74 (BSN.hardyZApproximantRS₀_eq qz4 10 (@BSN.floor_sqrt_eq_dec qz4 696589 1000 10 qz11 rfl rfl rfl)) (@Ns360p76 860720205796705063197 4722366482869645213696 366527951523047376868231 Ns360p74 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10)) Bool.true 1071525 16777216 19609 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (Ns360p166 (Ns360p165 rfl rfl rfl rfl) rfl rfl)) (Ns360p210 rfl) rfl rfl)) 

theorem RS361to372.d49 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 860720205796705063197 4722366482869645213696 366527951523047376868231 Ns360p74 := Ns360p211 

theorem RS361to372.d50 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS361to372.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS361to372.d3 a b h)) 

noncomputable def Ns360p212 := nat_lit 12197909518740441006080000 

noncomputable def Ns360p213 := nat_lit 324564996000445323673306398720 

noncomputable abbrev qz746 := (Enclosure.sfrac Bool.false 697923 1000)

noncomputable abbrev qz602 := qz746

noncomputable abbrev qz383 := qz602

noncomputable abbrev qz35 := qz383

noncomputable abbrev qz747 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 697923 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz603 := qz747

noncomputable abbrev qz384 := qz603

noncomputable abbrev qz36 := qz384

noncomputable abbrev qz748 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 697923 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz604 := qz748

noncomputable abbrev qz385 := qz604

noncomputable abbrev qz37 := qz385

noncomputable abbrev qz605 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz36 qz9))

noncomputable def Ns360p214 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 10) (@HMul.hMul Real Real Real qz5 qz605 (Zeta.RiemannSiegel.correction qz37)) 1115602467 134217728 9823 8388608 35038107242604839169 295147905179352825856 62280605594423314399 Ns360p212 Ns360p213 

noncomputable def Ns360p215 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin BSN.quadSignPos 9 10 697923 1000 199 268435456 134217728 4503599627370496 Bool.false 347445501596 2516 618095470 52 84886744 8 

noncomputable def Ns360p216 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 697923 1000 99 152 268435456 134217728 4503599627370496 Bool.false 347445501596 2516 

noncomputable def Ns360p217 := Ns360p216 558195838 52 94906264 8 589812974 52 89478488 8 Bool.false 930172926 118209 Bool.true 388126850 Bool.true 106609560 14148475504056880 1 Bool.false 266344006 Bool.false Bool.false 247542182 Bool.false Bool.false 1106853813 

noncomputable def Ns360p218 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 697923 1000 27 40 268435456 134217728 4503599627370496 Bool.false 347445501596 2516 

noncomputable def Ns360p219 := Ns360p218 480971758 52 109588312 8 522351262 52 101459064 8 Bool.false 761131194 87678 Bool.false 379498774 Bool.true 249161102 14148475504056880 1 Bool.false 265131678 Bool.false Bool.false 160867457 Bool.false Bool.false 930172926 

noncomputable def Ns360p220 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 697923 1000 208 108 268435456 134217728 4503599627370496 Bool.false 347445501596 2516 

noncomputable def Ns360p221 := Ns360p220 372130544 51 134217720 8 432030192 51 120047984 16 Bool.false 610011075 51551 Bool.false 22290856 Bool.false 382691652 14148475504056880 1 Bool.false 267510472 Bool.false Bool.false 38829078 Bool.false Bool.false 761131194 

noncomputable def Ns360p222 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 697923 1000 516 335 268435456 134217728 4503599627370496 Bool.false 347445501596 2516 

noncomputable def Ns360p223 := Ns360p222 186065264 51 189812528 16 294906480 51 154981288 8 Bool.false 268435360 2571 Bool.false 11041363 Bool.false 368247885 14148475504056880 1 Bool.false 268208409 Bool.false Bool.false 263139618 Bool.false Bool.false 610011075 

noncomputable def Ns360p224 := nat_lit 168419483340133757582792487046712327049162058841646253457 

noncomputable def Ns360p225 := nat_lit 130120437887329820192924937941540129634997592129536000 

noncomputable def Ns360p226 := nat_lit 79483934276528970925879394804640000 

noncomputable def Ns360p227 := nat_lit 332842074893155876718630122887208576320 

noncomputable abbrev qz606 := (@Eq.refl Real qz746)

noncomputable abbrev qz386 := qz606

noncomputable abbrev qz38 := qz386

noncomputable def Ns360p228 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz35 697923 1000 1948387055716 16000000 1395846 4000 2000 Ns360p226 Ns360p227 qz38 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns360p229 := nat_lit 485048112019585221838442362694531501901586729463941209956160 

noncomputable abbrev qz607 := (@HSub.hSub Real Real Real qz741 qz742 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz743 (@Nat.cast Real Real.instNatCast 1395846))))

noncomputable abbrev qz387 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 697923 4000) (Real.log (Enclosure.sfrac Bool.false 1948387055716 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz607))

noncomputable abbrev qz608 := (Enclosure.sfrac Bool.false 697923 2000)

noncomputable abbrev qz39 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz387 qz608) (@HMul.hMul Real Real Real qz349 qz608 (Real.log Real.pi)))

noncomputable def Ns360p230 := @Enclosure.Real.IsNear.addLit_ft_p qz39 (Enclosure.sfrac Bool.true Ns360p226 Ns360p227) 1457292325996473072713 1125899906842624000 20302948958785890903 Ns360p88 Ns360p226 Ns360p227 0 1 Ns360p229 

noncomputable def Ns360p231 := nat_lit 97797232513540975916358828032000 

noncomputable abbrev qz40 := (@HSub.hSub Real Real Real qz353 qz387 qz608)

noncomputable def Ns360p232 := @Enclosure.Real.IsNear.subLit_ff_p qz40 (@HMul.hMul Real Real Real qz5 qz608 (Real.log Real.pi)) 1907051797769573874761 1125899906842624000 2206010851871193 529000000000000000000 26807753549403 67108864000 697923 134217728000 Ns360p231 1457292325996473072713 1125899906842624000 

noncomputable def Ns360p233 := nat_lit 3814103595539147749522000 

noncomputable abbrev qz41 := qz387

noncomputable def Ns360p234 := @Enclosure.Real.IsNear.subLit_ff_p qz41 qz608 2299947518111236209737 1125899906842624000 2206010851871193 529000000000000000000 697923 2000 0 1 Ns360p233 1907051797769573874761 1125899906842624000 2206010851871193 529000000000000000000 

noncomputable def Ns360p235 := nat_lit 5179021392768730247175293769430859776 

noncomputable def Ns360p236 := nat_lit 56625716492969698022916096 

noncomputable def Ns360p237 := nat_lit 9558693927894299903351268236799653048713270739830216845174627098287809043087072224988545372490951424303949208028932255215455557309832155770263094261073927444614958987643621631590400 

noncomputable def Ns360p238 := nat_lit 303832549962232647549745593239451807355078332422700979977533312246112912701876735351994194215962035108281130357554574497000146486995770706376030221662207725540026121394455828234240 

noncomputable def Ns360p239 := nat_lit 30823815376204385370539809723959947234995286142030037164716869987655395929218217441951121125981208206242482745534388822868643354621386460516219810010560931441031435895439360 

noncomputable def Ns360p240 := BSN.log_dyadic_bound 899811055716 2996963055716 8 7 Ns360p237 134217728 42320000 Ns360p238 Ns360p239 83157120 3896774111432 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 899811055716) (BSN.artanhQ 2996963055716) 0 7 Ns360p238 Ns360p237 Ns360p239 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz388 := (Real.log (Enclosure.sfrac Bool.false 1948387055716 16000000))

noncomputable def Ns360p241 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 697923 4000) qz388 697923 4000 0 1 3296050504604919 281474976710656 781250529 33062500000000000 2300389456325378883237 1125899906842624000 545252712951267 132250000000000000000 (Enclosure.Real.IsNear.const Bool.false 697923 4000) (BSN.isNear_log_sfrac 1948387055716 16000000 3296050504604919 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1948387055716) qz356)) Bool.false Ns360p236 Ns360p100 1000000677120000 42320000000000000000000 3296050504604919 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 1948387055716 16000000 16 3896774111432 2097152000000 83157120 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns360p240 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p242 := BSN.arctan_dyadic_bound_f 1000 1395846 1 0 16777216 5290000 0 1 1 0 1 1 12019 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1395846) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1395846) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns360p243 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1395846))) 884279719003555 562949953421312 1 2000000000000000 12019 16777216 1 5290000 14828985754651776253952 883876428285347 562949953421312 200000000529 1058000000000000000 qz17 (Ns360p242 rfl) rfl rfl 

noncomputable abbrev qz389 := (@HMul.hMul Real Real Real qz583 qz588 qz607)

noncomputable abbrev qz42 := qz389

noncomputable abbrev qz390 := qz607

noncomputable abbrev qz43 := qz390

noncomputable def Ns360p244 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 697923 4000) qz388) qz42 2300389456325378883237 1125899906842624000 545252712951267 132250000000000000000 883876428285347 2251799813685248 200000000529 4232000000000000000 Ns360p235 2299947518111236209737 1125899906842624000 2206010851871193 529000000000000000000 (Ns360p241 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz43 1 4 0 1 883876428285347 562949953421312 200000000529 1058000000000000000 883876428285347 2251799813685248 200000000529 4232000000000000000 qz363 Ns360p243 rfl) 

noncomputable def Ns360p245 := @Ns360p230 Ns360p224 Ns360p225 20302948958785890903 Ns360p88 (@Ns360p232 20302948958785890903 Ns360p88 (Ns360p234 (Ns360p244 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 697923 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz608 (Real.log Real.pi) 697923 2000 0 1 38410761 33554432 1 67108864 26807753549403 67108864000 697923 134217728000 (Enclosure.Real.IsNear.const Bool.false 697923 2000) RS361to372.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns360p226 Ns360p227) 

noncomputable def Ns360p246 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz35) Bool.false Ns360p224 Ns360p225 20302948958785890903 Ns360p88 43430687699 33554432 315 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz35) (@HAdd.hAdd Real Real Real qz364 qz39 (Enclosure.sfrac Bool.true Ns360p226 Ns360p227)) Bool.false Ns360p224 Ns360p225 20302948958785890903 Ns360p88 Ns360p228 (Ns360p245 rfl rfl)) 

noncomputable def Ns360p247 := nat_lit 7591954399732038681755648 

noncomputable def Ns360p248 := nat_lit 3503522748914666351110681007002362135544125892443427191829915216018839782877432038478963788265455807905232619799246681145467528926608117041 

noncomputable def Ns360p249 := nat_lit 2487055541146833824090142897164268056351293902853606571756866402945749596552694344800326764476352441854878272140782147948240950414641 

noncomputable def Ns360p250 := nat_lit 17495891127254038719220774965813739841726444925390967123384676732222605158995035285926564067920407904935413891473922895647677070596845751601 

noncomputable def Ns360p251 := BSN.sin_dyadic_bound_f 107888160979 68719476736 4 3 33554432 10590333 Ns360p248 Ns360p114 Ns360p249 Ns360p250 Ns360p117 Ns360p249 33554420 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107888160979) qz594 0 3 Ns360p248 Ns360p114 Ns360p249 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107888160979) qz595 0 3 Ns360p250 Ns360p117 Ns360p249 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz391 := (@Nat.cast Real Real.instNatCast Ns360p100)

noncomputable def Ns360p252 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz35) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 43430687699) qz378) Bool.false 43430687699 33554432 315 33554432 Bool.false 33554420 33554432 1 5290000 (Ns360p246 rfl) (Enclosure.sfrac_false_div 43430687699 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 43430687699) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns360p247) qz391) 226375608064910080 72057594037927936 Bool.false 33554420 33554432 205 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q3 43430687699 33554432 226375608064910080 72057594037927936 205 Ns360p247 Ns360p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554420 33554432 Ns360p247 Ns360p100 107888160979 68719476736 10590333 10580000 (Ns360p251 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p253 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz35) Bool.false Ns360p224 Ns360p225 20302948958785890903 Ns360p88 347445501596 268435456 2516 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz35) (@HAdd.hAdd Real Real Real qz364 qz39 (Enclosure.sfrac Bool.true Ns360p226 Ns360p227)) Bool.false Ns360p224 Ns360p225 20302948958785890903 Ns360p88 Ns360p228 (Ns360p245 rfl rfl)) 

noncomputable def Ns360p254 := Ns360p223 51551 BSN.abs_quadSignPos (BSN.cos_quad_nat0 516 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268208409 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 335 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 263139618 268435456) qz38 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 1) Bool.false 8388605 8388608 106244027 11093934080000 268435360 268435456 2571 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz35)) Bool.false 8388605 8388608 106244027 11093934080000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz35) qz35) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz35)) Bool.false 33554420 33554432 1699904432 177502945280000 8388605 8388608 106244027 11093934080000 (Ns360p252 rfl rfl) rfl)) rfl) (Ns360p253 rfl) RS361to372.d7 

noncomputable def Ns360p255 := nat_lit 14862461840493499618437177361 

noncomputable def Ns360p256 := BSN.cos_dyadic_bound_f 11041363 268435456 2 1 268435456 134217728 Ns360p255 Ns360p155 Ns360p255 Ns360p255 Ns360p156 Ns360p255 268208409 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 11041363) qz367 0 1 Ns360p255 Ns360p155 Ns360p255 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 11041363) qz368 0 1 Ns360p255 Ns360p156 Ns360p255 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p257 := nat_lit 25756543663275774737330598258967441813843413459075476328417468008668986545831054028751122942155049833416040625 

noncomputable def Ns360p258 := nat_lit 871683568514489007341798292243696146469029465094156570908284878217177001794361422139649254553384847460322508800 

noncomputable def Ns360p259 := nat_lit 6218464140573817043743200230455984402468993811464745452032814988560226799855837422521149831523681640625 

noncomputable def Ns360p260 := nat_lit 128689564403996816105114286671909981707592730101966869754741388750039568695848115166542029166264226688353640625 

noncomputable def Ns360p261 := nat_lit 30508924898007115256962940228529365126416031278295479981789970737601195062802649774887723909368469661111287808000 

noncomputable def Ns360p262 := BSN.sin_dyadic_bound_f 368247885 268435456 4 3 268435456 134217728 Ns360p257 Ns360p258 Ns360p259 Ns360p260 Ns360p261 Ns360p259 263139618 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 368247885) qz369 0 3 Ns360p257 Ns360p258 Ns360p259 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 368247885) qz370 0 3 Ns360p260 Ns360p261 Ns360p259 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p263 := nat_lit 246891981507881610397448605696 

noncomputable def Ns360p264 := BSN.cos_dyadic_bound_f 22290856 268435456 2 1 268435456 134217728 Ns360p263 Ns360p155 Ns360p263 Ns360p263 Ns360p156 Ns360p263 267510472 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 22290856) qz367 0 1 Ns360p263 Ns360p155 Ns360p263 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 22290856) qz368 0 1 Ns360p263 Ns360p156 Ns360p263 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p265 := nat_lit 11569314270842203785373835963494550167986209671559139881759554557623013131409046311713137420955986560628555776 

noncomputable def Ns360p266 := nat_lit 9867062156946412345454837874656175701095907816237297706856303613391295401585689852355787232883555434496 

noncomputable def Ns360p267 := nat_lit 70072353684204493986946886947286029464653051211598832215952292097271711821300477357468014544003113803034132480 

noncomputable def Ns360p268 := BSN.cos_dyadic_bound_f 382691652 268435456 4 3 268435456 134217728 Ns360p265 Ns360p129 Ns360p266 Ns360p267 Ns360p132 Ns360p266 38829078 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 382691652) qz367 0 3 Ns360p265 Ns360p129 Ns360p266 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 382691652) qz368 0 3 Ns360p267 Ns360p132 Ns360p266 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p269 := Ns360p221 87678 BSN.abs_quadSignPos (BSN.cos_quad_nat0 208 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 267510472 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 108 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 38829078 268435456) qz38 rfl rfl (Ns360p254 RS361to372.d9 RS361to372.d11 RS361to372.d13 RS361to372.d17 (Ns360p256 rfl rfl) (Ns360p262 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns360p253 rfl) RS361to372.d19 RS361to372.d21 RS361to372.d23 RS361to372.d25 RS361to372.d17 (Ns360p264 rfl rfl) (Ns360p268 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns360p270 := nat_lit 29055815039776850974879305576024129872891437830544641302767196097738464501705505867724179710064291501841125376 

noncomputable def Ns360p271 := nat_lit 8923280119029973531793735377903309637747055024696000922197469998805241295766736517016305734309596696576 

noncomputable def Ns360p272 := nat_lit 145160559232422411401150391978589414287031193694594794349691793664013044706959749253526740918843863152057716736 

noncomputable def Ns360p273 := BSN.sin_dyadic_bound_f 379498774 268435456 4 3 268435456 134217728 Ns360p270 Ns360p258 Ns360p271 Ns360p272 Ns360p261 Ns360p271 265131678 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 379498774) qz369 0 3 Ns360p270 Ns360p258 Ns360p271 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 379498774) qz370 0 3 Ns360p272 Ns360p261 Ns360p271 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p274 := nat_lit 33634239225108766390100071144094572174056452969861353414727135923323136 

noncomputable def Ns360p275 := nat_lit 14853949537421607021200881952524668462129651290925313574431645286656 

noncomputable def Ns360p276 := nat_lit 100873009776251455956257811668378667185245099607002209617032544479396096 

noncomputable def Ns360p277 := BSN.cos_dyadic_bound_f 249161102 268435456 3 2 268435456 134217728 Ns360p274 Ns360p123 Ns360p275 Ns360p276 Ns360p126 Ns360p275 160867457 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 249161102) qz367 0 2 Ns360p274 Ns360p123 Ns360p275 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 249161102) qz368 0 2 Ns360p276 Ns360p126 Ns360p275 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p278 := Ns360p219 118209 BSN.abs_quadSignPos (BSN.cos_quad_nat3 27 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 265131678 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 40 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 160867457 268435456) qz38 rfl rfl (Ns360p269 rfl rfl) (Ns360p253 rfl) RS361to372.d27 RS361to372.d29 RS361to372.d31 RS361to372.d33 RS361to372.d17 (Ns360p273 rfl rfl) (Ns360p277 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p279 := nat_lit 31793638735078624945041514525959971822188896584707227384515848876765719865964462439242645096463768424000000000 

noncomputable def Ns360p280 := nat_lit 11686494284204114088680042006620748684036372374490530916468266417421113805816280586181640625000000000000 

noncomputable def Ns360p281 := nat_lit 158826322014914235831671980765383918371837390977793864156596231000389600948202596588957463181356342120000000000 

noncomputable def Ns360p282 := BSN.sin_dyadic_bound_f 388126850 268435456 4 3 268435456 134217728 Ns360p279 Ns360p258 Ns360p280 Ns360p281 Ns360p261 Ns360p280 266344006 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 388126850) qz369 0 3 Ns360p279 Ns360p258 Ns360p280 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 388126850) qz370 0 3 Ns360p281 Ns360p261 Ns360p280 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p283 := nat_lit 1126833710930433085192170591948788524496092365694646005242318028800000 

noncomputable def Ns360p284 := nat_lit 16686651946432755518947555539039899389847601208012839321600000000 

noncomputable def Ns360p285 := nat_lit 3380467759487406390065473880735287493689497401881521990048310886400000 

noncomputable def Ns360p286 := BSN.cos_dyadic_bound_f 106609560 268435456 3 2 268435456 134217728 Ns360p283 Ns360p123 Ns360p284 Ns360p285 Ns360p126 Ns360p284 247542182 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 106609560) qz367 0 2 Ns360p283 Ns360p123 Ns360p284 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 106609560) qz368 0 2 Ns360p285 Ns360p126 Ns360p284 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p287 := Ns360p217 144885 BSN.abs_quadSignPos (BSN.cos_quad_nat3 99 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 266344006 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 152 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 247542182 268435456) qz38 rfl rfl (Ns360p278 rfl) (Ns360p253 rfl) RS361to372.d35 RS361to372.d37 RS361to372.d39 RS361to372.d41 RS361to372.d17 (Ns360p282 rfl rfl) (Ns360p286 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p288 := nat_lit 590000593961501909072751627361 

noncomputable def Ns360p289 := BSN.sin_dyadic_bound_f 27714887 268435456 2 1 268435456 134217728 Ns360p288 Ns360p135 Ns360p288 Ns360p288 Ns360p136 Ns360p288 27665674 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 27714887) qz369 0 1 Ns360p288 Ns360p135 Ns360p288 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 27714887) qz370 0 1 Ns360p288 Ns360p136 Ns360p288 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p290 := Ns360p215 Bool.false 1106853813 144885 Bool.true 27714887 14148475504056880 1 Bool.false 27665674 Bool.false Bool.false 1115602467 157168 BSN.abs_quadSignPos (BSN.cos_quad_nat3 199 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 27665674 268435456) qz38 rfl (Ns360p287 rfl) (Ns360p253 rfl) RS361to372.d43 RS361to372.d45 RS361to372.d17 (Ns360p289 rfl rfl) rfl 

noncomputable def Ns360p291 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 10) 1115602467 268435456 157168 268435456 1115602467 268435456 157168 268435456 598934513887739904 1115602467 134217728 9823 8388608 (Ns360p290 rfl rfl rfl rfl) 

noncomputable def Ns360p292 := @Enclosure.Real.IsNear.mulLit_ff qz605 (Zeta.RiemannSiegel.correction qz37) 5167887 16777216 1 16777216 6779967759087 17592186044416 1535646958030169 93062664174960640000 35038107242604839169 295147905179352825856 

noncomputable abbrev qz609 := (@HPow.hPow Real Real Real qz7 qz36 qz9)

noncomputable def Ns360p293 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz609 1 1 0 1 5167887 16777216 1 16777216 5167887 16777216 1 16777216 

noncomputable def Ns360p294 := @Enclosure.Real.IsNear.sqrt_image qz36 3727155186819 33554432000 697923 33554432000 176820920 176820954 16777216 (@Enclosure.Real.IsNear.of_eq qz36 (@HMul.hMul Real Real Real qz5 qz35 qz3) Bool.false 3727155186819 33554432000 697923 33554432000 (BSN.t_div_two_pi_mk qz35 697923 1000 qz38) (@Enclosure.Real.IsNear.mulLit_ff qz35 qz3 697923 1000 0 1 5340353 33554432 1 33554432 3727155186819 33554432000 697923 33554432000 (Enclosure.Real.IsNear.const Bool.false 697923 1000) RS361to372.d48 rfl)) 

noncomputable abbrev qz749 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 697923 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz610 := qz749

noncomputable abbrev qz392 := qz610

noncomputable abbrev qz44 := qz392

noncomputable def Ns360p295 := @Enclosure.Real.IsNear.sqrt_image qz44 176820937 16777216 17 16777216 54466161 54466167 16777216 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 353641874 33554432 34 33554432 176820937 16777216 17 16777216 (Ns360p294 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns360p296 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz44) 13616541 4194304 3 16777216 5167886 5167888 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz44) Bool.false 108932328 33554432 6 33554432 13616541 4194304 3 16777216 (Ns360p295 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns360p297 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz44)) Bool.false 10335774 33554432 2 33554432 5167887 16777216 1 16777216 (Ns360p296 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz393 := (@HMul.hMul Real Real Real qz583 qz581 qz604)

noncomputable abbrev qz45 := (Real.cos qz393)

noncomputable abbrev qz611 := (@HMul.hMul Real Real Real qz737 qz748 qz748)

noncomputable abbrev qz394 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz611 qz604) qz600)

noncomputable abbrev qz46 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz394))

noncomputable def Ns360p298 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz37) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz45) qz46) Bool.false 6779967759087 

noncomputable def Ns360p299 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz45) qz46 1081461 1048576 59 

noncomputable abbrev qz47 := (@Neg.neg Real Real.instNeg (Real.cos qz393))

noncomputable def Ns360p300 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz45) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz47)) Bool.true 1081461 1048576 59 8388608 (BSN.inv_eq_neg_inv_neg qz45) 

noncomputable def Ns360p301 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz47) Bool.false 34606752 33554432 236 33554432 1081461 1048576 

noncomputable def Ns360p302 := @Enclosure.Real.IsNear.recentre' qz45 Bool.true 32534111 33554432 1170904432 177502945280000 32534111 33554432 73181527 11093934080000 

noncomputable abbrev qz48 := qz393

noncomputable def Ns360p303 := @Enclosure.Real.IsNear.cos_image qz48 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 113710285) qz378) Bool.false 113710285 33554432 215 33554432 Bool.true 32534111 33554432 1 

noncomputable def Ns360p304 := nat_lit 458763282031477175305466423 

noncomputable def Ns360p305 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz37 884279719003555 140737488355328 1 500000000000000 9048777 16777216 17 16777216 8001649982885831402235 2361183241434822606848 Ns360p304 

noncomputable def Ns360p306 := @Enclosure.Real.IsNear.subLit_ff_p qz44 qz1 176820937 16777216 17 16777216 10 1 0 1 9048777 9048777 16777216 17 

noncomputable def Ns360p307 := @Ns360p306 16777216 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 353641874 33554432 34 33554432 176820937 16777216 17 16777216 (Ns360p294 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns360p308 := @Enclosure.Real.IsNear.recentre' qz48 Bool.false 8001649982885831402235 2361183241434822606848 Ns360p304 Ns360p180 113710285 33554432 215 33554432 (@Ns360p305 Ns360p180 RS361to372.d47 (Ns360p307 rfl rfl) rfl) 

noncomputable def Ns360p309 := nat_lit 83325838363011250165374653534384713911201 

noncomputable def Ns360p310 := BSN.cos_dyadic_bound_f 16990060407 68719476736 2 1 33554432 10590333 Ns360p309 Ns360p186 Ns360p309 Ns360p309 Ns360p187 Ns360p309 32534111 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 16990060407) qz376 0 1 Ns360p309 Ns360p186 Ns360p309 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 16990060407) qz377 0 1 Ns360p309 Ns360p187 Ns360p309 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p311 := @Ns360p303 5290000 (Ns360p308 rfl) (Enclosure.sfrac_false_div 113710285 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 113710285) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1195569214388819093094400) qz391) 226375608064910080 72057594037927936 Bool.false 32534111 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q2 113710285 33554432 226375608064910080 72057594037927936 0 1195569214388819093094400 Ns360p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 32534111 33554432 1195569214388819093094400 Ns360p100 16990060407 68719476736 10590333 10580000 (Ns360p310 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p312 := @Enclosure.Real.IsNear.inv_image qz47 32534111 33554432 73181527 11093934080000 17303258 17303494 16777216 (@Enclosure.Real.IsNear.neg qz45 Bool.true 32534111 33554432 73181527 11093934080000 (Ns360p302 (Ns360p311 rfl rfl) rfl)) 

noncomputable def Ns360p313 := Ns360p300 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz47) Bool.false 1081461 1048576 59 8388608 (@Ns360p301 59 8388608 (Ns360p312 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p314 := @Enclosure.Real.IsNear.recentre' qz46 Bool.true 6269267 16777216 

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz349 qz346 qz394)

noncomputable def Ns360p315 := @Enclosure.Real.IsNear.cos_image qz49 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 65557535)) qz378) Bool.true 65557535 33554432 

noncomputable def Ns360p316 := nat_lit 77396677124098634176949560045 

noncomputable def Ns360p317 := nat_lit 39614081257132168796771975168 

noncomputable def Ns360p318 := nat_lit 15999271742309767246007630272244741 

noncomputable def Ns360p319 := @Enclosure.Real.IsNear.recentre' qz49 Bool.true Ns360p316 Ns360p317 Ns360p318 

noncomputable abbrev qz50 := qz394

noncomputable def Ns360p320 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz50 884279719003555 140737488355328 1 500000000000000 87525107113519 

noncomputable abbrev qz395 := (@HSub.hSub Real Real Real qz587 qz611 qz604)

noncomputable abbrev qz51 := qz395

noncomputable def Ns360p321 := @Enclosure.Real.IsNear.subLit_tf qz51 qz31 69932921069103 281474976710656 592871379 281474976710656 1 16 

noncomputable abbrev qz396 := qz611

noncomputable abbrev qz52 := qz396

noncomputable def Ns360p322 := @Enclosure.Real.IsNear.subLit_ff_n qz52 qz37 81880365195729 281474976710656 307658707 281474976710656 9048777 16777216 17 16777216 

noncomputable def Ns360p323 := @Enclosure.Real.IsNear.mulLit_ff qz37 qz37 9048777 16777216 17 16777216 9048777 16777216 17 16777216 81880365195729 281474976710656 

noncomputable def Ns360p324 := nat_lit 597544699972139009024728186875307254596327415523099162576104803062485281970552042599478246286890625 

noncomputable def Ns360p325 := nat_lit 6301898236536970614281313886222962230679111727281158398144670896716952393737555644824462890625 

noncomputable def Ns360p326 := nat_lit 3604292092529826492823666678277525134364345303082613995806824958048237129497787991996465042728490625 

noncomputable def Ns360p327 := BSN.cos_dyadic_bound_t 65557535 33554432 4 3 16777216 5290000 Ns360p324 Ns360p204 Ns360p325 Ns360p326 Ns360p207 Ns360p325 6269267 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 65557535) qz601 0 3 Ns360p324 Ns360p204 Ns360p325 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 65557535) (BSN.cosOddQ 33554432) 0 3 Ns360p326 Ns360p207 Ns360p325 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p328 := @Ns360p314 2387604432 177502945280000 6269267 16777216 149225277 11093934080000 (@Ns360p315 445 33554432 Bool.true 6269267 16777216 1 5290000 (@Ns360p319 Ns360p198 65557535 33554432 445 33554432 (@Ns360p320 281474976710656 592871379 281474976710656 Ns360p316 Ns360p317 Ns360p318 Ns360p198 RS361to372.d47 (@Ns360p321 0 1 1400401713816304 87525107113519 281474976710656 592871379 281474976710656 (@Ns360p322 1173279722287291957248 69932921069103 281474976710656 592871379 281474976710656 (@Ns360p323 307658707 281474976710656 (Ns360p307 rfl rfl) (Ns360p307 rfl rfl) rfl) (Ns360p307 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 65557535 33554432) (BSN.cos_neg_of_bound 65557535 33554432 Bool.true 6269267 16777216 1 5290000 (Ns360p327 rfl rfl)) rfl rfl) 

noncomputable def Ns360p329 := @Ns360p292 62280605594423314399 Ns360p212 (Ns360p293 qz33 (@Enclosure.Real.IsNear.of_eq qz609 (@Inv.inv Real Real.instInv (Real.sqrt qz44)) Bool.false 5167887 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz36 (BSN.t_div_two_pi_nonneg qz35 697923 1000 qz38)) Ns360p297) rfl) (@Ns360p298 17592186044416 1535646958030169 93062664174960640000 (BSN.correction_mk qz37 (BSN.cos_two_pi_p_ne_zero_mk qz35 697923 1000 10 qz38 rfl rfl (@BSN.floor_sqrt_eq_dec qz35 697923 1000 10 qz38 rfl rfl rfl))) (@Ns360p299 8388608 6269267 16777216 149225277 11093934080000 6779967759087 17592186044416 1535646958030169 93062664174960640000 Ns360p313 (Ns360p328 rfl) rfl)) 

noncomputable def Ns360p330 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz35) (hardyZApproximantRS₀ qz35) Bool.false 2418197661641577807615 295147905179352825856 14345945452323147794399 Ns360p212 (@Eq.refl Real (hardyZApproximantRS₀ qz35)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz35) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 10) (@HMul.hMul Real Real Real qz5 qz605 (Zeta.RiemannSiegel.correction qz37))) Bool.false 2418197661641577807615 295147905179352825856 14345945452323147794399 Ns360p212 (BSN.hardyZApproximantRS₀_eq qz35 10 (@BSN.floor_sqrt_eq_dec qz35 697923 1000 10 qz38 rfl rfl rfl)) (@Ns360p214 2418197661641577807615 295147905179352825856 14345945452323147794399 Ns360p212 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 10)) Bool.false 1115602467 134217728 9823 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz35) qz35 10) (Ns360p291 (Ns360p290 rfl rfl rfl rfl) rfl rfl)) (Ns360p329 rfl) rfl rfl)) 

theorem RS361to372.d51 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz35) Bool.false 2418197661641577807615 295147905179352825856 14345945452323147794399 Ns360p212 := Ns360p330 

noncomputable abbrev qz612 := (@HMul.hMul Real Real Real qz737 (Real.sqrt qz745) qz739)

noncomputable abbrev qz397 := qz612

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv qz397)

noncomputable abbrev qz398 := (@HMul.hMul Real Real Real qz583 (@HMul.hMul Real Real Real qz583 qz612 qz612) qz612)

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz398))

noncomputable abbrev qz399 := (@HMul.hMul Real Real Real qz583 qz598 qz598)

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz349 qz399 qz372))

noncomputable abbrev qz613 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) qz53)

noncomputable def Ns360p331 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz364 (@HAdd.hAdd Real Real Real qz364 qz613 qz54) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz55)) Bool.false 

noncomputable def Ns360p332 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz364 qz613 qz54) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz55) 18654601 1073741824 

noncomputable def Ns360p333 := @Enclosure.Real.IsNear.addLit_ff qz613 qz54 2331825 134217728 25 134217728 

noncomputable def Ns360p334 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) qz53 25 4 0 1 93273 33554432 1 33554432 2331825 

noncomputable def Ns360p335 := @Enclosure.Real.IsNear.recentre' qz53 Bool.false 93273 33554432 1 33554432 93273 33554432 1 33554432 

noncomputable def Ns360p336 := @Enclosure.Real.IsNear.mulLit_ff qz23 qz8 54440119 16777216 3 16777216 3720031155917 33554432000 696589 33554432000 202518938811829034123 562949953421312000 49082483611609 

noncomputable def Ns360p337 := @Enclosure.Real.IsNear.sqrt_image qz8 3720031155917 33554432000 696589 33554432000 176651853 176651887 16777216 qz21 

noncomputable def Ns360p338 := @Enclosure.Real.IsNear.sqrt_image qz22 88325935 8388608 17 16777216 54440116 54440122 16777216 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 353303740 33554432 34 33554432 88325935 8388608 17 16777216 (Ns360p337 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz400 := (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 108880238 33554432 6 33554432 54440119 16777216 3 16777216 (Ns360p338 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns360p339 := @Ns360p336 562949953421312000 qz400 

noncomputable def Ns360p340 := Ns360p339 qz21 

noncomputable abbrev qz56 := qz397

noncomputable def Ns360p341 := @Enclosure.Real.IsNear.inv_image qz56 202518938811829034123 562949953421312000 49082483611609 562949953421312000 46636 46637 16777216 (Ns360p340 rfl) rfl rfl 

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv qz398)

noncomputable def Ns360p342 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz57 1 32 0 1 1 

noncomputable def Ns360p343 := @Enclosure.Real.IsNear.recentre' qz57 Bool.false 1 33554432 1 33554432 

noncomputable def Ns360p344 := nat_lit 8306095671861731486462536548146317674511452761206482932018867 

noncomputable def Ns360p345 := nat_lit 178405961588244985132285746181186892047843328000000000 

noncomputable def Ns360p346 := nat_lit 6039196717433706988884711036878782628172119849443644301 

noncomputable abbrev qz58 := qz398

noncomputable def Ns360p347 := @Enclosure.Real.IsNear.inv_image qz58 Ns360p344 Ns360p345 Ns360p346 Ns360p345 0 1 

noncomputable def Ns360p348 := nat_lit 41013920577469352315377823393083098379129 

noncomputable def Ns360p349 := nat_lit 316912650057057350374175801344000000 

noncomputable def Ns360p350 := nat_lit 3976053479926857262378217327887339 

noncomputable def Ns360p351 := nat_lit 63382530011411470074835160268800000 

noncomputable abbrev qz401 := (@HMul.hMul Real Real Real qz583 qz612 qz612)

noncomputable abbrev qz59 := qz401

noncomputable def Ns360p352 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz56 Ns360p348 Ns360p349 Ns360p350 Ns360p351 202518938811829034123 562949953421312000 49082483611609 

noncomputable def Ns360p353 := @Enclosure.Real.IsNear.mulLit_ff qz56 qz56 202518938811829034123 562949953421312000 49082483611609 562949953421312000 202518938811829034123 562949953421312000 49082483611609 562949953421312000 Ns360p348 

noncomputable def Ns360p354 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz55 13 10 0 1 982093 33554432 1 

noncomputable def Ns360p355 := @Enclosure.Real.IsNear.recentre' qz55 Bool.false 982093 33554432 1 33554432 982093 33554432 

noncomputable abbrev qz60 := qz399

noncomputable def Ns360p356 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz23 2963726556734161 281474976710656 326640723 281474976710656 54440119 16777216 3 16777216 161345626432067976205159 

noncomputable def Ns360p357 := @Enclosure.Real.IsNear.mulLit_ff qz23 qz23 54440119 16777216 3 16777216 54440119 16777216 3 16777216 2963726556734161 281474976710656 326640723 

noncomputable def Ns360p358 := @Ns360p357 281474976710656 qz400 

noncomputable def Ns360p359 := Ns360p358 qz400 

noncomputable def Ns360p360 := @Ns360p356 4722366482869645213696 26673540480490689 4722366482869645213696 (Ns360p359 rfl) qz400 

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz349 qz399 qz372)

noncomputable def Ns360p361 := @Enclosure.Real.IsNear.inv_image qz61 161345626432067976205159 4722366482869645213696 26673540480490689 4722366482869645213696 491046 491047 16777216 (Ns360p360 rfl) 

noncomputable def Ns360p362 := @Ns360p332 201 1073741824 12767209 335544320 13 335544320 19968131686465536 297548349 5368709120 1213 5368709120 (@Ns360p333 1 1073741824 1 1073741824 2503778162966528 18654601 1073741824 201 1073741824 (@Ns360p334 134217728 25 134217728 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns360p335 (Ns360p341 rfl rfl rfl rfl) rfl) rfl) (@Ns360p342 33554432 1 33554432 1 1073741824 1 1073741824 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns360p343 1 33554432 1 33554432 (@Ns360p347 16777216 (@Ns360p352 562949953421312000 Ns360p344 Ns360p345 Ns360p346 Ns360p345 (@Ns360p353 Ns360p349 Ns360p350 Ns360p351 (Ns360p340 rfl) (Ns360p340 rfl) rfl) (Ns360p340 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns360p354 33554432 12767209 335544320 13 335544320 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns360p355 1 33554432 (Ns360p361 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS361to372.d52 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 := @Ns360p331 297548349 5368709120 1213 5368709120 (BSN.hardyZErrorBoundRS₀_mk qz4 696589 1000 qz11 rfl rfl) (Ns360p362 rfl rfl) 

noncomputable def Ns360p363 := nat_lit 780666209199388224389120000 

noncomputable def Ns360p364 := nat_lit 225770329239510728788783661056 

noncomputable abbrev qz750 := (Enclosure.sfrac Bool.false 699257 1000)

noncomputable abbrev qz614 := qz750

noncomputable abbrev qz402 := qz614

noncomputable abbrev qz62 := qz402

noncomputable abbrev qz751 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 699257 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz615 := qz751

noncomputable abbrev qz403 := qz615

noncomputable abbrev qz63 := qz403

noncomputable abbrev qz752 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 699257 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz616 := qz752

noncomputable abbrev qz404 := qz616

noncomputable abbrev qz64 := qz404

noncomputable abbrev qz617 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz63 qz9))

noncomputable def Ns360p365 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 10) (@HMul.hMul Real Real Real qz5 qz617 (Zeta.RiemannSiegel.correction qz64)) 39813337 67108864 4921 4194304 562625542573881400011 4722366482869645213696 4088654907395707055637 Ns360p363 Ns360p364 

noncomputable def Ns360p366 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin BSN.quadSignPos 9 10 699257 1000 199 268435456 134217728 4503599627370496 Bool.false 348289022608 2521 618095470 52 84886744 8 

noncomputable def Ns360p367 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 699257 1000 99 152 268435456 134217728 4503599627370496 Bool.false 348289022608 2521 

noncomputable def Ns360p368 := Ns360p367 558195838 52 94906264 8 589812974 52 89478488 8 Bool.true 253916077 118439 Bool.true 289239086 Bool.true 49899055 14148475504056880 1 Bool.false 236431647 Bool.false Bool.false 263810966 Bool.false Bool.true 82387877 

noncomputable def Ns360p369 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 699257 1000 28 40 268435456 134217728 4503599627370496 Bool.false 348289022608 2521 

noncomputable def Ns360p370 := Ns360p369 480971758 52 109588312 8 522351262 52 101459064 8 Bool.true 438823364 87849 Bool.false 159746032 Bool.true 102456673 14148475504056880 1 Bool.false 222289321 Bool.false Bool.false 249118803 Bool.false Bool.true 253916077 

noncomputable def Ns360p371 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 699257 1000 208 109 268435456 134217728 4503599627370496 Bool.false 348289022608 2521 

noncomputable def Ns360p372 := Ns360p371 372130544 51 134217720 8 432030192 51 120047984 16 Bool.true 374585926 51653 Bool.false 369389722 Bool.false 228226959 14148475504056880 1 Bool.false 51938061 Bool.false Bool.false 201707794 Bool.true Bool.true 438823364 

noncomputable def Ns360p373 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 699257 1000 517 336 268435456 134217728 4503599627370496 Bool.false 348289022608 2521 

noncomputable def Ns360p374 := Ns360p373 186065264 51 189812528 16 294906480 51 154981288 8 Bool.true 268435448 2579 Bool.false 184693885 Bool.false 396706225 14148475504056880 1 Bool.false 170462697 Bool.true Bool.false 24915289 Bool.false Bool.true 374585926 

noncomputable def Ns360p375 := nat_lit 1536964379653491485226529342026327410035719034139261790779 

noncomputable def Ns360p376 := nat_lit 1184578632475041791060837648673641750564555439734784000 

noncomputable def Ns360p377 := nat_lit 80246465549567860415573738267360000 

noncomputable def Ns360p378 := nat_lit 336677496896709780873163040460452109120 

noncomputable abbrev qz618 := (@Eq.refl Real qz750)

noncomputable abbrev qz405 := qz618

noncomputable abbrev qz65 := qz405

noncomputable def Ns360p379 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz62 699257 1000 1955842408196 16000000 1398514 4000 2000 Ns360p377 Ns360p378 qz65 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns360p380 := nat_lit 491828601489117275272489389448424771211430090924563773049280 

noncomputable abbrev qz619 := (@HSub.hSub Real Real Real qz741 qz742 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz743 (@Nat.cast Real Real.instNatCast 1398514))))

noncomputable abbrev qz406 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 699257 4000) (Real.log (Enclosure.sfrac Bool.false 1955842408196 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz619))

noncomputable abbrev qz620 := (Enclosure.sfrac Bool.false 699257 2000)

noncomputable abbrev qz66 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz406 qz620) (@HMul.hMul Real Real Real qz349 qz620 (Real.log Real.pi)))

noncomputable def Ns360p381 := @Enclosure.Real.IsNear.addLit_ft_p qz66 (Enclosure.sfrac Bool.true Ns360p377 Ns360p378) 1460830309040508414819 1125899906842624000 20341559997984569077 Ns360p88 Ns360p377 Ns360p378 0 1 Ns360p380 

noncomputable def Ns360p382 := nat_lit 98034662536477449700943855616000 

noncomputable abbrev qz67 := (@HSub.hSub Real Real Real qz353 qz406 qz620)

noncomputable def Ns360p383 := @Enclosure.Real.IsNear.subLit_ff_p qz67 (@HMul.hMul Real Real Real qz5 qz620 (Real.log Real.pi)) 1911449444609393732451 1125899906842624000 2210179604693937 529000000000000000000 26858993504577 67108864000 699257 134217728000 Ns360p382 1460830309040508414819 1125899906842624000 

noncomputable abbrev qz68 := qz406

noncomputable def Ns360p384 := @Enclosure.Real.IsNear.subLit_ff_p qz68 qz620 461019228037784019527 225179981368524800 2210179604693937 529000000000000000000 699257 2000 0 1 764579777843757492980400 1911449444609393732451 1125899906842624000 2210179604693937 529000000000000000000 

noncomputable def Ns360p385 := nat_lit 1038123011800798916079722372263837696 

noncomputable def Ns360p386 := nat_lit 56644184602120039820165120 

noncomputable def Ns360p387 := nat_lit 9897030408295751022109616820329057202009036400297230054942063900789819776323009970394842591961372153872608470008346865155492445328684461034455532789416331530416975597343173142118400 

noncomputable def Ns360p388 := nat_lit 318452292408086370769542015290536924821744536649466827543018745163637653732916514433125240052003303540662024199506343372112689075044303326380189915742740403535164242167577224151040 

noncomputable def Ns360p389 := nat_lit 34598357677979045782648337106168211583724680466702488933663470814794174693104074662150962485100517566580753998428422722263526887313207128295423061724195219602188400129474560 

noncomputable def Ns360p390 := BSN.log_dyadic_bound 907266408196 3004418408196 8 7 Ns360p387 134217728 42320000 Ns360p388 Ns360p389 83669713 3911684816392 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 907266408196) (BSN.artanhQ 3004418408196) 0 7 Ns360p388 Ns360p387 Ns360p389 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz407 := (Real.log (Enclosure.sfrac Bool.false 1955842408196 16000000))

noncomputable def Ns360p391 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 699257 4000) qz407 699257 4000 0 1 3297125490040055 281474976710656 781250529 33062500000000000 461107615757787747827 225179981368524800 546294901156953 132250000000000000000 (Enclosure.Real.IsNear.const Bool.false 699257 4000) (BSN.isNear_log_sfrac 1955842408196 16000000 3297125490040055 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1955842408196) qz356)) Bool.false Ns360p386 Ns360p100 1000000677120000 42320000000000000000000 3297125490040055 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 1955842408196 16000000 16 3911684816392 2097152000000 83669713 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns360p390 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p392 := BSN.arctan_dyadic_bound_f 1000 1398514 1 0 16777216 5290000 0 1 1 0 1 1 11996 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1398514) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1398514) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns360p393 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1398514))) 884279719003555 562949953421312 1 2000000000000000 11996 16777216 1 5290000 14828998702500704944128 883877200037283 562949953421312 200000000529 1058000000000000000 qz17 (Ns360p392 rfl) rfl rfl 

noncomputable abbrev qz408 := (@HMul.hMul Real Real Real qz583 qz588 qz619)

noncomputable abbrev qz69 := qz408

noncomputable abbrev qz409 := qz619

noncomputable abbrev qz70 := qz409

noncomputable def Ns360p394 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 699257 4000) qz407) qz69 461107615757787747827 225179981368524800 546294901156953 132250000000000000000 883877200037283 2251799813685248 200000000529 4232000000000000000 Ns360p385 461019228037784019527 225179981368524800 2210179604693937 529000000000000000000 (Ns360p391 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz70 1 4 0 1 883877200037283 562949953421312 200000000529 1058000000000000000 883877200037283 2251799813685248 200000000529 4232000000000000000 qz363 Ns360p393 rfl) 

noncomputable def Ns360p395 := @Ns360p381 Ns360p375 Ns360p376 20341559997984569077 Ns360p88 (@Ns360p383 20341559997984569077 Ns360p88 (Ns360p384 (Ns360p394 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 699257 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz620 (Real.log Real.pi) 699257 2000 0 1 38410761 33554432 1 67108864 26858993504577 67108864000 699257 134217728000 (Enclosure.Real.IsNear.const Bool.false 699257 2000) RS361to372.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns360p377 Ns360p378) 

noncomputable def Ns360p396 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns360p375 Ns360p376 20341559997984569077 Ns360p88 21768063913 16777216 79 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz364 qz66 (Enclosure.sfrac Bool.true Ns360p377 Ns360p378)) Bool.false Ns360p375 Ns360p376 20341559997984569077 Ns360p88 Ns360p379 (Ns360p395 rfl rfl)) 

noncomputable def Ns360p397 := nat_lit 3797834119266906864091136 

noncomputable def Ns360p398 := nat_lit 3510396998069606554212079755054733803585033323917433494923831148572142871722948240444395685057382165676005666377282232003861412493978832896 

noncomputable def Ns360p399 := nat_lit 2501694324500869311934868363721581795747788951947373787953034567796276454384006034128735213140412561381127776239100589562107849936896 

noncomputable def Ns360p400 := nat_lit 17530177197472350822879199461147282404839629969557394728429969437385012736033339465333111949449165437662105697940361876690702935970774061056 

noncomputable def Ns360p401 := BSN.sin_dyadic_bound_f 107940937802 68719476736 4 3 33554432 10590333 Ns360p398 Ns360p114 Ns360p399 Ns360p400 Ns360p117 Ns360p399 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107940937802) qz594 0 3 Ns360p398 Ns360p114 Ns360p399 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107940937802) qz595 0 3 Ns360p400 Ns360p117 Ns360p399 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p402 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz62) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21768063913) qz365) Bool.false 21768063913 16777216 79 8388608 Bool.true 33554431 33554432 1 5290000 (Ns360p396 rfl) (Enclosure.sfrac_false_div 21768063913 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21768063913) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns360p397) qz366) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 206 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q1 21768063913 16777216 226375608064910080 72057594037927936 206 Ns360p397 Ns360p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554431 33554432 Ns360p397 Ns360p112 107940937802 68719476736 10590333 10580000 (Ns360p401 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p403 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns360p375 Ns360p376 20341559997984569077 Ns360p88 348289022608 268435456 2521 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz364 qz66 (Enclosure.sfrac Bool.true Ns360p377 Ns360p378)) Bool.false Ns360p375 Ns360p376 20341559997984569077 Ns360p88 Ns360p379 (Ns360p395 rfl rfl)) 

noncomputable def Ns360p404 := Ns360p374 51653 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 517 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 170462697 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 336 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 24915289 268435456) qz65 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) Bool.true 33554431 33554432 26643663 2773483520000 268435448 268435456 2579 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.true 33554431 33554432 26643663 2773483520000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz62) qz62) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.true 33554431 33554432 426298608 44375736320000 33554431 33554432 26643663 2773483520000 (Ns360p402 rfl rfl) rfl)) rfl) (Ns360p403 rfl) RS361to372.d7 

noncomputable def Ns360p405 := nat_lit 18271893353002163549500659505602374489005622123654161994794642430430625 

noncomputable def Ns360p406 := nat_lit 1354004580502798213975441307989676000659709311744440099342375390625 

noncomputable def Ns360p407 := nat_lit 47852766583780090480155290847793283233870799365922838035729890138590625 

noncomputable def Ns360p408 := BSN.sin_dyadic_bound_f 184693885 268435456 3 2 268435456 134217728 Ns360p405 Ns360p144 Ns360p406 Ns360p407 Ns360p147 Ns360p406 170462697 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 184693885) qz369 0 2 Ns360p405 Ns360p144 Ns360p406 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 184693885) qz370 0 2 Ns360p407 Ns360p147 Ns360p406 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p409 := nat_lit 13364497678772325147903854677981820553403404986475531505029941771084942552147389966381577912066559298837890625 

noncomputable def Ns360p410 := nat_lit 15192462891166400155195014497825432001683679751859345205096532928001475497496253130197584629058837890625 

noncomputable def Ns360p411 := nat_lit 80924841954008971056616257644137463178881809679988030625209857158169660004251364267462893104161672514837890625 

noncomputable def Ns360p412 := BSN.cos_dyadic_bound_f 396706225 268435456 4 3 268435456 134217728 Ns360p409 Ns360p129 Ns360p410 Ns360p411 Ns360p132 Ns360p410 24915289 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 396706225) qz367 0 3 Ns360p409 Ns360p129 Ns360p410 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 396706225) qz368 0 3 Ns360p411 Ns360p132 Ns360p410 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p413 := nat_lit 10039456874510471758091853711459715265877208437234138174741530944321660452148171484412610306348775305961476096 

noncomputable def Ns360p414 := nat_lit 6453832476437141495605039137581211211421222554761586970251636478997788004805252336970016195800071868416 

noncomputable def Ns360p415 := nat_lit 60819526149116719358921262365920644622449868207916143677291209308637410288413023017767953674623785747222302720 

noncomputable def Ns360p416 := BSN.cos_dyadic_bound_f 369389722 268435456 4 3 268435456 134217728 Ns360p413 Ns360p129 Ns360p414 Ns360p415 Ns360p132 Ns360p414 51938061 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 369389722) qz367 0 3 Ns360p413 Ns360p129 Ns360p414 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 369389722) qz368 0 3 Ns360p415 Ns360p132 Ns360p414 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p417 := nat_lit 42607309611498541296787022341588350914319009680101848465007180375662465 

noncomputable def Ns360p418 := nat_lit 7360978486931983594906316089542551244863710249738468413558305333121 

noncomputable def Ns360p419 := nat_lit 111578655017326861137193305430491183502153341250338597983301616108576641 

noncomputable def Ns360p420 := BSN.sin_dyadic_bound_f 228226959 268435456 3 2 268435456 134217728 Ns360p417 Ns360p144 Ns360p418 Ns360p419 Ns360p147 Ns360p418 201707794 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 228226959) qz369 0 2 Ns360p417 Ns360p144 Ns360p418 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 228226959) qz370 0 2 Ns360p419 Ns360p147 Ns360p418 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p421 := Ns360p372 87849 BSN.abs_quadSignPos (BSN.cos_quad_nat0 208 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 51938061 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 109 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 201707794 268435456) qz65 rfl rfl (Ns360p404 RS361to372.d9 RS361to372.d11 RS361to372.d13 RS361to372.d17 (Ns360p408 rfl rfl) (Ns360p412 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns360p403 rfl) RS361to372.d19 RS361to372.d21 RS361to372.d23 RS361to372.d25 RS361to372.d17 (Ns360p416 rfl rfl) (Ns360p420 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns360p422 := nat_lit 5680957417107112786343689262321625742952290691855486272245694575149056 

noncomputable def Ns360p423 := nat_lit 424073011862878649643164798530937294079009109435042977255339851776 

noncomputable def Ns360p424 := nat_lit 17042024105297612601731781457367815354268714057347588730782573045743616 

noncomputable def Ns360p425 := BSN.cos_dyadic_bound_f 159746032 268435456 3 2 268435456 134217728 Ns360p422 Ns360p123 Ns360p423 Ns360p424 Ns360p126 Ns360p423 222289321 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 159746032) qz367 0 2 Ns360p422 Ns360p123 Ns360p423 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 159746032) qz368 0 2 Ns360p424 Ns360p126 Ns360p423 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p426 := nat_lit 961247623935307264579394075669039206370342858982472478680293160508161 

noncomputable def Ns360p427 := nat_lit 12142888129755254634811866946154657216334154127586202302416935681 

noncomputable def Ns360p428 := nat_lit 2883718586029662283228912603273225309796595908639162263636274647653121 

noncomputable def Ns360p429 := BSN.cos_dyadic_bound_f 102456673 268435456 3 2 268435456 134217728 Ns360p426 Ns360p123 Ns360p427 Ns360p428 Ns360p126 Ns360p427 249118803 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 102456673) qz367 0 2 Ns360p426 Ns360p123 Ns360p427 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 102456673) qz368 0 2 Ns360p428 Ns360p126 Ns360p427 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p430 := Ns360p370 118439 BSN.abs_quadSignPos (BSN.cos_quad_nat0 28 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 222289321 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 40 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 249118803 268435456) qz65 rfl rfl (Ns360p421 rfl rfl) (Ns360p403 rfl) RS361to372.d27 RS361to372.d29 RS361to372.d31 RS361to372.d33 RS361to372.d17 (Ns360p425 rfl rfl) (Ns360p429 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p431 := nat_lit 109941780147820954563308250618604808388929318572246815315992318130929920 

noncomputable def Ns360p432 := nat_lit 48984180178244047528687525827270283515286262312541342636445073817856 

noncomputable def Ns360p433 := nat_lit 287863449809718676350760876578339870083409180407378496987139922128158976 

noncomputable def Ns360p434 := BSN.sin_dyadic_bound_f 289239086 268435456 3 2 268435456 134217728 Ns360p431 Ns360p144 Ns360p432 Ns360p433 Ns360p147 Ns360p432 236431647 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 289239086) qz369 0 2 Ns360p431 Ns360p144 Ns360p432 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 289239086) qz370 0 2 Ns360p433 Ns360p147 Ns360p432 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p435 := nat_lit 6199680142775458638135943650625 

noncomputable def Ns360p436 := BSN.cos_dyadic_bound_f 49899055 268435456 2 1 268435456 134217728 Ns360p435 Ns360p155 Ns360p435 Ns360p435 Ns360p156 Ns360p435 263810966 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 49899055) qz367 0 1 Ns360p435 Ns360p155 Ns360p435 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 49899055) qz368 0 1 Ns360p435 Ns360p156 Ns360p435 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p437 := Ns360p368 145166 BSN.abs_quadSignPos (BSN.cos_quad_nat3 99 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 236431647 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 152 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 263810966 268435456) qz65 rfl rfl (Ns360p430 rfl) (Ns360p403 rfl) RS361to372.d35 RS361to372.d37 RS361to372.d39 RS361to372.d41 RS361to372.d17 (Ns360p434 rfl rfl) (Ns360p436 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p438 := BSN.sin_dyadic_bound_f 8733232 268435456 1 0 268435456 134217728 0 1 1 0 1 1 8731691 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 8733232) qz369 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 8733232) qz370 0 0 rfl) rfl rfl 

noncomputable def Ns360p439 := Ns360p366 Bool.true 82387877 145166 Bool.true 8733232 14148475504056880 1 Bool.false 8731691 Bool.false Bool.true 79626674 157472 BSN.abs_quadSignPos (BSN.cos_quad_nat3 199 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 8731691 268435456) qz65 rfl (Ns360p437 rfl) (Ns360p403 rfl) RS361to372.d43 RS361to372.d45 RS361to372.d17 (Ns360p438 rfl rfl) rfl 

noncomputable def Ns360p440 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 10) 79626674 268435456 157472 268435456 79626674 268435456 157472 268435456 42749245089906688 39813337 67108864 4921 4194304 (Ns360p439 rfl rfl rfl rfl) 

noncomputable def Ns360p441 := @Enclosure.Real.IsNear.mulLit_ff qz617 (Zeta.RiemannSiegel.correction qz64) 10330841 33554432 1 33554432 54460768738371 140737488355328 1579600912128419 93062664174960640000 562625542573881400011 4722366482869645213696 

noncomputable abbrev qz621 := (@HPow.hPow Real Real Real qz7 qz63 qz9)

noncomputable def Ns360p442 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz621 1 1 0 1 10330841 33554432 1 33554432 10330841 33554432 1 33554432 

noncomputable def Ns360p443 := @Enclosure.Real.IsNear.sqrt_image qz63 3734279217721 33554432000 699257 33554432000 176989826 176989860 16777216 (@Enclosure.Real.IsNear.of_eq qz63 (@HMul.hMul Real Real Real qz5 qz62 qz3) Bool.false 3734279217721 33554432000 699257 33554432000 (BSN.t_div_two_pi_mk qz62 699257 1000 qz65) (@Enclosure.Real.IsNear.mulLit_ff qz62 qz3 699257 1000 0 1 5340353 33554432 1 33554432 3734279217721 33554432000 699257 33554432000 (Enclosure.Real.IsNear.const Bool.false 699257 1000) RS361to372.d48 rfl)) 

noncomputable abbrev qz753 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 699257 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz622 := qz753

noncomputable abbrev qz410 := qz622

noncomputable abbrev qz71 := qz410

noncomputable def Ns360p444 := @Enclosure.Real.IsNear.sqrt_image qz71 176989843 16777216 17 16777216 54492169 54492175 16777216 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 353979686 33554432 34 33554432 176989843 16777216 17 16777216 (Ns360p443 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns360p445 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz71) 13623043 4194304 3 16777216 5165420 5165421 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz71) Bool.false 108984344 33554432 6 33554432 13623043 4194304 3 16777216 (Ns360p444 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns360p446 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 10330841 33554432 1 33554432 10330841 33554432 1 33554432 (Ns360p445 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz411 := (@HMul.hMul Real Real Real qz583 qz581 qz616)

noncomputable abbrev qz72 := (Real.cos qz411)

noncomputable abbrev qz623 := (@HMul.hMul Real Real Real qz737 qz752 qz752)

noncomputable abbrev qz412 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz623 qz616) qz600)

noncomputable abbrev qz73 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz412))

noncomputable def Ns360p447 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz64) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz72) qz73) Bool.false 54460768738371 

noncomputable def Ns360p448 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz72) qz73 35239493 33554432 245 

noncomputable abbrev qz74 := (@Neg.neg Real Real.instNeg (Real.cos qz411))

noncomputable def Ns360p449 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz72) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz74)) Bool.true 35239493 33554432 245 33554432 (BSN.inv_eq_neg_inv_neg qz72) 

noncomputable def Ns360p450 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz74) Bool.false 35239493 33554432 245 33554432 35239493 33554432 

noncomputable def Ns360p451 := @Enclosure.Real.IsNear.recentre' qz72 Bool.true 31949947 33554432 1170904432 177502945280000 31949947 33554432 73181527 11093934080000 

noncomputable abbrev qz75 := qz411

noncomputable abbrev qz413 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable def Ns360p452 := @Enclosure.Real.IsNear.cos_image qz75 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 28958205) qz413) Bool.false 28958205 8388608 215 33554432 Bool.true 31949947 33554432 1 

noncomputable def Ns360p453 := nat_lit 18350531281317122671906511 

noncomputable def Ns360p454 := nat_lit 2882303761517117440000000000000 

noncomputable def Ns360p455 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz64 884279719003555 140737488355328 1 500000000000000 9217683 16777216 17 16777216 8151010133103845863065 2361183241434822606848 Ns360p453 

noncomputable def Ns360p456 := @Enclosure.Real.IsNear.subLit_ff_p qz71 qz1 176989843 16777216 17 16777216 10 1 0 1 9217683 9217683 16777216 17 

noncomputable def Ns360p457 := @Ns360p456 16777216 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 353979686 33554432 34 33554432 176989843 16777216 17 16777216 (Ns360p443 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns360p458 := @Enclosure.Real.IsNear.recentre' qz75 Bool.false 8151010133103845863065 2361183241434822606848 Ns360p453 Ns360p454 28958205 8388608 215 33554432 (@Ns360p455 Ns360p454 RS361to372.d47 (Ns360p457 rfl rfl) rfl) 

noncomputable def Ns360p459 := nat_lit 1208925819614629174706176 

noncomputable def Ns360p460 := nat_lit 207269029038173938415998207308261325433761 

noncomputable def Ns360p461 := BSN.cos_dyadic_bound_f 21337012087 68719476736 2 1 33554432 10590333 Ns360p460 Ns360p186 Ns360p460 Ns360p460 Ns360p187 Ns360p460 31949947 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 21337012087) qz376 0 1 Ns360p460 Ns360p186 Ns360p460 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 21337012087) qz377 0 1 Ns360p460 Ns360p187 Ns360p460 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz414 := (@Nat.cast Real Real.instNatCast Ns360p459)

noncomputable def Ns360p462 := @Ns360p452 5290000 (Ns360p458 rfl) (Enclosure.sfrac_false_div 28958205 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 28958205) qz413) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 375364686277851459092480) qz414) 226375608064910080 72057594037927936 Bool.false 31949947 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q2 28958205 8388608 226375608064910080 72057594037927936 0 375364686277851459092480 Ns360p459 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 31949947 33554432 375364686277851459092480 Ns360p459 21337012087 68719476736 10590333 10580000 (Ns360p461 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p463 := @Enclosure.Real.IsNear.inv_image qz74 31949947 33554432 73181527 11093934080000 17619624 17619869 16777216 (@Enclosure.Real.IsNear.neg qz72 Bool.true 31949947 33554432 73181527 11093934080000 (Ns360p451 (Ns360p462 rfl rfl) rfl)) 

noncomputable def Ns360p464 := Ns360p449 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz74) Bool.false 35239493 33554432 245 33554432 (@Ns360p450 245 33554432 (Ns360p463 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p465 := @Enclosure.Real.IsNear.recentre' qz73 Bool.true 6181788 16777216 

noncomputable abbrev qz76 := (@HMul.hMul Real Real Real qz349 qz346 qz412)

noncomputable def Ns360p466 := @Enclosure.Real.IsNear.cos_image qz76 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32684563)) qz365) Bool.true 32684563 16777216 

noncomputable def Ns360p467 := nat_lit 77174243416547357449245247525 

noncomputable def Ns360p468 := nat_lit 16154247484110966294974351972570321 

noncomputable def Ns360p469 := @Enclosure.Real.IsNear.recentre' qz76 Bool.true Ns360p467 Ns360p317 Ns360p468 

noncomputable abbrev qz77 := qz412

noncomputable def Ns360p470 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz77 884279719003555 140737488355328 1 500000000000000 87273564866455 

noncomputable abbrev qz415 := (@HSub.hSub Real Real Real qz587 qz623 qz616)

noncomputable abbrev qz78 := qz415

noncomputable def Ns360p471 := @Enclosure.Real.IsNear.subLit_tf qz78 qz31 69681378822039 281474976710656 598614183 281474976710656 1 16 

noncomputable abbrev qz416 := qz623

noncomputable abbrev qz79 := qz416

noncomputable def Ns360p472 := @Enclosure.Real.IsNear.subLit_ff_n qz79 qz64 84965679888489 281474976710656 313401511 281474976710656 9217683 16777216 17 16777216 

noncomputable def Ns360p473 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz64 9217683 16777216 17 16777216 9217683 16777216 17 16777216 84965679888489 281474976710656 

noncomputable def Ns360p474 := nat_lit 144200860424924044565317407189120530528418568012700470737609769792912480287601744952165109453361 

noncomputable def Ns360p475 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600 

noncomputable def Ns360p476 := nat_lit 1486319558453167640109995602881830054540898727476773945395692741871001560170418511326597681 

noncomputable def Ns360p477 := nat_lit 869853138569383796174696751036987461490701814940367909006973208193500931367276725293337119412785 

noncomputable def Ns360p478 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600 

noncomputable def Ns360p479 := BSN.cos_dyadic_bound_t 32684563 16777216 4 3 16777216 5290000 Ns360p474 Ns360p475 Ns360p476 Ns360p477 Ns360p478 Ns360p476 6181788 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 32684563) (BSN.cosEvenQ 16777216) 0 3 Ns360p474 Ns360p475 Ns360p476 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 32684563) (BSN.cosOddQ 16777216) 0 3 Ns360p477 Ns360p478 Ns360p476 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p480 := @Ns360p465 1207027216 88751472640000 1545447 4194304 75439201 5546967040000 (@Ns360p466 225 16777216 Bool.true 6181788 16777216 1 5290000 (@Ns360p469 Ns360p198 32684563 16777216 225 16777216 (@Ns360p470 281474976710656 598614183 281474976710656 Ns360p467 Ns360p317 Ns360p468 Ns360p198 RS361to372.d47 (@Ns360p471 0 1 1396377037863280 87273564866455 281474976710656 598614183 281474976710656 (@Ns360p472 1169059543675173863424 69681378822039 281474976710656 598614183 281474976710656 (@Ns360p473 313401511 281474976710656 (Ns360p457 rfl rfl) (Ns360p457 rfl rfl) rfl) (Ns360p457 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 32684563 16777216) (BSN.cos_neg_of_bound 32684563 16777216 Bool.true 6181788 16777216 1 5290000 (Ns360p479 rfl rfl)) rfl rfl) 

noncomputable def Ns360p481 := @Ns360p441 4088654907395707055637 Ns360p363 (Ns360p442 qz33 (@Enclosure.Real.IsNear.of_eq qz621 (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 10330841 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz63 (BSN.t_div_two_pi_nonneg qz62 699257 1000 qz65)) Ns360p446) rfl) (@Ns360p447 140737488355328 1579600912128419 93062664174960640000 (BSN.correction_mk qz64 (BSN.cos_two_pi_p_ne_zero_mk qz62 699257 1000 10 qz65 rfl rfl (@BSN.floor_sqrt_eq_dec qz62 699257 1000 10 qz65 rfl rfl rfl))) (@Ns360p448 33554432 1545447 4194304 75439201 5546967040000 54460768738371 140737488355328 1579600912128419 93062664174960640000 Ns360p464 (Ns360p480 rfl) rfl)) 

noncomputable def Ns360p482 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (hardyZApproximantRS₀ qz62) Bool.true 3364240068786006104779 4722366482869645213696 920011395717358325935637 Ns360p363 (@Eq.refl Real (hardyZApproximantRS₀ qz62)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 10) (@HMul.hMul Real Real Real qz5 qz617 (Zeta.RiemannSiegel.correction qz64))) Bool.true 3364240068786006104779 4722366482869645213696 920011395717358325935637 Ns360p363 (BSN.hardyZApproximantRS₀_eq qz62 10 (@BSN.floor_sqrt_eq_dec qz62 699257 1000 10 qz65 rfl rfl rfl)) (@Ns360p365 3364240068786006104779 4722366482869645213696 920011395717358325935637 Ns360p363 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 10)) Bool.true 39813337 67108864 4921 4194304 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz62) qz62 10) (Ns360p440 (Ns360p439 rfl rfl rfl rfl) rfl rfl)) (Ns360p481 rfl) rfl rfl)) 

theorem RS361to372.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz62) Bool.true 3364240068786006104779 4722366482869645213696 920011395717358325935637 Ns360p363 := Ns360p482 

noncomputable def Ns360p483 := nat_lit 624532967359510579511296000 

noncomputable def Ns360p484 := nat_lit 850386581371888542255163637760 

noncomputable abbrev qz754 := (Enclosure.sfrac Bool.false 700590 1000)

noncomputable abbrev qz624 := qz754

noncomputable abbrev qz417 := qz624

noncomputable abbrev qz80 := qz417

noncomputable abbrev qz755 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 700590 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz625 := qz755

noncomputable abbrev qz418 := qz625

noncomputable abbrev qz81 := qz418

noncomputable abbrev qz756 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 700590 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz626 := qz756

noncomputable abbrev qz419 := qz626

noncomputable abbrev qz82 := qz419

noncomputable abbrev qz627 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz81 qz9))

noncomputable def Ns360p485 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 10) (@HMul.hMul Real Real Real qz5 qz627 (Zeta.RiemannSiegel.correction qz82)) 106100975 134217728 9861 8388608 1130318603721944748605 9444732965739290427392 3362065949371552031261 Ns360p483 Ns360p484 

noncomputable def Ns360p486 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos BSN.quadSignNeg 9 10 700590 1000 198 268435456 134217728 4503599627370496 Bool.false 349132252877 2526 618095470 52 84886744 8 

noncomputable def Ns360p487 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 700590 1000 99 151 268435456 134217728 4503599627370496 Bool.false 349132252877 2526 

noncomputable def Ns360p488 := Ns360p487 558195838 52 94906264 8 589812974 52 89478488 8 Bool.true 41730149 118668 Bool.true 190083869 Bool.true 414546909 14148475504056880 1 Bool.false 174591781 Bool.false Bool.false 268341287 Bool.false Bool.false 109444464 

noncomputable def Ns360p489 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 700590 1000 28 39 268435456 134217728 4503599627370496 Bool.false 349132252877 2526 

noncomputable def Ns360p490 := Ns360p489 480971758 52 109588312 8 522351262 52 101459064 8 Bool.true 166017946 88020 Bool.false 361840948 Bool.true 377178065 14148475504056880 1 Bool.false 59322677 Bool.false Bool.false 264758796 Bool.false Bool.true 41730149 

noncomputable def Ns360p491 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 700590 1000 209 110 268435456 134217728 4503599627370496 Bool.false 349132252877 2526 

noncomputable def Ns360p492 := Ns360p491 372130544 51 134217720 8 432030192 51 120047984 16 Bool.false 69041674 51755 Bool.false 294912548 Bool.false 73903554 14148475504056880 1 Bool.false 239065209 Bool.true Bool.false 258326277 Bool.true Bool.true 166017946 

noncomputable def Ns360p493 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 700590 1000 518 338 268435456 134217728 4503599627370496 Bool.false 349132252877 2526 

noncomputable def Ns360p494 := Ns360p493 186065264 51 189812528 16 294906480 51 154981288 8 Bool.false 268435432 2587 Bool.false 358241729 Bool.false 3511299 14148475504056880 1 Bool.false 62827469 Bool.true Bool.false 268412491 Bool.true Bool.false 69041674 

noncomputable def Ns360p495 := nat_lit 3463092876241709609771499715611874852522807435463 

noncomputable def Ns360p496 := nat_lit 2662649777391212958190604136166344122622279680 

noncomputable def Ns360p497 := nat_lit 81014259730963892836382352000000000 

noncomputable def Ns360p498 := nat_lit 340546762295743357977293004886080000000 

noncomputable abbrev qz628 := (@Eq.refl Real qz754)

noncomputable abbrev qz420 := qz628

noncomputable abbrev qz83 := qz420

noncomputable def Ns360p499 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz80 700590 1000 1963306392400 16000000 1401180 4000 2000 Ns360p497 Ns360p498 qz83 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns360p500 := nat_lit 9973707483576123676141919180962199575265685414133440000000 

noncomputable abbrev qz629 := (@HSub.hSub Real Real Real qz741 qz742 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz743 (@Nat.cast Real Real.instNatCast 1401180))))

noncomputable abbrev qz421 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 700590 4000) (Real.log (Enclosure.sfrac Bool.false 1963306392400 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz629))

noncomputable abbrev qz630 := (Enclosure.sfrac Bool.false 700590 2000)

noncomputable abbrev qz84 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz421 qz630) (@HMul.hMul Real Real Real qz349 qz630 (Real.log Real.pi)))

noncomputable def Ns360p501 := @Enclosure.Real.IsNear.addLit_ft_p qz84 (Enclosure.sfrac Bool.true Ns360p497 Ns360p498) 29287341452371632443 22517998136852480 2038014209337575199 216678400000000000000000 Ns360p497 Ns360p498 0 1 Ns360p500 

noncomputable def Ns360p502 := nat_lit 982720107224385179537637376000 

noncomputable abbrev qz85 := (@HSub.hSub Real Real Real qz353 qz421 qz630)

noncomputable def Ns360p503 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (@HMul.hMul Real Real Real qz5 qz630 (Real.log Real.pi)) 191584522755761743399 112589990684262400 442869046502913 105800000000000000000 2691019504899 6710886400 70059 13421772800 Ns360p502 29287341452371632443 22517998136852480 

noncomputable abbrev qz86 := qz421

noncomputable def Ns360p504 := @Enclosure.Real.IsNear.subLit_ff_p qz86 qz630 231024233542505440807 112589990684262400 442869046502913 105800000000000000000 700590 2000 0 1 383169045511523486798000 191584522755761743399 112589990684262400 442869046502913 105800000000000000000 

noncomputable def Ns360p505 := nat_lit 520220326047790973147219937393115136 

noncomputable def Ns360p506 := nat_lit 56662603748135232845381632 

noncomputable def Ns360p507 := nat_lit 10246870301396095642256348844070051800321199359768357474003004197262482971315137339975601483987094062967626250671841949541866378540215399262027266392064000000000000000000000000000000 

noncomputable def Ns360p508 := nat_lit 333724198319874693655574146231968524678722022953462252611568020665662059331064163380688181745669446576866067040788674614351579879747483632971555432038400000000000000000000000000000 

noncomputable def Ns360p509 := nat_lit 38803542166360677075792113454376966856084165320939597387990995872463009401711078815146017881953102761614762337246558389967933197277708122954137600000000000000000000000000000 

noncomputable def Ns360p510 := BSN.log_dyadic_bound 914730392400 3011882392400 8 7 Ns360p507 134217728 42320000 Ns360p508 Ns360p509 84180947 3926612784800 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 914730392400) (BSN.artanhQ 3011882392400) 0 7 Ns360p508 Ns360p507 Ns360p509 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz422 := (Real.log (Enclosure.sfrac Bool.false 1963306392400 16000000))

noncomputable def Ns360p511 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 700590 4000) qz422 700590 4000 0 1 3298197625445623 281474976710656 781250529 33062500000000000 231068427441094901757 112589990684262400 54733630811211 13225000000000000000 (Enclosure.Real.IsNear.const Bool.false 700590 4000) (BSN.isNear_log_sfrac 1963306392400 16000000 3298197625445623 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1963306392400) qz356)) Bool.false Ns360p506 Ns360p100 1000000677120000 42320000000000000000000 3298197625445623 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 1963306392400 16000000 16 3926612784800 2097152000000 84180947 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns360p510 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p512 := BSN.arctan_dyadic_bound_f 1000 1401180 1 0 16777216 5290000 0 1 1 0 1 1 11973 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1401180) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1401180) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns360p513 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1401180))) 884279719003555 562949953421312 1 2000000000000000 11973 16777216 1 5290000 14829011650349633634304 883877971789219 562949953421312 200000000529 1058000000000000000 qz17 (Ns360p512 rfl) rfl rfl 

noncomputable abbrev qz423 := (@HMul.hMul Real Real Real qz583 qz588 qz629)

noncomputable abbrev qz87 := qz423

noncomputable abbrev qz424 := qz629

noncomputable abbrev qz88 := qz424

noncomputable def Ns360p514 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 700590 4000) qz422) qz87 231068427441094901757 112589990684262400 54733630811211 13225000000000000000 883877971789219 2251799813685248 200000000529 4232000000000000000 Ns360p505 231024233542505440807 112589990684262400 442869046502913 105800000000000000000 (Ns360p511 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz88 1 4 0 1 883877971789219 562949953421312 200000000529 1058000000000000000 883877971789219 2251799813685248 200000000529 4232000000000000000 qz363 Ns360p513 rfl) 

noncomputable def Ns360p515 := @Ns360p501 Ns360p495 Ns360p496 2038014209337575199 216678400000000000000000 (@Ns360p503 2038014209337575199 216678400000000000000000 (Ns360p504 (Ns360p514 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 700590 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz630 (Real.log Real.pi) 700590 2000 0 1 38410761 33554432 1 67108864 2691019504899 6710886400 70059 13421772800 (Enclosure.Real.IsNear.const Bool.false 700590 2000) RS361to372.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns360p497 Ns360p498) 

noncomputable def Ns360p516 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz80) Bool.false Ns360p495 Ns360p496 2038014209337575199 216678400000000000000000 43641531609 33554432 317 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz80) (@HAdd.hAdd Real Real Real qz364 qz84 (Enclosure.sfrac Bool.true Ns360p497 Ns360p498)) Bool.false Ns360p495 Ns360p496 2038014209337575199 216678400000000000000000 Ns360p499 (Ns360p515 rfl rfl)) 

noncomputable def Ns360p517 := nat_lit 7594144354940159868796928 

noncomputable def Ns360p518 := nat_lit 3507575090090562960198967050688114404161185620835176982604339995331537604610777750290197928736213464104463974566571936547689090256011268096 

noncomputable def Ns360p519 := nat_lit 2495678126421945037397971799998020492137373291902189370441880814276939810051137332743129344692225550851559889295146094361043861508096 

noncomputable def Ns360p520 := nat_lit 17516102642592385623538318494699293406314763807416833399549169726919677602838222236530925073888049973207923219215969421664202832303329120256 

noncomputable def Ns360p521 := BSN.sin_dyadic_bound_f 107919282114 68719476736 4 3 33554432 10590333 Ns360p518 Ns360p114 Ns360p519 Ns360p520 Ns360p117 Ns360p519 33554429 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107919282114) qz594 0 3 Ns360p518 Ns360p114 Ns360p519 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107919282114) qz595 0 3 Ns360p520 Ns360p117 Ns360p519 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p522 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz80) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 43641531609) qz378) Bool.false 43641531609 33554432 317 33554432 Bool.false 33554429 33554432 1 5290000 (Ns360p516 rfl) (Enclosure.sfrac_false_div 43641531609 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 43641531609) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns360p517) qz391) 226375608064910080 72057594037927936 Bool.false 33554429 33554432 206 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q3 43641531609 33554432 226375608064910080 72057594037927936 206 Ns360p517 Ns360p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554429 33554432 Ns360p517 Ns360p100 107919282114 68719476736 10590333 10580000 (Ns360p521 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p523 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz80) Bool.false Ns360p495 Ns360p496 2038014209337575199 216678400000000000000000 349132252877 268435456 2526 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz80) (@HAdd.hAdd Real Real Real qz364 qz84 (Enclosure.sfrac Bool.true Ns360p497 Ns360p498)) Bool.false Ns360p495 Ns360p496 2038014209337575199 216678400000000000000000 Ns360p499 (Ns360p515 rfl rfl)) 

noncomputable def Ns360p524 := Ns360p494 51755 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 518 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 62827469 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 338 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268412491 268435456) qz83 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 1) Bool.false 33554429 33554432 106905277 11093934080000 268435432 268435456 2587 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz80)) Bool.false 33554429 33554432 106905277 11093934080000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz80) qz80) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz80)) Bool.false 33554429 33554432 1710484432 177502945280000 33554429 33554432 106905277 11093934080000 (Ns360p522 rfl rfl) rfl)) rfl) (Ns360p523 rfl) RS361to372.d7 

noncomputable def Ns360p525 := nat_lit 8879098986558829379362317094106330144235839502879719828762068428437622028215089276181868137453009356011480321 

noncomputable def Ns360p526 := nat_lit 4468009291295282330566930944190304052747443724998930839779478460912658959718639601544183423200810640641 

noncomputable def Ns360p527 := nat_lit 53798833729449596484990544174286458280066884456095305278941258548537151061840578429029014461708126803460236545 

noncomputable def Ns360p528 := BSN.cos_dyadic_bound_f 358241729 268435456 4 3 268435456 134217728 Ns360p525 Ns360p129 Ns360p526 Ns360p527 Ns360p132 Ns360p526 62827469 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 358241729) qz367 0 3 Ns360p525 Ns360p129 Ns360p526 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 358241729) qz368 0 3 Ns360p527 Ns360p132 Ns360p526 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p529 := BSN.cos_dyadic_bound_f 3511299 268435456 1 0 268435456 134217728 0 1 1 0 1 1 268412491 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 3511299) qz367 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 3511299) qz368 0 0 rfl) rfl rfl 

noncomputable def Ns360p530 := nat_lit 118829284618621841286137023820898096147061869201309586772969905648107520 

noncomputable def Ns360p531 := nat_lit 57219757270350139755943162646657184726095129889941054286821610029056 

noncomputable def Ns360p532 := nat_lit 311126913441762350761230202029495663990843598650274727460361565519282176 

noncomputable def Ns360p533 := BSN.sin_dyadic_bound_f 294912548 268435456 3 2 268435456 134217728 Ns360p530 Ns360p144 Ns360p531 Ns360p532 Ns360p147 Ns360p531 239065209 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 294912548) qz369 0 2 Ns360p530 Ns360p144 Ns360p531 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 294912548) qz370 0 2 Ns360p532 Ns360p147 Ns360p531 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p534 := nat_lit 29830552419878282335127197399056 

noncomputable def Ns360p535 := BSN.cos_dyadic_bound_f 73903554 268435456 2 1 268435456 134217728 Ns360p534 Ns360p155 Ns360p534 Ns360p534 Ns360p156 Ns360p534 258326277 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 73903554) qz367 0 1 Ns360p534 Ns360p155 Ns360p534 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 73903554) qz368 0 1 Ns360p534 Ns360p156 Ns360p534 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p536 := Ns360p492 88020 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 209 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 239065209 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 110 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 258326277 268435456) qz83 rfl rfl (Ns360p524 RS361to372.d9 RS361to372.d11 RS361to372.d13 RS361to372.d17 (Ns360p528 rfl rfl) (Ns360p529 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns360p523 rfl) RS361to372.d19 RS361to372.d21 RS361to372.d23 RS361to372.d25 RS361to372.d17 (Ns360p533 rfl rfl) (Ns360p535 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns360p537 := nat_lit 9242053257892065525265434025206093419992404365599929587147235304935600706432726611198352872059353229663666176 

noncomputable def Ns360p538 := nat_lit 5037470904541338136587004813203760684765718073559907534880746794643110601987655293888595015073735376896 

noncomputable def Ns360p539 := nat_lit 55995118661193216453057347768823954971529944398179298366374774142617471118977285759389979986199368734898913280 

noncomputable def Ns360p540 := BSN.cos_dyadic_bound_f 361840948 268435456 4 3 268435456 134217728 Ns360p537 Ns360p129 Ns360p538 Ns360p539 Ns360p132 Ns360p538 59322677 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 361840948) qz367 0 3 Ns360p537 Ns360p129 Ns360p538 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 361840948) qz368 0 3 Ns360p539 Ns360p132 Ns360p538 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p541 := nat_lit 28350673003655161967635521569159305996524360916821455828294669455223047245464164089489880825337386487410290625 

noncomputable def Ns360p542 := nat_lit 8290049771363412036828341174982168787982290114799301536224525238701848802863336382924752336152587890625 

noncomputable def Ns360p543 := nat_lit 141640525272281519134458899330652252989607500283980431889607748180257937509830049056815967524070234482699890625 

noncomputable def Ns360p544 := BSN.sin_dyadic_bound_f 377178065 268435456 4 3 268435456 134217728 Ns360p541 Ns360p258 Ns360p542 Ns360p543 Ns360p261 Ns360p542 264758796 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 377178065) qz369 0 3 Ns360p541 Ns360p258 Ns360p542 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 377178065) qz370 0 3 Ns360p543 Ns360p261 Ns360p542 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p545 := Ns360p490 118668 BSN.abs_quadSignPos (BSN.cos_quad_nat0 28 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 59322677 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 39 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 264758796 268435456) qz83 rfl rfl (Ns360p536 rfl rfl) (Ns360p523 rfl) RS361to372.d27 RS361to372.d29 RS361to372.d31 RS361to372.d33 RS361to372.d17 (Ns360p540 rfl rfl) (Ns360p544 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p546 := nat_lit 20500217169764979024759930043832458870329085615869468561341746392856225 

noncomputable def Ns360p547 := nat_lit 1704363028387326935974905416533571885345977027457503281898012014241 

noncomputable def Ns360p548 := nat_lit 53688285523528984630760619315553480782095140269232724560105310438028961 

noncomputable def Ns360p549 := BSN.sin_dyadic_bound_f 190083869 268435456 3 2 268435456 134217728 Ns360p546 Ns360p144 Ns360p547 Ns360p548 Ns360p147 Ns360p547 174591781 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 190083869) qz369 0 2 Ns360p546 Ns360p144 Ns360p547 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 190083869) qz370 0 2 Ns360p548 Ns360p147 Ns360p547 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p550 := nat_lit 41393215879529896054443558412776159397692199702015329749527155069096670073216841637842666520150860018794196081 

noncomputable def Ns360p551 := nat_lit 25756341516036184475305005257507053362526629960909833720353357586105758765322451317989978510662981741681 

noncomputable def Ns360p552 := nat_lit 206725787723069885637456711394883519365997635933744317762261120090333833537784645281457956021552631204813565041 

noncomputable def Ns360p553 := BSN.sin_dyadic_bound_f 414546909 268435456 4 3 268435456 134217728 Ns360p550 Ns360p258 Ns360p551 Ns360p552 Ns360p261 Ns360p551 268341287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 414546909) qz369 0 3 Ns360p550 Ns360p258 Ns360p551 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 414546909) qz370 0 3 Ns360p552 Ns360p261 Ns360p551 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz631 := (BSN.cos_quad_nat3 151 rfl)

noncomputable def Ns360p554 := Ns360p488 145446 BSN.abs_quadSignPos (BSN.cos_quad_nat3 99 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 174591781 268435456) BSN.abs_quadSignPos qz631 (BSN.sfrac_eq_quadSignPos_mul Bool.false 268341287 268435456) qz83 rfl rfl (Ns360p545 rfl) (Ns360p523 rfl) RS361to372.d35 RS361to372.d37 RS361to372.d39 RS361to372.d41 RS361to372.d17 (Ns360p549 rfl rfl) (Ns360p553 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p555 := nat_lit 15416196133829239324697887162246527854410406003533058609875417065044683549201716500292774150892655012077944721 

noncomputable def Ns360p556 := nat_lit 23288264788442956221024352806484773261752550385360121831384290413310426841897424885017798393143164977041 

noncomputable def Ns360p557 := nat_lit 93321354333269405580852662432709266481584932376769347677681075213834199893906221175572556160841856257298579345 

noncomputable def Ns360p558 := BSN.cos_dyadic_bound_f 411081653 268435456 4 3 268435456 134217728 Ns360p555 Ns360p129 Ns360p556 Ns360p557 Ns360p132 Ns360p556 10573039 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 411081653) qz367 0 3 Ns360p555 Ns360p129 Ns360p556 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 411081653) qz368 0 3 Ns360p557 Ns360p132 Ns360p556 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz632 := (BSN.cos_quad_nat2 198 rfl)

noncomputable def Ns360p559 := Ns360p486 Bool.false 109444464 145446 Bool.true 411081653 14148475504056880 1 Bool.false 10573039 Bool.true Bool.false 106100975 157776 BSN.abs_quadSignNeg qz632 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 10573039 268435456) qz83 rfl (Ns360p554 rfl) (Ns360p523 rfl) RS361to372.d43 RS361to372.d45 RS361to372.d17 (Ns360p558 rfl rfl) rfl 

noncomputable def Ns360p560 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 10) 106100975 268435456 157776 268435456 106100975 268435456 157776 268435456 56962527212339200 106100975 134217728 9861 8388608 (Ns360p559 rfl rfl rfl rfl) 

noncomputable def Ns360p561 := @Enclosure.Real.IsNear.mulLit_ff qz627 (Zeta.RiemannSiegel.correction qz82) 10325923 33554432 1 33554432 109464171263135 281474976710656 649787395500253 37225065669984256000 1130318603721944748605 9444732965739290427392 

noncomputable abbrev qz633 := (@HPow.hPow Real Real Real qz7 qz81 qz9)

noncomputable def Ns360p562 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz633 1 1 0 1 10325923 33554432 1 33554432 10325923 33554432 1 33554432 

noncomputable def Ns360p563 := @Enclosure.Real.IsNear.sqrt_image qz81 374139790827 3355443200 70059 3355443200 177158444 177158478 16777216 (@Enclosure.Real.IsNear.of_eq qz81 (@HMul.hMul Real Real Real qz5 qz80 qz3) Bool.false 374139790827 3355443200 70059 3355443200 (BSN.t_div_two_pi_mk qz80 700590 1000 qz83) (@Enclosure.Real.IsNear.mulLit_ff qz80 qz3 700590 1000 0 1 5340353 33554432 1 33554432 374139790827 3355443200 70059 3355443200 (Enclosure.Real.IsNear.const Bool.false 700590 1000) RS361to372.d48 rfl)) 

noncomputable abbrev qz757 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 700590 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz634 := qz757

noncomputable abbrev qz425 := qz634

noncomputable abbrev qz89 := qz425

noncomputable def Ns360p564 := @Enclosure.Real.IsNear.sqrt_image qz89 177158461 16777216 17 16777216 54518120 54518126 16777216 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 354316922 33554432 34 33554432 177158461 16777216 17 16777216 (Ns360p563 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns360p565 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz89) 54518123 16777216 3 16777216 5162961 5162962 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz89) Bool.false 109036246 33554432 6 33554432 54518123 16777216 3 16777216 (Ns360p564 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns360p566 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 10325923 33554432 1 33554432 10325923 33554432 1 33554432 (Ns360p565 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz426 := (@HMul.hMul Real Real Real qz583 qz581 qz626)

noncomputable abbrev qz90 := (Real.cos qz426)

noncomputable abbrev qz635 := (@HMul.hMul Real Real Real qz737 qz756 qz756)

noncomputable abbrev qz427 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz635 qz626) qz600)

noncomputable abbrev qz91 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz427))

noncomputable def Ns360p567 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz82) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz90) qz91) Bool.false 109464171263135 

noncomputable def Ns360p568 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz90) qz91 36041135 33554432 255 

noncomputable abbrev qz92 := (@Neg.neg Real Real.instNeg (Real.cos qz426))

noncomputable def Ns360p569 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz90) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz92)) Bool.true 36041135 33554432 255 33554432 (BSN.inv_eq_neg_inv_neg qz90) 

noncomputable def Ns360p570 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz92) Bool.false 36041135 33554432 255 33554432 36041135 33554432 

noncomputable def Ns360p571 := @Enclosure.Real.IsNear.recentre' qz90 Bool.true 31239302 33554432 582807216 88751472640000 15619651 16777216 36425451 5546967040000 

noncomputable abbrev qz93 := qz426

noncomputable def Ns360p572 := @Enclosure.Real.IsNear.cos_image qz93 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 117951737) qz378) Bool.false 117951737 33554432 107 16777216 Bool.true 31239302 33554432 1 

noncomputable def Ns360p573 := nat_lit 458763282034376484388696631 

noncomputable def Ns360p574 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz82 884279719003555 140737488355328 1 500000000000000 9386301 16777216 17 16777216 8300115610762787300055 2361183241434822606848 Ns360p573 

noncomputable def Ns360p575 := @Enclosure.Real.IsNear.subLit_ff_p qz89 qz1 177158461 16777216 17 16777216 10 1 0 1 9386301 9386301 16777216 17 

noncomputable def Ns360p576 := @Ns360p575 16777216 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 354316922 33554432 34 33554432 177158461 16777216 17 16777216 (Ns360p563 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns360p577 := @Enclosure.Real.IsNear.recentre' qz93 Bool.false 8300115610762787300055 2361183241434822606848 Ns360p573 Ns360p180 117951737 33554432 107 16777216 (@Ns360p574 Ns360p180 RS361to372.d47 (Ns360p576 rfl rfl) rfl) 

noncomputable def Ns360p578 := nat_lit 1806826867083534133100544 

noncomputable def Ns360p579 := nat_lit 434657279007078988562626626220686467582881 

noncomputable def Ns360p580 := BSN.cos_dyadic_bound_f 25676554103 68719476736 2 1 33554432 10590333 Ns360p579 Ns360p186 Ns360p579 Ns360p579 Ns360p187 Ns360p579 31239302 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 25676554103) qz376 0 1 Ns360p579 Ns360p186 Ns360p579 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 25676554103) qz377 0 1 Ns360p579 Ns360p187 Ns360p579 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p581 := @Ns360p572 5290000 (Ns360p577 rfl) (Enclosure.sfrac_false_div 117951737 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 117951737) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns360p578) qz391) 226375608064910080 72057594037927936 Bool.false 31239302 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q2 117951737 33554432 226375608064910080 72057594037927936 0 Ns360p578 Ns360p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 31239302 33554432 Ns360p578 Ns360p100 25676554103 68719476736 10590333 10580000 (Ns360p580 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p582 := @Enclosure.Real.IsNear.inv_image qz92 15619651 16777216 36425451 5546967040000 18020440 18020695 16777216 (@Enclosure.Real.IsNear.neg qz90 Bool.true 15619651 16777216 36425451 5546967040000 (Ns360p571 (Ns360p581 rfl rfl) rfl)) 

noncomputable def Ns360p583 := Ns360p569 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz92) Bool.false 36041135 33554432 255 33554432 (@Ns360p570 255 33554432 (Ns360p582 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p584 := @Enclosure.Real.IsNear.recentre' qz91 Bool.true 6074402 16777216 

noncomputable abbrev qz94 := (@HMul.hMul Real Real Real qz349 qz346 qz427)

noncomputable def Ns360p585 := @Enclosure.Real.IsNear.cos_image qz94 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 65138411)) qz378) Bool.true 65138411 33554432 

noncomputable def Ns360p586 := nat_lit 76901862301335288318277899205 

noncomputable def Ns360p587 := nat_lit 16308958978261274793191443387351517 

noncomputable def Ns360p588 := @Enclosure.Real.IsNear.recentre' qz94 Bool.true Ns360p586 Ns360p317 Ns360p587 

noncomputable abbrev qz95 := qz427

noncomputable def Ns360p589 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz95 884279719003555 140737488355328 1 500000000000000 86965538899831 

noncomputable abbrev qz428 := (@HSub.hSub Real Real Real qz587 qz635 qz626)

noncomputable abbrev qz96 := qz428

noncomputable def Ns360p590 := @Enclosure.Real.IsNear.subLit_tf qz96 qz31 69373352855415 281474976710656 604347195 281474976710656 1 16 

noncomputable abbrev qz429 := qz635

noncomputable abbrev qz97 := qz429

noncomputable def Ns360p591 := @Enclosure.Real.IsNear.subLit_ff_n qz97 qz82 88102646462601 281474976710656 319134523 281474976710656 9386301 16777216 17 16777216 

noncomputable def Ns360p592 := @Enclosure.Real.IsNear.mulLit_ff qz82 qz82 9386301 16777216 17 16777216 9386301 16777216 17 16777216 88102646462601 281474976710656 

noncomputable def Ns360p593 := nat_lit 582282519281717571178141581313534264652844773357832155571052537622663678131202737304690196146077201 

noncomputable def Ns360p594 := nat_lit 5835067993481477218416127310446297258279300311913847635576786135928353765754851976683456085521 

noncomputable def Ns360p595 := nat_lit 3512743248986951162384745305097528332205717616422311794928959986217232269072352417227416893920951825 

noncomputable def Ns360p596 := BSN.cos_dyadic_bound_t 65138411 33554432 4 3 16777216 5290000 Ns360p593 Ns360p204 Ns360p594 Ns360p595 Ns360p207 Ns360p594 6074402 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 65138411) qz601 0 3 Ns360p593 Ns360p204 Ns360p594 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 65138411) (BSN.cosOddQ 33554432) 0 3 Ns360p595 Ns360p207 Ns360p594 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p597 := @Ns360p584 2429924432 177502945280000 3037201 8388608 151870277 11093934080000 (@Ns360p585 453 33554432 Bool.true 6074402 16777216 1 5290000 (@Ns360p588 Ns360p198 65138411 33554432 453 33554432 (@Ns360p589 281474976710656 604347195 281474976710656 Ns360p586 Ns360p317 Ns360p587 Ns360p198 RS361to372.d47 (@Ns360p590 0 1 1391448622397296 86965538899831 281474976710656 604347195 281474976710656 (@Ns360p591 1163891725499514224640 69373352855415 281474976710656 604347195 281474976710656 (@Ns360p592 319134523 281474976710656 (Ns360p576 rfl rfl) (Ns360p576 rfl rfl) rfl) (Ns360p576 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 65138411 33554432) (BSN.cos_neg_of_bound 65138411 33554432 Bool.true 6074402 16777216 1 5290000 (Ns360p596 rfl rfl)) rfl rfl) 

noncomputable def Ns360p598 := @Ns360p561 3362065949371552031261 Ns360p483 (Ns360p562 qz33 (@Enclosure.Real.IsNear.of_eq qz633 (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 10325923 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz81 (BSN.t_div_two_pi_nonneg qz80 700590 1000 qz83)) Ns360p566) rfl) (@Ns360p567 281474976710656 649787395500253 37225065669984256000 (BSN.correction_mk qz82 (BSN.cos_two_pi_p_ne_zero_mk qz80 700590 1000 10 qz83 rfl rfl (@BSN.floor_sqrt_eq_dec qz80 700590 1000 10 qz83 rfl rfl rfl))) (@Ns360p568 33554432 3037201 8388608 151870277 11093934080000 109464171263135 281474976710656 649787395500253 37225065669984256000 Ns360p583 (Ns360p597 rfl) rfl)) 

noncomputable def Ns360p599 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz80) (hardyZApproximantRS₀ qz80) Bool.false 6335873763053778873795 9444732965739290427392 737514811092801048863261 Ns360p483 (@Eq.refl Real (hardyZApproximantRS₀ qz80)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz80) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 10) (@HMul.hMul Real Real Real qz5 qz627 (Zeta.RiemannSiegel.correction qz82))) Bool.false 6335873763053778873795 9444732965739290427392 737514811092801048863261 Ns360p483 (BSN.hardyZApproximantRS₀_eq qz80 10 (@BSN.floor_sqrt_eq_dec qz80 700590 1000 10 qz83 rfl rfl rfl)) (@Ns360p485 6335873763053778873795 9444732965739290427392 737514811092801048863261 Ns360p483 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 10)) Bool.false 106100975 134217728 9861 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz80) qz80 10) (Ns360p560 (Ns360p559 rfl rfl rfl rfl) rfl rfl)) (Ns360p598 rfl) rfl rfl)) 

theorem RS361to372.d54 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz80) Bool.false 6335873763053778873795 9444732965739290427392 737514811092801048863261 Ns360p483 := Ns360p599 

noncomputable def Ns360p600 := nat_lit 104706993625943758768401547264 

noncomputable abbrev qz758 := (Enclosure.sfrac Bool.false 701923 1000)

noncomputable abbrev qz636 := qz758

noncomputable abbrev qz430 := qz636

noncomputable abbrev qz98 := qz430

noncomputable abbrev qz759 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 701923 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz637 := qz759

noncomputable abbrev qz431 := qz637

noncomputable abbrev qz99 := qz431

noncomputable abbrev qz760 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 701923 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz638 := qz760

noncomputable abbrev qz432 := qz638

noncomputable abbrev qz100 := qz432

noncomputable abbrev qz639 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz99 qz9))

noncomputable def Ns360p601 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 10) (@HMul.hMul Real Real Real qz5 qz639 (Zeta.RiemannSiegel.correction qz100)) 72540661 134217728 158071 134217728 142053493023227517375 1180591620717411303424 1744482695167315837301 Ns360p74 Ns360p600 

noncomputable def Ns360p602 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos BSN.quadSignNeg 9 10 701923 1000 198 268435456 134217728 4503599627370496 Bool.false 349975823485 2531 618095470 52 84886744 8 

noncomputable def Ns360p603 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 701923 1000 99 151 268435456 134217728 4503599627370496 Bool.false 349975823485 2531 

noncomputable def Ns360p604 := Ns360p603 558195838 52 94906264 8 589812974 52 89478488 8 Bool.true 181337172 118889 Bool.true 90588313 Bool.true 357196995 14148475504056880 1 Bool.false 88878643 Bool.false Bool.false 260733010 Bool.false Bool.true 63002822 

noncomputable def Ns360p605 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 701923 1000 29 39 268435456 134217728 4503599627370496 Bool.false 349975823485 2531 

noncomputable def Ns360p606 := Ns360p605 480971758 52 109588312 8 522351262 52 101459064 8 Bool.true 202468653 88182 Bool.false 142618774 Bool.true 229901689 14148475504056880 1 Bool.false 136003200 Bool.true Bool.false 202808889 Bool.false Bool.true 181337172 

noncomputable def Ns360p607 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 701923 1000 210 110 268435456 134217728 4503599627370496 Bool.false 349975823485 2531 

noncomputable def Ns360p608 := Ns360p607 372130544 51 134217720 8 432030192 51 120047984 16 Bool.true 75859717 51848 Bool.false 220775712 Bool.false 341577916 14148475504056880 1 Bool.false 182650249 Bool.true Bool.false 78897013 Bool.true Bool.true 202468653 

noncomputable def Ns360p609 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 701923 1000 520 339 268435456 134217728 4503599627370496 Bool.false 349975823485 2531 

noncomputable def Ns360p610 := Ns360p609 186065264 51 189812528 16 294906480 51 154981288 8 Bool.true 268435408 2587 Bool.false 110472483 Bool.false 32314141 14148475504056880 1 Bool.false 246022450 Bool.false Bool.false 32236152 Bool.false Bool.true 75859717 

noncomputable def Ns360p611 := nat_lit 1580075934661710007402225263500911872935257303895460073657 

noncomputable def Ns360p612 := nat_lit 1211936298372675857400100009592809337339916608077824000 

noncomputable def Ns360p613 := nat_lit 81787919672340490232500588404640000 

noncomputable def Ns360p614 := nat_lit 344453013205076063457028115406276736320 

noncomputable abbrev qz640 := (@Eq.refl Real qz758)

noncomputable abbrev qz433 := qz640

noncomputable abbrev qz101 := qz433

noncomputable def Ns360p615 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz98 701923 1000 1970784591716 16000000 1403846 4000 2000 Ns360p613 Ns360p614 qz101 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns360p616 := nat_lit 505624299091747202368712084320291799339282337246547223570240 

noncomputable abbrev qz641 := (@HSub.hSub Real Real Real qz741 qz742 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz743 (@Nat.cast Real Real.instNatCast 1403846))))

noncomputable abbrev qz434 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 701923 4000) (Real.log (Enclosure.sfrac Bool.false 1970784591716 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz641))

noncomputable abbrev qz642 := (Enclosure.sfrac Bool.false 701923 2000)

noncomputable abbrev qz102 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz434 qz642) (@HMul.hMul Real Real Real qz349 qz642 (Real.log Real.pi)))

noncomputable def Ns360p617 := @Enclosure.Real.IsNear.addLit_ft_p qz102 (Enclosure.sfrac Bool.true Ns360p613 Ns360p614) 1467905263687521030057 1125899906842624000 20418724188766934903 Ns360p88 Ns360p613 Ns360p614 0 1 Ns360p616 

noncomputable def Ns360p618 := nat_lit 19701890941137997460647025049600 

noncomputable abbrev qz103 := (@HSub.hSub Real Real Real qz353 qz434 qz642)

noncomputable def Ns360p619 := @Enclosure.Real.IsNear.subLit_ff_p qz103 (@HMul.hMul Real Real Real qz5 qz642 (Real.log Real.pi)) 384048487599341467221 225179981368524800 2218510860335193 529000000000000000000 26961396593403 67108864000 701923 134217728000 Ns360p618 1467905263687521030057 1125899906842624000 

noncomputable def Ns360p620 := nat_lit 3840484875993414672210000 

noncomputable abbrev qz104 := qz434

noncomputable def Ns360p621 := @Enclosure.Real.IsNear.subLit_ff_p qz104 qz642 2315389958152054919081 1125899906842624000 2218510860335193 529000000000000000000 701923 2000 0 1 Ns360p620 384048487599341467221 225179981368524800 2218510860335193 529000000000000000000 

noncomputable def Ns360p622 := nat_lit 5213794676375491430396105261043417088 

noncomputable def Ns360p623 := nat_lit 56680987874159723437621248 

noncomputable def Ns360p624 := nat_lit 10608863427686356215498740330499076478440191155862588955877339174236020254847853278036080589110601747306318070388837412711894021156353491889737896797335023049371807557973715609190400 

noncomputable def Ns360p625 := nat_lit 349687543934749558855435052366787610144010867204599246824727613511634352613745957115519767745271691652983866788318592010721736462291182945871803522540415576791582740209400534794240 

noncomputable def Ns360p626 := nat_lit 43488671584474378453574078484201976839017923645397653688937627310664190299101395730976960710420264637963133374359515741375924244101955506332831031028665910465965868827279360 

noncomputable def Ns360p627 := BSN.log_dyadic_bound 922208591716 3019360591716 8 7 Ns360p624 134217728 42320000 Ns360p625 Ns360p626 84691209 3941569183432 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 922208591716) (BSN.artanhQ 3019360591716) 0 7 Ns360p625 Ns360p624 Ns360p626 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz435 := (Real.log (Enclosure.sfrac Bool.false 1970784591716 16000000))

noncomputable def Ns360p628 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 701923 4000) qz435 701923 4000 0 1 3299267722419447 281474976710656 781250529 33062500000000000 2315831897523825496581 1125899906842624000 548377715067267 132250000000000000000 (Enclosure.Real.IsNear.const Bool.false 701923 4000) (BSN.isNear_log_sfrac 1970784591716 16000000 3299267722419447 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1970784591716) qz356)) Bool.false Ns360p623 Ns360p100 1000000677120000 42320000000000000000000 3299267722419447 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 1970784591716 16000000 16 3941569183432 2097152000000 84691209 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns360p627 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p629 := BSN.arctan_dyadic_bound_f 1000 1403846 1 0 16777216 5290000 0 1 1 0 1 1 11950 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1403846) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1403846) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns360p630 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1403846))) 884279719003555 562949953421312 1 2000000000000000 11950 16777216 1 5290000 14829024598198562324480 883878743541155 562949953421312 200000000529 1058000000000000000 qz17 (Ns360p629 rfl) rfl rfl 

noncomputable abbrev qz436 := (@HMul.hMul Real Real Real qz583 qz588 qz641)

noncomputable abbrev qz105 := qz436

noncomputable abbrev qz437 := qz641

noncomputable abbrev qz106 := qz437

noncomputable def Ns360p631 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 701923 4000) qz435) qz105 2315831897523825496581 1125899906842624000 548377715067267 132250000000000000000 883878743541155 2251799813685248 200000000529 4232000000000000000 Ns360p622 2315389958152054919081 1125899906842624000 2218510860335193 529000000000000000000 (Ns360p628 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz106 1 4 0 1 883878743541155 562949953421312 200000000529 1058000000000000000 883878743541155 2251799813685248 200000000529 4232000000000000000 qz363 Ns360p630 rfl) 

noncomputable def Ns360p632 := @Ns360p617 Ns360p611 Ns360p612 20418724188766934903 Ns360p88 (@Ns360p619 20418724188766934903 Ns360p88 (Ns360p621 (Ns360p631 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 701923 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz642 (Real.log Real.pi) 701923 2000 0 1 38410761 33554432 1 67108864 26961396593403 67108864000 701923 134217728000 (Enclosure.Real.IsNear.const Bool.false 701923 2000) RS361to372.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns360p613 Ns360p614) 

noncomputable def Ns360p633 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz98) Bool.false Ns360p611 Ns360p612 20418724188766934903 Ns360p88 43746977935 33554432 317 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz98) (@HAdd.hAdd Real Real Real qz364 qz102 (Enclosure.sfrac Bool.true Ns360p613 Ns360p614)) Bool.false Ns360p611 Ns360p612 20418724188766934903 Ns360p88 Ns360p615 (Ns360p632 rfl rfl)) 

noncomputable def Ns360p634 := BSN.cos_dyadic_bound_f 40452853 68719476736 1 0 33554432 10590333 0 1 1 0 1 1 33554426 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 40452853) qz376 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 40452853) qz377 0 0 rfl) rfl rfl 

noncomputable def Ns360p635 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz98) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 43746977935) qz378) Bool.false 43746977935 33554432 317 33554432 Bool.true 33554426 33554432 1 5290000 (Ns360p633 rfl) (Enclosure.sfrac_false_div 43746977935 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 43746977935) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2846616520140280299520) qz391) 226375608064910080 72057594037927936 Bool.false 33554426 33554432 207 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q2 43746977935 33554432 226375608064910080 72057594037927936 207 2846616520140280299520 Ns360p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554426 33554432 2846616520140280299520 Ns360p100 40452853 68719476736 10590333 10580000 (Ns360p634 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p636 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz98) Bool.false Ns360p611 Ns360p612 20418724188766934903 Ns360p88 349975823485 268435456 2531 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz98) (@HAdd.hAdd Real Real Real qz364 qz102 (Enclosure.sfrac Bool.true Ns360p613 Ns360p614)) Bool.false Ns360p611 Ns360p612 20418724188766934903 Ns360p88 Ns360p615 (Ns360p632 rfl rfl)) 

noncomputable def Ns360p637 := Ns360p610 51848 BSN.abs_quadSignPos (BSN.cos_quad_nat0 520 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 246022450 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 339 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 32236152 268435456) qz101 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 1) Bool.true 16777213 16777216 106905277 11093934080000 268435408 268435456 2587 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz98)) Bool.true 16777213 16777216 106905277 11093934080000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz98) qz98) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz98)) Bool.true 33554426 33554432 1710484432 177502945280000 16777213 16777216 106905277 11093934080000 (Ns360p635 rfl rfl) rfl)) rfl) (Ns360p636 rfl) RS361to372.d7 

noncomputable def Ns360p638 := nat_lit 1299249842923744784420046793177562632107179135614193623082539749084321 

noncomputable def Ns360p639 := nat_lit 22183645843088310538741846162400036307726250909567818188126817441 

noncomputable def Ns360p640 := nat_lit 3897705161479548176639062895840363096248921954340761733611242993618081 

noncomputable def Ns360p641 := BSN.cos_dyadic_bound_f 110472483 268435456 3 2 268435456 134217728 Ns360p638 Ns360p123 Ns360p639 Ns360p640 Ns360p126 Ns360p639 246022450 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 110472483) qz367 0 2 Ns360p638 Ns360p123 Ns360p639 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 110472483) qz368 0 2 Ns360p640 Ns360p126 Ns360p639 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p642 := nat_lit 1090361384986916156127984830161 

noncomputable def Ns360p643 := BSN.sin_dyadic_bound_f 32314141 268435456 2 1 268435456 134217728 Ns360p642 Ns360p135 Ns360p642 Ns360p642 Ns360p136 Ns360p642 32236152 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 32314141) qz369 0 1 Ns360p642 Ns360p135 Ns360p642 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 32314141) qz370 0 1 Ns360p642 Ns360p136 Ns360p642 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p644 := nat_lit 20729662848024921956716303251519867134458142692162993469286725846040576 

noncomputable def Ns360p645 := nat_lit 5644303423593863160546034391363317398867505451982150565451054186496 

noncomputable def Ns360p646 := nat_lit 62177699937227578143827817685776874768576693065585016106729275429748736 

noncomputable def Ns360p647 := BSN.cos_dyadic_bound_f 220775712 268435456 3 2 268435456 134217728 Ns360p644 Ns360p123 Ns360p645 Ns360p646 Ns360p126 Ns360p645 182650249 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 220775712) qz367 0 2 Ns360p644 Ns360p123 Ns360p645 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 220775712) qz368 0 2 Ns360p646 Ns360p126 Ns360p645 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p648 := nat_lit 7336370709304768999673741405379488250984080020866688985873235210426095727993315717983568653537491406276263936 

noncomputable def Ns360p649 := nat_lit 2522768585591442309338019759255192794634766076572073617762867532675090154005569079075762149798451347456 

noncomputable def Ns360p650 := nat_lit 44461069744740154732694600006729222978654074933869912987626502028675271200029705760405168178694272454964019200 

noncomputable def Ns360p651 := BSN.cos_dyadic_bound_f 341577916 268435456 4 3 268435456 134217728 Ns360p648 Ns360p129 Ns360p649 Ns360p650 Ns360p132 Ns360p649 78897013 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 341577916) qz367 0 3 Ns360p648 Ns360p129 Ns360p649 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 341577916) qz368 0 3 Ns360p650 Ns360p132 Ns360p649 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p652 := Ns360p608 88182 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 210 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 182650249 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 110 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 78897013 268435456) qz101 rfl rfl (Ns360p637 RS361to372.d9 RS361to372.d11 RS361to372.d13 RS361to372.d17 (Ns360p641 rfl rfl) (Ns360p643 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns360p636 rfl) RS361to372.d19 RS361to372.d21 RS361to372.d23 RS361to372.d25 RS361to372.d17 (Ns360p647 rfl rfl) (Ns360p651 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns360p653 := nat_lit 6496202277745109395978495869982548008062641503586313893854070242894080 

noncomputable def Ns360p654 := nat_lit 171164458414560726005885642936059308411707131414697871423788114176 

noncomputable def Ns360p655 := nat_lit 17013585984971186748292051082722872115569489745465674496873593074442496 

noncomputable def Ns360p656 := BSN.sin_dyadic_bound_f 142618774 268435456 3 2 268435456 134217728 Ns360p653 Ns360p144 Ns360p654 Ns360p655 Ns360p147 Ns360p654 136003200 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 142618774) qz369 0 2 Ns360p653 Ns360p144 Ns360p654 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 142618774) qz370 0 2 Ns360p655 Ns360p147 Ns360p654 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p657 := nat_lit 43871977659910489697284073436929101008671746591949745852871596353290945 

noncomputable def Ns360p658 := nat_lit 7804360011999632398835522796918099804141438947685104489879753753281 

noncomputable def Ns360p659 := nat_lit 114890163002603283135669696726476444765885964458714987064537232752542401 

noncomputable def Ns360p660 := BSN.sin_dyadic_bound_f 229901689 268435456 3 2 268435456 134217728 Ns360p657 Ns360p144 Ns360p658 Ns360p659 Ns360p147 Ns360p658 202808889 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 229901689) qz369 0 2 Ns360p657 Ns360p144 Ns360p658 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 229901689) qz370 0 2 Ns360p659 Ns360p147 Ns360p658 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p661 := Ns360p606 118889 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 29 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 136003200 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 39 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 202808889 268435456) qz101 rfl rfl (Ns360p652 rfl rfl) (Ns360p636 rfl) RS361to372.d27 RS361to372.d29 RS361to372.d31 RS361to372.d33 RS361to372.d17 (Ns360p656 rfl rfl) (Ns360p660 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p662 := nat_lit 67342415184059185709146560468961 

noncomputable def Ns360p663 := BSN.sin_dyadic_bound_f 90588313 268435456 2 1 268435456 134217728 Ns360p662 Ns360p135 Ns360p662 Ns360p662 Ns360p136 Ns360p662 88878643 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 90588313) qz369 0 1 Ns360p662 Ns360p135 Ns360p662 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 90588313) qz370 0 1 Ns360p662 Ns360p136 Ns360p662 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p664 := nat_lit 22798139448093363567097969444805417589930289605174904450016041514362936313501351754584221240858502449465040625 

noncomputable def Ns360p665 := nat_lit 4314133295890852119143298558233386462802636215037669775934268598958251798489139683392148068164306640625 

noncomputable def Ns360p666 := nat_lit 113917696363568140942477942660119931567893703895907704962408410085433006776340438370208849561776823526098640625 

noncomputable def Ns360p667 := BSN.sin_dyadic_bound_f 357196995 268435456 4 3 268435456 134217728 Ns360p664 Ns360p258 Ns360p665 Ns360p666 Ns360p261 Ns360p665 260733010 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 357196995) qz369 0 3 Ns360p664 Ns360p258 Ns360p665 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 357196995) qz370 0 3 Ns360p666 Ns360p261 Ns360p665 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p668 := Ns360p604 145718 BSN.abs_quadSignPos (BSN.cos_quad_nat3 99 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 88878643 268435456) BSN.abs_quadSignPos qz631 (BSN.sfrac_eq_quadSignPos_mul Bool.false 260733010 268435456) qz101 rfl rfl (Ns360p661 rfl) (Ns360p636 rfl) RS361to372.d35 RS361to372.d37 RS361to372.d39 RS361to372.d41 RS361to372.d17 (Ns360p663 rfl rfl) (Ns360p667 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p669 := nat_lit 12665988806407456094751001603544869614712386120626593760166067816071213273160688505959716062921052811110568881 

noncomputable def Ns360p670 := nat_lit 12938383191712879426175385332103678367583504233780334653218143773560810250772661592994854852690777134001 

noncomputable def Ns360p671 := nat_lit 76702771137734493422137915145499090271901373714876897289225067541017451763336586269233082628017827885541151665 

noncomputable def Ns360p672 := BSN.cos_dyadic_bound_f 391432307 268435456 4 3 268435456 134217728 Ns360p669 Ns360p129 Ns360p670 Ns360p671 Ns360p132 Ns360p670 30161295 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 391432307) qz367 0 3 Ns360p669 Ns360p129 Ns360p670 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 391432307) qz368 0 3 Ns360p671 Ns360p132 Ns360p670 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p673 := Ns360p602 Bool.true 63002822 145718 Bool.true 391432307 14148475504056880 1 Bool.false 30161295 Bool.true Bool.true 72540661 158071 BSN.abs_quadSignNeg qz632 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 30161295 268435456) qz101 rfl (Ns360p668 rfl) (Ns360p636 rfl) RS361to372.d43 RS361to372.d45 RS361to372.d17 (Ns360p672 rfl rfl) rfl 

noncomputable def Ns360p674 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 10) 72540661 268435456 158071 268435456 72540661 268435456 158071 268435456 38944970828152832 72540661 134217728 158071 134217728 (Ns360p673 rfl rfl rfl rfl) 

noncomputable def Ns360p675 := @Enclosure.Real.IsNear.mulLit_ff qz639 (Zeta.RiemannSiegel.correction qz100) 10321017 33554432 1 33554432 13763517008375 35184372088832 337339251790589 18612532834992128000 142053493023227517375 1180591620717411303424 

noncomputable abbrev qz643 := (@HPow.hPow Real Real Real qz7 qz99 qz9)

noncomputable def Ns360p676 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz643 1 1 0 1 10321017 33554432 1 33554432 10321017 33554432 1 33554432 

noncomputable def Ns360p677 := @Enclosure.Real.IsNear.sqrt_image qz99 3748516598819 33554432000 701923 33554432000 177326902 177326936 16777216 (@Enclosure.Real.IsNear.of_eq qz99 (@HMul.hMul Real Real Real qz5 qz98 qz3) Bool.false 3748516598819 33554432000 701923 33554432000 (BSN.t_div_two_pi_mk qz98 701923 1000 qz101) (@Enclosure.Real.IsNear.mulLit_ff qz98 qz3 701923 1000 0 1 5340353 33554432 1 33554432 3748516598819 33554432000 701923 33554432000 (Enclosure.Real.IsNear.const Bool.false 701923 1000) RS361to372.d48 rfl)) 

noncomputable abbrev qz761 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 701923 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz644 := qz761

noncomputable abbrev qz438 := qz644

noncomputable abbrev qz107 := qz438

noncomputable def Ns360p678 := @Enclosure.Real.IsNear.sqrt_image qz107 177326919 16777216 17 16777216 54544034 54544041 16777216 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 354653838 33554432 34 33554432 177326919 16777216 17 16777216 (Ns360p677 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns360p679 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz107) 109088075 33554432 7 33554432 5160508 5160509 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz107) Bool.false 109088075 33554432 7 33554432 109088075 33554432 7 33554432 (Ns360p678 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns360p680 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 10321017 33554432 1 33554432 10321017 33554432 1 33554432 (Ns360p679 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz439 := (@HMul.hMul Real Real Real qz583 qz581 qz638)

noncomputable abbrev qz108 := (Real.cos qz439)

noncomputable abbrev qz645 := (@HMul.hMul Real Real Real qz737 qz760 qz760)

noncomputable abbrev qz440 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz645 qz638) qz600)

noncomputable abbrev qz109 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz440))

noncomputable def Ns360p681 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz100) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz108) qz109) Bool.false 13763517008375 

noncomputable def Ns360p682 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz108) qz109 4628765 4194304 135 

noncomputable abbrev qz110 := (@Neg.neg Real Real.instNeg (Real.cos qz439))

noncomputable def Ns360p683 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz108) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz110)) Bool.true 4628765 4194304 135 16777216 (BSN.inv_eq_neg_inv_neg qz108) 

noncomputable def Ns360p684 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz110) Bool.false 37030120 33554432 270 33554432 4628765 4194304 

noncomputable def Ns360p685 := @Enclosure.Real.IsNear.recentre' qz108 Bool.true 30404976 33554432 1170904432 177502945280000 1900311 2097152 73181527 11093934080000 

noncomputable abbrev qz111 := qz439

noncomputable def Ns360p686 := @Enclosure.Real.IsNear.cos_image qz111 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 60034321) qz365) Bool.false 60034321 16777216 215 33554432 Bool.true 30404976 33554432 1 

noncomputable def Ns360p687 := nat_lit 458763282035823527590195767 

noncomputable def Ns360p688 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz100 884279719003555 140737488355328 1 500000000000000 9554759 16777216 17 16777216 8449079603666688168245 2361183241434822606848 Ns360p687 

noncomputable def Ns360p689 := @Enclosure.Real.IsNear.subLit_ff_p qz107 qz1 177326919 16777216 17 16777216 10 1 0 1 9554759 9554759 16777216 17 

noncomputable def Ns360p690 := @Ns360p689 16777216 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 354653838 33554432 34 33554432 177326919 16777216 17 16777216 (Ns360p677 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns360p691 := @Enclosure.Real.IsNear.recentre' qz111 Bool.false 8449079603666688168245 2361183241434822606848 Ns360p687 Ns360p180 60034321 16777216 215 33554432 (@Ns360p688 Ns360p180 RS361to372.d47 (Ns360p690 rfl rfl) rfl) 

noncomputable def Ns360p692 := nat_lit 30395997293841238785182677239563010149388966441774878983021911517565621422107748384668481 

noncomputable def Ns360p693 := nat_lit 20052072892042597411705012245279816272850392000149059967199507548332190919545345701492817920 

noncomputable def Ns360p694 := nat_lit 658198170700579318169947676447924968703989837608329431369582530822989028441238305601 

noncomputable def Ns360p695 := nat_lit 91186675485182315196911691823336134598229491345649420290202995387635218288266362677394241 

noncomputable def Ns360p696 := nat_lit 902343280141916883526725551037591732278267640006707698523977839674948591379540556567176806400 

noncomputable def Ns360p697 := BSN.cos_dyadic_bound_f 30011975543 68719476736 3 2 33554432 10590333 Ns360p692 Ns360p693 Ns360p694 Ns360p695 Ns360p696 Ns360p694 30404976 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 30011975543) qz376 0 2 Ns360p692 Ns360p693 Ns360p694 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 30011975543) qz377 0 2 Ns360p695 Ns360p696 Ns360p694 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p698 := @Ns360p686 5290000 (Ns360p691 rfl) (Enclosure.sfrac_false_div 60034321 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 60034321) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1055952514648626903908352) qz366) 226375608064910080 72057594037927936 Bool.false 30404976 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q2 60034321 16777216 226375608064910080 72057594037927936 0 1055952514648626903908352 Ns360p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 30404976 33554432 1055952514648626903908352 Ns360p112 30011975543 68719476736 10590333 10580000 (Ns360p697 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p699 := @Enclosure.Real.IsNear.inv_image qz110 1900311 2097152 73181527 11093934080000 18514925 18515195 16777216 (@Enclosure.Real.IsNear.neg qz108 Bool.true 1900311 2097152 73181527 11093934080000 (Ns360p685 (Ns360p698 rfl rfl) rfl)) 

noncomputable def Ns360p700 := Ns360p683 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz110) Bool.false 4628765 4194304 135 16777216 (@Ns360p684 135 16777216 (Ns360p699 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p701 := @Enclosure.Real.IsNear.recentre' qz109 Bool.true 5946950 16777216 

noncomputable abbrev qz112 := (@HMul.hMul Real Real Real qz349 qz346 qz440)

noncomputable def Ns360p702 := @Enclosure.Real.IsNear.cos_image qz112 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32432691)) qz365) Bool.true 32432691 16777216 

noncomputable def Ns360p703 := nat_lit 76579527459074139848050176845 

noncomputable def Ns360p704 := nat_lit 16463523668160872838957891721570857 

noncomputable def Ns360p705 := @Enclosure.Real.IsNear.recentre' qz112 Bool.true Ns360p703 Ns360p317 Ns360p704 

noncomputable abbrev qz113 := qz440

noncomputable def Ns360p706 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz113 884279719003555 140737488355328 1 500000000000000 86601022067279 

noncomputable abbrev qz441 := (@HSub.hSub Real Real Real qz587 qz645 qz638)

noncomputable abbrev qz114 := qz441

noncomputable def Ns360p707 := @Enclosure.Real.IsNear.subLit_tf qz114 qz31 69008836022863 281474976710656 610074767 281474976710656 1 16 

noncomputable abbrev qz442 := qz645

noncomputable abbrev qz115 := qz442

noncomputable def Ns360p708 := @Enclosure.Real.IsNear.subLit_ff_n qz115 qz100 91293419548081 281474976710656 324862095 281474976710656 9554759 16777216 17 16777216 

noncomputable def Ns360p709 := @Enclosure.Real.IsNear.mulLit_ff qz100 qz100 9554759 16777216 17 16777216 9554759 16777216 17 16777216 91293419548081 281474976710656 

noncomputable def Ns360p710 := nat_lit 139770745470397793537484936578871056733322265969864220748936145749948895200630104876463704144561 

noncomputable def Ns360p711 := nat_lit 1354552407655315513182079074471852336532352230684323811796824959999920484838895089968904881 

noncomputable def Ns360p712 := nat_lit 843275306885008637994741634160985728139203979426634243137679786646515685139789577785525761899185 

noncomputable def Ns360p713 := BSN.cos_dyadic_bound_t 32432691 16777216 4 3 16777216 5290000 Ns360p710 Ns360p475 Ns360p711 Ns360p712 Ns360p478 Ns360p711 5946950 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 32432691) (BSN.cosEvenQ 16777216) 0 3 Ns360p710 Ns360p475 Ns360p711 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 32432691) (BSN.cosOddQ 16777216) 0 3 Ns360p712 Ns360p478 Ns360p711 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p714 := @Ns360p701 1228187216 88751472640000 2973475 8388608 76761701 5546967040000 (@Ns360p702 229 16777216 Bool.true 5946950 16777216 1 5290000 (@Ns360p705 Ns360p198 32432691 16777216 229 16777216 (@Ns360p706 281474976710656 610074767 281474976710656 Ns360p703 Ns360p317 Ns360p704 Ns360p198 RS361to372.d47 (@Ns360p707 0 1 1385616353076464 86601022067279 281474976710656 610074767 281474976710656 (@Ns360p708 1157776147864153489408 69008836022863 281474976710656 610074767 281474976710656 (@Ns360p709 324862095 281474976710656 (Ns360p690 rfl rfl) (Ns360p690 rfl rfl) rfl) (Ns360p690 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 32432691 16777216) (BSN.cos_neg_of_bound 32432691 16777216 Bool.true 5946950 16777216 1 5290000 (Ns360p713 rfl rfl)) rfl rfl) 

noncomputable def Ns360p715 := @Ns360p675 1744482695167315837301 Ns360p74 (Ns360p676 qz33 (@Enclosure.Real.IsNear.of_eq qz643 (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 10321017 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz99 (BSN.t_div_two_pi_nonneg qz98 701923 1000 qz101)) Ns360p680) rfl) (@Ns360p681 35184372088832 337339251790589 18612532834992128000 (BSN.correction_mk qz100 (BSN.cos_two_pi_p_ne_zero_mk qz98 701923 1000 10 qz101 rfl rfl (@BSN.floor_sqrt_eq_dec qz98 701923 1000 10 qz101 rfl rfl rfl))) (@Ns360p682 16777216 2973475 8388608 76761701 5546967040000 13763517008375 35184372088832 337339251790589 18612532834992128000 Ns360p700 (Ns360p714 rfl) rfl)) 

noncomputable def Ns360p716 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz98) (hardyZApproximantRS₀ qz98) Bool.true 780127895071683516863 1180591620717411303424 369507192415172398973301 Ns360p74 (@Eq.refl Real (hardyZApproximantRS₀ qz98)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz98) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 10) (@HMul.hMul Real Real Real qz5 qz639 (Zeta.RiemannSiegel.correction qz100))) Bool.true 780127895071683516863 1180591620717411303424 369507192415172398973301 Ns360p74 (BSN.hardyZApproximantRS₀_eq qz98 10 (@BSN.floor_sqrt_eq_dec qz98 701923 1000 10 qz101 rfl rfl rfl)) (@Ns360p601 780127895071683516863 1180591620717411303424 369507192415172398973301 Ns360p74 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 10)) Bool.true 72540661 134217728 158071 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz98) qz98 10) (Ns360p674 (Ns360p673 rfl rfl rfl rfl) rfl rfl)) (Ns360p715 rfl) rfl rfl)) 

theorem RS361to372.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz98) Bool.true 780127895071683516863 1180591620717411303424 369507192415172398973301 Ns360p74 := Ns360p716 

noncomputable def Ns360p717 := nat_lit 877307639429891259980446695424 

noncomputable abbrev qz762 := (Enclosure.sfrac Bool.false 703255 1000)

noncomputable abbrev qz646 := qz762

noncomputable abbrev qz443 := qz646

noncomputable abbrev qz116 := qz443

noncomputable abbrev qz763 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 703255 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz647 := qz763

noncomputable abbrev qz444 := qz647

noncomputable abbrev qz117 := qz444

noncomputable abbrev qz764 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 703255 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz648 := qz764

noncomputable abbrev qz445 := qz648

noncomputable abbrev qz118 := qz445

noncomputable abbrev qz649 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz117 qz9))

noncomputable def Ns360p718 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 10) (@HMul.hMul Real Real Real qz5 qz649 (Zeta.RiemannSiegel.correction qz118)) 387805469 134217728 158371 134217728 285894683820607915521 2361183241434822606848 4540483862113771838591 Ns360p363 Ns360p717 

noncomputable def Ns360p719 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos BSN.quadSignNeg 9 10 703255 1000 198 268435456 134217728 4503599627370496 Bool.false 350819100579 2535 618095470 52 84886744 8 

noncomputable def Ns360p720 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 703255 1000 98 151 268435456 134217728 4503599627370496 Bool.false 350819100579 2535 

noncomputable def Ns360p721 := Ns360p720 558195838 52 94906264 8 589812974 52 89478488 8 Bool.false 326449924 119115 Bool.true 412485503 Bool.true 299550783 14148475504056880 1 Bool.false 9170140 Bool.true Bool.false 241138944 Bool.false Bool.false 403587440 

noncomputable def Ns360p722 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 703255 1000 29 39 268435456 134217728 4503599627370496 Bool.false 350819100579 2535 

noncomputable def Ns360p723 := Ns360p722 480971758 52 109588312 8 522351262 52 101459064 8 Bool.false 400971542 88351 Bool.false 345241486 Bool.true 82396476 14148475504056880 1 Bool.false 257631987 Bool.true Bool.false 81108675 Bool.false Bool.false 326449924 

noncomputable def Ns360p724 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 703255 1000 211 111 268435456 134217728 4503599627370496 Bool.false 350819100579 2535 

noncomputable def Ns360p725 := Ns360p724 372130544 51 134217720 8 432030192 51 120047984 16 Bool.false 253932711 51949 Bool.false 146717494 Bool.false 187733366 14148475504056880 1 Bool.false 139520925 Bool.false Bool.false 172799698 Bool.false Bool.false 400971542 

noncomputable def Ns360p726 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 703255 1000 521 340 268435456 134217728 4503599627370496 Bool.false 350819100579 2535 

noncomputable def Ns360p727 := Ns360p726 186065264 51 189812528 16 294906480 51 154981288 8 Bool.false 268435424 2595 Bool.false 284253217 Bool.false 61118376 14148475504056880 1 Bool.false 234030032 Bool.true Bool.false 261507633 Bool.false Bool.false 253932711 

noncomputable def Ns360p728 := nat_lit 20505636037414713424111290394844559582340631030371697 

noncomputable def Ns360p729 := nat_lit 15690251047302665234162440711238934178051601203200 

noncomputable def Ns360p730 := nat_lit 82566891884247721856530376500000000 

noncomputable def Ns360p731 := nat_lit 348393559497287902052829815763045000000 

noncomputable abbrev qz650 := (@Eq.refl Real qz762)

noncomputable abbrev qz446 := qz650

noncomputable abbrev qz119 := qz446

noncomputable def Ns360p732 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz116 703255 1000 1978271380100 16000000 1406510 4000 2000 Ns360p730 Ns360p731 qz119 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns360p733 := nat_lit 102528180187073567120556451974222797911703155151858485000000 

noncomputable abbrev qz651 := (@HSub.hSub Real Real Real qz741 qz742 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz743 (@Nat.cast Real Real.instNatCast 1406510))))

noncomputable abbrev qz447 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 703255 4000) (Real.log (Enclosure.sfrac Bool.false 1978271380100 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz651))

noncomputable abbrev qz652 := (Enclosure.sfrac Bool.false 703255 2000)

noncomputable abbrev qz120 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz447 qz652) (@HMul.hMul Real Real Real qz349 qz652 (Real.log Real.pi)))

noncomputable def Ns360p734 := @Enclosure.Real.IsNear.addLit_ft_p qz120 (Enclosure.sfrac Bool.true Ns360p730 Ns360p731) 294288444733097548433 225179981368524800 4091455468070124511 433356800000000000000000 Ns360p730 Ns360p731 0 1 Ns360p733 

noncomputable def Ns360p735 := nat_lit 3949872642872991935304722022400 

noncomputable abbrev qz121 := (@HSub.hSub Real Real Real qz353 qz447 qz652)

noncomputable def Ns360p736 := @Enclosure.Real.IsNear.subLit_ff_p qz121 (@HMul.hMul Real Real Real qz5 qz652 (Real.log Real.pi)) 384927554583838104209 225179981368524800 444534672630741 105800000000000000000 5402511945411 13421772800 140651 26843545600 Ns360p735 294288444733097548433 225179981368524800 

noncomputable abbrev qz122 := qz447

noncomputable def Ns360p737 := @Enclosure.Real.IsNear.subLit_ff_p qz122 qz652 464107028482499058321 225179981368524800 444534672630741 105800000000000000000 703255 2000 0 1 769855109167676208418000 384927554583838104209 225179981368524800 444534672630741 105800000000000000000 

noncomputable def Ns360p738 := nat_lit 1045076120266905466353479408689348608 

noncomputable def Ns360p739 := nat_lit 56699323361308238428504064 

noncomputable def Ns360p740 := nat_lit 10983137832460573013082549570182474379738310612683982459779591892317552481654399597110992859863429732858829906834597015138552431076639821509428643952570250000000000000000000000000000 

noncomputable def Ns360p741 := nat_lit 366359266821354943903903925603750098020269800849090803184867183410781976151471810866908523647691080283626884301112835393202357569052287288169932448092150000000000000000000000000000 

noncomputable def Ns360p742 := nat_lit 48700931245537300483783037579134359147168063681369667682993898025560467422357388443262361301751247955771344250901849958398138657237986190002171350000000000000000000000000000 

noncomputable def Ns360p743 := BSN.log_dyadic_bound 929695380100 3026847380100 8 7 Ns360p740 134217728 42320000 Ns360p741 Ns360p742 85200121 3956542760200 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 929695380100) (BSN.artanhQ 3026847380100) 0 7 Ns360p741 Ns360p740 Ns360p742 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz448 := (Real.log (Enclosure.sfrac Bool.false 1978271380100 16000000))

noncomputable def Ns360p744 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 703255 4000) qz448 703255 4000 0 1 3300334988238071 281474976710656 781250529 33062500000000000 464195416430672924221 225179981368524800 109883668154379 26450000000000000000 (Enclosure.Real.IsNear.const Bool.false 703255 4000) (BSN.isNear_log_sfrac 1978271380100 16000000 3300334988238071 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1978271380100) qz356)) Bool.false Ns360p739 Ns360p100 1000000677120000 42320000000000000000000 3300334988238071 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 1978271380100 16000000 16 3956542760200 2097152000000 85200121 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns360p743 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p745 := BSN.arctan_dyadic_bound_f 1000 1406510 1 0 16777216 5290000 0 1 1 0 1 1 11928 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1406510) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1406510) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns360p746 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1406510))) 884279719003555 562949953421312 1 2000000000000000 11928 16777216 1 5290000 14829036983097537593344 883879481738659 562949953421312 200000000529 1058000000000000000 qz17 (Ns360p745 rfl) rfl rfl 

noncomputable abbrev qz449 := (@HMul.hMul Real Real Real qz583 qz588 qz651)

noncomputable abbrev qz123 := qz449

noncomputable abbrev qz450 := qz651

noncomputable abbrev qz124 := qz450

noncomputable def Ns360p747 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 703255 4000) qz448) qz123 464195416430672924221 225179981368524800 109883668154379 26450000000000000000 883879481738659 2251799813685248 200000000529 4232000000000000000 Ns360p738 464107028482499058321 225179981368524800 444534672630741 105800000000000000000 (Ns360p744 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz124 1 4 0 1 883879481738659 562949953421312 200000000529 1058000000000000000 883879481738659 2251799813685248 200000000529 4232000000000000000 qz363 Ns360p746 rfl) 

noncomputable def Ns360p748 := @Ns360p734 Ns360p728 Ns360p729 4091455468070124511 433356800000000000000000 (@Ns360p736 4091455468070124511 433356800000000000000000 (Ns360p737 (Ns360p747 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 703255 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz652 (Real.log Real.pi) 703255 2000 0 1 38410761 33554432 1 67108864 5402511945411 13421772800 140651 26843545600 (Enclosure.Real.IsNear.const Bool.false 703255 2000) RS361to372.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns360p730 Ns360p731) 

noncomputable def Ns360p749 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns360p728 Ns360p729 4091455468070124511 433356800000000000000000 10963096893 8388608 159 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz364 qz120 (Enclosure.sfrac Bool.true Ns360p730 Ns360p731)) Bool.false Ns360p728 Ns360p729 4091455468070124511 433356800000000000000000 Ns360p732 (Ns360p748 rfl rfl)) 

noncomputable def Ns360p750 := BSN.cos_dyadic_bound_f 30786157 68719476736 1 0 33554432 10590333 0 1 1 0 1 1 33554428 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 30786157) qz376 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 30786157) qz377 0 0 rfl) rfl rfl 

noncomputable def Ns360p751 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz116) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10963096893) qz413) Bool.false 10963096893 8388608 159 16777216 Bool.false 33554428 33554432 1 5290000 (Ns360p749 rfl) (Enclosure.sfrac_false_div 10963096893 8388608) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10963096893) qz413) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 541595809370620297216) qz414) 226375608064910080 72057594037927936 Bool.false 33554428 33554432 208 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q0 10963096893 8388608 226375608064910080 72057594037927936 208 541595809370620297216 Ns360p459 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554428 33554432 541595809370620297216 Ns360p459 30786157 68719476736 10590333 10580000 (Ns360p750 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p752 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns360p728 Ns360p729 4091455468070124511 433356800000000000000000 350819100579 268435456 2535 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz364 qz120 (Enclosure.sfrac Bool.true Ns360p730 Ns360p731)) Bool.false Ns360p728 Ns360p729 4091455468070124511 433356800000000000000000 Ns360p732 (Ns360p748 rfl rfl)) 

noncomputable def Ns360p753 := Ns360p727 51949 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 521 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 234030032 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 340 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 261507633 268435456) qz119 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) Bool.false 8388607 8388608 53617951 5546967040000 268435424 268435456 2595 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 8388607 8388608 53617951 5546967040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz116) qz116) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 33554428 33554432 857887216 88751472640000 8388607 8388608 53617951 5546967040000 (Ns360p751 rfl rfl) rfl)) rfl) (Ns360p752 rfl) RS361to372.d7 

noncomputable def Ns360p754 := nat_lit 102551825464371021208780647255775829997550284851982344784500754158932225 

noncomputable def Ns360p755 := nat_lit 42622911044862109983051911417117271514094199382689446283128087466241 

noncomputable def Ns360p756 := nat_lit 268519105788803850225881515908547079173037450670477024855900720179400961 

noncomputable def Ns360p757 := BSN.sin_dyadic_bound_f 284253217 268435456 3 2 268435456 134217728 Ns360p754 Ns360p144 Ns360p755 Ns360p756 Ns360p147 Ns360p755 234030032 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 284253217) qz369 0 2 Ns360p754 Ns360p144 Ns360p755 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 284253217) qz370 0 2 Ns360p756 Ns360p147 Ns360p755 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p758 := nat_lit 13953630667865020140130556645376 

noncomputable def Ns360p759 := BSN.cos_dyadic_bound_f 61118376 268435456 2 1 268435456 134217728 Ns360p758 Ns360p155 Ns360p758 Ns360p758 Ns360p156 Ns360p758 261507633 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 61118376) qz367 0 1 Ns360p758 Ns360p155 Ns360p758 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 61118376) qz368 0 1 Ns360p758 Ns360p156 Ns360p758 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p760 := nat_lit 7275816197390101771051172656313896317803735960558699187332637884473600 

noncomputable def Ns360p761 := nat_lit 214711449372029984501788807426121946685614502158128183519121039616 

noncomputable def Ns360p762 := nat_lit 19055361460341759447063877870371990920619912711316908521193115882414336 

noncomputable def Ns360p763 := BSN.sin_dyadic_bound_f 146717494 268435456 3 2 268435456 134217728 Ns360p760 Ns360p144 Ns360p761 Ns360p762 Ns360p147 Ns360p761 139520925 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 146717494) qz369 0 2 Ns360p760 Ns360p144 Ns360p761 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 146717494) qz370 0 2 Ns360p762 Ns360p147 Ns360p761 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p764 := nat_lit 19504801024216618423294498897846951794436274670606982216187082245136640 

noncomputable def Ns360p765 := nat_lit 1542878530836971727145595021795822617993654175215554718704671908096 

noncomputable def Ns360p766 := nat_lit 51081504688660264582974975673849585272618253459115556810945407839887616 

noncomputable def Ns360p767 := BSN.sin_dyadic_bound_f 187733366 268435456 3 2 268435456 134217728 Ns360p764 Ns360p144 Ns360p765 Ns360p766 Ns360p147 Ns360p765 172799698 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 187733366) qz369 0 2 Ns360p764 Ns360p144 Ns360p765 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 187733366) qz370 0 2 Ns360p766 Ns360p147 Ns360p765 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p768 := Ns360p725 88351 BSN.abs_quadSignPos (BSN.cos_quad_nat3 211 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 139520925 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 111 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 172799698 268435456) qz119 rfl rfl (Ns360p753 RS361to372.d9 RS361to372.d11 RS361to372.d13 RS361to372.d17 (Ns360p757 rfl rfl) (Ns360p759 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns360p752 rfl) RS361to372.d19 RS361to372.d21 RS361to372.d23 RS361to372.d25 RS361to372.d17 (Ns360p763 rfl rfl) (Ns360p767 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns360p769 := nat_lit 19893117180322501064921038494086193391399933106588438491117138888763967201047130378952482799493818728687210496 

noncomputable def Ns360p770 := nat_lit 2867317114643369262234081333239439882228430798487520368255764045295041033652697176483744121348322103296 

noncomputable def Ns360p771 := nat_lit 99409990809779870585547219953176152103913540581733639702022748993311712941821067850840231894846902331887456256 

noncomputable def Ns360p772 := BSN.sin_dyadic_bound_f 345241486 268435456 4 3 268435456 134217728 Ns360p769 Ns360p258 Ns360p770 Ns360p771 Ns360p261 Ns360p770 257631987 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 345241486) qz369 0 3 Ns360p769 Ns360p258 Ns360p770 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 345241486) qz370 0 3 Ns360p771 Ns360p261 Ns360p770 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p773 := nat_lit 46092954986646975339603839467776 

noncomputable def Ns360p774 := BSN.sin_dyadic_bound_f 82396476 268435456 2 1 268435456 134217728 Ns360p773 Ns360p135 Ns360p773 Ns360p773 Ns360p136 Ns360p773 81108675 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 82396476) qz369 0 1 Ns360p773 Ns360p135 Ns360p773 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 82396476) qz370 0 1 Ns360p773 Ns360p136 Ns360p773 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p775 := Ns360p723 119115 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 29 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 257631987 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 39 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 81108675 268435456) qz119 rfl rfl (Ns360p768 rfl rfl) (Ns360p752 rfl) RS361to372.d27 RS361to372.d29 RS361to372.d31 RS361to372.d33 RS361to372.d17 (Ns360p772 rfl rfl) (Ns360p774 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p776 := nat_lit 15628564303353535636647243805260667528997646369919355522179391028073831938632097957698977044381007250906949121 

noncomputable def Ns360p777 := nat_lit 24260752984821642242345763195457105533445644587457037310560865797132502709586483349101251651560275453441 

noncomputable def Ns360p778 := nat_lit 94604091106964905125894139330153769305440394597258137885337999265765335366538278318784605084611533560771782145 

noncomputable def Ns360p779 := BSN.cos_dyadic_bound_f 412485503 268435456 4 3 268435456 134217728 Ns360p776 Ns360p129 Ns360p777 Ns360p778 Ns360p132 Ns360p777 9170140 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 412485503) qz367 0 3 Ns360p776 Ns360p129 Ns360p777 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 412485503) qz368 0 3 Ns360p778 Ns360p132 Ns360p777 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p780 := nat_lit 126486968215929402250332579563479518745595439056219762617700676322164225 

noncomputable def Ns360p781 := nat_lit 64828156682366426213909062737478685346451024985057955798549123530241 

noncomputable def Ns360p782 := nat_lit 331170433073757936441762807993252345509808086344885474927446977500904961 

noncomputable def Ns360p783 := BSN.sin_dyadic_bound_f 299550783 268435456 3 2 268435456 134217728 Ns360p780 Ns360p144 Ns360p781 Ns360p782 Ns360p147 Ns360p781 241138944 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 299550783) qz369 0 2 Ns360p780 Ns360p144 Ns360p781 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 299550783) qz370 0 2 Ns360p782 Ns360p147 Ns360p781 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p784 := Ns360p721 145995 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 98 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 9170140 268435456) BSN.abs_quadSignPos qz631 (BSN.sfrac_eq_quadSignPos_mul Bool.false 241138944 268435456) qz119 rfl rfl (Ns360p775 rfl) (Ns360p752 rfl) RS361to372.d35 RS361to372.d37 RS361to372.d39 RS361to372.d41 RS361to372.d17 (Ns360p779 rfl rfl) (Ns360p783 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p785 := nat_lit 10266739269433273820486361738493611569620018021106933987898189859139993279796286781272964962996766479735493521 

noncomputable def Ns360p786 := nat_lit 6901157042309378474948396477941039027976537701153518675482588506365842146432960180879481694827379069841 

noncomputable def Ns360p787 := nat_lit 62194419191609900239495212891205809035840740938595789154357880529335837226890644223530670578097679383516844945 

noncomputable def Ns360p788 := BSN.cos_dyadic_bound_f 371458379 268435456 4 3 268435456 134217728 Ns360p785 Ns360p129 Ns360p786 Ns360p787 Ns360p132 Ns360p786 49906973 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 371458379) qz367 0 3 Ns360p785 Ns360p129 Ns360p786 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 371458379) qz368 0 3 Ns360p787 Ns360p132 Ns360p786 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p789 := Ns360p719 Bool.false 403587440 145995 Bool.true 371458379 14148475504056880 1 Bool.false 49906973 Bool.true Bool.false 387805469 158371 BSN.abs_quadSignNeg qz632 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 49906973 268435456) qz119 rfl (Ns360p784 rfl) (Ns360p752 rfl) RS361to372.d43 RS361to372.d45 RS361to372.d17 (Ns360p788 rfl rfl) rfl 

noncomputable def Ns360p790 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 10) 387805469 268435456 158371 268435456 387805469 268435456 158371 268435456 208201475820617728 387805469 134217728 158371 134217728 (Ns360p789 rfl rfl rfl rfl) 

noncomputable def Ns360p791 := @Enclosure.Real.IsNear.mulLit_ff qz649 (Zeta.RiemannSiegel.correction qz118) 10316127 33554432 1 33554432 27713373809823 70368744177664 439246307131697 23265666043740160000 285894683820607915521 2361183241434822606848 

noncomputable abbrev qz653 := (@HPow.hPow Real Real Real qz7 qz117 qz9)

noncomputable def Ns360p792 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz653 1 1 0 1 10316127 33554432 1 33554432 10316127 33554432 1 33554432 

noncomputable def Ns360p793 := @Enclosure.Real.IsNear.sqrt_image qz117 751125989803 6710886400 140651 6710886400 177495074 177495108 16777216 (@Enclosure.Real.IsNear.of_eq qz117 (@HMul.hMul Real Real Real qz5 qz116 qz3) Bool.false 751125989803 6710886400 140651 6710886400 (BSN.t_div_two_pi_mk qz116 703255 1000 qz119) (@Enclosure.Real.IsNear.mulLit_ff qz116 qz3 703255 1000 0 1 5340353 33554432 1 33554432 751125989803 6710886400 140651 6710886400 (Enclosure.Real.IsNear.const Bool.false 703255 1000) RS361to372.d48 rfl)) 

noncomputable abbrev qz765 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 703255 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz654 := qz765

noncomputable abbrev qz451 := qz654

noncomputable abbrev qz125 := qz451

noncomputable def Ns360p794 := @Enclosure.Real.IsNear.sqrt_image qz125 177495091 16777216 17 16777216 54569892 54569898 16777216 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 354990182 33554432 34 33554432 177495091 16777216 17 16777216 (Ns360p793 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns360p795 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz125) 54569895 16777216 3 16777216 5158063 5158064 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz125) Bool.false 109139790 33554432 6 33554432 54569895 16777216 3 16777216 (Ns360p794 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns360p796 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 10316127 33554432 1 33554432 10316127 33554432 1 33554432 (Ns360p795 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz452 := (@HMul.hMul Real Real Real qz583 qz581 qz648)

noncomputable abbrev qz126 := (Real.cos qz452)

noncomputable abbrev qz655 := (@HMul.hMul Real Real Real qz737 qz764 qz764)

noncomputable abbrev qz453 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz655 qz648) qz600)

noncomputable abbrev qz127 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz453))

noncomputable def Ns360p797 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz118) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz126) qz127) Bool.false 27713373809823 

noncomputable def Ns360p798 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz126) qz127 38229087 33554432 289 

noncomputable abbrev qz128 := (@Neg.neg Real Real.instNeg (Real.cos qz452))

noncomputable def Ns360p799 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz126) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz128)) Bool.true 38229087 33554432 289 33554432 (BSN.inv_eq_neg_inv_neg qz126) 

noncomputable def Ns360p800 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz128) Bool.false 38229087 33554432 289 33554432 38229087 33554432 

noncomputable def Ns360p801 := @Enclosure.Real.IsNear.recentre' qz126 Bool.true 29451394 33554432 1170904432 177502945280000 14725697 16777216 73181527 11093934080000 

noncomputable abbrev qz129 := qz452

noncomputable def Ns360p802 := @Enclosure.Real.IsNear.cos_image qz129 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 61090977) qz365) Bool.false 61090977 16777216 215 33554432 Bool.true 29451394 33554432 1 

noncomputable def Ns360p803 := nat_lit 458763282037268114070401591 

noncomputable def Ns360p804 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz118 884279719003555 140737488355328 1 500000000000000 9722931 16777216 17 16777216 8597790692570954019705 2361183241434822606848 Ns360p803 

noncomputable def Ns360p805 := @Enclosure.Real.IsNear.subLit_ff_p qz125 qz1 177495091 16777216 17 16777216 10 1 0 1 9722931 9722931 16777216 17 

noncomputable def Ns360p806 := @Ns360p805 16777216 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 354990182 33554432 34 33554432 177495091 16777216 17 16777216 (Ns360p793 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns360p807 := @Enclosure.Real.IsNear.recentre' qz129 Bool.false 8597790692570954019705 2361183241434822606848 Ns360p803 Ns360p180 61090977 16777216 215 33554432 (@Ns360p804 Ns360p180 RS361to372.d47 (Ns360p806 rfl rfl) rfl) 

noncomputable def Ns360p808 := nat_lit 52101219502024593947397536832337291151773160059983434738634876863395306550034407514995521 

noncomputable def Ns360p809 := nat_lit 1933776257553232710656614261526183169417120127468821679007015004228390164650702175041 

noncomputable def Ns360p810 := nat_lit 156299790953558675376771297268488821088980645939695366572546616560177462869773921140636481 

noncomputable def Ns360p811 := BSN.cos_dyadic_bound_f 34340038519 68719476736 3 2 33554432 10590333 Ns360p808 Ns360p693 Ns360p809 Ns360p810 Ns360p696 Ns360p809 29451394 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 34340038519) qz376 0 2 Ns360p808 Ns360p693 Ns360p809 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 34340038519) qz377 0 2 Ns360p810 Ns360p696 Ns360p809 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p812 := @Ns360p802 5290000 (Ns360p807 rfl) (Enclosure.sfrac_false_div 61090977 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 61090977) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1208232692820108466192384) qz366) 226375608064910080 72057594037927936 Bool.false 29451394 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q2 61090977 16777216 226375608064910080 72057594037927936 0 1208232692820108466192384 Ns360p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 29451394 33554432 1208232692820108466192384 Ns360p112 34340038519 68719476736 10590333 10580000 (Ns360p811 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p813 := @Enclosure.Real.IsNear.inv_image qz128 14725697 16777216 73181527 11093934080000 19114399 19114688 16777216 (@Enclosure.Real.IsNear.neg qz126 Bool.true 14725697 16777216 73181527 11093934080000 (Ns360p801 (Ns360p812 rfl rfl) rfl)) 

noncomputable def Ns360p814 := Ns360p799 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz128) Bool.false 38229087 33554432 289 33554432 (@Ns360p800 289 33554432 (Ns360p813 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p815 := @Enclosure.Real.IsNear.recentre' qz127 Bool.true 5799432 16777216 

noncomputable abbrev qz130 := (@HMul.hMul Real Real Real qz349 qz346 qz453)

noncomputable def Ns360p816 := @Enclosure.Real.IsNear.cos_image qz130 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 64550415)) qz378) Bool.true 64550415 33554432 

noncomputable def Ns360p817 := nat_lit 76207679247757334597386584805 

noncomputable def Ns360p818 := nat_lit 16617825945462712365241132511633297 

noncomputable def Ns360p819 := @Enclosure.Real.IsNear.recentre' qz130 Bool.true Ns360p817 Ns360p317 Ns360p818 

noncomputable abbrev qz131 := qz453

noncomputable def Ns360p820 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz131 884279719003555 140737488355328 1 500000000000000 86180512353751 

noncomputable abbrev qz454 := (@HSub.hSub Real Real Real qz587 qz655 qz648)

noncomputable abbrev qz132 := qz454

noncomputable def Ns360p821 := @Enclosure.Real.IsNear.subLit_tf qz132 qz31 68588326309335 281474976710656 615792615 281474976710656 1 16 

noncomputable abbrev qz455 := qz655

noncomputable abbrev qz133 := qz455

noncomputable def Ns360p822 := @Enclosure.Real.IsNear.subLit_ff_n qz133 qz118 94535387230761 281474976710656 330579943 281474976710656 9722931 16777216 17 16777216 

noncomputable def Ns360p823 := @Enclosure.Real.IsNear.mulLit_ff qz118 qz118 9722931 16777216 17 16777216 9722931 16777216 17 16777216 94535387230761 281474976710656 

noncomputable def Ns360p824 := nat_lit 561372665393947989393767394879978662002747459579438563600723960709908223203247734977980442241890625 

noncomputable def Ns360p825 := nat_lit 5233454644448584810827082401812134656292161463963172039400114882410779197434328137246337890625 

noncomputable def Ns360p826 := nat_lit 3387274552466242868518107297309165840058623791732681439390845737655599994447752336626404835355490625 

noncomputable def Ns360p827 := BSN.cos_dyadic_bound_t 64550415 33554432 4 3 16777216 5290000 Ns360p824 Ns360p204 Ns360p825 Ns360p826 Ns360p207 Ns360p825 5799432 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 64550415) qz601 0 3 Ns360p824 Ns360p204 Ns360p825 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 64550415) (BSN.cosOddQ 33554432) 0 3 Ns360p826 Ns360p207 Ns360p825 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p828 := @Ns360p815 1238767216 88751472640000 724929 2097152 77422951 5546967040000 (@Ns360p816 231 16777216 Bool.true 5799432 16777216 1 5290000 (@Ns360p819 Ns360p198 64550415 33554432 231 16777216 (@Ns360p820 281474976710656 615792615 281474976710656 Ns360p817 Ns360p317 Ns360p818 Ns360p198 RS361to372.d47 (@Ns360p821 0 1 1378888197660016 86180512353751 281474976710656 615792615 281474976710656 (@Ns360p822 1150721165570196111360 68588326309335 281474976710656 615792615 281474976710656 (@Ns360p823 330579943 281474976710656 (Ns360p806 rfl rfl) (Ns360p806 rfl rfl) rfl) (Ns360p806 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 64550415 33554432) (BSN.cos_neg_of_bound 64550415 33554432 Bool.true 5799432 16777216 1 5290000 (Ns360p827 rfl rfl)) rfl rfl) 

noncomputable def Ns360p829 := @Ns360p791 4540483862113771838591 Ns360p363 (Ns360p792 qz33 (@Enclosure.Real.IsNear.of_eq qz653 (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 10316127 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz117 (BSN.t_div_two_pi_nonneg qz116 703255 1000 qz119)) Ns360p796) rfl) (@Ns360p797 70368744177664 439246307131697 23265666043740160000 (BSN.correction_mk qz118 (BSN.cos_two_pi_p_ne_zero_mk qz116 703255 1000 10 qz119 rfl rfl (@BSN.floor_sqrt_eq_dec qz116 703255 1000 10 qz119 rfl rfl rfl))) (@Ns360p798 33554432 724929 2097152 77422951 5546967040000 27713373809823 70368744177664 439246307131697 23265666043740160000 Ns360p814 (Ns360p828 rfl) rfl)) 

noncomputable def Ns360p830 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (hardyZApproximantRS₀ qz116) Bool.false 6536451275869393795583 2361183241434822606848 925692183115406991678591 Ns360p363 (@Eq.refl Real (hardyZApproximantRS₀ qz116)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 10) (@HMul.hMul Real Real Real qz5 qz649 (Zeta.RiemannSiegel.correction qz118))) Bool.false 6536451275869393795583 2361183241434822606848 925692183115406991678591 Ns360p363 (BSN.hardyZApproximantRS₀_eq qz116 10 (@BSN.floor_sqrt_eq_dec qz116 703255 1000 10 qz119 rfl rfl rfl)) (@Ns360p718 6536451275869393795583 2361183241434822606848 925692183115406991678591 Ns360p363 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 10)) Bool.false 387805469 134217728 158371 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz116) qz116 10) (Ns360p790 (Ns360p789 rfl rfl rfl rfl) rfl rfl)) (Ns360p829 rfl) rfl rfl)) 

theorem RS361to372.d56 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz116) Bool.false 6536451275869393795583 2361183241434822606848 925692183115406991678591 Ns360p363 := Ns360p830 

noncomputable def Ns360p831 := nat_lit 97583276149923528048640000 

noncomputable def Ns360p832 := nat_lit 818811507642514894630527434752 

noncomputable abbrev qz766 := (Enclosure.sfrac Bool.false 704586 1000)

noncomputable abbrev qz656 := qz766

noncomputable abbrev qz456 := qz656

noncomputable abbrev qz134 := qz456

noncomputable abbrev qz767 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 704586 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz657 := qz767

noncomputable abbrev qz457 := qz657

noncomputable abbrev qz135 := qz457

noncomputable abbrev qz768 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 704586 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz658 := qz768

noncomputable abbrev qz458 := qz658

noncomputable abbrev qz136 := qz458

noncomputable abbrev qz659 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz135 qz9))

noncomputable def Ns360p833 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 10) (@HMul.hMul Real Real Real qz5 qz659 (Zeta.RiemannSiegel.correction qz136)) 157022377 134217728 79333 67108864 575887392738412484745 4722366482869645213696 594254247394259053983 Ns360p831 Ns360p832 

noncomputable def Ns360p834 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos BSN.quadSignNeg 9 10 704586 1000 198 268435456 134217728 4503599627370496 Bool.false 351662082801 2540 618095470 52 84886744 8 

noncomputable def Ns360p835 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 704586 1000 98 151 268435456 134217728 4503599627370496 Bool.false 351662082801 2540 

noncomputable def Ns360p836 := Ns360p835 558195838 52 94906264 8 589812974 52 89478488 8 Bool.true 167528986 119335 Bool.true 312461941 Bool.true 241609629 14148475504056880 1 Bool.false 106208804 Bool.true Bool.false 210283729 Bool.false Bool.true 134984890 

noncomputable def Ns360p837 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 704586 1000 30 38 268435456 134217728 4503599627370496 Bool.false 351662082801 2540 

noncomputable def Ns360p838 := Ns360p837 480971758 52 109588312 8 522351262 52 101459064 8 Bool.true 45414088 88513 Bool.false 126392870 Bool.true 356321212 14148475504056880 1 Bool.false 239225102 Bool.true Bool.false 64693018 Bool.true Bool.true 167528986 

noncomputable def Ns360p839 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 704586 1000 212 112 268435456 134217728 4503599627370496 Bool.false 351662082801 2540 

noncomputable def Ns360p840 := Ns360p839 372130544 51 134217720 8 432030192 51 120047984 16 Bool.true 293819477 52042 Bool.false 72736533 Bool.false 34025974 14148475504056880 1 Bool.false 258641086 Bool.false Bool.false 266281832 Bool.false Bool.true 45414088 

noncomputable def Ns360p841 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 704586 1000 523 341 268435456 134217728 4503599627370496 Bool.false 351662082801 2540 

noncomputable def Ns360p842 := Ns360p841 186065264 51 189812528 16 294906480 51 154981288 8 Bool.true 268435368 2595 Bool.false 36267717 Bool.false 89922644 14148475504056880 1 Bool.false 36157478 Bool.false Bool.false 88250247 Bool.true Bool.true 293819477 

noncomputable def Ns360p843 := nat_lit 1409873645769646440898261535420327767829537867125197433 

noncomputable def Ns360p844 := nat_lit 1076203814723135161501660046956257549532987916288000 

noncomputable def Ns360p845 := nat_lit 83351196659637584243825966484480000 

noncomputable def Ns360p846 := nat_lit 352368600306661990671816617490778951680 

noncomputable abbrev qz660 := (@Eq.refl Real qz766)

noncomputable abbrev qz459 := qz660

noncomputable abbrev qz137 := qz459

noncomputable def Ns360p847 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz134 704586 1000 1985766725584 16000000 1409172 4000 2000 Ns360p845 Ns360p846 qz137 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns360p848 := nat_lit 259867910388261231986367566208674814166340419668516390850560 

noncomputable abbrev qz661 := (@HSub.hSub Real Real Real qz741 qz742 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz743 (@Nat.cast Real Real.instNatCast 1409172))))

noncomputable abbrev qz460 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 704586 4000) (Real.log (Enclosure.sfrac Bool.false 1985766725584 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz661))

noncomputable abbrev qz662 := (Enclosure.sfrac Bool.false 704586 2000)

noncomputable abbrev qz138 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz460 qz662) (@HMul.hMul Real Real Real qz349 qz662 (Real.log Real.pi)))

noncomputable def Ns360p849 := @Enclosure.Real.IsNear.addLit_ft_p qz138 (Enclosure.sfrac Bool.true Ns360p845 Ns360p846) 737488973434788662917 562949953421312000 445560903220148151 47104000000000000000000 Ns360p845 Ns360p846 0 1 Ns360p848 

noncomputable def Ns360p850 := nat_lit 4949204721973484524843879628800 

noncomputable abbrev qz139 := (@HSub.hSub Real Real Real qz353 qz460 qz662)

noncomputable def Ns360p851 := @Enclosure.Real.IsNear.subLit_ff_p qz139 (@HMul.hMul Real Real Real qz5 qz662 (Real.log Real.pi)) 192903122664216255617 112589990684262400 96818814824787 23000000000000000000 13531842224973 33554432000 352293 67108864000 Ns360p850 737488973434788662917 562949953421312000 

noncomputable def Ns360p852 := nat_lit 1929031226642162556170000 

noncomputable abbrev qz140 := qz460

noncomputable def Ns360p853 := @Enclosure.Real.IsNear.subLit_ff_p qz140 qz662 1162838941261735546501 562949953421312000 96818814824787 23000000000000000000 704586 2000 0 1 Ns360p852 192903122664216255617 112589990684262400 96818814824787 23000000000000000000 

noncomputable def Ns360p854 := nat_lit 2618480511279127146488126364081717248 

noncomputable def Ns360p855 := nat_lit 56717610425753559931813888 

noncomputable def Ns360p856 := nat_lit 11370091433717789908519642537133334439815580611802484698521176459292668726563220860214590095014466367944065392997988343062871783899828765402077452578161628131347490344837925201510400 

noncomputable def Ns360p857 := nat_lit 383768591435196496898118868240265264459380138108150659620907188226908523918404785956527895470023787677818756001805898109273720512418615518914257373168758773612765516536142354186240 

noncomputable def Ns360p858 := nat_lit 54495368855378080449307231691656804801631271000672824472406441525451743488645363928250013277361315983932875340939078109652196097904175262589036088565314117606973275226767360 

noncomputable def Ns360p859 := BSN.log_dyadic_bound 937190725584 3034342725584 8 7 Ns360p856 134217728 42320000 Ns360p857 Ns360p858 85707689 3971533451168 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 937190725584) (BSN.artanhQ 3034342725584) 0 7 Ns360p857 Ns360p856 Ns360p858 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz461 := (Real.log (Enclosure.sfrac Bool.false 1985766725584 16000000))

noncomputable def Ns360p860 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 704586 4000) qz461 704586 4000 0 1 3301399435484407 281474976710656 781250529 33062500000000000 1163059911325108195251 562949953421312000 275229092612997 66125000000000000000 (Enclosure.Real.IsNear.const Bool.false 704586 4000) (BSN.isNear_log_sfrac 1985766725584 16000000 3301399435484407 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1985766725584) qz356)) Bool.false Ns360p855 Ns360p100 1000000677120000 42320000000000000000000 3301399435484407 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 1985766725584 16000000 16 3971533451168 2097152000000 85707689 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns360p859 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p861 := BSN.arctan_dyadic_bound_f 1000 1409172 1 0 16777216 5290000 0 1 1 0 1 1 11905 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1409172) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1409172) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns360p862 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1409172))) 884279719003555 562949953421312 1 2000000000000000 11905 16777216 1 5290000 14829049930946466283520 883880253490595 562949953421312 200000000529 1058000000000000000 qz17 (Ns360p861 rfl) rfl rfl 

noncomputable abbrev qz462 := (@HMul.hMul Real Real Real qz583 qz588 qz661)

noncomputable abbrev qz141 := qz462

noncomputable abbrev qz463 := qz661

noncomputable abbrev qz142 := qz463

noncomputable def Ns360p863 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 704586 4000) qz461) qz141 1163059911325108195251 562949953421312000 275229092612997 66125000000000000000 883880253490595 2251799813685248 200000000529 4232000000000000000 Ns360p854 1162838941261735546501 562949953421312000 96818814824787 23000000000000000000 (Ns360p860 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz142 1 4 0 1 883880253490595 562949953421312 200000000529 1058000000000000000 883880253490595 2251799813685248 200000000529 4232000000000000000 qz363 Ns360p862 rfl) 

noncomputable def Ns360p864 := @Ns360p849 Ns360p843 Ns360p844 445560903220148151 47104000000000000000000 (@Ns360p851 445560903220148151 47104000000000000000000 (Ns360p853 (Ns360p863 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 704586 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz662 (Real.log Real.pi) 704586 2000 0 1 38410761 33554432 1 67108864 13531842224973 33554432000 352293 67108864000 (Enclosure.Real.IsNear.const Bool.false 704586 2000) RS361to372.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns360p845 Ns360p846) 

noncomputable def Ns360p865 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz134) Bool.false Ns360p843 Ns360p844 445560903220148151 47104000000000000000000 21978880175 16777216 159 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz134) (@HAdd.hAdd Real Real Real qz364 qz138 (Enclosure.sfrac Bool.true Ns360p845 Ns360p846)) Bool.false Ns360p843 Ns360p844 445560903220148151 47104000000000000000000 Ns360p847 (Ns360p864 rfl rfl)) 

noncomputable def Ns360p866 := nat_lit 3796039577755106787983360 

noncomputable def Ns360p867 := nat_lit 3503753505038235005377894053415744064098213556517420729325289355836669146485968179806135495100869470062776776298297917286184610594360790625 

noncomputable def Ns360p868 := nat_lit 2487546011771856888519150706527571696526878882995768215843583775813267754341772273543611379357174995149772026531765927734941650390625 

noncomputable def Ns360p869 := nat_lit 17497042051376138136379906718759982858076572012475833957081145352041191335339236419862186550375300384207769716674490892729293561141202390625 

noncomputable def Ns360p870 := BSN.sin_dyadic_bound_f 107889933865 68719476736 4 3 33554432 10590333 Ns360p867 Ns360p114 Ns360p868 Ns360p869 Ns360p117 Ns360p868 33554421 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107889933865) qz594 0 3 Ns360p867 Ns360p114 Ns360p868 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107889933865) qz595 0 3 Ns360p869 Ns360p117 Ns360p868 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p871 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz134) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21978880175) qz365) Bool.false 21978880175 16777216 159 16777216 Bool.true 33554421 33554432 1 5290000 (Ns360p865 rfl) (Enclosure.sfrac_false_div 21978880175 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21978880175) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns360p866) qz366) 226375608064910080 72057594037927936 Bool.false 33554421 33554432 208 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q1 21978880175 16777216 226375608064910080 72057594037927936 208 Ns360p866 Ns360p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554421 33554432 Ns360p866 Ns360p112 107889933865 68719476736 10590333 10580000 (Ns360p870 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p872 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz134) Bool.false Ns360p843 Ns360p844 445560903220148151 47104000000000000000000 351662082801 268435456 2540 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz134) (@HAdd.hAdd Real Real Real qz364 qz138 (Enclosure.sfrac Bool.true Ns360p845 Ns360p846)) Bool.false Ns360p843 Ns360p844 445560903220148151 47104000000000000000000 Ns360p847 (Ns360p864 rfl rfl)) 

noncomputable def Ns360p873 := Ns360p842 52042 BSN.abs_quadSignPos (BSN.cos_quad_nat3 523 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 36157478 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 341 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 88250247 268435456) qz137 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 1) Bool.true 33554421 33554432 53617951 5546967040000 268435368 268435456 2595 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz134)) Bool.true 33554421 33554432 53617951 5546967040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz134) qz134) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz134)) Bool.true 33554421 33554432 857887216 88751472640000 33554421 33554432 53617951 5546967040000 (Ns360p871 rfl rfl) rfl)) rfl) (Ns360p872 rfl) RS361to372.d7 

noncomputable def Ns360p874 := nat_lit 1730138510125978028036421783921 

noncomputable def Ns360p875 := BSN.sin_dyadic_bound_f 36267717 268435456 2 1 268435456 134217728 Ns360p874 Ns360p135 Ns360p874 Ns360p874 Ns360p136 Ns360p874 36157478 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 36267717) qz369 0 1 Ns360p874 Ns360p135 Ns360p874 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 36267717) qz370 0 1 Ns360p874 Ns360p136 Ns360p874 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p876 := nat_lit 65384720557399559738165114941696 

noncomputable def Ns360p877 := BSN.sin_dyadic_bound_f 89922644 268435456 2 1 268435456 134217728 Ns360p876 Ns360p135 Ns360p876 Ns360p876 Ns360p136 Ns360p876 88250247 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 89922644) qz369 0 1 Ns360p876 Ns360p135 Ns360p876 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 89922644) qz370 0 1 Ns360p876 Ns360p136 Ns360p876 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p878 := nat_lit 27990482567549625111155049087921 

noncomputable def Ns360p879 := BSN.cos_dyadic_bound_f 72736533 268435456 2 1 268435456 134217728 Ns360p878 Ns360p155 Ns360p878 Ns360p878 Ns360p156 Ns360p878 258641086 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 72736533) qz367 0 1 Ns360p878 Ns360p155 Ns360p878 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 72736533) qz368 0 1 Ns360p878 Ns360p156 Ns360p878 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p880 := nat_lit 1340424210130844047453692552976 

noncomputable def Ns360p881 := BSN.cos_dyadic_bound_f 34025974 268435456 2 1 268435456 134217728 Ns360p880 Ns360p155 Ns360p880 Ns360p880 Ns360p156 Ns360p880 266281832 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 34025974) qz367 0 1 Ns360p880 Ns360p155 Ns360p880 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 34025974) qz368 0 1 Ns360p880 Ns360p156 Ns360p880 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p882 := Ns360p840 88513 BSN.abs_quadSignPos (BSN.cos_quad_nat0 212 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 258641086 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 112 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 266281832 268435456) qz137 rfl rfl (Ns360p873 RS361to372.d9 RS361to372.d11 RS361to372.d13 RS361to372.d17 (Ns360p875 rfl rfl) (Ns360p877 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns360p872 rfl) RS361to372.d19 RS361to372.d21 RS361to372.d23 RS361to372.d25 RS361to372.d17 (Ns360p879 rfl rfl) (Ns360p881 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns360p883 := nat_lit 2226239087721438825332998214912909217670396614855599008041523760800000 

noncomputable def Ns360p884 := nat_lit 65129928857383460541364354083429688474532366316393986592100000000 

noncomputable def Ns360p885 := nat_lit 6678587003306601709077911916030560793634240779834164236151387082400000 

noncomputable def Ns360p886 := BSN.cos_dyadic_bound_f 126392870 268435456 3 2 268435456 134217728 Ns360p883 Ns360p123 Ns360p884 Ns360p885 Ns360p126 Ns360p884 239225102 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 126392870) qz367 0 2 Ns360p883 Ns360p123 Ns360p884 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 126392870) qz368 0 2 Ns360p885 Ns360p126 Ns360p884 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p887 := nat_lit 8689874335634753034066915106572689299433013996399407910462787239586191795385125635318943693965759726995111936 

noncomputable def Ns360p888 := nat_lit 4188901255944281073373189321246353020979828490521217300142039468446468509241678168862048518196697235456 

noncomputable def Ns360p889 := nat_lit 52653720906676776185939581025054998442659076125851097799117101131369232479862873459299956933955550985794355200 

noncomputable def Ns360p890 := BSN.cos_dyadic_bound_f 356321212 268435456 4 3 268435456 134217728 Ns360p887 Ns360p129 Ns360p888 Ns360p889 Ns360p132 Ns360p888 64693018 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 356321212) qz367 0 3 Ns360p887 Ns360p129 Ns360p888 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 356321212) qz368 0 3 Ns360p889 Ns360p132 Ns360p888 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p891 := Ns360p838 119335 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 30 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 239225102 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 38 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 64693018 268435456) qz137 rfl rfl (Ns360p882 rfl rfl) (Ns360p872 rfl) RS361to372.d27 RS361to372.d29 RS361to372.d31 RS361to372.d33 RS361to372.d17 (Ns360p886 rfl rfl) (Ns360p890 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p892 := nat_lit 5134612152592305828439030774519921732578136573013078336626766727719653138911214092682158444640079675023113361 

noncomputable def Ns360p893 := nat_lit 866094967401081182871888242798524560062271782432024193925863004031600219542406828116954919565439220881 

noncomputable def Ns360p894 := nat_lit 31127308075409593751016953210681247894016764433436194567088223514996898637043972143566047907850353616001121425 

noncomputable def Ns360p895 := BSN.cos_dyadic_bound_f 312461941 268435456 4 3 268435456 134217728 Ns360p892 Ns360p129 Ns360p893 Ns360p894 Ns360p132 Ns360p893 106208804 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 312461941) qz367 0 3 Ns360p892 Ns360p129 Ns360p893 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 312461941) qz368 0 3 Ns360p894 Ns360p132 Ns360p893 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p896 := nat_lit 53517091023651396577701156073427505225809956572157990312463609793677985 

noncomputable def Ns360p897 := nat_lit 11612183971953949608791496974835731601266834370999079060876700224161 

noncomputable def Ns360p898 := nat_lit 140145009145037160832707841578160398692624025671432166595115653849746081 

noncomputable def Ns360p899 := BSN.sin_dyadic_bound_f 241609629 268435456 3 2 268435456 134217728 Ns360p896 Ns360p144 Ns360p897 Ns360p898 Ns360p147 Ns360p897 210283729 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 241609629) qz369 0 2 Ns360p896 Ns360p144 Ns360p897 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 241609629) qz370 0 2 Ns360p898 Ns360p147 Ns360p897 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p900 := Ns360p836 146266 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 98 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 106208804 268435456) BSN.abs_quadSignPos qz631 (BSN.sfrac_eq_quadSignPos_mul Bool.false 210283729 268435456) qz137 rfl rfl (Ns360p891 rfl) (Ns360p872 rfl) RS361to372.d35 RS361to372.d37 RS361to372.d39 RS361to372.d41 RS361to372.d17 (Ns360p895 rfl rfl) (Ns360p899 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p901 := nat_lit 8196483889197427405991431870300112453627877698581923478971298759390754109241770149708567389386180828636435601 

noncomputable def Ns360p902 := nat_lit 3516241489223527115146075363842838195960765301464030193367024025494122378753340768468307059832793650321 

noncomputable def Ns360p903 := nat_lit 49667629538503660042169204539360567461968812329837760593363992089241911816439051537648229797310136186457871505 

noncomputable def Ns360p904 := BSN.cos_dyadic_bound_f 351161227 268435456 4 3 268435456 134217728 Ns360p901 Ns360p129 Ns360p902 Ns360p903 Ns360p132 Ns360p902 69688653 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 351161227) qz367 0 3 Ns360p901 Ns360p129 Ns360p902 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 351161227) qz368 0 3 Ns360p903 Ns360p132 Ns360p902 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p905 := Ns360p834 Bool.true 134984890 146266 Bool.true 351161227 14148475504056880 1 Bool.false 69688653 Bool.true Bool.true 157022377 158666 BSN.abs_quadSignNeg qz632 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 69688653 268435456) qz137 rfl (Ns360p900 rfl) (Ns360p872 rfl) RS361to372.d43 RS361to372.d45 RS361to372.d17 (Ns360p904 rfl rfl) rfl 

noncomputable def Ns360p906 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 10) 157022377 268435456 158666 268435456 157022377 268435456 158666 268435456 84300746744397824 157022377 134217728 79333 67108864 (Ns360p905 rfl rfl rfl rfl) 

noncomputable def Ns360p907 := @Enclosure.Real.IsNear.mulLit_ff qz659 (Zeta.RiemannSiegel.correction qz136) 10311251 33554432 1 33554432 55850390290995 140737488355328 3681260984803081 186125328349921280000 575887392738412484745 4722366482869645213696 

noncomputable abbrev qz663 := (@HPow.hPow Real Real Real qz7 qz135 qz9)

noncomputable def Ns360p908 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz663 1 1 0 1 10311251 33554432 1 33554432 10311251 33554432 1 33554432 

noncomputable def Ns360p909 := @Enclosure.Real.IsNear.sqrt_image qz135 1881368979429 16777216000 352293 16777216000 177662961 177662995 16777216 (@Enclosure.Real.IsNear.of_eq qz135 (@HMul.hMul Real Real Real qz5 qz134 qz3) Bool.false 1881368979429 16777216000 352293 16777216000 (BSN.t_div_two_pi_mk qz134 704586 1000 qz137) (@Enclosure.Real.IsNear.mulLit_ff qz134 qz3 704586 1000 0 1 5340353 33554432 1 33554432 1881368979429 16777216000 352293 16777216000 (Enclosure.Real.IsNear.const Bool.false 704586 1000) RS361to372.d48 rfl)) 

noncomputable abbrev qz769 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 704586 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz664 := qz769

noncomputable abbrev qz464 := qz664

noncomputable abbrev qz143 := qz464

noncomputable def Ns360p910 := @Enclosure.Real.IsNear.sqrt_image qz143 88831489 8388608 17 16777216 54595694 54595700 16777216 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 355325956 33554432 34 33554432 88831489 8388608 17 16777216 (Ns360p909 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns360p911 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz143) 54595697 16777216 3 16777216 5155625 5155626 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz143) Bool.false 109191394 33554432 6 33554432 54595697 16777216 3 16777216 (Ns360p910 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns360p912 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 10311251 33554432 1 33554432 10311251 33554432 1 33554432 (Ns360p911 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz465 := (@HMul.hMul Real Real Real qz583 qz581 qz658)

noncomputable abbrev qz144 := (Real.cos qz465)

noncomputable abbrev qz665 := (@HMul.hMul Real Real Real qz737 qz768 qz768)

noncomputable abbrev qz466 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz665 qz658) qz600)

noncomputable abbrev qz145 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz466))

noncomputable def Ns360p913 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz136) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz144) qz145) Bool.false 55850390290995 

noncomputable def Ns360p914 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz144) qz145 9917049 8388608 155 

noncomputable abbrev qz146 := (@Neg.neg Real Real.instNeg (Real.cos qz465))

noncomputable def Ns360p915 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz144) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz146)) Bool.true 9917049 8388608 155 16777216 (BSN.inv_eq_neg_inv_neg qz144) 

noncomputable def Ns360p916 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz146) Bool.false 39668196 33554432 310 33554432 9917049 8388608 

noncomputable def Ns360p917 := @Enclosure.Real.IsNear.recentre' qz144 Bool.true 28382937 33554432 1170904432 177502945280000 28382937 33554432 73181527 11093934080000 

noncomputable abbrev qz147 := qz465

noncomputable def Ns360p918 := @Enclosure.Real.IsNear.cos_image qz147 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 31072921) qz413) Bool.false 31072921 8388608 215 33554432 Bool.true 28382937 33554432 1 

noncomputable def Ns360p919 := nat_lit 91752656407742050483849739 

noncomputable def Ns360p920 := nat_lit 14411518807585587200000000000000 

noncomputable def Ns360p921 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz136 884279719003555 140737488355328 1 500000000000000 4945409 8388608 17 16777216 4373124880877651928995 1180591620717411303424 Ns360p919 

noncomputable def Ns360p922 := @Enclosure.Real.IsNear.subLit_ff_p qz143 qz1 88831489 8388608 17 16777216 10 1 0 1 4945409 4945409 8388608 17 

noncomputable def Ns360p923 := @Ns360p922 16777216 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 355325956 33554432 34 33554432 88831489 8388608 17 16777216 (Ns360p909 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns360p924 := @Enclosure.Real.IsNear.recentre' qz147 Bool.false 4373124880877651928995 1180591620717411303424 Ns360p919 Ns360p920 31072921 8388608 215 33554432 (@Ns360p921 Ns360p920 RS361to372.d47 (Ns360p923 rfl rfl) rfl) 

noncomputable def Ns360p925 := nat_lit 83702099490993609079694594258198168058805437250612007960231760061368931274369448690056001 

noncomputable def Ns360p926 := nat_lit 4990724509832553966443370446399718266745678585124682594557542696181782292705796160321 

noncomputable def Ns360p927 := nat_lit 251096317023961162131150896033701704739882820394665774515506165098714430258522934477847361 

noncomputable def Ns360p928 := BSN.cos_dyadic_bound_f 38660765559 68719476736 3 2 33554432 10590333 Ns360p925 Ns360p693 Ns360p926 Ns360p927 Ns360p696 Ns360p926 28382937 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 38660765559) qz376 0 2 Ns360p925 Ns360p693 Ns360p926 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 38660765559) qz377 0 2 Ns360p927 Ns360p696 Ns360p926 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p929 := @Ns360p918 5290000 (Ns360p924 rfl) (Enclosure.sfrac_false_div 31072921 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 31072921) qz413) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 680127380344873085304832) qz414) 226375608064910080 72057594037927936 Bool.false 28382937 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q2 31072921 8388608 226375608064910080 72057594037927936 0 680127380344873085304832 Ns360p459 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 28382937 33554432 680127380344873085304832 Ns360p459 38660765559 68719476736 10590333 10580000 (Ns360p928 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p930 := @Enclosure.Real.IsNear.inv_image qz146 28382937 33554432 73181527 11093934080000 19833943 19834253 16777216 (@Enclosure.Real.IsNear.neg qz144 Bool.true 28382937 33554432 73181527 11093934080000 (Ns360p917 (Ns360p929 rfl rfl) rfl)) 

noncomputable def Ns360p931 := Ns360p915 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz146) Bool.false 9917049 8388608 155 16777216 (@Ns360p916 155 16777216 (Ns360p930 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p932 := @Enclosure.Real.IsNear.recentre' qz145 Bool.true 5631755 16777216 

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz349 qz346 qz466)

noncomputable def Ns360p933 := @Enclosure.Real.IsNear.cos_image qz148 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 64193721)) qz378) Bool.true 64193721 33554432 

noncomputable def Ns360p934 := nat_lit 18946642549716660799386629725 

noncomputable def Ns360p935 := nat_lit 16771866727693359732641348569515651 

noncomputable def Ns360p936 := @Enclosure.Real.IsNear.recentre' qz148 Bool.true Ns360p934 Ns360p195 Ns360p935 

noncomputable abbrev qz149 := qz466

noncomputable def Ns360p937 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz149 884279719003555 140737488355328 1 500000000000000 21426073834495 

noncomputable abbrev qz467 := (@HSub.hSub Real Real Real qz587 qz665 qz658)

noncomputable abbrev qz150 := qz467

noncomputable def Ns360p938 := @Enclosure.Real.IsNear.subLit_tf qz150 qz31 17028027323391 70368744177664 621500773 281474976710656 1 16 

noncomputable abbrev qz468 := qz665

noncomputable abbrev qz151 := qz468

noncomputable def Ns360p939 := @Enclosure.Real.IsNear.subLit_ff_n qz151 qz136 24457070177281 70368744177664 336288101 281474976710656 4945409 8388608 17 16777216 

noncomputable def Ns360p940 := @Enclosure.Real.IsNear.mulLit_ff qz136 qz136 4945409 8388608 17 16777216 4945409 8388608 17 16777216 24457070177281 70368744177664 

noncomputable def Ns360p941 := nat_lit 548969407042565618898399327721864509982959666138887756199501330040252679074739872094633520739961121 

noncomputable def Ns360p942 := nat_lit 4896780132078950346442658454265634307266847167215533091477269886517643576629780289659465419041 

noncomputable def Ns360p943 := nat_lit 3312825921743320104291770446040570624278861583211634465941310193872647773273629286932645329129752865 

noncomputable def Ns360p944 := BSN.cos_dyadic_bound_t 64193721 33554432 4 3 16777216 5290000 Ns360p941 Ns360p204 Ns360p942 Ns360p943 Ns360p207 Ns360p942 5631755 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 64193721) qz601 0 3 Ns360p941 Ns360p204 Ns360p942 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 64193721) (BSN.cosOddQ 33554432) 0 3 Ns360p943 Ns360p207 Ns360p942 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p945 := @Ns360p932 2503984432 177502945280000 5631755 16777216 156499027 11093934080000 (@Ns360p933 467 33554432 Bool.true 5631755 16777216 1 5290000 (@Ns360p936 Ns360p198 64193721 33554432 467 33554432 (@Ns360p937 70368744177664 621500773 281474976710656 Ns360p934 Ns360p195 Ns360p935 Ns360p198 RS361to372.d47 (@Ns360p938 0 1 342817181351920 21426073834495 70368744177664 621500773 281474976710656 (@Ns360p939 142841446229216329728 17028027323391 70368744177664 621500773 281474976710656 (@Ns360p940 336288101 281474976710656 (Ns360p923 rfl rfl) (Ns360p923 rfl rfl) rfl) (Ns360p923 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 64193721 33554432) (BSN.cos_neg_of_bound 64193721 33554432 Bool.true 5631755 16777216 1 5290000 (Ns360p944 rfl rfl)) rfl rfl) 

noncomputable def Ns360p946 := @Ns360p907 594254247394259053983 Ns360p831 (Ns360p908 qz33 (@Enclosure.Real.IsNear.of_eq qz663 (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 10311251 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz135 (BSN.t_div_two_pi_nonneg qz134 704586 1000 qz137)) Ns360p912) rfl) (@Ns360p913 140737488355328 3681260984803081 186125328349921280000 (BSN.correction_mk qz136 (BSN.cos_two_pi_p_ne_zero_mk qz134 704586 1000 10 qz137 rfl rfl (@BSN.floor_sqrt_eq_dec qz134 704586 1000 10 qz137 rfl rfl rfl))) (@Ns360p914 16777216 5631755 16777216 156499027 11093934080000 55850390290995 140737488355328 3681260984803081 186125328349921280000 Ns360p931 (Ns360p945 rfl) rfl)) 

noncomputable def Ns360p947 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz134) (hardyZApproximantRS₀ qz134) Bool.true 6100621131379268278409 4722366482869645213696 115952697012896641133983 Ns360p831 (@Eq.refl Real (hardyZApproximantRS₀ qz134)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz134) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 10) (@HMul.hMul Real Real Real qz5 qz659 (Zeta.RiemannSiegel.correction qz136))) Bool.true 6100621131379268278409 4722366482869645213696 115952697012896641133983 Ns360p831 (BSN.hardyZApproximantRS₀_eq qz134 10 (@BSN.floor_sqrt_eq_dec qz134 704586 1000 10 qz137 rfl rfl rfl)) (@Ns360p833 6100621131379268278409 4722366482869645213696 115952697012896641133983 Ns360p831 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 10)) Bool.true 157022377 134217728 79333 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz134) qz134 10) (Ns360p906 (Ns360p905 rfl rfl rfl rfl) rfl rfl)) (Ns360p946 rfl) rfl rfl)) 

theorem RS361to372.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz134) Bool.true 6100621131379268278409 4722366482869645213696 115952697012896641133983 Ns360p831 := Ns360p947 

noncomputable def Ns360p948 := nat_lit 19516655229984705609728000 

noncomputable def Ns360p949 := nat_lit 44461058698361888576257392640 

noncomputable abbrev qz770 := (Enclosure.sfrac Bool.false 705917 1000)

noncomputable abbrev qz666 := qz770

noncomputable abbrev qz469 := qz666

noncomputable abbrev qz152 := qz469

noncomputable abbrev qz771 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 705917 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz667 := qz771

noncomputable abbrev qz470 := qz667

noncomputable abbrev qz153 := qz470

noncomputable abbrev qz772 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 705917 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz668 := qz772

noncomputable abbrev qz471 := qz668

noncomputable abbrev qz154 := qz471

noncomputable abbrev qz669 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz153 qz9))

noncomputable def Ns360p950 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 10) (@HMul.hMul Real Real Real qz5 qz669 (Zeta.RiemannSiegel.correction qz154)) 167139141 134217728 79485 67108864 36282156715278280327 295147905179352825856 125189890095775367707 Ns360p948 Ns360p949 

noncomputable def Ns360p951 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos BSN.quadSignNeg 9 10 705917 1000 198 268435456 134217728 4503599627370496 Bool.false 352505402466 2545 618095470 52 84886744 8 

noncomputable def Ns360p952 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 705917 1000 98 151 268435456 134217728 4503599627370496 Bool.false 352505402466 2545 

noncomputable def Ns360p953 := Ns360p952 558195838 52 94906264 8 589812974 52 89478488 8 Bool.false 205727667 119565 Bool.true 212100937 Bool.true 183331032 14148475504056880 1 Bool.false 188910805 Bool.true Bool.false 169407710 Bool.false Bool.false 195406850 

noncomputable def Ns360p954 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 705917 1000 30 38 268435456 134217728 4503599627370496 Bool.false 352505402466 2545 

noncomputable def Ns360p955 := Ns360p954 480971758 52 109588312 8 522351262 52 101459064 8 Bool.false 315028989 88684 Bool.false 329539125 Bool.true 208251077 14148475504056880 1 Bool.false 90320884 Bool.true Bool.false 191626416 Bool.true Bool.false 205727667 

noncomputable def Ns360p956 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 705917 1000 212 112 268435456 134217728 4503599627370496 Bool.false 352505402466 2545 

noncomputable def Ns360p957 := Ns360p956 372130544 51 134217720 8 432030192 51 120047984 16 Bool.false 262944226 52144 Bool.false 420750444 Bool.false 302313454 14148475504056880 1 Bool.false 906982 Bool.false Bool.false 115451037 Bool.false Bool.false 315028989 

noncomputable def Ns360p958 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 705917 1000 524 342 268435456 134217728 4503599627370496 Bool.false 352505402466 2545 

noncomputable def Ns360p959 := Ns360p958 186065264 51 189812528 16 294906480 51 154981288 8 Bool.false 268435368 2603 Bool.false 210277087 Bool.false 119064356 14148475504056880 1 Bool.false 190202189 Bool.false Bool.false 242460080 Bool.true Bool.false 262944226 

noncomputable def Ns360p960 := nat_lit 1646609776438268051601390131734016033355902659133340154223 

noncomputable def Ns360p961 := nat_lit 1253905452510828664788272219873616661121175392354304000 

noncomputable def Ns360p962 := nat_lit 84141450247981749264439514891360000 

noncomputable def Ns360p963 := nat_lit 356381364244620233645341676229241062720 

noncomputable abbrev qz670 := (@Eq.refl Real qz770)

noncomputable abbrev qz472 := qz670

noncomputable abbrev qz155 := qz472

noncomputable def Ns360p964 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz152 705917 1000 1993276243556 16000000 1411834 4000 2000 Ns360p962 Ns360p963 qz155 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns360p965 := nat_lit 526915128460245776512444842154885130673888850922668849351360 

noncomputable abbrev qz671 := (@HSub.hSub Real Real Real qz741 qz742 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz743 (@Nat.cast Real Real.instNatCast 1411834))))

noncomputable abbrev qz473 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 705917 4000) (Real.log (Enclosure.sfrac Bool.false 1993276243556 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz671))

noncomputable abbrev qz672 := (Enclosure.sfrac Bool.false 705917 2000)

noncomputable abbrev qz156 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz473 qz672) (@HMul.hMul Real Real Real qz349 qz672 (Real.log Real.pi)))

noncomputable def Ns360p966 := @Enclosure.Real.IsNear.addLit_ft_p qz156 (Enclosure.sfrac Bool.true Ns360p962 Ns360p963) 1478515085411205920063 1125899906842624000 20534325755903007337 Ns360p88 Ns360p962 Ns360p963 0 1 Ns360p965 

noncomputable def Ns360p967 := nat_lit 19844293557761800433100547686400 

noncomputable abbrev qz157 := (@HSub.hSub Real Real Real qz353 qz473 qz672)

noncomputable def Ns360p968 := @Enclosure.Real.IsNear.subLit_ff_p qz157 (@HMul.hMul Real Real Real qz5 qz672 (Real.log Real.pi)) 386685219140534720371 225179981368524800 2230992118786497 529000000000000000000 27114809172837 67108864000 705917 134217728000 Ns360p967 1478515085411205920063 1125899906842624000 

noncomputable def Ns360p969 := nat_lit 3866852191405347203710000 

noncomputable abbrev qz158 := qz473

noncomputable def Ns360p970 := @Enclosure.Real.IsNear.subLit_ff_p qz158 qz672 2330822037971985904959 1125899906842624000 2230992118786497 529000000000000000000 705917 2000 0 1 Ns360p969 386685219140534720371 225179981368524800 2230992118786497 529000000000000000000 

noncomputable def Ns360p971 := nat_lit 5248544630838787899901539370068344832 

noncomputable def Ns360p972 := nat_lit 56735862974611337267642368 

noncomputable def Ns360p973 := nat_lit 11770440311298289542064763889706113189768365059778755969996092804084633915722236611883004930509255935821138665482332612426989447506483158400165290002335480484566031057227868431974400 

noncomputable def Ns360p974 := nat_lit 401959832400548579094756220526051380824865634385811739503992889213337584253624961810376408214148159485141851951039085943429550085762647797634015113619637800279821326228627537264640 

noncomputable def Ns360p975 := nat_lit 60937443236573165056049514806285743652152460247926142635193111148121620830474345416806189727593543234576898253452455922399923790493746393870981167670108413817257389415464960 

noncomputable def Ns360p976 := BSN.log_dyadic_bound 944700243556 3041852243556 8 7 Ns360p973 134217728 42320000 Ns360p974 Ns360p975 86214299 3986552487112 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 944700243556) (BSN.artanhQ 3041852243556) 0 7 Ns360p974 Ns360p973 Ns360p975 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz474 := (Real.log (Enclosure.sfrac Bool.false 1993276243556 16000000))

noncomputable def Ns360p977 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 705917 4000) qz474 705917 4000 0 1 3302461873659127 281474976710656 781250529 33062500000000000 2331263978467829954459 1125899906842624000 551498029680093 132250000000000000000 (Enclosure.Real.IsNear.const Bool.false 705917 4000) (BSN.isNear_log_sfrac 1993276243556 16000000 3302461873659127 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1993276243556) qz356)) Bool.false Ns360p972 Ns360p100 1000000677120000 42320000000000000000000 3302461873659127 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 1993276243556 16000000 16 3986552487112 2097152000000 86214299 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns360p976 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p978 := BSN.arctan_dyadic_bound_f 1000 1411834 1 0 16777216 5290000 0 1 1 0 1 1 11883 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1411834) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1411834) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns360p979 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1411834))) 884279719003555 562949953421312 1 2000000000000000 11883 16777216 1 5290000 14829062315845441552384 883880991688099 562949953421312 200000000529 1058000000000000000 qz17 (Ns360p978 rfl) rfl rfl 

noncomputable abbrev qz475 := (@HMul.hMul Real Real Real qz583 qz588 qz671)

noncomputable abbrev qz159 := qz475

noncomputable abbrev qz476 := qz671

noncomputable abbrev qz160 := qz476

noncomputable def Ns360p980 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 705917 4000) qz474) qz159 2331263978467829954459 1125899906842624000 551498029680093 132250000000000000000 883880991688099 2251799813685248 200000000529 4232000000000000000 Ns360p971 2330822037971985904959 1125899906842624000 2230992118786497 529000000000000000000 (Ns360p977 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz160 1 4 0 1 883880991688099 562949953421312 200000000529 1058000000000000000 883880991688099 2251799813685248 200000000529 4232000000000000000 qz363 Ns360p979 rfl) 

noncomputable def Ns360p981 := @Ns360p966 Ns360p960 Ns360p961 20534325755903007337 Ns360p88 (@Ns360p968 20534325755903007337 Ns360p88 (Ns360p970 (Ns360p980 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 705917 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz672 (Real.log Real.pi) 705917 2000 0 1 38410761 33554432 1 67108864 27114809172837 67108864000 705917 134217728000 (Enclosure.Real.IsNear.const Bool.false 705917 2000) RS361to372.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns360p962 Ns360p963) 

noncomputable def Ns360p982 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns360p960 Ns360p961 20534325755903007337 Ns360p88 11015793827 8388608 319 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz364 qz156 (Enclosure.sfrac Bool.true Ns360p962 Ns360p963)) Bool.false Ns360p960 Ns360p961 20534325755903007337 Ns360p88 Ns360p964 (Ns360p981 rfl rfl)) 

noncomputable def Ns360p983 := nat_lit 1898041439785826851487744 

noncomputable def Ns360p984 := nat_lit 3503913699220242888794350858405986227972359568937522677294391990276768102362299358012737838975581928734970709507289208063990007534375141376 

noncomputable def Ns360p985 := nat_lit 2487886541295947604380881941132707292656772108166423487184305952015599457695156760681903779316620657066824466302097356296848750411776 

noncomputable def Ns360p986 := nat_lit 17497841039156168198314699260937893552355867368592313164815346949325214077167732274199713898971289541646324145614942598687480114923370971136 

noncomputable def Ns360p987 := BSN.sin_dyadic_bound_f 107891164576 68719476736 4 3 33554432 10590333 Ns360p984 Ns360p114 Ns360p985 Ns360p986 Ns360p117 Ns360p985 33554421 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107891164576) qz594 0 3 Ns360p984 Ns360p114 Ns360p985 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107891164576) qz595 0 3 Ns360p986 Ns360p117 Ns360p985 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p988 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz152) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11015793827) qz413) Bool.false 11015793827 8388608 319 33554432 Bool.false 33554421 33554432 1 5290000 (Ns360p982 rfl) (Enclosure.sfrac_false_div 11015793827 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11015793827) qz413) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns360p983) qz414) 226375608064910080 72057594037927936 Bool.false 33554421 33554432 208 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q3 11015793827 8388608 226375608064910080 72057594037927936 208 Ns360p983 Ns360p459 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554421 33554432 Ns360p983 Ns360p459 107891164576 68719476736 10590333 10580000 (Ns360p987 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p989 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns360p960 Ns360p961 20534325755903007337 Ns360p88 352505402466 268435456 2545 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz364 qz156 (Enclosure.sfrac Bool.true Ns360p962 Ns360p963)) Bool.false Ns360p960 Ns360p961 20534325755903007337 Ns360p88 Ns360p964 (Ns360p981 rfl rfl)) 

noncomputable def Ns360p990 := Ns360p959 52144 BSN.abs_quadSignPos (BSN.cos_quad_nat0 524 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 190202189 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 342 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 242460080 268435456) qz155 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) Bool.false 33554421 33554432 107566527 11093934080000 268435368 268435456 2603 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.false 33554421 33554432 107566527 11093934080000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz152) qz152) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.false 33554421 33554432 1721064432 177502945280000 33554421 33554432 107566527 11093934080000 (Ns360p988 rfl rfl) rfl)) rfl) (Ns360p989 rfl) RS361to372.d7 

noncomputable def Ns360p991 := nat_lit 17058228654691904214444045186355108405501656770086893151022710883539201 

noncomputable def Ns360p992 := nat_lit 3822395457831158281631785224467014093019223078369131617300790565121 

noncomputable def Ns360p993 := nat_lit 51167041173160050326768871988616391188318931864103941189833531069487361 

noncomputable def Ns360p994 := BSN.cos_dyadic_bound_f 210277087 268435456 3 2 268435456 134217728 Ns360p991 Ns360p123 Ns360p992 Ns360p993 Ns360p126 Ns360p992 190202189 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 210277087) qz367 0 2 Ns360p991 Ns360p123 Ns360p992 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 210277087) qz368 0 2 Ns360p993 Ns360p126 Ns360p992 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p995 := nat_lit 1753096693754694706313552387789475427137047011872003768060517558583296 

noncomputable def Ns360p996 := nat_lit 40388166526325844379546525460672794269044487315140757645825212416 

noncomputable def Ns360p997 := nat_lit 5259209304931031467251898070317504935822602946641381022666261025325056 

noncomputable def Ns360p998 := BSN.cos_dyadic_bound_f 119064356 268435456 3 2 268435456 134217728 Ns360p995 Ns360p123 Ns360p996 Ns360p997 Ns360p126 Ns360p996 242460080 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 119064356) qz367 0 2 Ns360p995 Ns360p123 Ns360p996 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 119064356) qz368 0 2 Ns360p997 Ns360p126 Ns360p996 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p999 := nat_lit 16923936889594949343767132442788120414523233653347396085697644049991896113378314412567348228716650218458710016 

noncomputable def Ns360p1000 := nat_lit 30781869686734295344530723147531749177393891399726998707571657874430895597236198391920939386608010919936 

noncomputable def Ns360p1001 := nat_lit 102426690933575400661863065926135506030305721819732983754655479945504811556848687884528828038440232313799311360 

noncomputable def Ns360p1002 := BSN.cos_dyadic_bound_f 420750444 268435456 4 3 268435456 134217728 Ns360p999 Ns360p129 Ns360p1000 Ns360p1001 Ns360p132 Ns360p1000 906982 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 420750444) qz367 0 3 Ns360p999 Ns360p129 Ns360p1000 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 420750444) qz368 0 3 Ns360p1001 Ns360p132 Ns360p1000 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1003 := nat_lit 4498734544300993598872752576199163691711332730939769383432160595340829045704917357829648525383453480003178496 

noncomputable def Ns360p1004 := nat_lit 582759957116853713173802295643817707536308988590842471333093697554814523073301670644542540254037282816 

noncomputable def Ns360p1005 := nat_lit 27274914123711378114639939914530634403478968181905386606699405093770470154230623174616816496628896336100331520 

noncomputable def Ns360p1006 := BSN.cos_dyadic_bound_f 302313454 268435456 4 3 268435456 134217728 Ns360p1003 Ns360p129 Ns360p1004 Ns360p1005 Ns360p132 Ns360p1004 115451037 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 302313454) qz367 0 3 Ns360p1003 Ns360p129 Ns360p1004 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 302313454) qz368 0 3 Ns360p1005 Ns360p132 Ns360p1004 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1007 := Ns360p957 88684 BSN.abs_quadSignPos (BSN.cos_quad_nat0 212 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 906982 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 112 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 115451037 268435456) qz155 rfl rfl (Ns360p990 RS361to372.d9 RS361to372.d11 RS361to372.d13 RS361to372.d17 (Ns360p994 rfl rfl) (Ns360p998 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns360p989 rfl) RS361to372.d19 RS361to372.d21 RS361to372.d23 RS361to372.d25 RS361to372.d17 (Ns360p1002 rfl rfl) (Ns360p1006 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns360p1008 := nat_lit 6354180478161571484028305132341449309255996619060683716795955974067770084654096395187885537520783453369140625 

noncomputable def Ns360p1009 := nat_lit 1640150915241987746553911294762374803106612820431942447618560174461853217503536143340170383453369140625 

noncomputable def Ns360p1010 := nat_lit 38513989688467042630208256014891759171977636667037579657153782734465662797193116680442046004096143453369140625 

noncomputable def Ns360p1011 := BSN.cos_dyadic_bound_f 329539125 268435456 4 3 268435456 134217728 Ns360p1008 Ns360p129 Ns360p1009 Ns360p1010 Ns360p132 Ns360p1009 90320884 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 329539125) qz367 0 3 Ns360p1008 Ns360p129 Ns360p1009 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 329539125) qz368 0 3 Ns360p1010 Ns360p132 Ns360p1009 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1012 := nat_lit 16410108445330387497054718341475013743527666719341327470290363381384161 

noncomputable def Ns360p1013 := nat_lit 3537513034847635405562313864126418411582725768094869107602016371681 

noncomputable def Ns360p1014 := nat_lit 49223250309921467220353030396696788393759834706487792672655886111409121 

noncomputable def Ns360p1015 := BSN.cos_dyadic_bound_f 208251077 268435456 3 2 268435456 134217728 Ns360p1012 Ns360p123 Ns360p1013 Ns360p1014 Ns360p126 Ns360p1013 191626416 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 208251077) qz367 0 2 Ns360p1012 Ns360p123 Ns360p1013 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 208251077) qz368 0 2 Ns360p1014 Ns360p126 Ns360p1013 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1016 := Ns360p955 119565 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 30 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 90320884 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 38 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 191626416 268435456) qz155 rfl rfl (Ns360p1007 rfl rfl) (Ns360p989 rfl) RS361to372.d27 RS361to372.d29 RS361to372.d31 RS361to372.d33 RS361to372.d17 (Ns360p1011 rfl rfl) (Ns360p1015 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p1017 := nat_lit 17657934125038248062165459898245322877959813772828921062058466351841601 

noncomputable def Ns360p1018 := nat_lit 4095818439308646992677009320467402949252042434336369887964353331521 

noncomputable def Ns360p1019 := nat_lit 52965610738236126892511025676095033827980937233618090446399470348861761 

noncomputable def Ns360p1020 := BSN.cos_dyadic_bound_f 212100937 268435456 3 2 268435456 134217728 Ns360p1017 Ns360p123 Ns360p1018 Ns360p1019 Ns360p126 Ns360p1018 188910805 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 212100937) qz367 0 2 Ns360p1017 Ns360p123 Ns360p1018 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 212100937) qz368 0 2 Ns360p1019 Ns360p126 Ns360p1018 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1021 := nat_lit 17738483084727467220368460713511755604740304695411327595597121066106880 

noncomputable def Ns360p1022 := nat_lit 1276109275198327471355801883982122262209231755500944119260854091776 

noncomputable def Ns360p1023 := nat_lit 46455865806888283523154249618051960290657221160377904078942228076036096 

noncomputable def Ns360p1024 := BSN.sin_dyadic_bound_f 183331032 268435456 3 2 268435456 134217728 Ns360p1021 Ns360p144 Ns360p1022 Ns360p1023 Ns360p147 Ns360p1022 169407710 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 183331032) qz369 0 2 Ns360p1021 Ns360p144 Ns360p1022 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 183331032) qz370 0 2 Ns360p1023 Ns360p147 Ns360p1022 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1025 := Ns360p953 146547 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 98 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 188910805 268435456) BSN.abs_quadSignPos qz631 (BSN.sfrac_eq_quadSignPos_mul Bool.false 169407710 268435456) qz155 rfl rfl (Ns360p1016 rfl) (Ns360p989 rfl) RS361to372.d35 RS361to372.d37 RS361to372.d39 RS361to372.d41 RS361to372.d17 (Ns360p1020 rfl rfl) (Ns360p1024 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p1026 := nat_lit 6430792698896896388787762026323963886765980271747724066565372819999856030060378262690519638138403374917177441 

noncomputable def Ns360p1027 := nat_lit 1700111930360514990674499536013981568302788343945088653054609241350073808297937772267830263073808011361 

noncomputable def Ns360p1028 := nat_lit 38977929622756785133825604066432132075166397596326092602744920221985900516441627957683839018692966040725311585 

noncomputable def Ns360p1029 := BSN.cos_dyadic_bound_f 330526633 268435456 4 3 268435456 134217728 Ns360p1026 Ns360p129 Ns360p1027 Ns360p1028 Ns360p132 Ns360p1027 89390345 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 330526633) qz367 0 3 Ns360p1026 Ns360p129 Ns360p1027 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 330526633) qz368 0 3 Ns360p1028 Ns360p132 Ns360p1027 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1030 := Ns360p951 Bool.false 195406850 146547 Bool.true 330526633 14148475504056880 1 Bool.false 89390345 Bool.true Bool.false 167139141 158970 BSN.abs_quadSignNeg qz632 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 89390345 268435456) qz155 rfl (Ns360p1025 rfl) (Ns360p989 rfl) RS361to372.d43 RS361to372.d45 RS361to372.d17 (Ns360p1029 rfl rfl) rfl 

noncomputable def Ns360p1031 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 10) 167139141 268435456 158970 268435456 167139141 268435456 158970 268435456 89732143059566592 167139141 134217728 79485 67108864 (Ns360p1030 rfl rfl rfl rfl) 

noncomputable def Ns360p1032 := @Enclosure.Real.IsNear.mulLit_ff qz669 (Zeta.RiemannSiegel.correction qz154) 2576597 8388608 1 16777216 14081424730091 35184372088832 242032996986601 11632833021870080000 36282156715278280327 295147905179352825856 

noncomputable abbrev qz673 := (@HPow.hPow Real Real Real qz7 qz153 qz9)

noncomputable def Ns360p1033 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz673 1 1 0 1 2576597 8388608 1 16777216 2576597 8388608 1 16777216 

noncomputable def Ns360p1034 := @Enclosure.Real.IsNear.sqrt_image qz153 3769845968701 33554432000 705917 33554432000 177830689 177830723 16777216 (@Enclosure.Real.IsNear.of_eq qz153 (@HMul.hMul Real Real Real qz5 qz152 qz3) Bool.false 3769845968701 33554432000 705917 33554432000 (BSN.t_div_two_pi_mk qz152 705917 1000 qz155) (@Enclosure.Real.IsNear.mulLit_ff qz152 qz3 705917 1000 0 1 5340353 33554432 1 33554432 3769845968701 33554432000 705917 33554432000 (Enclosure.Real.IsNear.const Bool.false 705917 1000) RS361to372.d48 rfl)) 

noncomputable abbrev qz773 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 705917 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz674 := qz773

noncomputable abbrev qz477 := qz674

noncomputable abbrev qz161 := qz477

noncomputable def Ns360p1035 := @Enclosure.Real.IsNear.sqrt_image qz161 88915353 8388608 17 16777216 54621459 54621466 16777216 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 355661412 33554432 34 33554432 88915353 8388608 17 16777216 (Ns360p1034 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns360p1036 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz161) 109242925 33554432 7 33554432 5153193 5153195 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz161) Bool.false 109242925 33554432 7 33554432 109242925 33554432 7 33554432 (Ns360p1035 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns360p1037 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 10306388 33554432 2 33554432 2576597 8388608 1 16777216 (Ns360p1036 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz478 := (@HMul.hMul Real Real Real qz583 qz581 qz668)

noncomputable abbrev qz162 := (Real.cos qz478)

noncomputable abbrev qz675 := (@HMul.hMul Real Real Real qz737 qz772 qz772)

noncomputable abbrev qz479 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz675 qz668) qz600)

noncomputable abbrev qz163 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz479))

noncomputable def Ns360p1038 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz154) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz162) qz163) Bool.false 14081424730091 

noncomputable def Ns360p1039 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz162) qz163 41388079 33554432 337 

noncomputable abbrev qz164 := (@Neg.neg Real Real.instNeg (Real.cos qz478))

noncomputable def Ns360p1040 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz162) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz164)) Bool.true 41388079 33554432 337 33554432 (BSN.inv_eq_neg_inv_neg qz162) 

noncomputable def Ns360p1041 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz164) Bool.false 41388079 33554432 337 33554432 41388079 33554432 

noncomputable def Ns360p1042 := @Enclosure.Real.IsNear.recentre' qz162 Bool.true 27203483 33554432 1170904432 177502945280000 27203483 33554432 73181527 11093934080000 

noncomputable abbrev qz165 := qz478

noncomputable def Ns360p1043 := @Enclosure.Real.IsNear.cos_image qz165 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15799927) (@Nat.cast Real Real.instNatCast 4194304)) Bool.false 15799927 4194304 215 33554432 Bool.true 27203483 33554432 1 

noncomputable def Ns360p1044 := nat_lit 458763282040151024968495671 

noncomputable def Ns360p1045 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz154 884279719003555 140737488355328 1 500000000000000 5029273 8388608 17 16777216 4447284115232166065515 1180591620717411303424 Ns360p1044 

noncomputable def Ns360p1046 := @Enclosure.Real.IsNear.subLit_ff_p qz161 qz1 88915353 8388608 17 16777216 10 1 0 1 5029273 5029273 8388608 17 

noncomputable def Ns360p1047 := @Ns360p1046 16777216 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 355661412 33554432 34 33554432 88915353 8388608 17 16777216 (Ns360p1034 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns360p1048 := @Enclosure.Real.IsNear.recentre' qz165 Bool.false 4447284115232166065515 1180591620717411303424 Ns360p1044 Ns360p180 15799927 4194304 215 33554432 (@Ns360p1045 Ns360p180 RS361to372.d47 (Ns360p1047 rfl rfl) rfl) 

noncomputable def Ns360p1049 := nat_lit 127828821427822399107354255824063767809717821494463826639643266451342971085294586646690625 

noncomputable def Ns360p1050 := nat_lit 11639147287089424769858512028892418596022945843350934174630708614169679401188937890625 

noncomputable def Ns360p1051 := nat_lit 383463185988893018472523050448133518591961418591704778050580537936800573897081382064290625 

noncomputable def Ns360p1052 := BSN.cos_dyadic_bound_f 42977400695 68719476736 3 2 33554432 10590333 Ns360p1049 Ns360p693 Ns360p1050 Ns360p1051 Ns360p696 Ns360p1050 27203483 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 42977400695) qz376 0 2 Ns360p1049 Ns360p693 Ns360p1050 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 42977400695) qz377 0 2 Ns360p1051 Ns360p696 Ns360p1050 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1053 := @Ns360p1043 5290000 (Ns360p1048 rfl) (Enclosure.sfrac_false_div 15799927 4194304) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15799927) (@Nat.cast Real Real.instNatCast 4194304)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 378033214371624023752704) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 27203483 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q2 15799927 4194304 226375608064910080 72057594037927936 0 378033214371624023752704 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 27203483 33554432 378033214371624023752704 604462909807314587353088 42977400695 68719476736 10590333 10580000 (Ns360p1052 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p1054 := @Enclosure.Real.IsNear.inv_image qz164 27203483 33554432 73181527 11093934080000 20693871 20694208 16777216 (@Enclosure.Real.IsNear.neg qz162 Bool.true 27203483 33554432 73181527 11093934080000 (Ns360p1042 (Ns360p1053 rfl rfl) rfl)) 

noncomputable def Ns360p1055 := Ns360p1040 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz164) Bool.false 41388079 33554432 337 33554432 (@Ns360p1041 337 33554432 (Ns360p1054 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p1056 := @Enclosure.Real.IsNear.recentre' qz163 Bool.true 5443664 16777216 

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz349 qz346 qz479)

noncomputable def Ns360p1057 := @Enclosure.Real.IsNear.cos_image qz166 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 31897601)) qz365) Bool.true 31897601 16777216 

noncomputable def Ns360p1058 := nat_lit 18829020516247059144819807245 

noncomputable def Ns360p1059 := nat_lit 16925761623199866137188355609988387 

noncomputable def Ns360p1060 := @Enclosure.Real.IsNear.recentre' qz166 Bool.true Ns360p1058 Ns360p195 Ns360p1059 

noncomputable abbrev qz167 := qz479

noncomputable def Ns360p1061 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz167 884279719003555 140737488355328 1 500000000000000 21293059324559 

noncomputable abbrev qz480 := (@HSub.hSub Real Real Real qz587 qz675 qz668)

noncomputable abbrev qz168 := qz480

noncomputable def Ns360p1062 := @Enclosure.Real.IsNear.subLit_tf qz168 qz31 16895012813455 70368744177664 627203525 281474976710656 1 16 

noncomputable abbrev qz481 := qz675

noncomputable abbrev qz169 := qz481

noncomputable def Ns360p1063 := @Enclosure.Real.IsNear.subLit_ff_n qz169 qz154 25293586908529 70368744177664 341990853 281474976710656 5029273 8388608 17 16777216 

noncomputable def Ns360p1064 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz154 5029273 8388608 17 16777216 5029273 8388608 17 16777216 25293586908529 70368744177664 

noncomputable def Ns360p1065 := nat_lit 130702936152268470161919179731482197258207569394476038749770514193157688363604495381478973153281 

noncomputable def Ns360p1066 := nat_lit 1109420674839433005855621773162361978670917362325940775832514256837113495914556985562931201 

noncomputable def Ns360p1067 := nat_lit 788845910971542212066553704018283498288964349555789968494774563040192566404784260173122229018625 

noncomputable def Ns360p1068 := BSN.cos_dyadic_bound_t 31897601 16777216 4 3 16777216 5290000 Ns360p1065 Ns360p475 Ns360p1066 Ns360p1067 Ns360p478 Ns360p1066 5443664 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 31897601) (BSN.cosEvenQ 16777216) 0 3 Ns360p1065 Ns360p475 Ns360p1066 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 31897601) (BSN.cosOddQ 16777216) 0 3 Ns360p1067 Ns360p478 Ns360p1066 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1069 := @Ns360p1056 2525144432 177502945280000 340229 1048576 157821527 11093934080000 (@Ns360p1057 471 33554432 Bool.true 5443664 16777216 1 5290000 (@Ns360p1060 Ns360p198 31897601 16777216 471 33554432 (@Ns360p1061 70368744177664 627203525 281474976710656 Ns360p1058 Ns360p195 Ns360p1059 Ns360p198 RS361to372.d47 (@Ns360p1062 0 1 340688949192944 21293059324559 70368744177664 627203525 281474976710656 (@Ns360p1063 141725639647051120640 16895012813455 70368744177664 627203525 281474976710656 (@Ns360p1064 341990853 281474976710656 (Ns360p1047 rfl rfl) (Ns360p1047 rfl rfl) rfl) (Ns360p1047 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 31897601 16777216) (BSN.cos_neg_of_bound 31897601 16777216 Bool.true 5443664 16777216 1 5290000 (Ns360p1068 rfl rfl)) rfl rfl) 

noncomputable def Ns360p1070 := @Ns360p1032 125189890095775367707 Ns360p948 (Ns360p1033 qz33 (@Enclosure.Real.IsNear.of_eq qz673 (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 2576597 8388608 1 16777216 (BSN.rpow_neg_quarter_mk qz153 (BSN.t_div_two_pi_nonneg qz152 705917 1000 qz155)) Ns360p1037) rfl) (@Ns360p1038 35184372088832 242032996986601 11632833021870080000 (BSN.correction_mk qz154 (BSN.cos_two_pi_p_ne_zero_mk qz152 705917 1000 10 qz155 rfl rfl (@BSN.floor_sqrt_eq_dec qz152 705917 1000 10 qz155 rfl rfl rfl))) (@Ns360p1039 33554432 340229 1048576 157821527 11093934080000 14081424730091 35184372088832 242032996986601 11632833021870080000 Ns360p1055 (Ns360p1069 rfl) rfl)) 

noncomputable def Ns360p1071 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (hardyZApproximantRS₀ qz152) Bool.false 331260701256706480505 295147905179352825856 23241083208679358087707 Ns360p948 (@Eq.refl Real (hardyZApproximantRS₀ qz152)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 10) (@HMul.hMul Real Real Real qz5 qz669 (Zeta.RiemannSiegel.correction qz154))) Bool.false 331260701256706480505 295147905179352825856 23241083208679358087707 Ns360p948 (BSN.hardyZApproximantRS₀_eq qz152 10 (@BSN.floor_sqrt_eq_dec qz152 705917 1000 10 qz155 rfl rfl rfl)) (@Ns360p950 331260701256706480505 295147905179352825856 23241083208679358087707 Ns360p948 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 10)) Bool.false 167139141 134217728 79485 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz152) qz152 10) (Ns360p1031 (Ns360p1030 rfl rfl rfl rfl) rfl rfl)) (Ns360p1070 rfl) rfl rfl)) 

theorem RS361to372.d58 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz152) Bool.false 331260701256706480505 295147905179352825856 23241083208679358087707 Ns360p948 := Ns360p1071 

noncomputable def Ns360p1072 := nat_lit 3726588261373877165570153 

noncomputable def Ns360p1073 := nat_lit 3122664836797552897556480000 

noncomputable def Ns360p1074 := nat_lit 6801102335686466861582642053120 

noncomputable abbrev qz774 := (Enclosure.sfrac Bool.false 707248 1000)

noncomputable abbrev qz676 := qz774

noncomputable abbrev qz482 := qz676

noncomputable abbrev qz170 := qz482

noncomputable abbrev qz775 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 707248 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz677 := qz775

noncomputable abbrev qz483 := qz677

noncomputable abbrev qz171 := qz483

noncomputable abbrev qz776 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 707248 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz678 := qz776

noncomputable abbrev qz484 := qz678

noncomputable abbrev qz172 := qz484

noncomputable abbrev qz679 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz171 qz9))

noncomputable def Ns360p1075 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 10) (@HMul.hMul Real Real Real qz5 qz679 (Zeta.RiemannSiegel.correction qz172)) 703448825 134217728 79633 67108864 1171350691455585912615 9444732965739290427392 21158693251556843010153 Ns360p1073 Ns360p1074 

noncomputable def Ns360p1076 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.cos BSN.quadSignNeg 9 10 707248 1000 198 268435456 134217728 4503599627370496 Bool.false 353349058713 2550 618095470 52 84886744 8 

noncomputable def Ns360p1077 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 707248 1000 98 151 268435456 134217728 4503599627370496 Bool.false 353349058713 2550 

noncomputable def Ns360p1078 := Ns360p1077 558195838 52 94906264 8 589812974 52 89478488 8 Bool.true 622263053 119786 Bool.true 111403350 Bool.true 124715854 14148475504056880 1 Bool.false 245648604 Bool.true Bool.false 120277258 Bool.false Bool.true 669020528 

noncomputable def Ns360p1079 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 707248 1000 31 38 268435456 134217728 4503599627370496 Bool.false 353349058713 2550 

noncomputable def Ns360p1080 := Ns360p1079 480971758 52 109588312 8 522351262 52 101459064 8 Bool.true 567486267 88847 Bool.false 111364534 Bool.true 59844359 14148475504056880 1 Bool.false 108197362 Bool.false Bool.false 261792259 Bool.true Bool.true 622263053 

noncomputable def Ns360p1081 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 707248 1000 213 113 268435456 134217728 4503599627370496 Bool.false 353349058713 2550 

noncomputable def Ns360p1082 := Ns360p1081 372130544 51 134217720 8 432030192 51 120047984 16 Bool.true 374993545 52238 Bool.false 347443509 Bool.false 149280087 14148475504056880 1 Bool.false 258241732 Bool.true Bool.false 141703795 Bool.true Bool.true 567486267 

noncomputable def Ns360p1083 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 707248 1000 525 343 268435456 134217728 4503599627370496 Bool.false 353349058713 2550 

noncomputable def Ns360p1084 := Ns360p1083 186065264 51 189812528 16 294906480 51 154981288 8 Bool.true 268435416 2603 Bool.false 384623039 Bool.false 148542650 14148475504056880 1 Bool.false 265884802 Bool.true Bool.false 141076945 Bool.false Bool.true 374993545 

noncomputable def Ns360p1085 := nat_lit 101886685117487981828982793905579945836365145001558253 

noncomputable def Ns360p1086 := nat_lit 77402212077160151392556331188472832475252391936000 

noncomputable def Ns360p1087 := nat_lit 84937686425818193895994326384640000 

noncomputable def Ns360p1088 := nat_lit 360432137163170387002436123734679224320 

noncomputable abbrev qz680 := (@Eq.refl Real qz774)

noncomputable abbrev qz485 := qz680

noncomputable abbrev qz173 := qz485

noncomputable def Ns360p1089 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz170 707248 1000 2000799934016 16000000 1414496 4000 2000 Ns360p1087 Ns360p1088 qz173 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns360p1090 := nat_lit 133544915917193847542884327627921746606640522856442433372160 

noncomputable abbrev qz681 := (@HSub.hSub Real Real Real qz741 qz742 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz743 (@Nat.cast Real Real.instNatCast 1414496))))

noncomputable abbrev qz486 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 707248 4000) (Real.log (Enclosure.sfrac Bool.false 2000799934016 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz681))

noncomputable abbrev qz682 := (Enclosure.sfrac Bool.false 707248 2000)

noncomputable abbrev qz174 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz486 qz682) (@HMul.hMul Real Real Real qz349 qz682 (Real.log Real.pi)))

noncomputable def Ns360p1091 := @Enclosure.Real.IsNear.addLit_ft_p qz174 (Enclosure.sfrac Bool.true Ns360p1087 Ns360p1088) 370513408921053950813 281474976710656000 1285803122729949983 135424000000000000000000 Ns360p1087 Ns360p1088 0 1 Ns360p1090 

noncomputable def Ns360p1092 := nat_lit 12432366984729698160886153216 

noncomputable abbrev qz175 := (@HSub.hSub Real Real Real qz353 qz486 qz682)

noncomputable def Ns360p1093 := @Enclosure.Real.IsNear.subLit_ff_p qz175 (@HMul.hMul Real Real Real qz5 qz682 (Real.log Real.pi)) 3875644752989131873 2251799813685248 2235151496602893 529000000000000000000 1697870868483 4194304000 44203 8388608000 Ns360p1092 370513408921053950813 281474976710656000 

noncomputable abbrev qz176 := qz486

noncomputable def Ns360p1094 := @Enclosure.Real.IsNear.subLit_ff_p qz176 qz682 583991901287970501469 281474976710656000 2235151496602893 529000000000000000000 707248 2000 0 1 968911188247282968250000 3875644752989131873 2251799813685248 2235151496602893 529000000000000000000 

noncomputable def Ns360p1095 := nat_lit 328758213628486429182797408871907328 

noncomputable def Ns360p1096 := nat_lit 56754081115967961492881408 

noncomputable def Ns360p1097 := nat_lit 12184638918060927604760775122656247240386998820250919032280869446883811353956344482374763915113011863713329181594965324145331472045070533390311014362372602288768855312627338208870400 

noncomputable def Ns360p1098 := nat_lit 420966370946592387251855659611890636141824531632824094651309783310550520345117181893733144949841146396463650170869914653912336165333131040898716851712405579944827721278181070602240 

noncomputable def Ns360p1099 := nat_lit 68094988500094518660990479083980601310724032152722399656179687253854460901710439129433400115047639859819621596602206842156888458083656907794557219231684746265509945000591360 

noncomputable def Ns360p1100 := BSN.log_dyadic_bound 952223934016 3049375934016 8 7 Ns360p1097 134217728 42320000 Ns360p1098 Ns360p1099 86719954 4001599868032 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 952223934016) (BSN.artanhQ 3049375934016) 0 7 Ns360p1098 Ns360p1097 Ns360p1099 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz487 := (Real.log (Enclosure.sfrac Bool.false 2000799934016 16000000))

noncomputable def Ns360p1101 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 707248 4000) qz487 707248 4000 0 1 3303522309053687 281474976710656 781250529 33062500000000000 146025596627100126461 70368744177664000 34533617133387 8265625000000000000 (Enclosure.Real.IsNear.const Bool.false 707248 4000) (BSN.isNear_log_sfrac 2000799934016 16000000 3303522309053687 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2000799934016) qz356)) Bool.false Ns360p1096 Ns360p100 1000000677120000 42320000000000000000000 3303522309053687 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 2000799934016 16000000 16 4001599868032 2097152000000 86719954 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns360p1100 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p1102 := BSN.arctan_dyadic_bound_f 1000 1414496 1 0 16777216 5290000 0 1 1 0 1 1 11860 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1414496) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1414496) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns360p1103 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1414496))) 884279719003555 562949953421312 1 2000000000000000 11860 16777216 1 5290000 14829075263694370242560 883881763440035 562949953421312 200000000529 1058000000000000000 qz17 (Ns360p1102 rfl) rfl rfl 

noncomputable abbrev qz488 := (@HMul.hMul Real Real Real qz583 qz588 qz681)

noncomputable abbrev qz177 := qz488

noncomputable abbrev qz489 := qz681

noncomputable abbrev qz178 := qz489

noncomputable def Ns360p1104 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 707248 4000) qz487) qz177 146025596627100126461 70368744177664000 34533617133387 8265625000000000000 883881763440035 2251799813685248 200000000529 4232000000000000000 Ns360p1095 583991901287970501469 281474976710656000 2235151496602893 529000000000000000000 (Ns360p1101 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz178 1 4 0 1 883881763440035 562949953421312 200000000529 1058000000000000000 883881763440035 2251799813685248 200000000529 4232000000000000000 qz363 Ns360p1103 rfl) 

noncomputable def Ns360p1105 := @Ns360p1091 Ns360p1085 Ns360p1086 1285803122729949983 135424000000000000000000 (@Ns360p1093 1285803122729949983 135424000000000000000000 (Ns360p1094 (Ns360p1104 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 707248 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz682 (Real.log Real.pi) 707248 2000 0 1 38410761 33554432 1 67108864 1697870868483 4194304000 44203 8388608000 (Enclosure.Real.IsNear.const Bool.false 707248 2000) RS361to372.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns360p1087 Ns360p1088) 

noncomputable def Ns360p1106 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz170) Bool.false Ns360p1085 Ns360p1086 1285803122729949983 135424000000000000000000 44168632339 33554432 319 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz170) (@HAdd.hAdd Real Real Real qz364 qz174 (Enclosure.sfrac Bool.true Ns360p1087 Ns360p1088)) Bool.false Ns360p1085 Ns360p1086 1285803122729949983 135424000000000000000000 Ns360p1089 (Ns360p1105 rfl rfl)) 

noncomputable def Ns360p1107 := BSN.cos_dyadic_bound_f 34259156 68719476736 1 0 33554432 10590333 0 1 1 0 1 1 33554427 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 34259156) qz376 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 34259156) qz377 0 0 rfl) rfl rfl 

noncomputable def Ns360p1108 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz170) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44168632339) qz378) Bool.false 44168632339 33554432 319 33554432 Bool.true 33554427 33554432 1 5290000 (Ns360p1106 rfl) (Enclosure.sfrac_false_div 44168632339 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44168632339) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2410773811639854563328) qz391) 226375608064910080 72057594037927936 Bool.false 33554427 33554432 209 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q2 44168632339 33554432 226375608064910080 72057594037927936 209 2410773811639854563328 Ns360p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554427 33554432 2410773811639854563328 Ns360p100 34259156 68719476736 10590333 10580000 (Ns360p1107 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p1109 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz170) Bool.false Ns360p1085 Ns360p1086 1285803122729949983 135424000000000000000000 353349058713 268435456 2550 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz170) (@HAdd.hAdd Real Real Real qz364 qz174 (Enclosure.sfrac Bool.true Ns360p1087 Ns360p1088)) Bool.false Ns360p1085 Ns360p1086 1285803122729949983 135424000000000000000000 Ns360p1089 (Ns360p1105 rfl rfl)) 

noncomputable def Ns360p1110 := Ns360p1084 52238 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 525 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 265884802 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 343 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 141076945 268435456) qz173 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 1) Bool.true 33554427 33554432 107566527 11093934080000 268435416 268435456 2603 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz170)) Bool.true 33554427 33554432 107566527 11093934080000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz170) qz170) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz170)) Bool.true 33554427 33554432 1721064432 177502945280000 33554427 33554432 107566527 11093934080000 (Ns360p1108 rfl rfl) rfl)) rfl) (Ns360p1109 rfl) RS361to372.d7 

noncomputable def Ns360p1111 := nat_lit 30659447543058782627399162292667415116896735528860113380319632293637494826964125148482560759160758206854040321 

noncomputable def Ns360p1112 := nat_lit 10481502448865190106624407543218260417738861851910791884024540400359938689456310768654037662841356389121 

noncomputable def Ns360p1113 := nat_lit 153165295608786348029169370703729128990534250282355749919984492142421557329843436975727474396127634048294030081 

noncomputable def Ns360p1114 := BSN.sin_dyadic_bound_f 384623039 268435456 4 3 268435456 134217728 Ns360p1111 Ns360p258 Ns360p1112 Ns360p1113 Ns360p261 Ns360p1112 265884802 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 384623039) qz369 0 3 Ns360p1111 Ns360p258 Ns360p1112 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 384623039) qz370 0 3 Ns360p1113 Ns360p261 Ns360p1112 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1115 := nat_lit 7644682221197742004571742771858210472491469654686120431755948900000000 

noncomputable def Ns360p1116 := nat_lit 237033287354335587327241831191690693195782127506568789062500000000 

noncomputable def Ns360p1117 := nat_lit 20021403001624083944832225058568621833498198781685780971797574500000000 

noncomputable def Ns360p1118 := BSN.sin_dyadic_bound_f 148542650 268435456 3 2 268435456 134217728 Ns360p1115 Ns360p144 Ns360p1116 Ns360p1117 Ns360p147 Ns360p1116 141076945 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 148542650) qz369 0 2 Ns360p1115 Ns360p144 Ns360p1116 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 148542650) qz370 0 2 Ns360p1117 Ns360p147 Ns360p1116 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1119 := nat_lit 20405998834155286425013217843085138462477226359009713925755971966542872813384373608650522613025858850045204881 

noncomputable def Ns360p1120 := nat_lit 3094642106152007043647696105089862379653779691083920458951018176280634249102007415977338517638633134481 

noncomputable def Ns360p1121 := nat_lit 101971497848560433286769669588185863076605688955112357626715498560278032426459821098659089022261203517970749841 

noncomputable def Ns360p1122 := BSN.sin_dyadic_bound_f 347443509 268435456 4 3 268435456 134217728 Ns360p1119 Ns360p258 Ns360p1120 Ns360p1121 Ns360p261 Ns360p1120 258241732 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 347443509) qz369 0 3 Ns360p1119 Ns360p258 Ns360p1120 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 347443509) qz370 0 3 Ns360p1121 Ns360p261 Ns360p1120 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1123 := nat_lit 7797628757008385528237624669580630332390971944177181620781411239654465 

noncomputable def Ns360p1124 := nat_lit 246612471747718268836453951823600300148211432375957543443485357121 

noncomputable def Ns360p1125 := nat_lit 20421961752924846744377567494884412660538019892430676504119073318040641 

noncomputable def Ns360p1126 := BSN.sin_dyadic_bound_f 149280087 268435456 3 2 268435456 134217728 Ns360p1123 Ns360p144 Ns360p1124 Ns360p1125 Ns360p147 Ns360p1124 141703795 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 149280087) qz369 0 2 Ns360p1123 Ns360p144 Ns360p1124 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 149280087) qz370 0 2 Ns360p1125 Ns360p147 Ns360p1124 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1127 := Ns360p1082 88847 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 213 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 258241732 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 113 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 141703795 268435456) qz173 rfl rfl (Ns360p1110 RS361to372.d9 RS361to372.d11 RS361to372.d13 RS361to372.d17 (Ns360p1114 rfl rfl) (Ns360p1118 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns360p1109 rfl) RS361to372.d19 RS361to372.d21 RS361to372.d23 RS361to372.d25 RS361to372.d17 (Ns360p1122 rfl rfl) (Ns360p1126 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns360p1128 := nat_lit 153811078180585903329586476568336 

noncomputable def Ns360p1129 := BSN.sin_dyadic_bound_f 111364534 268435456 2 1 268435456 134217728 Ns360p1128 Ns360p135 Ns360p1128 Ns360p1128 Ns360p136 Ns360p1128 108197362 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 111364534) qz369 0 1 Ns360p1128 Ns360p135 Ns360p1128 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 111364534) qz370 0 1 Ns360p1128 Ns360p136 Ns360p1128 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1130 := nat_lit 12826048512733902102924260216161 

noncomputable def Ns360p1131 := BSN.cos_dyadic_bound_f 59844359 268435456 2 1 268435456 134217728 Ns360p1130 Ns360p155 Ns360p1130 Ns360p1130 Ns360p156 Ns360p1130 261792259 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 59844359) qz367 0 1 Ns360p1130 Ns360p155 Ns360p1130 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 59844359) qz368 0 1 Ns360p1130 Ns360p156 Ns360p1130 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1132 := Ns360p1080 119786 BSN.abs_quadSignPos (BSN.cos_quad_nat3 31 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 108197362 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 38 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 261792259 268435456) qz173 rfl rfl (Ns360p1127 rfl rfl) (Ns360p1109 rfl) RS361to372.d27 RS361to372.d29 RS361to372.d31 RS361to372.d33 RS361to372.d17 (Ns360p1129 rfl rfl) (Ns360p1131 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p1133 := nat_lit 1343598366426438513095689015793902784308309937218805065477030500000000 

noncomputable def Ns360p1134 := nat_lit 23723895660829659888307456600135941874583642293306289062500000000 

noncomputable def Ns360p1135 := nat_lit 4030747651487993879967290432468508081041180644371828583852966500000000 

noncomputable def Ns360p1136 := BSN.cos_dyadic_bound_f 111403350 268435456 3 2 268435456 134217728 Ns360p1133 Ns360p123 Ns360p1134 Ns360p1135 Ns360p126 Ns360p1134 245648604 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 111403350) qz367 0 2 Ns360p1133 Ns360p123 Ns360p1134 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 111403350) qz368 0 2 Ns360p1135 Ns360p126 Ns360p1134 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1137 := nat_lit 3798696988117667780743349372886734537295182023301205831094493187784960 

noncomputable def Ns360p1138 := nat_lit 58529298560611542522890918190362913807844404585804414047766036736 

noncomputable def Ns360p1139 := nat_lit 9948873540491460340401830343692948914865025931990971588577119108710656 

noncomputable def Ns360p1140 := BSN.sin_dyadic_bound_f 124715854 268435456 3 2 268435456 134217728 Ns360p1137 Ns360p144 Ns360p1138 Ns360p1139 Ns360p147 Ns360p1138 120277258 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 124715854) qz369 0 2 Ns360p1137 Ns360p144 Ns360p1138 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 124715854) qz370 0 2 Ns360p1139 Ns360p147 Ns360p1138 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1141 := Ns360p1078 146819 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 98 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 245648604 268435456) BSN.abs_quadSignPos qz631 (BSN.sfrac_eq_quadSignPos_mul Bool.false 120277258 268435456) qz173 rfl rfl (Ns360p1132 rfl) (Ns360p1109 rfl) RS361to372.d35 RS361to372.d37 RS361to372.d39 RS361to372.d41 RS361to372.d17 (Ns360p1136 rfl rfl) (Ns360p1140 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p1142 := nat_lit 4946016851935583634154448134315396428752408756417653112672561905624416395532276215959524775065518534679330816 

noncomputable def Ns360p1143 := nat_lit 774214954407751309738533696074672176145550542258038140027697956183572312228875535019353501150516084736 

noncomputable def Ns360p1144 := nat_lit 29984796644912415394117735553226070881622382442756182974633469151078760987370749057969166249968219410357288960 

noncomputable def Ns360p1145 := BSN.cos_dyadic_bound_f 309555456 268435456 4 3 268435456 134217728 Ns360p1142 Ns360p129 Ns360p1143 Ns360p1144 Ns360p132 Ns360p1143 108871835 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 309555456) qz367 0 3 Ns360p1142 Ns360p129 Ns360p1143 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 309555456) qz368 0 3 Ns360p1144 Ns360p132 Ns360p1143 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1146 := Ns360p1076 Bool.true 669020528 146819 Bool.true 309555456 14148475504056880 1 Bool.false 108871835 Bool.true Bool.true 703448825 159266 BSN.abs_quadSignNeg qz632 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 108871835 268435456) qz173 rfl (Ns360p1141 rfl) (Ns360p1109 rfl) RS361to372.d43 RS361to372.d45 RS361to372.d17 (Ns360p1145 rfl rfl) rfl 

noncomputable def Ns360p1147 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 10) 703448825 268435456 159266 268435456 703448825 268435456 159266 268435456 377661212223078400 703448825 134217728 79633 67108864 (Ns360p1146 rfl rfl rfl rfl) 

noncomputable def Ns360p1148 := @Enclosure.Real.IsNear.mulLit_ff qz679 (Zeta.RiemannSiegel.correction qz172) 10301535 33554432 1 33554432 113706422533689 281474976710656 4100572781691321 186125328349921280000 1171350691455585912615 9444732965739290427392 

noncomputable abbrev qz683 := (@HPow.hPow Real Real Real qz7 qz171 qz9)

noncomputable def Ns360p1149 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz683 1 1 0 1 10301535 33554432 1 33554432 10301535 33554432 1 33554432 

noncomputable def Ns360p1150 := @Enclosure.Real.IsNear.sqrt_image qz171 236059623659 2097152000 44203 2097152000 177998259 177998293 16777216 (@Enclosure.Real.IsNear.of_eq qz171 (@HMul.hMul Real Real Real qz5 qz170 qz3) Bool.false 236059623659 2097152000 44203 2097152000 (BSN.t_div_two_pi_mk qz170 707248 1000 qz173) (@Enclosure.Real.IsNear.mulLit_ff qz170 qz3 707248 1000 0 1 5340353 33554432 1 33554432 236059623659 2097152000 44203 2097152000 (Enclosure.Real.IsNear.const Bool.false 707248 1000) RS361to372.d48 rfl)) 

noncomputable abbrev qz777 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 707248 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz684 := qz777

noncomputable abbrev qz490 := qz684

noncomputable abbrev qz179 := qz490

noncomputable def Ns360p1151 := @Enclosure.Real.IsNear.sqrt_image qz179 44499569 4194304 17 16777216 54647188 54647194 16777216 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 355996552 33554432 34 33554432 44499569 4194304 17 16777216 (Ns360p1150 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns360p1152 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz179) 54647191 16777216 3 16777216 5150767 5150768 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz179) Bool.false 109294382 33554432 6 33554432 54647191 16777216 3 16777216 (Ns360p1151 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns360p1153 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 10301535 33554432 1 33554432 10301535 33554432 1 33554432 (Ns360p1152 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz491 := (@HMul.hMul Real Real Real qz583 qz581 qz678)

noncomputable abbrev qz180 := (Real.cos qz491)

noncomputable abbrev qz685 := (@HMul.hMul Real Real Real qz737 qz776 qz776)

noncomputable abbrev qz492 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz685 qz678) qz600)

noncomputable abbrev qz181 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz492))

noncomputable def Ns360p1154 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz172) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz180) qz181) Bool.false 113706422533689 

noncomputable def Ns360p1155 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz180) qz181 21720437 16777216 93 

noncomputable abbrev qz182 := (@Neg.neg Real Real.instNeg (Real.cos qz491))

noncomputable def Ns360p1156 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz180) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz182)) Bool.true 21720437 16777216 93 8388608 (BSN.inv_eq_neg_inv_neg qz180) 

noncomputable def Ns360p1157 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz182) Bool.false 43440874 33554432 372 33554432 21720437 16777216 

noncomputable def Ns360p1158 := @Enclosure.Real.IsNear.recentre' qz180 Bool.true 25917985 33554432 1170904432 177502945280000 25917985 33554432 73181527 11093934080000 

noncomputable abbrev qz183 := qz491

noncomputable def Ns360p1159 := @Enclosure.Real.IsNear.cos_image qz183 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 128505163) qz378) Bool.false 128505163 33554432 215 33554432 Bool.true 25917985 33554432 1 

noncomputable def Ns360p1160 := nat_lit 458763282041590440308077111 

noncomputable def Ns360p1161 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz172 884279719003555 140737488355328 1 500000000000000 2556529 4194304 17 16777216 2260686745744439460595 590295810358705651712 Ns360p1160 

noncomputable def Ns360p1162 := @Enclosure.Real.IsNear.subLit_ff_p qz179 qz1 44499569 4194304 17 16777216 10 1 0 1 2556529 2556529 4194304 17 

noncomputable def Ns360p1163 := @Ns360p1162 16777216 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 355996552 33554432 34 33554432 44499569 4194304 17 16777216 (Ns360p1150 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns360p1164 := @Enclosure.Real.IsNear.recentre' qz183 Bool.false 2260686745744439460595 590295810358705651712 Ns360p1160 Ns360p180 128505163 33554432 215 33554432 (@Ns360p1161 Ns360p180 RS361to372.d47 (Ns360p1163 rfl rfl) rfl) 

noncomputable def Ns360p1165 := nat_lit 3327735839918161464918016 

noncomputable def Ns360p1166 := nat_lit 187397072261439722365994463618028177598264279402772549689047799029815821310895938724969281 

noncomputable def Ns360p1167 := nat_lit 25012226253434746721840267032474396229588738687851799753030644444166062257677258734401 

noncomputable def Ns360p1168 := nat_lit 562141192331812297604539710320019584002333660730941945467637335800559131808172461657439041 

noncomputable def Ns360p1169 := BSN.cos_dyadic_bound_f 47289970551 68719476736 3 2 33554432 10590333 Ns360p1166 Ns360p693 Ns360p1167 Ns360p1168 Ns360p696 Ns360p1167 25917985 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 47289970551) qz376 0 2 Ns360p1166 Ns360p693 Ns360p1167 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 47289970551) qz377 0 2 Ns360p1168 Ns360p696 Ns360p1167 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1170 := @Ns360p1159 5290000 (Ns360p1164 rfl) (Enclosure.sfrac_false_div 128505163 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 128505163) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns360p1165) qz391) 226375608064910080 72057594037927936 Bool.false 25917985 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q2 128505163 33554432 226375608064910080 72057594037927936 0 Ns360p1165 Ns360p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 25917985 33554432 Ns360p1165 Ns360p100 47289970551 68719476736 10590333 10580000 (Ns360p1169 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p1171 := @Enclosure.Real.IsNear.inv_image qz182 25917985 33554432 73181527 11093934080000 21720251 21720623 16777216 (@Enclosure.Real.IsNear.neg qz180 Bool.true 25917985 33554432 73181527 11093934080000 (Ns360p1158 (Ns360p1170 rfl rfl) rfl)) 

noncomputable def Ns360p1172 := Ns360p1156 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz182) Bool.false 21720437 16777216 93 8388608 (@Ns360p1157 93 8388608 (Ns360p1171 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p1173 := @Enclosure.Real.IsNear.recentre' qz181 Bool.true 5234997 16777216 

noncomputable abbrev qz184 := (@HMul.hMul Real Real Real qz349 qz346 qz492)

noncomputable def Ns360p1174 := @Enclosure.Real.IsNear.cos_image qz184 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 63354975)) qz378) Bool.true 63354975 33554432 

noncomputable def Ns360p1175 := nat_lit 4674772068262501976356719805 

noncomputable def Ns360p1176 := nat_lit 2475880078570760549798248448 

noncomputable def Ns360p1177 := nat_lit 17079511549508796829308572615792607 

noncomputable def Ns360p1178 := @Enclosure.Real.IsNear.recentre' qz184 Bool.true Ns360p1175 Ns360p1176 Ns360p1177 

noncomputable abbrev qz185 := qz492

noncomputable def Ns360p1179 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz185 884279719003555 140737488355328 1 500000000000000 5286530910751 

noncomputable abbrev qz493 := (@HSub.hSub Real Real Real qz587 qz685 qz678)

noncomputable abbrev qz186 := qz493

noncomputable def Ns360p1180 := @Enclosure.Real.IsNear.subLit_tf qz186 qz31 4187019282975 17592186044416 632900905 281474976710656 1 16 

noncomputable abbrev qz494 := qz685

noncomputable abbrev qz187 := qz494

noncomputable def Ns360p1181 := @Enclosure.Real.IsNear.subLit_ff_n qz187 qz172 6535840527841 17592186044416 347688233 281474976710656 2556529 4194304 17 16777216 

noncomputable def Ns360p1182 := @Enclosure.Real.IsNear.mulLit_ff qz172 qz172 2556529 4194304 17 16777216 2556529 4194304 17 16777216 6535840527841 17592186044416 

noncomputable def Ns360p1183 := nat_lit 520624198830378191017869967813155631463337048120924980847722222472674720982956238566197276962890625 

noncomputable def Ns360p1184 := nat_lit 4181852268884133630631427948450024051083297321286897666380493409168947090482771396636962890625 

noncomputable def Ns360p1185 := nat_lit 3142622692485095230130131978223962965595463009329356147346824421063290743812964337579853852962890625 

noncomputable def Ns360p1186 := BSN.cos_dyadic_bound_t 63354975 33554432 4 3 16777216 5290000 Ns360p1183 Ns360p204 Ns360p1184 Ns360p1185 Ns360p207 Ns360p1184 5234997 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 63354975) qz601 0 3 Ns360p1183 Ns360p204 Ns360p1184 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 63354975) (BSN.cosOddQ 33554432) 0 3 Ns360p1185 Ns360p207 Ns360p1184 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1187 := @Ns360p1173 2546304432 177502945280000 5234997 16777216 159144027 11093934080000 (@Ns360p1174 475 33554432 Bool.true 5234997 16777216 1 5290000 (@Ns360p1178 Ns360p198 63354975 33554432 475 33554432 (@Ns360p1179 17592186044416 632900905 281474976710656 Ns360p1175 Ns360p1176 Ns360p1177 Ns360p198 RS361to372.d47 (@Ns360p1180 0 1 84584494572016 5286530910751 17592186044416 632900905 281474976710656 (@Ns360p1181 17561631726659174400 4187019282975 17592186044416 632900905 281474976710656 (@Ns360p1182 347688233 281474976710656 (Ns360p1163 rfl rfl) (Ns360p1163 rfl rfl) rfl) (Ns360p1163 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 63354975 33554432) (BSN.cos_neg_of_bound 63354975 33554432 Bool.true 5234997 16777216 1 5290000 (Ns360p1186 rfl rfl)) rfl rfl) 

noncomputable def Ns360p1188 := @Ns360p1148 21158693251556843010153 Ns360p1073 (Ns360p1149 qz33 (@Enclosure.Real.IsNear.of_eq qz683 (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 10301535 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz171 (BSN.t_div_two_pi_nonneg qz170 707248 1000 qz173)) Ns360p1153) rfl) (@Ns360p1154 281474976710656 4100572781691321 186125328349921280000 (BSN.correction_mk qz172 (BSN.cos_two_pi_p_ne_zero_mk qz170 707248 1000 10 qz173 rfl rfl (@BSN.floor_sqrt_eq_dec qz170 707248 1000 10 qz173 rfl rfl rfl))) (@Ns360p1155 8388608 5234997 16777216 159144027 11093934080000 113706422533689 281474976710656 4100572781691321 186125328349921280000 Ns360p1172 (Ns360p1187 rfl) rfl)) 

noncomputable def Ns360p1189 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz170) (hardyZApproximantRS₀ qz170) Bool.true 50672161099958917957415 9444732965739290427392 Ns360p1072 Ns360p1073 (@Eq.refl Real (hardyZApproximantRS₀ qz170)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz170) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 10) (@HMul.hMul Real Real Real qz5 qz679 (Zeta.RiemannSiegel.correction qz172))) Bool.true 50672161099958917957415 9444732965739290427392 Ns360p1072 Ns360p1073 (BSN.hardyZApproximantRS₀_eq qz170 10 (@BSN.floor_sqrt_eq_dec qz170 707248 1000 10 qz173 rfl rfl rfl)) (@Ns360p1075 50672161099958917957415 9444732965739290427392 Ns360p1072 Ns360p1073 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 10)) Bool.true 703448825 134217728 79633 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz170) qz170 10) (Ns360p1147 (Ns360p1146 rfl rfl rfl rfl) rfl rfl)) (Ns360p1188 rfl) rfl rfl)) 

theorem RS361to372.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz170) Bool.true 50672161099958917957415 9444732965739290427392 Ns360p1072 Ns360p1073 := Ns360p1189 

noncomputable def Ns360p1190 := nat_lit 124906593471902115902259200 

noncomputable def Ns360p1191 := nat_lit 396698289365724201237310603264 

noncomputable abbrev qz778 := (Enclosure.sfrac Bool.false 708578 1000)

noncomputable abbrev qz686 := qz778

noncomputable abbrev qz495 := qz686

noncomputable abbrev qz188 := qz495

noncomputable abbrev qz779 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 708578 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz687 := qz779

noncomputable abbrev qz496 := qz687

noncomputable abbrev qz189 := qz496

noncomputable abbrev qz780 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 708578 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz688 := qz780

noncomputable abbrev qz497 := qz688

noncomputable abbrev qz190 := qz497

noncomputable abbrev qz689 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz189 qz9))

noncomputable def Ns360p1192 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 10) (@HMul.hMul Real Real Real qz5 qz689 (Zeta.RiemannSiegel.correction qz190)) 46204005 33554432 9973 8388608 1182740920989477704953 9444732965739290427392 902094050571594456163 Ns360p1190 Ns360p1191 

noncomputable def Ns360p1193 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos BSN.quadSignNeg 9 10 708578 1000 198 268435456 134217728 4503599627370496 Bool.false 354192417482 2555 618095470 52 84886744 8 

noncomputable def Ns360p1194 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 708578 1000 98 151 268435456 134217728 4503599627370496 Bool.false 354192417482 2555 

noncomputable def Ns360p1195 := Ns360p1194 558195838 52 94906264 8 589812974 52 89478488 8 Bool.false 298401423 120014 Bool.true 10445046 Bool.true 65808340 14148475504056880 1 Bool.false 268232268 Bool.true Bool.false 65151126 Bool.false Bool.false 225284039 

noncomputable def Ns360p1196 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 708578 1000 31 37 268435456 134217728 4503599627370496 Bool.false 354192417482 2555 

noncomputable def Ns360p1197 := Ns360p1196 480971758 52 109588312 8 522351262 52 101459064 8 Bool.false 293305055 89017 Bool.false 315030865 Bool.true 332870197 14148475504056880 1 Bool.false 247535604 Bool.false Bool.false 253885282 Bool.true Bool.false 298401423 

noncomputable def Ns360p1198 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 708578 1000 214 113 268435456 134217728 4503599627370496 Bool.false 354192417482 2555 

noncomputable def Ns360p1199 := Ns360p1198 372130544 51 134217720 8 432030192 51 120047984 16 Bool.false 483413605 52339 Bool.false 274211226 Bool.false 418038700 14148475504056880 1 Bool.false 140142956 Bool.true Bool.false 268411064 Bool.true Bool.false 293305055 

noncomputable def Ns360p1200 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 708578 1000 527 344 268435456 134217728 4503599627370496 Bool.false 354192417482 2555 

noncomputable def Ns360p1201 := Ns360p1200 186065264 51 189812528 16 294906480 51 154981288 8 Bool.false 268435392 2611 Bool.false 137200151 Bool.false 178018372 14148475504056880 1 Bool.false 131304138 Bool.false Bool.false 211539115 Bool.false Bool.false 483413605 

noncomputable def Ns360p1202 := nat_lit 13220818340564373329262507133187810602945633698908885533 

noncomputable def Ns360p1203 := nat_lit 10019797784394460955010752013874641734065232805888000 

noncomputable def Ns360p1204 := nat_lit 85739334086042233770892474096640000 

noncomputable def Ns360p1205 := nat_lit 364518119909715495123628061769509867520 

noncomputable abbrev qz690 := (@Eq.refl Real qz778)

noncomputable abbrev qz498 := qz690

noncomputable abbrev qz191 := qz498

noncomputable def Ns360p1206 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz188 708578 1000 2008332128336 16000000 1417156 4000 2000 Ns360p1204 Ns360p1205 qz191 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns360p1207 := nat_lit 270762359614758365783296146087686361148326578153653975715840 

noncomputable abbrev qz691 := (@HSub.hSub Real Real Real qz741 qz742 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz743 (@Nat.cast Real Real.instNatCast 1417156))))

noncomputable abbrev qz499 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 708578 4000) (Real.log (Enclosure.sfrac Bool.false 2008332128336 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz691))

noncomputable abbrev qz692 := (Enclosure.sfrac Bool.false 708578 2000)

noncomputable abbrev qz192 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz499 qz692) (@HMul.hMul Real Real Real qz349 qz692 (Real.log Real.pi)))

noncomputable def Ns360p1208 := @Enclosure.Real.IsNear.addLit_ft_p qz192 (Enclosure.sfrac Bool.true Ns360p1204 Ns360p1205) 742795469121741923417 562949953421312000 10305672613823948429 1083392000000000000000000 Ns360p1204 Ns360p1205 0 1 Ns360p1207 

noncomputable def Ns360p1209 := nat_lit 24924080058553589090844934144000 

noncomputable abbrev qz193 := (@HSub.hSub Real Real Real qz353 qz499 qz692)

noncomputable def Ns360p1210 := @Enclosure.Real.IsNear.subLit_ff_p qz193 (@HMul.hMul Real Real Real qz5 qz692 (Real.log Real.pi)) 971108382573541205081 562949953421312000 2239307749417173 529000000000000000000 13608510103929 33554432000 354289 67108864000 Ns360p1209 742795469121741923417 562949953421312000 

noncomputable def Ns360p1211 := nat_lit 1942216765147082410162000 

noncomputable abbrev qz194 := qz499

noncomputable def Ns360p1212 := @Enclosure.Real.IsNear.subLit_ff_p qz194 qz692 1170555358621224412249 562949953421312000 2239307749417173 529000000000000000000 708578 2000 0 1 Ns360p1211 971108382573541205081 562949953421312000 2239307749417173 529000000000000000000 

noncomputable def Ns360p1213 := nat_lit 2635856338451541787717809895481802752 

noncomputable def Ns360p1214 := nat_lit 56772251411082144533970944 

noncomputable def Ns360p1215 := nat_lit 12612829332842948287981431661534976675894608802079184759335009309927761904692376588412008845949345219995461758028632751502003898829819634790150062841056411538057078859601556170342400 

noncomputable def Ns360p1216 := nat_lit 440807701867949380834216113017069632154725495722121210034726889412617363839097440886777669796231432545445055849883971897511455259678824455598481383130773982306791069040495757885440 

noncomputable def Ns360p1217 := nat_lit 76036192338745927881955587802456403307719651700145477116209493541569310526016843110777913807479701477987525111458210817382001304658924516881099329799310982267449674731356160 

noncomputable def Ns360p1218 := BSN.log_dyadic_bound 959756128336 3056908128336 8 7 Ns360p1215 134217728 42320000 Ns360p1216 Ns360p1217 87224281 4016664256672 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 959756128336) (BSN.artanhQ 3056908128336) 0 7 Ns360p1216 Ns360p1215 Ns360p1217 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz500 := (Real.log (Enclosure.sfrac Bool.false 2008332128336 16000000))

noncomputable def Ns360p1219 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 708578 4000) qz500 708578 4000 0 1 3304579959430391 281474976710656 781250529 33062500000000000 1170776329246633796999 562949953421312000 276788468668881 66125000000000000000 (Enclosure.Real.IsNear.const Bool.false 708578 4000) (BSN.isNear_log_sfrac 2008332128336 16000000 3304579959430391 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2008332128336) qz356)) Bool.false Ns360p1214 Ns360p100 1000000677120000 42320000000000000000000 3304579959430391 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 2008332128336 16000000 16 4016664256672 2097152000000 87224281 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns360p1218 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p1220 := BSN.arctan_dyadic_bound_f 1000 1417156 1 0 16777216 5290000 0 1 1 0 1 1 11838 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1417156) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1417156) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns360p1221 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1417156))) 884279719003555 562949953421312 1 2000000000000000 11838 16777216 1 5290000 14829087648593345511424 883882501637539 562949953421312 200000000529 1058000000000000000 qz17 (Ns360p1220 rfl) rfl rfl 

noncomputable abbrev qz501 := (@HMul.hMul Real Real Real qz583 qz588 qz691)

noncomputable abbrev qz195 := qz501

noncomputable abbrev qz502 := qz691

noncomputable abbrev qz196 := qz502

noncomputable def Ns360p1222 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 708578 4000) qz500) qz195 1170776329246633796999 562949953421312000 276788468668881 66125000000000000000 883882501637539 2251799813685248 200000000529 4232000000000000000 Ns360p1213 1170555358621224412249 562949953421312000 2239307749417173 529000000000000000000 (Ns360p1219 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz196 1 4 0 1 883882501637539 562949953421312 200000000529 1058000000000000000 883882501637539 2251799813685248 200000000529 4232000000000000000 qz363 Ns360p1221 rfl) 

noncomputable def Ns360p1223 := @Ns360p1208 Ns360p1202 Ns360p1203 10305672613823948429 1083392000000000000000000 (@Ns360p1210 10305672613823948429 1083392000000000000000000 (Ns360p1212 (Ns360p1222 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 708578 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz692 (Real.log Real.pi) 708578 2000 0 1 38410761 33554432 1 67108864 13608510103929 33554432000 354289 67108864000 (Enclosure.Real.IsNear.const Bool.false 708578 2000) RS361to372.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns360p1204 Ns360p1205) 

noncomputable def Ns360p1224 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz188) Bool.false Ns360p1202 Ns360p1203 10305672613823948429 1083392000000000000000000 44274052185 33554432 5 524288 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz188) (@HAdd.hAdd Real Real Real qz364 qz192 (Enclosure.sfrac Bool.true Ns360p1204 Ns360p1205)) Bool.false Ns360p1202 Ns360p1203 10305672613823948429 1083392000000000000000000 Ns360p1206 (Ns360p1223 rfl rfl)) 

noncomputable def Ns360p1225 := BSN.cos_dyadic_bound_f 45500492 68719476736 1 0 33554432 10590333 0 1 1 0 1 1 33554424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 45500492) qz376 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 45500492) qz377 0 0 rfl) rfl rfl 

noncomputable def Ns360p1226 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz188) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44274052185) qz378) Bool.false 44274052185 33554432 5 524288 Bool.false 33554424 33554432 1 5290000 (Ns360p1224 rfl) (Enclosure.sfrac_false_div 44274052185 33554432) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44274052185) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3201812484048468049920) qz391) 226375608064910080 72057594037927936 Bool.false 33554424 33554432 210 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q0 44274052185 33554432 226375608064910080 72057594037927936 210 3201812484048468049920 Ns360p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554424 33554432 3201812484048468049920 Ns360p100 45500492 68719476736 10590333 10580000 (Ns360p1225 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p1227 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz188) Bool.false Ns360p1202 Ns360p1203 10305672613823948429 1083392000000000000000000 354192417482 268435456 2555 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz188) (@HAdd.hAdd Real Real Real qz364 qz192 (Enclosure.sfrac Bool.true Ns360p1204 Ns360p1205)) Bool.false Ns360p1202 Ns360p1203 10305672613823948429 1083392000000000000000000 Ns360p1206 (Ns360p1223 rfl rfl)) 

noncomputable def Ns360p1228 := Ns360p1201 52339 BSN.abs_quadSignPos (BSN.cos_quad_nat3 527 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 131304138 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 344 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 211539115 268435456) qz191 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 1) Bool.false 4194303 4194304 1685893 173342720000 268435392 268435456 2611 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz188)) Bool.false 4194303 4194304 1685893 173342720000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz188) qz188) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz188)) Bool.false 33554424 33554432 26974288 2773483520000 4194303 4194304 1685893 173342720000 (Ns360p1226 rfl rfl) rfl)) rfl) (Ns360p1227 rfl) RS361to372.d7 

noncomputable def Ns360p1229 := nat_lit 5563773725791500330181689264367309377757507871369976215252336378723905 

noncomputable def Ns360p1230 := nat_lit 125555781268651124620775970766022229294723667580391390327704731201 

noncomputable def Ns360p1231 := nat_lit 14571585048665208762940752531295046239088900586697664691981302803283521 

noncomputable def Ns360p1232 := BSN.sin_dyadic_bound_f 137200151 268435456 3 2 268435456 134217728 Ns360p1229 Ns360p144 Ns360p1230 Ns360p1231 Ns360p147 Ns360p1230 131304138 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 137200151) qz369 0 2 Ns360p1229 Ns360p144 Ns360p1230 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 137200151) qz370 0 2 Ns360p1231 Ns360p147 Ns360p1230 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1233 := nat_lit 8761492508151089958315718195112493210438203057677515448117498038255616 

noncomputable def Ns360p1234 := nat_lit 1008599155841870914802445601703632590433583751712829430753027751936 

noncomputable def Ns360p1235 := nat_lit 26282460326141586133117549694134072366133742005529120685490988059262976 

noncomputable def Ns360p1236 := BSN.cos_dyadic_bound_f 178018372 268435456 3 2 268435456 134217728 Ns360p1233 Ns360p123 Ns360p1234 Ns360p1235 Ns360p126 Ns360p1234 211539115 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 178018372) qz367 0 2 Ns360p1233 Ns360p123 Ns360p1234 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 178018372) qz368 0 2 Ns360p1235 Ns360p126 Ns360p1234 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1237 := nat_lit 3044157325349053690073393332019592508253432286338449494316013232411626715712395131445702033253659102847635456 

noncomputable def Ns360p1238 := nat_lit 180726886197765338272854891438074957979134661651192632362026696776508607054619701243627373621448216576 

noncomputable def Ns360p1239 := nat_lit 18459912115520014115823590620635918958478203964206869491195368300455064185173771534157721783479197043889213440 

noncomputable def Ns360p1240 := BSN.cos_dyadic_bound_f 274211226 268435456 4 3 268435456 134217728 Ns360p1237 Ns360p129 Ns360p1238 Ns360p1239 Ns360p132 Ns360p1238 140142956 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 274211226) qz367 0 3 Ns360p1237 Ns360p129 Ns360p1238 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 274211226) qz368 0 3 Ns360p1239 Ns360p132 Ns360p1238 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1241 := nat_lit 42808324914898234812372362759439714812135152092644750328336833716660445674242978284566316921166659584000000000 

noncomputable def Ns360p1242 := nat_lit 28483795705315575173110576319306149201405458377168618235863818727790736679264881000000000000000000000000 

noncomputable def Ns360p1243 := nat_lit 213784651550312679451271450257827957072180110541306176089174105088644141778718035745469777399433297920000000000 

noncomputable def Ns360p1244 := BSN.sin_dyadic_bound_f 418038700 268435456 4 3 268435456 134217728 Ns360p1241 Ns360p258 Ns360p1242 Ns360p1243 Ns360p261 Ns360p1242 268411064 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 418038700) qz369 0 3 Ns360p1241 Ns360p258 Ns360p1242 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 418038700) qz370 0 3 Ns360p1243 Ns360p261 Ns360p1242 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1245 := Ns360p1199 89017 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 214 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 140142956 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 113 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268411064 268435456) qz191 rfl rfl (Ns360p1228 RS361to372.d9 RS361to372.d11 RS361to372.d13 RS361to372.d17 (Ns360p1232 rfl rfl) (Ns360p1236 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns360p1227 rfl) RS361to372.d19 RS361to372.d21 RS361to372.d23 RS361to372.d25 RS361to372.d17 (Ns360p1240 rfl rfl) (Ns360p1244 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns360p1246 := nat_lit 154748364864798594788834754349457938055510824826877292903217139621930625 

noncomputable def Ns360p1247 := nat_lit 97011863129270376337835722879296890218542819392208585134042062890625 

noncomputable def Ns360p1248 := nat_lit 405136269724644167647163098792490023751698329029472191322970726146090625 

noncomputable def Ns360p1249 := BSN.sin_dyadic_bound_f 315030865 268435456 3 2 268435456 134217728 Ns360p1246 Ns360p144 Ns360p1247 Ns360p1248 Ns360p147 Ns360p1247 247535604 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 315030865) qz369 0 2 Ns360p1246 Ns360p144 Ns360p1247 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 315030865) qz370 0 2 Ns360p1248 Ns360p147 Ns360p1247 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1250 := nat_lit 17189262575289053200839891481781477077216853960155550839769494656125917426853412973403112285170000735516964241 

noncomputable def Ns360p1251 := nat_lit 1850542043131998393464854224404066926175779000974384284108676101201315134384668822138441018245554058641 

noncomputable def Ns360p1252 := nat_lit 85904794556631497538434389477196084633918101937738271349186961707007094386005439389820766023898011194804352401 

noncomputable def Ns360p1253 := BSN.sin_dyadic_bound_f 332870197 268435456 4 3 268435456 134217728 Ns360p1250 Ns360p258 Ns360p1251 Ns360p1252 Ns360p261 Ns360p1251 253885282 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 332870197) qz369 0 3 Ns360p1250 Ns360p258 Ns360p1251 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 332870197) qz370 0 3 Ns360p1252 Ns360p261 Ns360p1251 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1254 := Ns360p1197 120014 BSN.abs_quadSignPos (BSN.cos_quad_nat3 31 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 247535604 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 37 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 253885282 268435456) qz191 rfl rfl (Ns360p1245 rfl rfl) (Ns360p1227 rfl) RS361to372.d27 RS361to372.d29 RS361to372.d31 RS361to372.d33 RS361to372.d17 (Ns360p1249 rfl rfl) (Ns360p1253 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p1255 := nat_lit 11902588733598024592102557456 

noncomputable def Ns360p1256 := BSN.cos_dyadic_bound_f 10445046 268435456 2 1 268435456 134217728 Ns360p1255 Ns360p155 Ns360p1255 Ns360p1255 Ns360p156 Ns360p1255 268232268 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 10445046) qz367 0 1 Ns360p1255 Ns360p155 Ns360p1255 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 10445046) qz368 0 1 Ns360p1255 Ns360p156 Ns360p1255 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1257 := nat_lit 18755288277465253404874291360000 

noncomputable def Ns360p1258 := BSN.sin_dyadic_bound_f 65808340 268435456 2 1 268435456 134217728 Ns360p1257 Ns360p135 Ns360p1257 Ns360p1257 Ns360p136 Ns360p1257 65151126 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 65808340) qz369 0 1 Ns360p1257 Ns360p135 Ns360p1257 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 65808340) qz370 0 1 Ns360p1257 Ns360p136 Ns360p1257 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1259 := Ns360p1195 147098 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 98 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268232268 268435456) BSN.abs_quadSignPos qz631 (BSN.sfrac_eq_quadSignPos_mul Bool.false 65151126 268435456) qz191 rfl rfl (Ns360p1254 rfl) (Ns360p1227 rfl) RS361to372.d35 RS361to372.d37 RS361to372.d39 RS361to372.d41 RS361to372.d17 (Ns360p1256 rfl rfl) (Ns360p1258 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p1260 := nat_lit 3718330825904553417219594066363702807551929414507985149963643174305659789170993629680194042073369755345883136 

noncomputable def Ns360p1261 := nat_lit 329214377451643549386036323226516625353824569393006172374058107307074797384039608079843963089302982656 

noncomputable def Ns360p1262 := nat_lit 22545977294568673588596854799049881313769143025875404445560760603636354361501951051770929012034068455883673600 

noncomputable def Ns360p1263 := BSN.cos_dyadic_bound_f 288263662 268435456 4 3 268435456 134217728 Ns360p1260 Ns360p129 Ns360p1261 Ns360p1262 Ns360p132 Ns360p1261 127971113 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 288263662) qz367 0 3 Ns360p1260 Ns360p129 Ns360p1261 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 288263662) qz368 0 3 Ns360p1262 Ns360p132 Ns360p1261 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1264 := Ns360p1193 Bool.false 225284039 147098 Bool.true 288263662 14148475504056880 1 Bool.false 127971113 Bool.true Bool.false 184816020 159568 BSN.abs_quadSignNeg qz632 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 127971113 268435456) qz191 rfl (Ns360p1259 rfl) (Ns360p1227 rfl) RS361to372.d43 RS361to372.d45 RS361to372.d17 (Ns360p1263 rfl rfl) rfl 

noncomputable def Ns360p1265 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 10) 184816020 268435456 159568 268435456 184816020 268435456 159568 268435456 99222345209610240 46204005 33554432 9973 8388608 (Ns360p1264 rfl rfl rfl rfl) 

noncomputable def Ns360p1266 := @Enclosure.Real.IsNear.mulLit_ff qz689 (Zeta.RiemannSiegel.correction qz190) 5148349 16777216 1 16777216 229732079349997 562949953421312 4365747491051457 186125328349921280000 1182740920989477704953 9444732965739290427392 

noncomputable abbrev qz693 := (@HPow.hPow Real Real Real qz7 qz189 qz9)

noncomputable def Ns360p1267 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz693 1 1 0 1 5148349 16777216 1 16777216 5148349 16777216 1 16777216 

noncomputable def Ns360p1268 := @Enclosure.Real.IsNear.sqrt_image qz189 1892028324017 16777216000 354289 16777216000 178165546 178165580 16777216 (@Enclosure.Real.IsNear.of_eq qz189 (@HMul.hMul Real Real Real qz5 qz188 qz3) Bool.false 1892028324017 16777216000 354289 16777216000 (BSN.t_div_two_pi_mk qz188 708578 1000 qz191) (@Enclosure.Real.IsNear.mulLit_ff qz188 qz3 708578 1000 0 1 5340353 33554432 1 33554432 1892028324017 16777216000 354289 16777216000 (Enclosure.Real.IsNear.const Bool.false 708578 1000) RS361to372.d48 rfl)) 

noncomputable abbrev qz781 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 708578 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz694 := qz781

noncomputable abbrev qz503 := qz694

noncomputable abbrev qz197 := qz503

noncomputable def Ns360p1269 := @Enclosure.Real.IsNear.sqrt_image qz197 178165563 16777216 17 16777216 54672862 54672868 16777216 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 356331126 33554432 34 33554432 178165563 16777216 17 16777216 (Ns360p1268 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns360p1270 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz197) 54672865 16777216 3 16777216 5148348 5148350 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz197) Bool.false 109345730 33554432 6 33554432 54672865 16777216 3 16777216 (Ns360p1269 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns360p1271 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz197)) Bool.false 10296698 33554432 2 33554432 5148349 16777216 1 16777216 (Ns360p1270 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz504 := (@HMul.hMul Real Real Real qz583 qz581 qz688)

noncomputable abbrev qz198 := (Real.cos qz504)

noncomputable abbrev qz695 := (@HMul.hMul Real Real Real qz737 qz780 qz780)

noncomputable abbrev qz505 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz695 qz688) qz600)

noncomputable abbrev qz199 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz505))

noncomputable def Ns360p1272 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz190) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz198) qz199) Bool.false 229732079349997 

noncomputable def Ns360p1273 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz198) qz199 45893519 33554432 413 

noncomputable abbrev qz200 := (@Neg.neg Real Real.instNeg (Real.cos qz504))

noncomputable def Ns360p1274 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz198) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz200)) Bool.true 45893519 33554432 413 33554432 (BSN.inv_eq_neg_inv_neg qz198) 

noncomputable def Ns360p1275 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz200) Bool.false 45893519 33554432 413 33554432 45893519 33554432 

noncomputable def Ns360p1276 := @Enclosure.Real.IsNear.recentre' qz198 Bool.true 24532874 33554432 582807216 88751472640000 12266437 16777216 36425451 5546967040000 

noncomputable abbrev qz201 := qz504

noncomputable def Ns360p1277 := @Enclosure.Real.IsNear.cos_image qz201 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 65303677) qz365) Bool.false 65303677 16777216 107 16777216 Bool.true 24532874 33554432 1 

noncomputable def Ns360p1278 := nat_lit 91752656408605484939233803 

noncomputable def Ns360p1279 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz190 884279719003555 140737488355328 1 500000000000000 10393403 16777216 17 16777216 9190675484330705547665 2361183241434822606848 Ns360p1278 

noncomputable def Ns360p1280 := @Enclosure.Real.IsNear.subLit_ff_p qz197 qz1 178165563 16777216 17 16777216 10 1 0 1 10393403 10393403 16777216 17 

noncomputable def Ns360p1281 := @Ns360p1280 16777216 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 356331126 33554432 34 33554432 178165563 16777216 17 16777216 (Ns360p1268 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns360p1282 := @Enclosure.Real.IsNear.recentre' qz201 Bool.false 9190675484330705547665 2361183241434822606848 Ns360p1278 Ns360p920 65303677 16777216 107 16777216 (@Ns360p1279 Ns360p920 RS361to372.d47 (Ns360p1281 rfl rfl) rfl) 

noncomputable def Ns360p1283 := nat_lit 1815346745627266498166784 

noncomputable def Ns360p1284 := nat_lit 265552223128956385285966272943942554963892596782528204023304178041824250789191241566681921 

noncomputable def Ns360p1285 := nat_lit 50220182755425505861763140177981040652524091445392600071596391900529249809920318405441 

noncomputable def Ns360p1286 := nat_lit 796556229021358304846175292551471702810372742164693826869769341341671693867953884063234881 

noncomputable def Ns360p1287 := BSN.cos_dyadic_bound_f 51595257719 68719476736 3 2 33554432 10590333 Ns360p1284 Ns360p693 Ns360p1285 Ns360p1286 Ns360p696 Ns360p1285 24532874 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 51595257719) qz376 0 2 Ns360p1284 Ns360p693 Ns360p1285 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 51595257719) qz377 0 2 Ns360p1286 Ns360p696 Ns360p1285 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1288 := @Ns360p1277 5290000 (Ns360p1282 rfl) (Enclosure.sfrac_false_div 65303677 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 65303677) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns360p1283) qz366) 226375608064910080 72057594037927936 Bool.false 24532874 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q2 65303677 16777216 226375608064910080 72057594037927936 0 Ns360p1283 Ns360p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 24532874 33554432 Ns360p1283 Ns360p112 51595257719 68719476736 10590333 10580000 (Ns360p1287 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p1289 := @Enclosure.Real.IsNear.inv_image qz200 12266437 16777216 36425451 5546967040000 22946553 22946966 16777216 (@Enclosure.Real.IsNear.neg qz198 Bool.true 12266437 16777216 36425451 5546967040000 (Ns360p1276 (Ns360p1288 rfl rfl) rfl)) 

noncomputable def Ns360p1290 := Ns360p1274 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz200) Bool.false 45893519 33554432 413 33554432 (@Ns360p1275 413 33554432 (Ns360p1289 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p1291 := @Enclosure.Real.IsNear.recentre' qz199 Bool.true 5005763 16777216 

noncomputable abbrev qz202 := (@HMul.hMul Real Real Real qz349 qz346 qz505)

noncomputable def Ns360p1292 := @Enclosure.Real.IsNear.cos_image qz202 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 62873533)) qz378) Bool.true 62873533 33554432 

noncomputable def Ns360p1293 := nat_lit 74227966967666096594847845525 

noncomputable def Ns360p1294 := nat_lit 17233001815799669041773254862183681 

noncomputable def Ns360p1295 := @Enclosure.Real.IsNear.recentre' qz202 Bool.true Ns360p1293 Ns360p317 Ns360p1294 

noncomputable abbrev qz203 := qz505

noncomputable def Ns360p1296 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz203 884279719003555 140737488355328 1 500000000000000 83941727230055 

noncomputable abbrev qz506 := (@HSub.hSub Real Real Real qz587 qz695 qz688)

noncomputable abbrev qz204 := qz506

noncomputable def Ns360p1297 := @Enclosure.Real.IsNear.subLit_tf qz204 qz31 66349541185639 281474976710656 638588663 281474976710656 1 16 

noncomputable abbrev qz507 := qz695

noncomputable abbrev qz205 := qz507

noncomputable def Ns360p1298 := @Enclosure.Real.IsNear.subLit_ff_n qz205 qz190 108022825920409 281474976710656 353375991 281474976710656 10393403 16777216 17 16777216 

noncomputable def Ns360p1299 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz190 10393403 16777216 17 16777216 10393403 16777216 17 16777216 108022825920409 281474976710656 

noncomputable def Ns360p1300 := nat_lit 504864350113979841483693407094122460442704189930287544559038457976854832390460304831186444711603441 

noncomputable def Ns360p1301 := nat_lit 3816052841342360011863190158749412209139770338685385458533685615756083263827603361699973278961 

noncomputable def Ns360p1302 := nat_lit 3047950731018748574111451989388572473983167136030211402592856767060415961500668781167129576216177905 

noncomputable def Ns360p1303 := BSN.cos_dyadic_bound_t 62873533 33554432 4 3 16777216 5290000 Ns360p1300 Ns360p204 Ns360p1301 Ns360p1302 Ns360p207 Ns360p1301 5005763 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 62873533) qz601 0 3 Ns360p1300 Ns360p204 Ns360p1301 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 62873533) (BSN.cosOddQ 33554432) 0 3 Ns360p1302 Ns360p207 Ns360p1301 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1304 := @Ns360p1291 2567464432 177502945280000 5005763 16777216 160466527 11093934080000 (@Ns360p1292 479 33554432 Bool.true 5005763 16777216 1 5290000 (@Ns360p1295 Ns360p198 62873533 33554432 479 33554432 (@Ns360p1296 281474976710656 638588663 281474976710656 Ns360p1293 Ns360p317 Ns360p1294 Ns360p198 RS361to372.d47 (@Ns360p1297 0 1 1343067635680880 83941727230055 281474976710656 638588663 281474976710656 (@Ns360p1298 1113160583972361601024 66349541185639 281474976710656 638588663 281474976710656 (@Ns360p1299 353375991 281474976710656 (Ns360p1281 rfl rfl) (Ns360p1281 rfl rfl) rfl) (Ns360p1281 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 62873533 33554432) (BSN.cos_neg_of_bound 62873533 33554432 Bool.true 5005763 16777216 1 5290000 (Ns360p1303 rfl rfl)) rfl rfl) 

noncomputable def Ns360p1305 := @Ns360p1266 902094050571594456163 Ns360p1190 (Ns360p1267 qz33 (@Enclosure.Real.IsNear.of_eq qz693 (@Inv.inv Real Real.instInv (Real.sqrt qz197)) Bool.false 5148349 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz189 (BSN.t_div_two_pi_nonneg qz188 708578 1000 qz191)) Ns360p1271) rfl) (@Ns360p1272 562949953421312 4365747491051457 186125328349921280000 (BSN.correction_mk qz190 (BSN.cos_two_pi_p_ne_zero_mk qz188 708578 1000 10 qz191 rfl rfl (@BSN.floor_sqrt_eq_dec qz188 708578 1000 10 qz191 rfl rfl rfl))) (@Ns360p1273 33554432 5005763 16777216 160466527 11093934080000 229732079349997 562949953421312 4365747491051457 186125328349921280000 Ns360p1290 (Ns360p1304 rfl) rfl)) 

noncomputable def Ns360p1306 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz188) (hardyZApproximantRS₀ qz188) Bool.false 11822530310324555672327 9444732965739290427392 149400326021272788491363 Ns360p1190 (@Eq.refl Real (hardyZApproximantRS₀ qz188)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz188) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 10) (@HMul.hMul Real Real Real qz5 qz689 (Zeta.RiemannSiegel.correction qz190))) Bool.false 11822530310324555672327 9444732965739290427392 149400326021272788491363 Ns360p1190 (BSN.hardyZApproximantRS₀_eq qz188 10 (@BSN.floor_sqrt_eq_dec qz188 708578 1000 10 qz191 rfl rfl rfl)) (@Ns360p1192 11822530310324555672327 9444732965739290427392 149400326021272788491363 Ns360p1190 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 10)) Bool.false 46204005 33554432 9973 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz188) qz188 10) (Ns360p1265 (Ns360p1264 rfl rfl rfl rfl) rfl rfl)) (Ns360p1305 rfl) rfl rfl)) 

theorem RS361to372.d60 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz188) Bool.false 11822530310324555672327 9444732965739290427392 149400326021272788491363 Ns360p1190 := Ns360p1306 

noncomputable def Ns360p1307 := nat_lit 228960457617122760728428675072 

noncomputable abbrev qz782 := (Enclosure.sfrac Bool.false 709907 1000)

noncomputable abbrev qz696 := qz782

noncomputable abbrev qz508 := qz696

noncomputable abbrev qz206 := qz508

noncomputable abbrev qz783 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 709907 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz697 := qz783

noncomputable abbrev qz509 := qz697

noncomputable abbrev qz207 := qz509

noncomputable abbrev qz784 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 709907 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz698 := qz784

noncomputable abbrev qz510 := qz698

noncomputable abbrev qz208 := qz510

noncomputable abbrev qz699 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz207 qz9))

noncomputable def Ns360p1308 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 10) (@HMul.hMul Real Real Real qz5 qz699 (Zeta.RiemannSiegel.correction qz208)) 92722289 33554432 159873 134217728 298802337731312641875 2361183241434822606848 6222947502598822346521 Ns360p363 Ns360p1307 

noncomputable def Ns360p1309 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos BSN.quadSignNeg 9 10 709907 1000 198 268435456 134217728 4503599627370496 Bool.false 355035476427 2560 618095470 52 84886744 8 

noncomputable def Ns360p1310 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 709907 1000 97 151 268435456 134217728 4503599627370496 Bool.false 355035476427 2560 

noncomputable def Ns360p1311 := Ns360p1310 558195838 52 94906264 8 589812974 52 89478488 8 Bool.true 237223208 120244 Bool.true 330885798 Bool.true 6610838 14148475504056880 1 Bool.false 253233896 Bool.true Bool.false 6610169 Bool.false Bool.true 324551520 

noncomputable def Ns360p1312 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 709907 1000 32 37 268435456 134217728 4503599627370496 Bool.false 355035476427 2560 

noncomputable def Ns360p1313 := Ns360p1312 480971758 52 109588312 8 522351262 52 101459064 8 Bool.true 275471573 89188 Bool.false 97220915 Bool.true 184016079 14148475504056880 1 Bool.false 251021514 Bool.false Bool.false 169938554 Bool.true Bool.true 237223208 

noncomputable def Ns360p1314 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 709907 1000 215 114 268435456 134217728 4503599627370496 Bool.false 355035476427 2560 

noncomputable def Ns360p1315 := Ns360p1314 372130544 51 134217720 8 432030192 51 120047984 16 Bool.true 300810693 52441 Bool.false 201051250 Bool.false 265272092 14148475504056880 1 Bool.false 182774450 Bool.false Bool.false 147688042 Bool.true Bool.true 275471573 

noncomputable def Ns360p1316 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 709907 1000 528 345 268435456 134217728 4503599627370496 Bool.false 355035476427 2560 

noncomputable def Ns360p1317 := Ns360p1316 186065264 51 189812528 16 294906480 51 154981288 8 Bool.true 268435440 2619 Bool.false 311320931 Bool.false 207489177 14148475504056880 1 Bool.false 107255742 Bool.false Bool.false 187436494 Bool.true Bool.true 300810693 

noncomputable def Ns360p1318 := nat_lit 1715471720238885102899508275583825745090395612272909736809 

noncomputable def Ns360p1319 := nat_lit 1297034983970270491233014978701403917396170541891584000 

noncomputable def Ns360p1320 := nat_lit 86546413594989664348918671827360000 

noncomputable def Ns360p1321 := nat_lit 368639514354717474371061308233209933120 

noncomputable abbrev qz785 := (@Eq.refl Real (Enclosure.sfrac Bool.false 709907 1000))

noncomputable abbrev qz700 := qz785

noncomputable abbrev qz511 := qz700

noncomputable abbrev qz209 := qz511

noncomputable def Ns360p1322 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz206 709907 1000 2015872794596 16000000 1419814 4000 2000 Ns360p1320 Ns360p1321 qz209 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns360p1323 := nat_lit 548950950476443232927842648186824238428926595927331115778880 

noncomputable abbrev qz701 := (@HSub.hSub Real Real Real qz741 qz742 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz743 (@Nat.cast Real Real.instNatCast 1419814))))

noncomputable abbrev qz512 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 709907 4000) (Real.log (Enclosure.sfrac Bool.false 2015872794596 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz701))

noncomputable abbrev qz702 := (Enclosure.sfrac Bool.false 709907 2000)

noncomputable abbrev qz210 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz512 qz702) (@HMul.hMul Real Real Real qz349 qz702 (Real.log Real.pi)))

noncomputable def Ns360p1324 := @Enclosure.Real.IsNear.addLit_ft_p qz210 (Enclosure.sfrac Bool.true Ns360p1320 Ns360p1321) 1489126983253409113849 1125899906842624000 20649811547809098727 Ns360p88 Ns360p1320 Ns360p1321 0 1 Ns360p1323 

noncomputable def Ns360p1325 := nat_lit 99933620197883309757653057536000 

noncomputable abbrev qz211 := (@HSub.hSub Real Real Real qz353 qz512 qz702)

noncomputable def Ns360p1326 := @Enclosure.Real.IsNear.subLit_ff_p qz211 (@HMul.hMul Real Real Real qz5 qz702 (Real.log Real.pi)) 1946609251824622085881 1125899906842624000 2243460877229337 529000000000000000000 27268068109227 67108864000 709907 134217728000 Ns360p1325 1489126983253409113849 1125899906842624000 

noncomputable abbrev qz212 := qz512

noncomputable def Ns360p1327 := @Enclosure.Real.IsNear.subLit_ff_p qz212 qz702 469250272881617084773 225179981368524800 2243460877229337 529000000000000000000 709907 2000 0 1 778643700729848834352400 1946609251824622085881 1125899906842624000 2243460877229337 529000000000000000000 

noncomputable def Ns360p1328 := nat_lit 1056657677046577133621028891555528704 

noncomputable def Ns360p1329 := nat_lit 56790373968040277447802880 

noncomputable def Ns360p1330 := nat_lit 2084231373226831326590393874323286009421087208164111657833034125865931138254907346735195741954504809564108431683120214023076123665458162181395786971691313765062602225017429349792740107740707785360785853644800 

noncomputable def Ns360p1331 := nat_lit 73678751083018043993053467920585588699160189202620876533720572831003092474064451081842808472706594453357215485319524686525933951016884715847456323684943168707913578189057410372811403720365102932463745761280 

noncomputable def Ns360p1332 := nat_lit 1190734900410946340953707299198563219003111206316378127993696571767832634021069399106077476567269789292982403231264394293332500461196950078815464338884901561102776592554554374570680426537140250214400 

noncomputable def Ns360p1333 := BSN.log_dyadic_bound 967296794596 3064448794596 9 8 Ns360p1330 134217728 42320000 Ns360p1331 Ns360p1332 87727283 4031745589192 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 967296794596) (BSN.artanhQ 3064448794596) 0 8 Ns360p1331 Ns360p1330 Ns360p1332 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz513 := (Real.log (Enclosure.sfrac Bool.false 2015872794596 16000000))

noncomputable def Ns360p1334 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 709907 4000) qz513 709907 4000 0 1 3305634831080695 281474976710656 781250529 33062500000000000 469338661205600589073 225179981368524800 554615219290803 132250000000000000000 (Enclosure.Real.IsNear.const Bool.false 709907 4000) (BSN.isNear_log_sfrac 2015872794596 16000000 3305634831080695 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2015872794596) qz356)) Bool.false Ns360p1329 Ns360p100 1000000677120000 42320000000000000000000 3305634831080695 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 2015872794596 16000000 16 4031745589192 2097152000000 87727283 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns360p1333 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p1335 := BSN.arctan_dyadic_bound_f 1000 1419814 1 0 16777216 5290000 0 1 1 0 1 1 11816 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1419814) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1419814) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns360p1336 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1419814))) 884279719003555 562949953421312 1 2000000000000000 11816 16777216 1 5290000 14829100033492320780288 883883239835043 562949953421312 200000000529 1058000000000000000 qz17 (Ns360p1335 rfl) rfl rfl 

noncomputable abbrev qz514 := (@HMul.hMul Real Real Real qz583 qz588 qz701)

noncomputable abbrev qz213 := qz514

noncomputable abbrev qz515 := qz701

noncomputable abbrev qz214 := qz515

noncomputable def Ns360p1337 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 709907 4000) qz513) qz213 469338661205600589073 225179981368524800 554615219290803 132250000000000000000 883883239835043 2251799813685248 200000000529 4232000000000000000 Ns360p1328 469250272881617084773 225179981368524800 2243460877229337 529000000000000000000 (Ns360p1334 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz214 1 4 0 1 883883239835043 562949953421312 200000000529 1058000000000000000 883883239835043 2251799813685248 200000000529 4232000000000000000 qz363 Ns360p1336 rfl) 

noncomputable def Ns360p1338 := @Ns360p1324 Ns360p1318 Ns360p1319 20649811547809098727 Ns360p88 (@Ns360p1326 20649811547809098727 Ns360p88 (Ns360p1327 (Ns360p1337 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 709907 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz702 (Real.log Real.pi) 709907 2000 0 1 38410761 33554432 1 67108864 27268068109227 67108864000 709907 134217728000 (Enclosure.Real.IsNear.const Bool.false 709907 2000) RS361to372.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns360p1320 Ns360p1321) 

noncomputable def Ns360p1339 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz206) Bool.false Ns360p1318 Ns360p1319 20649811547809098727 Ns360p88 44379434553 33554432 321 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz206) (@HAdd.hAdd Real Real Real qz364 qz210 (Enclosure.sfrac Bool.true Ns360p1320 Ns360p1321)) Bool.false Ns360p1318 Ns360p1319 20649811547809098727 Ns360p88 Ns360p1322 (Ns360p1338 rfl rfl)) 

noncomputable def Ns360p1340 := nat_lit 7594496649410427020640256 

noncomputable def Ns360p1341 := nat_lit 3508227312631890784003480761035710408271398165697313528286280415427628945418809175093151845679650787268204056581987974944200197615576700961 

noncomputable def Ns360p1342 := nat_lit 2497067783238956961079775672997989900906508048383902346223997321179160174424593868172915943521179522953813191865244479576397453744161 

noncomputable def Ns360p1343 := nat_lit 17519355671761635312547557707425968365534177996615514873125180281807568057967295740497708156886632007720459699855280957663016363485184677921 

noncomputable def Ns360p1344 := BSN.sin_dyadic_bound_f 107924288519 68719476736 4 3 33554432 10590333 Ns360p1341 Ns360p114 Ns360p1342 Ns360p1343 Ns360p117 Ns360p1342 33554430 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107924288519) qz594 0 3 Ns360p1341 Ns360p114 Ns360p1342 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107924288519) qz595 0 3 Ns360p1343 Ns360p117 Ns360p1342 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1345 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz206) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44379434553) qz378) Bool.false 44379434553 33554432 321 33554432 Bool.true 33554430 33554432 1 5290000 (Ns360p1339 rfl) (Enclosure.sfrac_false_div 44379434553 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44379434553) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns360p1340) qz391) 226375608064910080 72057594037927936 Bool.false 33554430 33554432 210 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q1 44379434553 33554432 226375608064910080 72057594037927936 210 Ns360p1340 Ns360p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554430 33554432 Ns360p1340 Ns360p100 107924288519 68719476736 10590333 10580000 (Ns360p1344 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p1346 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz206) Bool.false Ns360p1318 Ns360p1319 20649811547809098727 Ns360p88 355035476427 268435456 2560 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz206) (@HAdd.hAdd Real Real Real qz364 qz210 (Enclosure.sfrac Bool.true Ns360p1320 Ns360p1321)) Bool.false Ns360p1318 Ns360p1319 20649811547809098727 Ns360p88 Ns360p1322 (Ns360p1338 rfl rfl)) 

noncomputable def Ns360p1347 := Ns360p1317 52441 BSN.abs_quadSignPos (BSN.cos_quad_nat0 528 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 107255742 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 345 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 187436494 268435456) qz209 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 1) Bool.true 16777215 16777216 108227777 11093934080000 268435440 268435456 2619 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz206)) Bool.true 16777215 16777216 108227777 11093934080000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz206) qz206) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz206)) Bool.true 33554430 33554432 1731644432 177502945280000 16777215 16777216 108227777 11093934080000 (Ns360p1345 rfl rfl) rfl)) rfl) (Ns360p1346 rfl) RS361to372.d7 

noncomputable def Ns360p1348 := nat_lit 5059941930031484823430042693072237538033349549203046576253478572118659396003587554541783117044413121095094641 

noncomputable def Ns360p1349 := nat_lit 828895623012611889889551067128513216811429943663792610288856945078609850204141144979647424974921224561 

noncomputable def Ns360p1350 := nat_lit 30674962719211738129267467305463825606275346583565931535917712213378107732950828150641126126708042358299119985 

noncomputable def Ns360p1351 := BSN.cos_dyadic_bound_f 311320931 268435456 4 3 268435456 134217728 Ns360p1348 Ns360p129 Ns360p1349 Ns360p1350 Ns360p132 Ns360p1349 107255742 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 311320931) qz367 0 3 Ns360p1348 Ns360p129 Ns360p1349 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 311320931) qz368 0 3 Ns360p1350 Ns360p132 Ns360p1349 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1352 := nat_lit 29105452520980340074731691047089126738023236757784788349876194544145345 

noncomputable def Ns360p1353 := nat_lit 3435291419305116058576010501009185951816175374668349266091908486081 

noncomputable def Ns360p1354 := nat_lit 76223004225983920484011972534898459917567441510258315969911598811403201 

noncomputable def Ns360p1355 := BSN.sin_dyadic_bound_f 207489177 268435456 3 2 268435456 134217728 Ns360p1352 Ns360p144 Ns360p1353 Ns360p1354 Ns360p147 Ns360p1353 187436494 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 207489177) qz369 0 2 Ns360p1352 Ns360p144 Ns360p1353 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 207489177) qz370 0 2 Ns360p1354 Ns360p147 Ns360p1353 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1356 := nat_lit 25657456550013192987830743533661413236870785507627827930039062500000000 

noncomputable def Ns360p1357 := nat_lit 2669649342979063146072149774362143304750448465347290039062500000000 

noncomputable def Ns360p1358 := nat_lit 67193778198717348865891640059954734055025318460557558490039062500000000 

noncomputable def Ns360p1359 := BSN.sin_dyadic_bound_f 201051250 268435456 3 2 268435456 134217728 Ns360p1356 Ns360p144 Ns360p1357 Ns360p1358 Ns360p147 Ns360p1357 182774450 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 201051250) qz369 0 2 Ns360p1356 Ns360p144 Ns360p1357 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 201051250) qz370 0 2 Ns360p1358 Ns360p147 Ns360p1357 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1360 := nat_lit 43219676550137603623864039949560620977955909071174218322634019921002496 

noncomputable def Ns360p1361 := nat_lit 24520679384156531502215834166811306191412204549989003222853437423616 

noncomputable def Ns360p1362 := nat_lit 129609988291644497808587688180348240321484902804422676961456352888160256 

noncomputable def Ns360p1363 := BSN.cos_dyadic_bound_f 265272092 268435456 3 2 268435456 134217728 Ns360p1360 Ns360p123 Ns360p1361 Ns360p1362 Ns360p126 Ns360p1361 147688042 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 265272092) qz367 0 2 Ns360p1360 Ns360p123 Ns360p1361 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 265272092) qz368 0 2 Ns360p1362 Ns360p126 Ns360p1361 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1364 := Ns360p1315 89188 BSN.abs_quadSignPos (BSN.cos_quad_nat3 215 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 182774450 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 114 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 147688042 268435456) qz209 rfl rfl (Ns360p1347 RS361to372.d9 RS361to372.d11 RS361to372.d13 RS361to372.d17 (Ns360p1351 rfl rfl) (Ns360p1355 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns360p1346 rfl) RS361to372.d19 RS361to372.d21 RS361to372.d23 RS361to372.d25 RS361to372.d17 (Ns360p1359 rfl rfl) (Ns360p1363 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns360p1365 := nat_lit 779313250533631261823721223105414751959545664832531024764262822190625 

noncomputable def Ns360p1366 := nat_lit 7981373471086664761059436547742526702811784088057589009625390625 

noncomputable def Ns360p1367 := nat_lit 2337923788853951612141641550443148770825231370929416959114769215790625 

noncomputable def Ns360p1368 := BSN.cos_dyadic_bound_f 97220915 268435456 3 2 268435456 134217728 Ns360p1365 Ns360p123 Ns360p1366 Ns360p1367 Ns360p126 Ns360p1366 251021514 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 97220915) qz367 0 2 Ns360p1365 Ns360p123 Ns360p1366 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 97220915) qz368 0 2 Ns360p1367 Ns360p126 Ns360p1366 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1369 := nat_lit 18005123530489610285551861420696985067038267163686722438148418249037185 

noncomputable def Ns360p1370 := nat_lit 1314759084828837038583457560353466101603723289228823893427614258561 

noncomputable def Ns360p1371 := nat_lit 47154147255621161202192406694346769563792865114806474004085069752964481 

noncomputable def Ns360p1372 := BSN.sin_dyadic_bound_f 184016079 268435456 3 2 268435456 134217728 Ns360p1369 Ns360p144 Ns360p1370 Ns360p1371 Ns360p147 Ns360p1370 169938554 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 184016079) qz369 0 2 Ns360p1369 Ns360p144 Ns360p1370 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 184016079) qz370 0 2 Ns360p1371 Ns360p147 Ns360p1370 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1373 := Ns360p1313 120244 BSN.abs_quadSignPos (BSN.cos_quad_nat0 32 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 251021514 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 37 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 169938554 268435456) qz209 rfl rfl (Ns360p1364 rfl rfl) (Ns360p1346 rfl) RS361to372.d27 RS361to372.d29 RS361to372.d31 RS361to372.d33 RS361to372.d17 (Ns360p1368 rfl rfl) (Ns360p1372 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p1374 := nat_lit 16782709632751935957378634190890575048846788165763520304006728720798961679667784306777432606604203542726250496 

noncomputable def Ns360p1375 := nat_lit 1722413916113040570989275361809458208107588982982787289069972834108915271365635040086316673113068343296 

noncomputable def Ns360p1376 := nat_lit 83873969269869164898698987852548407747615228069215141870679085739237907659628318960342292941412504223379296256 

noncomputable def Ns360p1377 := BSN.sin_dyadic_bound_f 330885798 268435456 4 3 268435456 134217728 Ns360p1374 Ns360p258 Ns360p1375 Ns360p1376 Ns360p261 Ns360p1375 253233896 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 330885798) qz369 0 3 Ns360p1374 Ns360p258 Ns360p1375 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 330885798) qz370 0 3 Ns360p1376 Ns360p261 Ns360p1375 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1378 := BSN.sin_dyadic_bound_f 6610838 268435456 1 0 268435456 134217728 0 1 1 0 1 1 6610169 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 6610838) qz369 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 6610838) qz370 0 0 rfl) rfl rfl 

noncomputable def Ns360p1379 := Ns360p1311 147379 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 97 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 253233896 268435456) BSN.abs_quadSignPos qz631 (BSN.sfrac_eq_quadSignPos_mul Bool.false 6610169 268435456) qz209 rfl rfl (Ns360p1373 rfl) (Ns360p1346 rfl) RS361to372.d35 RS361to372.d37 RS361to372.d39 RS361to372.d41 RS361to372.d17 (Ns360p1377 rfl rfl) (Ns360p1378 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p1380 := nat_lit 2721987944093624709467995482876444160302878086345293751949267878848038533376087053662286684536138626941668721 

noncomputable def Ns360p1381 := nat_lit 129231789228666474028933396277753130366782710690719963670223213985255962127114916923773957183889821041 

noncomputable def Ns360p1382 := nat_lit 16507015902333142803899847079233022549292651752648341009939672578427092630071857894596403155810144900346367345 

noncomputable def Ns360p1383 := BSN.cos_dyadic_bound_f 266653597 268435456 4 3 268435456 134217728 Ns360p1380 Ns360p129 Ns360p1381 Ns360p1382 Ns360p132 Ns360p1381 146532472 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 266653597) qz367 0 3 Ns360p1380 Ns360p129 Ns360p1381 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 266653597) qz368 0 3 Ns360p1382 Ns360p132 Ns360p1381 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1384 := Ns360p1309 Bool.true 324551520 147379 Bool.true 266653597 14148475504056880 1 Bool.false 146532472 Bool.true Bool.true 370889156 159873 BSN.abs_quadSignNeg qz632 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 146532472 268435456) qz209 rfl (Ns360p1379 rfl) (Ns360p1346 rfl) RS361to372.d43 RS361to372.d45 RS361to372.d17 (Ns360p1383 rfl rfl) rfl 

noncomputable def Ns360p1385 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 10) 370889156 268435456 159873 268435456 370889156 268435456 159873 268435456 199119599432630272 92722289 33554432 159873 134217728 (Ns360p1384 rfl rfl rfl rfl) 

noncomputable def Ns360p1386 := @Enclosure.Real.IsNear.mulLit_ff qz699 (Zeta.RiemannSiegel.correction qz208) 10291875 33554432 1 33554432 29032837819281 70368744177664 301856946226073 11632833021870080000 298802337731312641875 2361183241434822606848 

noncomputable abbrev qz703 := (@HPow.hPow Real Real Real qz7 qz207 qz9)

noncomputable def Ns360p1387 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz703 1 1 0 1 10291875 33554432 1 33554432 10291875 33554432 1 33554432 

noncomputable def Ns360p1388 := @Enclosure.Real.IsNear.sqrt_image qz207 3791153977171 33554432000 709907 33554432000 178332550 178332585 16777216 (@Enclosure.Real.IsNear.of_eq qz207 (@HMul.hMul Real Real Real qz5 qz206 qz3) Bool.false 3791153977171 33554432000 709907 33554432000 (BSN.t_div_two_pi_mk qz206 709907 1000 qz209) (@Enclosure.Real.IsNear.mulLit_ff qz206 qz3 709907 1000 0 1 5340353 33554432 1 33554432 3791153977171 33554432000 709907 33554432000 (Enclosure.Real.IsNear.const Bool.false 709907 1000) RS361to372.d48 rfl)) 

noncomputable abbrev qz786 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 709907 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz704 := qz786

noncomputable abbrev qz516 := qz704

noncomputable abbrev qz215 := qz516

noncomputable def Ns360p1389 := @Enclosure.Real.IsNear.sqrt_image qz215 356665135 33554432 35 33554432 54698479 54698486 16777216 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 356665135 33554432 35 33554432 356665135 33554432 35 33554432 (Ns360p1388 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns360p1390 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz215) 109396965 33554432 7 33554432 5145937 5145938 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz215) Bool.false 109396965 33554432 7 33554432 109396965 33554432 7 33554432 (Ns360p1389 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns360p1391 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 10291875 33554432 1 33554432 10291875 33554432 1 33554432 (Ns360p1390 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz216 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz510))

noncomputable abbrev qz705 := (@HMul.hMul Real Real Real qz737 qz784 qz784)

noncomputable abbrev qz517 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz705 qz698) qz600)

noncomputable abbrev qz217 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz517))

noncomputable def Ns360p1392 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz208) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz216) qz217) Bool.false 29032837819281 

noncomputable def Ns360p1393 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz216) qz217 6104667 4194304 241 

noncomputable abbrev qz706 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz216))

noncomputable def Ns360p1394 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz216) (@Neg.neg Real Real.instNeg qz706) Bool.true 6104667 4194304 241 16777216 (BSN.inv_eq_neg_inv_neg qz216) 

noncomputable def Ns360p1395 := @Enclosure.Real.IsNear.recentre' qz706 Bool.false 48837336 33554432 482 33554432 6104667 4194304 

noncomputable def Ns360p1396 := @Enclosure.Real.IsNear.recentre' qz216 Bool.true 23054081 33554432 1202644432 177502945280000 23054081 33554432 75165277 11093934080000 

noncomputable abbrev qz218 := (@HMul.hMul Real Real Real qz349 qz346 qz510)

noncomputable def Ns360p1397 := @Enclosure.Real.IsNear.cos_image qz218 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 66352997) qz365) Bool.false 66352997 16777216 221 33554432 Bool.true 23054081 33554432 1 

noncomputable def Ns360p1398 := nat_lit 37780505579918720412425853 

noncomputable def Ns360p1399 := nat_lit 5764607523034234880000000000000 

noncomputable def Ns360p1400 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz208 884279719003555 140737488355328 1 500000000000000 21120815 33554432 35 33554432 18676708353326069497325 4722366482869645213696 Ns360p1398 

noncomputable def Ns360p1401 := @Enclosure.Real.IsNear.subLit_ff_p qz215 qz1 356665135 33554432 35 33554432 10 1 0 1 21120815 21120815 33554432 35 

noncomputable def Ns360p1402 := @Ns360p1401 33554432 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 356665135 33554432 35 33554432 356665135 33554432 35 33554432 (Ns360p1388 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns360p1403 := @Enclosure.Real.IsNear.recentre' qz218 Bool.false 18676708353326069497325 4722366482869645213696 Ns360p1398 Ns360p1399 66352997 16777216 221 33554432 (@Ns360p1400 Ns360p1399 RS361to372.d47 (Ns360p1402 rfl rfl) rfl) 

noncomputable def Ns360p1404 := nat_lit 1966569694779023581773824 

noncomputable def Ns360p1405 := nat_lit 365746287483269444472973787816446352872265826816535268090565613436573946114129331786775361 

noncomputable def Ns360p1406 := nat_lit 95252481674347484133943534655220746660129205141217917762064128076577547800062938217281 

noncomputable def Ns360p1407 := nat_lit 1097048357486459638450653476380028617123477222039323368436172712053568683246787869483891521 

noncomputable def Ns360p1408 := BSN.cos_dyadic_bound_f 55893272439 68719476736 3 2 33554432 10590333 Ns360p1405 Ns360p693 Ns360p1406 Ns360p1407 Ns360p696 Ns360p1406 23054081 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 55893272439) qz376 0 2 Ns360p1405 Ns360p693 Ns360p1406 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 55893272439) qz377 0 2 Ns360p1407 Ns360p696 Ns360p1406 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1409 := @Ns360p1397 5290000 (Ns360p1403 rfl) (Enclosure.sfrac_false_div 66352997 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 66352997) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns360p1404) qz366) 226375608064910080 72057594037927936 Bool.false 23054081 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q2 66352997 16777216 226375608064910080 72057594037927936 0 Ns360p1404 Ns360p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 23054081 33554432 Ns360p1404 Ns360p112 55893272439 68719476736 10590333 10580000 (Ns360p1408 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p1410 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz216) 23054081 33554432 75165277 11093934080000 24418427 24418909 16777216 (@Enclosure.Real.IsNear.neg qz216 Bool.true 23054081 33554432 75165277 11093934080000 (Ns360p1396 (Ns360p1409 rfl rfl) rfl)) 

noncomputable def Ns360p1411 := Ns360p1394 (@Enclosure.Real.IsNear.neg qz706 Bool.false 6104667 4194304 241 16777216 (@Ns360p1395 241 16777216 (Ns360p1410 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p1412 := @Enclosure.Real.IsNear.recentre' qz217 Bool.true 4755843 16777216 

noncomputable abbrev qz219 := (@HMul.hMul Real Real Real qz349 qz346 qz517)

noncomputable def Ns360p1413 := @Enclosure.Real.IsNear.cos_image qz219 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 3896943)) (@Nat.cast Real Real.instNatCast 2097152)) Bool.true 3896943 2097152 

noncomputable def Ns360p1414 := nat_lit 294444691814014793127089170045 

noncomputable def Ns360p1415 := nat_lit 158456325028528675187087900672 

noncomputable def Ns360p1416 := nat_lit 71590371630222849652790151900396213 

noncomputable def Ns360p1417 := @Enclosure.Real.IsNear.recentre' qz219 Bool.true Ns360p1414 Ns360p1415 Ns360p1416 

noncomputable def Ns360p1418 := nat_lit 4835703278458516698824704000000000000000 

noncomputable abbrev qz220 := qz517

noncomputable def Ns360p1419 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz220 884279719003555 140737488355328 1 500000000000000 332976868615519 

noncomputable abbrev qz518 := (@HSub.hSub Real Real Real qz587 qz705 qz698)

noncomputable abbrev qz221 := qz518

noncomputable def Ns360p1420 := @Enclosure.Real.IsNear.subLit_tf qz221 qz31 262608124437855 1125899906842624 2652863395 1125899906842624 1 16 

noncomputable abbrev qz519 := qz705

noncomputable abbrev qz222 := qz519

noncomputable def Ns360p1421 := @Enclosure.Real.IsNear.subLit_ff_n qz222 qz208 446088826264225 1125899906842624 1478458275 1125899906842624 21120815 33554432 35 33554432 

noncomputable def Ns360p1422 := @Enclosure.Real.IsNear.mulLit_ff qz208 qz208 21120815 33554432 35 33554432 21120815 33554432 35 33554432 446088826264225 1125899906842624 

noncomputable def Ns360p1423 := nat_lit 1734345143727376112798194747858752905244719744916909681252312751711206355754565260481 

noncomputable def Ns360p1424 := nat_lit 3466537250751077332112698720796095110148055492926080949987665366995300109908547993600 

noncomputable def Ns360p1425 := nat_lit 12265595599058921116427715914519325545367813937386297916685733311341514756216001 

noncomputable def Ns360p1426 := nat_lit 10472202094116132248530308096579289561291212442619056374212813794124341502197712049345 

noncomputable def Ns360p1427 := nat_lit 315454889818348037222255583592444655023473049856273366448877548396572310001677867417600 

noncomputable def Ns360p1428 := BSN.cos_dyadic_bound_t 3896943 2097152 4 3 16777216 5290000 Ns360p1423 Ns360p1424 Ns360p1425 Ns360p1426 Ns360p1427 Ns360p1425 4755843 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 3896943) (BSN.cosEvenQ 2097152) 0 3 Ns360p1423 Ns360p1424 Ns360p1425 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 3896943) (BSN.cosOddQ 2097152) 0 3 Ns360p1426 Ns360p1427 Ns360p1425 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1429 := @Ns360p1412 1333987216 88751472640000 4755843 16777216 83374201 5546967040000 (@Ns360p1413 249 16777216 Bool.true 4755843 16777216 1 5290000 (@Ns360p1417 Ns360p1418 3896943 2097152 249 16777216 (@Ns360p1419 1125899906842624 2652863395 1125899906842624 Ns360p1414 Ns360p1415 Ns360p1416 Ns360p1418 RS361to372.d47 (@Ns360p1420 0 1 5327629897848304 332976868615519 1125899906842624 2652863395 1125899906842624 (@Ns360p1421 8811666454097543823360 262608124437855 1125899906842624 2652863395 1125899906842624 (@Ns360p1422 1478458275 1125899906842624 (Ns360p1402 rfl rfl) (Ns360p1402 rfl rfl) rfl) (Ns360p1402 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 3896943 2097152) (BSN.cos_neg_of_bound 3896943 2097152 Bool.true 4755843 16777216 1 5290000 (Ns360p1428 rfl rfl)) rfl rfl) 

noncomputable def Ns360p1430 := @Ns360p1386 6222947502598822346521 Ns360p363 (Ns360p1387 qz33 (@Enclosure.Real.IsNear.of_eq qz703 (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 10291875 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz207 (BSN.t_div_two_pi_nonneg qz206 709907 1000 qz209)) Ns360p1391) rfl) (@Ns360p1392 70368744177664 301856946226073 11632833021870080000 (BSN.correction_mk qz208 (BSN.cos_two_pi_p_ne_zero_mk qz206 709907 1000 10 qz209 rfl rfl (@BSN.floor_sqrt_eq_dec qz206 709907 1000 10 qz209 rfl rfl rfl))) (@Ns360p1393 16777216 4755843 16777216 83374201 5546967040000 29032837819281 70368744177664 301856946226073 11632833021870080000 Ns360p1411 (Ns360p1429 rfl) rfl)) 

noncomputable def Ns360p1431 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz206) (hardyZApproximantRS₀ qz206) Bool.true 6823553371939741394771 2361183241434822606848 936110904355316472266521 Ns360p363 (@Eq.refl Real (hardyZApproximantRS₀ qz206)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz206) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 10) (@HMul.hMul Real Real Real qz5 qz699 (Zeta.RiemannSiegel.correction qz208))) Bool.true 6823553371939741394771 2361183241434822606848 936110904355316472266521 Ns360p363 (BSN.hardyZApproximantRS₀_eq qz206 10 (@BSN.floor_sqrt_eq_dec qz206 709907 1000 10 qz209 rfl rfl rfl)) (@Ns360p1308 6823553371939741394771 2361183241434822606848 936110904355316472266521 Ns360p363 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 10)) Bool.true 92722289 33554432 159873 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz206) qz206 10) (Ns360p1385 (Ns360p1384 rfl rfl rfl rfl) rfl rfl)) (Ns360p1430 rfl) rfl rfl)) 

theorem RS361to372.d61 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz206) Bool.true 6823553371939741394771 2361183241434822606848 936110904355316472266521 Ns360p363 := Ns360p1431 

noncomputable def Ns360p1432 := nat_lit 78066620919938822438912000 

noncomputable def Ns360p1433 := nat_lit 1106865423743739156406206464 

noncomputable abbrev qz787 := (Enclosure.sfrac Bool.false 711236 1000)

noncomputable abbrev qz707 := qz787

noncomputable abbrev qz520 := qz707

noncomputable abbrev qz223 := qz520

noncomputable abbrev qz788 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 711236 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz708 := qz788

noncomputable abbrev qz521 := qz708

noncomputable abbrev qz224 := qz521

noncomputable abbrev qz789 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 711236 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz709 := qz789

noncomputable abbrev qz522 := qz709

noncomputable abbrev qz225 := qz522

noncomputable abbrev qz710 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz224 qz9))

noncomputable def Ns360p1434 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (@HMul.hMul Real Real Real qz5 qz710 (Zeta.RiemannSiegel.correction qz225)) 11794849 33554432 160171 134217728 18887134295244607119 147573952589676412928 674196120124887263733 Ns360p1432 Ns360p1433 

noncomputable def Ns360p1435 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos BSN.quadSignNeg 9 10 711236 1000 198 268435456 134217728 4503599627370496 Bool.false 355878869581 2564 618095470 52 84886744 8 

noncomputable def Ns360p1436 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 711236 1000 97 150 268435456 134217728 4503599627370496 Bool.false 355878869581 2564 

noncomputable def Ns360p1437 := Ns360p1436 558195838 52 94906264 8 589812974 52 89478488 8 Bool.false 188268665 120469 Bool.true 229334912 Bool.true 368736554 14148475504056880 1 Bool.false 202437128 Bool.true Bool.false 52578732 Bool.true Bool.false 99170088 

noncomputable def Ns360p1438 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 711236 1000 32 37 268435456 134217728 4503599627370496 Bool.false 355878869581 2564 

noncomputable def Ns360p1439 := Ns360p1438 480971758 52 109588312 8 522351262 52 101459064 8 Bool.false 153927298 89356 Bool.false 301402603 Bool.true 34827752 14148475504056880 1 Bool.false 116272675 Bool.false Bool.false 34730122 Bool.true Bool.false 188268665 

noncomputable def Ns360p1440 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 711236 1000 216 115 268435456 134217728 4503599627370496 Bool.false 355878869581 2564 

noncomputable def Ns360p1441 := Ns360p1440 372130544 51 134217720 8 432030192 51 120047984 16 Bool.true 14257129 52541 Bool.false 128225483 Bool.false 112839693 14148475504056880 1 Bool.false 238388179 Bool.false Bool.false 109545744 Bool.false Bool.false 153927298 

noncomputable def Ns360p1442 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 711236 1000 530 346 268435456 134217728 4503599627370496 Bool.false 355878869581 2564 

noncomputable def Ns360p1443 := Ns360p1442 186065264 51 189812528 16 294906480 51 154981288 8 Bool.false 268435448 2627 Bool.false 64118493 Bool.false 237294191 14148475504056880 1 Bool.false 260814123 Bool.true Bool.false 170207145 Bool.true Bool.true 14257129 

noncomputable def Ns360p1444 := nat_lit 829197026983085890474788753214573242630192311436217 

noncomputable def Ns360p1445 := nat_lit 625454054954082825882922346414655397573951488000 

noncomputable def Ns360p1446 := nat_lit 87359559440413404352721677844480000 

noncomputable def Ns360p1447 := nat_lit 372799667688657537628962008008155463680 

noncomputable abbrev qz790 := (@Eq.refl Real (Enclosure.sfrac Bool.false 711236 1000))

noncomputable abbrev qz711 := qz790

noncomputable abbrev qz523 := qz711

noncomputable abbrev qz226 := qz523

noncomputable def Ns360p1448 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz223 711236 1000 2023427590784 16000000 1422472 4000 2000 Ns360p1446 Ns360p1447 qz226 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns360p1449 := nat_lit 8694761017658162706904920916907243524641965331565426769920 

noncomputable abbrev qz712 := (@HSub.hSub Real Real Real qz741 qz742 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz743 (@Nat.cast Real Real.instNatCast 1422472))))

noncomputable abbrev qz524 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 711236 4000) (Real.log (Enclosure.sfrac Bool.false 2023427590784 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz712))

noncomputable abbrev qz713 := (Enclosure.sfrac Bool.false 711236 2000)

noncomputable abbrev qz227 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz524 qz713) (@HMul.hMul Real Real Real qz349 qz713 (Real.log Real.pi)))

noncomputable def Ns360p1450 := @Enclosure.Real.IsNear.addLit_ft_p qz227 (Enclosure.sfrac Bool.true Ns360p1446 Ns360p1447) 23322881719318453269 17592186044416000 5172069466992575149 541696000000000000000000 Ns360p1446 Ns360p1447 0 1 Ns360p1449 

noncomputable def Ns360p1451 := nat_lit 391293024347457063279919104000 

noncomputable abbrev qz228 := (@HSub.hSub Real Real Real qz353 qz524 qz713)

noncomputable def Ns360p1452 := @Enclosure.Real.IsNear.subLit_ff_p qz228 (@HMul.hMul Real Real Real qz5 qz713 (Real.log Real.pi)) 30484424066800131093 17592186044416000 2247614005041501 529000000000000000000 6829779002649 16777216000 177809 33554432000 Ns360p1451 23322881719318453269 17592186044416000 

noncomputable abbrev qz229 := qz524

noncomputable def Ns360p1453 := @Enclosure.Real.IsNear.subLit_ff_p qz229 qz713 36740522083543260181 17592186044416000 2247614005041501 529000000000000000000 711236 2000 0 1 60968848133600262186000 30484424066800131093 17592186044416000 2247614005041501 529000000000000000000 

noncomputable def Ns360p1454 := nat_lit 1323716812518743246875039969688158208 

noncomputable def Ns360p1455 := nat_lit 56808462657929212535504896 

noncomputable def Ns360p1456 := nat_lit 2167981292365078491846801883501208750370642012811041723001743337212433440128940971938891334088503795182094947420791399017415024991488086411885437403112120858147967711381574694680997695120768280885912718540800 

noncomputable def Ns360p1457 := nat_lit 77512826841210597402194059333966891169527364557117889067211386789030683798312339599259710927018790659979034623692842625761750396087235654953556782589348565873819312473348783086901324410800178701471192186880 

noncomputable def Ns360p1458 := nat_lit 1348575236105874252319980338768011321960038258315768569043249151244039309689036924179728878188988927999046406722374760754032818084636068215534050795707933188872528253794725376159757320178811430502400 

noncomputable def Ns360p1459 := BSN.log_dyadic_bound 974851590784 3072003590784 9 8 Ns360p1456 134217728 42320000 Ns360p1457 Ns360p1458 88229345 4046855181568 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 974851590784) (BSN.artanhQ 3072003590784) 0 8 Ns360p1457 Ns360p1456 Ns360p1458 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz525 := (Real.log (Enclosure.sfrac Bool.false 2023427590784 16000000))

noncomputable def Ns360p1460 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 711236 4000) qz525 711236 4000 0 1 3306687731408119 281474976710656 781250529 33062500000000000 587958838833946231271 281474976710656000 138913375310961 33062500000000000000 (Enclosure.Real.IsNear.const Bool.false 711236 4000) (BSN.isNear_log_sfrac 2023427590784 16000000 3306687731408119 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2023427590784) qz356)) Bool.false Ns360p1455 Ns360p100 1000000677120000 42320000000000000000000 3306687731408119 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 2023427590784 16000000 16 4046855181568 2097152000000 88229345 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns360p1459 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p1461 := BSN.arctan_dyadic_bound_f 1000 1422472 1 0 16777216 5290000 0 1 1 0 1 1 11794 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1422472) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1422472) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns360p1462 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1422472))) 884279719003555 562949953421312 1 2000000000000000 11794 16777216 1 5290000 14829112418391296049152 883883978032547 562949953421312 200000000529 1058000000000000000 qz17 (Ns360p1461 rfl) rfl rfl 

noncomputable abbrev qz526 := (@HMul.hMul Real Real Real qz583 qz588 qz712)

noncomputable abbrev qz230 := qz526

noncomputable abbrev qz527 := qz712

noncomputable abbrev qz231 := qz527

noncomputable def Ns360p1463 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 711236 4000) qz525) qz230 587958838833946231271 281474976710656000 138913375310961 33062500000000000000 883883978032547 2251799813685248 200000000529 4232000000000000000 Ns360p1454 36740522083543260181 17592186044416000 2247614005041501 529000000000000000000 (Ns360p1460 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz231 1 4 0 1 883883978032547 562949953421312 200000000529 1058000000000000000 883883978032547 2251799813685248 200000000529 4232000000000000000 qz363 Ns360p1462 rfl) 

noncomputable def Ns360p1464 := @Ns360p1450 Ns360p1444 Ns360p1445 5172069466992575149 541696000000000000000000 (@Ns360p1452 5172069466992575149 541696000000000000000000 (Ns360p1453 (Ns360p1463 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 711236 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz713 (Real.log Real.pi) 711236 2000 0 1 38410761 33554432 1 67108864 6829779002649 16777216000 177809 33554432000 (Enclosure.Real.IsNear.const Bool.false 711236 2000) RS361to372.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns360p1446 Ns360p1447) 

noncomputable def Ns360p1465 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns360p1444 Ns360p1445 5172069466992575149 541696000000000000000000 44484858697 33554432 161 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz364 qz227 (Enclosure.sfrac Bool.true Ns360p1446 Ns360p1447)) Bool.false Ns360p1444 Ns360p1445 5172069466992575149 541696000000000000000000 Ns360p1448 (Ns360p1464 rfl rfl)) 

noncomputable def Ns360p1466 := BSN.cos_dyadic_bound_f 30523 68719476736 1 0 33554432 10590333 0 1 1 0 1 1 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 30523) qz376 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 30523) qz377 0 0 rfl) rfl rfl 

noncomputable def Ns360p1467 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz223) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44484858697) qz378) Bool.false 44484858697 33554432 161 16777216 Bool.false 33554431 33554432 1 5290000 (Ns360p1465 rfl) (Enclosure.sfrac_false_div 44484858697 33554432) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44484858697) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2147888508797190144) qz391) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 211 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q0 44484858697 33554432 226375608064910080 72057594037927936 211 2147888508797190144 Ns360p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554431 33554432 2147888508797190144 Ns360p100 30523 68719476736 10590333 10580000 (Ns360p1466 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p1468 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns360p1444 Ns360p1445 5172069466992575149 541696000000000000000000 355878869581 268435456 2564 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz364 qz227 (Enclosure.sfrac Bool.true Ns360p1446 Ns360p1447)) Bool.false Ns360p1444 Ns360p1445 5172069466992575149 541696000000000000000000 Ns360p1448 (Ns360p1464 rfl rfl)) 

noncomputable def Ns360p1469 := Ns360p1443 52541 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 530 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 260814123 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 346 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 170207145 268435456) qz226 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) Bool.false 33554431 33554432 54279201 5546967040000 268435448 268435456 2627 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 33554431 33554432 54279201 5546967040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz223) qz223) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 33554431 33554432 868467216 88751472640000 33554431 33554432 54279201 5546967040000 (Ns360p1467 rfl rfl) rfl)) rfl) (Ns360p1468 rfl) RS361to372.d7 

noncomputable def Ns360p1470 := nat_lit 16901810403640967744309450920401 

noncomputable def Ns360p1471 := BSN.cos_dyadic_bound_f 64118493 268435456 2 1 268435456 134217728 Ns360p1470 Ns360p155 Ns360p1470 Ns360p1470 Ns360p156 Ns360p1470 260814123 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 64118493) qz367 0 1 Ns360p1470 Ns360p155 Ns360p1470 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 64118493) qz368 0 1 Ns360p1470 Ns360p156 Ns360p1470 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1472 := nat_lit 27667826997406652977080970889878717265176326381506300804416841945270401 

noncomputable def Ns360p1473 := nat_lit 10053027116262018647636008592385268560844070209723897743839217928321 

noncomputable def Ns360p1474 := nat_lit 82983374937987434893947640652451381258407291004099454617762847399954561 

noncomputable def Ns360p1475 := BSN.cos_dyadic_bound_f 237294191 268435456 3 2 268435456 134217728 Ns360p1472 Ns360p123 Ns360p1473 Ns360p1474 Ns360p126 Ns360p1473 170207145 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 237294191) qz367 0 2 Ns360p1472 Ns360p123 Ns360p1473 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 237294191) qz368 0 2 Ns360p1474 Ns360p126 Ns360p1473 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1476 := nat_lit 2358194539772690617401446687338626822318775269525381008203869079252321 

noncomputable def Ns360p1477 := nat_lit 73079362325305229521100232894837107984589287459317548382040665441 

noncomputable def Ns360p1478 := nat_lit 7074437460593421241745297861550090792740356630001224389514843156426081 

noncomputable def Ns360p1479 := BSN.cos_dyadic_bound_f 128225483 268435456 3 2 268435456 134217728 Ns360p1476 Ns360p123 Ns360p1477 Ns360p1478 Ns360p126 Ns360p1477 238388179 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 128225483) qz367 0 2 Ns360p1476 Ns360p123 Ns360p1477 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 128225483) qz368 0 2 Ns360p1478 Ns360p126 Ns360p1477 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1480 := nat_lit 162124102033255020727765090394001 

noncomputable def Ns360p1481 := BSN.sin_dyadic_bound_f 112839693 268435456 2 1 268435456 134217728 Ns360p1480 Ns360p135 Ns360p1480 Ns360p1480 Ns360p136 Ns360p1480 109545744 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 112839693) qz369 0 1 Ns360p1480 Ns360p135 Ns360p1480 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 112839693) qz370 0 1 Ns360p1480 Ns360p136 Ns360p1480 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1482 := Ns360p1441 89356 BSN.abs_quadSignPos (BSN.cos_quad_nat0 216 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 238388179 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 115 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 109545744 268435456) qz226 rfl rfl (Ns360p1469 RS361to372.d9 RS361to372.d11 RS361to372.d13 RS361to372.d17 (Ns360p1471 rfl rfl) (Ns360p1475 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns360p1468 rfl) RS361to372.d19 RS361to372.d21 RS361to372.d23 RS361to372.d25 RS361to372.d17 (Ns360p1479 rfl rfl) (Ns360p1481 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns360p1483 := nat_lit 4444710465224375383566217012961505332552959372058235387306928304174108321201164059695219309405634425501141521 

noncomputable def Ns360p1484 := nat_lit 562035805875042273987153235131551134603192919015624187865859560116634121175347787922720139241378957841 

noncomputable def Ns360p1485 := nat_lit 26947583292436374459048862434098306415595387764034127541884707368429465232293281404120735982938469790233020945 

noncomputable def Ns360p1486 := BSN.cos_dyadic_bound_f 301402603 268435456 4 3 268435456 134217728 Ns360p1483 Ns360p129 Ns360p1484 Ns360p1485 Ns360p132 Ns360p1484 116272675 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 301402603) qz367 0 3 Ns360p1483 Ns360p129 Ns360p1484 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 301402603) qz368 0 3 Ns360p1485 Ns360p132 Ns360p1484 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1487 := nat_lit 1471301823306891499740977238016 

noncomputable def Ns360p1488 := BSN.sin_dyadic_bound_f 34827752 268435456 2 1 268435456 134217728 Ns360p1487 Ns360p135 Ns360p1487 Ns360p1487 Ns360p136 Ns360p1487 34730122 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 34827752) qz369 0 1 Ns360p1487 Ns360p135 Ns360p1487 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 34827752) qz370 0 1 Ns360p1487 Ns360p136 Ns360p1487 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1489 := Ns360p1439 120469 BSN.abs_quadSignPos (BSN.cos_quad_nat0 32 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 116272675 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 37 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 34730122 268435456) qz226 rfl rfl (Ns360p1482 rfl rfl) (Ns360p1468 rfl) RS361to372.d27 RS361to372.d29 RS361to372.d31 RS361to372.d33 RS361to372.d17 (Ns360p1486 rfl rfl) (Ns360p1488 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p1490 := nat_lit 43440868331078139627149434644461045776225196726811381666709479085834240 

noncomputable def Ns360p1491 := nat_lit 7651760788666978411168914636109314629348029321637061662271965495296 

noncomputable def Ns360p1492 := nat_lit 113761314206784904867963769635606180999761332713223349122500195375906816 

noncomputable def Ns360p1493 := BSN.sin_dyadic_bound_f 229334912 268435456 3 2 268435456 134217728 Ns360p1490 Ns360p144 Ns360p1491 Ns360p1492 Ns360p147 Ns360p1491 202437128 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 229334912) qz369 0 2 Ns360p1490 Ns360p144 Ns360p1491 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 229334912) qz370 0 2 Ns360p1492 Ns360p147 Ns360p1491 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1494 := nat_lit 9968486636984622229354343027771922731964303890399173392007422062265366619261956468578229415100887109325623296 

noncomputable def Ns360p1495 := nat_lit 6318213722117517135511037813808962986848040184828960258189944764423220086000472914604736664954925551616 

noncomputable def Ns360p1496 := nat_lit 60390189846944750891344860142428976067654079205253946147440617466185212555524559042584577417499714497951109120 

noncomputable def Ns360p1497 := BSN.cos_dyadic_bound_f 368736554 268435456 4 3 268435456 134217728 Ns360p1494 Ns360p129 Ns360p1495 Ns360p1496 Ns360p132 Ns360p1495 52578732 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 368736554) qz367 0 3 Ns360p1494 Ns360p129 Ns360p1495 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 368736554) qz368 0 3 Ns360p1496 Ns360p132 Ns360p1495 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1498 := Ns360p1437 147654 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 97 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 202437128 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 150 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 52578732 268435456) qz226 rfl rfl (Ns360p1489 rfl) (Ns360p1468 rfl) RS361to372.d35 RS361to372.d37 RS361to372.d39 RS361to372.d41 RS361to372.d17 (Ns360p1493 rfl rfl) (Ns360p1497 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p1499 := nat_lit 31293155208652725517565696435866261022466457306100782612911657891550561 

noncomputable def Ns360p1500 := nat_lit 12858909039782659096638431179628934846713237002171058689512376522081 

noncomputable def Ns360p1501 := nat_lit 93853747807878611234503812445239525197705945444298005721355948921607521 

noncomputable def Ns360p1502 := BSN.cos_dyadic_bound_f 244709323 268435456 3 2 268435456 134217728 Ns360p1499 Ns360p123 Ns360p1500 Ns360p1501 Ns360p126 Ns360p1500 164409004 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 244709323) qz367 0 2 Ns360p1499 Ns360p123 Ns360p1500 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 244709323) qz368 0 2 Ns360p1501 Ns360p126 Ns360p1500 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1503 := Ns360p1435 Bool.false 99170088 147654 Bool.true 244709323 14148475504056880 1 Bool.false 164409004 Bool.true Bool.false 47179396 160171 BSN.abs_quadSignNeg qz632 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 164409004 268435456) qz226 rfl (Ns360p1498 rfl) (Ns360p1468 rfl) RS361to372.d43 RS361to372.d45 RS361to372.d17 (Ns360p1502 rfl rfl) rfl 

noncomputable def Ns360p1504 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) 47179396 268435456 160171 268435456 47179396 268435456 160171 268435456 25329245358129152 11794849 33554432 160171 134217728 (Ns360p1503 rfl rfl rfl rfl) 

noncomputable def Ns360p1505 := @Enclosure.Real.IsNear.mulLit_ff qz710 (Zeta.RiemannSiegel.correction qz225) 1285883 4194304 1 16777216 14688065940093 35184372088832 130698806327151 4653133208748032000 18887134295244607119 147573952589676412928 

noncomputable abbrev qz714 := (@HPow.hPow Real Real Real qz7 qz224 qz9)

noncomputable def Ns360p1506 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz714 1 1 0 1 1285883 4194304 1 16777216 1285883 4194304 1 16777216 

noncomputable def Ns360p1507 := @Enclosure.Real.IsNear.sqrt_image qz224 949562826577 8388608000 177809 8388608000 178499398 178499433 16777216 (@Enclosure.Real.IsNear.of_eq qz224 (@HMul.hMul Real Real Real qz5 qz223 qz3) Bool.false 949562826577 8388608000 177809 8388608000 (BSN.t_div_two_pi_mk qz223 711236 1000 qz226) (@Enclosure.Real.IsNear.mulLit_ff qz223 qz3 711236 1000 0 1 5340353 33554432 1 33554432 949562826577 8388608000 177809 8388608000 (Enclosure.Real.IsNear.const Bool.false 711236 1000) RS361to372.d48 rfl)) 

noncomputable abbrev qz791 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 711236 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz715 := qz791

noncomputable abbrev qz528 := qz715

noncomputable abbrev qz232 := qz528

noncomputable def Ns360p1508 := @Enclosure.Real.IsNear.sqrt_image qz232 356998831 33554432 35 33554432 54724061 54724068 16777216 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 356998831 33554432 35 33554432 356998831 33554432 35 33554432 (Ns360p1507 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns360p1509 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz232) 109448129 33554432 7 33554432 5143531 5143533 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz232) Bool.false 109448129 33554432 7 33554432 109448129 33554432 7 33554432 (Ns360p1508 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns360p1510 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 10287064 33554432 2 33554432 1285883 4194304 1 16777216 (Ns360p1509 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz233 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz522))

noncomputable abbrev qz716 := (@HMul.hMul Real Real Real qz737 qz789 qz789)

noncomputable abbrev qz529 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz716 qz709) qz600)

noncomputable abbrev qz234 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz529))

noncomputable def Ns360p1511 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz225) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz233) qz234) Bool.false 14688065940093 

noncomputable def Ns360p1512 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz233) qz234 3274999 2097152 139 

noncomputable abbrev qz717 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz233))

noncomputable def Ns360p1513 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz233) (@Neg.neg Real Real.instNeg qz717) Bool.true 3274999 2097152 139 8388608 (BSN.inv_eq_neg_inv_neg qz233) 

noncomputable def Ns360p1514 := @Enclosure.Real.IsNear.recentre' qz717 Bool.false 52399984 33554432 556 33554432 3274999 2097152 

noncomputable def Ns360p1515 := @Enclosure.Real.IsNear.recentre' qz233 Bool.true 21486646 33554432 1202644432 177502945280000 10743323 16777216 75165277 11093934080000 

noncomputable abbrev qz235 := (@HMul.hMul Real Real Real qz349 qz346 qz522)

noncomputable def Ns360p1516 := @Enclosure.Real.IsNear.cos_image qz235 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 33700667) qz413) Bool.false 33700667 8388608 221 33554432 Bool.true 21486646 33554432 1 

noncomputable def Ns360p1517 := nat_lit 944512639500834437124258357 

noncomputable def Ns360p1518 := nat_lit 144115188075855872000000000000000 

noncomputable def Ns360p1519 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz225 884279719003555 140737488355328 1 500000000000000 21454511 33554432 35 33554432 18971788958438679786605 4722366482869645213696 Ns360p1517 

noncomputable def Ns360p1520 := @Enclosure.Real.IsNear.subLit_ff_p qz232 qz1 356998831 33554432 35 33554432 10 1 0 1 21454511 21454511 33554432 35 

noncomputable def Ns360p1521 := @Ns360p1520 33554432 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 356998831 33554432 35 33554432 356998831 33554432 35 33554432 (Ns360p1507 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns360p1522 := @Enclosure.Real.IsNear.recentre' qz235 Bool.false 18971788958438679786605 4722366482869645213696 Ns360p1517 Ns360p1518 33700667 8388608 221 33554432 (@Ns360p1519 Ns360p1518 RS361to372.d47 (Ns360p1521 rfl rfl) rfl) 

noncomputable def Ns360p1523 := nat_lit 491811930782002250394989321994853578375557750349934055112869587544326188320347453378132801 

noncomputable def Ns360p1524 := nat_lit 172201379897162234273484081958353208307815630415259347651829109748235678030788095245121 

noncomputable def Ns360p1525 := nat_lit 1475091389586212426716420997820644028710057619788971646643305104413482093604980783943908161 

noncomputable def Ns360p1526 := BSN.cos_dyadic_bound_f 60187260791 68719476736 3 2 33554432 10590333 Ns360p1523 Ns360p693 Ns360p1524 Ns360p1525 Ns360p696 Ns360p1524 21486646 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 60187260791) qz376 0 2 Ns360p1523 Ns360p693 Ns360p1524 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 60187260791) qz377 0 2 Ns360p1525 Ns360p696 Ns360p1524 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1527 := @Ns360p1516 5290000 (Ns360p1522 rfl) (Enclosure.sfrac_false_div 33700667 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 33700667) qz413) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1058825489350451049529344) qz414) 226375608064910080 72057594037927936 Bool.false 21486646 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q2 33700667 8388608 226375608064910080 72057594037927936 0 1058825489350451049529344 Ns360p459 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 21486646 33554432 1058825489350451049529344 Ns360p459 60187260791 68719476736 10590333 10580000 (Ns360p1526 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p1528 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz233) 10743323 16777216 75165277 11093934080000 26199714 26200270 16777216 (@Enclosure.Real.IsNear.neg qz233 Bool.true 10743323 16777216 75165277 11093934080000 (Ns360p1515 (Ns360p1527 rfl rfl) rfl)) 

noncomputable def Ns360p1529 := Ns360p1513 (@Enclosure.Real.IsNear.neg qz717 Bool.false 3274999 2097152 139 8388608 (@Ns360p1514 139 8388608 (Ns360p1528 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p1530 := @Enclosure.Real.IsNear.recentre' qz234 Bool.true 4484907 16777216 

noncomputable abbrev qz236 := (@HMul.hMul Real Real Real qz349 qz346 qz529)

noncomputable def Ns360p1531 := @Enclosure.Real.IsNear.cos_image qz236 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 61787411)) qz378) Bool.true 61787411 33554432 

noncomputable def Ns360p1532 := nat_lit 291782800953838077644184953725 

noncomputable def Ns360p1533 := nat_lit 14444146361915147449160072891088369 

noncomputable def Ns360p1534 := @Enclosure.Real.IsNear.recentre' qz236 Bool.true Ns360p1532 Ns360p1415 Ns360p1533 

noncomputable def Ns360p1535 := nat_lit 967140655691703339764940800000000000000 

noncomputable abbrev qz237 := qz529

noncomputable def Ns360p1536 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz237 884279719003555 140737488355328 1 500000000000000 329966632371295 

noncomputable abbrev qz530 := (@HSub.hSub Real Real Real qz587 qz716 qz709)

noncomputable abbrev qz238 := qz530

noncomputable def Ns360p1537 := @Enclosure.Real.IsNear.subLit_tf qz238 qz31 259597888193631 1125899906842624 2676222115 1125899906842624 1 16 

noncomputable abbrev qz531 := qz716

noncomputable abbrev qz239 := qz531

noncomputable def Ns360p1538 := @Enclosure.Real.IsNear.subLit_ff_n qz239 qz225 460296042249121 1125899906842624 1501816995 1125899906842624 21454511 33554432 35 33554432 

noncomputable def Ns360p1539 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz225 21454511 33554432 35 33554432 21454511 33554432 35 33554432 460296042249121 1125899906842624 

noncomputable def Ns360p1540 := nat_lit 470641004012409100524225893523253582601166917788618761759905064814609257496360300457344513304305201 

noncomputable def Ns360p1541 := nat_lit 3095993033798789804005930789883575554970754509369197252391383950658277416304886573686883753521 

noncomputable def Ns360p1542 := nat_lit 2842268174726212371301857917510392992922624868660410354308796492545475292099044435004327649383947825 

noncomputable def Ns360p1543 := BSN.cos_dyadic_bound_t 61787411 33554432 4 3 16777216 5290000 Ns360p1540 Ns360p204 Ns360p1541 Ns360p1542 Ns360p207 Ns360p1541 4484907 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 61787411) qz601 0 3 Ns360p1540 Ns360p204 Ns360p1541 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 61787411) (BSN.cosOddQ 33554432) 0 3 Ns360p1542 Ns360p207 Ns360p1541 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1544 := @Ns360p1530 1344567216 88751472640000 4484907 16777216 84035451 5546967040000 (@Ns360p1531 251 16777216 Bool.true 4484907 16777216 1 5290000 (@Ns360p1534 Ns360p1535 61787411 33554432 251 16777216 (@Ns360p1536 1125899906842624 2676222115 1125899906842624 Ns360p1532 Ns360p1415 Ns360p1533 Ns360p1535 RS361to372.d47 (@Ns360p1537 0 1 5279466117940720 329966632371295 1125899906842624 2676222115 1125899906842624 (@Ns360p1538 8710659686736794222592 259597888193631 1125899906842624 2676222115 1125899906842624 (@Ns360p1539 1501816995 1125899906842624 (Ns360p1521 rfl rfl) (Ns360p1521 rfl rfl) rfl) (Ns360p1521 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 61787411 33554432) (BSN.cos_neg_of_bound 61787411 33554432 Bool.true 4484907 16777216 1 5290000 (Ns360p1543 rfl rfl)) rfl rfl) 

noncomputable def Ns360p1545 := @Ns360p1505 674196120124887263733 Ns360p1432 (Ns360p1506 qz33 (@Enclosure.Real.IsNear.of_eq qz714 (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 1285883 4194304 1 16777216 (BSN.rpow_neg_quarter_mk qz224 (BSN.t_div_two_pi_nonneg qz223 711236 1000 qz226)) Ns360p1510) rfl) (@Ns360p1511 35184372088832 130698806327151 4653133208748032000 (BSN.correction_mk qz225 (BSN.cos_two_pi_p_ne_zero_mk qz223 711236 1000 10 qz226 rfl rfl (@BSN.floor_sqrt_eq_dec qz223 711236 1000 10 qz226 rfl rfl rfl))) (@Ns360p1512 8388608 4484907 16777216 84035451 5546967040000 14688065940093 35184372088832 130698806327151 4653133208748032000 Ns360p1529 (Ns360p1544 rfl) rfl)) 

noncomputable def Ns360p1546 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (hardyZApproximantRS₀ qz223) Bool.false 32987160198203896177 147573952589676412928 93836321017422516447733 Ns360p1432 (@Eq.refl Real (hardyZApproximantRS₀ qz223)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (@HMul.hMul Real Real Real qz5 qz710 (Zeta.RiemannSiegel.correction qz225))) Bool.false 32987160198203896177 147573952589676412928 93836321017422516447733 Ns360p1432 (BSN.hardyZApproximantRS₀_eq qz223 10 (@BSN.floor_sqrt_eq_dec qz223 711236 1000 10 qz226 rfl rfl rfl)) (@Ns360p1434 32987160198203896177 147573952589676412928 93836321017422516447733 Ns360p1432 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10)) Bool.false 11794849 33554432 160171 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (Ns360p1504 (Ns360p1503 rfl rfl rfl rfl) rfl rfl)) (Ns360p1545 rfl) rfl rfl)) 

theorem RS361to372.d62 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz223) Bool.false 32987160198203896177 147573952589676412928 93836321017422516447733 Ns360p1432 := Ns360p1546 

noncomputable def Ns360p1547 := nat_lit 31226648367975528975564800 

noncomputable def Ns360p1548 := nat_lit 109455461985247221499106951168 

noncomputable abbrev qz792 := (Enclosure.sfrac Bool.false 712564 1000)

noncomputable abbrev qz718 := qz792

noncomputable abbrev qz532 := qz718

noncomputable abbrev qz240 := qz532

noncomputable abbrev qz793 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 712564 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz719 := qz793

noncomputable abbrev qz533 := qz719

noncomputable abbrev qz241 := qz533

noncomputable abbrev qz794 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 712564 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz720 := qz794

noncomputable abbrev qz534 := qz720

noncomputable abbrev qz242 := qz534

noncomputable abbrev qz721 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz241 qz9))

noncomputable def Ns360p1549 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (@HMul.hMul Real Real Real qz5 qz721 (Zeta.RiemannSiegel.correction qz242)) 28969991 134217728 160465 134217728 305861269917559500725 2361183241434822606848 286423336617343455103 Ns360p1547 Ns360p1548 

noncomputable def Ns360p1550 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos BSN.quadSignNeg 9 10 712564 1000 198 268435456 134217728 4503599627370496 Bool.false 356721960697 2569 618095470 52 84886744 8 

noncomputable def Ns360p1551 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 712564 1000 97 150 268435456 134217728 4503599627370496 Bool.false 356721960697 2569 

noncomputable def Ns360p1552 := Ns360p1551 558195838 52 94906264 8 589812974 52 89478488 8 Bool.false 108296122 120689 Bool.true 127527869 Bool.true 308917068 14148475504056880 1 Bool.false 122784553 Bool.true Bool.false 109455051 Bool.true Bool.false 28400209 

noncomputable def Ns360p1553 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 712564 1000 33 36 268435456 134217728 4503599627370496 Bool.false 356721960697 2569 

noncomputable def Ns360p1554 := Ns360p1553 480971758 52 109588312 8 522351262 52 101459064 8 Bool.false 100068794 89518 Bool.false 84105796 Bool.true 307076541 14148475504056880 1 Bool.false 82736444 Bool.true Bool.false 111133037 Bool.false Bool.false 108296122 

noncomputable def Ns360p1555 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 712564 1000 217 115 268435456 134217728 4503599627370496 Bool.false 356721960697 2569 

noncomputable def Ns360p1556 := Ns360p1555 372130544 51 134217720 8 432030192 51 120047984 16 Bool.false 8853652 52634 Bool.false 55469808 Bool.false 382194714 14148475504056880 1 Bool.false 55075884 Bool.true Bool.false 265539968 Bool.false Bool.false 100068794 

noncomputable def Ns360p1557 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 712564 1000 531 347 268435456 134217728 4503599627370496 Bool.false 356721960697 2569 

noncomputable def Ns360p1558 := Ns360p1557 186065264 51 189812528 16 294906480 51 154981288 8 Bool.true 268435360 2627 Bool.false 238457510 Bool.false 267092073 14148475504056880 1 Bool.false 208310051 Bool.false Bool.false 225151988 Bool.false Bool.false 8853652 

noncomputable def Ns360p1559 := nat_lit 134482644044424400307257412540879162825402901359633 

noncomputable def Ns360p1560 := nat_lit 101199011710837384899290463376401703546996654080 

noncomputable def Ns360p1561 := nat_lit 88178187015873848590046532075520000 

noncomputable def Ns360p1562 := nat_lit 376995696540316138041356442035740999680 

noncomputable abbrev qz795 := (@Eq.refl Real (Enclosure.sfrac Bool.false 712564 1000))

noncomputable abbrev qz722 := qz795

noncomputable abbrev qz535 := qz722

noncomputable abbrev qz243 := qz535

noncomputable def Ns360p1563 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz240 712564 1000 2030990816384 16000000 1425128 4000 2000 Ns360p1561 Ns360p1562 qz243 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns360p1564 := nat_lit 1410152729615263599765827486124649090388096726960785326080 

noncomputable abbrev qz723 := (@HSub.hSub Real Real Real qz741 qz742 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz743 (@Nat.cast Real Real.instNatCast 1425128))))

noncomputable abbrev qz536 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 712564 4000) (Real.log (Enclosure.sfrac Bool.false 2030990816384 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz723))

noncomputable abbrev qz724 := (Enclosure.sfrac Bool.false 712564 2000)

noncomputable abbrev qz244 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz536 qz724) (@HMul.hMul Real Real Real qz349 qz724 (Real.log Real.pi)))

noncomputable def Ns360p1565 := @Enclosure.Real.IsNear.addLit_ft_p qz244 (Enclosure.sfrac Bool.true Ns360p1561 Ns360p1562) 3740501524966326481 2814749767106560 5181678811081001801 541696000000000000000000 Ns360p1561 Ns360p1562 0 1 Ns360p1564 

noncomputable def Ns360p1566 := nat_lit 1568880050817236302456422400000 

noncomputable abbrev qz245 := (@HSub.hSub Real Real Real qz353 qz536 qz724)

noncomputable def Ns360p1567 := @Enclosure.Real.IsNear.subLit_ff_p qz245 (@HMul.hMul Real Real Real qz5 qz724 (Real.log Real.pi)) 122212194841708647529 70368744177664000 2251764007851549 529000000000000000000 6842531375301 16777216000 178141 33554432000 Ns360p1566 3740501524966326481 2814749767106560 

noncomputable abbrev qz246 := qz536

noncomputable def Ns360p1568 := @Enclosure.Real.IsNear.subLit_ff_p qz246 qz724 147283311754815132777 70368744177664000 2251764007851549 529000000000000000000 712564 2000 0 1 244424389683417295058000 122212194841708647529 70368744177664000 2251764007851549 529000000000000000000 

noncomputable def Ns360p1569 := nat_lit 1326610135873756050600729323224694784 

noncomputable def Ns360p1570 := nat_lit 56826503969950067685588992 

noncomputable def Ns360p1571 := nat_lit 2254977053360755402095980718287251163665024619228242858576613143340480635098594269528692143745715433850847492155765394036884088055135639402607864056371559188530495553207330251199360177538446595151574650060800 

noncomputable def Ns360p1572 := nat_lit 81534385020586831675699534769485732523950307948505017389710982050522375953940730232756592765250233844142385592280804605789175723653123642194457778019672089501464250358599338023436061066475131051455681658880 

noncomputable def Ns360p1573 := nat_lit 1526080925875632044946016978662289473096707811048563268372374020790318719401482294618861230776785689503255443776263957877565719979870523764168113403378909010805772804936614408128337093147473897062400 

noncomputable def Ns360p1574 := BSN.log_dyadic_bound 982414816384 3079566816384 9 8 Ns360p1571 134217728 42320000 Ns360p1572 Ns360p1573 88730092 4061981632768 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 982414816384) (BSN.artanhQ 3079566816384) 0 8 Ns360p1572 Ns360p1571 Ns360p1573 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz537 := (Real.log (Enclosure.sfrac Bool.false 2030990816384 16000000))

noncomputable def Ns360p1575 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 712564 4000) qz537 712564 4000 0 1 3307737873980663 281474976710656 781250529 33062500000000000 589243732608789287483 281474976710656000 139172750486589 33062500000000000000 (Enclosure.Real.IsNear.const Bool.false 712564 4000) (BSN.isNear_log_sfrac 2030990816384 16000000 3307737873980663 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2030990816384) qz356)) Bool.false Ns360p1570 Ns360p100 1000000677120000 42320000000000000000000 3307737873980663 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 2030990816384 16000000 16 4061981632768 2097152000000 88730092 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns360p1574 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p1576 := BSN.arctan_dyadic_bound_f 1000 1425128 1 0 16777216 5290000 0 1 1 0 1 1 11772 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1425128) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1425128) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns360p1577 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1425128))) 884279719003555 562949953421312 1 2000000000000000 11772 16777216 1 5290000 14829124803290271318016 883884716230051 562949953421312 200000000529 1058000000000000000 qz17 (Ns360p1576 rfl) rfl rfl 

noncomputable abbrev qz538 := (@HMul.hMul Real Real Real qz583 qz588 qz723)

noncomputable abbrev qz247 := qz538

noncomputable abbrev qz539 := qz723

noncomputable abbrev qz248 := qz539

noncomputable def Ns360p1578 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 712564 4000) qz537) qz247 589243732608789287483 281474976710656000 139172750486589 33062500000000000000 883884716230051 2251799813685248 200000000529 4232000000000000000 Ns360p1569 147283311754815132777 70368744177664000 2251764007851549 529000000000000000000 (Ns360p1575 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz248 1 4 0 1 883884716230051 562949953421312 200000000529 1058000000000000000 883884716230051 2251799813685248 200000000529 4232000000000000000 qz363 Ns360p1577 rfl) 

noncomputable def Ns360p1579 := @Ns360p1565 Ns360p1559 Ns360p1560 5181678811081001801 541696000000000000000000 (@Ns360p1567 5181678811081001801 541696000000000000000000 (Ns360p1568 (Ns360p1578 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 712564 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz724 (Real.log Real.pi) 712564 2000 0 1 38410761 33554432 1 67108864 6842531375301 16777216000 178141 33554432000 (Enclosure.Real.IsNear.const Bool.false 712564 2000) RS361to372.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns360p1561 Ns360p1562) 

noncomputable def Ns360p1580 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns360p1559 Ns360p1560 5181678811081001801 541696000000000000000000 44590245087 33554432 161 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz364 qz244 (Enclosure.sfrac Bool.true Ns360p1561 Ns360p1562)) Bool.false Ns360p1559 Ns360p1560 5181678811081001801 541696000000000000000000 Ns360p1563 (Ns360p1579 rfl rfl)) 

noncomputable def Ns360p1581 := nat_lit 7591876616101328442097664 

noncomputable def Ns360p1582 := nat_lit 3503378881177961842801142531269134658584637462604027099283114648124883985222052198929766553316050732422177494540033309886897174920072754401 

noncomputable def Ns360p1583 := nat_lit 2486749783782124127506484006701486776393962217359755275173646223235408883227363259882511434909606312206337085904650545962332386456801 

noncomputable def Ns360p1584 := nat_lit 17495173569393132424996568275276370804415142147495989673045540297432900988880512405062264799294080782340251828833101634739974991471228712161 

noncomputable def Ns360p1585 := BSN.sin_dyadic_bound_f 107887055607 68719476736 4 3 33554432 10590333 Ns360p1582 Ns360p114 Ns360p1583 Ns360p1584 Ns360p117 Ns360p1583 33554420 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107887055607) qz594 0 3 Ns360p1582 Ns360p114 Ns360p1583 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107887055607) qz595 0 3 Ns360p1584 Ns360p117 Ns360p1583 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1586 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz240) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44590245087) qz378) Bool.false 44590245087 33554432 161 16777216 Bool.true 33554420 33554432 1 5290000 (Ns360p1580 rfl) (Enclosure.sfrac_false_div 44590245087 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44590245087) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns360p1581) qz391) 226375608064910080 72057594037927936 Bool.false 33554420 33554432 211 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q1 44590245087 33554432 226375608064910080 72057594037927936 211 Ns360p1581 Ns360p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554420 33554432 Ns360p1581 Ns360p100 107887055607 68719476736 10590333 10580000 (Ns360p1585 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p1587 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns360p1559 Ns360p1560 5181678811081001801 541696000000000000000000 356721960697 268435456 2569 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz364 qz244 (Enclosure.sfrac Bool.true Ns360p1561 Ns360p1562)) Bool.false Ns360p1559 Ns360p1560 5181678811081001801 541696000000000000000000 Ns360p1563 (Ns360p1579 rfl rfl)) 

noncomputable def Ns360p1588 := Ns360p1558 52634 BSN.abs_quadSignPos (BSN.cos_quad_nat3 531 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 208310051 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 347 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 225151988 268435456) qz243 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) Bool.true 8388605 8388608 54279201 5546967040000 268435360 268435456 2627 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 8388605 8388608 54279201 5546967040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz240) qz240) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 33554420 33554432 868467216 88751472640000 8388605 8388608 54279201 5546967040000 (Ns360p1586 rfl rfl) rfl)) rfl) (Ns360p1587 rfl) RS361to372.d7 

noncomputable def Ns360p1589 := nat_lit 50777900649609536542873991680667173643447661557522992366293240123040000 

noncomputable def Ns360p1590 := nat_lit 10454133397878018005046969035342947430239811437046645901600100000000 

noncomputable def Ns360p1591 := nat_lit 132972814056809364630757045023309185246523487241662142580260657303200000 

noncomputable def Ns360p1592 := BSN.sin_dyadic_bound_f 238457510 268435456 3 2 268435456 134217728 Ns360p1589 Ns360p144 Ns360p1590 Ns360p1591 Ns360p147 Ns360p1590 208310051 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 238457510) qz369 0 2 Ns360p1589 Ns360p144 Ns360p1590 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 238457510) qz370 0 2 Ns360p1591 Ns360p147 Ns360p1590 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1593 := nat_lit 79932985872668757176874475635804426923454321272778180653338665856545345 

noncomputable def Ns360p1594 := nat_lit 25899297876577669892792633851712490512984877849525325792124027286081 

noncomputable def Ns360p1595 := nat_lit 209306364136618000188178152877061202672026008769329336897937828818203201 

noncomputable def Ns360p1596 := BSN.sin_dyadic_bound_f 267092073 268435456 3 2 268435456 134217728 Ns360p1593 Ns360p144 Ns360p1594 Ns360p1595 Ns360p147 Ns360p1594 225151988 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 267092073) qz369 0 2 Ns360p1593 Ns360p144 Ns360p1594 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 267092073) qz370 0 2 Ns360p1595 Ns360p147 Ns360p1594 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1597 := nat_lit 9467311145753190037905169514496 

noncomputable def Ns360p1598 := BSN.sin_dyadic_bound_f 55469808 268435456 2 1 268435456 134217728 Ns360p1597 Ns360p135 Ns360p1597 Ns360p1597 Ns360p136 Ns360p1597 55075884 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 55469808) qz369 0 1 Ns360p1597 Ns360p135 Ns360p1597 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 55469808) qz370 0 1 Ns360p1597 Ns360p136 Ns360p1597 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1599 := nat_lit 29891431958560166757628829505981256488701774828829621367801498787320250276005535633903833598077193701744644096 

noncomputable def Ns360p1600 := nat_lit 9714402957883913954294637179977955670371140651934304729182182838570818464952704192630213798840216784896 

noncomputable def Ns360p1601 := nat_lit 149331737420599250948986090857428830712225168667635961716349775101983350688340144178391917634524400555067641856 

noncomputable def Ns360p1602 := BSN.sin_dyadic_bound_f 382194714 268435456 4 3 268435456 134217728 Ns360p1599 Ns360p258 Ns360p1600 Ns360p1601 Ns360p261 Ns360p1600 265539968 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 382194714) qz369 0 3 Ns360p1599 Ns360p258 Ns360p1600 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 382194714) qz370 0 3 Ns360p1601 Ns360p261 Ns360p1600 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1603 := Ns360p1556 89518 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 217 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 55075884 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 115 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 265539968 268435456) qz243 rfl rfl (Ns360p1588 RS361to372.d9 RS361to372.d11 RS361to372.d13 RS361to372.d17 (Ns360p1592 rfl rfl) (Ns360p1596 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns360p1587 rfl) RS361to372.d19 RS361to372.d21 RS361to372.d23 RS361to372.d25 RS361to372.d17 (Ns360p1598 rfl rfl) (Ns360p1602 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns360p1604 := nat_lit 50038433105647144186771266355456 

noncomputable def Ns360p1605 := BSN.sin_dyadic_bound_f 84105796 268435456 2 1 268435456 134217728 Ns360p1604 Ns360p135 Ns360p1604 Ns360p1604 Ns360p136 Ns360p1604 82736444 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 84105796) qz369 0 1 Ns360p1604 Ns360p135 Ns360p1604 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 84105796) qz370 0 1 Ns360p1604 Ns360p136 Ns360p1604 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1606 := nat_lit 4789319845771960787591733901997657459624045764212497982876613927106296094044085843778702813724459396597560561 

noncomputable def Ns360p1607 := nat_lit 703007048395517250942816368391345606463208627736727340017906185770988985611514612870096084821727524081 

noncomputable def Ns360p1608 := nat_lit 29035478914076574219440779550397489074415330641889836943946450092393690392484935072722500259609925174490051825 

noncomputable def Ns360p1609 := BSN.cos_dyadic_bound_f 307076541 268435456 4 3 268435456 134217728 Ns360p1606 Ns360p129 Ns360p1607 Ns360p1608 Ns360p132 Ns360p1607 111133037 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 307076541) qz367 0 3 Ns360p1606 Ns360p129 Ns360p1607 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 307076541) qz368 0 3 Ns360p1608 Ns360p132 Ns360p1607 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1610 := Ns360p1554 120689 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 33 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 82736444 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 111133037 268435456) qz243 rfl rfl (Ns360p1603 rfl rfl) (Ns360p1587 rfl) RS361to372.d27 RS361to372.d29 RS361to372.d31 RS361to372.d33 RS361to372.d17 (Ns360p1605 rfl rfl) (Ns360p1609 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p1611 := nat_lit 4153067861514640110925835004415182095780649122469999766066763636920225 

noncomputable def Ns360p1612 := nat_lit 69958553506764298776819012995102892821833094233017729734979342241 

noncomputable def Ns360p1613 := nat_lit 10876969228213617910226786352209199131884750448126003072898143368236961 

noncomputable def Ns360p1614 := BSN.sin_dyadic_bound_f 127527869 268435456 3 2 268435456 134217728 Ns360p1611 Ns360p144 Ns360p1612 Ns360p1613 Ns360p147 Ns360p1612 122784553 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 127527869) qz369 0 2 Ns360p1611 Ns360p144 Ns360p1612 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 127527869) qz370 0 2 Ns360p1613 Ns360p147 Ns360p1612 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1615 := nat_lit 4905300301528164601914738068312494891128467773271837061433914068585845604942866535441649722469315345704288256 

noncomputable def Ns360p1616 := nat_lit 755271071165920938483283843824098835946560504650436489025593329508398010845521181829259820064231653376 

noncomputable def Ns360p1617 := nat_lit 29738127546536499773865621916653077332581162790142893162637068008819081485999580320540845058279599728796631040 

noncomputable def Ns360p1618 := BSN.cos_dyadic_bound_f 308917068 268435456 4 3 268435456 134217728 Ns360p1615 Ns360p129 Ns360p1616 Ns360p1617 Ns360p132 Ns360p1616 109455051 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 308917068) qz367 0 3 Ns360p1615 Ns360p129 Ns360p1616 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 308917068) qz368 0 3 Ns360p1617 Ns360p132 Ns360p1616 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1619 := Ns360p1552 147925 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 97 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 122784553 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 150 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 109455051 268435456) qz243 rfl rfl (Ns360p1610 rfl) (Ns360p1587 rfl) RS361to372.d35 RS361to372.d37 RS361to372.d39 RS361to372.d41 RS361to372.d17 (Ns360p1614 rfl rfl) (Ns360p1618 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns360p1620 := nat_lit 21365469912887553664807191971406939959452406900078279189827169542636801 

noncomputable def Ns360p1621 := nat_lit 5995750073910369287577538624365601053732529850041065417535822398721 

noncomputable def Ns360p1622 := nat_lit 64084418238514840255846420836972088676249755640534755438646436983112961 

noncomputable def Ns360p1623 := BSN.cos_dyadic_bound_f 222448991 268435456 3 2 268435456 134217728 Ns360p1620 Ns360p123 Ns360p1621 Ns360p1622 Ns360p126 Ns360p1621 181420500 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 222448991) qz367 0 2 Ns360p1620 Ns360p123 Ns360p1621 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 222448991) qz368 0 2 Ns360p1622 Ns360p126 Ns360p1621 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1624 := Ns360p1550 Bool.false 28400209 147925 Bool.true 222448991 14148475504056880 1 Bool.false 181420500 Bool.true Bool.true 28969991 160465 BSN.abs_quadSignNeg qz632 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 181420500 268435456) qz243 rfl (Ns360p1619 rfl) (Ns360p1587 rfl) RS361to372.d43 RS361to372.d45 RS361to372.d17 (Ns360p1623 rfl rfl) rfl 

noncomputable def Ns360p1625 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) 28969991 268435456 160465 268435456 28969991 268435456 160465 268435456 15553145488801792 28969991 134217728 160465 134217728 (Ns360p1624 rfl rfl rfl rfl) 

noncomputable def Ns360p1626 := @Enclosure.Real.IsNear.mulLit_ff qz721 (Zeta.RiemannSiegel.correction qz242) 2570567 8388608 1 16777216 118985916304675 281474976710656 555590433329953 18612532834992128000 305861269917559500725 2361183241434822606848 

noncomputable abbrev qz725 := (@HPow.hPow Real Real Real qz7 qz241 qz9)

noncomputable def Ns360p1627 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz725 1 1 0 1 2570567 8388608 1 16777216 2570567 8388608 1 16777216 

noncomputable def Ns360p1628 := @Enclosure.Real.IsNear.sqrt_image qz241 951335823773 8388608000 178141 8388608000 178665965 178665999 16777216 (@Enclosure.Real.IsNear.of_eq qz241 (@HMul.hMul Real Real Real qz5 qz240 qz3) Bool.false 951335823773 8388608000 178141 8388608000 (BSN.t_div_two_pi_mk qz240 712564 1000 qz243) (@Enclosure.Real.IsNear.mulLit_ff qz240 qz3 712564 1000 0 1 5340353 33554432 1 33554432 951335823773 8388608000 178141 8388608000 (Enclosure.Real.IsNear.const Bool.false 712564 1000) RS361to372.d48 rfl)) 

noncomputable abbrev qz796 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 712564 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz726 := qz796

noncomputable abbrev qz540 := qz726

noncomputable abbrev qz249 := qz540

noncomputable def Ns360p1629 := @Enclosure.Real.IsNear.sqrt_image qz249 89332991 8388608 17 16777216 54749588 54749595 16777216 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 357331964 33554432 34 33554432 89332991 8388608 17 16777216 (Ns360p1628 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns360p1630 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz249) 109499183 33554432 7 33554432 5141133 5141135 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz249) Bool.false 109499183 33554432 7 33554432 109499183 33554432 7 33554432 (Ns360p1629 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns360p1631 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 10282268 33554432 2 33554432 2570567 8388608 1 16777216 (Ns360p1630 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz250 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz534))

noncomputable abbrev qz727 := (@HMul.hMul Real Real Real qz737 qz794 qz794)

noncomputable abbrev qz541 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz727 qz720) qz600)

noncomputable abbrev qz251 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz541))

noncomputable def Ns360p1632 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz242) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz250) qz251) Bool.false 118985916304675 

noncomputable def Ns360p1633 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz250) qz251 56754145 33554432 635 

noncomputable abbrev qz728 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz250))

noncomputable def Ns360p1634 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz250) (@Neg.neg Real Real.instNeg qz728) Bool.true 56754145 33554432 635 33554432 (BSN.inv_eq_neg_inv_neg qz250) 

noncomputable def Ns360p1635 := @Enclosure.Real.IsNear.recentre' qz728 Bool.false 56754145 33554432 635 33554432 56754145 33554432 

noncomputable def Ns360p1636 := @Enclosure.Real.IsNear.recentre' qz250 Bool.true 19838197 33554432 1170904432 177502945280000 19838197 33554432 73181527 11093934080000 

noncomputable abbrev qz252 := (@HMul.hMul Real Real Real qz349 qz346 qz534)

noncomputable def Ns360p1637 := @Enclosure.Real.IsNear.cos_image qz252 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 34223951) qz413) Bool.false 34223951 8388608 215 33554432 Bool.true 19838197 33554432 1 

noncomputable def Ns360p1638 := nat_lit 458763282047325991174763063 

noncomputable def Ns360p1639 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz242 884279719003555 140737488355328 1 500000000000000 5446911 8388608 17 16777216 4816592928517372768605 1180591620717411303424 Ns360p1638 

noncomputable def Ns360p1640 := @Enclosure.Real.IsNear.subLit_ff_p qz249 qz1 89332991 8388608 17 16777216 10 1 0 1 5446911 5446911 8388608 17 

noncomputable def Ns360p1641 := @Ns360p1640 16777216 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 357331964 33554432 34 33554432 89332991 8388608 17 16777216 (Ns360p1628 rfl rfl rfl rfl rfl rfl) rfl) qz375 

noncomputable def Ns360p1642 := @Enclosure.Real.IsNear.recentre' qz252 Bool.false 4816592928517372768605 1180591620717411303424 Ns360p1638 Ns360p180 34223951 8388608 215 33554432 (@Ns360p1639 Ns360p180 RS361to372.d47 (Ns360p1641 rfl rfl) rfl) 

noncomputable def Ns360p1643 := nat_lit 647690409340203045985273895169098958046307464880375338727549180434765721565365591108877121 

noncomputable def Ns360p1644 := nat_lit 298591264545327354815700862231947718950600493409129647483864648123461952178052447992641 

noncomputable def Ns360p1645 := nat_lit 1942474045491518483246190283782832978701021193654307756887679812008050240791740668430646081 

noncomputable def Ns360p1646 := BSN.cos_dyadic_bound_f 64474003319 68719476736 3 2 33554432 10590333 Ns360p1643 Ns360p693 Ns360p1644 Ns360p1645 Ns360p696 Ns360p1644 19838197 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 64474003319) qz376 0 2 Ns360p1643 Ns360p693 Ns360p1644 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 64474003319) qz377 0 2 Ns360p1645 Ns360p696 Ns360p1644 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1647 := @Ns360p1637 5290000 (Ns360p1642 rfl) (Enclosure.sfrac_false_div 34223951 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 34223951) qz413) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1134238661427537213652992) qz414) 226375608064910080 72057594037927936 Bool.false 19838197 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q2 34223951 8388608 226375608064910080 72057594037927936 0 1134238661427537213652992 Ns360p459 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 19838197 33554432 1134238661427537213652992 Ns360p459 64474003319 68719476736 10590333 10580000 (Ns360p1646 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns360p1648 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz250) 19838197 33554432 73181527 11093934080000 28376755 28377390 16777216 (@Enclosure.Real.IsNear.neg qz250 Bool.true 19838197 33554432 73181527 11093934080000 (Ns360p1636 (Ns360p1647 rfl rfl) rfl)) 

noncomputable def Ns360p1649 := Ns360p1634 (@Enclosure.Real.IsNear.neg qz728 Bool.false 56754145 33554432 635 33554432 (@Ns360p1635 635 33554432 (Ns360p1648 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns360p1650 := @Enclosure.Real.IsNear.recentre' qz251 Bool.true 4193030 16777216 

noncomputable abbrev qz253 := (@HMul.hMul Real Real Real qz349 qz346 qz541)

noncomputable def Ns360p1651 := @Enclosure.Real.IsNear.cos_image qz253 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 3823943)) (@Nat.cast Real Real.instNatCast 2097152)) Bool.true 3823943 2097152 

noncomputable def Ns360p1652 := nat_lit 18058060301044380476409997405 

noncomputable def Ns360p1653 := nat_lit 17692149541364308482477124174461131 

noncomputable def Ns360p1654 := @Enclosure.Real.IsNear.recentre' qz253 Bool.true Ns360p1652 Ns360p195 Ns360p1653 

noncomputable abbrev qz254 := qz541

noncomputable def Ns360p1655 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz254 884279719003555 140737488355328 1 500000000000000 20421208259071 

noncomputable abbrev qz542 := (@HSub.hSub Real Real Real qz587 qz727 qz720)

noncomputable abbrev qz255 := qz542

noncomputable def Ns360p1656 := @Enclosure.Real.IsNear.subLit_tf qz255 qz31 16023161747967 70368744177664 655602909 281474976710656 1 16 

noncomputable abbrev qz543 := qz727

noncomputable abbrev qz256 := qz543

noncomputable def Ns360p1657 := @Enclosure.Real.IsNear.subLit_ff_n qz256 qz242 29668839441921 70368744177664 370390237 281474976710656 5446911 8388608 17 16777216 

noncomputable def Ns360p1658 := @Enclosure.Real.IsNear.mulLit_ff qz242 qz242 5446911 8388608 17 16777216 5446911 8388608 17 16777216 29668839441921 70368744177664 

noncomputable def Ns360p1659 := nat_lit 1607168873315165659365994453188204825577080790079370298870518273646309185333575688481 

noncomputable def Ns360p1660 := nat_lit 9775453637075478038750269017694620098315927580656500297584175889473525879284001 

noncomputable def Ns360p1661 := nat_lit 9707618351424835128538166938250984029531462686986623312646242241409973788611069485345 

noncomputable def Ns360p1662 := BSN.cos_dyadic_bound_t 3823943 2097152 4 3 16777216 5290000 Ns360p1659 Ns360p1424 Ns360p1660 Ns360p1661 Ns360p1427 Ns360p1660 4193030 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 3823943) (BSN.cosEvenQ 2097152) 0 3 Ns360p1659 Ns360p1424 Ns360p1660 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 3823943) (BSN.cosOddQ 2097152) 0 3 Ns360p1661 Ns360p1427 Ns360p1660 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns360p1663 := @Ns360p1650 659058608 44375736320000 2096515 8388608 41191163 2773483520000 (@Ns360p1651 123 8388608 Bool.true 4193030 16777216 1 5290000 (@Ns360p1654 Ns360p198 3823943 2097152 123 8388608 (@Ns360p1655 70368744177664 655602909 281474976710656 Ns360p1652 Ns360p195 Ns360p1653 Ns360p198 RS361to372.d47 (@Ns360p1656 0 1 326739332145136 20421208259071 70368744177664 655602909 281474976710656 (@Ns360p1657 134412022824289959936 16023161747967 70368744177664 655602909 281474976710656 (@Ns360p1658 370390237 281474976710656 (Ns360p1641 rfl rfl) (Ns360p1641 rfl rfl) rfl) (Ns360p1641 rfl rfl) rfl rfl) qz382 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 3823943 2097152) (BSN.cos_neg_of_bound 3823943 2097152 Bool.true 4193030 16777216 1 5290000 (Ns360p1662 rfl rfl)) rfl rfl) 

noncomputable def Ns360p1664 := @Ns360p1626 286423336617343455103 Ns360p1547 (Ns360p1627 qz33 (@Enclosure.Real.IsNear.of_eq qz725 (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 2570567 8388608 1 16777216 (BSN.rpow_neg_quarter_mk qz241 (BSN.t_div_two_pi_nonneg qz240 712564 1000 qz243)) Ns360p1631) rfl) (@Ns360p1632 281474976710656 555590433329953 18612532834992128000 (BSN.correction_mk qz242 (BSN.cos_two_pi_p_ne_zero_mk qz240 712564 1000 10 qz243 rfl rfl (@BSN.floor_sqrt_eq_dec qz240 712564 1000 10 qz243 rfl rfl rfl))) (@Ns360p1633 33554432 2096515 8388608 41191163 2773483520000 118985916304675 281474976710656 555590433329953 18612532834992128000 Ns360p1649 (Ns360p1663 rfl) rfl)) 

noncomputable def Ns360p1665 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (hardyZApproximantRS₀ qz240) Bool.true 815506741294616620981 2361183241434822606848 37619674353704991199103 Ns360p1547 (@Eq.refl Real (hardyZApproximantRS₀ qz240)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (@HMul.hMul Real Real Real qz5 qz721 (Zeta.RiemannSiegel.correction qz242))) Bool.true 815506741294616620981 2361183241434822606848 37619674353704991199103 Ns360p1547 (BSN.hardyZApproximantRS₀_eq qz240 10 (@BSN.floor_sqrt_eq_dec qz240 712564 1000 10 qz243 rfl rfl rfl)) (@Ns360p1549 815506741294616620981 2361183241434822606848 37619674353704991199103 Ns360p1547 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (@HAdd.hAdd Real Real Real qz364 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10)) Bool.true 28969991 134217728 160465 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (Ns360p1625 (Ns360p1624 rfl rfl rfl rfl) rfl rfl)) (Ns360p1664 rfl) rfl rfl)) 

theorem RS361to372.d63 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz240) Bool.true 815506741294616620981 2361183241434822606848 37619674353704991199103 Ns360p1547 := Ns360p1665 

noncomputable def RS361to372.d64 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz544 := (RS361to372.d3 qz582 qz602 (@Enclosure.dec_le_dec qz582 qz602 696589 1000 697923 1000 (@Eq.refl Real qz582) qz606 rfl rfl rfl))

noncomputable abbrev qz257 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz544)

noncomputable def Ns360p1666 := @Enclosure.Real.IsNear.of_eq qz257 (hardyZApproximantRS₀ qz4) Bool.true 860720205796705063197 4722366482869645213696 366527951523047376868231 Ns360p74 

noncomputable abbrev qz545 := (@Enclosure.dec_le_dec qz582 qz602 696589 1000 697923 1000 (@Eq.refl Real qz582) qz606 rfl rfl rfl)

noncomputable abbrev qz258 := qz545

noncomputable def Ns360p1667 := @Enclosure.Real.IsNear.neg_val qz257 860720205796705063197 4722366482869645213696 366527951523047376868231 Ns360p74 (Ns360p1666 (RS361to372.d4 qz4 qz35 qz258) RS361to372.d49) rfl 

noncomputable abbrev qz259 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz544)

noncomputable def Ns360p1668 := @Enclosure.Real.IsNear.of_eq qz259 (hardyZApproximantRS₀ qz35) Bool.false 2418197661641577807615 295147905179352825856 14345945452323147794399 Ns360p212 

noncomputable def Ns360p1669 := @Enclosure.Real.IsNear.pos_val qz259 2418197661641577807615 295147905179352825856 14345945452323147794399 Ns360p212 (Ns360p1668 (RS361to372.d50 qz4 qz35 qz258) RS361to372.d51) rfl 

noncomputable def Ns360p1670 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz257 qz4 qz4 696589 1000 696589 1000 

noncomputable def Ns360p1671 := @Enclosure.norm_gt_of_isNear qz257 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 860720205796705063197 4722366482869645213696 366527951523047376868231 

noncomputable def Ns360p1672 := @Ns360p1671 Ns360p74 297548349 5368709120 1213 5368709120 (Ns360p1666 (RS361to372.d4 qz4 qz35 qz258) RS361to372.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable def Ns360p1673 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz259 qz4 qz35 696589 1000 697923 1000 

noncomputable def Ns360p1674 := @Enclosure.norm_gt_of_isNear qz259 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2418197661641577807615 295147905179352825856 14345945452323147794399 

noncomputable def Ns360p1675 := @Ns360p1674 Ns360p212 297548349 5368709120 1213 5368709120 (Ns360p1668 (RS361to372.d50 qz4 qz35 qz258) RS361to372.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable abbrev qz260 := qz544

noncomputable def Ns360p1676 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz260 (@BSN.thirtyTwoPi_le_dec qz4 696589 1000 qz11 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz257 qz259 (Ns360p1667 rfl rfl) (Ns360p1669 rfl rfl)) (Ns360p1670 qz11 qz11 rfl rfl rfl rfl (Ns360p1672 rfl)) (Ns360p1673 qz11 qz38 rfl rfl rfl rfl (Ns360p1675 rfl)) 

noncomputable abbrev qz546 := (RS361to372.d3 qz602 qz614 (@Enclosure.dec_le_dec qz602 qz614 697923 1000 699257 1000 qz606 qz618 rfl rfl rfl))

noncomputable abbrev qz261 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz546)

noncomputable def Ns360p1677 := @Enclosure.Real.IsNear.of_eq qz261 (hardyZApproximantRS₀ qz35) Bool.false 2418197661641577807615 295147905179352825856 14345945452323147794399 Ns360p212 

noncomputable abbrev qz547 := (@Enclosure.dec_le_dec qz602 qz614 697923 1000 699257 1000 qz606 qz618 rfl rfl rfl)

noncomputable abbrev qz262 := qz547

noncomputable def Ns360p1678 := @Enclosure.Real.IsNear.pos_val qz261 2418197661641577807615 295147905179352825856 14345945452323147794399 Ns360p212 (Ns360p1677 (RS361to372.d4 qz35 qz62 qz262) RS361to372.d51) rfl 

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz546)

noncomputable def Ns360p1679 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantRS₀ qz62) Bool.true 3364240068786006104779 4722366482869645213696 920011395717358325935637 Ns360p363 

noncomputable def Ns360p1680 := @Enclosure.Real.IsNear.neg_val qz263 3364240068786006104779 4722366482869645213696 920011395717358325935637 Ns360p363 (Ns360p1679 (RS361to372.d50 qz35 qz62 qz262) RS361to372.d53) rfl 

noncomputable def Ns360p1681 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz261 qz4 qz35 696589 1000 697923 1000 

noncomputable def Ns360p1682 := @Enclosure.norm_gt_of_isNear qz261 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2418197661641577807615 295147905179352825856 14345945452323147794399 

noncomputable def Ns360p1683 := @Ns360p1682 Ns360p212 297548349 5368709120 1213 5368709120 (Ns360p1677 (RS361to372.d4 qz35 qz62 qz262) RS361to372.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable def Ns360p1684 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz263 qz4 qz62 696589 1000 699257 1000 

noncomputable def Ns360p1685 := @Enclosure.norm_gt_of_isNear qz263 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 3364240068786006104779 4722366482869645213696 920011395717358325935637 

noncomputable def Ns360p1686 := @Ns360p1685 Ns360p363 297548349 5368709120 1213 5368709120 (Ns360p1679 (RS361to372.d50 qz35 qz62 qz262) RS361to372.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable abbrev qz264 := qz546

noncomputable def Ns360p1687 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz264 (@BSN.thirtyTwoPi_le_dec qz35 697923 1000 qz38 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz261 qz263 (Ns360p1678 rfl rfl) (Ns360p1680 rfl rfl)) (Ns360p1681 qz11 qz38 rfl rfl rfl rfl (Ns360p1683 rfl)) (Ns360p1684 qz11 qz65 rfl rfl rfl rfl (Ns360p1686 rfl)) 

noncomputable abbrev qz548 := (RS361to372.d3 qz614 qz624 (@Enclosure.dec_le_dec qz614 qz624 699257 1000 700590 1000 qz618 qz628 rfl rfl rfl))

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz548)

noncomputable def Ns360p1688 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantRS₀ qz62) Bool.true 3364240068786006104779 4722366482869645213696 920011395717358325935637 Ns360p363 

noncomputable abbrev qz549 := (@Enclosure.dec_le_dec qz614 qz624 699257 1000 700590 1000 qz618 qz628 rfl rfl rfl)

noncomputable abbrev qz266 := qz549

noncomputable def Ns360p1689 := @Enclosure.Real.IsNear.neg_val qz265 3364240068786006104779 4722366482869645213696 920011395717358325935637 Ns360p363 (Ns360p1688 (RS361to372.d4 qz62 qz80 qz266) RS361to372.d53) rfl 

noncomputable abbrev qz267 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz548)

noncomputable def Ns360p1690 := @Enclosure.Real.IsNear.of_eq qz267 (hardyZApproximantRS₀ qz80) Bool.false 6335873763053778873795 9444732965739290427392 737514811092801048863261 Ns360p483 

noncomputable def Ns360p1691 := @Enclosure.Real.IsNear.pos_val qz267 6335873763053778873795 9444732965739290427392 737514811092801048863261 Ns360p483 (Ns360p1690 (RS361to372.d50 qz62 qz80 qz266) RS361to372.d54) rfl 

noncomputable def Ns360p1692 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz265 qz4 qz62 696589 1000 699257 1000 

noncomputable def Ns360p1693 := @Enclosure.norm_gt_of_isNear qz265 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 3364240068786006104779 4722366482869645213696 920011395717358325935637 

noncomputable def Ns360p1694 := @Ns360p1693 Ns360p363 297548349 5368709120 1213 5368709120 (Ns360p1688 (RS361to372.d4 qz62 qz80 qz266) RS361to372.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable def Ns360p1695 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz267 qz4 qz80 696589 1000 700590 1000 

noncomputable def Ns360p1696 := @Enclosure.norm_gt_of_isNear qz267 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 6335873763053778873795 9444732965739290427392 737514811092801048863261 

noncomputable def Ns360p1697 := @Ns360p1696 Ns360p483 297548349 5368709120 1213 5368709120 (Ns360p1690 (RS361to372.d50 qz62 qz80 qz266) RS361to372.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable abbrev qz268 := qz548

noncomputable def Ns360p1698 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz268 (@BSN.thirtyTwoPi_le_dec qz62 699257 1000 qz65 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz265 qz267 (Ns360p1689 rfl rfl) (Ns360p1691 rfl rfl)) (Ns360p1692 qz11 qz65 rfl rfl rfl rfl (Ns360p1694 rfl)) (Ns360p1695 qz11 qz83 rfl rfl rfl rfl (Ns360p1697 rfl)) 

noncomputable abbrev qz550 := (RS361to372.d3 qz624 qz636 (@Enclosure.dec_le_dec qz624 qz636 700590 1000 701923 1000 qz628 qz640 rfl rfl rfl))

noncomputable abbrev qz269 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz550)

noncomputable def Ns360p1699 := @Enclosure.Real.IsNear.of_eq qz269 (hardyZApproximantRS₀ qz80) Bool.false 6335873763053778873795 9444732965739290427392 737514811092801048863261 Ns360p483 

noncomputable abbrev qz551 := (@Enclosure.dec_le_dec qz624 qz636 700590 1000 701923 1000 qz628 qz640 rfl rfl rfl)

noncomputable abbrev qz270 := qz551

noncomputable def Ns360p1700 := @Enclosure.Real.IsNear.pos_val qz269 6335873763053778873795 9444732965739290427392 737514811092801048863261 Ns360p483 (Ns360p1699 (RS361to372.d4 qz80 qz98 qz270) RS361to372.d54) rfl 

noncomputable abbrev qz271 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz550)

noncomputable def Ns360p1701 := @Enclosure.Real.IsNear.of_eq qz271 (hardyZApproximantRS₀ qz98) Bool.true 780127895071683516863 1180591620717411303424 369507192415172398973301 Ns360p74 

noncomputable def Ns360p1702 := @Enclosure.Real.IsNear.neg_val qz271 780127895071683516863 1180591620717411303424 369507192415172398973301 Ns360p74 (Ns360p1701 (RS361to372.d50 qz80 qz98 qz270) RS361to372.d55) rfl 

noncomputable def Ns360p1703 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz269 qz4 qz80 696589 1000 700590 1000 

noncomputable def Ns360p1704 := @Enclosure.norm_gt_of_isNear qz269 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 6335873763053778873795 9444732965739290427392 737514811092801048863261 

noncomputable def Ns360p1705 := @Ns360p1704 Ns360p483 297548349 5368709120 1213 5368709120 (Ns360p1699 (RS361to372.d4 qz80 qz98 qz270) RS361to372.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable def Ns360p1706 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz271 qz4 qz98 696589 1000 701923 1000 

noncomputable def Ns360p1707 := @Enclosure.norm_gt_of_isNear qz271 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 780127895071683516863 1180591620717411303424 369507192415172398973301 

noncomputable def Ns360p1708 := @Ns360p1707 Ns360p74 297548349 5368709120 1213 5368709120 (Ns360p1701 (RS361to372.d50 qz80 qz98 qz270) RS361to372.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable abbrev qz272 := qz550

noncomputable def Ns360p1709 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz272 (@BSN.thirtyTwoPi_le_dec qz80 700590 1000 qz83 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz269 qz271 (Ns360p1700 rfl rfl) (Ns360p1702 rfl rfl)) (Ns360p1703 qz11 qz83 rfl rfl rfl rfl (Ns360p1705 rfl)) (Ns360p1706 qz11 qz101 rfl rfl rfl rfl (Ns360p1708 rfl)) 

noncomputable abbrev qz552 := (RS361to372.d3 qz636 qz646 (@Enclosure.dec_le_dec qz636 qz646 701923 1000 703255 1000 qz640 qz650 rfl rfl rfl))

noncomputable abbrev qz273 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz552)

noncomputable def Ns360p1710 := @Enclosure.Real.IsNear.of_eq qz273 (hardyZApproximantRS₀ qz98) Bool.true 780127895071683516863 1180591620717411303424 369507192415172398973301 Ns360p74 

noncomputable abbrev qz553 := (@Enclosure.dec_le_dec qz636 qz646 701923 1000 703255 1000 qz640 qz650 rfl rfl rfl)

noncomputable abbrev qz274 := qz553

noncomputable def Ns360p1711 := @Enclosure.Real.IsNear.neg_val qz273 780127895071683516863 1180591620717411303424 369507192415172398973301 Ns360p74 (Ns360p1710 (RS361to372.d4 qz98 qz116 qz274) RS361to372.d55) rfl 

noncomputable abbrev qz275 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz552)

noncomputable def Ns360p1712 := @Enclosure.Real.IsNear.of_eq qz275 (hardyZApproximantRS₀ qz116) Bool.false 6536451275869393795583 2361183241434822606848 925692183115406991678591 Ns360p363 

noncomputable def Ns360p1713 := @Enclosure.Real.IsNear.pos_val qz275 6536451275869393795583 2361183241434822606848 925692183115406991678591 Ns360p363 (Ns360p1712 (RS361to372.d50 qz98 qz116 qz274) RS361to372.d56) rfl 

noncomputable def Ns360p1714 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz273 qz4 qz98 696589 1000 701923 1000 

noncomputable def Ns360p1715 := @Enclosure.norm_gt_of_isNear qz273 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 780127895071683516863 1180591620717411303424 369507192415172398973301 

noncomputable def Ns360p1716 := @Ns360p1715 Ns360p74 297548349 5368709120 1213 5368709120 (Ns360p1710 (RS361to372.d4 qz98 qz116 qz274) RS361to372.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable def Ns360p1717 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz275 qz4 qz116 696589 1000 703255 1000 

noncomputable def Ns360p1718 := @Enclosure.norm_gt_of_isNear qz275 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 6536451275869393795583 2361183241434822606848 925692183115406991678591 

noncomputable def Ns360p1719 := @Ns360p1718 Ns360p363 297548349 5368709120 1213 5368709120 (Ns360p1712 (RS361to372.d50 qz98 qz116 qz274) RS361to372.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable abbrev qz276 := qz552

noncomputable def Ns360p1720 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz276 (@BSN.thirtyTwoPi_le_dec qz98 701923 1000 qz101 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz273 qz275 (Ns360p1711 rfl rfl) (Ns360p1713 rfl rfl)) (Ns360p1714 qz11 qz101 rfl rfl rfl rfl (Ns360p1716 rfl)) (Ns360p1717 qz11 qz119 rfl rfl rfl rfl (Ns360p1719 rfl)) 

noncomputable abbrev qz554 := (RS361to372.d3 qz646 qz656 (@Enclosure.dec_le_dec qz646 qz656 703255 1000 704586 1000 qz650 qz660 rfl rfl rfl))

noncomputable abbrev qz277 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz554)

noncomputable def Ns360p1721 := @Enclosure.Real.IsNear.of_eq qz277 (hardyZApproximantRS₀ qz116) Bool.false 6536451275869393795583 2361183241434822606848 925692183115406991678591 Ns360p363 

noncomputable abbrev qz555 := (@Enclosure.dec_le_dec qz646 qz656 703255 1000 704586 1000 qz650 qz660 rfl rfl rfl)

noncomputable abbrev qz278 := qz555

noncomputable def Ns360p1722 := @Enclosure.Real.IsNear.pos_val qz277 6536451275869393795583 2361183241434822606848 925692183115406991678591 Ns360p363 (Ns360p1721 (RS361to372.d4 qz116 qz134 qz278) RS361to372.d56) rfl 

noncomputable abbrev qz279 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz554)

noncomputable def Ns360p1723 := @Enclosure.Real.IsNear.of_eq qz279 (hardyZApproximantRS₀ qz134) Bool.true 6100621131379268278409 4722366482869645213696 115952697012896641133983 Ns360p831 

noncomputable def Ns360p1724 := @Enclosure.Real.IsNear.neg_val qz279 6100621131379268278409 4722366482869645213696 115952697012896641133983 Ns360p831 (Ns360p1723 (RS361to372.d50 qz116 qz134 qz278) RS361to372.d57) rfl 

noncomputable def Ns360p1725 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz277 qz4 qz116 696589 1000 703255 1000 

noncomputable def Ns360p1726 := @Enclosure.norm_gt_of_isNear qz277 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 6536451275869393795583 2361183241434822606848 925692183115406991678591 

noncomputable def Ns360p1727 := @Ns360p1726 Ns360p363 297548349 5368709120 1213 5368709120 (Ns360p1721 (RS361to372.d4 qz116 qz134 qz278) RS361to372.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable def Ns360p1728 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz279 qz4 qz134 696589 1000 704586 1000 

noncomputable def Ns360p1729 := @Enclosure.norm_gt_of_isNear qz279 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 6100621131379268278409 4722366482869645213696 115952697012896641133983 

noncomputable def Ns360p1730 := @Ns360p1729 Ns360p831 297548349 5368709120 1213 5368709120 (Ns360p1723 (RS361to372.d50 qz116 qz134 qz278) RS361to372.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable abbrev qz280 := qz554

noncomputable def Ns360p1731 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz280 (@BSN.thirtyTwoPi_le_dec qz116 703255 1000 qz119 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz277 qz279 (Ns360p1722 rfl rfl) (Ns360p1724 rfl rfl)) (Ns360p1725 qz11 qz119 rfl rfl rfl rfl (Ns360p1727 rfl)) (Ns360p1728 qz11 qz137 rfl rfl rfl rfl (Ns360p1730 rfl)) 

noncomputable abbrev qz556 := (RS361to372.d3 qz656 qz666 (@Enclosure.dec_le_dec qz656 qz666 704586 1000 705917 1000 qz660 qz670 rfl rfl rfl))

noncomputable abbrev qz281 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz556)

noncomputable def Ns360p1732 := @Enclosure.Real.IsNear.of_eq qz281 (hardyZApproximantRS₀ qz134) Bool.true 6100621131379268278409 4722366482869645213696 115952697012896641133983 Ns360p831 

noncomputable abbrev qz557 := (@Enclosure.dec_le_dec qz656 qz666 704586 1000 705917 1000 qz660 qz670 rfl rfl rfl)

noncomputable abbrev qz282 := qz557

noncomputable def Ns360p1733 := @Enclosure.Real.IsNear.neg_val qz281 6100621131379268278409 4722366482869645213696 115952697012896641133983 Ns360p831 (Ns360p1732 (RS361to372.d4 qz134 qz152 qz282) RS361to372.d57) rfl 

noncomputable abbrev qz283 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz556)

noncomputable def Ns360p1734 := @Enclosure.Real.IsNear.of_eq qz283 (hardyZApproximantRS₀ qz152) Bool.false 331260701256706480505 295147905179352825856 23241083208679358087707 Ns360p948 

noncomputable def Ns360p1735 := @Enclosure.Real.IsNear.pos_val qz283 331260701256706480505 295147905179352825856 23241083208679358087707 Ns360p948 (Ns360p1734 (RS361to372.d50 qz134 qz152 qz282) RS361to372.d58) rfl 

noncomputable def Ns360p1736 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz281 qz4 qz134 696589 1000 704586 1000 

noncomputable def Ns360p1737 := @Enclosure.norm_gt_of_isNear qz281 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 6100621131379268278409 4722366482869645213696 115952697012896641133983 

noncomputable def Ns360p1738 := @Ns360p1737 Ns360p831 297548349 5368709120 1213 5368709120 (Ns360p1732 (RS361to372.d4 qz134 qz152 qz282) RS361to372.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable def Ns360p1739 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz283 qz4 qz152 696589 1000 705917 1000 

noncomputable def Ns360p1740 := @Enclosure.norm_gt_of_isNear qz283 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 331260701256706480505 295147905179352825856 23241083208679358087707 

noncomputable def Ns360p1741 := @Ns360p1740 Ns360p948 297548349 5368709120 1213 5368709120 (Ns360p1734 (RS361to372.d50 qz134 qz152 qz282) RS361to372.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable abbrev qz284 := qz556

noncomputable def Ns360p1742 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz134 704586 1000 qz137 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz281 qz283 (Ns360p1733 rfl rfl) (Ns360p1735 rfl rfl)) (Ns360p1736 qz11 qz137 rfl rfl rfl rfl (Ns360p1738 rfl)) (Ns360p1739 qz11 qz155 rfl rfl rfl rfl (Ns360p1741 rfl)) 

noncomputable abbrev qz558 := (RS361to372.d3 qz666 qz676 (@Enclosure.dec_le_dec qz666 qz676 705917 1000 707248 1000 qz670 qz680 rfl rfl rfl))

noncomputable abbrev qz285 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz558)

noncomputable def Ns360p1743 := @Enclosure.Real.IsNear.of_eq qz285 (hardyZApproximantRS₀ qz152) Bool.false 331260701256706480505 295147905179352825856 23241083208679358087707 Ns360p948 

noncomputable abbrev qz559 := (@Enclosure.dec_le_dec qz666 qz676 705917 1000 707248 1000 qz670 qz680 rfl rfl rfl)

noncomputable abbrev qz286 := qz559

noncomputable def Ns360p1744 := @Enclosure.Real.IsNear.pos_val qz285 331260701256706480505 295147905179352825856 23241083208679358087707 Ns360p948 (Ns360p1743 (RS361to372.d4 qz152 qz170 qz286) RS361to372.d58) rfl 

noncomputable abbrev qz287 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz558)

noncomputable def Ns360p1745 := @Enclosure.Real.IsNear.of_eq qz287 (hardyZApproximantRS₀ qz170) Bool.true 50672161099958917957415 9444732965739290427392 Ns360p1072 Ns360p1073 

noncomputable def Ns360p1746 := @Enclosure.Real.IsNear.neg_val qz287 50672161099958917957415 9444732965739290427392 Ns360p1072 Ns360p1073 (Ns360p1745 (RS361to372.d50 qz152 qz170 qz286) RS361to372.d59) rfl 

noncomputable def Ns360p1747 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz285 qz4 qz152 696589 1000 705917 1000 

noncomputable def Ns360p1748 := @Enclosure.norm_gt_of_isNear qz285 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 331260701256706480505 295147905179352825856 23241083208679358087707 

noncomputable def Ns360p1749 := @Ns360p1748 Ns360p948 297548349 5368709120 1213 5368709120 (Ns360p1743 (RS361to372.d4 qz152 qz170 qz286) RS361to372.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable def Ns360p1750 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz287 qz4 qz170 696589 1000 707248 1000 

noncomputable def Ns360p1751 := @Enclosure.norm_gt_of_isNear qz287 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 50672161099958917957415 9444732965739290427392 Ns360p1072 

noncomputable def Ns360p1752 := @Ns360p1751 Ns360p1073 297548349 5368709120 1213 5368709120 (Ns360p1745 (RS361to372.d50 qz152 qz170 qz286) RS361to372.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable abbrev qz288 := qz558

noncomputable def Ns360p1753 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz152 705917 1000 qz155 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz285 qz287 (Ns360p1744 rfl rfl) (Ns360p1746 rfl rfl)) (Ns360p1747 qz11 qz155 rfl rfl rfl rfl (Ns360p1749 rfl)) (Ns360p1750 qz11 qz173 rfl rfl rfl rfl (Ns360p1752 rfl)) 

noncomputable abbrev qz729 := (@Enclosure.dec_le_dec qz774 qz778 707248 1000 708578 1000 (@Eq.refl Real qz774) (@Eq.refl Real qz778) rfl rfl rfl)

noncomputable abbrev qz560 := (RS361to372.d3 qz676 qz686 qz729)

noncomputable abbrev qz289 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz560)

noncomputable def Ns360p1754 := @Enclosure.Real.IsNear.of_eq qz289 (hardyZApproximantRS₀ qz170) Bool.true 50672161099958917957415 9444732965739290427392 Ns360p1072 Ns360p1073 

noncomputable abbrev qz561 := qz729

noncomputable abbrev qz290 := qz561

noncomputable def Ns360p1755 := @Enclosure.Real.IsNear.neg_val qz289 50672161099958917957415 9444732965739290427392 Ns360p1072 Ns360p1073 (Ns360p1754 (RS361to372.d4 qz170 qz188 qz290) RS361to372.d59) rfl 

noncomputable abbrev qz291 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz560)

noncomputable def Ns360p1756 := @Enclosure.Real.IsNear.of_eq qz291 (hardyZApproximantRS₀ qz188) Bool.false 11822530310324555672327 9444732965739290427392 149400326021272788491363 Ns360p1190 

noncomputable def Ns360p1757 := @Enclosure.Real.IsNear.pos_val qz291 11822530310324555672327 9444732965739290427392 149400326021272788491363 Ns360p1190 (Ns360p1756 (RS361to372.d50 qz170 qz188 qz290) RS361to372.d60) rfl 

noncomputable def Ns360p1758 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz289 qz4 qz170 696589 1000 707248 1000 

noncomputable def Ns360p1759 := @Enclosure.norm_gt_of_isNear qz289 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 50672161099958917957415 9444732965739290427392 Ns360p1072 

noncomputable def Ns360p1760 := @Ns360p1759 Ns360p1073 297548349 5368709120 1213 5368709120 (Ns360p1754 (RS361to372.d4 qz170 qz188 qz290) RS361to372.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable def Ns360p1761 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz291 qz4 qz188 696589 1000 708578 1000 

noncomputable def Ns360p1762 := @Enclosure.norm_gt_of_isNear qz291 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 11822530310324555672327 9444732965739290427392 149400326021272788491363 

noncomputable def Ns360p1763 := @Ns360p1762 Ns360p1190 297548349 5368709120 1213 5368709120 (Ns360p1756 (RS361to372.d50 qz170 qz188 qz290) RS361to372.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable abbrev qz292 := qz560

noncomputable def Ns360p1764 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz170 707248 1000 qz173 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz289 qz291 (Ns360p1755 rfl rfl) (Ns360p1757 rfl rfl)) (Ns360p1758 qz11 qz173 rfl rfl rfl rfl (Ns360p1760 rfl)) (Ns360p1761 qz11 qz191 rfl rfl rfl rfl (Ns360p1763 rfl)) 

noncomputable abbrev qz730 := (@Enclosure.dec_le_dec qz778 qz782 708578 1000 709907 1000 (@Eq.refl Real qz778) qz785 rfl rfl rfl)

noncomputable abbrev qz562 := (RS361to372.d3 qz686 qz696 qz730)

noncomputable abbrev qz293 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz562)

noncomputable def Ns360p1765 := @Enclosure.Real.IsNear.of_eq qz293 (hardyZApproximantRS₀ qz188) Bool.false 11822530310324555672327 9444732965739290427392 149400326021272788491363 Ns360p1190 

noncomputable abbrev qz563 := qz730

noncomputable abbrev qz294 := qz563

noncomputable def Ns360p1766 := @Enclosure.Real.IsNear.pos_val qz293 11822530310324555672327 9444732965739290427392 149400326021272788491363 Ns360p1190 (Ns360p1765 (RS361to372.d4 qz188 qz206 qz294) RS361to372.d60) rfl 

noncomputable abbrev qz295 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz562)

noncomputable def Ns360p1767 := @Enclosure.Real.IsNear.of_eq qz295 (hardyZApproximantRS₀ qz206) Bool.true 6823553371939741394771 2361183241434822606848 936110904355316472266521 Ns360p363 

noncomputable def Ns360p1768 := @Enclosure.Real.IsNear.neg_val qz295 6823553371939741394771 2361183241434822606848 936110904355316472266521 Ns360p363 (Ns360p1767 (RS361to372.d50 qz188 qz206 qz294) RS361to372.d61) rfl 

noncomputable def Ns360p1769 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz293 qz4 qz188 696589 1000 708578 1000 

noncomputable def Ns360p1770 := @Enclosure.norm_gt_of_isNear qz293 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 11822530310324555672327 9444732965739290427392 149400326021272788491363 

noncomputable def Ns360p1771 := @Ns360p1770 Ns360p1190 297548349 5368709120 1213 5368709120 (Ns360p1765 (RS361to372.d4 qz188 qz206 qz294) RS361to372.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable def Ns360p1772 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz295 qz4 qz206 696589 1000 709907 1000 

noncomputable def Ns360p1773 := @Enclosure.norm_gt_of_isNear qz295 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 6823553371939741394771 2361183241434822606848 936110904355316472266521 

noncomputable def Ns360p1774 := @Ns360p1773 Ns360p363 297548349 5368709120 1213 5368709120 (Ns360p1767 (RS361to372.d50 qz188 qz206 qz294) RS361to372.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable abbrev qz296 := qz562

noncomputable def Ns360p1775 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz296 (@BSN.thirtyTwoPi_le_dec qz188 708578 1000 qz191 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz293 qz295 (Ns360p1766 rfl rfl) (Ns360p1768 rfl rfl)) (Ns360p1769 qz11 qz191 rfl rfl rfl rfl (Ns360p1771 rfl)) (Ns360p1772 qz11 qz209 rfl rfl rfl rfl (Ns360p1774 rfl)) 

noncomputable abbrev qz731 := (@Enclosure.dec_le_dec qz782 qz787 709907 1000 711236 1000 qz785 qz790 rfl rfl rfl)

noncomputable abbrev qz564 := (RS361to372.d3 qz696 qz707 qz731)

noncomputable abbrev qz297 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz564)

noncomputable def Ns360p1776 := @Enclosure.Real.IsNear.of_eq qz297 (hardyZApproximantRS₀ qz206) Bool.true 6823553371939741394771 2361183241434822606848 936110904355316472266521 Ns360p363 

noncomputable abbrev qz565 := qz731

noncomputable abbrev qz298 := qz565

noncomputable def Ns360p1777 := @Enclosure.Real.IsNear.neg_val qz297 6823553371939741394771 2361183241434822606848 936110904355316472266521 Ns360p363 (Ns360p1776 (RS361to372.d4 qz206 qz223 qz298) RS361to372.d61) rfl 

noncomputable abbrev qz299 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz564)

noncomputable def Ns360p1778 := @Enclosure.Real.IsNear.of_eq qz299 (hardyZApproximantRS₀ qz223) Bool.false 32987160198203896177 147573952589676412928 93836321017422516447733 Ns360p1432 

noncomputable def Ns360p1779 := @Enclosure.Real.IsNear.pos_val qz299 32987160198203896177 147573952589676412928 93836321017422516447733 Ns360p1432 (Ns360p1778 (RS361to372.d50 qz206 qz223 qz298) RS361to372.d62) rfl 

noncomputable def Ns360p1780 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz297 qz4 qz206 696589 1000 709907 1000 

noncomputable def Ns360p1781 := @Enclosure.norm_gt_of_isNear qz297 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 6823553371939741394771 2361183241434822606848 936110904355316472266521 

noncomputable def Ns360p1782 := @Ns360p1781 Ns360p363 297548349 5368709120 1213 5368709120 (Ns360p1776 (RS361to372.d4 qz206 qz223 qz298) RS361to372.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable def Ns360p1783 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz299 qz4 qz223 696589 1000 711236 1000 

noncomputable def Ns360p1784 := @Enclosure.norm_gt_of_isNear qz299 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 32987160198203896177 147573952589676412928 93836321017422516447733 

noncomputable def Ns360p1785 := @Ns360p1784 Ns360p1432 297548349 5368709120 1213 5368709120 (Ns360p1778 (RS361to372.d50 qz206 qz223 qz298) RS361to372.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable abbrev qz300 := qz564

noncomputable def Ns360p1786 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz206 709907 1000 qz209 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz297 qz299 (Ns360p1777 rfl rfl) (Ns360p1779 rfl rfl)) (Ns360p1780 qz11 qz209 rfl rfl rfl rfl (Ns360p1782 rfl)) (Ns360p1783 qz11 qz226 rfl rfl rfl rfl (Ns360p1785 rfl)) 

noncomputable abbrev qz797 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 711236 1000) (Enclosure.sfrac Bool.false 712564 1000) 711236 1000 712564 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 711236 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 712564 1000)) rfl rfl rfl)

noncomputable abbrev qz732 := qz797

noncomputable abbrev qz566 := (RS361to372.d3 qz707 qz718 qz732)

noncomputable abbrev qz301 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz566)

noncomputable def Ns360p1787 := @Enclosure.Real.IsNear.of_eq qz301 (hardyZApproximantRS₀ qz223) Bool.false 32987160198203896177 147573952589676412928 93836321017422516447733 Ns360p1432 

noncomputable abbrev qz567 := qz732

noncomputable abbrev qz302 := qz567

noncomputable def Ns360p1788 := @Enclosure.Real.IsNear.pos_val qz301 32987160198203896177 147573952589676412928 93836321017422516447733 Ns360p1432 (Ns360p1787 (RS361to372.d4 qz223 qz240 qz302) RS361to372.d62) rfl 

noncomputable abbrev qz303 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz566)

noncomputable def Ns360p1789 := @Enclosure.Real.IsNear.of_eq qz303 (hardyZApproximantRS₀ qz240) Bool.true 815506741294616620981 2361183241434822606848 37619674353704991199103 Ns360p1547 

noncomputable def Ns360p1790 := @Enclosure.Real.IsNear.neg_val qz303 815506741294616620981 2361183241434822606848 37619674353704991199103 Ns360p1547 (Ns360p1789 (RS361to372.d50 qz223 qz240 qz302) RS361to372.d63) rfl 

noncomputable def Ns360p1791 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz301 qz4 qz223 696589 1000 711236 1000 

noncomputable def Ns360p1792 := @Enclosure.norm_gt_of_isNear qz301 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 32987160198203896177 147573952589676412928 93836321017422516447733 

noncomputable def Ns360p1793 := @Ns360p1792 Ns360p1432 297548349 5368709120 1213 5368709120 (Ns360p1787 (RS361to372.d4 qz223 qz240 qz302) RS361to372.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable def Ns360p1794 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz303 qz4 qz240 696589 1000 712564 1000 

noncomputable def Ns360p1795 := @Enclosure.norm_gt_of_isNear qz303 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 815506741294616620981 2361183241434822606848 37619674353704991199103 

noncomputable def Ns360p1796 := @Ns360p1795 Ns360p1547 297548349 5368709120 1213 5368709120 (Ns360p1789 (RS361to372.d50 qz223 qz240 qz302) RS361to372.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 297548349 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS361to372.d52) rfl rfl rfl rfl 

noncomputable abbrev qz304 := qz566

noncomputable def Ns360p1797 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz304 (@BSN.thirtyTwoPi_le_dec qz223 711236 1000 qz226 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz301 qz303 (Ns360p1788 rfl rfl) (Ns360p1790 rfl rfl)) (Ns360p1791 qz11 qz226 rfl rfl rfl rfl (Ns360p1793 rfl)) (Ns360p1794 qz11 qz243 rfl rfl rfl rfl (Ns360p1796 rfl)) 

noncomputable def Ns360p1798 := @List.cons RS361to372.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns360p1786)) (@List.cons RS361to372.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz304 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz304) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz304) Ns360p1797)) (@List.nil RS361to372.d0)) 

noncomputable def Ns360p1799 := @List.cons RS361to372.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns360p1764)) (@List.cons RS361to372.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns360p1775)) Ns360p1798) 

noncomputable def Ns360p1800 := @List.cons RS361to372.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns360p1742)) (@List.cons RS361to372.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns360p1753)) Ns360p1799) 

noncomputable def Ns360p1801 := @List.cons RS361to372.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz276 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz276) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz276) Ns360p1720)) (@List.cons RS361to372.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz280 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz280) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz280) Ns360p1731)) Ns360p1800) 

noncomputable def Ns360p1802 := @List.cons RS361to372.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz268 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz268) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz268) Ns360p1698)) (@List.cons RS361to372.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz272 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz272) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz272) Ns360p1709)) Ns360p1801) 

noncomputable def Ns360p1803 := @List.cons RS361to372.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz260 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz260) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz260) Ns360p1676)) (@List.cons RS361to372.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz264 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz264) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz264) Ns360p1687)) Ns360p1802) 

noncomputable abbrev qz568 := (RS361to372.d2 qz676 qz686 qz729)

noncomputable abbrev qz733 := (RS361to372.d2 qz782 qz787 (@Enclosure.dec_le_dec qz782 qz787 709907 1000 711236 1000 qz785 qz790 rfl rfl rfl))

noncomputable abbrev qz734 := (@List.cons RS361to372.d1 (RS361to372.d2 qz787 qz792 qz797) (@List.nil RS361to372.d1))

noncomputable abbrev qz569 := (@List.cons RS361to372.d1 (RS361to372.d2 qz686 qz696 qz730) (@List.cons RS361to372.d1 qz733 qz734))

noncomputable abbrev qz305 := (@List.cons RS361to372.d1 (RS361to372.d2 qz469 qz482 qz559) (@List.cons RS361to372.d1 qz568 qz569))

noncomputable def Ns360p1804 := @List.cons RS361to372.d1 (RS361to372.d2 qz116 qz134 qz278) (@List.cons RS361to372.d1 (RS361to372.d2 qz134 qz152 qz282) qz305) 

noncomputable abbrev qz306 := (RS361to372.d2 qz430 qz443 qz553)

noncomputable def Ns360p1805 := @List.IsChain.cons_cons RS361to372.d1 RS361to372.d64 qz306 (RS361to372.d2 qz116 qz134 qz278) (@List.cons RS361to372.d1 (RS361to372.d2 qz134 qz152 qz282) qz305) 

noncomputable def Ns360p1806 := @List.IsChain.cons_cons RS361to372.d1 RS361to372.d64 (RS361to372.d2 qz116 qz134 qz278) (RS361to372.d2 qz134 qz152 qz282) qz305 (@Enclosure.dec_le_dec qz134 qz134 704586 1000 704586 1000 qz137 qz137 rfl rfl rfl) 

noncomputable abbrev qz307 := (RS361to372.d2 qz469 qz482 qz559)

noncomputable abbrev qz308 := qz568

noncomputable abbrev qz309 := qz569

noncomputable abbrev qz570 := (RS361to372.d2 qz686 qz696 qz730)

noncomputable abbrev qz310 := qz570

noncomputable abbrev qz571 := (@List.cons RS361to372.d1 qz733 qz734)

noncomputable abbrev qz311 := qz571

noncomputable abbrev qz572 := qz733

noncomputable abbrev qz312 := qz572

noncomputable abbrev qz573 := qz734

noncomputable abbrev qz313 := qz573

noncomputable abbrev qz735 := (RS361to372.d2 qz787 qz792 qz797)

noncomputable abbrev qz574 := qz735

noncomputable abbrev qz314 := qz574

noncomputable def Ns360p1807 := @List.IsChain.cons_cons RS361to372.d1 RS361to372.d64 qz307 qz308 qz309 (@Enclosure.dec_le_dec qz170 qz170 707248 1000 707248 1000 qz173 qz173 rfl rfl rfl) (@List.IsChain.cons_cons RS361to372.d1 RS361to372.d64 qz308 qz310 qz311 (@Enclosure.dec_le_dec qz188 qz188 708578 1000 708578 1000 qz191 qz191 rfl rfl rfl) (@List.IsChain.cons_cons RS361to372.d1 RS361to372.d64 qz310 qz312 qz313 (@Enclosure.dec_le_dec qz206 qz206 709907 1000 709907 1000 qz209 qz209 rfl rfl rfl) (@List.IsChain.cons_cons RS361to372.d1 RS361to372.d64 qz312 qz314 (@List.nil RS361to372.d1) (@Enclosure.dec_le_dec qz223 qz223 711236 1000 711236 1000 qz226 qz226 rfl rfl rfl) (@List.IsChain.singleton RS361to372.d1 RS361to372.d64 qz314)))) 

noncomputable abbrev qz315 := (@List.cons RS361to372.d1 qz568 qz569)

noncomputable def Ns360p1808 := @List.IsChain.cons_cons RS361to372.d1 RS361to372.d64 (RS361to372.d2 qz134 qz152 qz282) qz307 qz315 (@Enclosure.dec_le_dec qz152 qz152 705917 1000 705917 1000 qz155 qz155 rfl rfl rfl) Ns360p1807 

noncomputable def Ns360p1809 := @List.IsChain.cons_cons RS361to372.d1 RS361to372.d64 (RS361to372.d2 qz4 qz35 qz258) (RS361to372.d2 qz35 qz62 qz262) (@List.cons RS361to372.d1 (RS361to372.d2 qz62 qz80 qz266) (@List.cons RS361to372.d1 (RS361to372.d2 qz80 qz98 qz270) (@List.cons RS361to372.d1 qz306 Ns360p1804))) (@Enclosure.dec_le_dec qz35 qz35 697923 1000 697923 1000 qz38 qz38 rfl rfl rfl) (@List.IsChain.cons_cons RS361to372.d1 RS361to372.d64 (RS361to372.d2 qz35 qz62 qz262) (RS361to372.d2 qz62 qz80 qz266) (@List.cons RS361to372.d1 (RS361to372.d2 qz80 qz98 qz270) (@List.cons RS361to372.d1 qz306 Ns360p1804)) (@Enclosure.dec_le_dec qz62 qz62 699257 1000 699257 1000 qz65 qz65 rfl rfl rfl) (@List.IsChain.cons_cons RS361to372.d1 RS361to372.d64 (RS361to372.d2 qz62 qz80 qz266) (RS361to372.d2 qz80 qz98 qz270) (@List.cons RS361to372.d1 qz306 Ns360p1804) (@Enclosure.dec_le_dec qz80 qz80 700590 1000 700590 1000 qz83 qz83 rfl rfl rfl) (@List.IsChain.cons_cons RS361to372.d1 RS361to372.d64 (RS361to372.d2 qz80 qz98 qz270) qz306 Ns360p1804 (@Enclosure.dec_le_dec qz98 qz98 701923 1000 701923 1000 qz101 qz101 rfl rfl rfl) (Ns360p1805 (@Enclosure.dec_le_dec qz116 qz116 703255 1000 703255 1000 qz119 qz119 rfl rfl rfl) (Ns360p1806 Ns360p1808))))) 

noncomputable abbrev qz575 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz576 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns360p1803 Ns360p1809)

noncomputable abbrev qz577 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns360p1803 Ns360p1809))

theorem RS361to372.d65 : Zeta.Certificates.BatchSpec 12 696589 1000 712564 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz575 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 12) (And (@Eq (Option Real) (@Option.map qz575 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz575 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz575 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz575 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz240)))) qz576 (@And.intro (@Eq Nat (@List.length qz575 qz577) 12) (And (@Eq (Option Real) (@Option.map qz575 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz575 qz577)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz575 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz575 qz577)) (@Option.some Real qz240))) (@Eq.refl Nat 12) (@And.intro (@Eq (Option Real) (@Option.map qz575 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz575 qz577)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz575 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz575 qz577)) (@Option.some Real qz240)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz240))))

theorem solution : Zeta.Certificates.BatchSpec 12 696589 1000 712564 1000 := RS361to372.d65
#print axioms solution
#check solution
