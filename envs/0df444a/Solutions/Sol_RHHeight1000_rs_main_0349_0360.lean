-- Prove2me | solution 1 for RHHeight1000.rs_main_0349_0360
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:25:05.99735+00:00
-- url     : https://prove2.me/submissions/d10485d7-3f0d-4ef9-84a9-d337bd018ea9

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

noncomputable def RS349to360.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS349to360.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS349to360.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS349to360.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS349to360.d2 a b h 

theorem RS349to360.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS349to360.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS349to360.d3 a b h)) 

noncomputable def Ns348p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns348p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns348p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns348p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns348p0 Ns348p1 Ns348p2 Ns348p1 307286088 268435456 1 84640000 307286088 268435456 1 84640000 153643044 134217728 2 134217728 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns348p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns348p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns348p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns348p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns348p8 := nat_lit 167537954069964697925743468333314178468718661948561187618563575975392713740913527107727581163208035826476740967700482432525301063254420572874757592895482956004842597348203117269212172556829666669574421653274845612596416189641484794702002223261246862056663160605878293700340502480877986491439034432953223334258717026053687371824342493299510132312376251152844516906794910572262907940062760396663270105627554083664899640691826599584783763757814813433640133591539937449421955686657622469485188711283992428713614179785896055117030632677201478317872225272595773536303110412989181984739022579128493081560758017763072115692678596043664844667144619713966763611484179303468167142547433165016751768184247559143333542643815355903304572487929375 

noncomputable def Ns348p9 := nat_lit 17907736863639440849562382641391758203535690054199171304015283257442503423240620144819838407313611418261944516207295868563739563278604805791797182761045687776939279949642059267526948014748996956777332184087524644234759874591635243045607722412471722018588244283882362848653445974523544951031470230725674276297342086185092985546835544820091590454230569790847977790484558207349923322458845585052164126500435851662252152223728079705692133047658564669873831757357628115566356048471439549797170528303905720944834637690907185213991407615774042056720704508980680095051114888612186461088301140868302968264130481206655302741383410655080008578156649725227045954510069588220729495895148666460653631514375880874422615237249871322129146554264800 

noncomputable def Ns348p10 := nat_lit 55164646516618494962085419356369025784335016154267579706247610053041231157772817011486486467101704279863254798704146668052276438579475100451766223896220272709675360577301802978530276301158911649961092601279696986330335403118086533522541958716560166657634553390183479955483588238249446822384543398154260439705049143284278540285021213103458182619368483938376641172730818250587232036579805400979202432024046862170503602539341971086573372247299262086029843105216008583038025403798224342134620653974939981235680083776396058604459065501719125356177784467570909658245422960948263734871602033841948787585406240093531041217463298165642337705122589129757920995868559518021463265498464182174549661735402095023640043996665674913376875 

noncomputable def Ns348p11 := BSN.log_dyadic_bound Ns348p6 Ns348p7 15 14 Ns348p8 268435456 84640000 Ns348p9 Ns348p10 307286088 Ns348p4 Ns348p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns348p6) (BSN.artanhQ Ns348p7) 0 14 Ns348p9 Ns348p8 Ns348p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns348p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns348p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns348p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns348p15 := nat_lit 167537954069966963268140139327979112712430526945422964221951926912223381190141639739514890494967825643602350173964944759828460064784215684919760383437959917620844610857567326816719640593037578236900835917107172977527392439886629774248115214831425484905681376157923696414882114961796820014026232307332015059110330001516939277521159573995394989771587717775443426002499543257897301982481613760098955890450106043861450716722534643739571053080256776912576113428445260435254713579381797931690799491102381747484553243404562568585572234105168360737285205910186933811836504830286397217473365026331067977496463917110493303316865058355012304571237619413071097245713770677768486493924969821719264401216877841676972336093778875903304572487929375 

noncomputable def Ns348p16 := nat_lit 17907736863639702486765313263906285882628955290251965205176678923530777959693011244026517850256414903756943142851250712732214241881959351517241344993825585048584379523049477943740273636414656012170312373198803997844271825165684859407921203335666024680974464565759223251918458072775203410604089667122984485578465112081892102496937045858735135721609691262763214794451343726045584198128451069547586972080574568545086657023793200560105564573365716615162566961587407171758966967827997201380802107846920231945878242774600967607639551032178207663699700360114112068650063802902647517702890145150192721997537569966984346993833704449560383184487996362781528900358997452380059737141488304159449328022742959995775545894292303322129146554264800 

noncomputable def Ns348p17 := nat_lit 55164646516619937449385584700664297411818070214438189962773666351465523500358685366424500506990751111492356556545320273548942244833046464529601272738875466881799996765940232256588350019911833156887888425998391295014189841212513610526066550079316346993943774342801096070086869790972589246312728227659319758310961510342377923950694747797317942483020440897997204711883064182772445608288320382376665481938194224815739627075458138172195220395246294556718284728034954178416253903237031389214179719385823921869528509431462690683227358218086518156757026652846493301460983550768858152506145788622699720737745394141184245149692548799188169247529408201840608223422296381897323845616153036586108326210125693898345963996665674913376875 

noncomputable def Ns348p18 := BSN.log_dyadic_bound Ns348p13 Ns348p14 15 14 Ns348p15 268435456 84640000 Ns348p16 Ns348p17 307286088 Ns348p12 Ns348p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns348p13) (BSN.artanhQ Ns348p14) 0 14 Ns348p16 Ns348p15 Ns348p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns348p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 153643044 134217728 2 134217728 38410761 33554432 1 67108864 (Ns348p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns348p0 Ns348p1 307286088 268435456 1 84640000 Bool.false (BSN.logfrac_isNear Ns348p4 Ns348p5 1 Ns348p0 Ns348p1 307286088 268435456 84640000 rfl rfl rfl (Ns348p11 rfl))) (BSN.isNear_log_sfrac Ns348p2 Ns348p1 307286088 268435456 1 84640000 Bool.false (BSN.logfrac_isNear Ns348p12 Ns348p5 1 Ns348p2 Ns348p1 307286088 268435456 84640000 rfl rfl rfl (Ns348p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS349to360.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 67108864 := Ns348p19 

noncomputable def Ns348p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 16777216 5290000 385100712855 135135 11629079 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz578 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz316 := qz578

noncomputable abbrev qz0 := qz316

theorem RS349to360.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 11629079 16777216 1 5290000 := BSN.isNear_log_sfrac 2 1 11629079 16777216 1 5290000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 11629079 16777216 5290000 rfl rfl rfl (Ns348p20 rfl)) 

theorem RS349to360.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 186065264 268435456 51 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 11629079 16777216 1 5290000 186065264 268435456 51 268435456 RS349to360.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz579 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz319 := qz579

noncomputable def Ns348p21 := @Enclosure.Real.IsNear.inv_image qz317 47453133 33554432 1 33554432 11863282 11863284 16777216 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 47453133 33554432 1 33554432 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 47453133 33554432 1 33554432 47453133 33554432 1 33554432 (BSN.sqrt_enclosure 2 1 23726566 23726567 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS349to360.d8 : Enclosure.Real.IsNear qz320 Bool.false 11863283 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 23726566 33554432 2 33554432 11863283 16777216 1 16777216 (Ns348p21 rfl rfl) rfl 

theorem RS349to360.d9 : Enclosure.Real.IsNear qz320 Bool.false 189812528 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 11863283 16777216 1 16777216 189812528 268435456 16 268435456 RS349to360.d8 rfl 

noncomputable def Ns348p22 := BSN.log_dyadic_bound 1 2 13 12 132638213186519040000 16777216 5290000 13079757671720842725 316234143225 18431655 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 1) (BSN.artanhQ 2) 0 12 13079757671720842725 132638213186519040000 316234143225 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS349to360.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 18431655 16777216 1 5290000 := BSN.isNear_log_sfrac 3 1 18431655 16777216 1 5290000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 18431655 16777216 5290000 rfl rfl rfl (Ns348p22 rfl)) 

theorem RS349to360.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 294906480 268435456 51 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 18431655 16777216 1 5290000 294906480 268435456 51 268435456 RS349to360.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns348p23 := @Enclosure.Real.IsNear.inv_image qz321 58117981 33554432 1 33554432 9686330 9686331 16777216 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 58117981 33554432 1 33554432 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 58117981 33554432 1 33554432 58117981 33554432 1 33554432 (BSN.sqrt_enclosure 3 1 29058990 29058991 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS349to360.d12 : Enclosure.Real.IsNear qz323 Bool.false 19372661 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 19372661 33554432 1 33554432 19372661 33554432 1 33554432 (Ns348p23 rfl rfl) rfl 

theorem RS349to360.d13 : Enclosure.Real.IsNear qz323 Bool.false 154981288 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 19372661 33554432 1 33554432 154981288 268435456 8 268435456 RS349to360.d12 rfl 

noncomputable def Ns348p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns348p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns348p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns348p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns348p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns348p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns348p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns348p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns348p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns348p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns348p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns348p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns348p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns348p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns348p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns348p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns348p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns348p25 Ns348p26 Ns348p27 Ns348p28 200200021673987500790625 Ns348p29 Ns348p30 Ns348p31 Ns348p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns348p32 Ns348p33 151412625 Ns348p34 Ns348p35 1322214852783825 Ns348p27 Ns348p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns348p32 Ns348p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns348p34 Ns348p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns348p36 Ns348p37 1267389585 Ns348p38 Ns348p39 1927077560082675 Ns348p29 Ns348p30 Ns348p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns348p36 Ns348p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns348p38 Ns348p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS349to360.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns348p24 Ns348p25 1 Ns348p26 := Ns348p40 rfl rfl rfl 

noncomputable def Ns348p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns348p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns348p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns348p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns348p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns348p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns348p25 Ns348p26 Ns348p42 Ns348p43 9945 Ns348p44 Ns348p45 65835 Ns348p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns348p42 Ns348p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns348p44 Ns348p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS349to360.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns348p41 Ns348p25 1 Ns348p26 := Ns348p46 rfl 

noncomputable def Ns348p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns348p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS349to360.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns348p47 Ns348p25 1 Ns348p48 := BSN.pi_combine Ns348p24 Ns348p41 Ns348p25 Ns348p26 Ns348p48 Ns348p47 rfl rfl rfl rfl RS349to360.d14 RS349to360.d15 

theorem RS349to360.d17 : Enclosure.Real.IsNear Real.pi Bool.false 14148475504056880 4503599627370496 1 4503599627370496 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns348p47 Ns348p25 1 Ns348p48 14148475504056880 4503599627370496 1 4503599627370496 RS349to360.d16 rfl 

noncomputable def Ns348p49 := nat_lit 147443727375074537121690809726715087890625 

noncomputable def Ns348p50 := nat_lit 22889945643899497138335355216896171420000 

noncomputable def Ns348p51 := nat_lit 355592320898650075318906513310625 

noncomputable def Ns348p52 := BSN.log_dyadic_bound 3 5 17 16 Ns348p49 16777216 5290000 Ns348p50 Ns348p51 23258159 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 3) (BSN.artanhQ 5) 0 16 Ns348p50 Ns348p49 Ns348p51 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS349to360.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 23258159 16777216 1 5290000 := BSN.isNear_log_sfrac 4 1 23258159 16777216 1 5290000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 23258159 16777216 5290000 rfl rfl rfl (Ns348p52 rfl)) 

theorem RS349to360.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 372130544 268435456 51 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 23258159 16777216 1 5290000 372130544 268435456 51 268435456 RS349to360.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns348p53 := @Enclosure.Real.IsNear.inv_image qz325 67108865 33554432 1 33554432 8388607 8388608 16777216 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 67108865 33554432 1 33554432 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 67108865 33554432 1 33554432 67108865 33554432 1 33554432 (BSN.sqrt_enclosure 4 1 33554432 33554433 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS349to360.d20 : Enclosure.Real.IsNear qz327 Bool.false 16777215 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 16777215 33554432 1 33554432 16777215 33554432 1 33554432 (Ns348p53 rfl rfl) rfl 

theorem RS349to360.d21 : Enclosure.Real.IsNear qz327 Bool.false 134217720 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 16777215 33554432 1 33554432 134217720 268435456 8 268435456 RS349to360.d20 rfl 

noncomputable def Ns348p54 := nat_lit 61697213297292266380244507781205789317049021875 

noncomputable def Ns348p55 := nat_lit 12776162289178456695994184080609776001208236500 

noncomputable def Ns348p56 := nat_lit 57671893776295590731569354191667200000 

noncomputable def Ns348p57 := nat_lit 885951608314392539099884620 

noncomputable def Ns348p58 := nat_lit 1286943652057122751813246125 

noncomputable def Ns348p59 := BSN.log_dyadic_bound 2 3 22 21 Ns348p54 16777216 5290000 Ns348p55 Ns348p56 27001887 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 21 10 9927050056596826020 47940881637414340575 686533194547200 Ns348p57 Ns348p58 84004523356416638976000 Ns348p55 Ns348p54 Ns348p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base11 (BSN.artanhP 2) (BSN.artanhQ 3) 10 21 Ns348p57 Ns348p58 84004523356416638976000 rfl rfl rfl rfl)) rfl rfl 

theorem RS349to360.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 5290000 := BSN.isNear_log_sfrac 5 1 27001887 16777216 1 5290000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 27001887 16777216 5290000 rfl rfl rfl (Ns348p59 rfl rfl)) 

theorem RS349to360.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 432030192 268435456 51 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 27001887 16777216 1 5290000 432030192 268435456 51 268435456 RS349to360.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns348p60 := @Enclosure.Real.IsNear.inv_image qz328 75029991 33554432 1 33554432 7502998 7503000 16777216 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 75029991 33554432 1 33554432 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 75029991 33554432 1 33554432 75029991 33554432 1 33554432 (BSN.sqrt_enclosure 5 1 37514995 37514996 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS349to360.d24 : Enclosure.Real.IsNear qz329 Bool.false 7502999 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 15005998 33554432 2 33554432 7502999 16777216 1 16777216 (Ns348p60 rfl rfl) rfl 

theorem RS349to360.d25 : Enclosure.Real.IsNear qz329 Bool.false 120047984 268435456 16 268435456 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 7502999 16777216 1 16777216 120047984 268435456 16 268435456 RS349to360.d24 rfl 

noncomputable def Ns348p61 := BSN.log_dyadic_bound 2 10 5 4 94500000000 16777216 5290000 1291130880 26880 6802575 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 10) 0 4 1291130880 94500000000 26880 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz579)

theorem RS349to360.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 50000000529 264500000000000000 := BSN.isNear_log_sfrac 6 1 4034683545132279 2251799813685248 50000000529 264500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 1083052117253279893684224 604462909807314587353088 1000000010580000 5290000000000000000000 4034683545132279 2251799813685248 50000000529 264500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 6802575 16777216 24973259072661432 36028797018963968 5290000 1000000000000000 rfl rfl rfl rfl (Ns348p61 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS349to360.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 480971758 268435456 52 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683545132279 2251799813685248 50000000529 264500000000000000 480971758 268435456 52 268435456 RS349to360.d26 rfl 

noncomputable abbrev qz331 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns348p62 := @Enclosure.Real.IsNear.inv_image qz331 82191237 33554432 1 33554432 6849269 6849270 16777216 (@Enclosure.Real.IsNear.of_eq qz331 (Real.sqrt qz330) Bool.false 82191237 33554432 1 33554432 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 82191237 33554432 1 33554432 82191237 33554432 1 33554432 (BSN.sqrt_enclosure 6 1 41095618 41095619 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS349to360.d28 : Enclosure.Real.IsNear qz332 Bool.false 13698539 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 13698539 33554432 1 33554432 13698539 33554432 1 33554432 (Ns348p62 rfl rfl) rfl 

theorem RS349to360.d29 : Enclosure.Real.IsNear qz332 Bool.false 109588312 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 13698539 33554432 1 33554432 109588312 268435456 8 268435456 RS349to360.d28 rfl 

noncomputable def Ns348p63 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 16777216 5290000 11010900719820672 5524329195 9388794 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz579)

theorem RS349to360.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 50000000529 264500000000000000 := BSN.isNear_log_sfrac 7 1 4381799983422711 2251799813685248 50000000529 264500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 1176230476650867868041216 604462909807314587353088 1000000010580000 5290000000000000000000 4381799983422711 2251799813685248 50000000529 264500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 9388794 16777216 24973259072661432 36028797018963968 5290000 1000000000000000 rfl rfl rfl rfl (Ns348p63 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS349to360.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 522351262 268435456 52 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 50000000529 264500000000000000 522351262 268435456 52 268435456 RS349to360.d30 rfl 

noncomputable abbrev qz334 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns348p64 := @Enclosure.Real.IsNear.inv_image qz334 88776683 33554432 1 33554432 6341191 6341192 16777216 (@Enclosure.Real.IsNear.of_eq qz334 (Real.sqrt qz333) Bool.false 88776683 33554432 1 33554432 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 88776683 33554432 1 33554432 88776683 33554432 1 33554432 (BSN.sqrt_enclosure 7 1 44388341 44388342 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz335 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS349to360.d32 : Enclosure.Real.IsNear qz335 Bool.false 12682383 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 12682383 33554432 1 33554432 12682383 33554432 1 33554432 (Ns348p64 rfl rfl) rfl 

theorem RS349to360.d33 : Enclosure.Real.IsNear qz335 Bool.false 101459064 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 12682383 33554432 1 33554432 101459064 268435456 8 268435456 RS349to360.d32 rfl 

noncomputable def Ns348p65 := nat_lit 1256945285058001618599936 

noncomputable def Ns348p66 := BSN.log_dyadic_bound 0 16 1 0 1 16777216 5290000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz579)

theorem RS349to360.d34 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 100000001587 529000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 100000001587 529000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false Ns348p65 604462909807314587353088 1000000015870000 5290000000000000000000 9364972152248037 4503599627370496 100000001587 529000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 16777216 24973259072661432 36028797018963968 5290000 1000000000000000 rfl rfl rfl rfl (Ns348p66 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS349to360.d35 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 558195838 268435456 52 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 100000001587 529000000000000000 558195838 268435456 52 268435456 RS349to360.d34 rfl 

noncomputable abbrev qz337 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns348p67 := @Enclosure.Real.IsNear.inv_image qz337 94906265 33554432 1 33554432 5931641 5931642 16777216 (@Enclosure.Real.IsNear.of_eq qz337 (Real.sqrt qz336) Bool.false 94906265 33554432 1 33554432 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 94906265 33554432 1 33554432 94906265 33554432 1 33554432 (BSN.sqrt_enclosure 8 1 47453132 47453133 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz338 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS349to360.d36 : Enclosure.Real.IsNear qz338 Bool.false 11863283 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 11863283 33554432 1 33554432 11863283 33554432 1 33554432 (Ns348p67 rfl rfl) rfl 

theorem RS349to360.d37 : Enclosure.Real.IsNear qz338 Bool.false 94906264 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 11863283 33554432 1 33554432 94906264 268435456 8 268435456 RS349to360.d36 rfl 

noncomputable def Ns348p68 := nat_lit 1328140746012062765809664 

noncomputable def Ns348p69 := BSN.log_dyadic_bound 1 17 3 2 1252815 16777216 5290000 1448 3 1976071 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz579)

theorem RS349to360.d38 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 100000001587 529000000000000000 := BSN.isNear_log_sfrac 9 1 9895419672221413 4503599627370496 100000001587 529000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false Ns348p68 604462909807314587353088 1000000015870000 5290000000000000000000 9895419672221413 4503599627370496 100000001587 529000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 1976071 16777216 24973259072661432 36028797018963968 5290000 1000000000000000 rfl rfl rfl rfl (Ns348p69 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS349to360.d39 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 589812974 268435456 52 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 100000001587 529000000000000000 589812974 268435456 52 268435456 RS349to360.d38 rfl 

noncomputable abbrev qz340 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable def Ns348p70 := @Enclosure.Real.IsNear.inv_image qz340 100663297 33554432 1 33554432 5592405 5592406 16777216 (@Enclosure.Real.IsNear.of_eq qz340 (Real.sqrt qz339) Bool.false 100663297 33554432 1 33554432 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz339) Bool.false 100663297 33554432 1 33554432 100663297 33554432 1 33554432 (BSN.sqrt_enclosure 9 1 50331648 50331649 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz341 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS349to360.d40 : Enclosure.Real.IsNear qz341 Bool.false 11184811 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 11184811 33554432 1 33554432 11184811 33554432 1 33554432 (Ns348p70 rfl rfl) rfl 

theorem RS349to360.d41 : Enclosure.Real.IsNear qz341 Bool.false 89478488 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 11184811 33554432 1 33554432 89478488 268435456 8 268435456 RS349to360.d40 rfl 

noncomputable def Ns348p71 := nat_lit 1391827265235416537628672 

noncomputable def Ns348p72 := BSN.log_dyadic_bound 2 18 4 3 3571283520 16777216 5290000 14806464 960 3743727 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 18) 0 3 14806464 3571283520 960 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz737 := (Enclosure.sfrac Bool.false 10 1)

noncomputable abbrev qz580 := qz737

noncomputable abbrev qz342 := qz580

noncomputable abbrev qz1 := qz342

noncomputable abbrev qz343 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10) qz579)

theorem RS349to360.d42 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 10369921216632549 4503599627370496 100000001587 529000000000000000 := BSN.isNear_log_sfrac 10 1 10369921216632549 4503599627370496 100000001587 529000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz343) Bool.false Ns348p71 604462909807314587353088 1000000015870000 5290000000000000000000 10369921216632549 4503599627370496 100000001587 529000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 3743727 16777216 24973259072661432 36028797018963968 5290000 1000000000000000 rfl rfl rfl rfl (Ns348p72 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS349to360.d43 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 618095470 268435456 52 268435456 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 10369921216632549 4503599627370496 100000001587 529000000000000000 618095470 268435456 52 268435456 RS349to360.d42 rfl 

noncomputable abbrev qz344 := (Real.sqrt (@Nat.cast Real Real.instNatCast 10))

noncomputable def Ns348p73 := @Enclosure.Real.IsNear.inv_image qz344 106108431 33554432 1 33554432 5305421 5305422 16777216 (@Enclosure.Real.IsNear.of_eq qz344 (Real.sqrt qz343) Bool.false 106108431 33554432 1 33554432 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz343) Bool.false 106108431 33554432 1 33554432 106108431 33554432 1 33554432 (BSN.sqrt_enclosure 10 1 53054215 53054216 16777216 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz345 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

theorem RS349to360.d44 : Enclosure.Real.IsNear qz345 Bool.false 10610843 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz345 Bool.false 10610843 33554432 1 33554432 10610843 33554432 1 33554432 (Ns348p73 rfl rfl) rfl 

theorem RS349to360.d45 : Enclosure.Real.IsNear qz345 Bool.false 84886744 268435456 8 268435456 := @Enclosure.Real.IsNear.recentre' qz345 Bool.false 10610843 33554432 1 33554432 84886744 268435456 8 268435456 RS349to360.d44 rfl 

theorem RS349to360.d46 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz738 := (@instHMul Real Real.instMul)

noncomputable abbrev qz581 := (@HMul.hMul Real Real Real qz738 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz346 := qz581

noncomputable abbrev qz2 := qz346

theorem RS349to360.d47 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS349to360.d46 rfl 

noncomputable abbrev qz347 := (@Inv.inv Real Real.instInv qz581)

noncomputable abbrev qz3 := qz347

theorem RS349to360.d48 : Enclosure.Real.IsNear qz3 Bool.false 5340353 33554432 1 33554432 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 5340353 33554432 1 33554432 5340353 33554432 1 33554432 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 2670176 2670177 16777216 RS349to360.d47 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns348p74 := nat_lit 312266483679755289755648000 

noncomputable def Ns348p75 := nat_lit 644384967903915255587370172416 

noncomputable abbrev qz739 := (Enclosure.sfrac Bool.false 681206 1000)

noncomputable abbrev qz582 := qz739

noncomputable abbrev qz348 := qz582

noncomputable abbrev qz4 := qz348

noncomputable abbrev qz583 := qz738

noncomputable abbrev qz349 := qz583

noncomputable abbrev qz5 := qz349

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 10)

noncomputable abbrev qz7 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz740 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 681206 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz584 := qz740

noncomputable abbrev qz350 := qz584

noncomputable abbrev qz8 := qz350

noncomputable abbrev qz9 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz741 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 681206 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz585 := qz741

noncomputable abbrev qz351 := qz585

noncomputable abbrev qz10 := qz351

noncomputable abbrev qz586 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz8 qz9))

noncomputable def Ns348p76 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HMul.hMul Real Real Real qz5 qz586 (Zeta.RiemannSiegel.correction qz10)) 264666945 67108864 153413 134217728 289944005134155446529 2361183241434822606848 1596065757020011268927 Ns348p74 Ns348p75 

noncomputable def Ns348p77 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin BSN.quadSignPos 9 10 681206 1000 199 268435456 134217728 4503599627370496 Bool.false 336904159516 2456 618095470 52 84886744 8 

noncomputable def Ns348p78 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 681206 1000 102 153 268435456 134217728 4503599627370496 Bool.false 336904159516 2456 

noncomputable def Ns348p79 := Ns348p78 558195838 52 94906264 8 589812974 52 89478488 8 Bool.true 476464590 115386 Bool.true 333136821 Bool.true 366390725 14148475504056880 1 Bool.false 86924946 Bool.true Bool.false 262766245 Bool.true Bool.true 594785950 

noncomputable def Ns348p80 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 681206 1000 21 44 268435456 134217728 4503599627370496 Bool.false 336904159516 2456 

noncomputable def Ns348p81 := Ns348p80 480971758 52 109588312 8 522351262 52 101459064 8 Bool.true 385770908 85585 Bool.false 408506142 Bool.true 371727422 14148475504056880 1 Bool.false 268113364 Bool.true Bool.false 49642595 Bool.false Bool.true 476464590 

noncomputable def Ns348p82 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 681206 1000 197 101 268435456 134217728 4503599627370496 Bool.false 336904159516 2456 

noncomputable def Ns348p83 := Ns348p82 372130544 51 134217720 8 432030192 51 120047984 16 Bool.true 250908311 50323 Bool.false 340086791 Bool.false 15200289 14148475504056880 1 Bool.false 256136921 Bool.true Bool.false 15192167 Bool.true Bool.true 385770908 

noncomputable def Ns348p84 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 681206 1000 498 322 268435456 134217728 4503599627370496 Bool.false 336904159516 2456 

noncomputable def Ns348p85 := Ns348p84 186065264 51 189812528 16 294906480 51 154981288 8 Bool.true 125672 2515 Bool.false 169986010 Bool.false 238403999 14148475504056880 1 Bool.false 216388548 Bool.true Bool.false 169347506 Bool.true Bool.true 250908311 

noncomputable def Ns348p86 := nat_lit 79425561443787766173588240249473346407768632699060463 

noncomputable def Ns348p87 := nat_lit 63283982111725533643010172733229633528372926611456 

noncomputable def Ns348p88 := nat_lit 70409968946202935930211864212480000 

noncomputable def Ns348p89 := nat_lit 287782232188535697982889235996615905280 

noncomputable abbrev qz352 := (@Eq.refl Real qz582)

noncomputable abbrev qz11 := qz352

noncomputable def Ns348p90 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 681206 1000 1856167457744 16000000 1362412 4000 2000 Ns348p88 Ns348p89 qz11 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns348p91 := nat_lit 1626635498368773451235087160309214134431101597676758282240 

noncomputable abbrev qz742 := (@instHSub Real Real.instSub)

noncomputable abbrev qz587 := qz742

noncomputable abbrev qz353 := qz587

noncomputable abbrev qz588 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz743 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz744 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz589 := (@HSub.hSub Real Real Real qz742 qz743 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz744 (@Nat.cast Real Real.instNatCast 1362412))))

noncomputable abbrev qz354 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 681206 4000) (Real.log (Enclosure.sfrac Bool.false 1856167457744 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz589))

noncomputable abbrev qz590 := (Enclosure.sfrac Bool.false 681206 2000)

noncomputable abbrev qz12 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz354 qz590) (@HMul.hMul Real Real Real qz349 qz590 (Real.log Real.pi)))

noncomputable def Ns348p92 := @Enclosure.Real.IsNear.addLit_ft_p qz12 (Enclosure.sfrac Bool.true Ns348p88 Ns348p89) 5652314957378675883 4503599627370496 9909547664443806383 1083392000000000000000000 Ns348p88 Ns348p89 0 1 Ns348p91 

noncomputable def Ns348p93 := nat_lit 23707527234993209770770432000000 

noncomputable abbrev qz13 := (@HSub.hSub Real Real Real qz353 qz354 qz590)

noncomputable def Ns348p94 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (@HMul.hMul Real Real Real qz5 qz590 (Real.log Real.pi)) 926032673896917215103 562949953421312000 2153770191498021 529000000000000000000 13082820428883 33554432000 340603 67108864000 Ns348p93 5652314957378675883 4503599627370496 

noncomputable def Ns348p95 := nat_lit 1852065347793834430206000 

noncomputable abbrev qz14 := qz354

noncomputable def Ns348p96 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz590 1117775116882076346239 562949953421312000 2153770191498021 529000000000000000000 681206 2000 0 1 Ns348p95 926032673896917215103 562949953421312000 2153770191498021 529000000000000000000 

noncomputable def Ns348p97 := nat_lit 2517005799937065822805912505414582272 

noncomputable def Ns348p98 := nat_lit 56391242775323740410478592 

noncomputable def Ns348p99 := nat_lit 4835703278458516698824704 

noncomputable def Ns348p100 := nat_lit 6171177758378107054221536466229201478607131739995041228435265115964966345299560841404911845623690731438680054280289333081428724648329789435517566052398915637098936772624975816294400 

noncomputable def Ns348p101 := nat_lit 166814247788089794002365622971721901986977094759252965527261880766203181298906571133961689300713482622223903189770096394043236806716461572151010921809738861199131528423191231856640 

noncomputable def Ns348p102 := nat_lit 6783469520055230219640878214094924130338348166214650563066675581876355098716002601964781734081333648933378705608220090190996237858560622976977259212387589588131114867752960 

noncomputable def Ns348p103 := BSN.log_dyadic_bound 807591457744 2904743457744 8 7 Ns348p100 134217728 42320000 Ns348p101 Ns348p102 76649167 3712334915488 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 807591457744) (BSN.artanhQ 2904743457744) 0 7 Ns348p101 Ns348p100 Ns348p102 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz355 := (Real.log (Enclosure.sfrac Bool.false 1856167457744 16000000))

noncomputable abbrev qz356 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns348p104 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 681206 4000) qz355 681206 4000 0 1 3282402337955063 281474976710656 781250529 33062500000000000 1117996083514508322989 562949953421312000 266096273928987 66125000000000000000 (Enclosure.Real.IsNear.const Bool.false 681206 4000) (BSN.isNear_log_sfrac 1856167457744 16000000 3282402337955063 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1856167457744) qz356)) Bool.false Ns348p98 Ns348p99 1000000677120000 42320000000000000000000 3282402337955063 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 1856167457744 16000000 16 3712334915488 2097152000000 76649167 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns348p103 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p105 := BSN.arctan_dyadic_bound_f 1000 1362412 1 0 16777216 5290000 0 1 1 0 1 1 12314 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1362412) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1362412) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz591 := qz743

noncomputable abbrev qz357 := qz591

noncomputable abbrev qz15 := qz357

noncomputable abbrev qz592 := qz744

noncomputable abbrev qz358 := qz592

noncomputable abbrev qz16 := qz358

noncomputable abbrev qz745 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz593 := qz745

noncomputable abbrev qz359 := qz593

noncomputable abbrev qz17 := (@Enclosure.Real.IsNear.mulLit_ff qz359 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz360 := (@Nat.cast Real Real.instNatCast 1362412)

noncomputable def Ns348p106 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 qz360)) 884279719003555 562949953421312 1 2000000000000000 12314 16777216 1 5290000 14828819684415516966912 883866529727907 562949953421312 200000000529 1058000000000000000 qz17 (Ns348p105 rfl) rfl rfl 

noncomputable abbrev qz361 := (@HMul.hMul Real Real Real qz583 qz588 qz589)

noncomputable abbrev qz18 := qz361

noncomputable abbrev qz362 := qz588

noncomputable abbrev qz19 := qz362

noncomputable abbrev qz363 := qz589

noncomputable abbrev qz20 := qz363

noncomputable abbrev qz364 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns348p107 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 681206 4000) qz355) qz18 1117996083514508322989 562949953421312000 266096273928987 66125000000000000000 883866529727907 2251799813685248 200000000529 4232000000000000000 Ns348p97 1117775116882076346239 562949953421312000 2153770191498021 529000000000000000000 (Ns348p104 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz20 1 4 0 1 883866529727907 562949953421312 200000000529 1058000000000000000 883866529727907 2251799813685248 200000000529 4232000000000000000 qz364 Ns348p106 rfl) 

noncomputable def Ns348p108 := @Ns348p92 Ns348p86 Ns348p87 9909547664443806383 1083392000000000000000000 (@Ns348p94 9909547664443806383 1083392000000000000000000 (Ns348p96 (Ns348p107 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 681206 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz590 (Real.log Real.pi) 681206 2000 0 1 38410761 33554432 1 67108864 13082820428883 33554432000 340603 67108864000 (Enclosure.Real.IsNear.const Bool.false 681206 2000) RS349to360.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns348p88 Ns348p89) 

noncomputable abbrev qz365 := (@instHAdd Real Real.instAdd)

noncomputable def Ns348p109 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns348p86 Ns348p87 9909547664443806383 1083392000000000000000000 42113019939 33554432 77 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz365 qz12 (Enclosure.sfrac Bool.true Ns348p88 Ns348p89)) Bool.false Ns348p86 Ns348p87 9909547664443806383 1083392000000000000000000 Ns348p90 (Ns348p108 rfl rfl)) 

noncomputable def Ns348p110 := nat_lit 7593641027657243377532928 

noncomputable def Ns348p111 := nat_lit 1350875825158312787223041777117579021073275941309986607455977102227769067193721518485470440601385634710576067714544563563732265270083594321 

noncomputable def Ns348p112 := nat_lit 5312452879021523644167342878668926891519915429617346963252719967526930359331948649748578417931730498127901383505799396607174191825394073600 

noncomputable def Ns348p113 := nat_lit 2493693936948041947913079452003522175061518610759842707772491934999324804938561608308318349000456929925416245854024442297399182633041 

noncomputable def Ns348p114 := nat_lit 8175596596087895213557934851048647821354858898904941451214746318217852809059145456080975666600563725042881522857146530560849805286255110225 

noncomputable def Ns348p115 := nat_lit 483433211990958651619228201958872347128312304095178573655997517044950662699207327127120636031787475329639025899027745091252851456110860697600 

noncomputable abbrev qz594 := (BSN.cosEvenQ 68719476736)

noncomputable abbrev qz595 := (BSN.cosOddQ 68719476736)

noncomputable def Ns348p116 := BSN.cos_dyadic_bound_f 107912129403 68719476736 4 3 33554432 10590333 Ns348p111 Ns348p112 Ns348p113 Ns348p114 Ns348p115 Ns348p113 15709 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 107912129403) qz594 0 3 Ns348p111 Ns348p112 Ns348p113 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 107912129403) qz595 0 3 Ns348p114 Ns348p115 Ns348p113 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz366 := (@Nat.cast Real Real.instNatCast 33554432)

noncomputable abbrev qz367 := (@Nat.cast Real Real.instNatCast Ns348p99)

noncomputable def Ns348p117 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 42113019939) qz366) Bool.false 42113019939 33554432 77 8388608 Bool.true 15709 33554432 1 5290000 (Ns348p109 rfl) (Enclosure.sfrac_false_div 42113019939 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 42113019939) qz366) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns348p110) qz367) 226375608064910080 72057594037927936 Bool.false 15709 33554432 199 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q2 42113019939 33554432 226375608064910080 72057594037927936 199 Ns348p110 Ns348p99 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 15709 33554432 Ns348p110 Ns348p99 107912129403 68719476736 10590333 10580000 (Ns348p116 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p118 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns348p86 Ns348p87 9909547664443806383 1083392000000000000000000 336904159516 268435456 2456 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz365 qz12 (Enclosure.sfrac Bool.true Ns348p88 Ns348p89)) Bool.false Ns348p86 Ns348p87 9909547664443806383 1083392000000000000000000 Ns348p90 (Ns348p108 rfl rfl)) 

noncomputable def Ns348p119 := Ns348p85 50323 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 498 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 216388548 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 322 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 169347506 268435456) qz11 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 15709 33554432 25982413 2773483520000 125672 268435456 2515 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 15709 33554432 25982413 2773483520000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 15709 33554432 415718608 44375736320000 15709 33554432 25982413 2773483520000 (Ns348p117 rfl rfl) rfl)) rfl) (Ns348p118 rfl) RS349to360.d7 

noncomputable def Ns348p120 := nat_lit 7283885044690751995170101477070885789132894844821803122295274032800000 

noncomputable def Ns348p121 := nat_lit 1087025049619513796520974048308631508761049663116835882438097565248389120 

noncomputable def Ns348p122 := nat_lit 697116625313216984714875799151713005166663834374572686880100000000 

noncomputable def Ns348p123 := nat_lit 21850260900821629551540874679614353941388351206796660221512061898400000 

noncomputable def Ns348p124 := nat_lit 48916127232878120843443832173888417894247234840257614709714390436177510400 

noncomputable abbrev qz368 := (BSN.cosEvenQ 268435456)

noncomputable abbrev qz369 := (BSN.cosOddQ 268435456)

noncomputable def Ns348p125 := BSN.cos_dyadic_bound_f 169986010 268435456 3 2 268435456 134217728 Ns348p120 Ns348p121 Ns348p122 Ns348p123 Ns348p124 Ns348p122 216388548 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 169986010) qz368 0 2 Ns348p120 Ns348p121 Ns348p122 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 169986010) qz369 0 2 Ns348p123 Ns348p124 Ns348p122 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p126 := nat_lit 28189264284194359946261280872044619258973417286315544972831835322049281 

noncomputable def Ns348p127 := nat_lit 10435380473432173763592687373191736868160131591212304198296140768001 

noncomputable def Ns348p128 := nat_lit 84546922091636215491256657241387474303183931595764210310098913684611841 

noncomputable def Ns348p129 := BSN.cos_dyadic_bound_f 238403999 268435456 3 2 268435456 134217728 Ns348p126 Ns348p121 Ns348p127 Ns348p128 Ns348p124 Ns348p127 169347506 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 238403999) qz368 0 2 Ns348p126 Ns348p121 Ns348p127 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 238403999) qz369 0 2 Ns348p128 Ns348p124 Ns348p127 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p130 := nat_lit 18730400091847866297446699151373443401440242721129872632516026195039128118734778949276774878151705344775784481 

noncomputable def Ns348p131 := nat_lit 871683568514489007341798292243696146469029465094156570908284878217177001794361422139649254553384847460322508800 

noncomputable def Ns348p132 := nat_lit 2393741067537689216567825685724446445982451680017761706924538597077037641718425440555702784015216642081 

noncomputable def Ns348p133 := nat_lit 93602709699118997086676490622683104963476370968642039758662276360284112258346573894833893982752446703858321441 

noncomputable def Ns348p134 := nat_lit 30508924898007115256962940228529365126416031278295479981789970737601195062802649774887723909368469661111287808000 

noncomputable abbrev qz370 := (BSN.sinEvenQ 268435456)

noncomputable abbrev qz371 := (BSN.sinOddQ 268435456)

noncomputable def Ns348p135 := BSN.sin_dyadic_bound_f 340086791 268435456 4 3 268435456 134217728 Ns348p130 Ns348p131 Ns348p132 Ns348p133 Ns348p134 Ns348p132 256136921 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 340086791) qz370 0 3 Ns348p130 Ns348p131 Ns348p132 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 340086791) qz371 0 3 Ns348p133 Ns348p134 Ns348p132 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p136 := nat_lit 53383541365829618611170957441 

noncomputable def Ns348p137 := nat_lit 623075623024179315423659559506411520 

noncomputable def Ns348p138 := nat_lit 4361529361169255207965616916544880640 

noncomputable def Ns348p139 := BSN.sin_dyadic_bound_f 15200289 268435456 2 1 268435456 134217728 Ns348p136 Ns348p137 Ns348p136 Ns348p136 Ns348p138 Ns348p136 15192167 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 15200289) qz370 0 1 Ns348p136 Ns348p137 Ns348p136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 15200289) qz371 0 1 Ns348p136 Ns348p138 Ns348p136 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz596 := (BSN.cos_quad_nat1 101 rfl)

noncomputable def Ns348p140 := Ns348p83 85585 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 197 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 256136921 268435456) BSN.abs_quadSignNeg qz596 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 15192167 268435456) qz11 rfl rfl (Ns348p119 RS349to360.d9 RS349to360.d11 RS349to360.d13 RS349to360.d17 (Ns348p125 rfl rfl) (Ns348p129 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns348p118 rfl) RS349to360.d19 RS349to360.d21 RS349to360.d23 RS349to360.d25 RS349to360.d17 (Ns348p135 rfl rfl) (Ns348p139 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns348p141 := nat_lit 39028537710381172286105662621831610086466178467724525238400341462452714917701949449103053509956044549333979136 

noncomputable def Ns348p142 := nat_lit 21596485786222122220121106050728055492818508493020656002666607562122652201704484330227853548650046427136 

noncomputable def Ns348p143 := nat_lit 194929026507010793445303155332128530662414258367496185771687924757784867713931479695665731777457100484647325696 

noncomputable def Ns348p144 := BSN.sin_dyadic_bound_f 408506142 268435456 4 3 268435456 134217728 Ns348p141 Ns348p131 Ns348p142 Ns348p143 Ns348p134 Ns348p142 268113364 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 408506142) qz370 0 3 Ns348p141 Ns348p131 Ns348p142 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 408506142) qz371 0 3 Ns348p143 Ns348p134 Ns348p142 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p145 := nat_lit 10296580998308122566025141164775498098400619298464215937184410373933430605522609149019314972000196448498487296 

noncomputable def Ns348p146 := nat_lit 67052582193422231333984484018745857420694574238012043916021913709013615522643186318434558042568065189255577600 

noncomputable def Ns348p147 := nat_lit 6961377697180645350194392156072405779659380104715652975179433969188463600148331799839407301839114735616 

noncomputable def Ns348p148 := nat_lit 62374933394584199631700946828328270158221041645283541079775146525516885084934931283764193749068422165337477120 

noncomputable def Ns348p149 := nat_lit 6101784979601423051392588045705873025283206255659095996357994147520239012560529954977544781873693932222257561600 

noncomputable def Ns348p150 := BSN.cos_dyadic_bound_f 371727422 268435456 4 3 268435456 134217728 Ns348p145 Ns348p146 Ns348p147 Ns348p148 Ns348p149 Ns348p147 49642595 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 371727422) qz368 0 3 Ns348p145 Ns348p146 Ns348p147 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 371727422) qz369 0 3 Ns348p148 Ns348p149 Ns348p147 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p151 := Ns348p81 115386 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 21 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268113364 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 44 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 49642595 268435456) qz11 rfl rfl (Ns348p140 rfl rfl) (Ns348p118 rfl) RS349to360.d27 RS349to360.d29 RS349to360.d31 RS349to360.d33 RS349to360.d17 (Ns348p144 rfl rfl) (Ns348p150 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p152 := nat_lit 6636639000307231020909009847838429913507922518504268156912626082919018587634717794406792983064139739975851921 

noncomputable def Ns348p153 := nat_lit 1868407686908525718663199291804748983396530714660669955303125600323126082180893214238128871282405220241 

noncomputable def Ns348p154 := nat_lit 40224421488970295860118247892784963642815447227321807011942820493289956561039053460158744377684517729645305745 

noncomputable def Ns348p155 := BSN.cos_dyadic_bound_f 333136821 268435456 4 3 268435456 134217728 Ns348p152 Ns348p146 Ns348p153 Ns348p154 Ns348p149 Ns348p153 86924946 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 333136821) qz368 0 3 Ns348p152 Ns348p146 Ns348p153 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 333136821) qz369 0 3 Ns348p154 Ns348p149 Ns348p153 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p156 := nat_lit 25240284619695263957729234750113379277778171933509620123118596852536457745208918625317948848003947806744140625 

noncomputable def Ns348p157 := nat_lit 5852395318293147396526262113587014062131383767539253680154150832710757456677946873774588108062744140625 

noncomputable def Ns348p158 := nat_lit 126111962364325108227061158580394225192369510342154511996035433328377096390321170298041958223267306782744140625 

noncomputable def Ns348p159 := BSN.sin_dyadic_bound_f 366390725 268435456 4 3 268435456 134217728 Ns348p156 Ns348p131 Ns348p157 Ns348p158 Ns348p134 Ns348p157 262766245 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 366390725) qz370 0 3 Ns348p156 Ns348p131 Ns348p157 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 366390725) qz371 0 3 Ns348p158 Ns348p134 Ns348p157 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz597 := (BSN.cos_quad_nat1 153 rfl)

noncomputable def Ns348p160 := Ns348p79 141424 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 102 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 86924946 268435456) BSN.abs_quadSignNeg qz597 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 262766245 268435456) qz11 rfl rfl (Ns348p151 rfl) (Ns348p118 rfl) RS349to360.d35 RS349to360.d37 RS349to360.d39 RS349to360.d41 RS349to360.d17 (Ns348p155 rfl rfl) (Ns348p159 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p161 := nat_lit 49010231093374230648514095610543062512406018101601276893311080646830625 

noncomputable def Ns348p162 := nat_lit 9783225446575624168688766434777683578849446968051522941942878087235502080 

noncomputable def Ns348p163 := nat_lit 9739087754123392325286929247983843994638431032640903113215625390625 

noncomputable def Ns348p164 := nat_lit 128344361007235356682343595380258904166024442330140973258393338300590625 

noncomputable def Ns348p165 := nat_lit 179359133187219776425960717970924198945573194414277920602286098265984204800 

noncomputable def Ns348p166 := BSN.sin_dyadic_bound_f 236354995 268435456 3 2 268435456 134217728 Ns348p161 Ns348p162 Ns348p163 Ns348p164 Ns348p165 Ns348p163 206977589 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 236354995) qz370 0 2 Ns348p161 Ns348p162 Ns348p163 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 236354995) qz371 0 2 Ns348p164 Ns348p165 Ns348p163 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz372 := (BSN.cos_quad_nat3 199 rfl)

noncomputable def Ns348p167 := Ns348p77 Bool.true 594785950 141424 Bool.true 236354995 14148475504056880 1 Bool.false 206977589 Bool.false Bool.true 529333890 153413 BSN.abs_quadSignPos qz372 (BSN.sfrac_eq_quadSignPos_mul Bool.false 206977589 268435456) qz11 rfl (Ns348p160 rfl) (Ns348p118 rfl) RS349to360.d43 RS349to360.d45 RS349to360.d17 (Ns348p166 rfl rfl) rfl 

noncomputable def Ns348p168 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) 529333890 268435456 153413 268435456 529333890 268435456 153413 268435456 284183968276807680 264666945 67108864 153413 134217728 (Ns348p167 rfl rfl rfl rfl) 

noncomputable def Ns348p169 := @Enclosure.Real.IsNear.mulLit_ff qz586 (Zeta.RiemannSiegel.correction qz10) 10398609 33554432 1 33554432 27882960608881 70368744177664 1531337587888657 93062664174960640000 289944005134155446529 2361183241434822606848 

noncomputable abbrev qz598 := (@HPow.hPow Real Real Real qz7 qz8 qz9)

noncomputable def Ns348p170 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz598 1 1 0 1 10398609 33554432 1 33554432 10398609 33554432 1 33554432 

noncomputable abbrev qz21 := (@Enclosure.Real.IsNear.of_eq qz350 (@HMul.hMul Real Real Real qz349 qz348 qz347) Bool.false 1818940252859 16777216000 340603 16777216000 (BSN.t_div_two_pi_mk qz348 681206 1000 qz352) (@Enclosure.Real.IsNear.mulLit_ff qz348 qz347 681206 1000 0 1 5340353 33554432 1 33554432 1818940252859 16777216000 340603 16777216000 (Enclosure.Real.IsNear.const Bool.false 681206 1000) RS349to360.d48 rfl))

noncomputable def Ns348p171 := @Enclosure.Real.IsNear.sqrt_image qz8 1818940252859 16777216000 340603 16777216000 174690434 174690467 16777216 qz21 

noncomputable abbrev qz746 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 681206 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz599 := qz746

noncomputable abbrev qz373 := qz599

noncomputable abbrev qz22 := qz373

noncomputable def Ns348p172 := @Enclosure.Real.IsNear.sqrt_image qz22 349380901 33554432 33 33554432 54137040 54137046 16777216 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 349380901 33554432 33 33554432 349380901 33554432 33 33554432 (Ns348p171 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz600 := (Real.sqrt qz746)

noncomputable abbrev qz374 := qz600

noncomputable abbrev qz23 := qz374

noncomputable def Ns348p173 := @Enclosure.Real.IsNear.inv_image qz23 54137043 16777216 3 16777216 5199304 5199305 16777216 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 108274086 33554432 6 33554432 54137043 16777216 3 16777216 (Ns348p172 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns348p174 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz23) Bool.false 10398609 33554432 1 33554432 10398609 33554432 1 33554432 (Ns348p173 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz375 := (@HMul.hMul Real Real Real qz583 qz581 qz585)

noncomputable abbrev qz24 := (Real.cos qz375)

noncomputable abbrev qz601 := (@HMul.hMul Real Real Real qz738 qz741 qz741)

noncomputable abbrev qz602 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz376 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz601 qz585) qz602)

noncomputable abbrev qz25 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz376))

noncomputable def Ns348p175 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz10) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz24) qz25) Bool.false 27882960608881 

noncomputable def Ns348p176 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz24) qz25 9843617 8388608 37 

noncomputable abbrev qz26 := (@Neg.neg Real Real.instNeg (Real.cos qz375))

noncomputable def Ns348p177 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz24) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz26)) Bool.true 9843617 8388608 37 4194304 (BSN.inv_eq_neg_inv_neg qz24) 

noncomputable def Ns348p178 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz26) Bool.false 39374468 33554432 296 33554432 9843617 8388608 

noncomputable def Ns348p179 := @Enclosure.Real.IsNear.recentre' qz24 Bool.true 28594670 33554432 70867152 11093934080000 14297335 16777216 4429197 693370880000 

noncomputable abbrev qz27 := qz375

noncomputable abbrev qz377 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable def Ns348p180 := @Enclosure.Real.IsNear.cos_image qz27 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 43468901) qz377) Bool.false 43468901 16777216 13 2097152 Bool.true 28594670 33554432 1 

noncomputable def Ns348p181 := nat_lit 890540488617308825787485863 

noncomputable def Ns348p182 := nat_lit 144115188075855872000000000000000 

noncomputable def Ns348p183 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz10 884279719003555 140737488355328 1 500000000000000 13836581 33554432 33 33554432 12235407958649928045455 4722366482869645213696 Ns348p181 

noncomputable def Ns348p184 := @Enclosure.Real.IsNear.subLit_ff_p qz22 qz1 349380901 33554432 33 33554432 10 1 0 1 13836581 13836581 33554432 33 

noncomputable abbrev qz378 := (Enclosure.Real.IsNear.const Bool.false 10 1)

noncomputable def Ns348p185 := @Ns348p184 33554432 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 349380901 33554432 33 33554432 349380901 33554432 33 33554432 (Ns348p171 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns348p186 := @Enclosure.Real.IsNear.recentre' qz27 Bool.false 12235407958649928045455 4722366482869645213696 Ns348p181 Ns348p182 43468901 16777216 13 2097152 (@Ns348p183 Ns348p182 RS349to360.d47 (Ns348p185 rfl rfl) rfl) 

noncomputable def Ns348p187 := nat_lit 2466576369429420957499392 

noncomputable def Ns348p188 := nat_lit 2417851639229258349412352 

noncomputable def Ns348p189 := nat_lit 1629430076129849017081455688365032048199348755128852700726047361464948082473032096235237345 

noncomputable def Ns348p190 := nat_lit 180468656028383376705345110207518346455653528001341539704795567934989718275908111313435361280 

noncomputable def Ns348p191 := nat_lit 583388807765108851900502801537967121168514472783440227672659864953084433744215622397921 

noncomputable def Ns348p192 := nat_lit 4266610427032270582786449798324974846135450097143441027247225449769701888822355331513167841 

noncomputable def Ns348p193 := nat_lit 3308592027187028572931327020471169685020314680024594894587918745474811501724982040746314956800 

noncomputable abbrev qz379 := (BSN.sinEvenQ 68719476736)

noncomputable abbrev qz380 := (BSN.sinOddQ 68719476736)

noncomputable def Ns348p194 := BSN.sin_dyadic_bound_f 70104316859 68719476736 3 2 33554432 10590333 Ns348p189 Ns348p190 Ns348p191 Ns348p192 Ns348p193 Ns348p191 28594670 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 70104316859) qz379 0 2 Ns348p189 Ns348p190 Ns348p191 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 70104316859) qz380 0 2 Ns348p192 Ns348p193 Ns348p191 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz381 := (@Nat.cast Real Real.instNatCast Ns348p188)

noncomputable def Ns348p195 := @Ns348p180 5290000 (Ns348p186 rfl) (Enclosure.sfrac_false_div 43468901 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 43468901) qz377) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns348p187) qz381) 226375608064910080 72057594037927936 Bool.false 28594670 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q1 43468901 16777216 226375608064910080 72057594037927936 0 Ns348p187 Ns348p188 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 28594670 33554432 Ns348p187 Ns348p188 70104316859 68719476736 10590333 10580000 (Ns348p194 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p196 := @Enclosure.Real.IsNear.inv_image qz26 14297335 16777216 4429197 693370880000 19687086 19687382 16777216 (@Enclosure.Real.IsNear.neg qz24 Bool.true 14297335 16777216 4429197 693370880000 (Ns348p179 (Ns348p195 rfl rfl) rfl)) 

noncomputable def Ns348p197 := Ns348p177 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz26) Bool.false 9843617 8388608 37 4194304 (@Ns348p178 37 4194304 (Ns348p196 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p198 := @Enclosure.Real.IsNear.recentre' qz25 Bool.true 5665186 16777216 

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz349 qz346 qz376)

noncomputable def Ns348p199 := @Enclosure.Real.IsNear.cos_image qz28 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 64264729)) qz366) Bool.true 64264729 33554432 

noncomputable def Ns348p200 := nat_lit 303481604380931211242970512725 

noncomputable def Ns348p201 := nat_lit 158456325028528675187087900672 

noncomputable def Ns348p202 := nat_lit 54525680861129135489940019955199437 

noncomputable def Ns348p203 := @Enclosure.Real.IsNear.recentre' qz28 Bool.true Ns348p200 Ns348p201 Ns348p202 

noncomputable def Ns348p204 := nat_lit 4835703278458516698824704000000000000000 

noncomputable abbrev qz29 := qz376

noncomputable def Ns348p205 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz29 884279719003555 140737488355328 1 500000000000000 343196386685095 

noncomputable abbrev qz382 := (@HSub.hSub Real Real Real qz587 qz601 qz585)

noncomputable abbrev qz30 := qz382

noncomputable abbrev qz383 := qz602

noncomputable abbrev qz31 := qz383

noncomputable def Ns348p206 := @Enclosure.Real.IsNear.subLit_tf qz30 qz31 272827642507431 1125899906842624 2020511691 1125899906842624 1 16 

noncomputable abbrev qz384 := qz601

noncomputable abbrev qz32 := qz384

noncomputable def Ns348p207 := @Enclosure.Real.IsNear.subLit_ff_n qz32 qz10 191450973769561 1125899906842624 913215435 1125899906842624 13836581 33554432 33 33554432 

noncomputable def Ns348p208 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz10 13836581 33554432 33 33554432 13836581 33554432 33 33554432 191450973769561 1125899906842624 

noncomputable def Ns348p209 := nat_lit 551421789714682063535738400656059237171610564128301722539732022560181972756464355927457909253858721 

noncomputable def Ns348p210 := nat_lit 975743491921780970500323514261193594148711042915413329552712293065467609596717903600577236539801600 

noncomputable def Ns348p211 := nat_lit 4962176022737276360272908111151173759485403063069415644954161501971312110450821377958862644641 

noncomputable def Ns348p212 := nat_lit 3327547350863410963305021093943562922209538262329494281277229009269185685284087167925053009812252065 

noncomputable def Ns348p213 := nat_lit 88792657764882068315529439797768617067532704905302612989296818668957552473301329227652528525121945600 

noncomputable def Ns348p214 := BSN.cos_dyadic_bound_t 64264729 33554432 4 3 16777216 5290000 Ns348p209 Ns348p210 Ns348p211 Ns348p212 Ns348p213 Ns348p211 5665186 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 64264729) (BSN.cosEvenQ 33554432) 0 3 Ns348p209 Ns348p210 Ns348p211 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 64264729) (BSN.cosOddQ 33554432) 0 3 Ns348p212 Ns348p213 Ns348p211 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz385 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns348p215 := @Ns348p198 2038464432 177502945280000 2832593 8388608 127404027 11093934080000 (@Ns348p199 379 33554432 Bool.true 5665186 16777216 1 5290000 (@Ns348p203 Ns348p204 64264729 33554432 379 33554432 (@Ns348p205 1125899906842624 2020511691 1125899906842624 Ns348p200 Ns348p201 Ns348p202 Ns348p204 RS349to360.d47 (@Ns348p206 0 1 5491142186961520 343196386685095 1125899906842624 2020511691 1125899906842624 (@Ns348p207 9154576578235902984192 272827642507431 1125899906842624 2020511691 1125899906842624 (@Ns348p208 913215435 1125899906842624 (Ns348p185 rfl rfl) (Ns348p185 rfl rfl) rfl) (Ns348p185 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 64264729 33554432) (BSN.cos_neg_of_bound 64264729 33554432 Bool.true 5665186 16777216 1 5290000 (Ns348p214 rfl rfl)) rfl rfl) 

noncomputable abbrev qz33 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 10) (Enclosure.sfrac Bool.false 1 1) Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 10 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1))

noncomputable def Ns348p216 := @Ns348p169 1596065757020011268927 Ns348p74 (Ns348p170 qz33 (@Enclosure.Real.IsNear.of_eq qz598 (@Inv.inv Real Real.instInv qz23) Bool.false 10398609 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz8 (BSN.t_div_two_pi_nonneg qz4 681206 1000 qz11)) Ns348p174) rfl) (@Ns348p175 70368744177664 1531337587888657 93062664174960640000 (BSN.correction_mk qz10 (BSN.cos_two_pi_p_ne_zero_mk qz4 681206 1000 10 qz11 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 681206 1000 10 qz11 rfl rfl rfl))) (@Ns348p176 4194304 2832593 8388608 127404027 11093934080000 27882960608881 70368744177664 1531337587888657 93062664174960640000 Ns348p197 (Ns348p215 rfl) rfl)) 

noncomputable abbrev qz34 := qz353

noncomputable def Ns348p217 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 9602084277628589504769 2361183241434822606848 358521628233850927876927 Ns348p74 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HMul.hMul Real Real Real qz5 qz586 (Zeta.RiemannSiegel.correction qz10))) Bool.true 9602084277628589504769 2361183241434822606848 358521628233850927876927 Ns348p74 (BSN.hardyZApproximantRS₀_eq qz4 10 (@BSN.floor_sqrt_eq_dec qz4 681206 1000 10 qz11 rfl rfl rfl)) (@Ns348p76 9602084277628589504769 2361183241434822606848 358521628233850927876927 Ns348p74 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 10)) Bool.true 264666945 67108864 153413 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 10) (Ns348p168 (Ns348p167 rfl rfl rfl rfl) rfl rfl)) (Ns348p216 rfl) rfl rfl)) 

theorem RS349to360.d49 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 9602084277628589504769 2361183241434822606848 358521628233850927876927 Ns348p74 := Ns348p217 

theorem RS349to360.d50 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS349to360.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS349to360.d3 a b h)) 

noncomputable def Ns348p218 := nat_lit 39033310459969411219456000 

noncomputable def Ns348p219 := nat_lit 5421597730070918389122990080 

noncomputable abbrev qz747 := (Enclosure.sfrac Bool.false 682295 1000)

noncomputable abbrev qz603 := qz747

noncomputable abbrev qz386 := qz603

noncomputable abbrev qz35 := qz386

noncomputable abbrev qz748 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 682295 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz604 := qz748

noncomputable abbrev qz387 := qz604

noncomputable abbrev qz36 := qz387

noncomputable abbrev qz749 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 682295 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz605 := qz749

noncomputable abbrev qz388 := qz605

noncomputable abbrev qz37 := qz388

noncomputable abbrev qz606 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz36 qz9))

noncomputable def Ns348p220 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 10) (@HMul.hMul Real Real Real qz5 qz606 (Zeta.RiemannSiegel.correction qz37)) 11231059 16777216 76833 67108864 72005351991684195333 590295810358705651712 200810653446291262257 Ns348p218 Ns348p219 

noncomputable def Ns348p221 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin BSN.quadSignPos 9 10 682295 1000 199 268435456 134217728 4503599627370496 Bool.false 337589194943 2461 618095470 52 84886744 8 

noncomputable def Ns348p222 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 682295 1000 102 153 268435456 134217728 4503599627370496 Bool.false 337589194943 2461 

noncomputable def Ns348p223 := Ns348p222 558195838 52 94906264 8 589812974 52 89478488 8 Bool.false 165372473 115578 Bool.true 255976662 Bool.true 323661627 14148475504056880 1 Bool.false 155360060 Bool.true Bool.false 250745918 Bool.true Bool.false 26862422 

noncomputable def Ns348p224 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 682295 1000 22 44 268435456 134217728 4503599627370496 Bool.false 337589194943 2461 

noncomputable def Ns348p225 := Ns348p224 480971758 52 109588312 8 522351262 52 101459064 8 Bool.false 199842134 85729 Bool.false 148105896 Bool.true 255532519 14148475504056880 1 Bool.false 228603684 Bool.true Bool.false 155722044 Bool.false Bool.false 165372473 

noncomputable def Ns348p226 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 682295 1000 198 101 268435456 134217728 4503599627370496 Bool.false 337589194943 2461 

noncomputable def Ns348p227 := Ns348p226 372130544 51 134217720 8 432030192 51 120047984 16 Bool.false 389757594 50409 Bool.false 198214627 Bool.false 229754837 14148475504056880 1 Bool.false 198519225 Bool.true Bool.false 202712652 Bool.true Bool.false 199842134 

noncomputable def Ns348p228 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 682295 1000 499 323 268435456 134217728 4503599627370496 Bool.false 337589194943 2461 

noncomputable def Ns348p229 := Ns348p228 186065264 51 189812528 16 294906480 51 154981288 8 Bool.false 149370440 2523 Bool.false 230738937 Bool.false 180628841 14148475504056880 1 Bool.false 203356402 Bool.false Bool.false 167303053 Bool.false Bool.false 389757594 

noncomputable def Ns348p230 := nat_lit 16456396907374570350695821156345569771302487384379921 

noncomputable def Ns348p231 := nat_lit 13085372618878060422181170223348990566728938291200 

noncomputable def Ns348p232 := nat_lit 70974570268738818902291448500000000 

noncomputable def Ns348p233 := nat_lit 290553639345560120114812412935845000000 

noncomputable abbrev qz607 := (@Eq.refl Real qz747)

noncomputable abbrev qz389 := qz607

noncomputable abbrev qz38 := qz389

noncomputable def Ns348p234 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz35 682295 1000 1862106868100 16000000 1364590 4000 2000 Ns348p232 Ns348p233 qz38 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns348p235 := nat_lit 82281984536872851753479105781727848856512436921899605000000 

noncomputable abbrev qz608 := (@HSub.hSub Real Real Real qz742 qz743 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz744 (@Nat.cast Real Real.instNatCast 1364590))))

noncomputable abbrev qz390 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 682295 4000) (Real.log (Enclosure.sfrac Bool.false 1862106868100 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz608))

noncomputable abbrev qz609 := (Enclosure.sfrac Bool.false 682295 2000)

noncomputable abbrev qz39 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz390 qz609) (@HMul.hMul Real Real Real qz349 qz609 (Real.log Real.pi)))

noncomputable def Ns348p236 := @Enclosure.Real.IsNear.addLit_ft_p qz39 (Enclosure.sfrac Bool.true Ns348p232 Ns348p233) 283190397147515866609 225179981368524800 3970123027049990399 433356800000000000000000 Ns348p232 Ns348p233 0 1 Ns348p235 

noncomputable def Ns348p237 := nat_lit 3800917169655726046021104435200 

noncomputable abbrev qz40 := (@HSub.hSub Real Real Real qz353 qz390 qz609)

noncomputable def Ns348p238 := @Enclosure.Real.IsNear.subLit_ff_p qz40 (@HMul.hMul Real Real Real qz5 qz609 (Real.log Real.pi)) 371128074740438814193 225179981368524800 431434663760469 105800000000000000000 5241494035299 13421772800 136459 26843545600 Ns348p237 283190397147515866609 225179981368524800 

noncomputable abbrev qz41 := qz390

noncomputable def Ns348p239 := @Enclosure.Real.IsNear.subLit_ff_p qz41 qz609 447947662434357628401 225179981368524800 431434663760469 105800000000000000000 682295 2000 0 1 742256149480877628386000 371128074740438814193 225179981368524800 431434663760469 105800000000000000000 

noncomputable def Ns348p240 := nat_lit 1008688462810428872196313985159528448 

noncomputable def Ns348p241 := nat_lit 56406691491139907932389376 

noncomputable def Ns348p242 := nat_lit 6350202296870398780067982814393918427303304609337785129277534997758246814783318023988466164677575892236133346885890764330245725642290276235560623250650250000000000000000000000000000 

noncomputable def Ns348p243 := nat_lit 173568899519121920973706294116576418749521942296495823183692204038106442895105510025789776158302034040140476734293020797473680135520251253905611002940150000000000000000000000000000 

noncomputable def Ns348p244 := nat_lit 7516304268184852256908066220276435098422966580486034473305427706290773551364050061670086181502899919183271796150314558166317104600596506702043350000000000000000000000000000 

noncomputable def Ns348p245 := BSN.log_dyadic_bound 813530868100 2910682868100 8 7 Ns348p242 134217728 42320000 Ns348p243 Ns348p244 77077955 3724213736200 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 813530868100) (BSN.artanhQ 2910682868100) 0 7 Ns348p243 Ns348p242 Ns348p244 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz391 := (Real.log (Enclosure.sfrac Bool.false 1862106868100 16000000))

noncomputable def Ns348p246 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 682295 4000) qz391 682295 4000 0 1 3283301571566839 281474976710656 781250529 33062500000000000 448036049154439283101 225179981368524800 4635159388557 1150000000000000000 (Enclosure.Real.IsNear.const Bool.false 682295 4000) (BSN.isNear_log_sfrac 1862106868100 16000000 3283301571566839 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1862106868100) qz356)) Bool.false Ns348p241 Ns348p99 1000000677120000 42320000000000000000000 3283301571566839 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 1862106868100 16000000 16 3724213736200 2097152000000 77077955 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns348p245 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p247 := BSN.arctan_dyadic_bound_f 1000 1364590 1 0 16777216 5290000 0 1 1 0 1 1 12294 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1364590) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1364590) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns348p248 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1364590))) 884279719003555 562949953421312 1 2000000000000000 12294 16777216 1 5290000 14828830943414585393152 883867200816547 562949953421312 200000000529 1058000000000000000 qz17 (Ns348p247 rfl) rfl rfl 

noncomputable abbrev qz392 := (@HMul.hMul Real Real Real qz583 qz588 qz608)

noncomputable abbrev qz42 := qz392

noncomputable abbrev qz393 := qz608

noncomputable abbrev qz43 := qz393

noncomputable def Ns348p249 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 682295 4000) qz391) qz42 448036049154439283101 225179981368524800 4635159388557 1150000000000000000 883867200816547 2251799813685248 200000000529 4232000000000000000 Ns348p240 447947662434357628401 225179981368524800 431434663760469 105800000000000000000 (Ns348p246 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz43 1 4 0 1 883867200816547 562949953421312 200000000529 1058000000000000000 883867200816547 2251799813685248 200000000529 4232000000000000000 qz364 Ns348p248 rfl) 

noncomputable def Ns348p250 := @Ns348p236 Ns348p230 Ns348p231 3970123027049990399 433356800000000000000000 (@Ns348p238 3970123027049990399 433356800000000000000000 (Ns348p239 (Ns348p249 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 682295 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz609 (Real.log Real.pi) 682295 2000 0 1 38410761 33554432 1 67108864 5241494035299 13421772800 136459 26843545600 (Enclosure.Real.IsNear.const Bool.false 682295 2000) RS349to360.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns348p232 Ns348p233) 

noncomputable def Ns348p251 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz35) Bool.false Ns348p230 Ns348p231 3970123027049990399 433356800000000000000000 42198649367 33554432 309 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz35) (@HAdd.hAdd Real Real Real qz365 qz39 (Enclosure.sfrac Bool.true Ns348p232 Ns348p233)) Bool.false Ns348p230 Ns348p231 3970123027049990399 433356800000000000000000 Ns348p234 (Ns348p250 rfl rfl)) 

noncomputable def Ns348p252 := nat_lit 4742332254159848576385024 

noncomputable def Ns348p253 := nat_lit 773243743766784259529106998704086741067476478258129369427493280673094007784470129025390625 

noncomputable def Ns348p254 := nat_lit 20052072892042597411705012245279816272850392000149059967199507548332190919545345701492817920 

noncomputable def Ns348p255 := nat_lit 425497898370213975972497058061351544033845494718319833071405669307147902514801025390625 

noncomputable def Ns348p256 := nat_lit 2318880235503612350635376001996137520114361743784951468616337030680667727548380785025390625 

noncomputable def Ns348p257 := nat_lit 902343280141916883526725551037591732278267640006707698523977839674948591379540556567176806400 

noncomputable def Ns348p258 := BSN.cos_dyadic_bound_f 67392594675 68719476736 3 2 33554432 10590333 Ns348p253 Ns348p254 Ns348p255 Ns348p256 Ns348p257 Ns348p255 18671305 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 67392594675) qz594 0 2 Ns348p253 Ns348p254 Ns348p255 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 67392594675) qz595 0 2 Ns348p256 Ns348p257 Ns348p255 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p259 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz35) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 42198649367) qz366) Bool.false 42198649367 33554432 309 33554432 Bool.false 18671305 33554432 1 5290000 (Ns348p251 rfl) (Enclosure.sfrac_false_div 42198649367 33554432) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 42198649367) qz366) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns348p252) qz367) 226375608064910080 72057594037927936 Bool.false 18671305 33554432 200 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q0 42198649367 33554432 226375608064910080 72057594037927936 200 Ns348p252 Ns348p99 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 18671305 33554432 Ns348p252 Ns348p99 67392594675 68719476736 10590333 10580000 (Ns348p258 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p260 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz35) Bool.false Ns348p230 Ns348p231 3970123027049990399 433356800000000000000000 337589194943 268435456 2461 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz35) (@HAdd.hAdd Real Real Real qz365 qz39 (Enclosure.sfrac Bool.true Ns348p232 Ns348p233)) Bool.false Ns348p230 Ns348p231 3970123027049990399 433356800000000000000000 Ns348p234 (Ns348p250 rfl rfl)) 

noncomputable def Ns348p261 := Ns348p229 50409 BSN.abs_quadSignPos (BSN.cos_quad_nat3 499 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 203356402 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 323 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 167303053 268435456) qz38 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 1) Bool.false 18671305 33554432 104260277 11093934080000 149370440 268435456 2523 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz35)) Bool.false 18671305 33554432 104260277 11093934080000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz35) qz35) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz35)) Bool.false 18671305 33554432 1668164432 177502945280000 18671305 33554432 104260277 11093934080000 (Ns348p259 rfl rfl) rfl)) rfl) (Ns348p260 rfl) RS349to360.d7 

noncomputable def Ns348p262 := nat_lit 44514679016135930500022685758292187648649273440265446818419219675305665 

noncomputable def Ns348p263 := nat_lit 8034652537882724906230642902685508659225525958866114025153836963521 

noncomputable def Ns348p264 := nat_lit 116573055604818484040687422611779953018156970063428482244581040556431041 

noncomputable def Ns348p265 := BSN.sin_dyadic_bound_f 230738937 268435456 3 2 268435456 134217728 Ns348p262 Ns348p162 Ns348p263 Ns348p264 Ns348p165 Ns348p263 203356402 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 230738937) qz370 0 2 Ns348p262 Ns348p162 Ns348p263 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 230738937) qz371 0 2 Ns348p264 Ns348p165 Ns348p263 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p266 := nat_lit 16715490498020787270013844365308383643735629277058855659286727218649665 

noncomputable def Ns348p267 := nat_lit 1133174420194517873512891170782103186929790956803160966457349331521 

noncomputable def Ns348p268 := nat_lit 43776830926707461249669619132959738518909714159319321608948116530879041 

noncomputable def Ns348p269 := BSN.sin_dyadic_bound_f 180628841 268435456 3 2 268435456 134217728 Ns348p266 Ns348p162 Ns348p267 Ns348p268 Ns348p165 Ns348p267 167303053 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 180628841) qz370 0 2 Ns348p266 Ns348p162 Ns348p267 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 180628841) qz371 0 2 Ns348p268 Ns348p165 Ns348p267 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p270 := nat_lit 13467545145319890687947717495853204291726935702369213654838625446387361 

noncomputable def Ns348p271 := nat_lit 2382789054060393707961942249213607751612035889221723890882739166881 

noncomputable def Ns348p272 := nat_lit 40397869857851551276427228603061185659677583035329197516734110860828321 

noncomputable def Ns348p273 := BSN.cos_dyadic_bound_f 198214627 268435456 3 2 268435456 134217728 Ns348p270 Ns348p121 Ns348p271 Ns348p272 Ns348p124 Ns348p271 198519225 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 198214627) qz368 0 2 Ns348p270 Ns348p121 Ns348p271 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 198214627) qz369 0 2 Ns348p272 Ns348p124 Ns348p271 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p274 := nat_lit 43759970490437116243607593907339097831637384889016416077374520661626465 

noncomputable def Ns348p275 := nat_lit 7764568155093163006550528264661586972876220418230484406063653441121 

noncomputable def Ns348p276 := nat_lit 114596875316988963136009283187745327942046589400080145132656784389164641 

noncomputable def Ns348p277 := BSN.sin_dyadic_bound_f 229754837 268435456 3 2 268435456 134217728 Ns348p274 Ns348p162 Ns348p275 Ns348p276 Ns348p165 Ns348p275 202712652 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 229754837) qz370 0 2 Ns348p274 Ns348p162 Ns348p275 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 229754837) qz371 0 2 Ns348p276 Ns348p165 Ns348p275 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p278 := Ns348p227 85729 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 198 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 198519225 268435456) BSN.abs_quadSignNeg qz596 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 202712652 268435456) qz38 rfl rfl (Ns348p261 RS349to360.d9 RS349to360.d11 RS349to360.d13 RS349to360.d17 (Ns348p265 rfl rfl) (Ns348p269 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns348p260 rfl) RS349to360.d19 RS349to360.d21 RS349to360.d23 RS349to360.d25 RS349to360.d17 (Ns348p273 rfl rfl) (Ns348p277 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns348p279 := nat_lit 4197417243336862190847351914694282147595804584333059481342343083196416 

noncomputable def Ns348p280 := nat_lit 231514812520315803970473016087010314168990417143981700661416820736 

noncomputable def Ns348p281 := nat_lit 12591788700385545940934114798050672422159075772164890480625706415947776 

noncomputable def Ns348p282 := BSN.cos_dyadic_bound_f 148105896 268435456 3 2 268435456 134217728 Ns348p279 Ns348p121 Ns348p280 Ns348p281 Ns348p124 Ns348p280 228603684 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 148105896) qz368 0 2 Ns348p279 Ns348p121 Ns348p280 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 148105896) qz369 0 2 Ns348p281 Ns348p124 Ns348p280 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p283 := nat_lit 37210518759233111305819074578060604410472377193376079008114211484073921 

noncomputable def Ns348p284 := nat_lit 18178975715900363881126414374810759441684199462094628343498726703041 

noncomputable def Ns348p285 := nat_lit 111595198326267533189694970905432191712533763181204047767655636998815681 

noncomputable def Ns348p286 := BSN.cos_dyadic_bound_f 255532519 268435456 3 2 268435456 134217728 Ns348p283 Ns348p121 Ns348p284 Ns348p285 Ns348p124 Ns348p284 155722044 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 255532519) qz368 0 2 Ns348p283 Ns348p121 Ns348p284 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 255532519) qz369 0 2 Ns348p285 Ns348p124 Ns348p284 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p287 := Ns348p225 115578 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 22 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 228603684 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 44 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 155722044 268435456) qz38 rfl rfl (Ns348p278 rfl rfl) (Ns348p260 rfl) RS349to360.d27 RS349to360.d29 RS349to360.d31 RS349to360.d33 RS349to360.d17 (Ns348p282 rfl rfl) (Ns348p286 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p288 := nat_lit 37470025158283747937925196923296729038210820804763846149427386279813376 

noncomputable def Ns348p289 := nat_lit 18433294924535901832599689398813163132699562481105766561977540567296 

noncomputable def Ns348p290 := nat_lit 112373208885002172010110391391092560788367063289329326915158203758305536 

noncomputable def Ns348p291 := BSN.cos_dyadic_bound_f 255976662 268435456 3 2 268435456 134217728 Ns348p288 Ns348p121 Ns348p289 Ns348p290 Ns348p124 Ns348p289 155360060 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 255976662) qz368 0 2 Ns348p288 Ns348p121 Ns348p289 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 255976662) qz369 0 2 Ns348p290 Ns348p124 Ns348p289 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p292 := nat_lit 172428710859962524565358456078639508014285124878542142081260609743307745 

noncomputable def Ns348p293 := nat_lit 120428618252407042044963419869249187680195628542531742713794601894881 

noncomputable def Ns348p294 := nat_lit 451404024965588429126913634669029450876407391283303415962717358067500001 

noncomputable def Ns348p295 := BSN.sin_dyadic_bound_f 323661627 268435456 3 2 268435456 134217728 Ns348p292 Ns348p162 Ns348p293 Ns348p294 Ns348p165 Ns348p293 250745918 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 323661627) qz370 0 2 Ns348p292 Ns348p162 Ns348p293 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 323661627) qz371 0 2 Ns348p294 Ns348p165 Ns348p293 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p296 := Ns348p223 141658 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 102 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 155360060 268435456) BSN.abs_quadSignNeg qz597 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 250745918 268435456) qz38 rfl rfl (Ns348p287 rfl) (Ns348p260 rfl) RS349to360.d35 RS349to360.d37 RS349to360.d39 RS349to360.d41 RS349to360.d17 (Ns348p291 rfl rfl) (Ns348p295 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p297 := nat_lit 39838276269503664961982580490083693675123991795275794375426908218330625 

noncomputable def Ns348p298 := nat_lit 6435438631868410854913308302747960439255537863693646079202812890625 

noncomputable def Ns348p299 := nat_lit 104327923329010383187617851165348081975089755259657290794370812208090625 

noncomputable def Ns348p300 := BSN.sin_dyadic_bound_f 224425535 268435456 3 2 268435456 134217728 Ns348p297 Ns348p162 Ns348p298 Ns348p299 Ns348p165 Ns348p298 199179381 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 224425535) qz370 0 2 Ns348p297 Ns348p162 Ns348p298 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 224425535) qz371 0 2 Ns348p299 Ns348p165 Ns348p298 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p301 := Ns348p221 Bool.false 26862422 141658 Bool.true 224425535 14148475504056880 1 Bool.false 199179381 Bool.false Bool.false 89848472 153666 BSN.abs_quadSignPos qz372 (BSN.sfrac_eq_quadSignPos_mul Bool.false 199179381 268435456) qz38 rfl (Ns348p296 rfl) (Ns348p260 rfl) RS349to360.d43 RS349to360.d45 RS349to360.d17 (Ns348p300 rfl rfl) rfl 

noncomputable def Ns348p302 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 10) 89848472 268435456 153666 268435456 89848472 268435456 153666 268435456 48237031104446464 11231059 16777216 76833 67108864 (Ns348p301 rfl rfl rfl rfl) 

noncomputable def Ns348p303 := @Enclosure.Real.IsNear.mulLit_ff qz606 (Zeta.RiemannSiegel.correction qz37) 5197229 16777216 1 16777216 13854565960377 35184372088832 96154355431721 5816416510935040000 72005351991684195333 590295810358705651712 

noncomputable abbrev qz610 := (@HPow.hPow Real Real Real qz7 qz36 qz9)

noncomputable def Ns348p304 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz610 1 1 0 1 5197229 16777216 1 16777216 5197229 16777216 1 16777216 

noncomputable def Ns348p305 := @Enclosure.Real.IsNear.sqrt_image qz36 728739230027 6710886400 136459 6710886400 174830011 174830045 16777216 (@Enclosure.Real.IsNear.of_eq qz36 (@HMul.hMul Real Real Real qz5 qz35 qz3) Bool.false 728739230027 6710886400 136459 6710886400 (BSN.t_div_two_pi_mk qz35 682295 1000 qz38) (@Enclosure.Real.IsNear.mulLit_ff qz35 qz3 682295 1000 0 1 5340353 33554432 1 33554432 728739230027 6710886400 136459 6710886400 (Enclosure.Real.IsNear.const Bool.false 682295 1000) RS349to360.d48 rfl)) 

noncomputable abbrev qz750 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 682295 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz611 := qz750

noncomputable abbrev qz394 := qz611

noncomputable abbrev qz44 := qz394

noncomputable def Ns348p306 := @Enclosure.Real.IsNear.sqrt_image qz44 43707507 4194304 17 16777216 54158663 54158670 16777216 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 349660056 33554432 34 33554432 43707507 4194304 17 16777216 (Ns348p305 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns348p307 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz44) 108317333 33554432 7 33554432 5197228 5197230 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz44) Bool.false 108317333 33554432 7 33554432 108317333 33554432 7 33554432 (Ns348p306 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns348p308 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz44)) Bool.false 10394458 33554432 2 33554432 5197229 16777216 1 16777216 (Ns348p307 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz395 := (@HMul.hMul Real Real Real qz583 qz581 qz605)

noncomputable abbrev qz45 := (Real.cos qz395)

noncomputable abbrev qz612 := (@HMul.hMul Real Real Real qz738 qz749 qz749)

noncomputable abbrev qz396 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz612 qz605) qz602)

noncomputable abbrev qz46 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz396))

noncomputable def Ns348p309 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz37) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz45) qz46) Bool.false 13854565960377 

noncomputable def Ns348p310 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz45) qz46 2387571 2097152 143 

noncomputable abbrev qz47 := (@Neg.neg Real Real.instNeg (Real.cos qz395))

noncomputable def Ns348p311 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz45) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz47)) Bool.true 2387571 2097152 143 16777216 (BSN.inv_eq_neg_inv_neg qz45) 

noncomputable def Ns348p312 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz47) Bool.false 38201136 33554432 286 33554432 2387571 2097152 

noncomputable def Ns348p313 := @Enclosure.Real.IsNear.recentre' qz45 Bool.true 29472943 33554432 582807216 88751472640000 29472943 33554432 36425451 5546967040000 

noncomputable abbrev qz48 := qz395

noncomputable def Ns348p314 := @Enclosure.Real.IsNear.cos_image qz48 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 88691785) qz366) Bool.false 88691785 33554432 107 16777216 Bool.true 29472943 33554432 1 

noncomputable def Ns348p315 := nat_lit 91752656402875079443368459 

noncomputable def Ns348p316 := nat_lit 14411518807585587200000000000000 

noncomputable def Ns348p317 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz37 884279719003555 140737488355328 1 500000000000000 1764467 4194304 17 16777216 1560282382951045680185 590295810358705651712 Ns348p315 

noncomputable def Ns348p318 := @Enclosure.Real.IsNear.subLit_ff_p qz44 qz1 43707507 4194304 17 16777216 10 1 0 1 1764467 1764467 4194304 17 

noncomputable def Ns348p319 := @Ns348p318 16777216 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 349660056 33554432 34 33554432 43707507 4194304 17 16777216 (Ns348p305 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns348p320 := @Enclosure.Real.IsNear.recentre' qz48 Bool.false 1560282382951045680185 590295810358705651712 Ns348p315 Ns348p316 88691785 33554432 107 16777216 (@Ns348p317 Ns348p316 RS349to360.d47 (Ns348p319 rfl rfl) rfl) 

noncomputable def Ns348p321 := nat_lit 5185928328785695824936960 

noncomputable def Ns348p322 := nat_lit 1990113857019936708866525218041484228911308001369535903008641625016575561670015435002146785 

noncomputable def Ns348p323 := nat_lit 870109035802574144505937661713780046411546416623251968140631859542575625735280766021601 

noncomputable def Ns348p324 := nat_lit 5210794210899011022225985005323017336597330833198061147550405137747009920027421399003492321 

noncomputable def Ns348p325 := BSN.sin_dyadic_bound_f 73696474043 68719476736 3 2 33554432 10590333 Ns348p322 Ns348p190 Ns348p323 Ns348p324 Ns348p193 Ns348p323 29472943 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 73696474043) qz379 0 2 Ns348p322 Ns348p190 Ns348p323 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 73696474043) qz380 0 2 Ns348p324 Ns348p193 Ns348p323 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p326 := @Ns348p314 5290000 (Ns348p320 rfl) (Enclosure.sfrac_false_div 88691785 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 88691785) qz366) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns348p321) qz367) 226375608064910080 72057594037927936 Bool.false 29472943 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q1 88691785 33554432 226375608064910080 72057594037927936 0 Ns348p321 Ns348p99 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 29472943 33554432 Ns348p321 Ns348p99 73696474043 68719476736 10590333 10580000 (Ns348p325 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p327 := @Enclosure.Real.IsNear.inv_image qz47 29472943 33554432 36425451 5546967040000 19100425 19100711 16777216 (@Enclosure.Real.IsNear.neg qz45 Bool.true 29472943 33554432 36425451 5546967040000 (Ns348p313 (Ns348p326 rfl rfl) rfl)) 

noncomputable def Ns348p328 := Ns348p311 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz47) Bool.false 2387571 2097152 143 16777216 (@Ns348p312 143 16777216 (Ns348p327 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p329 := @Enclosure.Real.IsNear.recentre' qz46 Bool.true 5802787 16777216 

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz349 qz346 qz396)

noncomputable def Ns348p330 := @Enclosure.Real.IsNear.cos_image qz49 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 64557567)) qz366) Bool.true 64557567 33554432 

noncomputable def Ns348p331 := nat_lit 4763507697793522621184423525 

noncomputable def Ns348p332 := nat_lit 2475880078570760549798248448 

noncomputable def Ns348p333 := nat_lit 14172559848475787258807393742793551 

noncomputable def Ns348p334 := @Enclosure.Real.IsNear.recentre' qz49 Bool.true Ns348p331 Ns348p332 Ns348p333 

noncomputable def Ns348p335 := nat_lit 1208925819614629174706176000000000000000 

noncomputable abbrev qz50 := qz396

noncomputable def Ns348p336 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz50 884279719003555 140737488355328 1 500000000000000 5386878829655 

noncomputable abbrev qz397 := (@HSub.hSub Real Real Real qz587 qz612 qz605)

noncomputable abbrev qz51 := qz397

noncomputable def Ns348p337 := @Enclosure.Real.IsNear.subLit_tf qz51 qz31 4287367201879 17592186044416 525180473 281474976710656 1 16 

noncomputable abbrev qz398 := qz612

noncomputable abbrev qz52 := qz398

noncomputable def Ns348p338 := @Enclosure.Real.IsNear.subLit_ff_n qz52 qz37 3113343794089 17592186044416 239967801 281474976710656 1764467 4194304 17 16777216 

noncomputable def Ns348p339 := @Enclosure.Real.IsNear.mulLit_ff qz37 qz37 1764467 4194304 17 16777216 1764467 4194304 17 16777216 3113343794089 17592186044416 

noncomputable def Ns348p340 := nat_lit 561623518365530536772508918827085917444295264803858241264541700011577731833578803058254677257431041 

noncomputable def Ns348p341 := nat_lit 5240417106596554029707969357326126571214941704687749200258694807147359253772479122296798914561 

noncomputable def Ns348p342 := nat_lit 3388780078563287968839681042944641313881414103276529911249788588728320046326878345621998235280943105 

noncomputable def Ns348p343 := BSN.cos_dyadic_bound_t 64557567 33554432 4 3 16777216 5290000 Ns348p340 Ns348p210 Ns348p341 Ns348p342 Ns348p213 Ns348p341 5802787 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 64557567) (BSN.cosEvenQ 33554432) 0 3 Ns348p340 Ns348p210 Ns348p341 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 64557567) (BSN.cosOddQ 33554432) 0 3 Ns348p342 Ns348p213 Ns348p341 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p344 := @Ns348p329 1058907216 88751472640000 5802787 16777216 66181701 5546967040000 (@Ns348p330 197 16777216 Bool.true 5802787 16777216 1 5290000 (@Ns348p334 Ns348p335 64557567 33554432 197 16777216 (@Ns348p336 17592186044416 525180473 281474976710656 Ns348p331 Ns348p332 Ns348p333 Ns348p335 RS349to360.d47 (@Ns348p337 0 1 86190061274480 5386878829655 17592186044416 525180473 281474976710656 (@Ns348p338 17982521404309897216 4287367201879 17592186044416 525180473 281474976710656 (@Ns348p339 239967801 281474976710656 (Ns348p319 rfl rfl) (Ns348p319 rfl rfl) rfl) (Ns348p319 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 64557567 33554432) (BSN.cos_neg_of_bound 64557567 33554432 Bool.true 5802787 16777216 1 5290000 (Ns348p343 rfl rfl)) rfl rfl) 

noncomputable def Ns348p345 := @Ns348p303 200810653446291262257 Ns348p218 (Ns348p304 qz33 (@Enclosure.Real.IsNear.of_eq qz610 (@Inv.inv Real Real.instInv (Real.sqrt qz44)) Bool.false 5197229 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz36 (BSN.t_div_two_pi_nonneg qz35 682295 1000 qz38)) Ns348p308) rfl) (@Ns348p309 35184372088832 96154355431721 5816416510935040000 (BSN.correction_mk qz37 (BSN.cos_two_pi_p_ne_zero_mk qz35 682295 1000 10 qz38 rfl rfl (@BSN.floor_sqrt_eq_dec qz35 682295 1000 10 qz38 rfl rfl rfl))) (@Ns348p310 16777216 5802787 16777216 66181701 5546967040000 13854565960377 35184372088832 96154355431721 5816416510935040000 Ns348p328 (Ns348p344 rfl) rfl)) 

noncomputable def Ns348p346 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz35) (hardyZApproximantRS₀ qz35) Bool.false 323152406815941237755 590295810358705651712 44890083631913484094257 Ns348p218 (@Eq.refl Real (hardyZApproximantRS₀ qz35)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz35) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 10) (@HMul.hMul Real Real Real qz5 qz606 (Zeta.RiemannSiegel.correction qz37))) Bool.false 323152406815941237755 590295810358705651712 44890083631913484094257 Ns348p218 (BSN.hardyZApproximantRS₀_eq qz35 10 (@BSN.floor_sqrt_eq_dec qz35 682295 1000 10 qz38 rfl rfl rfl)) (@Ns348p220 323152406815941237755 590295810358705651712 44890083631913484094257 Ns348p218 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 10)) Bool.false 11231059 16777216 76833 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz35) qz35 10) (Ns348p302 (Ns348p301 rfl rfl rfl rfl) rfl rfl)) (Ns348p345 rfl) rfl rfl)) 

theorem RS349to360.d51 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz35) Bool.false 323152406815941237755 590295810358705651712 44890083631913484094257 Ns348p218 := Ns348p346 

noncomputable abbrev qz613 := (@HMul.hMul Real Real Real qz738 (Real.sqrt qz746) qz740)

noncomputable abbrev qz399 := qz613

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv qz399)

noncomputable abbrev qz400 := (@HMul.hMul Real Real Real qz583 (@HMul.hMul Real Real Real qz583 qz613 qz613) qz613)

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz349 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz400))

noncomputable abbrev qz401 := (@HMul.hMul Real Real Real qz583 qz600 qz600)

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz349 qz401 qz374))

noncomputable abbrev qz614 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) qz53)

noncomputable def Ns348p347 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz365 (@HAdd.hAdd Real Real Real qz365 qz614 qz54) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz55)) Bool.false 

noncomputable def Ns348p348 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz365 qz614 qz54) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz55) 19182601 1073741824 

noncomputable def Ns348p349 := @Enclosure.Real.IsNear.addLit_ff qz614 qz54 2397825 134217728 25 134217728 

noncomputable def Ns348p350 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) qz53 25 4 0 1 95913 33554432 1 33554432 2397825 

noncomputable def Ns348p351 := @Enclosure.Real.IsNear.recentre' qz53 Bool.false 95913 33554432 1 33554432 95913 33554432 1 33554432 

noncomputable def Ns348p352 := @Enclosure.Real.IsNear.mulLit_ff qz23 qz8 54137043 16777216 3 16777216 1818940252859 16777216000 340603 16777216000 98472046683458555937 281474976710656000 4779212207463 

noncomputable def Ns348p353 := @Enclosure.Real.IsNear.sqrt_image qz8 1818940252859 16777216000 340603 16777216000 174690434 174690467 16777216 qz21 

noncomputable def Ns348p354 := @Enclosure.Real.IsNear.sqrt_image qz22 349380901 33554432 33 33554432 54137040 54137046 16777216 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 349380901 33554432 33 33554432 349380901 33554432 33 33554432 (Ns348p353 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz402 := (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 108274086 33554432 6 33554432 54137043 16777216 3 16777216 (Ns348p354 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns348p355 := @Ns348p352 56294995342131200 qz402 

noncomputable def Ns348p356 := Ns348p355 qz21 

noncomputable abbrev qz56 := qz399

noncomputable def Ns348p357 := @Enclosure.Real.IsNear.inv_image qz56 98472046683458555937 281474976710656000 4779212207463 56294995342131200 47956 47957 16777216 (Ns348p356 rfl) rfl rfl 

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv qz400)

noncomputable def Ns348p358 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz57 1 32 0 1 1 

noncomputable def Ns348p359 := @Enclosure.Real.IsNear.recentre' qz57 Bool.false 1 33554432 1 33554432 

noncomputable def Ns348p360 := nat_lit 954858225682041063903847602210276413494905894148186322041953 

noncomputable def Ns348p361 := nat_lit 22300745198530623141535718272648361505980416000000000 

noncomputable def Ns348p362 := nat_lit 139028425315132029654752559514108143869861531607915411 

noncomputable def Ns348p363 := nat_lit 4460149039706124628307143654529672301196083200000000 

noncomputable abbrev qz58 := qz400

noncomputable def Ns348p364 := @Enclosure.Real.IsNear.inv_image qz58 Ns348p360 Ns348p361 Ns348p362 Ns348p363 0 1 

noncomputable def Ns348p365 := nat_lit 9696743978029241185759271887489357947969 

noncomputable def Ns348p366 := nat_lit 79228162514264337593543950336000000 

noncomputable def Ns348p367 := nat_lit 941237729411249726071094833197507 

noncomputable def Ns348p368 := nat_lit 15845632502852867518708790067200000 

noncomputable abbrev qz403 := (@HMul.hMul Real Real Real qz583 qz613 qz613)

noncomputable abbrev qz59 := qz403

noncomputable def Ns348p369 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz56 Ns348p365 Ns348p366 Ns348p367 Ns348p368 98472046683458555937 281474976710656000 4779212207463 

noncomputable def Ns348p370 := @Enclosure.Real.IsNear.mulLit_ff qz56 qz56 98472046683458555937 281474976710656000 4779212207463 56294995342131200 98472046683458555937 281474976710656000 4779212207463 56294995342131200 Ns348p365 

noncomputable def Ns348p371 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz55 13 10 0 1 998679 33554432 1 

noncomputable def Ns348p372 := @Enclosure.Real.IsNear.recentre' qz55 Bool.false 998679 33554432 1 33554432 998679 33554432 

noncomputable abbrev qz60 := qz401

noncomputable def Ns348p373 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz23 2930819424783849 281474976710656 324822267 281474976710656 54137043 16777216 3 16777216 158665897224758499018507 

noncomputable def Ns348p374 := @Enclosure.Real.IsNear.mulLit_ff qz23 qz23 54137043 16777216 3 16777216 54137043 16777216 3 16777216 2930819424783849 281474976710656 324822267 

noncomputable def Ns348p375 := @Ns348p374 281474976710656 qz402 

noncomputable def Ns348p376 := Ns348p375 qz402 

noncomputable def Ns348p377 := @Ns348p373 4722366482869645213696 26377376284754829 4722366482869645213696 (Ns348p376 rfl) qz402 

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz349 qz401 qz374)

noncomputable def Ns348p378 := @Enclosure.Real.IsNear.inv_image qz61 158665897224758499018507 4722366482869645213696 26377376284754829 4722366482869645213696 499339 499340 16777216 (Ns348p377 rfl) 

noncomputable def Ns348p379 := @Ns348p348 201 1073741824 12982827 335544320 13 335544320 20376817152032768 303638237 5368709120 1213 5368709120 (@Ns348p349 1 1073741824 1 1073741824 2574645123350528 19182601 1073741824 201 1073741824 (@Ns348p350 134217728 25 134217728 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns348p351 (Ns348p357 rfl rfl rfl rfl) rfl) rfl) (@Ns348p358 33554432 1 33554432 1 1073741824 1 1073741824 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns348p359 1 33554432 1 33554432 (@Ns348p364 16777216 (@Ns348p369 56294995342131200 Ns348p360 Ns348p361 Ns348p362 Ns348p363 (@Ns348p370 Ns348p366 Ns348p367 Ns348p368 (Ns348p356 rfl) (Ns348p356 rfl) rfl) (Ns348p356 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns348p371 33554432 12982827 335544320 13 335544320 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns348p372 1 33554432 (Ns348p378 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS349to360.d52 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 := @Ns348p347 303638237 5368709120 1213 5368709120 (BSN.hardyZErrorBoundRS₀_mk qz4 681206 1000 qz11 rfl rfl) (Ns348p379 rfl rfl) 

noncomputable def Ns348p380 := nat_lit 67884018191251149946880000 

noncomputable def Ns348p381 := nat_lit 2329787332071537681778081792 

noncomputable abbrev qz751 := (Enclosure.sfrac Bool.false 682966 1000)

noncomputable abbrev qz615 := qz751

noncomputable abbrev qz404 := qz615

noncomputable abbrev qz62 := qz404

noncomputable abbrev qz752 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 682966 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz616 := qz752

noncomputable abbrev qz405 := qz616

noncomputable abbrev qz63 := qz405

noncomputable abbrev qz753 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 682966 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz617 := qz753

noncomputable abbrev qz406 := qz617

noncomputable abbrev qz64 := qz406

noncomputable abbrev qz618 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz63 qz9))

noncomputable def Ns348p382 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 10) (@HMul.hMul Real Real Real qz5 qz618 (Zeta.RiemannSiegel.correction qz64)) 13748489 16777216 153805 134217728 17933158171525597875 147573952589676412928 345769483184522341679 Ns348p380 Ns348p381 

noncomputable def Ns348p383 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin BSN.quadSignPos 9 10 682966 1000 199 268435456 134217728 4503599627370496 Bool.false 338011403633 2463 618095470 52 84886744 8 

noncomputable def Ns348p384 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 682966 1000 102 153 268435456 134217728 4503599627370496 Bool.false 338011403633 2463 

noncomputable def Ns348p385 := Ns348p384 558195838 52 94906264 8 589812974 52 89478488 8 Bool.true 23598240 115679 Bool.true 208317379 Bool.true 297217443 14148475504056880 1 Bool.false 191579980 Bool.true Bool.false 240104678 Bool.true Bool.true 171366886 

noncomputable def Ns348p386 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 682966 1000 22 44 268435456 134217728 4503599627370496 Bool.false 338011403633 2463 

noncomputable def Ns348p387 := Ns348p386 480971758 52 109588312 8 522351262 52 101459064 8 Bool.true 35995012 85801 Bool.false 247582536 Bool.true 183821526 14148475504056880 1 Bool.false 162128376 Bool.true Bool.false 207917436 Bool.false Bool.true 23598240 

noncomputable def Ns348p388 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 682966 1000 198 101 268435456 134217728 4503599627370496 Bool.false 338011403633 2463 

noncomputable def Ns348p389 := Ns348p388 372130544 51 134217720 8 432030192 51 120047984 16 Bool.false 106421835 50447 Bool.false 370723722 Bool.false 362071268 14148475504056880 1 Bool.false 50628633 Bool.true Bool.false 261849225 Bool.true Bool.true 35995012 

noncomputable def Ns348p390 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 682966 1000 500 323 268435456 134217728 4503599627370496 Bool.false 338011403633 2463 

noncomputable def Ns348p391 := Ns348p390 186065264 51 189812528 16 294906480 51 154981288 8 Bool.true 223344536 2515 Bool.false 106440406 Bool.false 404955283 14148475504056880 1 Bool.false 247607560 Bool.false Bool.false 267916017 Bool.false Bool.false 106421835 

noncomputable def Ns348p392 := nat_lit 404649482512259554309258348683133916907607858690878491 

noncomputable def Ns348p393 := nat_lit 321356815748296637846185169093427171809762035630080 

noncomputable def Ns348p394 := nat_lit 71324255330993338370378946196480000 

noncomputable def Ns348p395 := nat_lit 292272321301694899235540259809046958080 

noncomputable abbrev qz619 := (@Eq.refl Real qz751)

noncomputable abbrev qz407 := qz619

noncomputable abbrev qz65 := qz407

noncomputable def Ns348p396 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz62 682966 1000 1865771228624 16000000 1365932 4000 2000 Ns348p394 Ns348p395 qz65 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns348p397 := nat_lit 8287221401851075672253610981030582618267808945989191495680 

noncomputable abbrev qz620 := (@HSub.hSub Real Real Real qz742 qz743 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz744 (@Nat.cast Real Real.instNatCast 1365932))))

noncomputable abbrev qz408 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 682966 4000) (Real.log (Enclosure.sfrac Bool.false 1865771228624 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz620))

noncomputable abbrev qz621 := (Enclosure.sfrac Bool.false 682966 2000)

noncomputable abbrev qz66 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz408 qz621) (@HMul.hMul Real Real Real qz349 qz621 (Real.log Real.pi)))

noncomputable def Ns348p398 := @Enclosure.Real.IsNear.addLit_ft_p qz66 (Enclosure.sfrac Bool.true Ns348p394 Ns348p395) 28354457141277258471 22517998136852480 431957313697375481 47104000000000000000000 Ns348p394 Ns348p395 0 1 Ns348p397 

noncomputable def Ns348p399 := nat_lit 23785442601097554062789836800000 

noncomputable abbrev qz67 := (@HSub.hSub Real Real Real qz353 qz408 qz621)

noncomputable def Ns348p400 := @Enclosure.Real.IsNear.subLit_ff_p qz67 (@HMul.hMul Real Real Real qz5 qz621 (Real.log Real.pi)) 928921827314453002383 562949953421312000 93881312835747 23000000000000000000 13116621898563 33554432000 341483 67108864000 Ns348p399 28354457141277258471 22517998136852480 

noncomputable def Ns348p401 := nat_lit 1857843654628906004766000 

noncomputable abbrev qz68 := qz408

noncomputable def Ns348p402 := @Enclosure.Real.IsNear.subLit_ff_p qz68 qz621 1121159666258622888079 562949953421312000 93881312835747 23000000000000000000 682966 2000 0 1 Ns348p401 928921827314453002383 562949953421312000 93881312835747 23000000000000000000 

noncomputable def Ns348p403 := nat_lit 2524627127592581847998200946037358592 

noncomputable def Ns348p404 := nat_lit 56416198121578925802913792 

noncomputable def Ns348p405 := nat_lit 6463045685248926653389562069842779617313665786130092116521122762402587196908856015920644737840130485274143321085940712700494077031907466503712433687888418474137267888389836138086400 

noncomputable def Ns348p406 := nat_lit 177858138032667942777118736167067880343414345969152863024194862063555049851403917919407924321964771922802019683919183839202025623920610280540770857249489949514997758922906759331840 

noncomputable def Ns348p407 := nat_lit 8004410580794244535400977756978954719792308911100565057448797084160714309492675107351834586905332918385485771921229497555083094389409465301830976294050021501331899689205760 

noncomputable def Ns348p408 := BSN.log_dyadic_bound 817195228624 2914347228624 8 7 Ns348p405 134217728 42320000 Ns348p406 Ns348p407 77341817 3731542457248 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 817195228624) (BSN.artanhQ 2914347228624) 0 7 Ns348p406 Ns348p405 Ns348p407 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz409 := (Real.log (Enclosure.sfrac Bool.false 1865771228624 16000000))

noncomputable def Ns348p409 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 682966 4000) qz409 682966 4000 0 1 3283854930287863 281474976710656 781250529 33062500000000000 1121380633159490320829 562949953421312000 266783774394507 66125000000000000000 (Enclosure.Real.IsNear.const Bool.false 682966 4000) (BSN.isNear_log_sfrac 1865771228624 16000000 3283854930287863 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1865771228624) qz356)) Bool.false Ns348p404 Ns348p99 1000000677120000 42320000000000000000000 3283854930287863 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 1865771228624 16000000 16 3731542457248 2097152000000 77341817 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns348p408 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p410 := BSN.arctan_dyadic_bound_f 1000 1365932 1 0 16777216 5290000 0 1 1 0 1 1 12282 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1365932) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1365932) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns348p411 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1365932))) 884279719003555 562949953421312 1 2000000000000000 12282 16777216 1 5290000 14828837698814026448896 883867603469731 562949953421312 200000000529 1058000000000000000 qz17 (Ns348p410 rfl) rfl rfl 

noncomputable abbrev qz410 := (@HMul.hMul Real Real Real qz583 qz588 qz620)

noncomputable abbrev qz69 := qz410

noncomputable abbrev qz411 := qz620

noncomputable abbrev qz70 := qz411

noncomputable def Ns348p412 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 682966 4000) qz409) qz69 1121380633159490320829 562949953421312000 266783774394507 66125000000000000000 883867603469731 2251799813685248 200000000529 4232000000000000000 Ns348p403 1121159666258622888079 562949953421312000 93881312835747 23000000000000000000 (Ns348p409 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz70 1 4 0 1 883867603469731 562949953421312 200000000529 1058000000000000000 883867603469731 2251799813685248 200000000529 4232000000000000000 qz364 Ns348p411 rfl) 

noncomputable def Ns348p413 := @Ns348p398 Ns348p392 Ns348p393 431957313697375481 47104000000000000000000 (@Ns348p400 431957313697375481 47104000000000000000000 (Ns348p402 (Ns348p412 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 682966 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz621 (Real.log Real.pi) 682966 2000 0 1 38410761 33554432 1 67108864 13116621898563 33554432000 341483 67108864000 (Enclosure.Real.IsNear.const Bool.false 682966 2000) RS349to360.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns348p394 Ns348p395) 

noncomputable def Ns348p414 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns348p392 Ns348p393 431957313697375481 47104000000000000000000 21125712727 16777216 77 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz365 qz66 (Enclosure.sfrac Bool.true Ns348p394 Ns348p395)) Bool.false Ns348p392 Ns348p393 431957313697375481 47104000000000000000000 Ns348p396 (Ns348p413 rfl rfl)) 

noncomputable def Ns348p415 := nat_lit 2376131505399951905521664 

noncomputable def Ns348p416 := nat_lit 1403194165470008693233428664863532042242014641701243295840980711489192928738549394168889600 

noncomputable def Ns348p417 := nat_lit 432678527065439472943118238849149298299444015317481440351252031992018104188542409523456 

noncomputable def Ns348p418 := nat_lit 3674331810996678723131357645113018630817553533192742233441999836324661069765609820826910976 

noncomputable def Ns348p419 := BSN.sin_dyadic_bound_f 67533719214 68719476736 3 2 33554432 10590333 Ns348p416 Ns348p190 Ns348p417 Ns348p418 Ns348p193 Ns348p417 27918067 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 67533719214) qz379 0 2 Ns348p416 Ns348p190 Ns348p417 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 67533719214) qz380 0 2 Ns348p418 Ns348p193 Ns348p417 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p420 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz62) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21125712727) qz377) Bool.false 21125712727 16777216 77 8388608 Bool.true 27918067 33554432 1 5290000 (Ns348p414 rfl) (Enclosure.sfrac_false_div 21125712727 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21125712727) qz377) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns348p415) qz381) 226375608064910080 72057594037927936 Bool.false 27918067 33554432 200 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q1 21125712727 16777216 226375608064910080 72057594037927936 200 Ns348p415 Ns348p188 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 27918067 33554432 Ns348p415 Ns348p188 67533719214 68719476736 10590333 10580000 (Ns348p419 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p421 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns348p392 Ns348p393 431957313697375481 47104000000000000000000 338011403633 268435456 2463 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz365 qz66 (Enclosure.sfrac Bool.true Ns348p394 Ns348p395)) Bool.false Ns348p392 Ns348p393 431957313697375481 47104000000000000000000 Ns348p396 (Ns348p413 rfl rfl)) 

noncomputable def Ns348p422 := Ns348p391 50447 BSN.abs_quadSignPos (BSN.cos_quad_nat0 500 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 247607560 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 323 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 267916017 268435456) qz65 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) Bool.true 27918067 33554432 25982413 2773483520000 223344536 268435456 2515 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.true 27918067 33554432 25982413 2773483520000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz62) qz62) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.true 27918067 33554432 415718608 44375736320000 27918067 33554432 25982413 2773483520000 (Ns348p420 rfl rfl) rfl)) rfl) (Ns348p421 rfl) RS349to360.d7 

noncomputable def Ns348p423 := nat_lit 1119698963961101092930324159287197362003723270298627009123764569661696 

noncomputable def Ns348p424 := nat_lit 16476015029038968577555442441922323272838125509283715962139074816 

noncomputable def Ns348p425 := nat_lit 3359063939853245200853817366976708241364624134644862459939369430835456 

noncomputable def Ns348p426 := BSN.cos_dyadic_bound_f 106440406 268435456 3 2 268435456 134217728 Ns348p423 Ns348p121 Ns348p424 Ns348p425 Ns348p124 Ns348p424 247607560 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 106440406) qz368 0 2 Ns348p423 Ns348p121 Ns348p424 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 106440406) qz369 0 2 Ns348p425 Ns348p124 Ns348p424 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p427 := nat_lit 37686845669626291415594881659474686624158308403406116257250257833169854487004403525857108212196522692869286961 

noncomputable def Ns348p428 := nat_lit 19448442585980808590641191438259431432924257573167342757699645783820525061615796294361502657692990630961 

noncomputable def Ns348p429 := nat_lit 188234982545088459362143747731561016083154526992056429484711278458139671001600440018182755451775831304008297521 

noncomputable def Ns348p430 := BSN.sin_dyadic_bound_f 404955283 268435456 4 3 268435456 134217728 Ns348p427 Ns348p131 Ns348p428 Ns348p429 Ns348p134 Ns348p428 267916017 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 404955283) qz370 0 3 Ns348p427 Ns348p131 Ns348p428 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 404955283) qz371 0 3 Ns348p429 Ns348p134 Ns348p428 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p431 := nat_lit 10185584079123068947306447647902330068396872032600380769956237502353076642543921405336722983509128224382980096 

noncomputable def Ns348p432 := nat_lit 6739140650370561884027132725754949367920077225712494242880541065967790119496609440126971457169800892416 

noncomputable def Ns348p433 := nat_lit 61703499464745118097063070956616503322006493051462007655017095566199351956743581373149122282343701278641950720 

noncomputable def Ns348p434 := BSN.cos_dyadic_bound_f 370723722 268435456 4 3 268435456 134217728 Ns348p431 Ns348p146 Ns348p432 Ns348p433 Ns348p149 Ns348p432 50628633 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 370723722) qz368 0 3 Ns348p431 Ns348p146 Ns348p432 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 370723722) qz369 0 3 Ns348p433 Ns348p149 Ns348p432 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p435 := nat_lit 24069636898185179936945485531561235503255603866696543992028762163097488875392467012935200542437067726809726976 

noncomputable def Ns348p436 := nat_lit 5076083474748420908781578642000787005297936524966360444603658606747736287575154236746494519727332786176 

noncomputable def Ns348p437 := nat_lit 120266822057941079716674837903036347904369306041456994784503922860061710931086014312635815490079304459627790336 

noncomputable def Ns348p438 := BSN.sin_dyadic_bound_f 362071268 268435456 4 3 268435456 134217728 Ns348p435 Ns348p131 Ns348p436 Ns348p437 Ns348p134 Ns348p436 261849225 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 362071268) qz370 0 3 Ns348p435 Ns348p131 Ns348p436 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 362071268) qz371 0 3 Ns348p437 Ns348p134 Ns348p436 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p439 := Ns348p389 85801 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 198 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 50628633 268435456) BSN.abs_quadSignNeg qz596 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 261849225 268435456) qz65 rfl rfl (Ns348p422 RS349to360.d9 RS349to360.d11 RS349to360.d13 RS349to360.d17 (Ns348p426 rfl rfl) (Ns348p430 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns348p421 rfl) RS349to360.d19 RS349to360.d21 RS349to360.d23 RS349to360.d25 RS349to360.d17 (Ns348p434 rfl rfl) (Ns348p438 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns348p440 := nat_lit 32789579755014373950946723548303794062900435500408783180193002669735936 

noncomputable def Ns348p441 := nat_lit 14117573484344963904901303819527310724897733698274692008962693267456 

noncomputable def Ns348p442 := nat_lit 98340504118074431925030368037272327567251511033829800156561082622672896 

noncomputable def Ns348p443 := BSN.cos_dyadic_bound_f 247582536 268435456 3 2 268435456 134217728 Ns348p440 Ns348p121 Ns348p441 Ns348p442 Ns348p124 Ns348p441 162128376 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 247582536) qz368 0 2 Ns348p440 Ns348p121 Ns348p441 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 247582536) qz369 0 2 Ns348p442 Ns348p124 Ns348p441 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p444 := nat_lit 9961187315432401761549614485805578492628529607626444131085462148505856 

noncomputable def Ns348p445 := nat_lit 1303679801123757472812207297957993878784571484626387813470935736576 

noncomputable def Ns348p446 := nat_lit 29880954586694957769703219042820819490128019679910079617629444574044416 

noncomputable def Ns348p447 := BSN.cos_dyadic_bound_f 183821526 268435456 3 2 268435456 134217728 Ns348p444 Ns348p121 Ns348p445 Ns348p446 Ns348p124 Ns348p445 207917436 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 183821526) qz368 0 2 Ns348p444 Ns348p121 Ns348p445 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 183821526) qz369 0 2 Ns348p446 Ns348p124 Ns348p445 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p448 := Ns348p387 115679 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 22 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 162128376 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 44 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 207917436 268435456) qz65 rfl rfl (Ns348p439 rfl rfl) (Ns348p421 rfl) RS349to360.d27 RS349to360.d29 RS349to360.d31 RS349to360.d33 RS349to360.d17 (Ns348p443 rfl rfl) (Ns348p447 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p449 := nat_lit 16431021233697323083387662342865412094215655438902644374980475198759841 

noncomputable def Ns348p450 := nat_lit 3546533135578938267506402589710135012999978345311130490481982432161 

noncomputable def Ns348p451 := nat_lit 49285970634820811373627974223416816012620966360017310863960461631415201 

noncomputable def Ns348p452 := BSN.cos_dyadic_bound_f 208317379 268435456 3 2 268435456 134217728 Ns348p449 Ns348p121 Ns348p450 Ns348p451 Ns348p124 Ns348p450 191579980 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 208317379) qz368 0 2 Ns348p449 Ns348p121 Ns348p450 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 208317379) qz369 0 2 Ns348p451 Ns348p124 Ns348p450 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p453 := nat_lit 122589780082894313162386414832149732101617978701216053060076391818246305 

noncomputable def Ns348p454 := nat_lit 60896782695287083683609694329234339826190142353493679873598608292001 

noncomputable def Ns348p455 := nat_lit 320969876854645117289810004102906728477852303034612577770880914158172321 

noncomputable def Ns348p456 := BSN.sin_dyadic_bound_f 297217443 268435456 3 2 268435456 134217728 Ns348p453 Ns348p162 Ns348p454 Ns348p455 Ns348p165 Ns348p454 240104678 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 297217443) qz370 0 2 Ns348p453 Ns348p162 Ns348p454 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 297217443) qz371 0 2 Ns348p455 Ns348p165 Ns348p454 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p457 := Ns348p385 141785 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 102 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 191579980 268435456) BSN.abs_quadSignNeg qz597 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 240104678 268435456) qz65 rfl rfl (Ns348p448 rfl) (Ns348p421 rfl) RS349to360.d35 RS349to360.d37 RS349to360.d39 RS349to360.d41 RS349to360.d17 (Ns348p452 rfl rfl) (Ns348p456 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p458 := nat_lit 34794653091769149207486551620782225273012710567048685894291932541395200 

noncomputable def Ns348p459 := nat_lit 4909303236885300450785874460667115264635401127056694563712408002816 

noncomputable def Ns348p460 := nat_lit 91120904939869005056973029495779033718890546549969418884328098471649536 

noncomputable def Ns348p461 := BSN.sin_dyadic_bound_f 216958906 268435456 3 2 268435456 134217728 Ns348p458 Ns348p162 Ns348p459 Ns348p460 Ns348p165 Ns348p459 194097361 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 216958906) qz370 0 2 Ns348p458 Ns348p162 Ns348p459 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 216958906) qz371 0 2 Ns348p460 Ns348p165 Ns348p459 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p462 := Ns348p383 Bool.true 171366886 141785 Bool.true 216958906 14148475504056880 1 Bool.false 194097361 Bool.false Bool.true 109987912 153805 BSN.abs_quadSignPos qz372 (BSN.sfrac_eq_quadSignPos_mul Bool.false 194097361 268435456) qz65 rfl (Ns348p457 rfl) (Ns348p421 rfl) RS349to360.d43 RS349to360.d45 RS349to360.d17 (Ns348p461 rfl rfl) rfl 

noncomputable def Ns348p463 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 10) 109987912 268435456 153805 268435456 109987912 268435456 153805 268435456 59049310624415744 13748489 16777216 153805 134217728 (Ns348p462 rfl rfl rfl rfl) 

noncomputable def Ns348p464 := @Enclosure.Real.IsNear.mulLit_ff qz618 (Zeta.RiemannSiegel.correction qz64) 324747 1048576 1 16777216 55221936373625 140737488355328 1523528524568439 93062664174960640000 17933158171525597875 147573952589676412928 

noncomputable abbrev qz622 := (@HPow.hPow Real Real Real qz7 qz63 qz9)

noncomputable def Ns348p465 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz622 1 1 0 1 324747 1048576 1 16777216 324747 1048576 1 16777216 

noncomputable def Ns348p466 := @Enclosure.Real.IsNear.sqrt_image qz63 1823639763499 16777216000 341483 16777216000 174915958 174915992 16777216 (@Enclosure.Real.IsNear.of_eq qz63 (@HMul.hMul Real Real Real qz5 qz62 qz3) Bool.false 1823639763499 16777216000 341483 16777216000 (BSN.t_div_two_pi_mk qz62 682966 1000 qz65) (@Enclosure.Real.IsNear.mulLit_ff qz62 qz3 682966 1000 0 1 5340353 33554432 1 33554432 1823639763499 16777216000 341483 16777216000 (Enclosure.Real.IsNear.const Bool.false 682966 1000) RS349to360.d48 rfl)) 

noncomputable abbrev qz754 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 682966 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz623 := qz754

noncomputable abbrev qz412 := qz623

noncomputable abbrev qz71 := qz412

noncomputable def Ns348p467 := @Enclosure.Real.IsNear.sqrt_image qz71 174915975 16777216 17 16777216 54171974 54171980 16777216 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 349831950 33554432 34 33554432 174915975 16777216 17 16777216 (Ns348p466 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns348p468 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz71) 54171977 16777216 3 16777216 5195951 5195953 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz71) Bool.false 108343954 33554432 6 33554432 54171977 16777216 3 16777216 (Ns348p467 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns348p469 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 10391904 33554432 2 33554432 324747 1048576 1 16777216 (Ns348p468 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz413 := (@HMul.hMul Real Real Real qz583 qz581 qz617)

noncomputable abbrev qz72 := (Real.cos qz413)

noncomputable abbrev qz624 := (@HMul.hMul Real Real Real qz738 qz753 qz753)

noncomputable abbrev qz414 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz624 qz617) qz602)

noncomputable abbrev qz73 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz414))

noncomputable def Ns348p470 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz64) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz72) qz73) Bool.false 55221936373625 

noncomputable def Ns348p471 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz72) qz73 37562749 33554432 279 

noncomputable abbrev qz74 := (@Neg.neg Real Real.instNeg (Real.cos qz413))

noncomputable def Ns348p472 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz72) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz74)) Bool.true 37562749 33554432 279 33554432 (BSN.inv_eq_neg_inv_neg qz72) 

noncomputable def Ns348p473 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz74) Bool.false 37562749 33554432 279 33554432 37562749 33554432 

noncomputable def Ns348p474 := @Enclosure.Real.IsNear.recentre' qz72 Bool.true 29973842 33554432 1170904432 177502945280000 14986921 16777216 73181527 11093934080000 

noncomputable abbrev qz75 := qz413

noncomputable def Ns348p475 := @Enclosure.Real.IsNear.cos_image qz75 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44885913) qz377) Bool.false 44885913 16777216 215 33554432 Bool.true 29973842 33554432 1 

noncomputable def Ns348p476 := nat_lit 458763282015113676325220919 

noncomputable def Ns348p477 := nat_lit 72057594037927936000000000000000 

noncomputable def Ns348p478 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz64 884279719003555 140737488355328 1 500000000000000 7143815 16777216 17 16777216 6317130720813381262325 2361183241434822606848 Ns348p476 

noncomputable def Ns348p479 := @Enclosure.Real.IsNear.subLit_ff_p qz71 qz1 174915975 16777216 17 16777216 10 1 0 1 7143815 7143815 16777216 17 

noncomputable def Ns348p480 := @Ns348p479 16777216 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 349831950 33554432 34 33554432 174915975 16777216 17 16777216 (Ns348p466 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns348p481 := @Enclosure.Real.IsNear.recentre' qz75 Bool.false 6317130720813381262325 2361183241434822606848 Ns348p476 Ns348p477 44885913 16777216 215 33554432 (@Ns348p478 Ns348p477 RS349to360.d47 (Ns348p480 rfl rfl) rfl) 

noncomputable def Ns348p482 := nat_lit 2670789320315165638393856 

noncomputable def Ns348p483 := nat_lit 2240135204580714016845911984964523244084056013010889331579607372620349347501541053594054625 

noncomputable def Ns348p484 := nat_lit 1102347720920891468724318261002232421508931982369331017959348128802763635374915542822881 

noncomputable def Ns348p485 := nat_lit 5865236020448950505551834873913081072490084620390397903917513697987615245189619562819858401 

noncomputable def Ns348p486 := BSN.sin_dyadic_bound_f 75908398011 68719476736 3 2 33554432 10590333 Ns348p483 Ns348p190 Ns348p484 Ns348p485 Ns348p193 Ns348p484 29973842 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 75908398011) qz379 0 2 Ns348p483 Ns348p190 Ns348p484 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 75908398011) qz380 0 2 Ns348p485 Ns348p193 Ns348p484 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p487 := @Ns348p475 5290000 (Ns348p481 rfl) (Enclosure.sfrac_false_div 44885913 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44885913) qz377) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns348p482) qz381) 226375608064910080 72057594037927936 Bool.false 29973842 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q1 44885913 16777216 226375608064910080 72057594037927936 0 Ns348p482 Ns348p188 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 29973842 33554432 Ns348p482 Ns348p188 75908398011 68719476736 10590333 10580000 (Ns348p486 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p488 := @Enclosure.Real.IsNear.inv_image qz74 14986921 16777216 73181527 11093934080000 18781235 18781514 16777216 (@Enclosure.Real.IsNear.neg qz72 Bool.true 14986921 16777216 73181527 11093934080000 (Ns348p474 (Ns348p487 rfl rfl) rfl)) 

noncomputable def Ns348p489 := Ns348p472 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz74) Bool.false 37562749 33554432 279 33554432 (@Ns348p473 279 33554432 (Ns348p488 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p490 := @Enclosure.Real.IsNear.recentre' qz73 Bool.true 5880500 16777216 

noncomputable abbrev qz76 := (@HMul.hMul Real Real Real qz349 qz346 qz414)

noncomputable abbrev qz625 := (@Nat.cast Real Real.instNatCast 4194304)

noncomputable def Ns348p491 := @Enclosure.Real.IsNear.cos_image qz76 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8090421)) qz625) Bool.true 8090421 4194304 

noncomputable def Ns348p492 := nat_lit 76411866735028790086354816205 

noncomputable def Ns348p493 := nat_lit 39614081257132168796771975168 

noncomputable def Ns348p494 := nat_lit 14251418504065846412555237310429609 

noncomputable def Ns348p495 := @Enclosure.Real.IsNear.recentre' qz76 Bool.true Ns348p492 Ns348p493 Ns348p494 

noncomputable abbrev qz77 := qz414

noncomputable def Ns348p496 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz77 884279719003555 140737488355328 1 500000000000000 86411420609231 

noncomputable abbrev qz415 := (@HSub.hSub Real Real Real qz587 qz624 qz617)

noncomputable abbrev qz78 := qz415

noncomputable def Ns348p497 := @Enclosure.Real.IsNear.subLit_tf qz78 qz31 68819234564815 281474976710656 528102671 281474976710656 1 16 

noncomputable abbrev qz416 := qz624

noncomputable abbrev qz79 := qz416

noncomputable def Ns348p498 := @Enclosure.Real.IsNear.subLit_ff_n qz79 qz64 51034092754225 281474976710656 242889999 281474976710656 7143815 16777216 17 16777216 

noncomputable def Ns348p499 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz64 7143815 16777216 17 16777216 7143815 16777216 17 16777216 51034092754225 281474976710656 

noncomputable def Ns348p500 := nat_lit 8257670946128853670406792632634619633047613855411870432281242367668331533875939001323921 

noncomputable def Ns348p501 := nat_lit 14198936579076412752333613960380805571166435299025227571149477343212749250185412581785600 

noncomputable def Ns348p502 := nat_lit 78641802329246314014771419344781824755760277069981246888243202372903970963363287441 

noncomputable def Ns348p503 := nat_lit 49823188114335553138191851396367701392832843760084519635997194797246835814061298108944785 

noncomputable def Ns348p504 := nat_lit 1292103228695953560462358870394653306976145612211295708974602438232360181766872544942489600 

noncomputable def Ns348p505 := BSN.cos_dyadic_bound_t 8090421 4194304 4 3 16777216 5290000 Ns348p500 Ns348p501 Ns348p502 Ns348p503 Ns348p504 Ns348p502 5880500 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 8090421) (BSN.cosEvenQ 4194304) 0 3 Ns348p500 Ns348p501 Ns348p502 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 8090421) (BSN.cosOddQ 4194304) 0 3 Ns348p503 Ns348p504 Ns348p502 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p506 := @Ns348p490 2133684432 177502945280000 1470125 4194304 133355277 11093934080000 (@Ns348p491 397 33554432 Bool.true 5880500 16777216 1 5290000 (@Ns348p495 Ns348p335 8090421 4194304 397 33554432 (@Ns348p496 281474976710656 528102671 281474976710656 Ns348p492 Ns348p493 Ns348p494 Ns348p335 RS349to360.d47 (@Ns348p497 0 1 1382582729747696 86411420609231 281474976710656 528102671 281474976710656 (@Ns348p498 1154595163248567255040 68819234564815 281474976710656 528102671 281474976710656 (@Ns348p499 242889999 281474976710656 (Ns348p480 rfl rfl) (Ns348p480 rfl rfl) rfl) (Ns348p480 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 8090421 4194304) (BSN.cos_neg_of_bound 8090421 4194304 Bool.true 5880500 16777216 1 5290000 (Ns348p505 rfl rfl)) rfl rfl) 

noncomputable def Ns348p507 := @Ns348p464 345769483184522341679 Ns348p380 (Ns348p465 qz33 (@Enclosure.Real.IsNear.of_eq qz622 (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 324747 1048576 1 16777216 (BSN.rpow_neg_quarter_mk qz63 (BSN.t_div_two_pi_nonneg qz62 682966 1000 qz65)) Ns348p469) rfl) (@Ns348p470 140737488355328 1523528524568439 93062664174960640000 (BSN.correction_mk qz64 (BSN.cos_two_pi_p_ne_zero_mk qz62 682966 1000 10 qz65 rfl rfl (@BSN.floor_sqrt_eq_dec qz62 682966 1000 10 qz65 rfl rfl rfl))) (@Ns348p471 33554432 1470125 4194304 133355277 11093934080000 55221936373625 140737488355328 1523528524568439 93062664174960640000 Ns348p489 (Ns348p506 rfl) rfl)) 

noncomputable def Ns348p508 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (hardyZApproximantRS₀ qz62) Bool.true 138866146330329041587 147573952589676412928 78136547001824855141679 Ns348p380 (@Eq.refl Real (hardyZApproximantRS₀ qz62)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 10) (@HMul.hMul Real Real Real qz5 qz618 (Zeta.RiemannSiegel.correction qz64))) Bool.true 138866146330329041587 147573952589676412928 78136547001824855141679 Ns348p380 (BSN.hardyZApproximantRS₀_eq qz62 10 (@BSN.floor_sqrt_eq_dec qz62 682966 1000 10 qz65 rfl rfl rfl)) (@Ns348p382 138866146330329041587 147573952589676412928 78136547001824855141679 Ns348p380 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 10)) Bool.true 13748489 16777216 153805 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz62) qz62 10) (Ns348p463 (Ns348p462 rfl rfl rfl rfl) rfl rfl)) (Ns348p507 rfl) rfl rfl)) 

theorem RS349to360.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz62) Bool.true 138866146330329041587 147573952589676412928 78136547001824855141679 Ns348p380 := Ns348p508 

noncomputable def Ns348p509 := nat_lit 97583276149923528048640000 

noncomputable def Ns348p510 := nat_lit 7183551323673585486730887168 

noncomputable abbrev qz755 := (Enclosure.sfrac Bool.false 684557 1000)

noncomputable abbrev qz626 := qz755

noncomputable abbrev qz417 := qz626

noncomputable abbrev qz80 := qz417

noncomputable abbrev qz756 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 684557 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz627 := qz756

noncomputable abbrev qz418 := qz627

noncomputable abbrev qz81 := qz418

noncomputable abbrev qz757 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 684557 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz628 := qz757

noncomputable abbrev qz419 := qz628

noncomputable abbrev qz82 := qz419

noncomputable abbrev qz629 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz81 qz9))

noncomputable def Ns348p511 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 10) (@HMul.hMul Real Real Real qz5 qz629 (Zeta.RiemannSiegel.correction qz82)) 14191799 16777216 154163 134217728 71156511752562703045 590295810358705651712 469703961841276443493 Ns348p509 Ns348p510 

noncomputable def Ns348p512 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin BSN.quadSignPos 9 10 684557 1000 199 268435456 134217728 4503599627370496 Bool.false 339012850560 2468 618095470 52 84886744 8 

noncomputable def Ns348p513 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 684557 1000 102 153 268435456 134217728 4503599627370496 Bool.false 339012850560 2468 

noncomputable def Ns348p514 := Ns348p513 558195838 52 94906264 8 589812974 52 89478488 8 Bool.false 213790214 115949 Bool.true 94960030 Bool.true 234162957 14148475504056880 1 Bool.false 251813656 Bool.true Bool.false 205574874 Bool.true Bool.false 56235683 

noncomputable def Ns348p515 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 684557 1000 23 44 268435456 134217728 4503599627370496 Bool.false 339012850560 2468 

noncomputable def Ns348p516 := Ns348p515 480971758 52 109588312 8 522351262 52 101459064 8 Bool.false 87313254 86002 Bool.false 62145968 Bool.true 13435457 14148475504056880 1 Bool.false 61592307 Bool.false Bool.false 268099297 Bool.false Bool.false 213790214 

noncomputable def Ns348p517 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 684557 1000 199 102 268435456 134217728 4503599627370496 Bool.false 339012850560 2468 

noncomputable def Ns348p518 := Ns348p517 372130544 51 134217720 8 432030192 51 120047984 16 Bool.false 26815116 50566 Bool.false 358453525 Bool.false 254500731 14148475504056880 1 Bool.false 261028996 Bool.false Bool.false 156561323 Bool.true Bool.false 87313254 

noncomputable def Ns348p519 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 684557 1000 501 325 268435456 134217728 4503599627370496 Bool.false 339012850560 2468 

noncomputable def Ns348p520 := Ns348p519 186065264 51 189812528 16 294906480 51 154981288 8 Bool.false 268435304 2523 Bool.false 390200070 Bool.false 93891144 14148475504056880 1 Bool.false 266594355 Bool.true Bool.false 91988375 Bool.true Bool.false 26815116 

noncomputable def Ns348p521 := nat_lit 1316973281978252007354244157327269638775736040846767513471 

noncomputable def Ns348p522 := nat_lit 1042799182696667390253578360232223249881695344656384000 

noncomputable def Ns348p523 := nat_lit 2166784000000000000000000 

noncomputable def Ns348p524 := nat_lit 72158899809592181014009526987360000 

noncomputable def Ns348p525 := nat_lit 296381353648674630180033307235653197120 

noncomputable abbrev qz630 := (@Eq.refl Real qz755)

noncomputable abbrev qz420 := qz630

noncomputable abbrev qz83 := qz420

noncomputable def Ns348p526 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz80 684557 1000 1874474144996 16000000 1369114 4000 2000 Ns348p524 Ns348p525 qz83 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns348p527 := nat_lit 421431450233040642353358130344726284408235533070965604310720 

noncomputable abbrev qz631 := (@HSub.hSub Real Real Real qz742 qz743 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz744 (@Nat.cast Real Real.instNatCast 1369114))))

noncomputable abbrev qz421 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 684557 4000) (Real.log (Enclosure.sfrac Bool.false 1874474144996 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz631))

noncomputable abbrev qz632 := (Enclosure.sfrac Bool.false 684557 2000)

noncomputable abbrev qz84 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz421 qz632) (@HMul.hMul Real Real Real qz349 qz632 (Real.log Real.pi)))

noncomputable def Ns348p528 := @Enclosure.Real.IsNear.addLit_ft_p qz84 (Enclosure.sfrac Bool.true Ns348p524 Ns348p525) 1421923229274055210031 1125899906842624000 19916086027804232377 Ns348p523 Ns348p524 Ns348p525 0 1 Ns348p527 

noncomputable def Ns348p529 := nat_lit 95423652611793389818461814784000 

noncomputable abbrev qz85 := (@HSub.hSub Real Real Real qz353 qz421 qz632)

noncomputable def Ns348p530 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (@HMul.hMul Real Real Real qz5 qz632 (Real.log Real.pi)) 1863069308022826300463 1125899906842624000 2164242073588737 529000000000000000000 26294355317877 67108864000 684557 134217728000 Ns348p529 1421923229274055210031 1125899906842624000 

noncomputable def Ns348p531 := nat_lit 3726138616045652600926000 

noncomputable abbrev qz86 := qz421

noncomputable def Ns348p532 := @Enclosure.Real.IsNear.subLit_ff_p qz86 qz632 2248440639287059379247 1125899906842624000 2164242073588737 529000000000000000000 684557 2000 0 1 Ns348p531 1863069308022826300463 1125899906842624000 2164242073588737 529000000000000000000 

noncomputable def Ns348p533 := nat_lit 5063038212628940214698469546321248256 

noncomputable def Ns348p534 := nat_lit 56438701852312158773182464 

noncomputable def Ns348p535 := nat_lit 6738555747212835795278322559905385592535486994009210442624436750290783474753605737591516392045296285031846894321226331819718871935225136430146617291490659270992393498191114692198400 

noncomputable def Ns348p536 := nat_lit 188430512490528424214194734765522872620529815985054727911110668240757209761455748673178171557692445754952359505796237063536419497078477053911148234863425216411509527315670410199040 

noncomputable def Ns348p537 := nat_lit 9284076606823164035793880846220848658031758333229139992077975902728501605998882065927096285996419137661261877121727052048427743115880485141402567236182874904556097566146560 

noncomputable def Ns348p538 := BSN.log_dyadic_bound 825898144996 2923050144996 8 7 Ns348p535 134217728 42320000 Ns348p536 Ns348p537 77966421 3748948289992 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 825898144996) (BSN.artanhQ 2923050144996) 0 7 Ns348p536 Ns348p535 Ns348p537 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz422 := (Real.log (Enclosure.sfrac Bool.false 1874474144996 16000000))

noncomputable def Ns348p539 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 684557 4000) qz422 684557 4000 0 1 3285164819815671 281474976710656 781250529 33062500000000000 2248882573558556292747 1125899906842624000 534810518380653 132250000000000000000 (Enclosure.Real.IsNear.const Bool.false 684557 4000) (BSN.isNear_log_sfrac 1874474144996 16000000 3285164819815671 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1874474144996) qz356)) Bool.false Ns348p534 Ns348p99 1000000677120000 42320000000000000000000 3285164819815671 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 1874474144996 16000000 16 3748948289992 2097152000000 77966421 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns348p538 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p540 := BSN.arctan_dyadic_bound_f 1000 1369114 1 0 16777216 5290000 0 1 1 0 1 1 12254 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1369114) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1369114) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns348p541 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1369114))) 884279719003555 562949953421312 1 2000000000000000 12254 16777216 1 5290000 14828853461412722245632 883868542993827 562949953421312 200000000529 1058000000000000000 qz17 (Ns348p540 rfl) rfl rfl 

noncomputable abbrev qz423 := (@HMul.hMul Real Real Real qz583 qz588 qz631)

noncomputable abbrev qz87 := qz423

noncomputable abbrev qz424 := qz631

noncomputable abbrev qz88 := qz424

noncomputable def Ns348p542 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 684557 4000) qz422) qz87 2248882573558556292747 1125899906842624000 534810518380653 132250000000000000000 883868542993827 2251799813685248 200000000529 4232000000000000000 Ns348p533 2248440639287059379247 1125899906842624000 2164242073588737 529000000000000000000 (Ns348p539 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz88 1 4 0 1 883868542993827 562949953421312 200000000529 1058000000000000000 883868542993827 2251799813685248 200000000529 4232000000000000000 qz364 Ns348p541 rfl) 

noncomputable def Ns348p543 := @Ns348p528 Ns348p521 Ns348p522 19916086027804232377 Ns348p523 (@Ns348p530 19916086027804232377 Ns348p523 (Ns348p532 (Ns348p542 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 684557 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz632 (Real.log Real.pi) 684557 2000 0 1 38410761 33554432 1 67108864 26294355317877 67108864000 684557 134217728000 (Enclosure.Real.IsNear.const Bool.false 684557 2000) RS349to360.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns348p524 Ns348p525) 

noncomputable def Ns348p544 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz80) Bool.false Ns348p521 Ns348p522 19916086027804232377 Ns348p523 2648537895 2097152 309 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz80) (@HAdd.hAdd Real Real Real qz365 qz84 (Enclosure.sfrac Bool.true Ns348p524 Ns348p525)) Bool.false Ns348p521 Ns348p522 19916086027804232377 Ns348p523 Ns348p526 (Ns348p543 rfl rfl)) 

noncomputable def Ns348p545 := BSN.cos_dyadic_bound_f 71227874 68719476736 1 0 33554432 10590333 0 1 1 0 1 1 33554413 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 71227874) qz594 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 71227874) qz595 0 0 rfl) rfl rfl 

noncomputable def Ns348p546 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz80) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2648537895) (@Nat.cast Real Real.instNatCast 2097152)) Bool.false 2648537895 2097152 309 33554432 Bool.false 33554413 33554432 1 5290000 (Ns348p544 rfl) (Enclosure.sfrac_false_div 2648537895 2097152) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2648537895) (@Nat.cast Real Real.instNatCast 2097152)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 313263504399060172800) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 33554413 33554432 201 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q0 2648537895 2097152 226375608064910080 72057594037927936 201 313263504399060172800 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554413 33554432 313263504399060172800 302231454903657293676544 71227874 68719476736 10590333 10580000 (Ns348p545 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p547 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz80) Bool.false Ns348p521 Ns348p522 19916086027804232377 Ns348p523 339012850560 268435456 2468 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz80) (@HAdd.hAdd Real Real Real qz365 qz84 (Enclosure.sfrac Bool.true Ns348p524 Ns348p525)) Bool.false Ns348p521 Ns348p522 19916086027804232377 Ns348p523 Ns348p526 (Ns348p543 rfl rfl)) 

noncomputable def Ns348p548 := Ns348p520 50566 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 501 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 266594355 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 325 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 91988375 268435456) qz83 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 1) Bool.false 33554413 33554432 104260277 11093934080000 268435304 268435456 2523 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz80)) Bool.false 33554413 33554432 104260277 11093934080000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz80) qz80) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz80)) Bool.false 33554413 33554432 1668164432 177502945280000 33554413 33554432 104260277 11093934080000 (Ns348p546 rfl rfl) rfl)) rfl) (Ns348p547 rfl) RS349to360.d7 

noncomputable def Ns348p549 := nat_lit 32479427310070911450121653200412718450743361486951192264524407628949405916638349472592639528984501178534400000 

noncomputable def Ns348p550 := nat_lit 12457993949858435343814200806567759666800144678454322655105169301949740332001281101583607201000000000000 

noncomputable def Ns348p551 := nat_lit 162249086698573054116261564922364559808771976063906573974955423669037741093822300477214587057172469508672000000 

noncomputable def Ns348p552 := BSN.sin_dyadic_bound_f 390200070 268435456 4 3 268435456 134217728 Ns348p549 Ns348p131 Ns348p550 Ns348p551 Ns348p134 Ns348p550 266594355 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 390200070) qz370 0 3 Ns348p549 Ns348p131 Ns348p550 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 390200070) qz371 0 3 Ns348p551 Ns348p134 Ns348p550 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p553 := nat_lit 77713867527437883659239020957696 

noncomputable def Ns348p554 := BSN.sin_dyadic_bound_f 93891144 268435456 2 1 268435456 134217728 Ns348p553 Ns348p137 Ns348p553 Ns348p553 Ns348p138 Ns348p553 91988375 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 93891144) qz370 0 1 Ns348p553 Ns348p137 Ns348p553 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 93891144) qz371 0 1 Ns348p553 Ns348p138 Ns348p553 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p555 := nat_lit 23120967669671566236266994290819134781216924089637168274569026391266466669817545860586046003349014948619140625 

noncomputable def Ns348p556 := nat_lit 4499810934217721247211311654656080845529441096716005033802286734474432069449230389075338840484619140625 

noncomputable def Ns348p557 := nat_lit 115529757356617110543565509547968168092001673039384286464303653582694565551660633873774405452989712804619140625 

noncomputable def Ns348p558 := BSN.sin_dyadic_bound_f 358453525 268435456 4 3 268435456 134217728 Ns348p555 Ns348p131 Ns348p556 Ns348p557 Ns348p134 Ns348p556 261028996 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 358453525) qz370 0 3 Ns348p555 Ns348p131 Ns348p556 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 358453525) qz371 0 3 Ns348p557 Ns348p134 Ns348p556 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p559 := nat_lit 36612868023813791638695948905275676521566656258758286597215772918589921 

noncomputable def Ns348p560 := nat_lit 17599983990056203920390856913521268902353856360332651047271837379041 

noncomputable def Ns348p561 := nat_lit 109803404103461262508247065001999987026895261063554194489552775081011681 

noncomputable def Ns348p562 := BSN.cos_dyadic_bound_f 254500731 268435456 3 2 268435456 134217728 Ns348p559 Ns348p121 Ns348p560 Ns348p561 Ns348p124 Ns348p560 156561323 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 254500731) qz368 0 2 Ns348p559 Ns348p121 Ns348p560 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 254500731) qz369 0 2 Ns348p561 Ns348p124 Ns348p560 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p563 := Ns348p518 86002 BSN.abs_quadSignPos qz372 (BSN.sfrac_eq_quadSignPos_mul Bool.false 261028996 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 102 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 156561323 268435456) qz83 rfl rfl (Ns348p548 RS349to360.d9 RS349to360.d11 RS349to360.d13 RS349to360.d17 (Ns348p552 rfl rfl) (Ns348p554 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns348p547 rfl) RS349to360.d19 RS349to360.d21 RS349to360.d23 RS349to360.d25 RS349to360.d17 (Ns348p558 rfl rfl) (Ns348p562 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns348p564 := nat_lit 14915981234509923064387904536576 

noncomputable def Ns348p565 := BSN.sin_dyadic_bound_f 62145968 268435456 2 1 268435456 134217728 Ns348p564 Ns348p137 Ns348p564 Ns348p564 Ns348p138 Ns348p564 61592307 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 62145968) qz370 0 1 Ns348p564 Ns348p137 Ns348p564 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 62145968) qz371 0 1 Ns348p564 Ns348p138 Ns348p564 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p566 := nat_lit 32584403364744885555951724801 

noncomputable def Ns348p567 := nat_lit 124615124604835863084731911901282304 

noncomputable def Ns348p568 := nat_lit 1869226869072537946270978678519234560 

noncomputable def Ns348p569 := BSN.cos_dyadic_bound_f 13435457 268435456 2 1 268435456 134217728 Ns348p566 Ns348p567 Ns348p566 Ns348p566 Ns348p568 Ns348p566 268099297 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 13435457) qz368 0 1 Ns348p566 Ns348p567 Ns348p566 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 13435457) qz369 0 1 Ns348p566 Ns348p568 Ns348p566 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p570 := Ns348p516 115949 BSN.abs_quadSignPos (BSN.cos_quad_nat3 23 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 61592307 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 44 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268099297 268435456) qz83 rfl rfl (Ns348p563 rfl rfl) (Ns348p547 rfl) RS349to360.d27 RS349to360.d29 RS349to360.d31 RS349to360.d33 RS349to360.d17 (Ns348p565 rfl rfl) (Ns348p569 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p571 := nat_lit 709310219450612532229348757993285979690035948502993457028233136800000 

noncomputable def Ns348p572 := nat_lit 6611907134592369940161373268640042308530452926873402256100000000 

noncomputable def Ns348p573 := nat_lit 2127917434537568411948165951233320658985490784603126624280187210400000 

noncomputable def Ns348p574 := BSN.cos_dyadic_bound_f 94960030 268435456 3 2 268435456 134217728 Ns348p571 Ns348p121 Ns348p572 Ns348p573 Ns348p124 Ns348p572 251813656 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 94960030) qz368 0 2 Ns348p571 Ns348p121 Ns348p572 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 94960030) qz369 0 2 Ns348p573 Ns348p124 Ns348p572 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p575 := nat_lit 47216873692339314384948949468941247048316325905034952316555479330179105 

noncomputable def Ns348p576 := nat_lit 9039523740819209461776616238331946138158849913005819384067680749601 

noncomputable def Ns348p577 := nat_lit 123648605203403544669071038849507871499461929708565722835785383905445921 

noncomputable def Ns348p578 := BSN.sin_dyadic_bound_f 234162957 268435456 3 2 268435456 134217728 Ns348p575 Ns348p162 Ns348p576 Ns348p577 Ns348p165 Ns348p576 205574874 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 234162957) qz370 0 2 Ns348p575 Ns348p162 Ns348p576 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 234162957) qz371 0 2 Ns348p577 Ns348p165 Ns348p576 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p579 := Ns348p514 142115 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 102 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 251813656 268435456) BSN.abs_quadSignNeg qz597 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 205574874 268435456) qz83 rfl rfl (Ns348p570 rfl) (Ns348p547 rfl) RS349to360.d35 RS349to360.d37 RS349to360.d39 RS349to360.d41 RS349to360.d17 (Ns348p574 rfl rfl) (Ns348p578 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p580 := nat_lit 24577633497363940689232351938289093520047590056510572191830274618873985 

noncomputable def Ns348p581 := nat_lit 2449688972576609792758557361046909957556796870262327588674196396161 

noncomputable def Ns348p582 := nat_lit 64366026329997577770229788840744026126860024857832978638697627683838081 

noncomputable def Ns348p583 := BSN.sin_dyadic_bound_f 198901871 268435456 3 2 268435456 134217728 Ns348p580 Ns348p162 Ns348p581 Ns348p582 Ns348p165 Ns348p581 181194429 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 198901871) qz370 0 2 Ns348p580 Ns348p162 Ns348p581 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 198901871) qz371 0 2 Ns348p582 Ns348p165 Ns348p581 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p584 := Ns348p512 Bool.false 56235683 142115 Bool.true 198901871 14148475504056880 1 Bool.false 181194429 Bool.false Bool.false 113534392 154163 BSN.abs_quadSignPos qz372 (BSN.sfrac_eq_quadSignPos_mul Bool.false 181194429 268435456) qz83 rfl (Ns348p579 rfl) (Ns348p547 rfl) RS349to360.d43 RS349to360.d45 RS349to360.d17 (Ns348p583 rfl rfl) rfl 

noncomputable def Ns348p585 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 10) 113534392 268435456 154163 268435456 113534392 268435456 154163 268435456 60953312576405504 14191799 16777216 154163 134217728 (Ns348p584 rfl rfl rfl rfl) 

noncomputable def Ns348p586 := @Enclosure.Real.IsNear.mulLit_ff qz629 (Zeta.RiemannSiegel.correction qz82) 2596465 8388608 1 16777216 27405149598613 70368744177664 360057743840437 23265666043740160000 71156511752562703045 590295810358705651712 

noncomputable abbrev qz633 := (@HPow.hPow Real Real Real qz7 qz81 qz9)

noncomputable def Ns348p587 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz633 1 1 0 1 2596465 8388608 1 16777216 2596465 8388608 1 16777216 

noncomputable def Ns348p588 := @Enclosure.Real.IsNear.sqrt_image qz81 3655776028621 33554432000 684557 33554432000 175119577 175119610 16777216 (@Enclosure.Real.IsNear.of_eq qz81 (@HMul.hMul Real Real Real qz5 qz80 qz3) Bool.false 3655776028621 33554432000 684557 33554432000 (BSN.t_div_two_pi_mk qz80 684557 1000 qz83) (@Enclosure.Real.IsNear.mulLit_ff qz80 qz3 684557 1000 0 1 5340353 33554432 1 33554432 3655776028621 33554432000 684557 33554432000 (Enclosure.Real.IsNear.const Bool.false 684557 1000) RS349to360.d48 rfl)) 

noncomputable abbrev qz758 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 684557 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz634 := qz758

noncomputable abbrev qz425 := qz634

noncomputable abbrev qz89 := qz425

noncomputable def Ns348p589 := @Enclosure.Real.IsNear.sqrt_image qz89 350239187 33554432 33 33554432 54203495 54203502 16777216 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 350239187 33554432 33 33554432 350239187 33554432 33 33554432 (Ns348p588 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns348p590 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz89) 108406997 33554432 7 33554432 5192929 5192931 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz89) Bool.false 108406997 33554432 7 33554432 108406997 33554432 7 33554432 (Ns348p589 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns348p591 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 10385860 33554432 2 33554432 2596465 8388608 1 16777216 (Ns348p590 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz426 := (@HMul.hMul Real Real Real qz583 qz581 qz628)

noncomputable abbrev qz90 := (Real.cos qz426)

noncomputable abbrev qz635 := (@HMul.hMul Real Real Real qz738 qz757 qz757)

noncomputable abbrev qz427 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz635 qz628) qz602)

noncomputable abbrev qz91 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz427))

noncomputable def Ns348p592 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz82) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz90) qz91) Bool.false 27405149598613 

noncomputable def Ns348p593 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz90) qz91 4534693 4194304 63 

noncomputable abbrev qz92 := (@Neg.neg Real Real.instNeg (Real.cos qz426))

noncomputable def Ns348p594 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz90) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz92)) Bool.true 4534693 4194304 63 8388608 (BSN.inv_eq_neg_inv_neg qz90) 

noncomputable def Ns348p595 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz92) Bool.false 36277544 33554432 252 33554432 4534693 4194304 

noncomputable def Ns348p596 := @Enclosure.Real.IsNear.recentre' qz90 Bool.true 31035726 33554432 70867152 11093934080000 15517863 16777216 4429197 693370880000 

noncomputable abbrev qz93 := qz426

noncomputable abbrev qz636 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable def Ns348p597 := @Enclosure.Real.IsNear.cos_image qz93 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23082643) qz636) Bool.false 23082643 8388608 13 2097152 Bool.true 31035726 33554432 1 

noncomputable def Ns348p598 := nat_lit 35621619544987257855548607 

noncomputable def Ns348p599 := nat_lit 5764607523034234880000000000000 

noncomputable def Ns348p600 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz82 884279719003555 140737488355328 1 500000000000000 14694867 33554432 33 33554432 12994372861554613252185 4722366482869645213696 Ns348p598 

noncomputable def Ns348p601 := @Enclosure.Real.IsNear.subLit_ff_p qz89 qz1 350239187 33554432 33 33554432 10 1 0 1 14694867 14694867 33554432 33 

noncomputable def Ns348p602 := @Ns348p601 33554432 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 350239187 33554432 33 33554432 350239187 33554432 33 33554432 (Ns348p588 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns348p603 := @Enclosure.Real.IsNear.recentre' qz93 Bool.false 12994372861554613252185 4722366482869645213696 Ns348p598 Ns348p599 23082643 8388608 13 2097152 (@Ns348p600 Ns348p599 RS349to360.d47 (Ns348p602 rfl rfl) rfl) 

noncomputable def Ns348p604 := nat_lit 1427583200414668796461056 

noncomputable def Ns348p605 := nat_lit 1208925819614629174706176 

noncomputable def Ns348p606 := nat_lit 2926218898454250590624949884986400517013599677401219577865771612161231269935013388087668705 

noncomputable def Ns348p607 := nat_lit 1880411744728897890133350118142489787197118703140629790546520198066695979488836565020641 

noncomputable def Ns348p608 := nat_lit 7660862162650619045528938560487389703951584772436204541416136046768259627767767423886241761 

noncomputable def Ns348p609 := BSN.sin_dyadic_bound_f 81148709819 68719476736 3 2 33554432 10590333 Ns348p606 Ns348p190 Ns348p607 Ns348p608 Ns348p193 Ns348p607 31035726 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 81148709819) qz379 0 2 Ns348p606 Ns348p190 Ns348p607 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 81148709819) qz380 0 2 Ns348p608 Ns348p193 Ns348p607 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p610 := @Ns348p597 5290000 (Ns348p603 rfl) (Enclosure.sfrac_false_div 23082643 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23082643) qz636) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns348p604) (@Nat.cast Real Real.instNatCast Ns348p605)) 226375608064910080 72057594037927936 Bool.false 31035726 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q1 23082643 8388608 226375608064910080 72057594037927936 0 Ns348p604 Ns348p605 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 31035726 33554432 Ns348p604 Ns348p605 81148709819 68719476736 10590333 10580000 (Ns348p609 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p611 := @Enclosure.Real.IsNear.inv_image qz92 15517863 16777216 4429197 693370880000 18138646 18138898 16777216 (@Enclosure.Real.IsNear.neg qz90 Bool.true 15517863 16777216 4429197 693370880000 (Ns348p596 (Ns348p610 rfl rfl) rfl)) 

noncomputable def Ns348p612 := Ns348p594 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz92) Bool.false 4534693 4194304 63 8388608 (@Ns348p595 63 8388608 (Ns348p611 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p613 := @Enclosure.Real.IsNear.recentre' qz91 Bool.true 6043441 16777216 

noncomputable abbrev qz94 := (@HMul.hMul Real Real Real qz349 qz346 qz427)

noncomputable def Ns348p614 := @Enclosure.Real.IsNear.cos_image qz94 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8134001)) qz625) Bool.true 8134001 4194304 

noncomputable def Ns348p615 := nat_lit 307293872944782998561411995045 

noncomputable def Ns348p616 := nat_lit 56054357728588935366695385202403537 

noncomputable def Ns348p617 := @Enclosure.Real.IsNear.recentre' qz94 Bool.true Ns348p615 Ns348p201 Ns348p616 

noncomputable abbrev qz95 := qz427

noncomputable def Ns348p618 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz95 884279719003555 140737488355328 1 500000000000000 347507543530519 

noncomputable abbrev qz428 := (@HSub.hSub Real Real Real qz587 qz635 qz628)

noncomputable abbrev qz96 := qz428

noncomputable def Ns348p619 := @Enclosure.Real.IsNear.subLit_tf qz96 qz31 277138799352855 1125899906842624 2077158567 1125899906842624 1 16 

noncomputable abbrev qz429 := qz635

noncomputable abbrev qz97 := qz429

noncomputable def Ns348p620 := @Enclosure.Real.IsNear.subLit_ff_n qz97 qz82 215939116147689 1125899906842624 969862311 1125899906842624 14694867 33554432 33 33554432 

noncomputable def Ns348p621 := @Enclosure.Real.IsNear.mulLit_ff qz82 qz82 14694867 33554432 33 33554432 14694867 33554432 33 33554432 215939116147689 1125899906842624 

noncomputable def Ns348p622 := nat_lit 8438538655450819096121014192834490805139354969852231518428490066288927381371917973455681 

noncomputable def Ns348p623 := nat_lit 83878500417592208780393713335547483003316024462224196663634252335547709569193608001 

noncomputable def Ns348p624 := nat_lit 50908439285482359701150427330042700570401895029345097660992168407262048100819739541635905 

noncomputable def Ns348p625 := BSN.cos_dyadic_bound_t 8134001 4194304 4 3 16777216 5290000 Ns348p622 Ns348p501 Ns348p623 Ns348p624 Ns348p504 Ns348p623 6043441 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 8134001) (BSN.cosEvenQ 4194304) 0 3 Ns348p622 Ns348p501 Ns348p623 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 8134001) (BSN.cosOddQ 4194304) 0 3 Ns348p624 Ns348p504 Ns348p623 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p626 := @Ns348p613 1048327216 88751472640000 6043441 16777216 65520451 5546967040000 (@Ns348p614 195 16777216 Bool.true 6043441 16777216 1 5290000 (@Ns348p617 Ns348p204 8134001 4194304 195 16777216 (@Ns348p618 1125899906842624 2077158567 1125899906842624 Ns348p615 Ns348p201 Ns348p616 Ns348p204 RS349to360.d47 (@Ns348p619 0 1 5560120696488304 347507543530519 1125899906842624 2077158567 1125899906842624 (@Ns348p620 9299234997447017103360 277138799352855 1125899906842624 2077158567 1125899906842624 (@Ns348p621 969862311 1125899906842624 (Ns348p602 rfl rfl) (Ns348p602 rfl rfl) rfl) (Ns348p602 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 8134001 4194304) (BSN.cos_neg_of_bound 8134001 4194304 Bool.true 6043441 16777216 1 5290000 (Ns348p625 rfl rfl)) rfl rfl) 

noncomputable def Ns348p627 := @Ns348p586 469703961841276443493 Ns348p509 (Ns348p587 qz33 (@Enclosure.Real.IsNear.of_eq qz633 (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 2596465 8388608 1 16777216 (BSN.rpow_neg_quarter_mk qz81 (BSN.t_div_two_pi_nonneg qz80 684557 1000 qz83)) Ns348p591) rfl) (@Ns348p592 70368744177664 360057743840437 23265666043740160000 (BSN.correction_mk qz82 (BSN.cos_two_pi_p_ne_zero_mk qz80 684557 1000 10 qz83 rfl rfl (@BSN.floor_sqrt_eq_dec qz80 684557 1000 10 qz83 rfl rfl rfl))) (@Ns348p593 8388608 6043441 16777216 65520451 5546967040000 27405149598613 70368744177664 360057743840437 23265666043740160000 Ns348p612 (Ns348p626 rfl) rfl)) 

noncomputable def Ns348p628 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz80) (hardyZApproximantRS₀ qz80) Bool.false 428173024873351185723 590295810358705651712 112554231283751097883493 Ns348p509 (@Eq.refl Real (hardyZApproximantRS₀ qz80)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz80) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 10) (@HMul.hMul Real Real Real qz5 qz629 (Zeta.RiemannSiegel.correction qz82))) Bool.false 428173024873351185723 590295810358705651712 112554231283751097883493 Ns348p509 (BSN.hardyZApproximantRS₀_eq qz80 10 (@BSN.floor_sqrt_eq_dec qz80 684557 1000 10 qz83 rfl rfl rfl)) (@Ns348p511 428173024873351185723 590295810358705651712 112554231283751097883493 Ns348p509 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 10)) Bool.false 14191799 16777216 154163 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz80) qz80 10) (Ns348p585 (Ns348p584 rfl rfl rfl rfl) rfl rfl)) (Ns348p627 rfl) rfl rfl)) 

theorem RS349to360.d54 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz80) Bool.false 428173024873351185723 590295810358705651712 112554231283751097883493 Ns348p509 := Ns348p628 

noncomputable def Ns348p629 := nat_lit 62453296735951057951129600 

noncomputable def Ns348p630 := nat_lit 160841036417884552290870755328 

noncomputable abbrev qz759 := (Enclosure.sfrac Bool.false 685896 1000)

noncomputable abbrev qz637 := qz759

noncomputable abbrev qz430 := qz637

noncomputable abbrev qz98 := qz430

noncomputable abbrev qz760 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 685896 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz638 := qz760

noncomputable abbrev qz431 := qz638

noncomputable abbrev qz99 := qz431

noncomputable abbrev qz761 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 685896 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz639 := qz761

noncomputable abbrev qz432 := qz639

noncomputable abbrev qz100 := qz432

noncomputable abbrev qz640 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz99 qz9))

noncomputable def Ns348p631 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 10) (@HMul.hMul Real Real Real qz5 qz640 (Zeta.RiemannSiegel.correction qz100)) 60075759 67108864 154467 134217728 282990352073421108039 2361183241434822606848 304264360310741057787 Ns348p629 Ns348p630 

noncomputable def Ns348p632 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin BSN.quadSignPos 9 10 685896 1000 199 268435456 134217728 4503599627370496 Bool.false 339856062547 2473 618095470 52 84886744 8 

noncomputable def Ns348p633 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 685896 1000 101 153 268435456 134217728 4503599627370496 Bool.false 339856062547 2473 

noncomputable def Ns348p634 := Ns348p633 558195838 52 94906264 8 589812974 52 89478488 8 Bool.true 23025370 116179 Bool.true 420829698 Bool.true 180710542 14148475504056880 1 Bool.false 268434179 Bool.true Bool.false 167366937 Bool.true Bool.true 173720164 

noncomputable def Ns348p635 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 685896 1000 23 43 268435456 134217728 4503599627370496 Bool.false 339856062547 2473 

noncomputable def Ns348p636 := Ns348p635 480971758 52 109588312 8 522351262 52 101459064 8 Bool.true 203373497 86173 Bool.false 261336771 Bool.true 291309238 14148475504056880 1 Bool.false 221966681 Bool.false Bool.false 237404890 Bool.false Bool.true 23025370 

noncomputable def Ns348p637 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 685896 1000 200 103 268435456 134217728 4503599627370496 Bool.false 339856062547 2473 

noncomputable def Ns348p638 := Ns348p637 372130544 51 134217720 8 432030192 51 120047984 16 Bool.true 312892411 50668 Bool.false 281725286 Bool.false 97566863 14148475504056880 1 Bool.false 133680145 Bool.false Bool.false 95432801 Bool.false Bool.true 203373497 

noncomputable def Ns348p639 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 685896 1000 503 326 268435456 134217728 4503599627370496 Bool.false 339856062547 2473 

noncomputable def Ns348p640 := Ns348p639 186065264 51 189812528 16 294906480 51 154981288 8 Bool.true 268435392 2531 Bool.false 140955812 Bool.false 120565926 14148475504056880 1 Bool.false 134566875 Bool.false Bool.false 241811894 Bool.true Bool.true 312892411 

noncomputable def Ns348p641 := nat_lit 9059105139860450206428701634801663318792319709949267 

noncomputable def Ns348p642 := nat_lit 7155338059721769386694215594333790199984685056000 

noncomputable def Ns348p643 := nat_lit 72867383081190553943295528468480000 

noncomputable def Ns348p644 := nat_lit 299876753881089037657938619838115348480 

noncomputable abbrev qz641 := (@Eq.refl Real qz759)

noncomputable abbrev qz433 := qz641

noncomputable abbrev qz101 := qz433

noncomputable def Ns348p645 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz98 685896 1000 1881814291264 16000000 1371792 4000 2000 Ns348p643 Ns348p644 qz101 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns348p646 := nat_lit 106865552600261003651132050260905125306867223612022329180160 

noncomputable abbrev qz642 := (@HSub.hSub Real Real Real qz742 qz743 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz744 (@Nat.cast Real Real.instNatCast 1371792))))

noncomputable abbrev qz434 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 685896 4000) (Real.log (Enclosure.sfrac Bool.false 1881814291264 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz642))

noncomputable abbrev qz643 := (Enclosure.sfrac Bool.false 685896 2000)

noncomputable abbrev qz102 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz434 qz643) (@HMul.hMul Real Real Real qz349 qz643 (Real.log Real.pi)))

noncomputable def Ns348p647 := @Enclosure.Real.IsNear.addLit_ft_p qz102 (Enclosure.sfrac Bool.true Ns348p643 Ns348p644) 356364979037293640967 281474976710656000 2494355223255048357 270848000000000000000000 Ns348p643 Ns348p644 0 1 Ns348p646 

noncomputable def Ns348p648 := nat_lit 2989406114072073734964903936000 

noncomputable abbrev qz103 := (@HSub.hSub Real Real Real qz353 qz434 qz643)

noncomputable def Ns348p649 := @Enclosure.Real.IsNear.subLit_ff_p qz103 (@HMul.hMul Real Real Real qz5 qz643 (Real.log Real.pi)) 466867220205475069191 281474976710656000 2168426451422061 529000000000000000000 3293223415857 8388608000 85737 16777216000 Ns348p648 356364979037293640967 281474976710656000 

noncomputable abbrev qz104 := qz434

noncomputable def Ns348p650 := @Enclosure.Real.IsNear.subLit_ff_p qz104 qz643 563398500518441123079 281474976710656000 2168426451422061 529000000000000000000 685896 2000 0 1 933734440410950138382000 466867220205475069191 281474976710656000 2168426451422061 529000000000000000000 

noncomputable def Ns348p651 := nat_lit 634330319248986909842031463467319296 

noncomputable def Ns348p652 := nat_lit 56457600757788456322596864 

noncomputable def Ns348p653 := nat_lit 6979360642424738216090152104501589972354272003276230549495827262066205382156432115337523629810485804872050220452928137120111523994060226376624877247231970051955090928694515361382400 

noncomputable def Ns348p654 := nat_lit 197784206020568018619513993822485577225862109074284318918508872975079069950323168611790215611853649867020572003346360951297322613969981719532803409234017397129354200236489640509440 

noncomputable def Ns348p655 := nat_lit 10508407865517157036416738115708370577475566909635814151218500221517220170014944587078605610060420797921801664807699682061588296850619481537292788588854263353473572704092160 

noncomputable def Ns348p656 := BSN.log_dyadic_bound 833238291264 2930390291264 8 7 Ns348p653 134217728 42320000 Ns348p654 Ns348p655 78490971 3763628582528 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 833238291264) (BSN.artanhQ 2930390291264) 0 7 Ns348p654 Ns348p653 Ns348p655 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz435 := (Real.log (Enclosure.sfrac Bool.false 1881814291264 16000000))

noncomputable def Ns348p657 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 685896 4000) qz435 685896 4000 0 1 3286264880897271 281474976710656 781250529 33062500000000000 281754492093489323727 140737488355328000 66982076604873 16531250000000000000 (Enclosure.Real.IsNear.const Bool.false 685896 4000) (BSN.isNear_log_sfrac 1881814291264 16000000 3286264880897271 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1881814291264) qz356)) Bool.false Ns348p652 Ns348p99 1000000677120000 42320000000000000000000 3286264880897271 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 1881814291264 16000000 16 3763628582528 2097152000000 78490971 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns348p656 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p658 := BSN.arctan_dyadic_bound_f 1000 1371792 1 0 16777216 5290000 0 1 1 0 1 1 12230 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1371792) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1371792) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns348p659 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1371792))) 884279719003555 562949953421312 1 2000000000000000 12230 16777216 1 5290000 14828866972211604357120 883869348300195 562949953421312 200000000529 1058000000000000000 qz17 (Ns348p658 rfl) rfl rfl 

noncomputable abbrev qz436 := (@HMul.hMul Real Real Real qz583 qz588 qz642)

noncomputable abbrev qz105 := qz436

noncomputable abbrev qz437 := qz642

noncomputable abbrev qz106 := qz437

noncomputable def Ns348p660 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 685896 4000) qz435) qz105 281754492093489323727 140737488355328000 66982076604873 16531250000000000000 883869348300195 2251799813685248 200000000529 4232000000000000000 Ns348p651 563398500518441123079 281474976710656000 2168426451422061 529000000000000000000 (Ns348p657 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz106 1 4 0 1 883869348300195 562949953421312 200000000529 1058000000000000000 883869348300195 2251799813685248 200000000529 4232000000000000000 qz364 Ns348p659 rfl) 

noncomputable def Ns348p661 := @Ns348p647 Ns348p641 Ns348p642 2494355223255048357 270848000000000000000000 (@Ns348p649 2494355223255048357 270848000000000000000000 (Ns348p650 (Ns348p660 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 685896 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz643 (Real.log Real.pi) 685896 2000 0 1 38410761 33554432 1 67108864 3293223415857 8388608000 85737 16777216000 (Enclosure.Real.IsNear.const Bool.false 685896 2000) RS349to360.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns348p643 Ns348p644) 

noncomputable def Ns348p662 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz98) Bool.false Ns348p641 Ns348p642 2494355223255048357 270848000000000000000000 21241003909 16777216 155 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz98) (@HAdd.hAdd Real Real Real qz365 qz102 (Enclosure.sfrac Bool.true Ns348p643 Ns348p644)) Bool.false Ns348p641 Ns348p642 2494355223255048357 270848000000000000000000 Ns348p645 (Ns348p661 rfl rfl)) 

noncomputable def Ns348p663 := BSN.cos_dyadic_bound_f 44892506 68719476736 1 0 33554432 10590333 0 1 1 0 1 1 33554424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 44892506) qz594 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 44892506) qz595 0 0 rfl) rfl rfl 

noncomputable def Ns348p664 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz98) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21241003909) qz377) Bool.false 21241003909 16777216 155 16777216 Bool.true 33554424 33554432 1 5290000 (Ns348p662 rfl) (Enclosure.sfrac_false_div 21241003909 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21241003909) qz377) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1579514635988886355968) qz381) 226375608064910080 72057594037927936 Bool.false 33554424 33554432 201 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q2 21241003909 16777216 226375608064910080 72057594037927936 201 1579514635988886355968 Ns348p188 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33554424 33554432 1579514635988886355968 Ns348p188 44892506 68719476736 10590333 10580000 (Ns348p663 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p665 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz98) Bool.false Ns348p641 Ns348p642 2494355223255048357 270848000000000000000000 339856062547 268435456 2473 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz98) (@HAdd.hAdd Real Real Real qz365 qz102 (Enclosure.sfrac Bool.true Ns348p643 Ns348p644)) Bool.false Ns348p641 Ns348p642 2494355223255048357 270848000000000000000000 Ns348p645 (Ns348p661 rfl rfl)) 

noncomputable def Ns348p666 := Ns348p640 50668 BSN.abs_quadSignPos (BSN.cos_quad_nat3 503 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 134566875 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 326 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 241811894 268435456) qz101 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 1) Bool.true 4194303 4194304 52295451 5546967040000 268435392 268435456 2531 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz98)) Bool.true 4194303 4194304 52295451 5546967040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz98) qz98) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz98)) Bool.true 33554424 33554432 836727216 88751472640000 4194303 4194304 52295451 5546967040000 (Ns348p664 rfl rfl) rfl)) rfl) (Ns348p665 rfl) RS349to360.d7 

noncomputable def Ns348p667 := nat_lit 6198465250682889032882024345659738884232113240619774856313286378455040 

noncomputable def Ns348p668 := nat_lit 155834604089411443152966513598574112872478362135940692273119952896 

noncomputable def Ns348p669 := nat_lit 16233823352905707467592578007134442243472788760465475957794926892220416 

noncomputable def Ns348p670 := BSN.sin_dyadic_bound_f 140955812 268435456 3 2 268435456 134217728 Ns348p667 Ns348p162 Ns348p668 Ns348p669 Ns348p165 Ns348p668 134566875 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 140955812) qz370 0 2 Ns348p667 Ns348p162 Ns348p668 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 140955812) qz371 0 2 Ns348p669 Ns348p165 Ns348p668 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p671 := nat_lit 1843222063034176485371592037809256257636968848241459831728429646029056 

noncomputable def Ns348p672 := nat_lit 44647452979220979046685854271547273119924789392113998345815531776 

noncomputable def Ns348p673 := nat_lit 5529576894196571014156682741719225678364666695145595267188597307023616 

noncomputable def Ns348p674 := BSN.cos_dyadic_bound_f 120565926 268435456 3 2 268435456 134217728 Ns348p671 Ns348p121 Ns348p672 Ns348p673 Ns348p124 Ns348p672 241811894 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 120565926) qz368 0 2 Ns348p671 Ns348p121 Ns348p672 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 120565926) qz369 0 2 Ns348p673 Ns348p124 Ns348p672 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p675 := nat_lit 3392045073989976446225164322061718675807290658520897947838600758628627176070297242030060109099352047101874176 

noncomputable def Ns348p676 := nat_lit 249982692460569227624287206187222643130160155863192082413447496003773874088029075459842253820374224896 

noncomputable def Ns348p677 := nat_lit 20568505372875436220884284789305304728456198348722247158307215504839674286996337089729773030661628831663329280 

noncomputable def Ns348p678 := BSN.cos_dyadic_bound_f 281725286 268435456 4 3 268435456 134217728 Ns348p675 Ns348p146 Ns348p676 Ns348p677 Ns348p149 Ns348p676 133680145 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 281725286) qz368 0 3 Ns348p675 Ns348p146 Ns348p676 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 281725286) qz369 0 3 Ns348p677 Ns348p149 Ns348p676 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p679 := nat_lit 90616934567975597134293805671361 

noncomputable def Ns348p680 := BSN.sin_dyadic_bound_f 97566863 268435456 2 1 268435456 134217728 Ns348p679 Ns348p137 Ns348p679 Ns348p679 Ns348p138 Ns348p679 95432801 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 97566863) qz370 0 1 Ns348p679 Ns348p137 Ns348p679 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 97566863) qz371 0 1 Ns348p679 Ns348p138 Ns348p679 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p681 := Ns348p638 86173 BSN.abs_quadSignPos (BSN.cos_quad_nat0 200 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133680145 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 103 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 95432801 268435456) qz101 rfl rfl (Ns348p666 RS349to360.d9 RS349to360.d11 RS349to360.d13 RS349to360.d17 (Ns348p670 rfl rfl) (Ns348p674 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns348p665 rfl) RS349to360.d19 RS349to360.d21 RS349to360.d23 RS349to360.d25 RS349to360.d17 (Ns348p678 rfl rfl) (Ns348p680 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns348p682 := nat_lit 73260922268763045838081773749280199869213200416275857212184641793223585 

noncomputable def Ns348p683 := nat_lit 21757258229517902081165970639733878887454389580587305219163628563361 

noncomputable def Ns348p684 := nat_lit 191838618000103043448749424438507620996407265411877722775843035012197281 

noncomputable def Ns348p685 := BSN.sin_dyadic_bound_f 261336771 268435456 3 2 268435456 134217728 Ns348p682 Ns348p162 Ns348p683 Ns348p684 Ns348p165 Ns348p683 221966681 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 261336771) qz370 0 2 Ns348p682 Ns348p162 Ns348p683 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 261336771) qz371 0 2 Ns348p684 Ns348p165 Ns348p683 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p686 := nat_lit 113124707913964178132674840722525631965913898552822528578304369307869440 

noncomputable def Ns348p687 := nat_lit 51860184506909540639233287005323708143103649368209158991038780989696 

noncomputable def Ns348p688 := nat_lit 296195032809275946329303919427653750097542804586986664781002142541865216 

noncomputable def Ns348p689 := BSN.sin_dyadic_bound_f 291309238 268435456 3 2 268435456 134217728 Ns348p686 Ns348p162 Ns348p687 Ns348p688 Ns348p165 Ns348p687 237404890 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 291309238) qz370 0 2 Ns348p686 Ns348p162 Ns348p687 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 291309238) qz371 0 2 Ns348p688 Ns348p165 Ns348p687 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p690 := Ns348p636 116179 BSN.abs_quadSignPos (BSN.cos_quad_nat3 23 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 221966681 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 43 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 237404890 268435456) qz101 rfl rfl (Ns348p681 rfl rfl) (Ns348p665 rfl) RS349to360.d27 RS349to360.d29 RS349to360.d31 RS349to360.d33 RS349to360.d17 (Ns348p685 rfl rfl) (Ns348p689 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p691 := nat_lit 43965352387022644862346830065242309182657943217690109289170257657644985125308819378184381745342544178839556096 

noncomputable def Ns348p692 := nat_lit 30851519960371646539601746946832657443089665013704497971101450203698815989064633726198273092385819856896 

noncomputable def Ns348p693 := nat_lit 219555735367598937045150686918466599125003695068923865772396734393488591153327292423600240058002561968646393856 

noncomputable def Ns348p694 := BSN.sin_dyadic_bound_f 420829698 268435456 4 3 268435456 134217728 Ns348p691 Ns348p131 Ns348p692 Ns348p693 Ns348p134 Ns348p692 268434179 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 420829698) qz370 0 3 Ns348p691 Ns348p131 Ns348p692 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 420829698) qz371 0 3 Ns348p693 Ns348p134 Ns348p692 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p695 := nat_lit 16745755696926163609779222696747939458632567832589277919101236515488000 

noncomputable def Ns348p696 := nat_lit 1137281324991797527483471923451289232176471969185278298258081628416 

noncomputable def Ns348p697 := nat_lit 43856090274566156067710610013130444113852249083117046956591773027451136 

noncomputable def Ns348p698 := BSN.sin_dyadic_bound_f 180710542 268435456 3 2 268435456 134217728 Ns348p695 Ns348p162 Ns348p696 Ns348p697 Ns348p165 Ns348p696 167366937 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 180710542) qz370 0 2 Ns348p695 Ns348p162 Ns348p696 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 180710542) qz371 0 2 Ns348p697 Ns348p165 Ns348p696 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p699 := Ns348p634 142396 BSN.abs_quadSignNeg qz596 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268434179 268435456) BSN.abs_quadSignNeg qz597 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 167366937 268435456) qz101 rfl rfl (Ns348p690 rfl) (Ns348p665 rfl) RS349to360.d35 RS349to360.d37 RS349to360.d39 RS349to360.d41 RS349to360.d17 (Ns348p694 rfl rfl) (Ns348p698 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p700 := nat_lit 17734104746494127648401256368715844702747633287316911304466378352613825 

noncomputable def Ns348p701 := nat_lit 1275479441548801940003804051764777738067578679979415991552315349441 

noncomputable def Ns348p702 := nat_lit 46444399750293541018862331949600545533715501577490991504854191936756161 

noncomputable def Ns348p703 := BSN.sin_dyadic_bound_f 183319719 268435456 3 2 268435456 134217728 Ns348p700 Ns348p162 Ns348p701 Ns348p702 Ns348p165 Ns348p701 169398935 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 183319719) qz370 0 2 Ns348p700 Ns348p162 Ns348p701 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 183319719) qz371 0 2 Ns348p702 Ns348p165 Ns348p701 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p704 := Ns348p632 Bool.true 173720164 142396 Bool.true 183319719 14148475504056880 1 Bool.false 169398935 Bool.false Bool.true 120151518 154467 BSN.abs_quadSignPos qz372 (BSN.sfrac_eq_quadSignPos_mul Bool.false 169398935 268435456) qz101 rfl (Ns348p699 rfl) (Ns348p665 rfl) RS349to360.d43 RS349to360.d45 RS349to360.d17 (Ns348p703 rfl rfl) rfl 

noncomputable def Ns348p705 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 10) 120151518 268435456 154467 268435456 120151518 268435456 154467 268435456 64505855046844416 60075759 67108864 154467 134217728 (Ns348p704 rfl rfl rfl rfl) 

noncomputable def Ns348p706 := @Enclosure.Real.IsNear.mulLit_ff qz640 (Zeta.RiemannSiegel.correction qz100) 2595197 8388608 1 16777216 109043880704787 281474976710656 18232129671033 1163283302187008000 282990352073421108039 2361183241434822606848 

noncomputable abbrev qz644 := (@HPow.hPow Real Real Real qz7 qz99 qz9)

noncomputable def Ns348p707 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz644 1 1 0 1 2595197 8388608 1 16777216 2595197 8388608 1 16777216 

noncomputable def Ns348p708 := @Enclosure.Real.IsNear.sqrt_image qz99 457865845161 4194304000 85737 4194304000 175290761 175290795 16777216 (@Enclosure.Real.IsNear.of_eq qz99 (@HMul.hMul Real Real Real qz5 qz98 qz3) Bool.false 457865845161 4194304000 85737 4194304000 (BSN.t_div_two_pi_mk qz98 685896 1000 qz101) (@Enclosure.Real.IsNear.mulLit_ff qz98 qz3 685896 1000 0 1 5340353 33554432 1 33554432 457865845161 4194304000 85737 4194304000 (Enclosure.Real.IsNear.const Bool.false 685896 1000) RS349to360.d48 rfl)) 

noncomputable abbrev qz762 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 685896 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz645 := qz762

noncomputable abbrev qz438 := qz645

noncomputable abbrev qz107 := qz438

noncomputable def Ns348p709 := @Enclosure.Real.IsNear.sqrt_image qz107 87645389 8388608 17 16777216 54229982 54229988 16777216 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 350581556 33554432 34 33554432 87645389 8388608 17 16777216 (Ns348p708 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns348p710 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz107) 54229985 16777216 3 16777216 5190393 5190395 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz107) Bool.false 108459970 33554432 6 33554432 54229985 16777216 3 16777216 (Ns348p709 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns348p711 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 10380788 33554432 2 33554432 2595197 8388608 1 16777216 (Ns348p710 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz439 := (@HMul.hMul Real Real Real qz583 qz581 qz639)

noncomputable abbrev qz108 := (Real.cos qz439)

noncomputable abbrev qz646 := (@HMul.hMul Real Real Real qz738 qz761 qz761)

noncomputable abbrev qz440 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz646 qz639) qz602)

noncomputable abbrev qz109 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz440))

noncomputable def Ns348p712 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz100) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz108) qz109) Bool.false 109043880704787 

noncomputable def Ns348p713 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz108) qz109 35417783 33554432 247 

noncomputable abbrev qz110 := (@Neg.neg Real Real.instNeg (Real.cos qz439))

noncomputable def Ns348p714 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz108) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz110)) Bool.true 35417783 33554432 247 33554432 (BSN.inv_eq_neg_inv_neg qz108) 

noncomputable def Ns348p715 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz110) Bool.false 35417783 33554432 247 33554432 35417783 33554432 

noncomputable def Ns348p716 := @Enclosure.Real.IsNear.recentre' qz108 Bool.true 31789113 33554432 582807216 88751472640000 31789113 33554432 36425451 5546967040000 

noncomputable abbrev qz111 := qz439

noncomputable def Ns348p717 := @Enclosure.Real.IsNear.cos_image qz111 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23620435) qz636) Bool.false 23620435 8388608 107 16777216 Bool.true 31789113 33554432 1 

noncomputable def Ns348p718 := nat_lit 91752656403666641916021259 

noncomputable def Ns348p719 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz100 884279719003555 140737488355328 1 500000000000000 3759309 8388608 17 16777216 3324280706167535343495 1180591620717411303424 Ns348p718 

noncomputable def Ns348p720 := @Enclosure.Real.IsNear.subLit_ff_p qz107 qz1 87645389 8388608 17 16777216 10 1 0 1 3759309 3759309 8388608 17 

noncomputable def Ns348p721 := @Ns348p720 16777216 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 350581556 33554432 34 33554432 87645389 8388608 17 16777216 (Ns348p708 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns348p722 := @Enclosure.Real.IsNear.recentre' qz111 Bool.false 3324280706167535343495 1180591620717411303424 Ns348p718 Ns348p316 23620435 8388608 107 16777216 (@Ns348p719 Ns348p316 RS349to360.d47 (Ns348p721 rfl rfl) rfl) 

noncomputable def Ns348p723 := nat_lit 1505087195640359477575680 

noncomputable def Ns348p724 := nat_lit 3615875409525043556778723036268565844483551735778422746968313807371408133417421939510030305 

noncomputable def Ns348p725 := nat_lit 2870349725141718505871686025184038566512164807793142084567238273353495065508038503247841 

noncomputable def Ns348p726 := nat_lit 9465502649201075104458577603329279244539711041159442107256284443053972785987187303044820961 

noncomputable def Ns348p727 := BSN.sin_dyadic_bound_f 85554301883 68719476736 3 2 33554432 10590333 Ns348p724 Ns348p190 Ns348p725 Ns348p726 Ns348p193 Ns348p725 31789113 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 85554301883) qz379 0 2 Ns348p724 Ns348p190 Ns348p725 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 85554301883) qz380 0 2 Ns348p726 Ns348p193 Ns348p725 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p728 := @Ns348p717 5290000 (Ns348p722 rfl) (Enclosure.sfrac_false_div 23620435 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23620435) qz636) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns348p723) (@Nat.cast Real Real.instNatCast Ns348p605)) 226375608064910080 72057594037927936 Bool.false 31789113 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q1 23620435 8388608 226375608064910080 72057594037927936 0 Ns348p723 Ns348p605 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 31789113 33554432 Ns348p723 Ns348p605 85554301883 68719476736 10590333 10580000 (Ns348p727 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p729 := @Enclosure.Real.IsNear.inv_image qz110 31789113 33554432 36425451 5546967040000 17708768 17709015 16777216 (@Enclosure.Real.IsNear.neg qz108 Bool.true 31789113 33554432 36425451 5546967040000 (Ns348p716 (Ns348p728 rfl rfl) rfl)) 

noncomputable def Ns348p730 := Ns348p714 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz110) Bool.false 35417783 33554432 247 33554432 (@Ns348p715 247 33554432 (Ns348p729 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p731 := @Enclosure.Real.IsNear.recentre' qz109 Bool.true 6157578 16777216 

noncomputable abbrev qz112 := (@HMul.hMul Real Real Real qz349 qz346 qz440)

noncomputable def Ns348p732 := @Enclosure.Real.IsNear.cos_image qz112 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 65317057)) qz366) Bool.true 65317057 33554432 

noncomputable def Ns348p733 := nat_lit 19278192681784275753229034725 

noncomputable def Ns348p734 := nat_lit 9903520314283042199192993792 

noncomputable def Ns348p735 := nat_lit 14595310212804876829287549178052051 

noncomputable def Ns348p736 := @Enclosure.Real.IsNear.recentre' qz112 Bool.true Ns348p733 Ns348p734 Ns348p735 

noncomputable abbrev qz113 := qz440

noncomputable def Ns348p737 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz113 884279719003555 140737488355328 1 500000000000000 21801011905495 

noncomputable abbrev qz441 := (@HSub.hSub Real Real Real qz587 qz646 qz639)

noncomputable abbrev qz114 := qz441

noncomputable def Ns348p738 := @Enclosure.Real.IsNear.subLit_tf qz114 qz31 17402965394391 70368744177664 540845973 281474976710656 1 16 

noncomputable abbrev qz442 := qz646

noncomputable abbrev qz115 := qz442

noncomputable def Ns348p739 := @Enclosure.Real.IsNear.subLit_ff_n qz115 qz100 14132404157481 70368744177664 255633301 281474976710656 3759309 8388608 17 16777216 

noncomputable def Ns348p740 := @Enclosure.Real.IsNear.mulLit_ff qz100 qz100 3759309 8388608 17 16777216 3759309 8388608 17 16777216 14132404157481 70368744177664 

noncomputable def Ns348p741 := nat_lit 588751114558078740307789155682116183246457584899378177765142631447094876767812838640806687771265281 

noncomputable def Ns348p742 := nat_lit 6030027617906526637520164474641105770043877852825803783500922182229945005998159618379943840001 

noncomputable def Ns348p743 := nat_lit 3551547762033889487048029701446901504422462778879605782031448052033799545773723940049598897455433985 

noncomputable def Ns348p744 := BSN.cos_dyadic_bound_t 65317057 33554432 4 3 16777216 5290000 Ns348p741 Ns348p210 Ns348p742 Ns348p743 Ns348p213 Ns348p742 6157578 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 65317057) (BSN.cosEvenQ 33554432) 0 3 Ns348p741 Ns348p210 Ns348p742 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 65317057) (BSN.cosOddQ 33554432) 0 3 Ns348p743 Ns348p213 Ns348p742 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p745 := @Ns348p731 1090647216 88751472640000 3078789 8388608 68165451 5546967040000 (@Ns348p732 203 16777216 Bool.true 6157578 16777216 1 5290000 (@Ns348p736 Ns348p335 65317057 33554432 203 16777216 (@Ns348p737 70368744177664 540845973 281474976710656 Ns348p733 Ns348p734 Ns348p735 Ns348p335 RS349to360.d47 (@Ns348p738 0 1 348816190487920 21801011905495 70368744177664 540845973 281474976710656 (@Ns348p739 145986654731111497728 17402965394391 70368744177664 540845973 281474976710656 (@Ns348p740 255633301 281474976710656 (Ns348p721 rfl rfl) (Ns348p721 rfl rfl) rfl) (Ns348p721 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 65317057 33554432) (BSN.cos_neg_of_bound 65317057 33554432 Bool.true 6157578 16777216 1 5290000 (Ns348p744 rfl rfl)) rfl rfl) 

noncomputable def Ns348p746 := @Ns348p706 304264360310741057787 Ns348p629 (Ns348p707 qz33 (@Enclosure.Real.IsNear.of_eq qz644 (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 2595197 8388608 1 16777216 (BSN.rpow_neg_quarter_mk qz99 (BSN.t_div_two_pi_nonneg qz98 685896 1000 qz101)) Ns348p711) rfl) (@Ns348p712 281474976710656 18232129671033 1163283302187008000 (BSN.correction_mk qz100 (BSN.cos_two_pi_p_ne_zero_mk qz98 685896 1000 10 qz101 rfl rfl (@BSN.floor_sqrt_eq_dec qz98 685896 1000 10 qz101 rfl rfl rfl))) (@Ns348p713 33554432 3078789 8388608 68165451 5546967040000 109043880704787 281474976710656 18232129671033 1163283302187008000 Ns348p730 (Ns348p745 rfl) rfl)) 

noncomputable def Ns348p747 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz98) (hardyZApproximantRS₀ qz98) Bool.true 2396718210248418931527 2361183241434822606848 72179817095878966952187 Ns348p629 (@Eq.refl Real (hardyZApproximantRS₀ qz98)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz98) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 10) (@HMul.hMul Real Real Real qz5 qz640 (Zeta.RiemannSiegel.correction qz100))) Bool.true 2396718210248418931527 2361183241434822606848 72179817095878966952187 Ns348p629 (BSN.hardyZApproximantRS₀_eq qz98 10 (@BSN.floor_sqrt_eq_dec qz98 685896 1000 10 qz101 rfl rfl rfl)) (@Ns348p631 2396718210248418931527 2361183241434822606848 72179817095878966952187 Ns348p629 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 10)) Bool.true 60075759 67108864 154467 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz98) qz98 10) (Ns348p705 (Ns348p704 rfl rfl rfl rfl) rfl rfl)) (Ns348p746 rfl) rfl rfl)) 

theorem RS349to360.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz98) Bool.true 2396718210248418931527 2361183241434822606848 72179817095878966952187 Ns348p629 := Ns348p747 

noncomputable def Ns348p748 := nat_lit 780666209199388224389120000 

noncomputable def Ns348p749 := nat_lit 4735933036419368540220424192 

noncomputable abbrev qz763 := (Enclosure.sfrac Bool.false 687234 1000)

noncomputable abbrev qz647 := qz763

noncomputable abbrev qz443 := qz647

noncomputable abbrev qz116 := qz443

noncomputable abbrev qz764 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 687234 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz648 := qz764

noncomputable abbrev qz444 := qz648

noncomputable abbrev qz117 := qz444

noncomputable abbrev qz765 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 687234 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz649 := qz765

noncomputable abbrev qz445 := qz649

noncomputable abbrev qz118 := qz445

noncomputable abbrev qz650 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz117 qz9))

noncomputable def Ns348p750 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 10) (@HMul.hMul Real Real Real qz5 qz650 (Zeta.RiemannSiegel.correction qz118)) 264739837 67108864 154771 134217728 2200230700302334725 18446744073709551616 3747884162209354880547 Ns348p748 Ns348p749 

noncomputable def Ns348p751 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin BSN.quadSignPos 9 10 687234 1000 199 268435456 134217728 4503599627370496 Bool.false 340698994779 2478 618095470 52 84886744 8 

noncomputable def Ns348p752 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 687234 1000 101 153 268435456 134217728 4503599627370496 Bool.false 340698994779 2478 

noncomputable def Ns348p753 := Ns348p752 558195838 52 94906264 8 589812974 52 89478488 8 Bool.false 609454987 116408 Bool.true 324763498 Bool.true 126948070 14148475504056880 1 Bool.false 251137182 Bool.true Bool.false 122268677 Bool.true Bool.false 479908359 

noncomputable def Ns348p754 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 687234 1000 24 43 268435456 134217728 4503599627370496 Bool.false 340698994779 2478 

noncomputable def Ns348p755 := Ns348p754 480971758 52 109588312 8 522351262 52 101459064 8 Bool.false 448109031 86344 Bool.false 39071363 Bool.true 147282994 14148475504056880 1 Bool.false 265597011 Bool.false Bool.false 140003730 Bool.false Bool.false 609454987 

noncomputable def Ns348p756 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 687234 1000 201 103 268435456 134217728 4503599627370496 Bool.false 340698994779 2478 

noncomputable def Ns348p757 := Ns348p756 372130544 51 134217720 8 432030192 51 120047984 16 Bool.false 423825619 50770 Bool.false 205089422 Bool.false 362442698 14148475504056880 1 Bool.false 185711165 Bool.true Bool.false 261930747 Bool.false Bool.false 448109031 

noncomputable def Ns348p758 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 687234 1000 504 327 268435456 134217728 4503599627370496 Bool.false 340698994779 2478 

noncomputable def Ns348p759 := Ns348p758 186065264 51 189812528 16 294906480 51 154981288 8 Bool.false 268435368 2539 Bool.false 313275293 Bool.false 147255859 14148475504056880 1 Bool.false 105461337 Bool.false Bool.false 139980577 Bool.false Bool.false 423825619 

noncomputable def Ns348p760 := nat_lit 1176113680905911351814850725271935450238268864192918469 

noncomputable def Ns348p761 := nat_lit 926655543688365993410497232562293151804768124928000 

noncomputable def Ns348p762 := nat_lit 73580885040414761468202591083520000 

noncomputable def Ns348p763 := nat_lit 303403790647109197041371775160246702080 

noncomputable abbrev qz651 := (@Eq.refl Real qz763)

noncomputable abbrev qz446 := qz651

noncomputable abbrev qz119 := qz446

noncomputable def Ns348p764 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz116 687234 1000 1889163283024 16000000 1374468 4000 2000 Ns348p762 Ns348p763 qz119 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns348p765 := nat_lit 216781273664577580366513285682123142187917717048038732206080 

noncomputable abbrev qz652 := (@HSub.hSub Real Real Real qz742 qz743 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz744 (@Nat.cast Real Real.instNatCast 1374468))))

noncomputable abbrev qz447 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 687234 4000) (Real.log (Enclosure.sfrac Bool.false 1889163283024 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz652))

noncomputable abbrev qz653 := (Enclosure.sfrac Bool.false 687234 2000)

noncomputable abbrev qz120 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz447 qz653) (@HMul.hMul Real Real Real qz349 qz653 (Real.log Real.pi)))

noncomputable def Ns348p766 := @Enclosure.Real.IsNear.addLit_ft_p qz120 (Enclosure.sfrac Bool.true Ns348p762 Ns348p763) 714497714826091473801 562949953421312000 9996784300234523037 1083392000000000000000000 Ns348p762 Ns348p763 0 1 Ns348p765 

noncomputable def Ns348p767 := nat_lit 23974564986287478183435436032000 

noncomputable abbrev qz121 := (@HSub.hSub Real Real Real qz353 qz447 qz653)

noncomputable def Ns348p768 := @Enclosure.Real.IsNear.subLit_ff_p qz121 (@HMul.hMul Real Real Real qz5 qz653 (Real.log Real.pi)) 935933317911614630793 562949953421312000 2172607704253269 529000000000000000000 13198590462537 33554432000 343617 67108864000 Ns348p767 714497714826091473801 562949953421312000 

noncomputable def Ns348p769 := nat_lit 1871866635823229261586000 

noncomputable abbrev qz122 := qz447

noncomputable def Ns348p770 := @Enclosure.Real.IsNear.subLit_ff_p qz122 qz653 1129372492056385596297 562949953421312000 2172607704253269 529000000000000000000 687234 2000 0 1 Ns348p769 935933317911614630793 562949953421312000 2172607704253269 529000000000000000000 

noncomputable def Ns348p771 := nat_lit 2543120767193813312634132209552326656 

noncomputable def Ns348p772 := nat_lit 56476448682516972037996544 

noncomputable def Ns348p773 := nat_lit 7228440553129740794365492386243826861499988540421766987628983539696157449569932558209415719845592731458915102991309485244247558125359294819571679892906415535751437984031798879846400 

noncomputable def Ns348p774 := nat_lit 207566703458377108402289216293092360853067374116900355797185563199931591654192787700311429182869323440223826864485043216363959476762565657679944791989649516629923060089786036387840 

noncomputable def Ns348p775 := nat_lit 11883031867757319176520708637211213646791487386698023129089572116805788262132710917667691949673035111592307619478411208900252439085916229738391158915208954599163347871989760 

noncomputable def Ns348p776 := BSN.log_dyadic_bound 840587283024 2937739283024 8 7 Ns348p773 134217728 42320000 Ns348p774 Ns348p775 79014106 3778326566048 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 840587283024) (BSN.artanhQ 2937739283024) 0 7 Ns348p774 Ns348p773 Ns348p775 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz448 := (Real.log (Enclosure.sfrac Bool.false 1889163283024 16000000))

noncomputable def Ns348p777 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 687234 4000) qz448 687234 4000 0 1 3287361974508791 281474976710656 781250529 33062500000000000 1129593459594787237047 562949953421312000 268450963023393 66125000000000000000 (Enclosure.Real.IsNear.const Bool.false 687234 4000) (BSN.isNear_log_sfrac 1889163283024 16000000 3287361974508791 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1889163283024) qz356)) Bool.false Ns348p772 Ns348p99 1000000677120000 42320000000000000000000 3287361974508791 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 1889163283024 16000000 16 3778326566048 2097152000000 79014106 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns348p776 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p778 := BSN.arctan_dyadic_bound_f 1000 1374468 1 0 16777216 5290000 0 1 1 0 1 1 12206 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1374468) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1374468) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns348p779 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1374468))) 884279719003555 562949953421312 1 2000000000000000 12206 16777216 1 5290000 14828880483010486468608 883870153606563 562949953421312 200000000529 1058000000000000000 qz17 (Ns348p778 rfl) rfl rfl 

noncomputable abbrev qz449 := (@HMul.hMul Real Real Real qz583 qz588 qz652)

noncomputable abbrev qz123 := qz449

noncomputable abbrev qz450 := qz652

noncomputable abbrev qz124 := qz450

noncomputable def Ns348p780 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 687234 4000) qz448) qz123 1129593459594787237047 562949953421312000 268450963023393 66125000000000000000 883870153606563 2251799813685248 200000000529 4232000000000000000 Ns348p771 1129372492056385596297 562949953421312000 2172607704253269 529000000000000000000 (Ns348p777 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz124 1 4 0 1 883870153606563 562949953421312 200000000529 1058000000000000000 883870153606563 2251799813685248 200000000529 4232000000000000000 qz364 Ns348p779 rfl) 

noncomputable def Ns348p781 := @Ns348p766 Ns348p760 Ns348p761 9996784300234523037 1083392000000000000000000 (@Ns348p768 9996784300234523037 1083392000000000000000000 (Ns348p770 (Ns348p780 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 687234 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz653 (Real.log Real.pi) 687234 2000 0 1 38410761 33554432 1 67108864 13198590462537 33554432000 343617 67108864000 (Enclosure.Real.IsNear.const Bool.false 687234 2000) RS349to360.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns348p762 Ns348p763) 

noncomputable def Ns348p782 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns348p760 Ns348p761 9996784300234523037 1083392000000000000000000 42587374347 33554432 311 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz365 qz120 (Enclosure.sfrac Bool.true Ns348p762 Ns348p763)) Bool.false Ns348p760 Ns348p761 9996784300234523037 1083392000000000000000000 Ns348p764 (Ns348p781 rfl rfl)) 

noncomputable def Ns348p783 := nat_lit 7592171225734422844145664 

noncomputable def Ns348p784 := nat_lit 3503923811190165908056581370973671816955293984632694962188044482964613607677550063351810317836872934814778179649271098063987908634513288721 

noncomputable def Ns348p785 := nat_lit 69061887427279807374175457422696049589758900585025510522285359577850094671315332446731519433112496475662717985575392155893264493730122956800 

noncomputable def Ns348p786 := nat_lit 2487908037650957960404474334187074461283730564125555290673758819291088995782112457292142701641851537349858302085828794570220801928721 

noncomputable def Ns348p787 := nat_lit 17497891473821238393025103520552028655665137945087215753399689907189736734537353197429220272862444243755129810941668733043418095962496740881 

noncomputable def Ns348p788 := nat_lit 2417166059954793258096141009794361735641561520475892868279987585224753313496036635635603180158937376648195129495138725456264257280554303488000 

noncomputable def Ns348p789 := BSN.sin_dyadic_bound_f 107891242261 68719476736 4 3 33554432 10590333 Ns348p784 Ns348p785 Ns348p786 Ns348p787 Ns348p788 Ns348p786 33554421 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107891242261) qz379 0 3 Ns348p784 Ns348p785 Ns348p786 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107891242261) qz380 0 3 Ns348p787 Ns348p788 Ns348p786 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p790 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz116) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 42587374347) qz366) Bool.false 42587374347 33554432 311 33554432 Bool.false 33554421 33554432 1 5290000 (Ns348p782 rfl) (Enclosure.sfrac_false_div 42587374347 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 42587374347) qz366) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns348p783) qz367) 226375608064910080 72057594037927936 Bool.false 33554421 33554432 201 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q3 42587374347 33554432 226375608064910080 72057594037927936 201 Ns348p783 Ns348p99 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554421 33554432 Ns348p783 Ns348p99 107891242261 68719476736 10590333 10580000 (Ns348p789 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p791 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns348p760 Ns348p761 9996784300234523037 1083392000000000000000000 340698994779 268435456 2478 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz365 qz120 (Enclosure.sfrac Bool.true Ns348p762 Ns348p763)) Bool.false Ns348p760 Ns348p761 9996784300234523037 1083392000000000000000000 Ns348p764 (Ns348p781 rfl rfl)) 

noncomputable def Ns348p792 := Ns348p759 50770 BSN.abs_quadSignPos (BSN.cos_quad_nat0 504 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 105461337 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 327 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 139980577 268435456) qz119 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) Bool.false 33554421 33554432 104921527 11093934080000 268435368 268435456 2539 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 33554421 33554432 104921527 11093934080000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz116) qz116) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 33554421 33554432 1678744432 177502945280000 33554421 33554432 104921527 11093934080000 (Ns348p790 rfl rfl) rfl)) rfl) (Ns348p791 rfl) RS349to360.d7 

noncomputable def Ns348p793 := nat_lit 5188342952558598155986285618520412948651338987768738476131872895953833659744486556735553983139724022415015281 

noncomputable def Ns348p794 := nat_lit 893539463673426706360485445697136926645673971042396175033423452392824800201850044575948010420464172401 

noncomputable def Ns348p795 := nat_lit 31452798421564832872988537544890480735781565866100880738825131977170334597572196409807370149001055067218820465 

noncomputable def Ns348p796 := BSN.cos_dyadic_bound_f 313275293 268435456 4 3 268435456 134217728 Ns348p793 Ns348p146 Ns348p794 Ns348p795 Ns348p149 Ns348p794 105461337 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 313275293) qz368 0 3 Ns348p793 Ns348p146 Ns348p794 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 313275293) qz369 0 3 Ns348p795 Ns348p149 Ns348p794 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p797 := nat_lit 7383200128637543723434605653863556930436592665543136379072974751544865 

noncomputable def Ns348p798 := nat_lit 221095889111836506152666092359138569235658425009466522427373925921 

noncomputable def Ns348p799 := nat_lit 19336594753087385826080672395969305736317075438972484713678622886737441 

noncomputable def Ns348p800 := BSN.sin_dyadic_bound_f 147255859 268435456 3 2 268435456 134217728 Ns348p797 Ns348p162 Ns348p798 Ns348p799 Ns348p165 Ns348p798 139980577 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 147255859) qz370 0 2 Ns348p797 Ns348p162 Ns348p798 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 147255859) qz371 0 2 Ns348p799 Ns348p165 Ns348p798 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p801 := nat_lit 27781985321918202412669751405716699510962475463610663364791937212924160 

noncomputable def Ns348p802 := nat_lit 3130012622718394329492143867427652332526709181069643130432621691136 

noncomputable def Ns348p803 := nat_lit 72757274870301367013792075924901234901125249637449053199862944646349056 

noncomputable def Ns348p804 := BSN.sin_dyadic_bound_f 205089422 268435456 3 2 268435456 134217728 Ns348p801 Ns348p162 Ns348p802 Ns348p803 Ns348p165 Ns348p802 185711165 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 205089422) qz370 0 2 Ns348p801 Ns348p162 Ns348p802 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 205089422) qz371 0 2 Ns348p803 Ns348p165 Ns348p802 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p805 := nat_lit 24168664754722944896686030660486960315829752001724826697055981794425520170943458938812731920671873875451908096 

noncomputable def Ns348p806 := nat_lit 5138924714053124719233130987932515377810189066492403908624874286552295607686573195173000993017359568896 

noncomputable def Ns348p807 := nat_lit 120761291130373975583314540185279745510372746852520835389400440727813029365359870274380912043974547060443385856 

noncomputable def Ns348p808 := BSN.sin_dyadic_bound_f 362442698 268435456 4 3 268435456 134217728 Ns348p805 Ns348p131 Ns348p806 Ns348p807 Ns348p134 Ns348p806 261930747 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 362442698) qz370 0 3 Ns348p805 Ns348p131 Ns348p806 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 362442698) qz371 0 3 Ns348p807 Ns348p134 Ns348p806 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p809 := Ns348p757 86344 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 201 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 185711165 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 103 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 261930747 268435456) qz119 rfl rfl (Ns348p792 RS349to360.d9 RS349to360.d11 RS349to360.d13 RS349to360.d17 (Ns348p796 rfl rfl) (Ns348p800 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns348p791 rfl) RS349to360.d19 RS349to360.d21 RS349to360.d23 RS349to360.d25 RS349to360.d17 (Ns348p804 rfl rfl) (Ns348p808 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns348p810 := nat_lit 2330420259686142387005798817361 

noncomputable def Ns348p811 := BSN.cos_dyadic_bound_f 39071363 268435456 2 1 268435456 134217728 Ns348p810 Ns348p567 Ns348p810 Ns348p810 Ns348p568 Ns348p810 265597011 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 39071363) qz368 0 1 Ns348p810 Ns348p567 Ns348p810 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 39071363) qz369 0 1 Ns348p810 Ns348p568 Ns348p810 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p812 := nat_lit 7388643837984019836058835945640398474171198701679389419898335530041600 

noncomputable def Ns348p813 := nat_lit 221422032071349035565117540927805757450431571629807743932242575616 

noncomputable def Ns348p814 := nat_lit 19350851559049079291239369667325255746841076853282428791957845614510336 

noncomputable def Ns348p815 := BSN.sin_dyadic_bound_f 147282994 268435456 3 2 268435456 134217728 Ns348p812 Ns348p162 Ns348p813 Ns348p814 Ns348p165 Ns348p813 140003730 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 147282994) qz370 0 2 Ns348p812 Ns348p162 Ns348p813 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 147282994) qz371 0 2 Ns348p814 Ns348p165 Ns348p813 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p816 := Ns348p755 116408 BSN.abs_quadSignPos (BSN.cos_quad_nat0 24 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 265597011 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 43 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 140003730 268435456) qz119 rfl rfl (Ns348p809 rfl rfl) (Ns348p791 rfl) RS349to360.d27 RS349to360.d29 RS349to360.d31 RS349to360.d33 RS349to360.d17 (Ns348p811 rfl rfl) (Ns348p815 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p817 := nat_lit 15573798791968861307933360506210013361163611317032080555783260023464122122873580823310594110802089274299191296 

noncomputable def Ns348p818 := nat_lit 1376596072293714453507593144597448438431434925002181973228189267969407753230935337119666485103796228096 

noncomputable def Ns348p819 := nat_lit 77834908364964736934870998500400576643433072771719570447749661136449448159870830564556384035879554559310893056 

noncomputable def Ns348p820 := BSN.sin_dyadic_bound_f 324763498 268435456 4 3 268435456 134217728 Ns348p817 Ns348p131 Ns348p818 Ns348p819 Ns348p134 Ns348p818 251137182 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 324763498) qz370 0 3 Ns348p817 Ns348p131 Ns348p818 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 324763498) qz371 0 3 Ns348p819 Ns348p134 Ns348p818 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p821 := nat_lit 4078053278769449387549668590778471274924241435926707963626820923040000 

noncomputable def Ns348p822 := nat_lit 67454172857926635098099064254149746207942214378963005600100000000 

noncomputable def Ns348p823 := nat_lit 10680506518592502229030401767839584715688676616222859678918321303200000 

noncomputable def Ns348p824 := BSN.sin_dyadic_bound_f 126948070 268435456 3 2 268435456 134217728 Ns348p821 Ns348p162 Ns348p822 Ns348p823 Ns348p165 Ns348p822 122268677 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 126948070) qz370 0 2 Ns348p821 Ns348p162 Ns348p822 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 126948070) qz371 0 2 Ns348p823 Ns348p165 Ns348p822 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p825 := Ns348p753 142676 BSN.abs_quadSignNeg qz596 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 251137182 268435456) BSN.abs_quadSignNeg qz597 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 122268677 268435456) qz119 rfl rfl (Ns348p816 rfl) (Ns348p791 rfl) RS349to360.d35 RS349to360.d37 RS349to360.d39 RS349to360.d41 RS349to360.d17 (Ns348p820 rfl rfl) (Ns348p824 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p826 := nat_lit 12330389416066728806871331498524947484699702999691659090813021487890625 

noncomputable def Ns348p827 := nat_lit 616634109379395115183752655302385991616887275464018164215087890625 

noncomputable def Ns348p828 := nat_lit 32292878682092913568762237372790087168322318610270260637006327087890625 

noncomputable def Ns348p829 := BSN.sin_dyadic_bound_f 167399225 268435456 3 2 268435456 134217728 Ns348p826 Ns348p162 Ns348p827 Ns348p828 Ns348p165 Ns348p827 156758265 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 167399225) qz370 0 2 Ns348p826 Ns348p162 Ns348p827 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 167399225) qz371 0 2 Ns348p828 Ns348p165 Ns348p827 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p830 := Ns348p751 Bool.false 479908359 142676 Bool.true 167399225 14148475504056880 1 Bool.false 156758265 Bool.false Bool.false 529479674 154771 BSN.abs_quadSignPos qz372 (BSN.sfrac_eq_quadSignPos_mul Bool.false 156758265 268435456) qz119 rfl (Ns348p825 rfl) (Ns348p791 rfl) RS349to360.d43 RS349to360.d45 RS349to360.d17 (Ns348p829 rfl rfl) rfl 

noncomputable def Ns348p831 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 10) 529479674 268435456 154771 268435456 529479674 268435456 154771 268435456 284262235465842688 264739837 67108864 154771 134217728 (Ns348p830 rfl rfl rfl rfl) 

noncomputable def Ns348p832 := @Enclosure.Real.IsNear.mulLit_ff qz650 (Zeta.RiemannSiegel.correction qz118) 10375731 33554432 1 33554432 212055487975 549755813888 1441405762584559 93062664174960640000 2200230700302334725 18446744073709551616 

noncomputable abbrev qz654 := (@HPow.hPow Real Real Real qz7 qz117 qz9)

noncomputable def Ns348p833 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz654 1 1 0 1 10375731 33554432 1 33554432 10375731 33554432 1 33554432 

noncomputable def Ns348p834 := @Enclosure.Real.IsNear.sqrt_image qz117 1835036076801 16777216000 343617 16777216000 175461650 175461684 16777216 (@Enclosure.Real.IsNear.of_eq qz117 (@HMul.hMul Real Real Real qz5 qz116 qz3) Bool.false 1835036076801 16777216000 343617 16777216000 (BSN.t_div_two_pi_mk qz116 687234 1000 qz119) (@Enclosure.Real.IsNear.mulLit_ff qz116 qz3 687234 1000 0 1 5340353 33554432 1 33554432 1835036076801 16777216000 343617 16777216000 (Enclosure.Real.IsNear.const Bool.false 687234 1000) RS349to360.d48 rfl)) 

noncomputable abbrev qz766 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 687234 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz655 := qz766

noncomputable abbrev qz451 := qz655

noncomputable abbrev qz125 := qz451

noncomputable def Ns348p835 := @Enclosure.Real.IsNear.sqrt_image qz125 175461667 16777216 17 16777216 54256409 54256416 16777216 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 350923334 33554432 34 33554432 175461667 16777216 17 16777216 (Ns348p834 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns348p836 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz125) 108512825 33554432 7 33554432 5187865 5187866 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz125) Bool.false 108512825 33554432 7 33554432 108512825 33554432 7 33554432 (Ns348p835 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns348p837 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 10375731 33554432 1 33554432 10375731 33554432 1 33554432 (Ns348p836 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz452 := (@HMul.hMul Real Real Real qz583 qz581 qz649)

noncomputable abbrev qz126 := (Real.cos qz452)

noncomputable abbrev qz656 := (@HMul.hMul Real Real Real qz738 qz765 qz765)

noncomputable abbrev qz453 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz656 qz649) qz602)

noncomputable abbrev qz127 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz453))

noncomputable def Ns348p838 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz118) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz126) qz127) Bool.false 212055487975 

noncomputable def Ns348p839 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz126) qz127 4342285 4194304 119 

noncomputable abbrev qz128 := (@Neg.neg Real Real.instNeg (Real.cos qz452))

noncomputable def Ns348p840 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz126) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz128)) Bool.true 4342285 4194304 119 16777216 (BSN.inv_eq_neg_inv_neg qz126) 

noncomputable def Ns348p841 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz128) Bool.false 34738280 33554432 238 33554432 4342285 4194304 

noncomputable def Ns348p842 := @Enclosure.Real.IsNear.recentre' qz126 Bool.true 32410928 33554432 1170904432 177502945280000 2025683 2097152 73181527 11093934080000 

noncomputable abbrev qz129 := qz452

noncomputable def Ns348p843 := @Enclosure.Real.IsNear.cos_image qz129 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 48314597) qz377) Bool.false 48314597 16777216 215 33554432 Bool.true 32410928 33554432 1 

noncomputable def Ns348p844 := nat_lit 458763282019801134912598583 

noncomputable def Ns348p845 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz118 884279719003555 140737488355328 1 500000000000000 7689507 16777216 17 16777216 6799675089235869197385 2361183241434822606848 Ns348p844 

noncomputable def Ns348p846 := @Enclosure.Real.IsNear.subLit_ff_p qz125 qz1 175461667 16777216 17 16777216 10 1 0 1 7689507 7689507 16777216 17 

noncomputable def Ns348p847 := @Ns348p846 16777216 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 350923334 33554432 34 33554432 175461667 16777216 17 16777216 (Ns348p834 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns348p848 := @Enclosure.Real.IsNear.recentre' qz129 Bool.false 6799675089235869197385 2361183241434822606848 Ns348p844 Ns348p477 48314597 16777216 215 33554432 (@Ns348p845 Ns348p477 RS349to360.d47 (Ns348p847 rfl rfl) rfl) 

noncomputable def Ns348p849 := nat_lit 3164914759827843453026304 

noncomputable def Ns348p850 := nat_lit 4419482715763016097087898873658036634581131474233043786816011812341773057519359461800390625 

noncomputable def Ns348p851 := nat_lit 4286449413001645687906236906593888838980296017930721823200484513730175512817535400390625 

noncomputable def Ns348p852 := nat_lit 11567895718424944256497410761731801080068423858009893511090087295491937723625189247400390625 

noncomputable def Ns348p853 := BSN.sin_dyadic_bound_f 89952287675 68719476736 3 2 33554432 10590333 Ns348p850 Ns348p190 Ns348p851 Ns348p852 Ns348p193 Ns348p851 32410928 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 89952287675) qz379 0 2 Ns348p850 Ns348p190 Ns348p851 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 89952287675) qz380 0 2 Ns348p852 Ns348p193 Ns348p851 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p854 := @Ns348p843 5290000 (Ns348p848 rfl) (Enclosure.sfrac_false_div 48314597 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 48314597) qz377) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns348p849) qz381) 226375608064910080 72057594037927936 Bool.false 32410928 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q1 48314597 16777216 226375608064910080 72057594037927936 0 Ns348p849 Ns348p188 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 32410928 33554432 Ns348p849 Ns348p188 89952287675 68719476736 10590333 10580000 (Ns348p853 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p855 := @Enclosure.Real.IsNear.inv_image qz128 2025683 2097152 73181527 11093934080000 17369021 17369259 16777216 (@Enclosure.Real.IsNear.neg qz126 Bool.true 2025683 2097152 73181527 11093934080000 (Ns348p842 (Ns348p854 rfl rfl) rfl)) 

noncomputable def Ns348p856 := Ns348p840 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz128) Bool.false 4342285 4194304 119 16777216 (@Ns348p841 119 16777216 (Ns348p855 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p857 := @Enclosure.Real.IsNear.recentre' qz127 Bool.true 6250880 16777216 

noncomputable abbrev qz130 := (@HMul.hMul Real Real Real qz349 qz346 qz453)

noncomputable def Ns348p858 := @Enclosure.Real.IsNear.cos_image qz130 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32758949)) qz377) Bool.true 32758949 16777216 

noncomputable def Ns348p859 := nat_lit 77349881837539053848390339845 

noncomputable def Ns348p860 := nat_lit 14752105409786768485764239401178801 

noncomputable def Ns348p861 := @Enclosure.Real.IsNear.recentre' qz130 Bool.true Ns348p859 Ns348p493 Ns348p860 

noncomputable abbrev qz131 := qz453

noncomputable def Ns348p862 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz131 884279719003555 140737488355328 1 500000000000000 87472188013879 

noncomputable abbrev qz454 := (@HSub.hSub Real Real Real qz587 qz656 qz649)

noncomputable abbrev qz132 := qz454

noncomputable def Ns348p863 := @Enclosure.Real.IsNear.subLit_tf qz132 qz31 69880001969463 281474976710656 546656199 281474976710656 1 16 

noncomputable abbrev qz455 := qz656

noncomputable abbrev qz133 := qz455

noncomputable def Ns348p864 := @Enclosure.Real.IsNear.subLit_ff_n qz133 qz118 59128517903049 281474976710656 261443527 281474976710656 7689507 16777216 17 16777216 

noncomputable def Ns348p865 := @Enclosure.Real.IsNear.mulLit_ff qz118 qz118 7689507 16777216 17 16777216 7689507 16777216 17 16777216 59128517903049 281474976710656 

noncomputable def Ns348p866 := nat_lit 145529409043165642633326250354360564942522339103201756648320834110148258861369040562390236617681 

noncomputable def Ns348p867 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600 

noncomputable def Ns348p868 := nat_lit 1527423678843917243810380041805152625623398415722983677772388193120851126095266259514907601 

noncomputable def Ns348p869 := nat_lit 877821801388016640060849013546524945767077015900240842943091155739348125828557327118454626409425 

noncomputable def Ns348p870 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600 

noncomputable def Ns348p871 := BSN.cos_dyadic_bound_t 32758949 16777216 4 3 16777216 5290000 Ns348p866 Ns348p867 Ns348p868 Ns348p869 Ns348p870 Ns348p868 6250880 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 32758949) (BSN.cosEvenQ 16777216) 0 3 Ns348p866 Ns348p867 Ns348p868 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 32758949) (BSN.cosOddQ 16777216) 0 3 Ns348p869 Ns348p870 Ns348p868 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p872 := @Ns348p857 1101227216 88751472640000 48835 131072 68826701 5546967040000 (@Ns348p858 205 16777216 Bool.true 6250880 16777216 1 5290000 (@Ns348p861 Ns348p335 32758949 16777216 205 16777216 (@Ns348p862 281474976710656 546656199 281474976710656 Ns348p859 Ns348p493 Ns348p860 Ns348p335 RS349to360.d47 (@Ns348p863 0 1 1399555008222064 87472188013879 281474976710656 546656199 281474976710656 (@Ns348p864 1172391887122106155008 69880001969463 281474976710656 546656199 281474976710656 (@Ns348p865 261443527 281474976710656 (Ns348p847 rfl rfl) (Ns348p847 rfl rfl) rfl) (Ns348p847 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 32758949 16777216) (BSN.cos_neg_of_bound 32758949 16777216 Bool.true 6250880 16777216 1 5290000 (Ns348p871 rfl rfl)) rfl rfl) 

noncomputable def Ns348p873 := @Ns348p832 3747884162209354880547 Ns348p748 (Ns348p833 qz33 (@Enclosure.Real.IsNear.of_eq qz654 (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 10375731 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz117 (BSN.t_div_two_pi_nonneg qz116 687234 1000 qz119)) Ns348p837) rfl) (@Ns348p838 549755813888 1441405762584559 93062664174960640000 (BSN.correction_mk qz118 (BSN.cos_two_pi_p_ne_zero_mk qz116 687234 1000 10 qz119 rfl rfl (@BSN.floor_sqrt_eq_dec qz116 687234 1000 10 qz119 rfl rfl rfl))) (@Ns348p839 16777216 48835 131072 68826701 5546967040000 212055487975 549755813888 1441405762584559 93062664174960640000 Ns348p856 (Ns348p872 rfl) rfl)) 

noncomputable def Ns348p874 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (hardyZApproximantRS₀ qz116) Bool.false 70570901578953393403 18446744073709551616 903960483976136430720547 Ns348p748 (@Eq.refl Real (hardyZApproximantRS₀ qz116)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 10) (@HMul.hMul Real Real Real qz5 qz650 (Zeta.RiemannSiegel.correction qz118))) Bool.false 70570901578953393403 18446744073709551616 903960483976136430720547 Ns348p748 (BSN.hardyZApproximantRS₀_eq qz116 10 (@BSN.floor_sqrt_eq_dec qz116 687234 1000 10 qz119 rfl rfl rfl)) (@Ns348p750 70570901578953393403 18446744073709551616 903960483976136430720547 Ns348p748 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 10)) Bool.false 264739837 67108864 154771 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz116) qz116 10) (Ns348p831 (Ns348p830 rfl rfl rfl rfl) rfl rfl)) (Ns348p873 rfl) rfl rfl)) 

theorem RS349to360.d56 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz116) Bool.false 70570901578953393403 18446744073709551616 903960483976136430720547 Ns348p748 := Ns348p874 

noncomputable def Ns348p875 := nat_lit 4996263738876084636090368 

noncomputable def Ns348p876 := nat_lit 3380379642817643685618162597888 

noncomputable abbrev qz767 := (Enclosure.sfrac Bool.false 688572 1000)

noncomputable abbrev qz657 := qz767

noncomputable abbrev qz456 := qz657

noncomputable abbrev qz134 := qz456

noncomputable abbrev qz768 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 688572 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz658 := qz768

noncomputable abbrev qz457 := qz658

noncomputable abbrev qz135 := qz457

noncomputable abbrev qz769 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 688572 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz659 := qz769

noncomputable abbrev qz458 := qz659

noncomputable abbrev qz136 := qz458

noncomputable abbrev qz660 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz135 qz9))

noncomputable def Ns348p877 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 10) (@HMul.hMul Real Real Real qz5 qz660 (Zeta.RiemannSiegel.correction qz136)) 341964809 134217728 155069 134217728 1122156814728704771545 9444732965739290427392 23823390749291617559 Ns348p875 Ns348p876 

noncomputable def Ns348p878 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin BSN.quadSignPos 9 10 688572 1000 199 268435456 134217728 4503599627370496 Bool.false 341542276827 2483 618095470 52 84886744 8 

noncomputable def Ns348p879 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 688572 1000 101 153 268435456 134217728 4503599627370496 Bool.false 341542276827 2483 

noncomputable def Ns348p880 := Ns348p879 558195838 52 94906264 8 589812974 52 89478488 8 Bool.true 291946605 116631 Bool.true 228347481 Bool.true 72835781 14148475504056880 1 Bool.false 201787297 Bool.true Bool.false 71945341 Bool.true Bool.true 387270968 

noncomputable def Ns348p881 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 688572 1000 24 43 268435456 134217728 4503599627370496 Bool.false 341542276827 2483 

noncomputable def Ns348p882 := Ns348p881 480971758 52 109588312 8 522351262 52 101459064 8 Bool.true 362051432 86508 Bool.false 238813199 Bool.true 2906935 14148475504056880 1 Bool.false 169029815 Bool.false Bool.false 2906878 Bool.false Bool.true 291946605 

noncomputable def Ns348p883 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 688572 1000 202 104 268435456 134217728 4503599627370496 Bool.false 341542276827 2483 

noncomputable def Ns348p884 := Ns348p883 372130544 51 134217720 8 432030192 51 120047984 16 Bool.true 329386969 50864 Bool.false 128803374 Bool.false 206010921 14148475504056880 1 Bool.false 238121960 Bool.true Bool.false 193188472 Bool.false Bool.true 362051432 

noncomputable def Ns348p885 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 688572 1000 506 328 268435456 134217728 4503599627370496 Bool.false 341542276827 2483 

noncomputable def Ns348p886 := Ns348p885 186065264 51 189812528 16 294906480 51 154981288 8 Bool.true 268435344 2539 Bool.false 64287161 Bool.false 174295609 14148475504056880 1 Bool.false 260774166 Bool.true Bool.false 213810499 Bool.false Bool.true 329386969 

noncomputable def Ns348p887 := nat_lit 582453542077152433192644279753487594415376111657453 

noncomputable def Ns348p888 := nat_lit 457779879019405304349960347727898052273373184000 

noncomputable def Ns348p889 := nat_lit 74299965254727008896154206863360000 

noncomputable def Ns348p890 := nat_lit 306965329585570673581186170097521131520 

noncomputable abbrev qz661 := (@Eq.refl Real qz767)

noncomputable abbrev qz459 := qz661

noncomputable abbrev qz137 := qz459

noncomputable def Ns348p891 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz134 688572 1000 1896526596736 16000000 1377144 4000 2000 Ns348p889 Ns348p890 qz137 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns348p892 := nat_lit 54967212480338297080866915145811370702152767949159289323520 

noncomputable abbrev qz662 := (@HSub.hSub Real Real Real qz742 qz743 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz744 (@Nat.cast Real Real.instNatCast 1377144))))

noncomputable abbrev qz460 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 688572 4000) (Real.log (Enclosure.sfrac Bool.false 1896526596736 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz662))

noncomputable abbrev qz663 := (Enclosure.sfrac Bool.false 688572 2000)

noncomputable abbrev qz138 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz460 qz663) (@HMul.hMul Real Real Real qz349 qz663 (Real.log Real.pi)))

noncomputable def Ns348p893 := @Enclosure.Real.IsNear.addLit_ft_p qz138 (Enclosure.sfrac Bool.true Ns348p889 Ns348p890) 179066551298608289601 140737488355328000 5008073853724426323 541696000000000000000000 Ns348p889 Ns348p890 0 1 Ns348p892 

noncomputable def Ns348p894 := nat_lit 600847641902366354805306163200 

noncomputable abbrev qz139 := (@HSub.hSub Real Real Real qz353 qz460 qz663)

noncomputable def Ns348p895 := @Enclosure.Real.IsNear.subLit_ff_p qz139 (@HMul.hMul Real Real Real qz5 qz663 (Real.log Real.pi)) 46906646451455830797 28147497671065600 2176788957084477 529000000000000000000 6612143630823 16777216000 172143 33554432000 Ns348p894 179066551298608289601 140737488355328000 

noncomputable abbrev qz140 := qz460

noncomputable def Ns348p896 := @Enclosure.Real.IsNear.subLit_ff_p qz140 qz663 282987179173181609793 140737488355328000 2176788957084477 529000000000000000000 688572 2000 0 1 469066464514558307970000 46906646451455830797 28147497671065600 2176788957084477 529000000000000000000 

noncomputable def Ns348p897 := nat_lit 1274460954674968484201961440912867328 

noncomputable def Ns348p898 := nat_lit 56495259965958919467040768 

noncomputable def Ns348p899 := nat_lit 7486263443101742491843572154304802354088008450999604451685031727788555334143814194937337942949955157719175383379602696952238050321162500608261200928103129913527283994345972590182400 

noncomputable def Ns348p900 := nat_lit 217804049702288986537980140701933072276779346046036675940366286204543990167015914839361531861096767227852302274733144385342052335649805561167863264539473003825286719259113097789440 

noncomputable def Ns348p901 := nat_lit 13426275301714668370141783488505265428555573017544640416224781843184880516335880909662025062364377980864933989812338378470611370927693446111254421643528387827007739826012160 

noncomputable def Ns348p902 := BSN.log_dyadic_bound 847950596736 2945102596736 8 7 Ns348p899 134217728 42320000 Ns348p900 Ns348p901 79536224 3793053193472 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 847950596736) (BSN.artanhQ 2945102596736) 0 7 Ns348p900 Ns348p899 Ns348p901 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz461 := (Real.log (Enclosure.sfrac Bool.false 1896526596736 16000000))

noncomputable def Ns348p903 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 688572 4000) qz461 688572 4000 0 1 3288456935316727 281474976710656 781250529 33062500000000000 566084842216227335961 281474976710656000 134486809813647 33062500000000000000 (Enclosure.Real.IsNear.const Bool.false 688572 4000) (BSN.isNear_log_sfrac 1896526596736 16000000 3288456935316727 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1896526596736) qz356)) Bool.false Ns348p898 Ns348p99 1000000677120000 42320000000000000000000 3288456935316727 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 1896526596736 16000000 16 3793053193472 2097152000000 79536224 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns348p902 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p904 := BSN.arctan_dyadic_bound_f 1000 1377144 1 0 16777216 5290000 0 1 1 0 1 1 12182 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1377144) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1377144) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns348p905 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1377144))) 884279719003555 562949953421312 1 2000000000000000 12182 16777216 1 5290000 14828893993809368580096 883870958912931 562949953421312 200000000529 1058000000000000000 qz17 (Ns348p904 rfl) rfl rfl 

noncomputable abbrev qz462 := (@HMul.hMul Real Real Real qz583 qz588 qz662)

noncomputable abbrev qz141 := qz462

noncomputable abbrev qz463 := qz662

noncomputable abbrev qz142 := qz463

noncomputable def Ns348p906 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 688572 4000) qz461) qz141 566084842216227335961 281474976710656000 134486809813647 33062500000000000000 883870958912931 2251799813685248 200000000529 4232000000000000000 Ns348p897 282987179173181609793 140737488355328000 2176788957084477 529000000000000000000 (Ns348p903 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz142 1 4 0 1 883870958912931 562949953421312 200000000529 1058000000000000000 883870958912931 2251799813685248 200000000529 4232000000000000000 qz364 Ns348p905 rfl) 

noncomputable def Ns348p907 := @Ns348p893 Ns348p887 Ns348p888 5008073853724426323 541696000000000000000000 (@Ns348p895 5008073853724426323 541696000000000000000000 (Ns348p896 (Ns348p906 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 688572 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz663 (Real.log Real.pi) 688572 2000 0 1 38410761 33554432 1 67108864 6612143630823 16777216000 172143 33554432000 (Enclosure.Real.IsNear.const Bool.false 688572 2000) RS349to360.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns348p889 Ns348p890) 

noncomputable def Ns348p908 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz134) Bool.false Ns348p887 Ns348p888 5008073853724426323 541696000000000000000000 42692784603 33554432 311 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz134) (@HAdd.hAdd Real Real Real qz365 qz138 (Enclosure.sfrac Bool.true Ns348p889 Ns348p890)) Bool.false Ns348p887 Ns348p888 5008073853724426323 541696000000000000000000 Ns348p891 (Ns348p907 rfl rfl)) 

noncomputable def Ns348p909 := nat_lit 7591580199753183999819776 

noncomputable def Ns348p910 := nat_lit 3502830673569970439610573206939233885359975051533793095727958645668532464302300335115863508056341457175000886167595264711165549688648499121 

noncomputable def Ns348p911 := nat_lit 2485584925418092888798577280200647209157393024272840519321172194889251353159042285871380903873648357374019458392099463372118946611121 

noncomputable def Ns348p912 := nat_lit 17492439316506092727254133186132710769798480295891292869519105561380367030298054332839535364044369999809123485605923435581578518440608399281 

noncomputable def Ns348p913 := BSN.sin_dyadic_bound_f 107882843277 68719476736 4 3 33554432 10590333 Ns348p910 Ns348p785 Ns348p911 Ns348p912 Ns348p788 Ns348p911 33554418 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107882843277) qz379 0 3 Ns348p910 Ns348p785 Ns348p911 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107882843277) qz380 0 3 Ns348p912 Ns348p788 Ns348p911 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p914 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz134) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 42692784603) qz366) Bool.false 42692784603 33554432 311 33554432 Bool.true 33554418 33554432 1 5290000 (Ns348p908 rfl) (Enclosure.sfrac_false_div 42692784603 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 42692784603) qz366) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns348p909) qz367) 226375608064910080 72057594037927936 Bool.false 33554418 33554432 202 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q1 42692784603 33554432 226375608064910080 72057594037927936 202 Ns348p909 Ns348p99 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554418 33554432 Ns348p909 Ns348p99 107882843277 68719476736 10590333 10580000 (Ns348p913 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p915 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz134) Bool.false Ns348p887 Ns348p888 5008073853724426323 541696000000000000000000 341542276827 268435456 2483 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz134) (@HAdd.hAdd Real Real Real qz365 qz138 (Enclosure.sfrac Bool.true Ns348p889 Ns348p890)) Bool.false Ns348p887 Ns348p888 5008073853724426323 541696000000000000000000 Ns348p891 (Ns348p907 rfl rfl)) 

noncomputable def Ns348p916 := Ns348p886 50864 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 506 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 260774166 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 328 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 213810499 268435456) qz137 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 1) Bool.true 16777209 16777216 104921527 11093934080000 268435344 268435456 2539 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz134)) Bool.true 16777209 16777216 104921527 11093934080000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz134) qz134) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz134)) Bool.true 33554418 33554432 1678744432 177502945280000 16777209 16777216 104921527 11093934080000 (Ns348p914 rfl rfl) rfl)) rfl) (Ns348p915 rfl) RS349to360.d7 

noncomputable def Ns348p917 := nat_lit 17080358773889032153340628486241 

noncomputable def Ns348p918 := BSN.cos_dyadic_bound_f 64287161 268435456 2 1 268435456 134217728 Ns348p917 Ns348p567 Ns348p917 Ns348p917 Ns348p568 Ns348p917 260774166 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 64287161) qz368 0 1 Ns348p917 Ns348p567 Ns348p917 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 64287161) qz369 0 1 Ns348p917 Ns348p568 Ns348p917 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p919 := nat_lit 8051198342015207070390631330133186194825238945689177660839001187064001 

noncomputable def Ns348p920 := nat_lit 851709652398530630312013044586607981286526155872825284317977417921 

noncomputable def Ns348p921 := nat_lit 24151891606740824149911269964310385368513143784755787331948367606356161 

noncomputable def Ns348p922 := BSN.cos_dyadic_bound_f 174295609 268435456 3 2 268435456 134217728 Ns348p919 Ns348p121 Ns348p920 Ns348p921 Ns348p124 Ns348p920 213810499 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 174295609) qz368 0 2 Ns348p919 Ns348p121 Ns348p920 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 174295609) qz369 0 2 Ns348p921 Ns348p124 Ns348p920 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p923 := nat_lit 2400996114041138231286859738252896550156129905428256543330841448038656 

noncomputable def Ns348p924 := nat_lit 75756153614418248613549763172306020476957591021871826247111557376 

noncomputable def Ns348p925 := nat_lit 7202836829816185857363352115232345038427435801102725886340030121001216 

noncomputable def Ns348p926 := BSN.cos_dyadic_bound_f 128803374 268435456 3 2 268435456 134217728 Ns348p923 Ns348p121 Ns348p924 Ns348p925 Ns348p124 Ns348p924 238121960 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 128803374) qz368 0 2 Ns348p923 Ns348p121 Ns348p924 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 128803374) qz369 0 2 Ns348p925 Ns348p124 Ns348p924 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p927 := nat_lit 15715182819146263850412926485046748689324609310769650092516773554098241 

noncomputable def Ns348p928 := nat_lit 3244307044316981405002937634866755098114683767338317106185143914561 

noncomputable def Ns348p929 := nat_lit 47139059843350157588428773579870512557777598564774273643337950374465601 

noncomputable def Ns348p930 := BSN.cos_dyadic_bound_f 206010921 268435456 3 2 268435456 134217728 Ns348p927 Ns348p121 Ns348p928 Ns348p929 Ns348p124 Ns348p928 193188472 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 206010921) qz368 0 2 Ns348p927 Ns348p121 Ns348p928 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 206010921) qz369 0 2 Ns348p929 Ns348p124 Ns348p928 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p931 := Ns348p884 86508 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 202 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 238121960 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 104 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 193188472 268435456) qz137 rfl rfl (Ns348p916 RS349to360.d9 RS349to360.d11 RS349to360.d13 RS349to360.d17 (Ns348p918 rfl rfl) (Ns348p922 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns348p915 rfl) RS349to360.d19 RS349to360.d21 RS349to360.d23 RS349to360.d25 RS349to360.d17 (Ns348p926 rfl rfl) (Ns348p930 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns348p932 := nat_lit 28383373275676346338510704044364109667510901029409024293353322761591681 

noncomputable def Ns348p933 := nat_lit 10579535729733569810588640453042393527182799923800392418541720214401 

noncomputable def Ns348p934 := nat_lit 85128960755569571875910934852186244215478337488379472095222884844346241 

noncomputable def Ns348p935 := BSN.cos_dyadic_bound_f 238813199 268435456 3 2 268435456 134217728 Ns348p932 Ns348p121 Ns348p933 Ns348p934 Ns348p124 Ns348p933 169029815 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 238813199) qz368 0 2 Ns348p932 Ns348p121 Ns348p933 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 238813199) qz369 0 2 Ns348p934 Ns348p124 Ns348p933 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p936 := BSN.sin_dyadic_bound_f 2906935 268435456 1 0 268435456 134217728 0 1 1 0 1 1 2906878 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 2906935) qz370 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 2906935) qz371 0 0 rfl) rfl rfl 

noncomputable def Ns348p937 := Ns348p882 116631 BSN.abs_quadSignPos (BSN.cos_quad_nat0 24 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 169029815 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 43 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 2906878 268435456) qz137 rfl rfl (Ns348p931 rfl rfl) (Ns348p915 rfl) RS349to360.d27 RS349to360.d29 RS349to360.d31 RS349to360.d33 RS349to360.d17 (Ns348p935 rfl rfl) (Ns348p936 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p938 := nat_lit 42697396724610478318118842200491454794174292067646911511294095520690625 

noncomputable def Ns348p939 := nat_lit 7392133484732115116747735717320112761494596546045415891471788143041 

noncomputable def Ns348p940 := nat_lit 111814547015004543599169852286316244278366440354191170903850724421005761 

noncomputable def Ns348p941 := BSN.sin_dyadic_bound_f 228347481 268435456 3 2 268435456 134217728 Ns348p938 Ns348p162 Ns348p939 Ns348p940 Ns348p165 Ns348p939 201787297 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 228347481) qz370 0 2 Ns348p938 Ns348p162 Ns348p939 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 228347481) qz371 0 2 Ns348p940 Ns348p165 Ns348p939 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p942 := nat_lit 28143566047666762003476877361521 

noncomputable def Ns348p943 := BSN.sin_dyadic_bound_f 72835781 268435456 2 1 268435456 134217728 Ns348p942 Ns348p137 Ns348p942 Ns348p942 Ns348p138 Ns348p942 71945341 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 72835781) qz370 0 1 Ns348p942 Ns348p137 Ns348p942 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 72835781) qz371 0 1 Ns348p942 Ns348p138 Ns348p942 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p944 := Ns348p880 142951 BSN.abs_quadSignNeg qz596 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 201787297 268435456) BSN.abs_quadSignNeg qz597 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 71945341 268435456) qz137 rfl rfl (Ns348p937 rfl) (Ns348p915 rfl) RS349to360.d35 RS349to360.d37 RS349to360.d39 RS349to360.d41 RS349to360.d17 (Ns348p941 rfl rfl) (Ns348p943 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p945 := nat_lit 8191171125408091913779926504493070318349452615945336991568362737827840 

noncomputable def Ns348p946 := nat_lit 272132579582061272894568244368109632556919050375967794235399274496 

noncomputable def Ns348p947 := nat_lit 21452626637606631674981787734610016751510140887108607220535997476438016 

noncomputable def Ns348p948 := BSN.sin_dyadic_bound_f 151128916 268435456 3 2 268435456 134217728 Ns348p945 Ns348p162 Ns348p946 Ns348p947 Ns348p165 Ns348p946 143270658 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 151128916) qz370 0 2 Ns348p945 Ns348p162 Ns348p946 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 151128916) qz371 0 2 Ns348p947 Ns348p165 Ns348p946 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p949 := Ns348p878 Bool.true 387270968 142951 Bool.true 151128916 14148475504056880 1 Bool.false 143270658 Bool.false Bool.true 341964809 155069 BSN.abs_quadSignPos qz372 (BSN.sfrac_eq_quadSignPos_mul Bool.false 143270658 268435456) qz137 rfl (Ns348p944 rfl) (Ns348p915 rfl) RS349to360.d43 RS349to360.d45 RS349to360.d17 (Ns348p948 rfl rfl) rfl 

noncomputable def Ns348p950 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 10) 341964809 268435456 155069 268435456 341964809 268435456 155069 268435456 183590958879735808 341964809 134217728 155069 134217728 (Ns348p949 rfl rfl rfl rfl) 

noncomputable def Ns348p951 := @Enclosure.Real.IsNear.mulLit_ff qz660 (Zeta.RiemannSiegel.correction qz136) 10370687 33554432 1 33554432 108204674842535 281474976710656 1145832874169 74450131339968512 1122156814728704771545 9444732965739290427392 

noncomputable abbrev qz664 := (@HPow.hPow Real Real Real qz7 qz135 qz9)

noncomputable def Ns348p952 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz664 1 1 0 1 10370687 33554432 1 33554432 10370687 33554432 1 33554432 

noncomputable def Ns348p953 := @Enclosure.Real.IsNear.sqrt_image qz135 919304386479 8388608000 172143 8388608000 175632373 175632407 16777216 (@Enclosure.Real.IsNear.of_eq qz135 (@HMul.hMul Real Real Real qz5 qz134 qz3) Bool.false 919304386479 8388608000 172143 8388608000 (BSN.t_div_two_pi_mk qz134 688572 1000 qz137) (@Enclosure.Real.IsNear.mulLit_ff qz134 qz3 688572 1000 0 1 5340353 33554432 1 33554432 919304386479 8388608000 172143 8388608000 (Enclosure.Real.IsNear.const Bool.false 688572 1000) RS349to360.d48 rfl)) 

noncomputable abbrev qz770 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 688572 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz665 := qz770

noncomputable abbrev qz464 := qz665

noncomputable abbrev qz143 := qz464

noncomputable def Ns348p954 := @Enclosure.Real.IsNear.sqrt_image qz143 87816195 8388608 17 16777216 54282798 54282805 16777216 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 351264780 33554432 34 33554432 87816195 8388608 17 16777216 (Ns348p953 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns348p955 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz143) 108565603 33554432 7 33554432 5185343 5185344 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz143) Bool.false 108565603 33554432 7 33554432 108565603 33554432 7 33554432 (Ns348p954 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns348p956 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 10370687 33554432 1 33554432 10370687 33554432 1 33554432 (Ns348p955 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz465 := (@HMul.hMul Real Real Real qz583 qz581 qz659)

noncomputable abbrev qz144 := (Real.cos qz465)

noncomputable abbrev qz666 := (@HMul.hMul Real Real Real qz738 qz769 qz769)

noncomputable abbrev qz466 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz666 qz659) qz602)

noncomputable abbrev qz145 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz466))

noncomputable def Ns348p957 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz136) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz144) qz145) Bool.false 108204674842535 

noncomputable def Ns348p958 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz144) qz145 17111135 16777216 115 

noncomputable abbrev qz146 := (@Neg.neg Real Real.instNeg (Real.cos qz465))

noncomputable def Ns348p959 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz144) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz146)) Bool.true 17111135 16777216 115 16777216 (BSN.inv_eq_neg_inv_neg qz144) 

noncomputable def Ns348p960 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz146) Bool.false 34222270 33554432 230 33554432 17111135 16777216 

noncomputable def Ns348p961 := @Enclosure.Real.IsNear.recentre' qz144 Bool.true 32899627 33554432 582807216 88751472640000 32899627 33554432 36425451 5546967040000 

noncomputable abbrev qz147 := qz465

noncomputable def Ns348p962 := @Enclosure.Real.IsNear.cos_image qz147 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 98774563) qz366) Bool.false 98774563 33554432 107 16777216 Bool.true 32899627 33554432 1 

noncomputable def Ns348p963 := nat_lit 458763282021267634315948599 

noncomputable def Ns348p964 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz136 884279719003555 140737488355328 1 500000000000000 3930115 8388608 17 16777216 3475320987851656558825 1180591620717411303424 Ns348p963 

noncomputable def Ns348p965 := @Enclosure.Real.IsNear.subLit_ff_p qz143 qz1 87816195 8388608 17 16777216 10 1 0 1 3930115 3930115 8388608 17 

noncomputable def Ns348p966 := @Ns348p965 16777216 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 351264780 33554432 34 33554432 87816195 8388608 17 16777216 (Ns348p953 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns348p967 := @Enclosure.Real.IsNear.recentre' qz147 Bool.false 3475320987851656558825 1180591620717411303424 Ns348p963 Ns348p477 98774563 33554432 107 16777216 (@Ns348p964 Ns348p477 RS349to360.d47 (Ns348p966 rfl rfl) rfl) 

noncomputable def Ns348p968 := nat_lit 6639009776582797742309376 

noncomputable def Ns348p969 := nat_lit 5349400779490029258332400821543603340833780354935410539014795195305631234204429781576216545 

noncomputable def Ns348p970 := nat_lit 6277519365317618992402406733163517668525862614505390227804335471559859199805130105188321 

noncomputable def Ns348p971 := nat_lit 14000171772072895722025731588379553530720382866312114113241351825513175365164298264910262241 

noncomputable def Ns348p972 := BSN.sin_dyadic_bound_f 94346003387 68719476736 3 2 33554432 10590333 Ns348p969 Ns348p190 Ns348p970 Ns348p971 Ns348p193 Ns348p970 32899627 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 94346003387) qz379 0 2 Ns348p969 Ns348p190 Ns348p970 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 94346003387) qz380 0 2 Ns348p971 Ns348p193 Ns348p970 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p973 := @Ns348p962 5290000 (Ns348p967 rfl) (Enclosure.sfrac_false_div 98774563 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 98774563) qz366) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns348p968) qz367) 226375608064910080 72057594037927936 Bool.false 32899627 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q1 98774563 33554432 226375608064910080 72057594037927936 0 Ns348p968 Ns348p99 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 32899627 33554432 Ns348p968 Ns348p99 94346003387 68719476736 10590333 10580000 (Ns348p972 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p974 := @Enclosure.Real.IsNear.inv_image qz146 32899627 33554432 36425451 5546967040000 17111020 17111250 16777216 (@Enclosure.Real.IsNear.neg qz144 Bool.true 32899627 33554432 36425451 5546967040000 (Ns348p961 (Ns348p973 rfl rfl) rfl)) 

noncomputable def Ns348p975 := Ns348p959 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz146) Bool.false 17111135 16777216 115 16777216 (@Ns348p960 115 16777216 (Ns348p974 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p976 := @Enclosure.Real.IsNear.recentre' qz145 Bool.true 6323641 16777216 

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz349 qz346 qz466)

noncomputable def Ns348p977 := @Enclosure.Real.IsNear.cos_image qz148 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16418715)) qz636) Bool.true 16418715 8388608 

noncomputable def Ns348p978 := nat_lit 19383797630093306361048325445 

noncomputable def Ns348p979 := nat_lit 14908748297358548286441619668275259 

noncomputable def Ns348p980 := @Enclosure.Real.IsNear.recentre' qz148 Bool.true Ns348p978 Ns348p734 Ns348p979 

noncomputable abbrev qz149 := qz466

noncomputable def Ns348p981 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz149 884279719003555 140737488355328 1 500000000000000 21920436727799 

noncomputable abbrev qz467 := (@HSub.hSub Real Real Real qz587 qz666 qz659)

noncomputable abbrev qz150 := qz467

noncomputable def Ns348p982 := @Enclosure.Real.IsNear.subLit_tf qz150 qz31 17522390216695 70368744177664 552460781 281474976710656 1 16 

noncomputable abbrev qz468 := qz666

noncomputable abbrev qz151 := qz468

noncomputable def Ns348p983 := @Enclosure.Real.IsNear.subLit_ff_n qz151 qz136 15445803913225 70368744177664 267248109 281474976710656 3930115 8388608 17 16777216 

noncomputable def Ns348p984 := @Enclosure.Real.IsNear.mulLit_ff qz136 qz136 3930115 8388608 17 16777216 3930115 8388608 17 16777216 15445803913225 70368744177664 

noncomputable def Ns348p985 := nat_lit 35874308038198354815741292259219670949404612054646222544290295718127032756862307020878140625 

noncomputable def Ns348p986 := nat_lit 58158844227896986633558482781719779619497718984807332131428259197799420928759449934993817600 

noncomputable def Ns348p987 := nat_lit 383769072101852975257485604228277799268523288045882759583879939715338419860156494140625 

noncomputable def Ns348p988 := nat_lit 216379065598001770533004983679611523521851524585731479877619627406862096695598606043623740625 

noncomputable def Ns348p989 := nat_lit 5292454824738625783653821933136499945374292427617467223959971586999747304517109944084437401600 

noncomputable def Ns348p990 := BSN.cos_dyadic_bound_t 16418715 8388608 4 3 16777216 5290000 Ns348p985 Ns348p986 Ns348p987 Ns348p988 Ns348p989 Ns348p987 6323641 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16418715) (BSN.cosEvenQ 8388608) 0 3 Ns348p985 Ns348p986 Ns348p987 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16418715) (BSN.cosOddQ 8388608) 0 3 Ns348p988 Ns348p989 Ns348p987 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p991 := @Ns348p976 2228904432 177502945280000 6323641 16777216 139306527 11093934080000 (@Ns348p977 415 33554432 Bool.true 6323641 16777216 1 5290000 (@Ns348p980 Ns348p335 16418715 8388608 415 33554432 (@Ns348p981 70368744177664 552460781 281474976710656 Ns348p978 Ns348p734 Ns348p979 Ns348p335 RS349to360.d47 (@Ns348p982 0 1 350726987644784 21920436727799 70368744177664 552460781 281474976710656 (@Ns348p983 146988462750889410560 17522390216695 70368744177664 552460781 281474976710656 (@Ns348p984 267248109 281474976710656 (Ns348p966 rfl rfl) (Ns348p966 rfl rfl) rfl) (Ns348p966 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16418715 8388608) (BSN.cos_neg_of_bound 16418715 8388608 Bool.true 6323641 16777216 1 5290000 (Ns348p990 rfl rfl)) rfl rfl) 

noncomputable def Ns348p992 := @Ns348p951 23823390749291617559 Ns348p875 (Ns348p952 qz33 (@Enclosure.Real.IsNear.of_eq qz664 (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 10370687 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz135 (BSN.t_div_two_pi_nonneg qz134 688572 1000 qz137)) Ns348p956) rfl) (@Ns348p957 281474976710656 1145832874169 74450131339968512 (BSN.correction_mk qz136 (BSN.cos_two_pi_p_ne_zero_mk qz134 688572 1000 10 qz137 rfl rfl (@BSN.floor_sqrt_eq_dec qz134 688572 1000 10 qz137 rfl rfl rfl))) (@Ns348p958 16777216 6323641 16777216 139306527 11093934080000 108204674842535 281474976710656 1145832874169 74450131339968512 Ns348p975 (Ns348p991 rfl) rfl)) 

noncomputable def Ns348p993 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz134) (hardyZApproximantRS₀ qz134) Bool.true 25185790977013436597721 9444732965739290427392 5796277099128080211223 Ns348p875 (@Eq.refl Real (hardyZApproximantRS₀ qz134)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz134) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 10) (@HMul.hMul Real Real Real qz5 qz660 (Zeta.RiemannSiegel.correction qz136))) Bool.true 25185790977013436597721 9444732965739290427392 5796277099128080211223 Ns348p875 (BSN.hardyZApproximantRS₀_eq qz134 10 (@BSN.floor_sqrt_eq_dec qz134 688572 1000 10 qz137 rfl rfl rfl)) (@Ns348p877 25185790977013436597721 9444732965739290427392 5796277099128080211223 Ns348p875 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 10)) Bool.true 341964809 134217728 155069 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz134) qz134 10) (Ns348p950 (Ns348p949 rfl rfl rfl rfl) rfl rfl)) (Ns348p992 rfl) rfl rfl)) 

theorem RS349to360.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz134) Bool.true 25185790977013436597721 9444732965739290427392 5796277099128080211223 Ns348p875 := Ns348p993 

noncomputable def Ns348p994 := nat_lit 271536072765004599787520000 

noncomputable def Ns348p995 := nat_lit 541621831857228566325631123456 

noncomputable abbrev qz771 := (Enclosure.sfrac Bool.false 689910 1000)

noncomputable abbrev qz667 := qz771

noncomputable abbrev qz469 := qz667

noncomputable abbrev qz152 := qz469

noncomputable abbrev qz772 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 689910 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz668 := qz772

noncomputable abbrev qz470 := qz668

noncomputable abbrev qz153 := qz470

noncomputable abbrev qz773 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 689910 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz669 := qz773

noncomputable abbrev qz471 := qz669

noncomputable abbrev qz154 := qz471

noncomputable abbrev qz670 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz153 qz9))

noncomputable def Ns348p996 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 10) (@HMul.hMul Real Real Real qz5 qz670 (Zeta.RiemannSiegel.correction qz154)) 30660729 16777216 77687 67108864 2237735034380481873005 18889465931478580854784 1289815045729788707301 Ns348p994 Ns348p995 

noncomputable def Ns348p997 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin BSN.quadSignPos 9 10 689910 1000 199 268435456 134217728 4503599627370496 Bool.false 342385908029 2488 618095470 52 84886744 8 

noncomputable def Ns348p998 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 689910 1000 101 153 268435456 134217728 4503599627370496 Bool.false 342385908029 2488 

noncomputable def Ns348p999 := Ns348p998 558195838 52 94906264 8 589812974 52 89478488 8 Bool.false 255308633 116861 Bool.true 131582310 Bool.true 18374338 14148475504056880 1 Bool.false 126375851 Bool.true Bool.false 18359992 Bool.true Bool.false 204508025 

noncomputable def Ns348p1000 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 689910 1000 25 42 268435456 134217728 4503599627370496 Bool.false 342385908029 2488 

noncomputable def Ns348p1001 := Ns348p1000 480971758 52 109588312 8 522351262 52 101459064 8 Bool.false 313488047 86679 Bool.false 17246760 Bool.true 279839150 14148475504056880 1 Bool.false 17234896 Bool.true Bool.false 135312448 Bool.true Bool.false 255308633 

noncomputable def Ns348p1002 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 689910 1000 203 105 268435456 134217728 4503599627370496 Bool.false 342385908029 2488 

noncomputable def Ns348p1003 := Ns348p1002 372130544 51 134217720 8 432030192 51 120047984 16 Bool.false 309425447 50966 Bool.false 52866479 Bool.false 49928298 14148475504056880 1 Bool.false 52525389 Bool.false Bool.false 49640917 Bool.true Bool.false 313488047 

noncomputable def Ns348p1004 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 689910 1000 507 329 268435456 134217728 4503599627370496 Bool.false 342385908029 2488 

noncomputable def Ns348p1005 := Ns348p1004 186065264 51 189812528 16 294906480 51 154981288 8 Bool.false 268435440 2547 Bool.false 237305611 Bool.false 201684512 14148475504056880 1 Bool.false 207581617 Bool.false Bool.false 183237734 Bool.true Bool.false 309425447 

noncomputable def Ns348p1006 := nat_lit 15485709578079835007229949192666069849843249716519 

noncomputable def Ns348p1007 := nat_lit 12141018116060660423641065392135995851695718400 

noncomputable def Ns348p1008 := nat_lit 75024656369054450093709648000000000 

noncomputable def Ns348p1009 := nat_lit 310561640175552451560092744470080000000 

noncomputable abbrev qz671 := (@Eq.refl Real qz771)

noncomputable abbrev qz472 := qz671

noncomputable abbrev qz155 := qz472

noncomputable def Ns348p1010 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz152 689910 1000 1903904232400 16000000 1379820 4000 2000 Ns348p1008 Ns348p1009 qz155 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns348p1011 := nat_lit 44598843584869924820822253674878281167548559183574720000000 

noncomputable abbrev qz672 := (@HSub.hSub Real Real Real qz742 qz743 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz744 (@Nat.cast Real Real.instNatCast 1379820))))

noncomputable abbrev qz473 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 689910 4000) (Real.log (Enclosure.sfrac Bool.false 1903904232400 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz672))

noncomputable abbrev qz673 := (Enclosure.sfrac Bool.false 689910 2000)

noncomputable abbrev qz156 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz473 qz673) (@HMul.hMul Real Real Real qz349 qz673 (Real.log Real.pi)))

noncomputable def Ns348p1012 := @Enclosure.Real.IsNear.addLit_ft_p qz156 (Enclosure.sfrac Bool.true Ns348p1008 Ns348p1009) 143607085558553563059 112589990684262400 2007102222932636451 216678400000000000000000 Ns348p1008 Ns348p1009 0 1 Ns348p1011 

noncomputable def Ns348p1013 := nat_lit 38549233496741340400167419904 

noncomputable abbrev qz157 := (@HSub.hSub Real Real Real qz353 qz473 qz673)

noncomputable def Ns348p1014 := @Enclosure.Real.IsNear.subLit_ff_p qz157 (@HMul.hMul Real Real Real qz5 qz673 (Real.log Real.pi)) 7522666179012892587 4503599627370496 436194041983137 105800000000000000000 2649996812151 6710886400 68991 13421772800 Ns348p1013 143607085558553563059 112589990684262400 

noncomputable abbrev qz158 := qz473

noncomputable def Ns348p1015 := @Enclosure.Real.IsNear.subLit_ff_p qz158 qz673 226905134711812050867 112589990684262400 436194041983137 105800000000000000000 689910 2000 0 1 376133308950644629350000 7522666179012892587 4503599627370496 436194041983137 105800000000000000000 

noncomputable def Ns348p1016 := nat_lit 510944940068284474784456872103510016 

noncomputable def Ns348p1017 := nat_lit 56514034752229486685585408 

noncomputable def Ns348p1018 := nat_lit 7753130342389591575403557195609981677102241602377350089503974723671502477829429110487417907639873323758979971749236505265004180725365686658082394865664000000000000000000000000000000 

noncomputable def Ns348p1019 := nat_lit 228516269011692712373989393757045462386042839573209817767665278661457381669331956594753190179770756763818502337401773569219518196904408765248221636198400000000000000000000000000000 

noncomputable def Ns348p1020 := nat_lit 15157485045757448667641856741611559572123524389931127489858115604447089732108357225830904122643505174362951146139081475584174903004102087252377600000000000000000000000000000 

noncomputable def Ns348p1021 := BSN.log_dyadic_bound 855328232400 2952480232400 8 7 Ns348p1018 134217728 42320000 Ns348p1019 Ns348p1020 80057329 3807808464800 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 855328232400) (BSN.artanhQ 2952480232400) 0 7 Ns348p1019 Ns348p1018 Ns348p1020 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz474 := (Real.log (Enclosure.sfrac Bool.false 1903904232400 16000000))

noncomputable def Ns348p1022 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 689910 4000) qz474 689910 4000 0 1 3289549771709687 281474976710656 781250529 33062500000000000 226949328300023015817 112589990684262400 53899255246239 13225000000000000000 (Enclosure.Real.IsNear.const Bool.false 689910 4000) (BSN.isNear_log_sfrac 1903904232400 16000000 3289549771709687 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1903904232400) qz356)) Bool.false Ns348p1017 Ns348p99 1000000677120000 42320000000000000000000 3289549771709687 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 1903904232400 16000000 16 3807808464800 2097152000000 80057329 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns348p1021 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p1023 := BSN.arctan_dyadic_bound_f 1000 1379820 1 0 16777216 5290000 0 1 1 0 1 1 12158 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1379820) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1379820) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns348p1024 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1379820))) 884279719003555 562949953421312 1 2000000000000000 12158 16777216 1 5290000 14828907504608250691584 883871764219299 562949953421312 200000000529 1058000000000000000 qz17 (Ns348p1023 rfl) rfl rfl 

noncomputable abbrev qz475 := (@HMul.hMul Real Real Real qz583 qz588 qz672)

noncomputable abbrev qz159 := qz475

noncomputable abbrev qz476 := qz672

noncomputable abbrev qz160 := qz476

noncomputable def Ns348p1025 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 689910 4000) qz474) qz159 226949328300023015817 112589990684262400 53899255246239 13225000000000000000 883871764219299 2251799813685248 200000000529 4232000000000000000 Ns348p1016 226905134711812050867 112589990684262400 436194041983137 105800000000000000000 (Ns348p1022 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz160 1 4 0 1 883871764219299 562949953421312 200000000529 1058000000000000000 883871764219299 2251799813685248 200000000529 4232000000000000000 qz364 Ns348p1024 rfl) 

noncomputable def Ns348p1026 := @Ns348p1012 Ns348p1006 Ns348p1007 2007102222932636451 216678400000000000000000 (@Ns348p1014 2007102222932636451 216678400000000000000000 (Ns348p1015 (Ns348p1025 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 689910 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz673 (Real.log Real.pi) 689910 2000 0 1 38410761 33554432 1 67108864 2649996812151 6710886400 68991 13421772800 (Enclosure.Real.IsNear.const Bool.false 689910 2000) RS349to360.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns348p1008 Ns348p1009) 

noncomputable def Ns348p1027 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns348p1006 Ns348p1007 2007102222932636451 216678400000000000000000 42798238503 33554432 39 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz365 qz156 (Enclosure.sfrac Bool.true Ns348p1008 Ns348p1009)) Bool.false Ns348p1006 Ns348p1007 2007102222932636451 216678400000000000000000 Ns348p1010 (Ns348p1026 rfl rfl)) 

noncomputable def Ns348p1028 := nat_lit 7597278937040327809171456 

noncomputable def Ns348p1029 := nat_lit 3513381525694280506964606155213136606547817061175026523059472180242744662268884174665218384992906979679625564319122983808874502044442540625 

noncomputable def Ns348p1030 := nat_lit 2508067712365169323464593944298471718450445119916430060133746463057638775415408674238004045038700489941385308970960885655000244140625 

noncomputable def Ns348p1031 := nat_lit 17545062804029341320507717445593146860886002755595094434052039096357161613568129924441623410063127292936229927801852318775727988397236140625 

noncomputable def Ns348p1032 := BSN.sin_dyadic_bound_f 107963827205 68719476736 4 3 33554432 10590333 Ns348p1029 Ns348p785 Ns348p1030 Ns348p1031 Ns348p788 Ns348p1030 33554430 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107963827205) qz379 0 3 Ns348p1029 Ns348p785 Ns348p1030 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107963827205) qz380 0 3 Ns348p1031 Ns348p788 Ns348p1030 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1033 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz152) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 42798238503) qz366) Bool.false 42798238503 33554432 39 4194304 Bool.false 33554430 33554432 1 5290000 (Ns348p1027 rfl) (Enclosure.sfrac_false_div 42798238503 33554432) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 42798238503) qz366) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns348p1028) qz367) 226375608064910080 72057594037927936 Bool.false 33554430 33554432 202 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q3 42798238503 33554432 226375608064910080 72057594037927936 202 Ns348p1028 Ns348p99 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554430 33554432 Ns348p1028 Ns348p99 107963827205 68719476736 10590333 10580000 (Ns348p1032 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p1034 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns348p1006 Ns348p1007 2007102222932636451 216678400000000000000000 342385908029 268435456 2488 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz365 qz156 (Enclosure.sfrac Bool.true Ns348p1008 Ns348p1009)) Bool.false Ns348p1006 Ns348p1007 2007102222932636451 216678400000000000000000 Ns348p1010 (Ns348p1026 rfl rfl)) 

noncomputable def Ns348p1035 := Ns348p1005 50966 BSN.abs_quadSignPos (BSN.cos_quad_nat3 507 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 207581617 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 329 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 183237734 268435456) qz155 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) Bool.false 16777215 16777216 13156519 1386741760000 268435440 268435456 2547 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.false 16777215 16777216 13156519 1386741760000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz152) qz152) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.false 33554430 33554432 210504304 22187868160000 16777215 16777216 13156519 1386741760000 (Ns348p1033 rfl rfl) rfl)) rfl) (Ns348p1034 rfl) RS349to360.d7 

noncomputable def Ns348p1036 := nat_lit 49803634337466197083748544530895726300952737210556480329222693581538145 

noncomputable def Ns348p1037 := nat_lit 10056898257278187199908775481353348321431465452298623065016324899681 

noncomputable def Ns348p1038 := nat_lit 130421807334280637201970145277757092033784375083582298329668456758952801 

noncomputable def Ns348p1039 := BSN.sin_dyadic_bound_f 237305611 268435456 3 2 268435456 134217728 Ns348p1036 Ns348p162 Ns348p1037 Ns348p1038 Ns348p165 Ns348p1037 207581617 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 237305611) qz370 0 2 Ns348p1036 Ns348p162 Ns348p1037 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 237305611) qz371 0 2 Ns348p1038 Ns348p165 Ns348p1037 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1040 := nat_lit 25982279976135440672655638314062731793190076469423888580114352900669440 

noncomputable def Ns348p1041 := nat_lit 2737665537787659013110918585876130044625028918104888679382642589696 

noncomputable def Ns348p1042 := nat_lit 68044396098055450313791158859120498104949378801671347890056685699465216 

noncomputable def Ns348p1043 := BSN.sin_dyadic_bound_f 201684512 268435456 3 2 268435456 134217728 Ns348p1040 Ns348p162 Ns348p1041 Ns348p1042 Ns348p165 Ns348p1041 183237734 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 201684512) qz370 0 2 Ns348p1040 Ns348p162 Ns348p1041 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 201684512) qz371 0 2 Ns348p1042 Ns348p165 Ns348p1041 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1044 := nat_lit 7811268142715752198427287068481 

noncomputable def Ns348p1045 := BSN.sin_dyadic_bound_f 52866479 268435456 2 1 268435456 134217728 Ns348p1044 Ns348p137 Ns348p1044 Ns348p1044 Ns348p138 Ns348p1044 52525389 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 52866479) qz370 0 1 Ns348p1044 Ns348p137 Ns348p1044 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 52866479) qz371 0 1 Ns348p1044 Ns348p138 Ns348p1044 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1046 := nat_lit 6214226043951959858848387654416 

noncomputable def Ns348p1047 := BSN.sin_dyadic_bound_f 49928298 268435456 2 1 268435456 134217728 Ns348p1046 Ns348p137 Ns348p1046 Ns348p1046 Ns348p138 Ns348p1046 49640917 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 49928298) qz370 0 1 Ns348p1046 Ns348p137 Ns348p1046 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 49928298) qz371 0 1 Ns348p1046 Ns348p138 Ns348p1046 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1048 := Ns348p1003 86679 BSN.abs_quadSignPos (BSN.cos_quad_nat3 203 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 52525389 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 105 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 49640917 268435456) qz155 rfl rfl (Ns348p1035 RS349to360.d9 RS349to360.d11 RS349to360.d13 RS349to360.d17 (Ns348p1039 rfl rfl) (Ns348p1043 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns348p1034 rfl) RS349to360.d19 RS349to360.d21 RS349to360.d23 RS349to360.d25 RS349to360.d17 (Ns348p1045 rfl rfl) (Ns348p1047 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns348p1049 := nat_lit 88476937073555866743605760000 

noncomputable def Ns348p1050 := BSN.sin_dyadic_bound_f 17246760 268435456 2 1 268435456 134217728 Ns348p1049 Ns348p137 Ns348p1049 Ns348p1049 Ns348p138 Ns348p1049 17234896 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 17246760) qz370 0 1 Ns348p1049 Ns348p137 Ns348p1049 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 17246760) qz371 0 1 Ns348p1049 Ns348p138 Ns348p1049 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1051 := nat_lit 3302051801077643777033846525019023924040344613773504198731853188360614834291030712875840414062721640000000000 

noncomputable def Ns348p1052 := nat_lit 230622500074172803876093878817903705373963631867024130824627379933688781622289297119140625000000000000 

noncomputable def Ns348p1053 := nat_lit 20023064269510306590419974343105816308227592078589084952850692926032136699869422165878295684121344616000000000 

noncomputable def Ns348p1054 := BSN.cos_dyadic_bound_f 279839150 268435456 4 3 268435456 134217728 Ns348p1051 Ns348p146 Ns348p1052 Ns348p1053 Ns348p149 Ns348p1052 135312448 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 279839150) qz368 0 3 Ns348p1051 Ns348p146 Ns348p1052 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 279839150) qz369 0 3 Ns348p1053 Ns348p149 Ns348p1052 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1055 := Ns348p1001 116861 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 25 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 17234896 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 42 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 135312448 268435456) qz155 rfl rfl (Ns348p1048 rfl rfl) (Ns348p1034 rfl) RS349to360.d27 RS349to360.d29 RS349to360.d31 RS349to360.d33 RS349to360.d17 (Ns348p1050 rfl rfl) (Ns348p1054 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p1056 := nat_lit 4706950360307769173854164079147826991178873832423777191858969095840000 

noncomputable def Ns348p1057 := nat_lit 89862821680086109859249926996545813195688868468983423904100000000 

noncomputable def Ns348p1058 := nat_lit 12327581641951913411154467135981552474151876541037133338849074327200000 

noncomputable def Ns348p1059 := BSN.sin_dyadic_bound_f 131582310 268435456 3 2 268435456 134217728 Ns348p1056 Ns348p162 Ns348p1057 Ns348p1058 Ns348p165 Ns348p1057 126375851 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 131582310) qz370 0 2 Ns348p1056 Ns348p162 Ns348p1057 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 131582310) qz371 0 2 Ns348p1058 Ns348p165 Ns348p1057 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1060 := nat_lit 113984763958292544928749803536 

noncomputable def Ns348p1061 := BSN.sin_dyadic_bound_f 18374338 268435456 2 1 268435456 134217728 Ns348p1060 Ns348p137 Ns348p1060 Ns348p1060 Ns348p138 Ns348p1060 18359992 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 18374338) qz370 0 1 Ns348p1060 Ns348p137 Ns348p1060 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 18374338) qz371 0 1 Ns348p1060 Ns348p138 Ns348p1060 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1062 := Ns348p999 143232 BSN.abs_quadSignNeg qz596 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 126375851 268435456) BSN.abs_quadSignNeg qz597 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 18359992 268435456) qz155 rfl rfl (Ns348p1055 rfl) (Ns348p1034 rfl) RS349to360.d35 RS349to360.d37 RS349to360.d39 RS349to360.d41 RS349to360.d17 (Ns348p1059 rfl rfl) (Ns348p1061 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p1063 := nat_lit 5139981805781200378784661478710849214200902392079949479319490173770785 

noncomputable def Ns348p1064 := nat_lit 107157470326617109500575183548216199734562569763171314522326473761 

noncomputable def Ns348p1065 := nat_lit 13461683617332138850068255322516955591917078877953584454184676212251681 

noncomputable def Ns348p1066 := BSN.sin_dyadic_bound_f 134509453 268435456 3 2 268435456 134217728 Ns348p1063 Ns348p162 Ns348p1064 Ns348p1065 Ns348p165 Ns348p1064 128950749 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 134509453) qz370 0 2 Ns348p1063 Ns348p162 Ns348p1064 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 134509453) qz371 0 2 Ns348p1065 Ns348p165 Ns348p1064 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1067 := Ns348p997 Bool.false 204508025 143232 Bool.true 134509453 14148475504056880 1 Bool.false 128950749 Bool.false Bool.false 245285832 155374 BSN.abs_quadSignPos qz372 (BSN.sfrac_eq_quadSignPos_mul Bool.false 128950749 268435456) qz155 rfl (Ns348p1062 rfl) (Ns348p1034 rfl) RS349to360.d43 RS349to360.d45 RS349to360.d17 (Ns348p1066 rfl rfl) rfl 

noncomputable def Ns348p1068 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 10) 245285832 268435456 155374 268435456 245285832 268435456 155374 268435456 131686828326518784 30660729 16777216 77687 67108864 (Ns348p1067 rfl rfl rfl rfl) 

noncomputable def Ns348p1069 := @Enclosure.Real.IsNear.mulLit_ff qz670 (Zeta.RiemannSiegel.correction qz154) 10365655 33554432 1 33554432 215879752353371 562949953421312 124132208737171 8092405580431360000 2237735034380481873005 18889465931478580854784 

noncomputable abbrev qz674 := (@HPow.hPow Real Real Real qz7 qz153 qz9)

noncomputable def Ns348p1070 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz674 1 1 0 1 10365655 33554432 1 33554432 10365655 33554432 1 33554432 

noncomputable def Ns348p1071 := @Enclosure.Real.IsNear.sqrt_image qz153 368436293823 3355443200 68991 3355443200 175802931 175802965 16777216 (@Enclosure.Real.IsNear.of_eq qz153 (@HMul.hMul Real Real Real qz5 qz152 qz3) Bool.false 368436293823 3355443200 68991 3355443200 (BSN.t_div_two_pi_mk qz152 689910 1000 qz155) (@Enclosure.Real.IsNear.mulLit_ff qz152 qz3 689910 1000 0 1 5340353 33554432 1 33554432 368436293823 3355443200 68991 3355443200 (Enclosure.Real.IsNear.const Bool.false 689910 1000) RS349to360.d48 rfl)) 

noncomputable abbrev qz774 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 689910 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz675 := qz774

noncomputable abbrev qz477 := qz675

noncomputable abbrev qz161 := qz477

noncomputable def Ns348p1072 := @Enclosure.Real.IsNear.sqrt_image qz161 43950737 4194304 17 16777216 54309149 54309156 16777216 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 351605896 33554432 34 33554432 43950737 4194304 17 16777216 (Ns348p1071 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns348p1073 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz161) 108618305 33554432 7 33554432 5182827 5182828 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz161) Bool.false 108618305 33554432 7 33554432 108618305 33554432 7 33554432 (Ns348p1072 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns348p1074 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 10365655 33554432 1 33554432 10365655 33554432 1 33554432 (Ns348p1073 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz478 := (@HMul.hMul Real Real Real qz583 qz581 qz669)

noncomputable abbrev qz162 := (Real.cos qz478)

noncomputable abbrev qz676 := (@HMul.hMul Real Real Real qz738 qz773 qz773)

noncomputable abbrev qz479 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz676 qz669) qz602)

noncomputable abbrev qz163 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz479))

noncomputable def Ns348p1075 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz154) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz162) qz163) Bool.false 215879752353371 

noncomputable def Ns348p1076 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz162) qz163 33857983 33554432 225 

noncomputable abbrev qz164 := (@Neg.neg Real Real.instNeg (Real.cos qz478))

noncomputable def Ns348p1077 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz162) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz164)) Bool.true 33857983 33554432 225 33554432 (BSN.inv_eq_neg_inv_neg qz162) 

noncomputable def Ns348p1078 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz164) Bool.false 33857983 33554432 225 33554432 33857983 33554432 

noncomputable def Ns348p1079 := @Enclosure.Real.IsNear.recentre' qz162 Bool.true 33253602 33554432 582807216 88751472640000 16626801 16777216 36425451 5546967040000 

noncomputable abbrev qz165 := qz478

noncomputable def Ns348p1080 := @Enclosure.Real.IsNear.cos_image qz165 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50458929) qz377) Bool.false 50458929 16777216 107 16777216 Bool.true 33253602 33554432 1 

noncomputable def Ns348p1081 := nat_lit 91752656404546543276018187 

noncomputable def Ns348p1082 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz154 884279719003555 140737488355328 1 500000000000000 2007697 4194304 17 16777216 1775365739004280362835 590295810358705651712 Ns348p1081 

noncomputable def Ns348p1083 := @Enclosure.Real.IsNear.subLit_ff_p qz161 qz1 43950737 4194304 17 16777216 10 1 0 1 2007697 2007697 4194304 17 

noncomputable def Ns348p1084 := @Ns348p1083 16777216 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 351605896 33554432 34 33554432 43950737 4194304 17 16777216 (Ns348p1071 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns348p1085 := @Enclosure.Real.IsNear.recentre' qz165 Bool.false 1775365739004280362835 590295810358705651712 Ns348p1081 Ns348p316 50458929 16777216 107 16777216 (@Ns348p1082 Ns348p316 RS349to360.d47 (Ns348p1084 rfl rfl) rfl) 

noncomputable def Ns348p1086 := nat_lit 3473945569304919626743808 

noncomputable def Ns348p1087 := nat_lit 6418086776709172035284488921532333372843819260446948611873355523448416776028000280694992865 

noncomputable def Ns348p1088 := nat_lit 9032035525675727059588408933738727823955243114058642632960024767449198434711399560097761 

noncomputable def Ns348p1089 := nat_lit 16794651595768166058124804037168153274304551478985913323976852997503316663559991802532442081 

noncomputable def Ns348p1090 := BSN.sin_dyadic_bound_f 98735471547 68719476736 3 2 33554432 10590333 Ns348p1087 Ns348p190 Ns348p1088 Ns348p1089 Ns348p193 Ns348p1088 33253602 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 98735471547) qz379 0 2 Ns348p1087 Ns348p190 Ns348p1088 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 98735471547) qz380 0 2 Ns348p1089 Ns348p193 Ns348p1088 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1091 := @Ns348p1080 5290000 (Ns348p1085 rfl) (Enclosure.sfrac_false_div 50458929 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50458929) qz377) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns348p1086) qz381) 226375608064910080 72057594037927936 Bool.false 33253602 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q1 50458929 16777216 226375608064910080 72057594037927936 0 Ns348p1086 Ns348p188 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33253602 33554432 Ns348p1086 Ns348p188 98735471547 68719476736 10590333 10580000 (Ns348p1090 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p1092 := @Enclosure.Real.IsNear.inv_image qz164 16626801 16777216 36425451 5546967040000 16928879 16929104 16777216 (@Enclosure.Real.IsNear.neg qz162 Bool.true 16626801 16777216 36425451 5546967040000 (Ns348p1079 (Ns348p1091 rfl rfl) rfl)) 

noncomputable def Ns348p1093 := Ns348p1077 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz164) Bool.false 33857983 33554432 225 33554432 (@Ns348p1078 225 33554432 (Ns348p1092 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p1094 := @Enclosure.Real.IsNear.recentre' qz163 Bool.true 6376037 16777216 

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz349 qz346 qz479)

noncomputable def Ns348p1095 := @Enclosure.Real.IsNear.cos_image qz166 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 65788073)) qz366) Bool.true 65788073 33554432 

noncomputable def Ns348p1096 := nat_lit 4854302985717835110118294525 

noncomputable def Ns348p1097 := nat_lit 15065239793046781605597950573055711 

noncomputable def Ns348p1098 := @Enclosure.Real.IsNear.recentre' qz166 Bool.true Ns348p1096 Ns348p332 Ns348p1097 

noncomputable abbrev qz167 := qz479

noncomputable def Ns348p1099 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz167 884279719003555 140737488355328 1 500000000000000 5489555941855 

noncomputable abbrev qz480 := (@HSub.hSub Real Real Real qz587 qz676 qz669)

noncomputable abbrev qz168 := qz480

noncomputable def Ns348p1100 := @Enclosure.Real.IsNear.subLit_tf qz168 qz31 4390044314079 17592186044416 558259753 281474976710656 1 16 

noncomputable abbrev qz481 := qz676

noncomputable abbrev qz169 := qz481

noncomputable def Ns348p1101 := @Enclosure.Real.IsNear.subLit_ff_n qz169 qz154 4030847243809 17592186044416 273047081 281474976710656 2007697 4194304 17 16777216 

noncomputable def Ns348p1102 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz154 2007697 4194304 17 16777216 2007697 4194304 17 16777216 4030847243809 17592186044416 

noncomputable def Ns348p1103 := nat_lit 606068248605993179324809732188494854662981172006171436792204335911464100159286912768378364198575201 

noncomputable def Ns348p1104 := nat_lit 6573035651278014644299617386113840875674375394647319549724342211972289410554819056150027623521 

noncomputable def Ns348p1105 := nat_lit 3655408391667443403039999007128334562708694872267882874734140554009214468095212184226608576507337825 

noncomputable def Ns348p1106 := BSN.cos_dyadic_bound_t 65788073 33554432 4 3 16777216 5290000 Ns348p1103 Ns348p210 Ns348p1104 Ns348p1105 Ns348p213 Ns348p1104 6376037 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 65788073) (BSN.cosEvenQ 33554432) 0 3 Ns348p1103 Ns348p210 Ns348p1104 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 65788073) (BSN.cosOddQ 33554432) 0 3 Ns348p1105 Ns348p213 Ns348p1104 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1107 := @Ns348p1094 2250064432 177502945280000 6376037 16777216 140629027 11093934080000 (@Ns348p1095 419 33554432 Bool.true 6376037 16777216 1 5290000 (@Ns348p1098 Ns348p335 65788073 33554432 419 33554432 (@Ns348p1099 17592186044416 558259753 281474976710656 Ns348p1096 Ns348p332 Ns348p1097 Ns348p335 RS349to360.d47 (@Ns348p1100 0 1 87832895069680 5489555941855 17592186044416 558259753 281474976710656 (@Ns348p1101 18413180426718806016 4390044314079 17592186044416 558259753 281474976710656 (@Ns348p1102 273047081 281474976710656 (Ns348p1084 rfl rfl) (Ns348p1084 rfl rfl) rfl) (Ns348p1084 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 65788073 33554432) (BSN.cos_neg_of_bound 65788073 33554432 Bool.true 6376037 16777216 1 5290000 (Ns348p1106 rfl rfl)) rfl rfl) 

noncomputable def Ns348p1108 := @Ns348p1069 1289815045729788707301 Ns348p994 (Ns348p1070 qz33 (@Enclosure.Real.IsNear.of_eq qz674 (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 10365655 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz153 (BSN.t_div_two_pi_nonneg qz152 689910 1000 qz155)) Ns348p1074) rfl) (@Ns348p1075 562949953421312 124132208737171 8092405580431360000 (BSN.correction_mk qz154 (BSN.cos_two_pi_p_ne_zero_mk qz152 689910 1000 10 qz155 rfl rfl (@BSN.floor_sqrt_eq_dec qz152 689910 1000 10 qz155 rfl rfl rfl))) (@Ns348p1076 33554432 6376037 16777216 140629027 11093934080000 215879752353371 562949953421312 124132208737171 8092405580431360000 Ns348p1093 (Ns348p1107 rfl) rfl)) 

noncomputable def Ns348p1109 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (hardyZApproximantRS₀ qz152) Bool.false 32283176890446458239891 18889465931478580854784 315627171209215320867301 Ns348p994 (@Eq.refl Real (hardyZApproximantRS₀ qz152)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 10) (@HMul.hMul Real Real Real qz5 qz670 (Zeta.RiemannSiegel.correction qz154))) Bool.false 32283176890446458239891 18889465931478580854784 315627171209215320867301 Ns348p994 (BSN.hardyZApproximantRS₀_eq qz152 10 (@BSN.floor_sqrt_eq_dec qz152 689910 1000 10 qz155 rfl rfl rfl)) (@Ns348p996 32283176890446458239891 18889465931478580854784 315627171209215320867301 Ns348p994 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 10)) Bool.false 30660729 16777216 77687 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz152) qz152 10) (Ns348p1068 (Ns348p1067 rfl rfl rfl rfl) rfl rfl)) (Ns348p1108 rfl) rfl rfl)) 

theorem RS349to360.d58 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz152) Bool.false 32283176890446458239891 18889465931478580854784 315627171209215320867301 Ns348p994 := Ns348p1109 

noncomputable def Ns348p1110 := nat_lit 71957473815463479645761961984 

noncomputable abbrev qz775 := (Enclosure.sfrac Bool.false 691247 1000)

noncomputable abbrev qz677 := qz775

noncomputable abbrev qz482 := qz677

noncomputable abbrev qz170 := qz482

noncomputable abbrev qz776 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 691247 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz678 := qz776

noncomputable abbrev qz483 := qz678

noncomputable abbrev qz171 := qz483

noncomputable abbrev qz777 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 691247 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz679 := qz777

noncomputable abbrev qz484 := qz679

noncomputable abbrev qz172 := qz484

noncomputable abbrev qz680 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz171 qz9))

noncomputable def Ns348p1111 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 10) (@HMul.hMul Real Real Real qz5 qz680 (Zeta.RiemannSiegel.correction qz172)) 14741699 4194304 155665 134217728 558321132018688599745 4722366482869645213696 1442846002718303880483 Ns348p74 Ns348p1110 

noncomputable def Ns348p1112 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin BSN.quadSignPos 9 10 691247 1000 199 268435456 134217728 4503599627370496 Bool.false 343229256257 2492 618095470 52 84886744 8 

noncomputable def Ns348p1113 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 691247 1000 101 152 268435456 134217728 4503599627370496 Bool.false 343229256257 2492 

noncomputable def Ns348p1114 := Ns348p1113 558195838 52 94906264 8 589812974 52 89478488 8 Bool.true 507647065 117079 Bool.true 34541918 Bool.true 385263485 14148475504056880 1 Bool.false 34446671 Bool.true Bool.false 36282550 Bool.false Bool.true 507731619 

noncomputable def Ns348p1115 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 691247 1000 25 42 268435456 134217728 4503599627370496 Bool.false 343229256257 2492 

noncomputable def Ns348p1116 := Ns348p1115 480971758 52 109588312 8 522351262 52 101459064 8 Bool.true 339325244 86840 Bool.false 217535748 Bool.true 134874559 14148475504056880 1 Bool.false 194495381 Bool.true Bool.false 235258668 Bool.true Bool.true 507647065 

noncomputable def Ns348p1117 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 691247 1000 203 105 268435456 134217728 4503599627370496 Bool.false 343229256257 2492 

noncomputable def Ns348p1118 := Ns348p1117 372130544 51 134217720 8 432030192 51 120047984 16 Bool.true 362242920 51059 Bool.false 398676170 Bool.false 315652159 14148475504056880 1 Bool.false 267452322 Bool.false Bool.false 247775290 Bool.true Bool.true 339325244 

noncomputable def Ns348p1119 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 691247 1000 508 330 268435456 134217728 4503599627370496 Bool.false 343229256257 2492 

noncomputable def Ns348p1120 := Ns348p1119 186065264 51 189812528 16 294906480 51 154981288 8 Bool.true 268435432 2547 Bool.false 410227153 Bool.false 229085348 14148475504056880 1 Bool.false 11426821 Bool.false Bool.false 176474268 Bool.true Bool.true 362242920 

noncomputable def Ns348p1121 := nat_lit 1413471160581950997060876387868668495104084234410872422837 

noncomputable def Ns348p1122 := nat_lit 1105458723627909708269958807892372270926661957976064000 

noncomputable def Ns348p1123 := nat_lit 75754443199193221901583670883360000 

noncomputable def Ns348p1124 := nat_lit 314190266302577387099847444429875699520 

noncomputable abbrev qz681 := (@Eq.refl Real qz775)

noncomputable abbrev qz485 := qz681

noncomputable abbrev qz173 := qz485

noncomputable def Ns348p1125 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz170 691247 1000 1911290660036 16000000 1382494 4000 2000 Ns348p1123 Ns348p1124 qz173 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns348p1126 := nat_lit 452310771386224319059480444117973918433306955011479175307840 

noncomputable abbrev qz682 := (@HSub.hSub Real Real Real qz742 qz743 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz744 (@Nat.cast Real Real.instNatCast 1382494))))

noncomputable abbrev qz486 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 691247 4000) (Real.log (Enclosure.sfrac Bool.false 1911290660036 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz682))

noncomputable abbrev qz683 := (Enclosure.sfrac Bool.false 691247 2000)

noncomputable abbrev qz174 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz486 qz683) (@HMul.hMul Real Real Real qz349 qz683 (Real.log Real.pi)))

noncomputable def Ns348p1127 := @Enclosure.Real.IsNear.addLit_ft_p qz174 (Enclosure.sfrac Bool.true Ns348p1123 Ns348p1124) 1439608113901759128317 1125899906842624000 20109720099947528467 Ns348p523 Ns348p1123 Ns348p1124 0 1 Ns348p1126 

noncomputable def Ns348p1128 := nat_lit 96610465129129662702984101888000 

noncomputable abbrev qz175 := (@HSub.hSub Real Real Real qz353 qz486 qz683)

noncomputable def Ns348p1129 := @Enclosure.Real.IsNear.subLit_ff_p qz175 (@HMul.hMul Real Real Real qz5 qz683 (Real.log Real.pi)) 1885065400142133224189 1125899906842624000 2185148337744777 529000000000000000000 26551323308967 67108864000 691247 134217728000 Ns348p1128 1439608113901759128317 1125899906842624000 

noncomputable def Ns348p1130 := nat_lit 3770130800284266448378000 

noncomputable abbrev qz176 := qz486

noncomputable def Ns348p1131 := @Enclosure.Real.IsNear.subLit_ff_p qz176 qz683 2274202866594754880253 1125899906842624000 2185148337744777 529000000000000000000 691247 2000 0 1 Ns348p1130 1885065400142133224189 1125899906842624000 2185148337744777 529000000000000000000 

noncomputable def Ns348p1132 := nat_lit 5121049591280525952062865384872607744 

noncomputable def Ns348p1133 := nat_lit 56532759134213024373538816 

noncomputable def Ns348p1134 := nat_lit 8029142405463227211341172620671529435975972255500235351458888182374570496862941556913328548025841778090189324758734099590987134758430815602587149335151111650651862853327448860262400 

noncomputable def Ns348p1135 := nat_lit 239715657671690832476480063031170523329347339606905449506001645116809058579325517804259500521748420964615271280738392842967059648519555450523626200673276984415058698021151115837440 

noncomputable def Ns348p1136 := nat_lit 17096544396204904615165687927010026514765569606604382213422058223153103220922429410445488871938413316558652000511612988342639320650852165834274517428989868100194152910684160 

noncomputable def Ns348p1137 := BSN.log_dyadic_bound 862714660036 2959866660036 8 7 Ns348p1134 134217728 42320000 Ns348p1135 Ns348p1136 80577035 3822581320072 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 862714660036) (BSN.artanhQ 2959866660036) 0 7 Ns348p1135 Ns348p1134 Ns348p1136 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz487 := (Real.log (Enclosure.sfrac Bool.false 1911290660036 16000000))

noncomputable def Ns348p1138 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 691247 4000) qz487 691247 4000 0 1 3290639674186999 281474976710656 781250529 33062500000000000 2274644802862740497753 1125899906842624000 540037084419663 132250000000000000000 (Enclosure.Real.IsNear.const Bool.false 691247 4000) (BSN.isNear_log_sfrac 1911290660036 16000000 3290639674186999 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1911290660036) qz356)) Bool.false Ns348p1133 Ns348p99 1000000677120000 42320000000000000000000 3290639674186999 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 1911290660036 16000000 16 3822581320072 2097152000000 80577035 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns348p1137 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p1139 := BSN.arctan_dyadic_bound_f 1000 1382494 1 0 16777216 5290000 0 1 1 0 1 1 12135 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1382494) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1382494) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns348p1140 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1382494))) 884279719003555 562949953421312 1 2000000000000000 12135 16777216 1 5290000 14828920452457179381760 883872535971235 562949953421312 200000000529 1058000000000000000 qz17 (Ns348p1139 rfl) rfl rfl 

noncomputable abbrev qz488 := (@HMul.hMul Real Real Real qz583 qz588 qz682)

noncomputable abbrev qz177 := qz488

noncomputable abbrev qz489 := qz682

noncomputable abbrev qz178 := qz489

noncomputable def Ns348p1141 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 691247 4000) qz487) qz177 2274644802862740497753 1125899906842624000 540037084419663 132250000000000000000 883872535971235 2251799813685248 200000000529 4232000000000000000 Ns348p1132 2274202866594754880253 1125899906842624000 2185148337744777 529000000000000000000 (Ns348p1138 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz178 1 4 0 1 883872535971235 562949953421312 200000000529 1058000000000000000 883872535971235 2251799813685248 200000000529 4232000000000000000 qz364 Ns348p1140 rfl) 

noncomputable def Ns348p1142 := @Ns348p1127 Ns348p1121 Ns348p1122 20109720099947528467 Ns348p523 (@Ns348p1129 20109720099947528467 Ns348p523 (Ns348p1131 (Ns348p1141 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 691247 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz683 (Real.log Real.pi) 691247 2000 0 1 38410761 33554432 1 67108864 26551323308967 67108864000 691247 134217728000 (Enclosure.Real.IsNear.const Bool.false 691247 2000) RS349to360.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns348p1123 Ns348p1124) 

noncomputable def Ns348p1143 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz170) Bool.false Ns348p1121 Ns348p1122 20109720099947528467 Ns348p523 5362957129 4194304 39 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz170) (@HAdd.hAdd Real Real Real qz365 qz174 (Enclosure.sfrac Bool.true Ns348p1123 Ns348p1124)) Bool.false Ns348p1121 Ns348p1122 20109720099947528467 Ns348p523 Ns348p1125 (Ns348p1142 rfl rfl)) 

noncomputable def Ns348p1144 := nat_lit 3514496074549643901002657909172683823872930011147448033390792472213669541045616090327567028543032332396478022815985537014556240689628184576 

noncomputable def Ns348p1145 := nat_lit 2510450572553809514007735628402389247716547488034047755833538337521259943591483820998427415407188295338336318266945338966972066430976 

noncomputable def Ns348p1146 := nat_lit 17550621711125230093825174631568300496929796659408681122141367962685253699601500768580480502659008213972144630111361390801696192292072718336 

noncomputable def Ns348p1147 := BSN.sin_dyadic_bound_f 107972371324 68719476736 4 3 33554432 10590333 Ns348p1144 Ns348p785 Ns348p1145 Ns348p1146 Ns348p788 Ns348p1145 33554429 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107972371324) qz379 0 3 Ns348p1144 Ns348p785 Ns348p1145 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107972371324) qz380 0 3 Ns348p1146 Ns348p788 Ns348p1145 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1148 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz170) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5362957129) qz625) Bool.false 5362957129 4194304 39 4194304 Bool.true 33554429 33554432 1 5290000 (Ns348p1143 rfl) (Enclosure.sfrac_false_div 5362957129 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5362957129) qz625) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949735022001255065059328) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 33554429 33554432 203 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q1 5362957129 4194304 226375608064910080 72057594037927936 203 949735022001255065059328 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554429 33554432 949735022001255065059328 604462909807314587353088 107972371324 68719476736 10590333 10580000 (Ns348p1147 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p1149 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz170) Bool.false Ns348p1121 Ns348p1122 20109720099947528467 Ns348p523 343229256257 268435456 2492 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz170) (@HAdd.hAdd Real Real Real qz365 qz174 (Enclosure.sfrac Bool.true Ns348p1123 Ns348p1124)) Bool.false Ns348p1121 Ns348p1122 20109720099947528467 Ns348p523 Ns348p1125 (Ns348p1142 rfl rfl)) 

noncomputable def Ns348p1150 := Ns348p1120 51059 BSN.abs_quadSignPos (BSN.cos_quad_nat0 508 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 11426821 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 330 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 176474268 268435456) qz173 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 1) Bool.true 33554429 33554432 13156519 1386741760000 268435432 268435456 2547 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz170)) Bool.true 33554429 33554432 13156519 1386741760000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz170) qz170) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz170)) Bool.true 33554429 33554432 210504304 22187868160000 33554429 33554432 13156519 1386741760000 (Ns348p1148 rfl rfl) rfl)) rfl) (Ns348p1149 rfl) RS349to360.d7 

noncomputable def Ns348p1151 := nat_lit 15288001091541625935704909365684444038486313731433897539866530358543823293093628650441342425138520920387446721 

noncomputable def Ns348p1152 := nat_lit 22713958922912598809591722378310281768149222625772312830292785738192244244564168084685860943065288239041 

noncomputable def Ns348p1153 := nat_lit 92546999386813091266549068242792380675810027425237519763408398295005758026649166592365848105900987184619153345 

noncomputable def Ns348p1154 := BSN.cos_dyadic_bound_f 410227153 268435456 4 3 268435456 134217728 Ns348p1151 Ns348p146 Ns348p1152 Ns348p1153 Ns348p149 Ns348p1152 11426821 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 410227153) qz368 0 3 Ns348p1151 Ns348p146 Ns348p1152 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 410227153) qz369 0 3 Ns348p1153 Ns348p149 Ns348p1152 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1155 := nat_lit 24032289576543479939116531377831357708002102645212926216914026679566336 

noncomputable def Ns348p1156 := nat_lit 7585400314862327252084240303406398244445458163268176501722128121856 

noncomputable def Ns348p1157 := nat_lit 72081697929000715162845425652887260327517417019312242297738635782455296 

noncomputable def Ns348p1158 := BSN.cos_dyadic_bound_f 229085348 268435456 3 2 268435456 134217728 Ns348p1155 Ns348p121 Ns348p1156 Ns348p1157 Ns348p124 Ns348p1156 176474268 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 229085348) qz368 0 2 Ns348p1155 Ns348p121 Ns348p1156 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 229085348) qz369 0 2 Ns348p1157 Ns348p124 Ns348p1156 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1159 := nat_lit 35399538382849652727221691889170218349826879556915093760687721107012443569904097120686276188902547736742400000 

noncomputable def Ns348p1160 := nat_lit 16122906267744005479341238889979797546184890058160205615464783714435180609009856785257759361000000000000 

noncomputable def Ns348p1161 := nat_lit 176821865316013671378441002554332192466805695342591198976973583985443335375670310128200168418329150939712000000 

noncomputable def Ns348p1162 := BSN.sin_dyadic_bound_f 398676170 268435456 4 3 268435456 134217728 Ns348p1159 Ns348p131 Ns348p1160 Ns348p1161 Ns348p134 Ns348p1160 267452322 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 398676170) qz370 0 3 Ns348p1159 Ns348p131 Ns348p1160 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 398676170) qz371 0 3 Ns348p1161 Ns348p134 Ns348p1160 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1163 := nat_lit 155973514069282411173832563556501959075118280934960370858236992576945665 

noncomputable def Ns348p1164 := nat_lit 98553059991946397486214588982774013146856441112436757667491536043521 

noncomputable def Ns348p1165 := nat_lit 408342498560514592240298080932485401556405349163095121306778089500311041 

noncomputable def Ns348p1166 := BSN.sin_dyadic_bound_f 315652159 268435456 3 2 268435456 134217728 Ns348p1163 Ns348p162 Ns348p1164 Ns348p1165 Ns348p165 Ns348p1164 247775290 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 315652159) qz370 0 2 Ns348p1163 Ns348p162 Ns348p1164 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 315652159) qz371 0 2 Ns348p1165 Ns348p165 Ns348p1164 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1167 := Ns348p1118 86840 BSN.abs_quadSignPos (BSN.cos_quad_nat3 203 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 267452322 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 105 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 247775290 268435456) qz173 rfl rfl (Ns348p1150 RS349to360.d9 RS349to360.d11 RS349to360.d13 RS349to360.d17 (Ns348p1154 rfl rfl) (Ns348p1158 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns348p1149 rfl) RS349to360.d19 RS349to360.d21 RS349to360.d23 RS349to360.d25 RS349to360.d17 (Ns348p1162 rfl rfl) (Ns348p1166 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns348p1168 := nat_lit 35166227216391854250068659670215792001807238993699100868424963492741120 

noncomputable def Ns348p1169 := nat_lit 5014701465161283277421905544314467928484675161497513009299031392256 

noncomputable def Ns348p1170 := nat_lit 92093904621511261910587806527302946104277603128474268205764610715877376 

noncomputable def Ns348p1171 := BSN.sin_dyadic_bound_f 217535748 268435456 3 2 268435456 134217728 Ns348p1168 Ns348p162 Ns348p1169 Ns348p1170 Ns348p165 Ns348p1169 194495381 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 217535748) qz370 0 2 Ns348p1168 Ns348p162 Ns348p1169 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 217535748) qz371 0 2 Ns348p1170 Ns348p165 Ns348p1169 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1172 := nat_lit 2886725056593058279776509140627968705877432353597188375866357429670401 

noncomputable def Ns348p1173 := nat_lit 109506601610502130445963766454818892477448441403339317812686328321 

noncomputable def Ns348p1174 := nat_lit 8659956156575953835068635494350996479847342163908758448963446916354561 

noncomputable def Ns348p1175 := BSN.cos_dyadic_bound_f 134874559 268435456 3 2 268435456 134217728 Ns348p1172 Ns348p121 Ns348p1173 Ns348p1174 Ns348p124 Ns348p1173 235258668 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 134874559) qz368 0 2 Ns348p1172 Ns348p121 Ns348p1173 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 134874559) qz369 0 2 Ns348p1174 Ns348p124 Ns348p1173 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1176 := Ns348p1116 117079 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 25 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 194495381 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 42 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 235258668 268435456) qz173 rfl rfl (Ns348p1167 rfl rfl) (Ns348p1149 rfl) RS349to360.d27 RS349to360.d29 RS349to360.d31 RS349to360.d33 RS349to360.d17 (Ns348p1171 rfl rfl) (Ns348p1175 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p1177 := nat_lit 1423592841261831481033447388176 

noncomputable def Ns348p1178 := BSN.sin_dyadic_bound_f 34541918 268435456 2 1 268435456 134217728 Ns348p1177 Ns348p137 Ns348p1177 Ns348p1177 Ns348p138 Ns348p1177 34446671 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 34541918) qz370 0 1 Ns348p1177 Ns348p137 Ns348p1177 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 34541918) qz371 0 1 Ns348p1177 Ns348p138 Ns348p1177 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1179 := nat_lit 11884256142517166656973609403896125569496217432506495643731563662946804225424035557468855124047241206510640625 

noncomputable def Ns348p1180 := nat_lit 10692867518735683309937351323021621779909009830061978379997900555358351836715901117920478669101806640625 

noncomputable def Ns348p1181 := nat_lit 71976679392718159861590940565873949117772645765379066682586230439619590891372032629890148871266876945544240625 

noncomputable def Ns348p1182 := BSN.cos_dyadic_bound_f 385263485 268435456 4 3 268435456 134217728 Ns348p1179 Ns348p146 Ns348p1180 Ns348p1181 Ns348p149 Ns348p1180 36282550 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 385263485) qz368 0 3 Ns348p1179 Ns348p146 Ns348p1180 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 385263485) qz369 0 3 Ns348p1181 Ns348p149 Ns348p1180 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1183 := Ns348p1114 143500 BSN.abs_quadSignNeg qz596 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 34446671 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 152 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 36282550 268435456) qz173 rfl rfl (Ns348p1176 rfl) (Ns348p1149 rfl) RS349to360.d35 RS349to360.d37 RS349to360.d39 RS349to360.d41 RS349to360.d17 (Ns348p1178 rfl rfl) (Ns348p1182 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p1184 := nat_lit 190968830043006095121925094479921 

noncomputable def Ns348p1185 := BSN.sin_dyadic_bound_f 117554869 268435456 2 1 268435456 134217728 Ns348p1184 Ns348p137 Ns348p1184 Ns348p1184 Ns348p138 Ns348p1184 113833304 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 117554869) qz370 0 1 Ns348p1184 Ns348p137 Ns348p1184 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 117554869) qz371 0 1 Ns348p1184 Ns348p138 Ns348p1184 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1186 := Ns348p1112 Bool.true 507731619 143500 Bool.true 117554869 14148475504056880 1 Bool.false 113833304 Bool.false Bool.true 471734368 155665 BSN.abs_quadSignPos qz372 (BSN.sfrac_eq_quadSignPos_mul Bool.false 113833304 268435456) qz173 rfl (Ns348p1183 rfl) (Ns348p1149 rfl) RS349to360.d43 RS349to360.d45 RS349to360.d17 (Ns348p1185 rfl rfl) rfl 

noncomputable def Ns348p1187 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 10) 471734368 268435456 155665 268435456 471734368 268435456 155665 268435456 253260460369903616 14741699 4194304 155665 134217728 (Ns348p1186 rfl rfl rfl rfl) 

noncomputable def Ns348p1188 := @Enclosure.Real.IsNear.mulLit_ff qz680 (Zeta.RiemannSiegel.correction qz172) 10360639 33554432 1 33554432 53888677331455 140737488355328 2778366228205519 186125328349921280000 558321132018688599745 4722366482869645213696 

noncomputable abbrev qz684 := (@HPow.hPow Real Real Real qz7 qz171 qz9)

noncomputable def Ns348p1189 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz684 1 1 0 1 10360639 33554432 1 33554432 10360639 33554432 1 33554432 

noncomputable def Ns348p1190 := @Enclosure.Real.IsNear.sqrt_image qz171 3691502990191 33554432000 691247 33554432000 175973196 175973229 16777216 (@Enclosure.Real.IsNear.of_eq qz171 (@HMul.hMul Real Real Real qz5 qz170 qz3) Bool.false 3691502990191 33554432000 691247 33554432000 (BSN.t_div_two_pi_mk qz170 691247 1000 qz173) (@Enclosure.Real.IsNear.mulLit_ff qz170 qz3 691247 1000 0 1 5340353 33554432 1 33554432 3691502990191 33554432000 691247 33554432000 (Enclosure.Real.IsNear.const Bool.false 691247 1000) RS349to360.d48 rfl)) 

noncomputable abbrev qz778 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 691247 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz685 := qz778

noncomputable abbrev qz490 := qz685

noncomputable abbrev qz179 := qz490

noncomputable def Ns348p1191 := @Enclosure.Real.IsNear.sqrt_image qz179 351946425 33554432 33 33554432 54335442 54335448 16777216 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 351946425 33554432 33 33554432 351946425 33554432 33 33554432 (Ns348p1190 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns348p1192 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz179) 54335445 16777216 3 16777216 5180319 5180320 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz179) Bool.false 108670890 33554432 6 33554432 54335445 16777216 3 16777216 (Ns348p1191 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns348p1193 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 10360639 33554432 1 33554432 10360639 33554432 1 33554432 (Ns348p1192 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz491 := (@HMul.hMul Real Real Real qz583 qz581 qz679)

noncomputable abbrev qz180 := (Real.cos qz491)

noncomputable abbrev qz686 := (@HMul.hMul Real Real Real qz738 qz777 qz777)

noncomputable abbrev qz492 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz686 qz679) qz602)

noncomputable abbrev qz181 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz492))

noncomputable def Ns348p1194 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz172) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz180) qz181) Bool.false 53888677331455 

noncomputable def Ns348p1195 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz180) qz181 16818689 16777216 27 

noncomputable abbrev qz182 := (@Neg.neg Real Real.instNeg (Real.cos qz491))

noncomputable def Ns348p1196 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz180) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz182)) Bool.true 16818689 16777216 27 4194304 (BSN.inv_eq_neg_inv_neg qz180) 

noncomputable def Ns348p1197 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz182) Bool.false 33637378 33554432 216 33554432 16818689 16777216 

noncomputable def Ns348p1198 := @Enclosure.Real.IsNear.recentre' qz180 Bool.true 33471690 33554432 70867152 11093934080000 16735845 16777216 4429197 693370880000 

noncomputable abbrev qz183 := qz491

noncomputable def Ns348p1199 := @Enclosure.Real.IsNear.cos_image qz183 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 103057465) qz366) Bool.false 103057465 33554432 13 2097152 Bool.true 33471690 33554432 1 

noncomputable def Ns348p1200 := nat_lit 890540488639346509141692071 

noncomputable def Ns348p1201 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz172 884279719003555 140737488355328 1 500000000000000 16402105 33554432 33 33554432 14504048800466804483275 4722366482869645213696 Ns348p1200 

noncomputable def Ns348p1202 := @Enclosure.Real.IsNear.subLit_ff_p qz179 qz1 351946425 33554432 33 33554432 10 1 0 1 16402105 16402105 33554432 33 

noncomputable def Ns348p1203 := @Ns348p1202 33554432 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 351946425 33554432 33 33554432 351946425 33554432 33 33554432 (Ns348p1190 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns348p1204 := @Enclosure.Real.IsNear.recentre' qz183 Bool.false 14504048800466804483275 4722366482869645213696 Ns348p1200 Ns348p182 103057465 33554432 13 2097152 (@Ns348p1201 Ns348p182 RS349to360.d47 (Ns348p1203 rfl rfl) rfl) 

noncomputable def Ns348p1205 := nat_lit 7256241003823257008209920 

noncomputable def Ns348p1206 := nat_lit 2922759979824390759815821140949385156970056174269242850051770069457586234973991086879857835837593826824352731291344404221624403162646401361 

noncomputable def Ns348p1207 := nat_lit 1445382450319943578814587750231226432918565053199222063681293306187425671984157928762416487526726923009237609028936160980118043316561 

noncomputable def Ns348p1208 := nat_lit 14598673202460960849202571073251058747331397991285767450148666531561457394568159922262775890881199614203423166390241363940303038130987946321 

noncomputable def Ns348p1209 := BSN.sin_dyadic_bound_f 103117386683 68719476736 4 3 33554432 10590333 Ns348p1206 Ns348p785 Ns348p1207 Ns348p1208 Ns348p788 Ns348p1207 33471690 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 103117386683) qz379 0 3 Ns348p1206 Ns348p785 Ns348p1207 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 103117386683) qz380 0 3 Ns348p1208 Ns348p788 Ns348p1207 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1210 := @Ns348p1199 5290000 (Ns348p1204 rfl) (Enclosure.sfrac_false_div 103057465 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 103057465) qz366) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns348p1205) qz367) 226375608064910080 72057594037927936 Bool.false 33471690 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q1 103057465 33554432 226375608064910080 72057594037927936 0 Ns348p1205 Ns348p99 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33471690 33554432 Ns348p1205 Ns348p99 103117386683 68719476736 10590333 10580000 (Ns348p1209 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p1211 := @Enclosure.Real.IsNear.inv_image qz182 16735845 16777216 4429197 693370880000 16818581 16818797 16777216 (@Enclosure.Real.IsNear.neg qz180 Bool.true 16735845 16777216 4429197 693370880000 (Ns348p1198 (Ns348p1210 rfl rfl) rfl)) 

noncomputable def Ns348p1212 := Ns348p1196 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz182) Bool.false 16818689 16777216 27 4194304 (@Ns348p1197 27 4194304 (Ns348p1211 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p1213 := @Enclosure.Real.IsNear.recentre' qz181 Bool.true 6408190 16777216 

noncomputable abbrev qz184 := (@HMul.hMul Real Real Real qz349 qz346 qz492)

noncomputable def Ns348p1214 := @Enclosure.Real.IsNear.cos_image qz184 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 65857625)) qz366) Bool.true 65857625 33554432 

noncomputable def Ns348p1215 := nat_lit 311003841177622152024166426445 

noncomputable def Ns348p1216 := nat_lit 59095086853631219684744571759535333 

noncomputable def Ns348p1217 := @Enclosure.Real.IsNear.recentre' qz184 Bool.true Ns348p1215 Ns348p201 Ns348p1216 

noncomputable abbrev qz185 := qz492

noncomputable def Ns348p1218 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz185 884279719003555 140737488355328 1 500000000000000 351703012625999 

noncomputable abbrev qz493 := (@HSub.hSub Real Real Real qz587 qz686 qz679)

noncomputable abbrev qz186 := qz493

noncomputable def Ns348p1219 := @Enclosure.Real.IsNear.subLit_tf qz186 qz31 281334268448335 1125899906842624 2189836275 1125899906842624 1 16 

noncomputable abbrev qz494 := qz686

noncomputable abbrev qz187 := qz494

noncomputable def Ns348p1220 := @Enclosure.Real.IsNear.subLit_ff_n qz187 qz172 269029048431025 1125899906842624 1082540019 1125899906842624 16402105 33554432 33 33554432 

noncomputable def Ns348p1221 := @Enclosure.Real.IsNear.mulLit_ff qz172 qz172 16402105 33554432 33 33554432 16402105 33554432 33 33554432 269029048431025 1125899906842624 

noncomputable def Ns348p1222 := nat_lit 608657821708936422244866278465629039818402920160059961472061532763401865139043231777059332275390625 

noncomputable def Ns348p1223 := nat_lit 6656911422384141843317380851179644184080939093736075597884501525199753814376890659332275390625 

noncomputable def Ns348p1224 := nat_lit 3670936612280585616048620925125181627554741001808092780088279021893060252189536096534819332275390625 

noncomputable def Ns348p1225 := BSN.cos_dyadic_bound_t 65857625 33554432 4 3 16777216 5290000 Ns348p1222 Ns348p210 Ns348p1223 Ns348p1224 Ns348p213 Ns348p1223 6408190 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 65857625) (BSN.cosEvenQ 33554432) 0 3 Ns348p1222 Ns348p210 Ns348p1223 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 65857625) (BSN.cosOddQ 33554432) 0 3 Ns348p1224 Ns348p213 Ns348p1223 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1226 := @Ns348p1213 2207744432 177502945280000 3204095 8388608 137984027 11093934080000 (@Ns348p1214 411 33554432 Bool.true 6408190 16777216 1 5290000 (@Ns348p1217 Ns348p204 65857625 33554432 411 33554432 (@Ns348p1218 1125899906842624 2189836275 1125899906842624 Ns348p1215 Ns348p201 Ns348p1216 Ns348p204 RS349to360.d47 (@Ns348p1219 0 1 5627248202015984 351703012625999 1125899906842624 2189836275 1125899906842624 (@Ns348p1220 9440011579919402270720 281334268448335 1125899906842624 2189836275 1125899906842624 (@Ns348p1221 1082540019 1125899906842624 (Ns348p1203 rfl rfl) (Ns348p1203 rfl rfl) rfl) (Ns348p1203 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 65857625 33554432) (BSN.cos_neg_of_bound 65857625 33554432 Bool.true 6408190 16777216 1 5290000 (Ns348p1225 rfl rfl)) rfl rfl) 

noncomputable def Ns348p1227 := @Ns348p1188 1442846002718303880483 Ns348p74 (Ns348p1189 qz33 (@Enclosure.Real.IsNear.of_eq qz684 (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 10360639 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz171 (BSN.t_div_two_pi_nonneg qz170 691247 1000 qz173)) Ns348p1193) rfl) (@Ns348p1194 140737488355328 2778366228205519 186125328349921280000 (BSN.correction_mk qz172 (BSN.cos_two_pi_p_ne_zero_mk qz170 691247 1000 10 qz173 rfl rfl (@BSN.floor_sqrt_eq_dec qz170 691247 1000 10 qz173 rfl rfl rfl))) (@Ns348p1195 4194304 3204095 8388608 137984027 11093934080000 53888677331455 140737488355328 2778366228205519 186125328349921280000 Ns348p1212 (Ns348p1226 rfl) rfl)) 

noncomputable def Ns348p1228 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz170) (hardyZApproximantRS₀ qz170) Bool.true 17155998662820691977921 4722366482869645213696 363607836472599504520483 Ns348p74 (@Eq.refl Real (hardyZApproximantRS₀ qz170)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz170) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 10) (@HMul.hMul Real Real Real qz5 qz680 (Zeta.RiemannSiegel.correction qz172))) Bool.true 17155998662820691977921 4722366482869645213696 363607836472599504520483 Ns348p74 (BSN.hardyZApproximantRS₀_eq qz170 10 (@BSN.floor_sqrt_eq_dec qz170 691247 1000 10 qz173 rfl rfl rfl)) (@Ns348p1111 17155998662820691977921 4722366482869645213696 363607836472599504520483 Ns348p74 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 10)) Bool.true 14741699 4194304 155665 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz170) qz170 10) (Ns348p1187 (Ns348p1186 rfl rfl rfl rfl) rfl rfl)) (Ns348p1227 rfl) rfl rfl)) 

theorem RS349to360.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz170) Bool.true 17155998662820691977921 4722366482869645213696 363607836472599504520483 Ns348p74 := Ns348p1228 

noncomputable def Ns348p1229 := nat_lit 3203019472437163054271037440 

noncomputable abbrev qz779 := (Enclosure.sfrac Bool.false 692583 1000)

noncomputable abbrev qz687 := qz779

noncomputable abbrev qz495 := qz687

noncomputable abbrev qz188 := qz495

noncomputable abbrev qz780 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 692583 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz688 := qz780

noncomputable abbrev qz496 := qz688

noncomputable abbrev qz189 := qz496

noncomputable abbrev qz781 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 692583 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz689 := qz781

noncomputable abbrev qz497 := qz689

noncomputable abbrev qz190 := qz497

noncomputable abbrev qz690 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz189 qz9))

noncomputable def Ns348p1230 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 10) (@HMul.hMul Real Real Real qz5 qz690 (Zeta.RiemannSiegel.correction qz190)) 59260815 134217728 155971 134217728 8714622849081675365 73786976294838206464 186885087799448377003 Ns348p218 Ns348p1229 

noncomputable def Ns348p1231 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin BSN.quadSignPos 9 10 692583 1000 199 268435456 134217728 4503599627370496 Bool.false 344072320690 2497 618095470 52 84886744 8 

noncomputable def Ns348p1232 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 692583 1000 100 152 268435456 134217728 4503599627370496 Bool.false 344072320690 2497 

noncomputable def Ns348p1233 := Ns348p1232 558195838 52 94906264 8 589812974 52 89478488 8 Bool.true 23608586 117310 Bool.true 358884552 Bool.true 330189185 14148475504056880 1 Bool.false 62202321 Bool.false Bool.false 89708463 Bool.false Bool.false 28286077 

noncomputable def Ns348p1234 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 692583 1000 25 41 268435456 134217728 4503599627370496 Bool.false 344072320690 2497 

noncomputable def Ns348p1235 := Ns348p1234 480971758 52 109588312 8 522351262 52 101459064 8 Bool.false 187353645 87012 Bool.false 418021912 Bool.true 411328840 14148475504056880 1 Bool.false 268410837 Bool.true Bool.false 268236774 Bool.true Bool.true 23608586 

noncomputable def Ns348p1236 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 692583 1000 204 106 268435456 134217728 4503599627370496 Bool.false 344072320690 2497 

noncomputable def Ns348p1237 := Ns348p1236 372130544 51 134217720 8 432030192 51 120047984 16 Bool.false 238469660 51161 Bool.false 322916768 Bool.false 159866827 14148475504056880 1 Bool.false 96528999 Bool.false Bool.false 222221581 Bool.true Bool.false 187353645 

noncomputable def Ns348p1238 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 692583 1000 510 331 268435456 134217728 4503599627370496 Bool.false 344072320690 2497 

noncomputable def Ns348p1239 := Ns348p1238 186065264 51 189812528 16 294906480 51 154981288 8 Bool.false 268435416 2555 Bool.false 161393537 Bool.false 256497296 14148475504056880 1 Bool.false 221361562 Bool.true Bool.false 219209215 Bool.false Bool.false 238469660 

noncomputable def Ns348p1240 := nat_lit 159272678539526197389920450736850379426036323893413962757 

noncomputable def Ns348p1241 := nat_lit 124260021864949024661254376375118611471186060640256000 

noncomputable def Ns348p1242 := nat_lit 76489345889425871640973489508640000 

noncomputable def Ns348p1243 := nat_lit 317851401173510686803436268342030502720 

noncomputable abbrev qz691 := (@Eq.refl Real qz779)

noncomputable abbrev qz498 := qz691

noncomputable abbrev qz191 := qz498

noncomputable def Ns348p1244 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz188 692583 1000 1918685847556 16000000 1385166 4000 2000 Ns348p1242 Ns348p1243 qz191 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns348p1245 := nat_lit 458705314193835448482970898122129092746984612813032212740160 

noncomputable abbrev qz692 := (@HSub.hSub Real Real Real qz742 qz743 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz744 (@Nat.cast Real Real.instNatCast 1385166))))

noncomputable abbrev qz499 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 692583 4000) (Real.log (Enclosure.sfrac Bool.false 1918685847556 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz692))

noncomputable abbrev qz693 := (Enclosure.sfrac Bool.false 692583 2000)

noncomputable abbrev qz192 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz499 qz693) (@HMul.hMul Real Real Real qz349 qz693 (Real.log Real.pi)))

noncomputable def Ns348p1246 := @Enclosure.Real.IsNear.addLit_ft_p qz192 (Enclosure.sfrac Bool.true Ns348p1242 Ns348p1243) 1443144181902731086853 1125899906842624000 20148389026761197163 Ns348p523 Ns348p1242 Ns348p1243 0 1 Ns348p1245 

noncomputable def Ns348p1247 := nat_lit 96847766635701641736190164992000 

noncomputable abbrev qz193 := (@HSub.hSub Real Real Real qz353 qz499 qz693)

noncomputable def Ns348p1248 := @Enclosure.Real.IsNear.subLit_ff_p qz193 (@HMul.hMul Real Real Real qz5 qz693 (Real.log Real.pi)) 1889462420790157741061 1125899906842624000 2189323340571753 529000000000000000000 26602640085663 67108864000 692583 134217728000 Ns348p1247 1443144181902731086853 1125899906842624000 

noncomputable def Ns348p1249 := nat_lit 3778924841580315482122000 

noncomputable abbrev qz194 := qz499

noncomputable def Ns348p1250 := @Enclosure.Real.IsNear.subLit_ff_p qz194 qz693 2279351988380550269957 1125899906842624000 2189323340571753 529000000000000000000 692583 2000 0 1 Ns348p1249 1889462420790157741061 1125899906842624000 2189323340571753 529000000000000000000 

noncomputable def Ns348p1251 := nat_lit 5132644382758422662060067429428494336 

noncomputable def Ns348p1252 := nat_lit 56551433400139908682612736 

noncomputable def Ns348p1253 := nat_lit 8314599229627033293786023424794976702286201544746221557035771577768458112764174128137192280564999985334704034747747578817849285715621508969503472759203032105033490474725166966374400 

noncomputable def Ns348p1254 := nat_lit 251422767447032885139978982405058079101862638410312664618473193402897639412126128558817629714174169171794383901149853201160955399798764384135838123878251242078198946562956737904640 

noncomputable def Ns348p1255 := nat_lit 19266597293852021671584566645155145426678061540912395833420928366350293522042315754521291566074301863307796216761628437439908582100541986051429951785666189357467715984424960 

noncomputable def Ns348p1256 := BSN.log_dyadic_bound 870109847556 2967261847556 8 7 Ns348p1253 134217728 42320000 Ns348p1254 Ns348p1255 81095350 3837371695112 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 870109847556) (BSN.artanhQ 2967261847556) 0 7 Ns348p1254 Ns348p1253 Ns348p1255 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz500 := (Real.log (Enclosure.sfrac Bool.false 1918685847556 16000000))

noncomputable def Ns348p1257 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 692583 4000) qz500 692583 4000 0 1 3291726659525879 281474976710656 781250529 33062500000000000 2279793925034411855457 1125899906842624000 541080835126407 132250000000000000000 (Enclosure.Real.IsNear.const Bool.false 692583 4000) (BSN.isNear_log_sfrac 1918685847556 16000000 3291726659525879 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1918685847556) qz356)) Bool.false Ns348p1252 Ns348p99 1000000677120000 42320000000000000000000 3291726659525879 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 1918685847556 16000000 16 3837371695112 2097152000000 81095350 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns348p1256 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p1258 := BSN.arctan_dyadic_bound_f 1000 1385166 1 0 16777216 5290000 0 1 1 0 1 1 12112 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1385166) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1385166) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns348p1259 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1385166))) 884279719003555 562949953421312 1 2000000000000000 12112 16777216 1 5290000 14828933400306108071936 883873307723171 562949953421312 200000000529 1058000000000000000 qz17 (Ns348p1258 rfl) rfl rfl 

noncomputable abbrev qz501 := (@HMul.hMul Real Real Real qz583 qz588 qz692)

noncomputable abbrev qz195 := qz501

noncomputable abbrev qz502 := qz692

noncomputable abbrev qz196 := qz502

noncomputable def Ns348p1260 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 692583 4000) qz500) qz195 2279793925034411855457 1125899906842624000 541080835126407 132250000000000000000 883873307723171 2251799813685248 200000000529 4232000000000000000 Ns348p1251 2279351988380550269957 1125899906842624000 2189323340571753 529000000000000000000 (Ns348p1257 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz196 1 4 0 1 883873307723171 562949953421312 200000000529 1058000000000000000 883873307723171 2251799813685248 200000000529 4232000000000000000 qz364 Ns348p1259 rfl) 

noncomputable def Ns348p1261 := @Ns348p1246 Ns348p1240 Ns348p1241 20148389026761197163 Ns348p523 (@Ns348p1248 20148389026761197163 Ns348p523 (Ns348p1250 (Ns348p1260 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 692583 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz693 (Real.log Real.pi) 692583 2000 0 1 38410761 33554432 1 67108864 26602640085663 67108864000 692583 134217728000 (Enclosure.Real.IsNear.const Bool.false 692583 2000) RS349to360.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns348p1242 Ns348p1243) 

noncomputable def Ns348p1262 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz188) Bool.false Ns348p1240 Ns348p1241 20148389026761197163 Ns348p523 21504520043 16777216 313 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz188) (@HAdd.hAdd Real Real Real qz365 qz192 (Enclosure.sfrac Bool.true Ns348p1242 Ns348p1243)) Bool.false Ns348p1240 Ns348p1241 20148389026761197163 Ns348p523 Ns348p1244 (Ns348p1261 rfl rfl)) 

noncomputable def Ns348p1263 := nat_lit 3796684464341381122359296 

noncomputable def Ns348p1264 := nat_lit 3506139821186762339857871857943898899622993320864524859638402187355958501647490544905266624018833901801592537118910647327892188930649358336 

noncomputable def Ns348p1265 := nat_lit 2492621885446039326350077332792791058191851959758930340251605104881826167177125943173880731817403623274725546802937016499275391041536 

noncomputable def Ns348p1266 := nat_lit 17508944081292128512153831205644041840977508023122609519968250136778777796179645905692494549341710971434618575593910285537269679057373495296 

noncomputable def Ns348p1267 := BSN.sin_dyadic_bound_f 107908262644 68719476736 4 3 33554432 10590333 Ns348p1264 Ns348p785 Ns348p1265 Ns348p1266 Ns348p788 Ns348p1265 33554427 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107908262644) qz379 0 3 Ns348p1264 Ns348p785 Ns348p1265 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107908262644) qz380 0 3 Ns348p1266 Ns348p788 Ns348p1265 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1268 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz188) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21504520043) qz377) Bool.false 21504520043 16777216 313 33554432 Bool.false 33554427 33554432 1 5290000 (Ns348p1262 rfl) (Enclosure.sfrac_false_div 21504520043 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21504520043) qz377) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns348p1263) qz381) 226375608064910080 72057594037927936 Bool.false 33554427 33554432 203 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q3 21504520043 16777216 226375608064910080 72057594037927936 203 Ns348p1263 Ns348p188 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554427 33554432 Ns348p1263 Ns348p188 107908262644 68719476736 10590333 10580000 (Ns348p1267 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p1269 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz188) Bool.false Ns348p1240 Ns348p1241 20148389026761197163 Ns348p523 344072320690 268435456 2497 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz188) (@HAdd.hAdd Real Real Real qz365 qz192 (Enclosure.sfrac Bool.true Ns348p1242 Ns348p1243)) Bool.false Ns348p1240 Ns348p1241 20148389026761197163 Ns348p523 Ns348p1244 (Ns348p1261 rfl rfl)) 

noncomputable def Ns348p1270 := Ns348p1239 51161 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 510 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 221361562 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 331 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 219209215 268435456) qz191 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 1) Bool.false 33554427 33554432 105582777 11093934080000 268435416 268435456 2555 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz188)) Bool.false 33554427 33554432 105582777 11093934080000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz188) qz188) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz188)) Bool.false 33554427 33554432 1689324432 177502945280000 33554427 33554432 105582777 11093934080000 (Ns348p1268 rfl rfl) rfl)) rfl) (Ns348p1269 rfl) RS349to360.d7 

noncomputable def Ns348p1271 := nat_lit 5918983543433614052641196007410293027454567362023673947906800947584001 

noncomputable def Ns348p1272 := nat_lit 460351025966673442342216892528394881434458981715216604956445137921 

noncomputable def Ns348p1273 := nat_lit 17756029928248908811038903588445822292600833168107591410510489952476161 

noncomputable def Ns348p1274 := BSN.cos_dyadic_bound_f 161393537 268435456 3 2 268435456 134217728 Ns348p1271 Ns348p121 Ns348p1272 Ns348p1273 Ns348p124 Ns348p1272 221361562 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 161393537) qz368 0 2 Ns348p1271 Ns348p121 Ns348p1272 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 161393537) qz369 0 2 Ns348p1273 Ns348p124 Ns348p1272 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1275 := nat_lit 67981723575184452358460468329927785180131659226716194269119392576962560 

noncomputable def Ns348p1276 := nat_lit 18735372362217635336786897858760713477621627515918678634401613479936 

noncomputable def Ns348p1277 := nat_lit 178017037808325213338755952553277634316619148673040449987047473184505856 

noncomputable def Ns348p1278 := BSN.sin_dyadic_bound_f 256497296 268435456 3 2 268435456 134217728 Ns348p1275 Ns348p162 Ns348p1276 Ns348p1277 Ns348p165 Ns348p1276 219209215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 256497296) qz370 0 2 Ns348p1275 Ns348p162 Ns348p1276 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 256497296) qz371 0 2 Ns348p1277 Ns348p165 Ns348p1276 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1279 := nat_lit 5857984892405978522760003744041726996051102111821462589512206482203388891891344897591732005687587780801069056 

noncomputable def Ns348p1280 := nat_lit 1285544648922079014216503230141995529092118302559855870260378818021918641295273524881541971730996658176 

noncomputable def Ns348p1281 := nat_lit 35508939406151827162410074279423838868441967903389011320442083957577292922939628901808270049904518293503344640 

noncomputable def Ns348p1282 := BSN.cos_dyadic_bound_f 322916768 268435456 4 3 268435456 134217728 Ns348p1279 Ns348p146 Ns348p1280 Ns348p1281 Ns348p149 Ns348p1280 96528999 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 322916768) qz368 0 3 Ns348p1279 Ns348p146 Ns348p1280 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 322916768) qz369 0 3 Ns348p1281 Ns348p149 Ns348p1280 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1283 := nat_lit 5698161260848195114334868612484770583835313413875330852596837312632161 

noncomputable def Ns348p1284 := nat_lit 426645178599581567170838271497143410392800571807629549735590499681 

noncomputable def Ns348p1285 := nat_lit 17093630492187386179870264160911317464685154640482377298691040756897121 

noncomputable def Ns348p1286 := BSN.cos_dyadic_bound_f 159866827 268435456 3 2 268435456 134217728 Ns348p1283 Ns348p121 Ns348p1284 Ns348p1285 Ns348p124 Ns348p1284 222221581 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 159866827) qz368 0 2 Ns348p1283 Ns348p121 Ns348p1284 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 159866827) qz369 0 2 Ns348p1285 Ns348p124 Ns348p1284 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1287 := Ns348p1237 87012 BSN.abs_quadSignPos (BSN.cos_quad_nat0 204 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 96528999 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 106 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 222221581 268435456) qz191 rfl rfl (Ns348p1270 RS349to360.d9 RS349to360.d11 RS349to360.d13 RS349to360.d17 (Ns348p1274 rfl rfl) (Ns348p1278 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns348p1269 rfl) RS349to360.d19 RS349to360.d21 RS349to360.d23 RS349to360.d25 RS349to360.d17 (Ns348p1282 rfl rfl) (Ns348p1286 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns348p1288 := nat_lit 42801435422380453912998307027140039620923176698646891167426031197331980235435474153454323042774684780048941056 

noncomputable def Ns348p1289 := nat_lit 28470072180939836227133025849952127765516948650931325207200232478965971685342005531811735665030679494656 

noncomputable def Ns348p1290 := nat_lit 213750286652573712528154316654895987839832041460326402071573163369648857469373156347473872177736833443892822016 

noncomputable def Ns348p1291 := BSN.sin_dyadic_bound_f 418021912 268435456 4 3 268435456 134217728 Ns348p1288 Ns348p131 Ns348p1289 Ns348p1290 Ns348p134 Ns348p1289 268410837 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 418021912) qz370 0 3 Ns348p1288 Ns348p131 Ns348p1289 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 418021912) qz371 0 3 Ns348p1290 Ns348p134 Ns348p1289 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1292 := nat_lit 40120473177407647850522609622742450816849721937594636790611565310989133983359058695638431540603685070438400000 

noncomputable def Ns348p1293 := nat_lit 23456862901726061995082124316409448544152217742730886187420727451040621456339319829200633856000000000000 

noncomputable def Ns348p1294 := nat_lit 200376600767164074943548610754374639971804972834171655777847651344636527218851206649741180739929287688192000000 

noncomputable def Ns348p1295 := BSN.sin_dyadic_bound_f 411328840 268435456 4 3 268435456 134217728 Ns348p1292 Ns348p131 Ns348p1293 Ns348p1294 Ns348p134 Ns348p1293 268236774 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 411328840) qz370 0 3 Ns348p1292 Ns348p131 Ns348p1293 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 411328840) qz371 0 3 Ns348p1294 Ns348p134 Ns348p1293 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1296 := Ns348p1235 117310 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 25 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268410837 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 41 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 268236774 268435456) qz191 rfl rfl (Ns348p1287 rfl rfl) (Ns348p1269 rfl) RS349to360.d27 RS349to360.d29 RS349to360.d31 RS349to360.d33 RS349to360.d17 (Ns348p1291 rfl rfl) (Ns348p1295 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p1297 := nat_lit 8943122116390534161786937536676222465095391616126685317201167465122860278890894046434333759816586446740914176 

noncomputable def Ns348p1298 := nat_lit 4565172337914644602056671778735028063072525231740431157408408039793367413429222144733546943172256464896 

noncomputable def Ns348p1299 := nat_lit 54186262586592355656855877972357631946127046673276319707739729396323786144521423428912101801950240920861409280 

noncomputable def Ns348p1300 := BSN.cos_dyadic_bound_f 358884552 268435456 4 3 268435456 134217728 Ns348p1297 Ns348p146 Ns348p1298 Ns348p1299 Ns348p149 Ns348p1298 62202321 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 358884552) qz368 0 3 Ns348p1297 Ns348p146 Ns348p1298 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 358884552) qz369 0 3 Ns348p1299 Ns348p149 Ns348p1298 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1301 := nat_lit 6404535368618329949484177725068638648286857660572734633104396853038755140317920662231573789495718151436890625 

noncomputable def Ns348p1302 := nat_lit 1679399933298362045540172795003308101908028062695166643067115257065107936939589722877822249043212890625 

noncomputable def Ns348p1303 := nat_lit 38818924475413666342213162692142516272181128361245086945036296910934107587031551848833557453745333673638490625 

noncomputable def Ns348p1304 := BSN.cos_dyadic_bound_f 330189185 268435456 4 3 268435456 134217728 Ns348p1301 Ns348p146 Ns348p1302 Ns348p1303 Ns348p149 Ns348p1302 89708463 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 330189185) qz368 0 3 Ns348p1301 Ns348p146 Ns348p1302 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 330189185) qz369 0 3 Ns348p1303 Ns348p149 Ns348p1302 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1305 := Ns348p1233 143782 BSN.abs_quadSignPos (BSN.cos_quad_nat0 100 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 62202321 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 152 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 89708463 268435456) qz191 rfl rfl (Ns348p1296 rfl) (Ns348p1269 rfl) RS349to360.d35 RS349to360.d37 RS349to360.d39 RS349to360.d41 RS349to360.d17 (Ns348p1300 rfl rfl) (Ns348p1304 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p1306 := nat_lit 101068188381380533608094457921536 

noncomputable def Ns348p1307 := BSN.sin_dyadic_bound_f 100265984 268435456 2 1 268435456 134217728 Ns348p1306 Ns348p137 Ns348p1306 Ns348p1306 Ns348p138 Ns348p1306 97950723 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 100265984) qz370 0 1 Ns348p1306 Ns348p137 Ns348p1306 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 100265984) qz371 0 1 Ns348p1306 Ns348p138 Ns348p1306 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1308 := Ns348p1231 Bool.false 28286077 143782 Bool.true 100265984 14148475504056880 1 Bool.false 97950723 Bool.false Bool.false 59260815 155971 BSN.abs_quadSignPos qz372 (BSN.sfrac_eq_quadSignPos_mul Bool.false 97950723 268435456) qz191 rfl (Ns348p1305 rfl) (Ns348p1269 rfl) RS349to360.d43 RS349to360.d45 RS349to360.d17 (Ns348p1307 rfl rfl) rfl 

noncomputable def Ns348p1309 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 10) 59260815 268435456 155971 268435456 59260815 268435456 155971 268435456 31815407794913280 59260815 134217728 155971 134217728 (Ns348p1308 rfl rfl rfl rfl) 

noncomputable def Ns348p1310 := @Enclosure.Real.IsNear.mulLit_ff qz690 (Zeta.RiemannSiegel.correction qz190) 10355639 33554432 1 33554432 841534052035 2199023255552 720148310624633 46531332087480320000 8714622849081675365 73786976294838206464 

noncomputable abbrev qz694 := (@HPow.hPow Real Real Real qz7 qz189 qz9)

noncomputable def Ns348p1311 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz694 1 1 0 1 10355639 33554432 1 33554432 10355639 33554432 1 33554432 

noncomputable def Ns348p1312 := @Enclosure.Real.IsNear.sqrt_image qz189 3698637701799 33554432000 692583 33554432000 176143169 176143203 16777216 (@Enclosure.Real.IsNear.of_eq qz189 (@HMul.hMul Real Real Real qz5 qz188 qz3) Bool.false 3698637701799 33554432000 692583 33554432000 (BSN.t_div_two_pi_mk qz188 692583 1000 qz191) (@Enclosure.Real.IsNear.mulLit_ff qz188 qz3 692583 1000 0 1 5340353 33554432 1 33554432 3698637701799 33554432000 692583 33554432000 (Enclosure.Real.IsNear.const Bool.false 692583 1000) RS349to360.d48 rfl)) 

noncomputable abbrev qz782 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 692583 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz695 := qz782

noncomputable abbrev qz503 := qz695

noncomputable abbrev qz197 := qz503

noncomputable def Ns348p1313 := @Enclosure.Real.IsNear.sqrt_image qz197 88071593 8388608 17 16777216 54361677 54361683 16777216 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 352286372 33554432 34 33554432 88071593 8388608 17 16777216 (Ns348p1312 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns348p1314 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz197) 3397605 1048576 3 16777216 5177819 5177820 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz197) Bool.false 108723360 33554432 6 33554432 3397605 1048576 3 16777216 (Ns348p1313 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns348p1315 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz197)) Bool.false 10355639 33554432 1 33554432 10355639 33554432 1 33554432 (Ns348p1314 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz504 := (@HMul.hMul Real Real Real qz583 qz581 qz689)

noncomputable abbrev qz198 := (Real.cos qz504)

noncomputable abbrev qz696 := (@HMul.hMul Real Real Real qz738 qz781 qz781)

noncomputable abbrev qz505 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz696 qz689) qz602)

noncomputable abbrev qz199 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz505))

noncomputable def Ns348p1316 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz190) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz198) qz199) Bool.false 841534052035 

noncomputable def Ns348p1317 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz198) qz199 4194395 4194304 111 

noncomputable abbrev qz200 := (@Neg.neg Real Real.instNeg (Real.cos qz504))

noncomputable def Ns348p1318 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz198) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz200)) Bool.true 4194395 4194304 111 16777216 (BSN.inv_eq_neg_inv_neg qz198) 

noncomputable def Ns348p1319 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz200) Bool.false 33555160 33554432 222 33554432 4194395 4194304 

noncomputable def Ns348p1320 := @Enclosure.Real.IsNear.recentre' qz198 Bool.true 33553704 33554432 582807216 88751472640000 4194213 4194304 36425451 5546967040000 

noncomputable abbrev qz201 := qz504

noncomputable def Ns348p1321 := @Enclosure.Real.IsNear.cos_image qz201 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 105193415) qz366) Bool.false 105193415 33554432 107 16777216 Bool.true 33553704 33554432 1 

noncomputable def Ns348p1322 := nat_lit 458763282025655338545803831 

noncomputable def Ns348p1323 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz190 884279719003555 140737488355328 1 500000000000000 4185513 8388608 17 16777216 3701164259525726498715 1180591620717411303424 Ns348p1322 

noncomputable def Ns348p1324 := @Enclosure.Real.IsNear.subLit_ff_p qz197 qz1 88071593 8388608 17 16777216 10 1 0 1 4185513 4185513 8388608 17 

noncomputable def Ns348p1325 := @Ns348p1324 16777216 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 352286372 33554432 34 33554432 88071593 8388608 17 16777216 (Ns348p1312 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns348p1326 := @Enclosure.Real.IsNear.recentre' qz201 Bool.false 3701164259525726498715 1180591620717411303424 Ns348p1322 Ns348p477 105193415 33554432 107 16777216 (@Ns348p1323 Ns348p477 RS349to360.d47 (Ns348p1325 rfl rfl) rfl) 

noncomputable def Ns348p1327 := nat_lit 7564063839793881358008320 

noncomputable def Ns348p1328 := nat_lit 3452220966901826258458637339395590267426112960809879487561475566719470277759003757586525255348585382325398167902942317961501928958199271761 

noncomputable def Ns348p1329 := nat_lit 2379603617242312119117242243232752247004110232553306430701553602324735712816634850910270584937106727807319891493183792421798885658961 

noncomputable def Ns348p1330 := nat_lit 17240012628601629096375891857518892416957374536337936438279674964524780968629287531219339507828364734937691840412407906071225538114707984721 

noncomputable def Ns348p1331 := BSN.sin_dyadic_bound_f 107491812283 68719476736 4 3 33554432 10590333 Ns348p1328 Ns348p785 Ns348p1329 Ns348p1330 Ns348p788 Ns348p1329 33553704 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107491812283) qz379 0 3 Ns348p1328 Ns348p785 Ns348p1329 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107491812283) qz380 0 3 Ns348p1330 Ns348p788 Ns348p1329 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1332 := @Ns348p1321 5290000 (Ns348p1326 rfl) (Enclosure.sfrac_false_div 105193415 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 105193415) qz366) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns348p1327) qz367) 226375608064910080 72057594037927936 Bool.false 33553704 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q1 105193415 33554432 226375608064910080 72057594037927936 0 Ns348p1327 Ns348p99 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33553704 33554432 Ns348p1327 Ns348p99 107491812283 68719476736 10590333 10580000 (Ns348p1331 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p1333 := @Enclosure.Real.IsNear.inv_image qz200 4194213 4194304 36425451 5546967040000 16777469 16777691 16777216 (@Enclosure.Real.IsNear.neg qz198 Bool.true 4194213 4194304 36425451 5546967040000 (Ns348p1320 (Ns348p1332 rfl rfl) rfl)) 

noncomputable def Ns348p1334 := Ns348p1318 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz200) Bool.false 4194395 4194304 111 16777216 (@Ns348p1319 111 16777216 (Ns348p1333 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p1335 := @Enclosure.Real.IsNear.recentre' qz199 Bool.true 6420256 16777216 

noncomputable abbrev qz202 := (@HMul.hMul Real Real Real qz349 qz346 qz505)

noncomputable def Ns348p1336 := @Enclosure.Real.IsNear.cos_image qz202 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 65883741)) qz366) Bool.true 65883741 33554432 

noncomputable def Ns348p1337 := nat_lit 19445448326394893973239497645 

noncomputable def Ns348p1338 := nat_lit 15377417196098637913681780011440867 

noncomputable def Ns348p1339 := @Enclosure.Real.IsNear.recentre' qz202 Bool.true Ns348p1337 Ns348p734 Ns348p1338 

noncomputable abbrev qz203 := qz505

noncomputable def Ns348p1340 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz203 884279719003555 140737488355328 1 500000000000000 21990155273839 

noncomputable abbrev qz506 := (@HSub.hSub Real Real Real qz587 qz696 qz689)

noncomputable abbrev qz204 := qz506

noncomputable def Ns348p1341 := @Enclosure.Real.IsNear.subLit_tf qz204 qz31 17592108762735 70368744177664 569827845 281474976710656 1 16 

noncomputable abbrev qz507 := qz696

noncomputable abbrev qz205 := qz507

noncomputable def Ns348p1342 := @Enclosure.Real.IsNear.subLit_ff_n qz205 qz190 17518519073169 70368744177664 284615173 281474976710656 4185513 8388608 17 16777216 

noncomputable def Ns348p1343 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz190 4185513 8388608 17 16777216 4185513 8388608 17 16777216 17518519073169 70368744177664 

noncomputable def Ns348p1344 := nat_lit 609632347963777497554280798186473102511089413965900004710345655740943102841437806659626709357429361 

noncomputable def Ns348p1345 := nat_lit 6688658375544432551219315739979028276722105808078867246059196255890563455999977241275465466481 

noncomputable def Ns348p1346 := nat_lit 3676780104776220851911916323261823711715859563743742497062735453660191169573101364837111607330079345 

noncomputable def Ns348p1347 := BSN.cos_dyadic_bound_t 65883741 33554432 4 3 16777216 5290000 Ns348p1344 Ns348p210 Ns348p1345 Ns348p1346 Ns348p213 Ns348p1345 6420256 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 65883741) (BSN.cosEvenQ 33554432) 0 3 Ns348p1344 Ns348p210 Ns348p1345 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 65883741) (BSN.cosOddQ 33554432) 0 3 Ns348p1346 Ns348p213 Ns348p1345 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1348 := @Ns348p1335 574418608 44375736320000 200633 524288 35901163 2773483520000 (@Ns348p1336 107 8388608 Bool.true 6420256 16777216 1 5290000 (@Ns348p1339 Ns348p335 65883741 33554432 107 8388608 (@Ns348p1340 70368744177664 569827845 281474976710656 Ns348p1337 Ns348p734 Ns348p1338 Ns348p335 RS349to360.d47 (@Ns348p1341 0 1 351842484381424 21990155273839 70368744177664 569827845 281474976710656 (@Ns348p1342 147573304303948922880 17592108762735 70368744177664 569827845 281474976710656 (@Ns348p1343 284615173 281474976710656 (Ns348p1325 rfl rfl) (Ns348p1325 rfl rfl) rfl) (Ns348p1325 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 65883741 33554432) (BSN.cos_neg_of_bound 65883741 33554432 Bool.true 6420256 16777216 1 5290000 (Ns348p1347 rfl rfl)) rfl rfl) 

noncomputable def Ns348p1349 := @Ns348p1310 186885087799448377003 Ns348p218 (Ns348p1311 qz33 (@Enclosure.Real.IsNear.of_eq qz694 (@Inv.inv Real Real.instInv (Real.sqrt qz197)) Bool.false 10355639 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz189 (BSN.t_div_two_pi_nonneg qz188 692583 1000 qz191)) Ns348p1315) rfl) (@Ns348p1316 2199023255552 720148310624633 46531332087480320000 (BSN.correction_mk qz190 (BSN.cos_two_pi_p_ne_zero_mk qz188 692583 1000 10 qz191 rfl rfl (@BSN.floor_sqrt_eq_dec qz188 692583 1000 10 qz191 rfl rfl rfl))) (@Ns348p1317 16777216 200633 524288 35901163 2773483520000 841534052035 2199023255552 720148310624633 46531332087480320000 Ns348p1334 (Ns348p1348 rfl) rfl)) 

noncomputable def Ns348p1350 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz188) (hardyZApproximantRS₀ qz188) Bool.false 23864354732909523355 73786976294838206464 45546500069151904569003 Ns348p218 (@Eq.refl Real (hardyZApproximantRS₀ qz188)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz188) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 10) (@HMul.hMul Real Real Real qz5 qz690 (Zeta.RiemannSiegel.correction qz190))) Bool.false 23864354732909523355 73786976294838206464 45546500069151904569003 Ns348p218 (BSN.hardyZApproximantRS₀_eq qz188 10 (@BSN.floor_sqrt_eq_dec qz188 692583 1000 10 qz191 rfl rfl rfl)) (@Ns348p1230 23864354732909523355 73786976294838206464 45546500069151904569003 Ns348p218 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 10)) Bool.false 59260815 134217728 155971 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz188) qz188 10) (Ns348p1309 (Ns348p1308 rfl rfl rfl rfl) rfl rfl)) (Ns348p1349 rfl) rfl rfl)) 

theorem RS349to360.d60 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz188) Bool.false 23864354732909523355 73786976294838206464 45546500069151904569003 Ns348p218 := Ns348p1350 

noncomputable def Ns348p1351 := nat_lit 6416029247550191151072935936 

noncomputable abbrev qz783 := (Enclosure.sfrac Bool.false 693919 1000)

noncomputable abbrev qz697 := qz783

noncomputable abbrev qz508 := qz697

noncomputable abbrev qz206 := qz508

noncomputable abbrev qz784 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 693919 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz698 := qz784

noncomputable abbrev qz509 := qz698

noncomputable abbrev qz207 := qz509

noncomputable abbrev qz785 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 693919 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz699 := qz785

noncomputable abbrev qz510 := qz699

noncomputable abbrev qz208 := qz510

noncomputable abbrev qz700 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz207 qz9))

noncomputable def Ns348p1352 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 10) (@HMul.hMul Real Real Real qz5 qz700 (Zeta.RiemannSiegel.correction qz208)) 2469637 2097152 156275 134217728 278837085114870144255 2361183241434822606848 3771660026626536144177 Ns348p748 Ns348p1351 

noncomputable def Ns348p1353 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin BSN.quadSignPos 9 10 693919 1000 199 268435456 134217728 4503599627370496 Bool.false 344915730975 2502 618095470 52 84886744 8 

noncomputable def Ns348p1354 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 693919 1000 100 152 268435456 134217728 4503599627370496 Bool.false 344915730975 2502 

noncomputable def Ns348p1355 := Ns348p1354 558195838 52 94906264 8 589812974 52 89478488 8 Bool.true 283736760 117539 Bool.true 261223907 Bool.true 274769033 14148475504056880 1 Bool.false 151051539 Bool.false Bool.false 139666900 Bool.false Bool.true 183776343 

noncomputable def Ns348p1356 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 693919 1000 26 41 268435456 134217728 4503599627370496 Bool.false 344915730975 2502 

noncomputable def Ns348p1357 := Ns348p1356 480971758 52 109588312 8 522351262 52 101459064 8 Bool.true 117584062 87183 Bool.false 197196500 Bool.true 265779841 14148475504056880 1 Bool.false 199203107 Bool.true Bool.false 224434782 Bool.true Bool.true 283736760 

noncomputable def Ns348p1358 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 693919 1000 205 107 268435456 134217728 4503599627370496 Bool.false 344915730975 2502 

noncomputable def Ns348p1359 := Ns348p1358 372130544 51 134217720 8 432030192 51 120047984 16 Bool.true 12615966 51263 Bool.false 247503218 Bool.false 4427348 14148475504056880 1 Bool.false 213895964 Bool.true Bool.false 4427147 Bool.false Bool.true 117584062 

noncomputable def Ns348p1360 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 693919 1000 511 332 268435456 134217728 4503599627370496 Bool.false 344915730975 2502 

noncomputable def Ns348p1361 := Ns348p1360 186065264 51 189812528 16 294906480 51 154981288 8 Bool.true 268435448 2563 Bool.false 334563201 Bool.false 284255095 14148475504056880 1 Bool.false 254430049 Bool.false Bool.false 131480445 Bool.false Bool.true 12615966 

noncomputable def Ns348p1362 := nat_lit 1453679835955345991097661600186058718704812044813572180773 

noncomputable def Ns348p1363 := nat_lit 1131346513362008563356634057846013971861610793271296000 

noncomputable def Ns348p1364 := nat_lit 77229941047831096513309977087520000 

noncomputable def Ns348p1365 := nat_lit 321548018678756921916781851065824745280 

noncomputable abbrev qz786 := (@Eq.refl Real (Enclosure.sfrac Bool.false 693919 1000))

noncomputable abbrev qz701 := qz786

noncomputable abbrev qz511 := qz701

noncomputable abbrev qz209 := qz511

noncomputable def Ns348p1366 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz206 693919 1000 1926095314244 16000000 1387838 4000 2000 Ns348p1364 Ns348p1365 qz209 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns348p1367 := nat_lit 465177547505710717151251712059538789985539854340343097847360 

noncomputable abbrev qz702 := (@HSub.hSub Real Real Real qz742 qz743 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz744 (@Nat.cast Real Real.instNatCast 1387838))))

noncomputable abbrev qz512 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 693919 4000) (Real.log (Enclosure.sfrac Bool.false 1926095314244 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz702))

noncomputable abbrev qz703 := (Enclosure.sfrac Bool.false 693919 2000)

noncomputable abbrev qz210 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz512 qz703) (@HMul.hMul Real Real Real qz349 qz703 (Real.log Real.pi)))

noncomputable def Ns348p1368 := @Enclosure.Real.IsNear.addLit_ft_p qz210 (Enclosure.sfrac Bool.true Ns348p1364 Ns348p1365) 1446681700513386247437 1125899906842624000 20187057953574865859 Ns348p523 Ns348p1364 Ns348p1365 0 1 Ns348p1367 

noncomputable def Ns348p1369 := nat_lit 97085165491041567858719981568000 

noncomputable abbrev qz211 := (@HSub.hSub Real Real Real qz353 qz512 qz703)

noncomputable def Ns348p1370 := @Enclosure.Real.IsNear.subLit_ff_p qz211 (@HMul.hMul Real Real Real qz5 qz703 (Real.log Real.pi)) 1893860892047865459981 1125899906842624000 2193498343398729 529000000000000000000 26653956862359 67108864000 693919 134217728000 Ns348p1369 1446681700513386247437 1125899906842624000 

noncomputable def Ns348p1371 := nat_lit 3787721784095730919962000 

noncomputable abbrev qz212 := qz512

noncomputable def Ns348p1372 := @Enclosure.Real.IsNear.subLit_ff_p qz212 qz703 2284502560776028861709 1125899906842624000 2193498343398729 529000000000000000000 693919 2000 0 1 Ns348p1371 1893860892047865459981 1125899906842624000 2193498343398729 529000000000000000000 

noncomputable def Ns348p1373 := nat_lit 5144242440718933736445581285845368832 

noncomputable def Ns348p1374 := nat_lit 56570071673298571046682624 

noncomputable def Ns348p1375 := nat_lit 8610034685489416164559387264373087003857058723545945174105191218344560794015740090934531590518540268965072520548145661226137260325919833092784838686043234711143103063448265057894400 

noncomputable def Ns348p1376 := nat_lit 263668328179826928346597053157884378564892772127723790619791198788723819837700696059381111806533190812425453170725047035668165109443459330753516737827166620401586741610417896816640 

noncomputable def Ns348p1377 := nat_lit 21695088355735859853663264473287685244258166798165809426046638268860713777689332229330792543099002487375658153171757898113120313897544882544845856525097566284948240817192960 

noncomputable def Ns348p1378 := BSN.log_dyadic_bound 877519314244 2974671314244 8 7 Ns348p1375 134217728 42320000 Ns348p1376 Ns348p1377 81612666 3852190628488 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 877519314244) (BSN.artanhQ 2974671314244) 0 7 Ns348p1376 Ns348p1375 Ns348p1377 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz513 := (Real.log (Enclosure.sfrac Bool.false 1926095314244 16000000))

noncomputable def Ns348p1379 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 693919 4000) qz513 693919 4000 0 1 3292811549809911 281474976710656 781250529 33062500000000000 2284944497832543631209 1125899906842624000 542124585833151 132250000000000000000 (Enclosure.Real.IsNear.const Bool.false 693919 4000) (BSN.isNear_log_sfrac 1926095314244 16000000 3292811549809911 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1926095314244) qz356)) Bool.false Ns348p1374 Ns348p99 1000000677120000 42320000000000000000000 3292811549809911 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 1926095314244 16000000 16 3852190628488 2097152000000 81612666 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns348p1378 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p1380 := BSN.arctan_dyadic_bound_f 1000 1387838 1 0 16777216 5290000 0 1 1 0 1 1 12088 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1387838) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1387838) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns348p1381 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1387838))) 884279719003555 562949953421312 1 2000000000000000 12088 16777216 1 5290000 14828946911104990183424 883874113029539 562949953421312 200000000529 1058000000000000000 qz17 (Ns348p1380 rfl) rfl rfl 

noncomputable abbrev qz514 := (@HMul.hMul Real Real Real qz583 qz588 qz702)

noncomputable abbrev qz213 := qz514

noncomputable abbrev qz515 := qz702

noncomputable abbrev qz214 := qz515

noncomputable def Ns348p1382 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 693919 4000) qz513) qz213 2284944497832543631209 1125899906842624000 542124585833151 132250000000000000000 883874113029539 2251799813685248 200000000529 4232000000000000000 Ns348p1373 2284502560776028861709 1125899906842624000 2193498343398729 529000000000000000000 (Ns348p1379 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz214 1 4 0 1 883874113029539 562949953421312 200000000529 1058000000000000000 883874113029539 2251799813685248 200000000529 4232000000000000000 qz364 Ns348p1381 rfl) 

noncomputable def Ns348p1383 := @Ns348p1368 Ns348p1362 Ns348p1363 20187057953574865859 Ns348p523 (@Ns348p1370 20187057953574865859 Ns348p523 (Ns348p1372 (Ns348p1382 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 693919 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz703 (Real.log Real.pi) 693919 2000 0 1 38410761 33554432 1 67108864 26653956862359 67108864000 693919 134217728000 (Enclosure.Real.IsNear.const Bool.false 693919 2000) RS349to360.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns348p1364 Ns348p1365) 

noncomputable def Ns348p1384 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz206) Bool.false Ns348p1362 Ns348p1363 20187057953574865859 Ns348p523 43114466371 33554432 157 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz206) (@HAdd.hAdd Real Real Real qz365 qz210 (Enclosure.sfrac Bool.true Ns348p1364 Ns348p1365)) Bool.false Ns348p1362 Ns348p1363 20187057953574865859 Ns348p523 Ns348p1366 (Ns348p1383 rfl rfl)) 

noncomputable def Ns348p1385 := nat_lit 7595087925051191294164992 

noncomputable def Ns348p1386 := nat_lit 3509322179772820421923233691240672119052636034991216439034358674073137865588985483638191051758506720371870931445262037007311815009051344896 

noncomputable def Ns348p1387 := nat_lit 2499401717323260870785081041155780001457038384157940658504006723275426349796268108157622722341398543731534048159185150795763622608896 

noncomputable def Ns348p1388 := nat_lit 17524816434504415768442071034897290208524698390631742736469872548748262612796702605493524077278091225203731644250921720540541933749908013056 

noncomputable def Ns348p1389 := BSN.sin_dyadic_bound_f 107932691052 68719476736 4 3 33554432 10590333 Ns348p1386 Ns348p785 Ns348p1387 Ns348p1388 Ns348p788 Ns348p1387 33554431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107932691052) qz379 0 3 Ns348p1386 Ns348p785 Ns348p1387 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107932691052) qz380 0 3 Ns348p1388 Ns348p788 Ns348p1387 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1390 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz206) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 43114466371) qz366) Bool.false 43114466371 33554432 157 16777216 Bool.true 33554431 33554432 1 5290000 (Ns348p1384 rfl) (Enclosure.sfrac_false_div 43114466371 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 43114466371) qz366) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns348p1385) qz367) 226375608064910080 72057594037927936 Bool.false 33554431 33554432 204 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q1 43114466371 33554432 226375608064910080 72057594037927936 204 Ns348p1385 Ns348p99 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554431 33554432 Ns348p1385 Ns348p99 107932691052 68719476736 10590333 10580000 (Ns348p1389 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p1391 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz206) Bool.false Ns348p1362 Ns348p1363 20187057953574865859 Ns348p523 344915730975 268435456 2502 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz206) (@HAdd.hAdd Real Real Real qz365 qz210 (Enclosure.sfrac Bool.true Ns348p1364 Ns348p1365)) Bool.false Ns348p1362 Ns348p1363 20187057953574865859 Ns348p523 Ns348p1366 (Ns348p1383 rfl rfl)) 

noncomputable def Ns348p1392 := Ns348p1361 51263 BSN.abs_quadSignPos (BSN.cos_quad_nat3 511 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 254430049 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 332 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 131480445 268435456) qz209 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 1) Bool.true 33554431 33554432 52956701 5546967040000 268435448 268435456 2563 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz206)) Bool.true 33554431 33554432 52956701 5546967040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz206) qz206) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz206)) Bool.true 33554431 33554432 847307216 88751472640000 33554431 33554432 52956701 5546967040000 (Ns348p1390 rfl rfl) rfl)) rfl) (Ns348p1391 rfl) RS349to360.d7 

noncomputable def Ns348p1393 := nat_lit 17541924367342270814834856645186307198294264847532564905281293544080584921378981001999269434253389048799091201 

noncomputable def Ns348p1394 := nat_lit 1966699685381436023920081599397447763087189363692862689933368339225279564252338327670392988365394598401 

noncomputable def Ns348p1395 := nat_lit 87666383655385804461544935858179801116860871288819693530883632242785150450305507988229423872385533338264066561 

noncomputable def Ns348p1396 := BSN.sin_dyadic_bound_f 334563201 268435456 4 3 268435456 134217728 Ns348p1393 Ns348p131 Ns348p1394 Ns348p1395 Ns348p134 Ns348p1394 254430049 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 334563201) qz370 0 3 Ns348p1393 Ns348p131 Ns348p1394 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 334563201) qz371 0 3 Ns348p1395 Ns348p134 Ns348p1394 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1397 := nat_lit 3515626615146424191606598435312057426119960553063562287702098173809343175764309970183055972162679788164390625 

noncomputable def Ns348p1398 := nat_lit 278290956125340358244331099583254002770610839565225317097971756986270162282420033039737669472900390625 

noncomputable def Ns348p1399 := nat_lit 21317499284845750464947218726684626317342220471524367489767791846660157604048593896515120715873588636701990625 

noncomputable def Ns348p1400 := BSN.cos_dyadic_bound_f 284255095 268435456 4 3 268435456 134217728 Ns348p1397 Ns348p146 Ns348p1398 Ns348p1399 Ns348p149 Ns348p1398 131480445 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 284255095) qz368 0 3 Ns348p1397 Ns348p146 Ns348p1398 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 284255095) qz369 0 3 Ns348p1399 Ns348p149 Ns348p1398 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1401 := nat_lit 58934347718711564735289506885060700068689281069812178186862612490010880 

noncomputable def Ns348p1402 := nat_lit 14081431261552197856648833983134224698059253486577856764848622059776 

noncomputable def Ns348p1403 := nat_lit 154329064565059204081609372301091044768484592581958388245116134942884096 

noncomputable def Ns348p1404 := BSN.sin_dyadic_bound_f 247503218 268435456 3 2 268435456 134217728 Ns348p1401 Ns348p162 Ns348p1402 Ns348p1403 Ns348p165 Ns348p1402 213895964 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 247503218) qz370 0 2 Ns348p1401 Ns348p162 Ns348p1402 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 247503218) qz371 0 2 Ns348p1403 Ns348p165 Ns348p1402 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1405 := BSN.sin_dyadic_bound_f 4427348 268435456 1 0 268435456 134217728 0 1 1 0 1 1 4427147 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 4427348) qz370 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 4427348) qz371 0 0 rfl) rfl rfl 

noncomputable def Ns348p1406 := Ns348p1359 87183 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 205 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 213895964 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 107 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 4427147 268435456) qz209 rfl rfl (Ns348p1392 RS349to360.d9 RS349to360.d11 RS349to360.d13 RS349to360.d17 (Ns348p1396 rfl rfl) (Ns348p1400 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns348p1391 rfl) RS349to360.d19 RS349to360.d21 RS349to360.d23 RS349to360.d25 RS349to360.d17 (Ns348p1404 rfl rfl) (Ns348p1405 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns348p1407 := nat_lit 13192918668660754662163671597515347905681522653341628408080000000000000 

noncomputable def Ns348p1408 := nat_lit 2286618009881450858673338848041428587925043753906250000000000000000 

noncomputable def Ns348p1409 := nat_lit 39574182769962501084773668114849960859868717872517072724240000000000000 

noncomputable def Ns348p1410 := BSN.cos_dyadic_bound_f 197196500 268435456 3 2 268435456 134217728 Ns348p1407 Ns348p121 Ns348p1408 Ns348p1409 Ns348p124 Ns348p1408 199203107 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 197196500) qz368 0 2 Ns348p1407 Ns348p121 Ns348p1408 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 197196500) qz369 0 2 Ns348p1409 Ns348p124 Ns348p1408 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1411 := nat_lit 78373175713241497839611147779934657883031451472861143096234186776433665 

noncomputable def Ns348p1412 := nat_lit 24898678540992107720214790978564573628296633913779094891192950379521 

noncomputable def Ns348p1413 := nat_lit 205222767102756602357910753571577856574446083116871161003170462494807041 

noncomputable def Ns348p1414 := BSN.sin_dyadic_bound_f 265779841 268435456 3 2 268435456 134217728 Ns348p1411 Ns348p162 Ns348p1412 Ns348p1413 Ns348p165 Ns348p1412 224434782 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 265779841) qz370 0 2 Ns348p1411 Ns348p162 Ns348p1412 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 265779841) qz371 0 2 Ns348p1413 Ns348p165 Ns348p1412 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1415 := Ns348p1357 117539 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 26 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 199203107 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 41 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 224434782 268435456) qz209 rfl rfl (Ns348p1406 rfl rfl) (Ns348p1391 rfl) RS349to360.d27 RS349to360.d29 RS349to360.d31 RS349to360.d33 RS349to360.d17 (Ns348p1410 rfl rfl) (Ns348p1414 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p1416 := nat_lit 40639863982530818633217330445715474620115513050964315072784611272363681 

noncomputable def Ns348p1417 := nat_lit 21682200973553789696732923515044415395495708370471383709805276106401 

noncomputable def Ns348p1418 := nat_lit 121876227545645348320258525490116335029555547736152002450934223264878241 

noncomputable def Ns348p1419 := BSN.cos_dyadic_bound_f 261223907 268435456 3 2 268435456 134217728 Ns348p1416 Ns348p121 Ns348p1417 Ns348p1418 Ns348p124 Ns348p1417 151051539 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 261223907) qz368 0 2 Ns348p1416 Ns348p121 Ns348p1417 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 261223907) qz369 0 2 Ns348p1418 Ns348p124 Ns348p1417 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1420 := nat_lit 3069019225985649370453090618765436533083248316440801911006825123207203402264993778283338308114475384595939041 

noncomputable def Ns348p1421 := nat_lit 185188248356062280501330347528081683098276891464807112783698577193273821999952387454472973564190260961 

noncomputable def Ns348p1422 := nat_lit 18610610249719800775050839134364209865637173758959609395225782549315809101183129628351308089104330205659266785 

noncomputable def Ns348p1423 := BSN.cos_dyadic_bound_f 274769033 268435456 4 3 268435456 134217728 Ns348p1420 Ns348p146 Ns348p1421 Ns348p1422 Ns348p149 Ns348p1421 139666900 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 274769033) qz368 0 3 Ns348p1420 Ns348p146 Ns348p1421 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 274769033) qz369 0 3 Ns348p1422 Ns348p149 Ns348p1421 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1424 := Ns348p1355 144063 BSN.abs_quadSignPos (BSN.cos_quad_nat0 100 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 151051539 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 152 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 139666900 268435456) qz209 rfl rfl (Ns348p1415 rfl) (Ns348p1391 rfl) RS349to360.d35 RS349to360.d37 RS349to360.d39 RS349to360.d41 RS349to360.d17 (Ns348p1419 rfl rfl) (Ns348p1423 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p1425 := nat_lit 46620529974596363604167752650256 

noncomputable def Ns348p1426 := BSN.sin_dyadic_bound_f 82631246 268435456 2 1 268435456 134217728 Ns348p1425 Ns348p137 Ns348p1425 Ns348p1425 Ns348p138 Ns348p1425 81332440 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 82631246) qz370 0 1 Ns348p1425 Ns348p137 Ns348p1425 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 82631246) qz371 0 1 Ns348p1425 Ns348p138 Ns348p1425 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1427 := Ns348p1353 Bool.true 183776343 144063 Bool.true 82631246 14148475504056880 1 Bool.false 81332440 Bool.false Bool.true 158056768 156275 BSN.abs_quadSignPos qz372 (BSN.sfrac_eq_quadSignPos_mul Bool.false 81332440 268435456) qz209 rfl (Ns348p1424 rfl) (Ns348p1391 rfl) RS349to360.d43 RS349to360.d45 RS349to360.d17 (Ns348p1426 rfl rfl) rfl 

noncomputable def Ns348p1428 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 10) 158056768 268435456 156275 268435456 158056768 268435456 156275 268435456 84856081183932416 2469637 2097152 156275 134217728 (Ns348p1427 rfl rfl rfl rfl) 

noncomputable def Ns348p1429 := @Enclosure.Real.IsNear.mulLit_ff qz700 (Zeta.RiemannSiegel.correction qz208) 10350651 33554432 1 33554432 26939086741005 70368744177664 363528142098951 23265666043740160000 278837085114870144255 2361183241434822606848 

noncomputable abbrev qz704 := (@HPow.hPow Real Real Real qz7 qz207 qz9)

noncomputable def Ns348p1430 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz704 1 1 0 1 10350651 33554432 1 33554432 10350651 33554432 1 33554432 

noncomputable def Ns348p1431 := @Enclosure.Real.IsNear.sqrt_image qz207 3705772413407 33554432000 693919 33554432000 176312978 176313012 16777216 (@Enclosure.Real.IsNear.of_eq qz207 (@HMul.hMul Real Real Real qz5 qz206 qz3) Bool.false 3705772413407 33554432000 693919 33554432000 (BSN.t_div_two_pi_mk qz206 693919 1000 qz209) (@Enclosure.Real.IsNear.mulLit_ff qz206 qz3 693919 1000 0 1 5340353 33554432 1 33554432 3705772413407 33554432000 693919 33554432000 (Enclosure.Real.IsNear.const Bool.false 693919 1000) RS349to360.d48 rfl)) 

noncomputable abbrev qz787 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 693919 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz705 := qz787

noncomputable abbrev qz516 := qz705

noncomputable abbrev qz215 := qz516

noncomputable def Ns348p1432 := @Enclosure.Real.IsNear.sqrt_image qz215 176312995 16777216 17 16777216 54387874 54387880 16777216 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 352625990 33554432 34 33554432 176312995 16777216 17 16777216 (Ns348p1431 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns348p1433 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz215) 54387877 16777216 3 16777216 5175325 5175326 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz215) Bool.false 108775754 33554432 6 33554432 54387877 16777216 3 16777216 (Ns348p1432 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns348p1434 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 10350651 33554432 1 33554432 10350651 33554432 1 33554432 (Ns348p1433 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz216 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz510))

noncomputable abbrev qz706 := (@HMul.hMul Real Real Real qz738 qz785 qz785)

noncomputable abbrev qz517 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz706 qz699) qz602)

noncomputable abbrev qz217 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz517))

noncomputable def Ns348p1435 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz208) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz216) qz217) Bool.false 26939086741005 

noncomputable def Ns348p1436 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz216) qz217 33609035 33554432 223 

noncomputable abbrev qz707 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz216))

noncomputable def Ns348p1437 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz216) (@Neg.neg Real Real.instNeg qz707) Bool.true 33609035 33554432 223 33554432 (BSN.inv_eq_neg_inv_neg qz216) 

noncomputable def Ns348p1438 := @Enclosure.Real.IsNear.recentre' qz707 Bool.false 33609035 33554432 223 33554432 33609035 33554432 

noncomputable def Ns348p1439 := @Enclosure.Real.IsNear.recentre' qz216 Bool.true 33499918 33554432 1170904432 177502945280000 16749959 16777216 73181527 11093934080000 

noncomputable abbrev qz218 := (@HMul.hMul Real Real Real qz349 qz346 qz510)

noncomputable def Ns348p1440 := @Enclosure.Real.IsNear.cos_image qz218 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 107327297) qz366) Bool.false 107327297 33554432 215 33554432 Bool.true 33499918 33554432 1 

noncomputable def Ns348p1441 := nat_lit 458763282027113986748936759 

noncomputable def Ns348p1442 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz208 884279719003555 140737488355328 1 500000000000000 8540835 16777216 17 16777216 7552487173855727668425 2361183241434822606848 Ns348p1441 

noncomputable def Ns348p1443 := @Enclosure.Real.IsNear.subLit_ff_p qz215 qz1 176312995 16777216 17 16777216 10 1 0 1 8540835 8540835 16777216 17 

noncomputable def Ns348p1444 := @Ns348p1443 16777216 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 352625990 33554432 34 33554432 176312995 16777216 17 16777216 (Ns348p1431 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns348p1445 := @Enclosure.Real.IsNear.recentre' qz218 Bool.false 7552487173855727668425 2361183241434822606848 Ns348p1441 Ns348p477 107327297 33554432 215 33554432 (@Ns348p1442 Ns348p477 RS349to360.d47 (Ns348p1444 rfl rfl) rfl) 

noncomputable def Ns348p1446 := nat_lit 235572799081700664232709224586674031521 

noncomputable def Ns348p1447 := nat_lit 535217884764734955396857238543560676143529984 

noncomputable def Ns348p1448 := nat_lit 8028268271471024330952858578153410142152949760 

noncomputable def Ns348p1449 := BSN.cos_dyadic_bound_f 3917700983 68719476736 2 1 33554432 10590333 Ns348p1446 Ns348p1447 Ns348p1446 Ns348p1446 Ns348p1448 Ns348p1446 33499918 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 3917700983) qz594 0 1 Ns348p1446 Ns348p1447 Ns348p1446 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 3917700983) qz595 0 1 Ns348p1446 Ns348p1448 Ns348p1446 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1450 := @Ns348p1440 5290000 (Ns348p1445 rfl) (Enclosure.sfrac_false_div 107327297 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 107327297) qz366) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 275683698282887972388864) qz367) 226375608064910080 72057594037927936 Bool.false 33499918 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q2 107327297 33554432 226375608064910080 72057594037927936 0 275683698282887972388864 Ns348p99 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33499918 33554432 275683698282887972388864 Ns348p99 3917700983 68719476736 10590333 10580000 (Ns348p1449 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p1451 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz216) 16749959 16777216 73181527 11093934080000 16804406 16804629 16777216 (@Enclosure.Real.IsNear.neg qz216 Bool.true 16749959 16777216 73181527 11093934080000 (Ns348p1439 (Ns348p1450 rfl rfl) rfl)) 

noncomputable def Ns348p1452 := Ns348p1437 (@Enclosure.Real.IsNear.neg qz707 Bool.false 33609035 33554432 223 33554432 (@Ns348p1438 223 33554432 (Ns348p1451 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p1453 := @Enclosure.Real.IsNear.recentre' qz217 Bool.true 6412344 16777216 

noncomputable abbrev qz219 := (@HMul.hMul Real Real Real qz349 qz346 qz517)

noncomputable def Ns348p1454 := @Enclosure.Real.IsNear.cos_image qz219 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8233327)) qz625) Bool.true 8233327 4194304 

noncomputable def Ns348p1455 := nat_lit 77761575193503454329881868805 

noncomputable def Ns348p1456 := nat_lit 15533221464389009764694159940338609 

noncomputable def Ns348p1457 := @Enclosure.Real.IsNear.recentre' qz219 Bool.true Ns348p1455 Ns348p493 Ns348p1456 

noncomputable abbrev qz220 := qz517

noncomputable def Ns348p1458 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz220 884279719003555 140737488355328 1 500000000000000 87937757162551 

noncomputable abbrev qz518 := (@HSub.hSub Real Real Real qz587 qz706 qz699)

noncomputable abbrev qz221 := qz518

noncomputable def Ns348p1459 := @Enclosure.Real.IsNear.subLit_tf qz221 qz31 70345571118135 281474976710656 575601351 281474976710656 1 16 

noncomputable abbrev qz519 := qz706

noncomputable abbrev qz222 := qz519

noncomputable def Ns348p1460 := @Enclosure.Real.IsNear.subLit_ff_n qz222 qz208 72945862497225 281474976710656 290388679 281474976710656 8540835 16777216 17 16777216 

noncomputable def Ns348p1461 := @Enclosure.Real.IsNear.mulLit_ff qz208 qz208 8540835 16777216 17 16777216 8540835 16777216 17 16777216 72945862497225 281474976710656 

noncomputable def Ns348p1462 := nat_lit 8862017270566836368729853660592181610519089834849855849905734332360157190005579525624001 

noncomputable def Ns348p1463 := nat_lit 97029629621037671810766276979185004690984881303525821410849427566865912093861449921 

noncomputable def Ns348p1464 := nat_lit 53448421688717886572021040477403043884175218381895304896638551436548167536144583798526145 

noncomputable def Ns348p1465 := BSN.cos_dyadic_bound_t 8233327 4194304 4 3 16777216 5290000 Ns348p1462 Ns348p501 Ns348p1463 Ns348p1464 Ns348p504 Ns348p1463 6412344 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 8233327) (BSN.cosEvenQ 4194304) 0 3 Ns348p1462 Ns348p501 Ns348p1463 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 8233327) (BSN.cosOddQ 4194304) 0 3 Ns348p1464 Ns348p504 Ns348p1463 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1466 := @Ns348p1453 144927152 11093934080000 801543 2097152 9057947 693370880000 (@Ns348p1454 27 2097152 Bool.true 6412344 16777216 1 5290000 (@Ns348p1457 Ns348p335 8233327 4194304 27 2097152 (@Ns348p1458 281474976710656 575601351 281474976710656 Ns348p1455 Ns348p493 Ns348p1456 Ns348p335 RS349to360.d47 (@Ns348p1459 0 1 1407004114600816 87937757162551 281474976710656 575601351 281474976710656 (@Ns348p1460 1180202841292312412160 70345571118135 281474976710656 575601351 281474976710656 (@Ns348p1461 290388679 281474976710656 (Ns348p1444 rfl rfl) (Ns348p1444 rfl rfl) rfl) (Ns348p1444 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 8233327 4194304) (BSN.cos_neg_of_bound 8233327 4194304 Bool.true 6412344 16777216 1 5290000 (Ns348p1465 rfl rfl)) rfl rfl) 

noncomputable def Ns348p1467 := @Ns348p1429 3771660026626536144177 Ns348p748 (Ns348p1430 qz33 (@Enclosure.Real.IsNear.of_eq qz704 (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 10350651 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz207 (BSN.t_div_two_pi_nonneg qz206 693919 1000 qz209)) Ns348p1434) rfl) (@Ns348p1435 70368744177664 363528142098951 23265666043740160000 (BSN.correction_mk qz208 (BSN.cos_two_pi_p_ne_zero_mk qz206 693919 1000 10 qz209 rfl rfl (@BSN.floor_sqrt_eq_dec qz206 693919 1000 10 qz209 rfl rfl rfl))) (@Ns348p1436 33554432 801543 2097152 9057947 693370880000 26939086741005 70368744177664 363528142098951 23265666043740160000 Ns348p1452 (Ns348p1466 rfl) rfl)) 

noncomputable def Ns348p1468 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz206) (hardyZApproximantRS₀ qz206) Bool.true 3059401153349967551743 2361183241434822606848 912732150272999912144177 Ns348p748 (@Eq.refl Real (hardyZApproximantRS₀ qz206)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz206) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 10) (@HMul.hMul Real Real Real qz5 qz700 (Zeta.RiemannSiegel.correction qz208))) Bool.true 3059401153349967551743 2361183241434822606848 912732150272999912144177 Ns348p748 (BSN.hardyZApproximantRS₀_eq qz206 10 (@BSN.floor_sqrt_eq_dec qz206 693919 1000 10 qz209 rfl rfl rfl)) (@Ns348p1352 3059401153349967551743 2361183241434822606848 912732150272999912144177 Ns348p748 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 10)) Bool.true 2469637 2097152 156275 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz206) qz206 10) (Ns348p1428 (Ns348p1427 rfl rfl rfl rfl) rfl rfl)) (Ns348p1467 rfl) rfl rfl)) 

theorem RS349to360.d61 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz206) Bool.true 3059401153349967551743 2361183241434822606848 912732150272999912144177 Ns348p748 := Ns348p1468 

noncomputable def Ns348p1469 := nat_lit 9758327614992352804864000 

noncomputable def Ns348p1470 := nat_lit 88923899887436462575755198464 

noncomputable abbrev qz788 := (Enclosure.sfrac Bool.false 695254 1000)

noncomputable abbrev qz708 := qz788

noncomputable abbrev qz520 := qz708

noncomputable abbrev qz223 := qz520

noncomputable abbrev qz789 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 695254 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz709 := qz789

noncomputable abbrev qz521 := qz709

noncomputable abbrev qz224 := qz521

noncomputable abbrev qz790 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 695254 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz710 := qz790

noncomputable abbrev qz522 := qz710

noncomputable abbrev qz225 := qz522

noncomputable abbrev qz711 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz224 qz9))

noncomputable def Ns348p1471 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (@HMul.hMul Real Real Real qz5 qz711 (Zeta.RiemannSiegel.correction qz225)) 83253029 67108864 156567 134217728 139533408720898352163 1180591620717411303424 47833130394277780833 Ns348p1469 Ns348p1470 

noncomputable def Ns348p1472 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin BSN.quadSignPos 9 10 695254 1000 199 268435456 134217728 4503599627370496 Bool.false 345758854512 2506 618095470 52 84886744 8 

noncomputable def Ns348p1473 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 695254 1000 100 152 268435456 134217728 4503599627370496 Bool.false 345758854512 2506 

noncomputable def Ns348p1474 := Ns348p1473 558195838 52 94906264 8 589812974 52 89478488 8 Bool.false 7068093 117757 Bool.true 163291814 Bool.true 219045816 14148475504056880 1 Bool.false 220282250 Bool.false Bool.false 183914146 Bool.false Bool.false 146254345 

noncomputable def Ns348p1475 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 695254 1000 26 41 268435456 134217728 4503599627370496 Bool.false 345758854512 2506 

noncomputable def Ns348p1476 := Ns348p1475 480971758 52 109588312 8 522351262 52 101459064 8 Bool.false 60481603 87343 Bool.false 398222740 Bool.true 119995239 14148475504056880 1 Bool.false 23404931 Bool.true Bool.false 116038650 Bool.true Bool.false 7068093 

noncomputable def Ns348p1477 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 695254 1000 206 107 268435456 134217728 4503599627370496 Bool.false 345758854512 2506 

noncomputable def Ns348p1478 := Ns348p1477 372130544 51 134217720 8 432030192 51 120047984 16 Bool.false 66442512 51355 Bool.false 172175050 Bool.false 270790578 14148475504056880 1 Bool.false 215085969 Bool.true Bool.false 227144415 Bool.false Bool.false 60481603 

noncomputable def Ns348p1479 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 695254 1000 513 333 268435456 134217728 4503599627370496 Bool.false 345758854512 2506 

noncomputable def Ns348p1480 := Ns348p1479 186065264 51 189812528 16 294906480 51 154981288 8 Bool.false 268435344 2563 Bool.false 85974754 Bool.false 312021053 14148475504056880 1 Bool.false 84512394 Bool.true Bool.false 246355719 Bool.true Bool.false 66442512 

noncomputable def Ns348p1481 := nat_lit 11516682815938988065075459069960331732450843395003999907 

noncomputable def Ns348p1482 := nat_lit 8941162208747006592171773960663954931211107827712000 

noncomputable def Ns348p1483 := nat_lit 77975700907801079704035818091520000 

noncomputable def Ns348p1484 := nat_lit 325277586261909403844466358738425876480 

noncomputable abbrev qz791 := (@Eq.refl Real (Enclosure.sfrac Bool.false 695254 1000))

noncomputable abbrev qz712 := qz791

noncomputable abbrev qz523 := qz712

noncomputable abbrev qz226 := qz523

noncomputable def Ns348p1485 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz223 695254 1000 1933513498064 16000000 1390508 4000 2000 Ns348p1483 Ns348p1484 qz226 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns348p1486 := nat_lit 235861664070430475572745401752787593880593272729681918095360 

noncomputable abbrev qz713 := (@HSub.hSub Real Real Real qz742 qz743 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz744 (@Nat.cast Real Real.instNatCast 1390508))))

noncomputable abbrev qz524 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 695254 4000) (Real.log (Enclosure.sfrac Bool.false 1933513498064 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz713))

noncomputable abbrev qz714 := (Enclosure.sfrac Bool.false 695254 2000)

noncomputable abbrev qz227 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz524 qz714) (@HMul.hMul Real Real Real qz349 qz714 (Real.log Real.pi)))

noncomputable def Ns348p1487 := @Enclosure.Real.IsNear.addLit_ft_p qz227 (Enclosure.sfrac Bool.true Ns348p1483 Ns348p1484) 725109008208560677007 562949953421312000 10112848968290519647 1083392000000000000000000 Ns348p1483 Ns348p1484 0 1 Ns348p1486 

noncomputable def Ns348p1488 := nat_lit 24330620908521591054505345024000 

noncomputable abbrev qz228 := (@HSub.hSub Real Real Real qz353 qz524 qz714)

noncomputable def Ns348p1489 := @Enclosure.Real.IsNear.subLit_ff_p qz228 (@HMul.hMul Real Real Real qz5 qz714 (Real.log Real.pi)) 949128758086509551759 562949953421312000 2197670221223589 529000000000000000000 13352617614147 33554432000 347627 67108864000 Ns348p1488 725109008208560677007 562949953421312000 

noncomputable def Ns348p1490 := nat_lit 1898257516173019103518000 

noncomputable abbrev qz229 := qz524

noncomputable def Ns348p1491 := @Enclosure.Real.IsNear.subLit_ff_p qz229 qz714 1144825361544499978383 562949953421312000 2197670221223589 529000000000000000000 695254 2000 0 1 Ns348p1490 949128758086509551759 562949953421312000 2197670221223589 529000000000000000000 

noncomputable def Ns348p1492 := nat_lit 2577917535828051731848988963565993984 

noncomputable def Ns348p1493 := nat_lit 56588660154659753202548736 

noncomputable def Ns348p1494 := nat_lit 8915558032337298347972263826465604793615141563678213441699442616129690607385760720022146915991314859212875443846951981141932569930043305782861529960833040257080897211811362137702400 

noncomputable def Ns348p1495 := nat_lit 276466016311695471545387325858000489646650351701493244799495777026504990600738683240521591606904515508576947248436117704985679439348137321646358508364498155403990689948057930301440 

noncomputable def Ns348p1496 := nat_lit 24408675857400142903404165791183286585267372964399771037769307250996394154148680608389311636285474562343602668211216500471152540045042017637606673487350859459183570489180160 

noncomputable def Ns348p1497 := BSN.log_dyadic_bound 884937498064 2982089498064 8 7 Ns348p1494 134217728 42320000 Ns348p1495 Ns348p1496 82128600 3867026996128 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 884937498064) (BSN.artanhQ 2982089498064) 0 7 Ns348p1495 Ns348p1494 Ns348p1496 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz525 := (Real.log (Enclosure.sfrac Bool.false 1933513498064 16000000))

noncomputable def Ns348p1498 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 695254 4000) qz525 695254 4000 0 1 3293893541829879 281474976710656 781250529 33062500000000000 1145046330265695347133 562949953421312000 271583777644683 66125000000000000000 (Enclosure.Real.IsNear.const Bool.false 695254 4000) (BSN.isNear_log_sfrac 1933513498064 16000000 3293893541829879 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1933513498064) qz356)) Bool.false Ns348p1493 Ns348p99 1000000677120000 42320000000000000000000 3293893541829879 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 1933513498064 16000000 16 3867026996128 2097152000000 82128600 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns348p1497 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p1499 := BSN.arctan_dyadic_bound_f 1000 1390508 1 0 16777216 5290000 0 1 1 0 1 1 12065 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1390508) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1390508) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns348p1500 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1390508))) 884279719003555 562949953421312 1 2000000000000000 12065 16777216 1 5290000 14828959858953918873600 883874884781475 562949953421312 200000000529 1058000000000000000 qz17 (Ns348p1499 rfl) rfl rfl 

noncomputable abbrev qz526 := (@HMul.hMul Real Real Real qz583 qz588 qz713)

noncomputable abbrev qz230 := qz526

noncomputable abbrev qz527 := qz713

noncomputable abbrev qz231 := qz527

noncomputable def Ns348p1501 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 695254 4000) qz525) qz230 1145046330265695347133 562949953421312000 271583777644683 66125000000000000000 883874884781475 2251799813685248 200000000529 4232000000000000000 Ns348p1492 1144825361544499978383 562949953421312000 2197670221223589 529000000000000000000 (Ns348p1498 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz231 1 4 0 1 883874884781475 562949953421312 200000000529 1058000000000000000 883874884781475 2251799813685248 200000000529 4232000000000000000 qz364 Ns348p1500 rfl) 

noncomputable def Ns348p1502 := @Ns348p1487 Ns348p1481 Ns348p1482 10112848968290519647 1083392000000000000000000 (@Ns348p1489 10112848968290519647 1083392000000000000000000 (Ns348p1491 (Ns348p1501 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 695254 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz714 (Real.log Real.pi) 695254 2000 0 1 38410761 33554432 1 67108864 13352617614147 33554432000 347627 67108864000 (Enclosure.Real.IsNear.const Bool.false 695254 2000) RS349to360.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns348p1483 Ns348p1484) 

noncomputable def Ns348p1503 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns348p1481 Ns348p1482 10112848968290519647 1083392000000000000000000 21609928407 16777216 157 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz365 qz227 (Enclosure.sfrac Bool.true Ns348p1483 Ns348p1484)) Bool.false Ns348p1481 Ns348p1482 10112848968290519647 1083392000000000000000000 Ns348p1485 (Ns348p1502 rfl rfl)) 

noncomputable def Ns348p1504 := nat_lit 3795820772424302758723584 

noncomputable def Ns348p1505 := nat_lit 3502944123000133658560214348995621468606385365116398594269945616978937850906611547724455083945279295666238005199585516755180626030099846001 

noncomputable def Ns348p1506 := nat_lit 2485825958524113938510063106245338555595675953506937480271778449550823459816871776163614154110244756016392437654841034604311110636401 

noncomputable def Ns348p1507 := nat_lit 17493005159582598602419047957875249843567184555322721661950750083706438043677046242034206249194409926213257521399807246221768072768005755761 

noncomputable def Ns348p1508 := BSN.sin_dyadic_bound_f 107883715043 68719476736 4 3 33554432 10590333 Ns348p1505 Ns348p785 Ns348p1506 Ns348p1507 Ns348p788 Ns348p1506 33554418 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107883715043) qz379 0 3 Ns348p1505 Ns348p785 Ns348p1506 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107883715043) qz380 0 3 Ns348p1507 Ns348p788 Ns348p1506 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1509 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz223) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21609928407) qz377) Bool.false 21609928407 16777216 157 16777216 Bool.false 33554418 33554432 1 5290000 (Ns348p1503 rfl) (Enclosure.sfrac_false_div 21609928407 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21609928407) qz377) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns348p1504) qz381) 226375608064910080 72057594037927936 Bool.false 33554418 33554432 204 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q3 21609928407 16777216 226375608064910080 72057594037927936 204 Ns348p1504 Ns348p188 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554418 33554432 Ns348p1504 Ns348p188 107883715043 68719476736 10590333 10580000 (Ns348p1508 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p1510 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns348p1481 Ns348p1482 10112848968290519647 1083392000000000000000000 345758854512 268435456 2506 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz365 qz227 (Enclosure.sfrac Bool.true Ns348p1483 Ns348p1484)) Bool.false Ns348p1481 Ns348p1482 10112848968290519647 1083392000000000000000000 Ns348p1485 (Ns348p1502 rfl rfl)) 

noncomputable def Ns348p1511 := Ns348p1480 51355 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 513 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 84512394 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 333 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 246355719 268435456) qz226 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) Bool.false 16777209 16777216 52956701 5546967040000 268435344 268435456 2563 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 16777209 16777216 52956701 5546967040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz223) qz223) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 33554418 33554432 847307216 88751472640000 16777209 16777216 52956701 5546967040000 (Ns348p1509 rfl rfl) rfl)) rfl) (Ns348p1510 rfl) RS349to360.d7 

noncomputable def Ns348p1512 := nat_lit 54636612798871427810521371786256 

noncomputable def Ns348p1513 := BSN.sin_dyadic_bound_f 85974754 268435456 2 1 268435456 134217728 Ns348p1512 Ns348p137 Ns348p1512 Ns348p1512 Ns348p138 Ns348p1512 84512394 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 85974754) qz370 0 1 Ns348p1512 Ns348p137 Ns348p1512 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 85974754) qz371 0 1 Ns348p1512 Ns348p138 Ns348p1512 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1514 := nat_lit 148915183880580490647750891502210883240613833058926201902092529963975585 

noncomputable def Ns348p1515 := nat_lit 89840298310046860575663293825594641801549347240656627917321227027361 

noncomputable def Ns348p1516 := nat_lit 389870502061399304398415546696739445733928959068321846631709534585701281 

noncomputable def Ns348p1517 := BSN.sin_dyadic_bound_f 312021053 268435456 3 2 268435456 134217728 Ns348p1514 Ns348p162 Ns348p1515 Ns348p1516 Ns348p165 Ns348p1515 246355719 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 312021053) qz370 0 2 Ns348p1514 Ns348p162 Ns348p1515 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 312021053) qz371 0 2 Ns348p1516 Ns348p165 Ns348p1515 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1518 := nat_lit 7666434276081100584757282986457152854813233228145370540292070500000000 

noncomputable def Ns348p1519 := nat_lit 772256801972461761856683035540892659755043414474531289062500000000 

noncomputable def Ns348p1520 := nat_lit 22997758314639356830748135593300376779120189597607162558298086500000000 

noncomputable def Ns348p1521 := BSN.cos_dyadic_bound_f 172175050 268435456 3 2 268435456 134217728 Ns348p1518 Ns348p121 Ns348p1519 Ns348p1520 Ns348p124 Ns348p1519 215085969 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 172175050) qz368 0 2 Ns348p1518 Ns348p121 Ns348p1519 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 172175050) qz369 0 2 Ns348p1520 Ns348p124 Ns348p1519 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1522 := nat_lit 84454772315268129262285853940487472038874160973367096399193262637564160 

noncomputable def Ns348p1523 := nat_lit 28911351513348919161801289895495697515976578246523354794655362171136 

noncomputable def Ns348p1524 := nat_lit 221144261494680630770200986803350671829644554755943262280600531559629056 

noncomputable def Ns348p1525 := BSN.sin_dyadic_bound_f 270790578 268435456 3 2 268435456 134217728 Ns348p1522 Ns348p162 Ns348p1523 Ns348p1524 Ns348p165 Ns348p1523 227144415 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 270790578) qz370 0 2 Ns348p1522 Ns348p162 Ns348p1523 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 270790578) qz371 0 2 Ns348p1524 Ns348p165 Ns348p1523 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1526 := Ns348p1478 87343 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 206 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 215085969 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat3 107 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 227144415 268435456) qz226 rfl rfl (Ns348p1511 RS349to360.d9 RS349to360.d11 RS349to360.d13 RS349to360.d17 (Ns348p1513 rfl rfl) (Ns348p1517 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns348p1510 rfl) RS349to360.d19 RS349to360.d21 RS349to360.d23 RS349to360.d25 RS349to360.d17 (Ns348p1521 rfl rfl) (Ns348p1525 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns348p1527 := nat_lit 13570621200230455658407770947568523867541595009907132857747114714734620712502421879508438966634125983744000000 

noncomputable def Ns348p1528 := nat_lit 15904230991946957056044536660440401413966989025317343210214704174120276362383627553123864576000000000000 

noncomputable def Ns348p1529 := nat_lit 82170577850724074355425578466253506757624723002588782438386915044766782931189839301241950766721872533913600000 

noncomputable def Ns348p1530 := BSN.cos_dyadic_bound_f 398222740 268435456 4 3 268435456 134217728 Ns348p1527 Ns348p146 Ns348p1528 Ns348p1529 Ns348p149 Ns348p1528 23404931 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 398222740) qz368 0 3 Ns348p1527 Ns348p146 Ns348p1528 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 398222740) qz369 0 3 Ns348p1529 Ns348p149 Ns348p1528 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1531 := nat_lit 3255390531616881401412385245402026591197471265744434725671516273783745 

noncomputable def Ns348p1532 := nat_lit 42984523875961085598249136100295398281685714041659379039041106881 

noncomputable def Ns348p1533 := nat_lit 8525953226910318780989088001261145355824730585793642547287907983832001 

noncomputable def Ns348p1534 := BSN.sin_dyadic_bound_f 119995239 268435456 3 2 268435456 134217728 Ns348p1531 Ns348p162 Ns348p1532 Ns348p1533 Ns348p165 Ns348p1532 116038650 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 119995239) qz370 0 2 Ns348p1531 Ns348p162 Ns348p1532 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 119995239) qz371 0 2 Ns348p1533 Ns348p165 Ns348p1532 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1535 := Ns348p1476 117757 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 26 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 23404931 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 41 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 116038650 268435456) qz226 rfl rfl (Ns348p1526 rfl rfl) (Ns348p1510 rfl) RS349to360.d27 RS349to360.d29 RS349to360.d31 RS349to360.d33 RS349to360.d17 (Ns348p1530 rfl rfl) (Ns348p1534 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p1536 := nat_lit 6202429644371515260953332797374436927740003326469701356618128885883136 

noncomputable def Ns348p1537 := nat_lit 505493189751172811424321966100475099963132151017526081106041446656 

noncomputable def Ns348p1538 := nat_lit 18606277946735043437237149748191109833020083715107069017692174574756096 

noncomputable def Ns348p1539 := BSN.cos_dyadic_bound_f 163291814 268435456 3 2 268435456 134217728 Ns348p1536 Ns348p121 Ns348p1537 Ns348p1538 Ns348p124 Ns348p1537 220282250 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 163291814) qz368 0 2 Ns348p1536 Ns348p121 Ns348p1537 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 163291814) qz369 0 2 Ns348p1538 Ns348p124 Ns348p1537 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1540 := nat_lit 20087377816091542018305738024392482325129435903937880781526399530827776 

noncomputable def Ns348p1541 := nat_lit 5300046708434874191850874416243660592977068380725935369640996765696 

noncomputable def Ns348p1542 := nat_lit 60251533354857756306533512324344959654202353575052190473839916598951936 

noncomputable def Ns348p1543 := BSN.cos_dyadic_bound_f 219045816 268435456 3 2 268435456 134217728 Ns348p1540 Ns348p121 Ns348p1541 Ns348p1542 Ns348p124 Ns348p1541 183914146 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 219045816) qz368 0 2 Ns348p1540 Ns348p121 Ns348p1541 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 219045816) qz369 0 2 Ns348p1542 Ns348p124 Ns348p1541 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1544 := Ns348p1474 144331 BSN.abs_quadSignPos (BSN.cos_quad_nat0 100 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 220282250 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 152 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 183914146 268435456) qz226 rfl rfl (Ns348p1535 rfl) (Ns348p1510 rfl) RS349to360.d35 RS349to360.d37 RS349to360.d39 RS349to360.d41 RS349to360.d17 (Ns348p1539 rfl rfl) (Ns348p1543 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p1545 := nat_lit 17485637861872786435898321227536 

noncomputable def Ns348p1546 := BSN.sin_dyadic_bound_f 64665162 268435456 2 1 268435456 134217728 Ns348p1545 Ns348p137 Ns348p1545 Ns348p1545 Ns348p138 Ns348p1545 64041542 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 64665162) qz370 0 1 Ns348p1545 Ns348p137 Ns348p1545 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 64665162) qz371 0 1 Ns348p1545 Ns348p138 Ns348p1545 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1547 := Ns348p1472 Bool.false 146254345 144331 Bool.true 64665162 14148475504056880 1 Bool.false 64041542 Bool.false Bool.false 166506058 156567 BSN.abs_quadSignPos qz372 (BSN.sfrac_eq_quadSignPos_mul Bool.false 64041542 268435456) qz226 rfl (Ns348p1544 rfl) (Ns348p1510 rfl) RS349to360.d43 RS349to360.d45 RS349to360.d17 (Ns348p1546 rfl rfl) rfl 

noncomputable def Ns348p1548 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) 166506058 268435456 156567 268435456 166506058 268435456 156567 268435456 89392259211984896 83253029 67108864 156567 134217728 (Ns348p1547 rfl rfl rfl rfl) 

noncomputable def Ns348p1549 := @Enclosure.Real.IsNear.mulLit_ff qz711 (Zeta.RiemannSiegel.correction qz225) 10345679 33554432 1 33554432 13487119474797 35184372088832 2952136214373159 186125328349921280000 139533408720898352163 1180591620717411303424 

noncomputable abbrev qz715 := (@HPow.hPow Real Real Real qz7 qz224 qz9)

noncomputable def Ns348p1550 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz715 1 1 0 1 10345679 33554432 1 33554432 10345679 33554432 1 33554432 

noncomputable def Ns348p1551 := @Enclosure.Real.IsNear.sqrt_image qz224 1856450892331 16777216000 347627 16777216000 176482497 176482531 16777216 (@Enclosure.Real.IsNear.of_eq qz224 (@HMul.hMul Real Real Real qz5 qz223 qz3) Bool.false 1856450892331 16777216000 347627 16777216000 (BSN.t_div_two_pi_mk qz223 695254 1000 qz226) (@Enclosure.Real.IsNear.mulLit_ff qz223 qz3 695254 1000 0 1 5340353 33554432 1 33554432 1856450892331 16777216000 347627 16777216000 (Enclosure.Real.IsNear.const Bool.false 695254 1000) RS349to360.d48 rfl)) 

noncomputable abbrev qz792 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 695254 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz716 := qz792

noncomputable abbrev qz528 := qz716

noncomputable abbrev qz232 := qz528

noncomputable def Ns348p1552 := @Enclosure.Real.IsNear.sqrt_image qz232 88241257 8388608 17 16777216 54414014 54414020 16777216 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 352965028 33554432 34 33554432 88241257 8388608 17 16777216 (Ns348p1551 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns348p1553 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz232) 54414017 16777216 3 16777216 5172839 5172840 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz232) Bool.false 108828034 33554432 6 33554432 54414017 16777216 3 16777216 (Ns348p1552 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns348p1554 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 10345679 33554432 1 33554432 10345679 33554432 1 33554432 (Ns348p1553 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz233 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz522))

noncomputable abbrev qz717 := (@HMul.hMul Real Real Real qz738 qz790 qz790)

noncomputable abbrev qz529 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz717 qz710) qz602)

noncomputable abbrev qz234 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz529))

noncomputable def Ns348p1555 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz225) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz233) qz234) Bool.false 13487119474797 

noncomputable def Ns348p1556 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz233) qz234 33799509 33554432 225 

noncomputable abbrev qz718 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz233))

noncomputable def Ns348p1557 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz233) (@Neg.neg Real Real.instNeg qz718) Bool.true 33799509 33554432 225 33554432 (BSN.inv_eq_neg_inv_neg qz233) 

noncomputable def Ns348p1558 := @Enclosure.Real.IsNear.recentre' qz718 Bool.false 33799509 33554432 225 33554432 33799509 33554432 

noncomputable def Ns348p1559 := @Enclosure.Real.IsNear.recentre' qz233 Bool.true 33311132 33554432 1170904432 177502945280000 8327783 8388608 73181527 11093934080000 

noncomputable abbrev qz235 := (@HMul.hMul Real Real Real qz349 qz346 qz522)

noncomputable def Ns348p1560 := @Enclosure.Real.IsNear.cos_image qz235 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 855137) (@Nat.cast Real Real.instNatCast 262144)) Bool.false 855137 262144 215 33554432 Bool.true 33311132 33554432 1 

noncomputable def Ns348p1561 := nat_lit 458763282028570143871038007 

noncomputable def Ns348p1562 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz225 884279719003555 140737488355328 1 500000000000000 4355177 8388608 17 16777216 3851194693770745654235 1180591620717411303424 Ns348p1561 

noncomputable def Ns348p1563 := @Enclosure.Real.IsNear.subLit_ff_p qz232 qz1 88241257 8388608 17 16777216 10 1 0 1 4355177 4355177 8388608 17 

noncomputable def Ns348p1564 := @Ns348p1563 16777216 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 352965028 33554432 34 33554432 88241257 8388608 17 16777216 (Ns348p1551 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns348p1565 := @Enclosure.Real.IsNear.recentre' qz235 Bool.false 3851194693770745654235 1180591620717411303424 Ns348p1561 Ns348p477 855137 262144 215 33554432 (@Ns348p1562 Ns348p477 RS349to360.d47 (Ns348p1564 rfl rfl) rfl) 

noncomputable def Ns348p1566 := nat_lit 4701231701239481845464844079535624350625 

noncomputable def Ns348p1567 := BSN.cos_dyadic_bound_f 8280430455 68719476736 2 1 33554432 10590333 Ns348p1566 Ns348p1447 Ns348p1566 Ns348p1566 Ns348p1448 Ns348p1566 33311132 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 8280430455) qz594 0 1 Ns348p1566 Ns348p1447 Ns348p1566 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 8280430455) qz595 0 1 Ns348p1566 Ns348p1448 Ns348p1566 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1568 := @Ns348p1560 5290000 (Ns348p1565 rfl) (Enclosure.sfrac_false_div 855137 262144) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 855137) (@Nat.cast Real Real.instNatCast 262144)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4552214784487586791424) (@Nat.cast Real Real.instNatCast 37778931862957161709568)) 226375608064910080 72057594037927936 Bool.false 33311132 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q2 855137 262144 226375608064910080 72057594037927936 0 4552214784487586791424 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 33311132 33554432 4552214784487586791424 37778931862957161709568 8280430455 68719476736 10590333 10580000 (Ns348p1567 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p1569 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz233) 8327783 8388608 73181527 11093934080000 16899642 16899867 16777216 (@Enclosure.Real.IsNear.neg qz233 Bool.true 8327783 8388608 73181527 11093934080000 (Ns348p1559 (Ns348p1568 rfl rfl) rfl)) 

noncomputable def Ns348p1570 := Ns348p1557 (@Enclosure.Real.IsNear.neg qz718 Bool.false 33799509 33554432 225 33554432 (@Ns348p1558 225 33554432 (Ns348p1569 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p1571 := @Enclosure.Real.IsNear.recentre' qz234 Bool.true 6384528 16777216 

noncomputable abbrev qz236 := (@HMul.hMul Real Real Real qz349 qz346 qz529)

noncomputable def Ns348p1572 := @Enclosure.Real.IsNear.cos_image qz236 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32903217)) qz377) Bool.true 32903217 16777216 

noncomputable def Ns348p1573 := nat_lit 19422631397894042970029705005 

noncomputable def Ns348p1574 := nat_lit 15688759649975354661946029041493987 

noncomputable def Ns348p1575 := @Enclosure.Real.IsNear.recentre' qz236 Bool.true Ns348p1573 Ns348p734 Ns348p1574 

noncomputable abbrev qz237 := qz529

noncomputable def Ns348p1576 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz237 884279719003555 140737488355328 1 500000000000000 21964352433391 

noncomputable abbrev qz530 := (@HSub.hSub Real Real Real qz587 qz717 qz710)

noncomputable abbrev qz238 := qz530

noncomputable def Ns348p1577 := @Enclosure.Real.IsNear.subLit_tf qz238 qz31 17566305922287 70368744177664 581364997 281474976710656 1 16 

noncomputable abbrev qz531 := qz717

noncomputable abbrev qz239 := qz531

noncomputable def Ns348p1578 := @Enclosure.Real.IsNear.subLit_ff_n qz239 qz225 18967566701329 70368744177664 296152325 281474976710656 4355177 8388608 17 16777216 

noncomputable def Ns348p1579 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz225 4355177 8388608 17 16777216 4355177 8388608 17 16777216 18967566701329 70368744177664 

noncomputable def Ns348p1580 := nat_lit 148132581291992887631117464777014089403721510999462086026544767174905911966664602284612123186241 

noncomputable def Ns348p1581 := nat_lit 1610127769620214838659346197462403809906304246935510694791039165197150035406405693570896961 

noncomputable def Ns348p1582 := nat_lit 893433315626070467394109506237241841980020061857012245213345676246595452620427186904707579335745 

noncomputable def Ns348p1583 := BSN.cos_dyadic_bound_t 32903217 16777216 4 3 16777216 5290000 Ns348p1580 Ns348p867 Ns348p1581 Ns348p1582 Ns348p870 Ns348p1581 6384528 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 32903217) (BSN.cosEvenQ 16777216) 0 3 Ns348p1580 Ns348p867 Ns348p1581 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 32903217) (BSN.cosOddQ 16777216) 0 3 Ns348p1582 Ns348p870 Ns348p1581 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1584 := @Ns348p1571 2345284432 177502945280000 399033 1048576 146580277 11093934080000 (@Ns348p1572 437 33554432 Bool.true 6384528 16777216 1 5290000 (@Ns348p1575 Ns348p335 32903217 16777216 437 33554432 (@Ns348p1576 70368744177664 581364997 281474976710656 Ns348p1573 Ns348p734 Ns348p1574 Ns348p335 RS349to360.d47 (@Ns348p1577 0 1 351429638934256 21964352433391 70368744177664 581364997 281474976710656 (@Ns348p1578 147356854390144106496 17566305922287 70368744177664 581364997 281474976710656 (@Ns348p1579 296152325 281474976710656 (Ns348p1564 rfl rfl) (Ns348p1564 rfl rfl) rfl) (Ns348p1564 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 32903217 16777216) (BSN.cos_neg_of_bound 32903217 16777216 Bool.true 6384528 16777216 1 5290000 (Ns348p1583 rfl rfl)) rfl rfl) 

noncomputable def Ns348p1585 := @Ns348p1549 47833130394277780833 Ns348p1469 (Ns348p1550 qz33 (@Enclosure.Real.IsNear.of_eq qz715 (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 10345679 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz224 (BSN.t_div_two_pi_nonneg qz223 695254 1000 qz226)) Ns348p1554) rfl) (@Ns348p1555 35184372088832 2952136214373159 186125328349921280000 (BSN.correction_mk qz225 (BSN.cos_two_pi_p_ne_zero_mk qz223 695254 1000 10 qz226 rfl rfl (@BSN.floor_sqrt_eq_dec qz223 695254 1000 10 qz226 rfl rfl rfl))) (@Ns348p1556 33554432 399033 1048576 146580277 11093934080000 13487119474797 35184372088832 2952136214373159 186125328349921280000 Ns348p1570 (Ns348p1584 rfl) rfl)) 

noncomputable def Ns348p1586 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (hardyZApproximantRS₀ qz223) Bool.false 1325069366208262183901 1180591620717411303424 11431069178738857876833 Ns348p1469 (@Eq.refl Real (hardyZApproximantRS₀ qz223)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (@HMul.hMul Real Real Real qz5 qz711 (Zeta.RiemannSiegel.correction qz225))) Bool.false 1325069366208262183901 1180591620717411303424 11431069178738857876833 Ns348p1469 (BSN.hardyZApproximantRS₀_eq qz223 10 (@BSN.floor_sqrt_eq_dec qz223 695254 1000 10 qz226 rfl rfl rfl)) (@Ns348p1471 1325069366208262183901 1180591620717411303424 11431069178738857876833 Ns348p1469 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 10)) Bool.false 83253029 67108864 156567 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz223) qz223 10) (Ns348p1548 (Ns348p1547 rfl rfl rfl rfl) rfl rfl)) (Ns348p1585 rfl) rfl rfl)) 

theorem RS349to360.d62 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz223) Bool.false 1325069366208262183901 1180591620717411303424 11431069178738857876833 Ns348p1469 := Ns348p1586 

noncomputable def Ns348p1587 := nat_lit 14440488808215772933549719552 

noncomputable abbrev qz793 := (Enclosure.sfrac Bool.false 696589 1000)

noncomputable abbrev qz719 := qz793

noncomputable abbrev qz532 := qz719

noncomputable abbrev qz240 := qz532

noncomputable abbrev qz794 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 696589 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz720 := qz794

noncomputable abbrev qz533 := qz720

noncomputable abbrev qz241 := qz533

noncomputable abbrev qz795 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 696589 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz721 := qz795

noncomputable abbrev qz534 := qz721

noncomputable abbrev qz242 := qz534

noncomputable abbrev qz722 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz241 qz9))

noncomputable def Ns348p1588 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (@HMul.hMul Real Real Real qz5 qz722 (Zeta.RiemannSiegel.correction qz242)) 1071525 16777216 19609 16777216 559112731376819392797 4722366482869645213696 1554795161686738916231 Ns348p74 Ns348p1587 

noncomputable def Ns348p1589 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin BSN.quadSignPos 9 10 696589 1000 199 268435456 134217728 4503599627370496 Bool.false 346602322357 2511 618095470 52 84886744 8 

noncomputable def Ns348p1590 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 696589 1000 100 152 268435456 134217728 4503599627370496 Bool.false 346602322357 2511 

noncomputable def Ns348p1591 := Ns348p1590 558195838 52 94906264 8 589812974 52 89478488 8 Bool.true 188781386 117988 Bool.true 65015412 Bool.true 162978292 14148475504056880 1 Bool.false 260600461 Bool.false Bool.false 220461271 Bool.false Bool.true 23158119 

noncomputable def Ns348p1592 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 696589 1000 27 40 268435456 134217728 4503599627370496 Bool.false 346602322357 2511 

noncomputable def Ns348p1593 := Ns348p1592 480971758 52 109588312 8 522351262 52 101459064 8 Bool.true 266081391 87515 Bool.false 177935860 Bool.true 395523757 14148475504056880 1 Bool.false 165188703 Bool.false Bool.false 26092407 Bool.false Bool.true 188781386 

noncomputable def Ns348p1594 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 696589 1000 207 108 268435456 134217728 4503599627370496 Bool.false 346602322357 2511 

noncomputable def Ns348p1595 := Ns348p1594 372130544 51 134217720 8 432030192 51 120047984 16 Bool.true 422664474 51457 Bool.false 97191191 Bool.false 115840689 14148475504056880 1 Bool.false 95081578 Bool.false Bool.false 243825993 Bool.false Bool.true 266081391 

noncomputable def Ns348p1596 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 696589 1000 514 334 268435456 134217728 4503599627370496 Bool.false 346602322357 2511 

noncomputable def Ns348p1597 := Ns348p1596 186065264 51 189812528 16 294906480 51 154981288 8 Bool.true 268435440 2571 Bool.false 259388043 Bool.false 340131319 14148475504056880 1 Bool.false 152565618 Bool.true Bool.false 80278564 Bool.true Bool.true 422664474 

noncomputable def Ns348p1598 := nat_lit 1494838333762314546148375446652443754014605327335394379391 

noncomputable def Ns348p1599 := nat_lit 1157717602815949724944464619517125339406938172030976000 

noncomputable def Ns348p1600 := nat_lit 78727210733077210042986180135520000 

noncomputable def Ns348p1601 := nat_lit 329043133096987993708485367823506447680 

noncomputable abbrev qz796 := (@Eq.refl Real (Enclosure.sfrac Bool.false 696589 1000))

noncomputable abbrev qz723 := qz796

noncomputable abbrev qz535 := qz723

noncomputable abbrev qz243 := qz535

noncomputable def Ns348p1602 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz240 696589 1000 1940945939684 16000000 1393178 4000 2000 Ns348p1600 Ns348p1601 qz243 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns348p1603 := nat_lit 478348266803940654767480142928782001284673704747326201405120 

noncomputable abbrev qz724 := (@HSub.hSub Real Real Real qz742 qz743 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz744 (@Nat.cast Real Real.instNatCast 1393178))))

noncomputable abbrev qz536 := (@HSub.hSub Real Real Real qz587 (@HMul.hMul Real Real Real qz583 (Enclosure.sfrac Bool.false 696589 4000) (Real.log (Enclosure.sfrac Bool.false 1940945939684 16000000))) (@HMul.hMul Real Real Real qz583 qz588 qz724))

noncomputable abbrev qz725 := (Enclosure.sfrac Bool.false 696589 2000)

noncomputable abbrev qz244 := (@HSub.hSub Real Real Real qz353 (@HSub.hSub Real Real Real qz353 qz536 qz725) (@HMul.hMul Real Real Real qz349 qz725 (Real.log Real.pi)))

noncomputable def Ns348p1604 := @Enclosure.Real.IsNear.addLit_ft_p qz244 (Enclosure.sfrac Bool.true Ns348p1600 Ns348p1601) 1453755776455918406959 1125899906842624000 20264337919587212729 Ns348p523 Ns348p1600 Ns348p1601 0 1 Ns348p1603 

noncomputable def Ns348p1605 := nat_lit 97559898691394630367708184576000 

noncomputable abbrev qz245 := (@HSub.hSub Real Real Real qz353 qz536 qz725)

noncomputable def Ns348p1606 := @Enclosure.Real.IsNear.subLit_ff_p qz245 (@HMul.hMul Real Real Real qz5 qz725 (Real.log Real.pi)) 1902655584433234693423 1125899906842624000 2201842099048449 529000000000000000000 26756513594229 67108864000 696589 134217728000 Ns348p1605 1453755776455918406959 1125899906842624000 

noncomputable def Ns348p1607 := nat_lit 3805311168866469386846000 

noncomputable abbrev qz246 := qz536

noncomputable def Ns348p1608 := @Enclosure.Real.IsNear.subLit_ff_p qz246 qz725 2294800329537032998191 1125899906842624000 2201842099048449 529000000000000000000 696589 2000 0 1 Ns348p1607 1902655584433234693423 1125899906842624000 2201842099048449 529000000000000000000 

noncomputable def Ns348p1609 := nat_lit 5167430954496336618115915926227386368 

noncomputable def Ns348p1610 := nat_lit 56607213003540683603050496 

noncomputable def Ns348p1611 := nat_lit 9231739368872585915843368351351618168643069341638586663650079683286004343593866822171324597845904282143060311816576562754801121972855287597818051237006261825326406676990153614950400 

noncomputable def Ns348p1612 := nat_lit 289849192674789257800899317384820417825867197912734808173202013134623119532583064633087391612490880828056029566201866452342228546450811881920509654041833524368965348715074410250240 

noncomputable def Ns348p1613 := nat_lit 27440808142698014072107041937973816741323055864689734909144325063747898841570327956230041585092141181885314905404959471063763327829276890358152051854335442530452479787663360 

noncomputable def Ns348p1614 := BSN.log_dyadic_bound 892369939684 2989521939684 8 7 Ns348p1611 134217728 42320000 Ns348p1612 Ns348p1613 82643545 3881891879368 2097152000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 892369939684) (BSN.artanhQ 2989521939684) 0 7 Ns348p1612 Ns348p1611 Ns348p1613 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz537 := (Real.log (Enclosure.sfrac Bool.false 1940945939684 16000000))

noncomputable def Ns348p1615 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 696589 4000) qz537 696589 4000 0 1 3294973459766519 281474976710656 781250529 33062500000000000 2295242267365299703691 1125899906842624000 544210524745581 132250000000000000000 (Enclosure.Real.IsNear.const Bool.false 696589 4000) (BSN.isNear_log_sfrac 1940945939684 16000000 3294973459766519 281474976710656 781250529 33062500000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1940945939684) qz356)) Bool.false Ns348p1610 Ns348p99 1000000677120000 42320000000000000000000 3294973459766519 281474976710656 781250529 33062500000000000 (BSN.log_rat_reduce_isNear 1940945939684 16000000 16 3881891879368 2097152000000 82643545 134217728 24973259072661432 36028797018963968 42320000 1000000000000000 rfl rfl rfl rfl (Ns348p1614 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p1616 := BSN.arctan_dyadic_bound_f 1000 1393178 1 0 16777216 5290000 0 1 1 0 1 1 12042 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1393178) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1393178) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns348p1617 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1393178))) 884279719003555 562949953421312 1 2000000000000000 12042 16777216 1 5290000 14828972806802847563776 883875656533411 562949953421312 200000000529 1058000000000000000 qz17 (Ns348p1616 rfl) rfl rfl 

noncomputable abbrev qz538 := (@HMul.hMul Real Real Real qz583 qz588 qz724)

noncomputable abbrev qz247 := qz538

noncomputable abbrev qz539 := qz724

noncomputable abbrev qz248 := qz539

noncomputable def Ns348p1618 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 696589 4000) qz537) qz247 2295242267365299703691 1125899906842624000 544210524745581 132250000000000000000 883875656533411 2251799813685248 200000000529 4232000000000000000 Ns348p1609 2294800329537032998191 1125899906842624000 2201842099048449 529000000000000000000 (Ns348p1615 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz248 1 4 0 1 883875656533411 562949953421312 200000000529 1058000000000000000 883875656533411 2251799813685248 200000000529 4232000000000000000 qz364 Ns348p1617 rfl) 

noncomputable def Ns348p1619 := @Ns348p1604 Ns348p1598 Ns348p1599 20264337919587212729 Ns348p523 (@Ns348p1606 20264337919587212729 Ns348p523 (Ns348p1608 (Ns348p1618 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 696589 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz725 (Real.log Real.pi) 696589 2000 0 1 38410761 33554432 1 67108864 26756513594229 67108864000 696589 134217728000 (Enclosure.Real.IsNear.const Bool.false 696589 2000) RS349to360.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns348p1600 Ns348p1601) 

noncomputable def Ns348p1620 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns348p1598 Ns348p1599 20264337919587212729 Ns348p523 21662645147 16777216 315 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz365 qz244 (Enclosure.sfrac Bool.true Ns348p1600 Ns348p1601)) Bool.false Ns348p1598 Ns348p1599 20264337919587212729 Ns348p523 Ns348p1602 (Ns348p1619 rfl rfl)) 

noncomputable def Ns348p1621 := nat_lit 3797198724997620174946304 

noncomputable def Ns348p1622 := nat_lit 3508043649994986505184799870781888370017296143628806032208215044071731480461842708789417337833871345485862127894362110227725170385454650321 

noncomputable def Ns348p1623 := nat_lit 2496676410701827893630894539800490122272943567077926577927112218778697780931948400911148393805159175023774319375452523636626654778321 

noncomputable def Ns348p1624 := nat_lit 17518439635012417256056620727325089742712076918965274919578126521671163406168296256041831949060430381287011035009420314641160486839129494481 

noncomputable def Ns348p1625 := BSN.sin_dyadic_bound_f 107922878811 68719476736 4 3 33554432 10590333 Ns348p1622 Ns348p785 Ns348p1623 Ns348p1624 Ns348p788 Ns348p1623 33554430 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 107922878811) qz379 0 3 Ns348p1622 Ns348p785 Ns348p1623 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 107922878811) qz380 0 3 Ns348p1624 Ns348p788 Ns348p1623 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1626 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz240) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21662645147) qz377) Bool.false 21662645147 16777216 315 33554432 Bool.true 33554430 33554432 1 5290000 (Ns348p1620 rfl) (Enclosure.sfrac_false_div 21662645147 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21662645147) qz377) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns348p1621) qz381) 226375608064910080 72057594037927936 Bool.false 33554430 33554432 205 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q1 21662645147 16777216 226375608064910080 72057594037927936 205 Ns348p1621 Ns348p188 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33554430 33554432 Ns348p1621 Ns348p188 107922878811 68719476736 10590333 10580000 (Ns348p1625 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p1627 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns348p1598 Ns348p1599 20264337919587212729 Ns348p523 346602322357 268435456 2511 268435456 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz365 qz244 (Enclosure.sfrac Bool.true Ns348p1600 Ns348p1601)) Bool.false Ns348p1598 Ns348p1599 20264337919587212729 Ns348p523 Ns348p1602 (Ns348p1619 rfl rfl)) 

noncomputable def Ns348p1628 := Ns348p1597 51457 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 514 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 152565618 268435456) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 334 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 80278564 268435456) qz243 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) Bool.true 16777215 16777216 106244027 11093934080000 268435440 268435456 2571 268435456 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 16777215 16777216 106244027 11093934080000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz240) qz240) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 33554430 33554432 1699904432 177502945280000 16777215 16777216 106244027 11093934080000 (Ns348p1626 rfl rfl) rfl)) rfl) (Ns348p1627 rfl) RS349to360.d7 

noncomputable def Ns348p1629 := nat_lit 39508808074642644191777055626462127751305100428889517237791800808150881 

noncomputable def Ns348p1630 := nat_lit 20492720673605067910534363646013072735475665670970505518857148405601 

noncomputable def Ns348p1631 := nat_lit 118485438782580722439510098152094357108444349955326610702337688127641441 

noncomputable def Ns348p1632 := BSN.cos_dyadic_bound_f 259388043 268435456 3 2 268435456 134217728 Ns348p1629 Ns348p121 Ns348p1630 Ns348p1631 Ns348p124 Ns348p1630 152565618 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 259388043) qz368 0 2 Ns348p1629 Ns348p121 Ns348p1630 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 259388043) qz369 0 2 Ns348p1631 Ns348p124 Ns348p1630 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1633 := nat_lit 7212689342846157159661145698641747296382293407212663217161733548462067998993719594945627076255513321045692641 

noncomputable def Ns348p1634 := nat_lit 2397504764169930453462074438895155028518212433686583757750368466664445020026858362154038514117064462561 

noncomputable def Ns348p1635 := nat_lit 43712280127233758388211025279273050288567284950755386891051534899616991479347698473374785493509354203067125985 

noncomputable def Ns348p1636 := BSN.cos_dyadic_bound_f 340131319 268435456 4 3 268435456 134217728 Ns348p1633 Ns348p146 Ns348p1634 Ns348p1635 Ns348p149 Ns348p1634 80278564 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 340131319) qz368 0 3 Ns348p1633 Ns348p146 Ns348p1634 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 340131319) qz369 0 3 Ns348p1635 Ns348p149 Ns348p1634 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1637 := nat_lit 89229326786591104328326898307361 

noncomputable def Ns348p1638 := BSN.sin_dyadic_bound_f 97191191 268435456 2 1 268435456 134217728 Ns348p1637 Ns348p137 Ns348p1637 Ns348p1637 Ns348p138 Ns348p1637 95081578 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 97191191) qz370 0 1 Ns348p1637 Ns348p137 Ns348p1637 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 97191191) qz371 0 1 Ns348p1637 Ns348p138 Ns348p1637 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1639 := nat_lit 1570805050913057364873831806394780284431179275545003620512029152997761 

noncomputable def Ns348p1640 := nat_lit 32425677258887046301473623414213662948690931093894319109794001281 

noncomputable def Ns348p1641 := nat_lit 4712350301384654320528892471937512425967640444772823072897867870990721 

noncomputable def Ns348p1642 := BSN.cos_dyadic_bound_f 115840689 268435456 3 2 268435456 134217728 Ns348p1639 Ns348p121 Ns348p1640 Ns348p1641 Ns348p124 Ns348p1640 243825993 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 115840689) qz368 0 2 Ns348p1639 Ns348p121 Ns348p1640 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 115840689) qz369 0 2 Ns348p1641 Ns348p124 Ns348p1640 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1643 := Ns348p1595 87515 BSN.abs_quadSignPos (BSN.cos_quad_nat3 207 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 95081578 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 108 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 243825993 268435456) qz243 rfl rfl (Ns348p1628 RS349to360.d9 RS349to360.d11 RS349to360.d13 RS349to360.d17 (Ns348p1632 rfl rfl) (Ns348p1636 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns348p1627 rfl) RS349to360.d19 RS349to360.d21 RS349to360.d23 RS349to360.d25 RS349to360.d17 (Ns348p1638 rfl rfl) (Ns348p1642 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns348p1644 := nat_lit 15740660562835222287398566047174208568874122079646064795819549040640000 

noncomputable def Ns348p1645 := nat_lit 1004865309688022099190900789413763308661483039628394127385600000000 

noncomputable def Ns348p1646 := nat_lit 41223912644543230145502316284178162063599153521770771350940194611200000 

noncomputable def Ns348p1647 := BSN.sin_dyadic_bound_f 177935860 268435456 3 2 268435456 134217728 Ns348p1644 Ns348p162 Ns348p1645 Ns348p1646 Ns348p165 Ns348p1645 165188703 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 177935860) qz370 0 2 Ns348p1644 Ns348p162 Ns348p1645 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 177935860) qz371 0 2 Ns348p1646 Ns348p165 Ns348p1645 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1648 := nat_lit 13205421542429298316653825369898184850945990989659451701074048235182150785527757424406583782199519396737036081 

noncomputable def Ns348p1649 := nat_lit 14657870903683134549080008325540873776628109210394077773174379520850353573124303064674814894092950417201 

noncomputable def Ns348p1650 := nat_lit 79963394121746025069465528028397140531194622498014464994614416864325852011917919267645119904530591617294774065 

noncomputable def Ns348p1651 := BSN.cos_dyadic_bound_f 395523757 268435456 4 3 268435456 134217728 Ns348p1648 Ns348p146 Ns348p1649 Ns348p1650 Ns348p149 Ns348p1649 26092407 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 395523757) qz368 0 3 Ns348p1648 Ns348p146 Ns348p1649 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 395523757) qz369 0 3 Ns348p1650 Ns348p149 Ns348p1649 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1652 := Ns348p1593 117988 BSN.abs_quadSignPos (BSN.cos_quad_nat3 27 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 165188703 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 40 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 26092407 268435456) qz243 rfl rfl (Ns348p1643 rfl rfl) (Ns348p1627 rfl) RS349to360.d27 RS349to360.d29 RS349to360.d31 RS349to360.d33 RS349to360.d17 (Ns348p1647 rfl rfl) (Ns348p1651 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p1653 := nat_lit 17867561104330877008156564705536 

noncomputable def Ns348p1654 := BSN.cos_dyadic_bound_f 65015412 268435456 2 1 268435456 134217728 Ns348p1653 Ns348p567 Ns348p1653 Ns348p1653 Ns348p568 Ns348p1653 260600461 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 65015412) qz368 0 1 Ns348p1653 Ns348p567 Ns348p1653 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 65015412) qz369 0 1 Ns348p1653 Ns348p568 Ns348p1653 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1655 := nat_lit 6154927896217747621645365641934213391449161515172936917481154423095296 

noncomputable def Ns348p1656 := nat_lit 497780749124739730137158527196565159522030916971936000024646844416 

noncomputable def Ns348p1657 := nat_lit 18463788127154993385475822608748247044028440483684866880443413975597056 

noncomputable def Ns348p1658 := BSN.cos_dyadic_bound_f 162978292 268435456 3 2 268435456 134217728 Ns348p1655 Ns348p121 Ns348p1656 Ns348p1657 Ns348p124 Ns348p1656 220461271 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 162978292) qz368 0 2 Ns348p1655 Ns348p121 Ns348p1656 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 162978292) qz369 0 2 Ns348p1657 Ns348p124 Ns348p1656 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1659 := Ns348p1591 144613 BSN.abs_quadSignPos (BSN.cos_quad_nat0 100 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 260600461 268435456) BSN.abs_quadSignPos (BSN.cos_quad_nat0 152 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 220461271 268435456) qz243 rfl rfl (Ns348p1652 rfl) (Ns348p1627 rfl) RS349to360.d35 RS349to360.d37 RS349to360.d39 RS349to360.d41 RS349to360.d17 (Ns348p1654 rfl rfl) (Ns348p1658 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns348p1660 := nat_lit 4617189345077268045423578176321 

noncomputable def Ns348p1661 := BSN.sin_dyadic_bound_f 46354769 268435456 2 1 268435456 134217728 Ns348p1660 Ns348p137 Ns348p1660 Ns348p1660 Ns348p138 Ns348p1660 46124728 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 46354769) qz370 0 1 Ns348p1660 Ns348p137 Ns348p1660 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 46354769) qz371 0 1 Ns348p1660 Ns348p138 Ns348p1660 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1662 := Ns348p1589 Bool.true 23158119 144613 Bool.true 46354769 14148475504056880 1 Bool.false 46124728 Bool.false Bool.true 8572200 156872 BSN.abs_quadSignPos qz372 (BSN.sfrac_eq_quadSignPos_mul Bool.false 46124728 268435456) qz243 rfl (Ns348p1659 rfl) (Ns348p1627 rfl) RS349to360.d43 RS349to360.d45 RS349to360.d17 (Ns348p1661 rfl rfl) rfl 

noncomputable def Ns348p1663 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) 8572200 268435456 156872 268435456 8572200 268435456 156872 268435456 4602164831846400 1071525 16777216 19609 16777216 (Ns348p1662 rfl rfl rfl rfl) 

noncomputable def Ns348p1664 := @Enclosure.Real.IsNear.mulLit_ff qz722 (Zeta.RiemannSiegel.correction qz242) 10340719 33554432 1 33554432 54069038272563 140737488355328 750054080630249 46531332087480320000 559112731376819392797 4722366482869645213696 

noncomputable abbrev qz726 := (@HPow.hPow Real Real Real qz7 qz241 qz9)

noncomputable def Ns348p1665 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz726 1 1 0 1 10340719 33554432 1 33554432 10340719 33554432 1 33554432 

noncomputable def Ns348p1666 := @Enclosure.Real.IsNear.sqrt_image qz241 3720031155917 33554432000 696589 33554432000 176651853 176651887 16777216 (@Enclosure.Real.IsNear.of_eq qz241 (@HMul.hMul Real Real Real qz5 qz240 qz3) Bool.false 3720031155917 33554432000 696589 33554432000 (BSN.t_div_two_pi_mk qz240 696589 1000 qz243) (@Enclosure.Real.IsNear.mulLit_ff qz240 qz3 696589 1000 0 1 5340353 33554432 1 33554432 3720031155917 33554432000 696589 33554432000 (Enclosure.Real.IsNear.const Bool.false 696589 1000) RS349to360.d48 rfl)) 

noncomputable abbrev qz797 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 696589 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz727 := qz797

noncomputable abbrev qz540 := qz727

noncomputable abbrev qz249 := qz540

noncomputable def Ns348p1667 := @Enclosure.Real.IsNear.sqrt_image qz249 88325935 8388608 17 16777216 54440116 54440122 16777216 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 353303740 33554432 34 33554432 88325935 8388608 17 16777216 (Ns348p1666 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns348p1668 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz249) 54440119 16777216 3 16777216 5170359 5170360 16777216 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz249) Bool.false 108880238 33554432 6 33554432 54440119 16777216 3 16777216 (Ns348p1667 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns348p1669 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 10340719 33554432 1 33554432 10340719 33554432 1 33554432 (Ns348p1668 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz250 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz534))

noncomputable abbrev qz728 := (@HMul.hMul Real Real Real qz738 qz795 qz795)

noncomputable abbrev qz541 := (@HSub.hSub Real Real Real qz587 (@HSub.hSub Real Real Real qz587 qz728 qz721) qz602)

noncomputable abbrev qz251 := (Real.cos (@HMul.hMul Real Real Real qz349 qz346 qz541))

noncomputable def Ns348p1670 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz242) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz250) qz251) Bool.false 54069038272563 

noncomputable def Ns348p1671 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz250) qz251 17065033 16777216 115 

noncomputable abbrev qz729 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz250))

noncomputable def Ns348p1672 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz250) (@Neg.neg Real Real.instNeg qz729) Bool.true 17065033 16777216 115 16777216 (BSN.inv_eq_neg_inv_neg qz250) 

noncomputable def Ns348p1673 := @Enclosure.Real.IsNear.recentre' qz729 Bool.false 34130066 33554432 230 33554432 17065033 16777216 

noncomputable def Ns348p1674 := @Enclosure.Real.IsNear.recentre' qz250 Bool.true 32988507 33554432 1170904432 177502945280000 32988507 33554432 73181527 11093934080000 

noncomputable abbrev qz252 := (@HMul.hMul Real Real Real qz349 qz346 qz534)

noncomputable def Ns348p1675 := @Enclosure.Real.IsNear.cos_image qz252 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 55792863) qz377) Bool.false 55792863 16777216 215 33554432 Bool.true 32988507 33554432 1 

noncomputable def Ns348p1676 := nat_lit 458763282030024900833800759 

noncomputable def Ns348p1677 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz242 884279719003555 140737488355328 1 500000000000000 4439855 8388608 17 16777216 3926073731816528684525 1180591620717411303424 Ns348p1676 

noncomputable def Ns348p1678 := @Enclosure.Real.IsNear.subLit_ff_p qz249 qz1 88325935 8388608 17 16777216 10 1 0 1 4439855 4439855 8388608 17 

noncomputable def Ns348p1679 := @Ns348p1678 16777216 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 353303740 33554432 34 33554432 88325935 8388608 17 16777216 (Ns348p1666 rfl rfl rfl rfl rfl rfl) rfl) qz378 

noncomputable def Ns348p1680 := @Enclosure.Real.IsNear.recentre' qz252 Bool.false 3926073731816528684525 1180591620717411303424 Ns348p1676 Ns348p477 55792863 16777216 215 33554432 (@Ns348p1677 Ns348p477 RS349to360.d47 (Ns348p1679 rfl rfl) rfl) 

noncomputable def Ns348p1681 := nat_lit 25517953923488179138771671563889375390625 

noncomputable def Ns348p1682 := BSN.cos_dyadic_bound_f 12638963575 68719476736 2 1 33554432 10590333 Ns348p1681 Ns348p1447 Ns348p1681 Ns348p1681 Ns348p1448 Ns348p1681 32988507 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 12638963575) qz594 0 1 Ns348p1681 Ns348p1447 Ns348p1681 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 12638963575) qz595 0 1 Ns348p1681 Ns348p1448 Ns348p1681 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1683 := @Ns348p1675 5290000 (Ns348p1680 rfl) (Enclosure.sfrac_false_div 55792863 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 55792863) qz377) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 444693997262783408766976) qz381) 226375608064910080 72057594037927936 Bool.false 32988507 33554432 0 1000000000000000 10580000 5290000 (BSN.sin_reduce_arg_pos_rat_q2 55792863 16777216 226375608064910080 72057594037927936 0 444693997262783408766976 Ns348p188 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 32988507 33554432 444693997262783408766976 Ns348p188 12638963575 68719476736 10590333 10580000 (Ns348p1682 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns348p1684 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz250) 32988507 33554432 73181527 11093934080000 17064918 17065148 16777216 (@Enclosure.Real.IsNear.neg qz250 Bool.true 32988507 33554432 73181527 11093934080000 (Ns348p1674 (Ns348p1683 rfl rfl) rfl)) 

noncomputable def Ns348p1685 := Ns348p1672 (@Enclosure.Real.IsNear.neg qz729 Bool.false 17065033 16777216 115 16777216 (@Ns348p1673 115 16777216 (Ns348p1684 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns348p1686 := @Enclosure.Real.IsNear.recentre' qz251 Bool.true 6336822 16777216 

noncomputable abbrev qz253 := (@HMul.hMul Real Real Real qz349 qz346 qz541)

noncomputable def Ns348p1687 := @Enclosure.Real.IsNear.cos_image qz253 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 65703325)) qz366) Bool.true 65703325 33554432 

noncomputable def Ns348p1688 := nat_lit 19392198759735323647727122045 

noncomputable def Ns348p1689 := nat_lit 15844148278731290319969951513614859 

noncomputable def Ns348p1690 := @Enclosure.Real.IsNear.recentre' qz253 Bool.true Ns348p1688 Ns348p734 Ns348p1689 

noncomputable abbrev qz254 := qz541

noncomputable def Ns348p1691 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz254 884279719003555 140737488355328 1 500000000000000 21929937261919 

noncomputable abbrev qz542 := (@HSub.hSub Real Real Real qz587 qz728 qz721)

noncomputable abbrev qz255 := qz542

noncomputable def Ns348p1692 := @Enclosure.Real.IsNear.subLit_tf qz255 qz31 17531890750815 70368744177664 587123101 281474976710656 1 16 

noncomputable abbrev qz543 := qz728

noncomputable abbrev qz256 := qz543

noncomputable def Ns348p1693 := @Enclosure.Real.IsNear.subLit_ff_n qz256 qz242 19712312421025 70368744177664 301910429 281474976710656 4439855 8388608 17 16777216 

noncomputable def Ns348p1694 := @Enclosure.Real.IsNear.mulLit_ff qz242 qz242 4439855 8388608 17 16777216 4439855 8388608 17 16777216 19712312421025 70368744177664 

noncomputable def Ns348p1695 := nat_lit 602924232610143746180039173327246173850138526707746481465751466852725907491049288006604510556640625 

noncomputable def Ns348p1696 := nat_lit 6472144093077475538449514268995199529417478656077570019256675888497227955899298191070556640625 

noncomputable def Ns348p1697 := nat_lit 3636554469651357385055376403502721573971634618933981971784009331853936783099965641249232606556640625 

noncomputable def Ns348p1698 := BSN.cos_dyadic_bound_t 65703325 33554432 4 3 16777216 5290000 Ns348p1695 Ns348p210 Ns348p1696 Ns348p1697 Ns348p213 Ns348p1696 6336822 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 65703325) (BSN.cosEvenQ 33554432) 0 3 Ns348p1695 Ns348p210 Ns348p1696 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 65703325) (BSN.cosOddQ 33554432) 0 3 Ns348p1697 Ns348p213 Ns348p1696 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns348p1699 := @Ns348p1686 295144304 22187868160000 3168411 8388608 18446519 1386741760000 (@Ns348p1687 55 4194304 Bool.true 6336822 16777216 1 5290000 (@Ns348p1690 Ns348p335 65703325 33554432 55 4194304 (@Ns348p1691 70368744177664 587123101 281474976710656 Ns348p1688 Ns348p734 Ns348p1689 Ns348p335 RS349to360.d47 (@Ns348p1692 0 1 350878996190704 21929937261919 70368744177664 587123101 281474976710656 (@Ns348p1693 147068159007412715520 17531890750815 70368744177664 587123101 281474976710656 (@Ns348p1694 301910429 281474976710656 (Ns348p1679 rfl rfl) (Ns348p1679 rfl rfl) rfl) (Ns348p1679 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 65703325 33554432) (BSN.cos_neg_of_bound 65703325 33554432 Bool.true 6336822 16777216 1 5290000 (Ns348p1698 rfl rfl)) rfl rfl) 

noncomputable def Ns348p1700 := @Ns348p1664 1554795161686738916231 Ns348p74 (Ns348p1665 qz33 (@Enclosure.Real.IsNear.of_eq qz726 (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 10340719 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz241 (BSN.t_div_two_pi_nonneg qz240 696589 1000 qz243)) Ns348p1669) rfl) (@Ns348p1670 140737488355328 750054080630249 46531332087480320000 (BSN.correction_mk qz242 (BSN.cos_two_pi_p_ne_zero_mk qz240 696589 1000 10 qz243 rfl rfl (@BSN.floor_sqrt_eq_dec qz240 696589 1000 10 qz243 rfl rfl rfl))) (@Ns348p1671 16777216 3168411 8388608 18446519 1386741760000 54069038272563 140737488355328 750054080630249 46531332087480320000 Ns348p1685 (Ns348p1699 rfl) rfl)) 

noncomputable def Ns348p1701 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (hardyZApproximantRS₀ qz240) Bool.true 860720205796705063197 4722366482869645213696 366527951523047376868231 Ns348p74 (@Eq.refl Real (hardyZApproximantRS₀ qz240)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (@HMul.hMul Real Real Real qz5 qz722 (Zeta.RiemannSiegel.correction qz242))) Bool.true 860720205796705063197 4722366482869645213696 366527951523047376868231 Ns348p74 (BSN.hardyZApproximantRS₀_eq qz240 10 (@BSN.floor_sqrt_eq_dec qz240 696589 1000 10 qz243 rfl rfl rfl)) (@Ns348p1588 860720205796705063197 4722366482869645213696 366527951523047376868231 Ns348p74 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (@HAdd.hAdd Real Real Real qz365 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 10)) Bool.true 1071525 16777216 19609 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz240) qz240 10) (Ns348p1663 (Ns348p1662 rfl rfl rfl rfl) rfl rfl)) (Ns348p1700 rfl) rfl rfl)) 

theorem RS349to360.d63 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz240) Bool.true 860720205796705063197 4722366482869645213696 366527951523047376868231 Ns348p74 := Ns348p1701 

noncomputable def RS349to360.d64 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz544 := (RS349to360.d3 qz582 qz603 (@Enclosure.dec_le_dec qz582 qz603 681206 1000 682295 1000 (@Eq.refl Real qz582) qz607 rfl rfl rfl))

noncomputable abbrev qz257 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz544)

noncomputable def Ns348p1702 := @Enclosure.Real.IsNear.of_eq qz257 (hardyZApproximantRS₀ qz4) Bool.true 9602084277628589504769 2361183241434822606848 358521628233850927876927 Ns348p74 

noncomputable abbrev qz545 := (@Enclosure.dec_le_dec qz582 qz603 681206 1000 682295 1000 (@Eq.refl Real qz582) qz607 rfl rfl rfl)

noncomputable abbrev qz258 := qz545

noncomputable def Ns348p1703 := @Enclosure.Real.IsNear.neg_val qz257 9602084277628589504769 2361183241434822606848 358521628233850927876927 Ns348p74 (Ns348p1702 (RS349to360.d4 qz4 qz35 qz258) RS349to360.d49) rfl 

noncomputable abbrev qz259 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz544)

noncomputable def Ns348p1704 := @Enclosure.Real.IsNear.of_eq qz259 (hardyZApproximantRS₀ qz35) Bool.false 323152406815941237755 590295810358705651712 44890083631913484094257 Ns348p218 

noncomputable def Ns348p1705 := @Enclosure.Real.IsNear.pos_val qz259 323152406815941237755 590295810358705651712 44890083631913484094257 Ns348p218 (Ns348p1704 (RS349to360.d50 qz4 qz35 qz258) RS349to360.d51) rfl 

noncomputable def Ns348p1706 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz257 qz4 qz4 681206 1000 681206 1000 

noncomputable def Ns348p1707 := @Enclosure.norm_gt_of_isNear qz257 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 9602084277628589504769 2361183241434822606848 358521628233850927876927 

noncomputable def Ns348p1708 := @Ns348p1707 Ns348p74 303638237 5368709120 1213 5368709120 (Ns348p1702 (RS349to360.d4 qz4 qz35 qz258) RS349to360.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable def Ns348p1709 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz259 qz4 qz35 681206 1000 682295 1000 

noncomputable def Ns348p1710 := @Enclosure.norm_gt_of_isNear qz259 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 323152406815941237755 590295810358705651712 44890083631913484094257 

noncomputable def Ns348p1711 := @Ns348p1710 Ns348p218 303638237 5368709120 1213 5368709120 (Ns348p1704 (RS349to360.d50 qz4 qz35 qz258) RS349to360.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable abbrev qz260 := qz544

noncomputable def Ns348p1712 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz260 (@BSN.thirtyTwoPi_le_dec qz4 681206 1000 qz11 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz257 qz259 (Ns348p1703 rfl rfl) (Ns348p1705 rfl rfl)) (Ns348p1706 qz11 qz11 rfl rfl rfl rfl (Ns348p1708 rfl)) (Ns348p1709 qz11 qz38 rfl rfl rfl rfl (Ns348p1711 rfl)) 

noncomputable abbrev qz546 := (RS349to360.d3 qz603 qz615 (@Enclosure.dec_le_dec qz603 qz615 682295 1000 682966 1000 qz607 qz619 rfl rfl rfl))

noncomputable abbrev qz261 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz546)

noncomputable def Ns348p1713 := @Enclosure.Real.IsNear.of_eq qz261 (hardyZApproximantRS₀ qz35) Bool.false 323152406815941237755 590295810358705651712 44890083631913484094257 Ns348p218 

noncomputable abbrev qz547 := (@Enclosure.dec_le_dec qz603 qz615 682295 1000 682966 1000 qz607 qz619 rfl rfl rfl)

noncomputable abbrev qz262 := qz547

noncomputable def Ns348p1714 := @Enclosure.Real.IsNear.pos_val qz261 323152406815941237755 590295810358705651712 44890083631913484094257 Ns348p218 (Ns348p1713 (RS349to360.d4 qz35 qz62 qz262) RS349to360.d51) rfl 

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz546)

noncomputable def Ns348p1715 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantRS₀ qz62) Bool.true 138866146330329041587 147573952589676412928 78136547001824855141679 Ns348p380 

noncomputable def Ns348p1716 := @Enclosure.Real.IsNear.neg_val qz263 138866146330329041587 147573952589676412928 78136547001824855141679 Ns348p380 (Ns348p1715 (RS349to360.d50 qz35 qz62 qz262) RS349to360.d53) rfl 

noncomputable def Ns348p1717 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz261 qz4 qz35 681206 1000 682295 1000 

noncomputable def Ns348p1718 := @Enclosure.norm_gt_of_isNear qz261 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 323152406815941237755 590295810358705651712 44890083631913484094257 

noncomputable def Ns348p1719 := @Ns348p1718 Ns348p218 303638237 5368709120 1213 5368709120 (Ns348p1713 (RS349to360.d4 qz35 qz62 qz262) RS349to360.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable def Ns348p1720 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz263 qz4 qz62 681206 1000 682966 1000 

noncomputable def Ns348p1721 := @Enclosure.norm_gt_of_isNear qz263 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 138866146330329041587 147573952589676412928 78136547001824855141679 

noncomputable def Ns348p1722 := @Ns348p1721 Ns348p380 303638237 5368709120 1213 5368709120 (Ns348p1715 (RS349to360.d50 qz35 qz62 qz262) RS349to360.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable abbrev qz264 := qz546

noncomputable def Ns348p1723 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz264 (@BSN.thirtyTwoPi_le_dec qz35 682295 1000 qz38 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz261 qz263 (Ns348p1714 rfl rfl) (Ns348p1716 rfl rfl)) (Ns348p1717 qz11 qz38 rfl rfl rfl rfl (Ns348p1719 rfl)) (Ns348p1720 qz11 qz65 rfl rfl rfl rfl (Ns348p1722 rfl)) 

noncomputable abbrev qz548 := (RS349to360.d3 qz615 qz626 (@Enclosure.dec_le_dec qz615 qz626 682966 1000 684557 1000 qz619 qz630 rfl rfl rfl))

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz548)

noncomputable def Ns348p1724 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantRS₀ qz62) Bool.true 138866146330329041587 147573952589676412928 78136547001824855141679 Ns348p380 

noncomputable abbrev qz549 := (@Enclosure.dec_le_dec qz615 qz626 682966 1000 684557 1000 qz619 qz630 rfl rfl rfl)

noncomputable abbrev qz266 := qz549

noncomputable def Ns348p1725 := @Enclosure.Real.IsNear.neg_val qz265 138866146330329041587 147573952589676412928 78136547001824855141679 Ns348p380 (Ns348p1724 (RS349to360.d4 qz62 qz80 qz266) RS349to360.d53) rfl 

noncomputable abbrev qz267 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz548)

noncomputable def Ns348p1726 := @Enclosure.Real.IsNear.of_eq qz267 (hardyZApproximantRS₀ qz80) Bool.false 428173024873351185723 590295810358705651712 112554231283751097883493 Ns348p509 

noncomputable def Ns348p1727 := @Enclosure.Real.IsNear.pos_val qz267 428173024873351185723 590295810358705651712 112554231283751097883493 Ns348p509 (Ns348p1726 (RS349to360.d50 qz62 qz80 qz266) RS349to360.d54) rfl 

noncomputable def Ns348p1728 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz265 qz4 qz62 681206 1000 682966 1000 

noncomputable def Ns348p1729 := @Enclosure.norm_gt_of_isNear qz265 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 138866146330329041587 147573952589676412928 78136547001824855141679 

noncomputable def Ns348p1730 := @Ns348p1729 Ns348p380 303638237 5368709120 1213 5368709120 (Ns348p1724 (RS349to360.d4 qz62 qz80 qz266) RS349to360.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable def Ns348p1731 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz267 qz4 qz80 681206 1000 684557 1000 

noncomputable def Ns348p1732 := @Enclosure.norm_gt_of_isNear qz267 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 428173024873351185723 590295810358705651712 112554231283751097883493 

noncomputable def Ns348p1733 := @Ns348p1732 Ns348p509 303638237 5368709120 1213 5368709120 (Ns348p1726 (RS349to360.d50 qz62 qz80 qz266) RS349to360.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable abbrev qz268 := qz548

noncomputable def Ns348p1734 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz268 (@BSN.thirtyTwoPi_le_dec qz62 682966 1000 qz65 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz265 qz267 (Ns348p1725 rfl rfl) (Ns348p1727 rfl rfl)) (Ns348p1728 qz11 qz65 rfl rfl rfl rfl (Ns348p1730 rfl)) (Ns348p1731 qz11 qz83 rfl rfl rfl rfl (Ns348p1733 rfl)) 

noncomputable abbrev qz550 := (RS349to360.d3 qz626 qz637 (@Enclosure.dec_le_dec qz626 qz637 684557 1000 685896 1000 qz630 qz641 rfl rfl rfl))

noncomputable abbrev qz269 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz550)

noncomputable def Ns348p1735 := @Enclosure.Real.IsNear.of_eq qz269 (hardyZApproximantRS₀ qz80) Bool.false 428173024873351185723 590295810358705651712 112554231283751097883493 Ns348p509 

noncomputable abbrev qz551 := (@Enclosure.dec_le_dec qz626 qz637 684557 1000 685896 1000 qz630 qz641 rfl rfl rfl)

noncomputable abbrev qz270 := qz551

noncomputable def Ns348p1736 := @Enclosure.Real.IsNear.pos_val qz269 428173024873351185723 590295810358705651712 112554231283751097883493 Ns348p509 (Ns348p1735 (RS349to360.d4 qz80 qz98 qz270) RS349to360.d54) rfl 

noncomputable abbrev qz271 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz550)

noncomputable def Ns348p1737 := @Enclosure.Real.IsNear.of_eq qz271 (hardyZApproximantRS₀ qz98) Bool.true 2396718210248418931527 2361183241434822606848 72179817095878966952187 Ns348p629 

noncomputable def Ns348p1738 := @Enclosure.Real.IsNear.neg_val qz271 2396718210248418931527 2361183241434822606848 72179817095878966952187 Ns348p629 (Ns348p1737 (RS349to360.d50 qz80 qz98 qz270) RS349to360.d55) rfl 

noncomputable def Ns348p1739 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz269 qz4 qz80 681206 1000 684557 1000 

noncomputable def Ns348p1740 := @Enclosure.norm_gt_of_isNear qz269 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 428173024873351185723 590295810358705651712 112554231283751097883493 

noncomputable def Ns348p1741 := @Ns348p1740 Ns348p509 303638237 5368709120 1213 5368709120 (Ns348p1735 (RS349to360.d4 qz80 qz98 qz270) RS349to360.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable def Ns348p1742 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz271 qz4 qz98 681206 1000 685896 1000 

noncomputable def Ns348p1743 := @Enclosure.norm_gt_of_isNear qz271 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2396718210248418931527 2361183241434822606848 72179817095878966952187 

noncomputable def Ns348p1744 := @Ns348p1743 Ns348p629 303638237 5368709120 1213 5368709120 (Ns348p1737 (RS349to360.d50 qz80 qz98 qz270) RS349to360.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable abbrev qz272 := qz550

noncomputable def Ns348p1745 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz272 (@BSN.thirtyTwoPi_le_dec qz80 684557 1000 qz83 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz269 qz271 (Ns348p1736 rfl rfl) (Ns348p1738 rfl rfl)) (Ns348p1739 qz11 qz83 rfl rfl rfl rfl (Ns348p1741 rfl)) (Ns348p1742 qz11 qz101 rfl rfl rfl rfl (Ns348p1744 rfl)) 

noncomputable abbrev qz552 := (RS349to360.d3 qz637 qz647 (@Enclosure.dec_le_dec qz637 qz647 685896 1000 687234 1000 qz641 qz651 rfl rfl rfl))

noncomputable abbrev qz273 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz552)

noncomputable def Ns348p1746 := @Enclosure.Real.IsNear.of_eq qz273 (hardyZApproximantRS₀ qz98) Bool.true 2396718210248418931527 2361183241434822606848 72179817095878966952187 Ns348p629 

noncomputable abbrev qz553 := (@Enclosure.dec_le_dec qz637 qz647 685896 1000 687234 1000 qz641 qz651 rfl rfl rfl)

noncomputable abbrev qz274 := qz553

noncomputable def Ns348p1747 := @Enclosure.Real.IsNear.neg_val qz273 2396718210248418931527 2361183241434822606848 72179817095878966952187 Ns348p629 (Ns348p1746 (RS349to360.d4 qz98 qz116 qz274) RS349to360.d55) rfl 

noncomputable abbrev qz275 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz552)

noncomputable def Ns348p1748 := @Enclosure.Real.IsNear.of_eq qz275 (hardyZApproximantRS₀ qz116) Bool.false 70570901578953393403 18446744073709551616 903960483976136430720547 Ns348p748 

noncomputable def Ns348p1749 := @Enclosure.Real.IsNear.pos_val qz275 70570901578953393403 18446744073709551616 903960483976136430720547 Ns348p748 (Ns348p1748 (RS349to360.d50 qz98 qz116 qz274) RS349to360.d56) rfl 

noncomputable def Ns348p1750 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz273 qz4 qz98 681206 1000 685896 1000 

noncomputable def Ns348p1751 := @Enclosure.norm_gt_of_isNear qz273 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2396718210248418931527 2361183241434822606848 72179817095878966952187 

noncomputable def Ns348p1752 := @Ns348p1751 Ns348p629 303638237 5368709120 1213 5368709120 (Ns348p1746 (RS349to360.d4 qz98 qz116 qz274) RS349to360.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable def Ns348p1753 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz275 qz4 qz116 681206 1000 687234 1000 

noncomputable def Ns348p1754 := @Enclosure.norm_gt_of_isNear qz275 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 70570901578953393403 18446744073709551616 903960483976136430720547 

noncomputable def Ns348p1755 := @Ns348p1754 Ns348p748 303638237 5368709120 1213 5368709120 (Ns348p1748 (RS349to360.d50 qz98 qz116 qz274) RS349to360.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable abbrev qz276 := qz552

noncomputable def Ns348p1756 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz276 (@BSN.thirtyTwoPi_le_dec qz98 685896 1000 qz101 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz273 qz275 (Ns348p1747 rfl rfl) (Ns348p1749 rfl rfl)) (Ns348p1750 qz11 qz101 rfl rfl rfl rfl (Ns348p1752 rfl)) (Ns348p1753 qz11 qz119 rfl rfl rfl rfl (Ns348p1755 rfl)) 

noncomputable abbrev qz554 := (RS349to360.d3 qz647 qz657 (@Enclosure.dec_le_dec qz647 qz657 687234 1000 688572 1000 qz651 qz661 rfl rfl rfl))

noncomputable abbrev qz277 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz554)

noncomputable def Ns348p1757 := @Enclosure.Real.IsNear.of_eq qz277 (hardyZApproximantRS₀ qz116) Bool.false 70570901578953393403 18446744073709551616 903960483976136430720547 Ns348p748 

noncomputable abbrev qz555 := (@Enclosure.dec_le_dec qz647 qz657 687234 1000 688572 1000 qz651 qz661 rfl rfl rfl)

noncomputable abbrev qz278 := qz555

noncomputable def Ns348p1758 := @Enclosure.Real.IsNear.pos_val qz277 70570901578953393403 18446744073709551616 903960483976136430720547 Ns348p748 (Ns348p1757 (RS349to360.d4 qz116 qz134 qz278) RS349to360.d56) rfl 

noncomputable abbrev qz279 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz554)

noncomputable def Ns348p1759 := @Enclosure.Real.IsNear.of_eq qz279 (hardyZApproximantRS₀ qz134) Bool.true 25185790977013436597721 9444732965739290427392 5796277099128080211223 Ns348p875 

noncomputable def Ns348p1760 := @Enclosure.Real.IsNear.neg_val qz279 25185790977013436597721 9444732965739290427392 5796277099128080211223 Ns348p875 (Ns348p1759 (RS349to360.d50 qz116 qz134 qz278) RS349to360.d57) rfl 

noncomputable def Ns348p1761 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz277 qz4 qz116 681206 1000 687234 1000 

noncomputable def Ns348p1762 := @Enclosure.norm_gt_of_isNear qz277 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 70570901578953393403 18446744073709551616 903960483976136430720547 

noncomputable def Ns348p1763 := @Ns348p1762 Ns348p748 303638237 5368709120 1213 5368709120 (Ns348p1757 (RS349to360.d4 qz116 qz134 qz278) RS349to360.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable def Ns348p1764 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz279 qz4 qz134 681206 1000 688572 1000 

noncomputable def Ns348p1765 := @Enclosure.norm_gt_of_isNear qz279 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 25185790977013436597721 9444732965739290427392 5796277099128080211223 

noncomputable def Ns348p1766 := @Ns348p1765 Ns348p875 303638237 5368709120 1213 5368709120 (Ns348p1759 (RS349to360.d50 qz116 qz134 qz278) RS349to360.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable abbrev qz280 := qz554

noncomputable def Ns348p1767 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz280 (@BSN.thirtyTwoPi_le_dec qz116 687234 1000 qz119 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz277 qz279 (Ns348p1758 rfl rfl) (Ns348p1760 rfl rfl)) (Ns348p1761 qz11 qz119 rfl rfl rfl rfl (Ns348p1763 rfl)) (Ns348p1764 qz11 qz137 rfl rfl rfl rfl (Ns348p1766 rfl)) 

noncomputable abbrev qz556 := (RS349to360.d3 qz657 qz667 (@Enclosure.dec_le_dec qz657 qz667 688572 1000 689910 1000 qz661 qz671 rfl rfl rfl))

noncomputable abbrev qz281 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz556)

noncomputable def Ns348p1768 := @Enclosure.Real.IsNear.of_eq qz281 (hardyZApproximantRS₀ qz134) Bool.true 25185790977013436597721 9444732965739290427392 5796277099128080211223 Ns348p875 

noncomputable abbrev qz557 := (@Enclosure.dec_le_dec qz657 qz667 688572 1000 689910 1000 qz661 qz671 rfl rfl rfl)

noncomputable abbrev qz282 := qz557

noncomputable def Ns348p1769 := @Enclosure.Real.IsNear.neg_val qz281 25185790977013436597721 9444732965739290427392 5796277099128080211223 Ns348p875 (Ns348p1768 (RS349to360.d4 qz134 qz152 qz282) RS349to360.d57) rfl 

noncomputable abbrev qz283 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz556)

noncomputable def Ns348p1770 := @Enclosure.Real.IsNear.of_eq qz283 (hardyZApproximantRS₀ qz152) Bool.false 32283176890446458239891 18889465931478580854784 315627171209215320867301 Ns348p994 

noncomputable def Ns348p1771 := @Enclosure.Real.IsNear.pos_val qz283 32283176890446458239891 18889465931478580854784 315627171209215320867301 Ns348p994 (Ns348p1770 (RS349to360.d50 qz134 qz152 qz282) RS349to360.d58) rfl 

noncomputable def Ns348p1772 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz281 qz4 qz134 681206 1000 688572 1000 

noncomputable def Ns348p1773 := @Enclosure.norm_gt_of_isNear qz281 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 25185790977013436597721 9444732965739290427392 5796277099128080211223 

noncomputable def Ns348p1774 := @Ns348p1773 Ns348p875 303638237 5368709120 1213 5368709120 (Ns348p1768 (RS349to360.d4 qz134 qz152 qz282) RS349to360.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable def Ns348p1775 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz283 qz4 qz152 681206 1000 689910 1000 

noncomputable def Ns348p1776 := @Enclosure.norm_gt_of_isNear qz283 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 32283176890446458239891 18889465931478580854784 315627171209215320867301 

noncomputable def Ns348p1777 := @Ns348p1776 Ns348p994 303638237 5368709120 1213 5368709120 (Ns348p1770 (RS349to360.d50 qz134 qz152 qz282) RS349to360.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable abbrev qz284 := qz556

noncomputable def Ns348p1778 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz134 688572 1000 qz137 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz281 qz283 (Ns348p1769 rfl rfl) (Ns348p1771 rfl rfl)) (Ns348p1772 qz11 qz137 rfl rfl rfl rfl (Ns348p1774 rfl)) (Ns348p1775 qz11 qz155 rfl rfl rfl rfl (Ns348p1777 rfl)) 

noncomputable abbrev qz558 := (RS349to360.d3 qz667 qz677 (@Enclosure.dec_le_dec qz667 qz677 689910 1000 691247 1000 qz671 qz681 rfl rfl rfl))

noncomputable abbrev qz285 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz558)

noncomputable def Ns348p1779 := @Enclosure.Real.IsNear.of_eq qz285 (hardyZApproximantRS₀ qz152) Bool.false 32283176890446458239891 18889465931478580854784 315627171209215320867301 Ns348p994 

noncomputable abbrev qz559 := (@Enclosure.dec_le_dec qz667 qz677 689910 1000 691247 1000 qz671 qz681 rfl rfl rfl)

noncomputable abbrev qz286 := qz559

noncomputable def Ns348p1780 := @Enclosure.Real.IsNear.pos_val qz285 32283176890446458239891 18889465931478580854784 315627171209215320867301 Ns348p994 (Ns348p1779 (RS349to360.d4 qz152 qz170 qz286) RS349to360.d58) rfl 

noncomputable abbrev qz287 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz558)

noncomputable def Ns348p1781 := @Enclosure.Real.IsNear.of_eq qz287 (hardyZApproximantRS₀ qz170) Bool.true 17155998662820691977921 4722366482869645213696 363607836472599504520483 Ns348p74 

noncomputable def Ns348p1782 := @Enclosure.Real.IsNear.neg_val qz287 17155998662820691977921 4722366482869645213696 363607836472599504520483 Ns348p74 (Ns348p1781 (RS349to360.d50 qz152 qz170 qz286) RS349to360.d59) rfl 

noncomputable def Ns348p1783 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz285 qz4 qz152 681206 1000 689910 1000 

noncomputable def Ns348p1784 := @Enclosure.norm_gt_of_isNear qz285 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 32283176890446458239891 18889465931478580854784 315627171209215320867301 

noncomputable def Ns348p1785 := @Ns348p1784 Ns348p994 303638237 5368709120 1213 5368709120 (Ns348p1779 (RS349to360.d4 qz152 qz170 qz286) RS349to360.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable def Ns348p1786 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz287 qz4 qz170 681206 1000 691247 1000 

noncomputable def Ns348p1787 := @Enclosure.norm_gt_of_isNear qz287 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 17155998662820691977921 4722366482869645213696 363607836472599504520483 

noncomputable def Ns348p1788 := @Ns348p1787 Ns348p74 303638237 5368709120 1213 5368709120 (Ns348p1781 (RS349to360.d50 qz152 qz170 qz286) RS349to360.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable abbrev qz288 := qz558

noncomputable def Ns348p1789 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz152 689910 1000 qz155 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz285 qz287 (Ns348p1780 rfl rfl) (Ns348p1782 rfl rfl)) (Ns348p1783 qz11 qz155 rfl rfl rfl rfl (Ns348p1785 rfl)) (Ns348p1786 qz11 qz173 rfl rfl rfl rfl (Ns348p1788 rfl)) 

noncomputable abbrev qz730 := (@Enclosure.dec_le_dec qz775 qz779 691247 1000 692583 1000 (@Eq.refl Real qz775) (@Eq.refl Real qz779) rfl rfl rfl)

noncomputable abbrev qz560 := (RS349to360.d3 qz677 qz687 qz730)

noncomputable abbrev qz289 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz560)

noncomputable def Ns348p1790 := @Enclosure.Real.IsNear.of_eq qz289 (hardyZApproximantRS₀ qz170) Bool.true 17155998662820691977921 4722366482869645213696 363607836472599504520483 Ns348p74 

noncomputable abbrev qz561 := qz730

noncomputable abbrev qz290 := qz561

noncomputable def Ns348p1791 := @Enclosure.Real.IsNear.neg_val qz289 17155998662820691977921 4722366482869645213696 363607836472599504520483 Ns348p74 (Ns348p1790 (RS349to360.d4 qz170 qz188 qz290) RS349to360.d59) rfl 

noncomputable abbrev qz291 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz560)

noncomputable def Ns348p1792 := @Enclosure.Real.IsNear.of_eq qz291 (hardyZApproximantRS₀ qz188) Bool.false 23864354732909523355 73786976294838206464 45546500069151904569003 Ns348p218 

noncomputable def Ns348p1793 := @Enclosure.Real.IsNear.pos_val qz291 23864354732909523355 73786976294838206464 45546500069151904569003 Ns348p218 (Ns348p1792 (RS349to360.d50 qz170 qz188 qz290) RS349to360.d60) rfl 

noncomputable def Ns348p1794 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz289 qz4 qz170 681206 1000 691247 1000 

noncomputable def Ns348p1795 := @Enclosure.norm_gt_of_isNear qz289 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 17155998662820691977921 4722366482869645213696 363607836472599504520483 

noncomputable def Ns348p1796 := @Ns348p1795 Ns348p74 303638237 5368709120 1213 5368709120 (Ns348p1790 (RS349to360.d4 qz170 qz188 qz290) RS349to360.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable def Ns348p1797 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz291 qz4 qz188 681206 1000 692583 1000 

noncomputable def Ns348p1798 := @Enclosure.norm_gt_of_isNear qz291 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 23864354732909523355 73786976294838206464 45546500069151904569003 

noncomputable def Ns348p1799 := @Ns348p1798 Ns348p218 303638237 5368709120 1213 5368709120 (Ns348p1792 (RS349to360.d50 qz170 qz188 qz290) RS349to360.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable abbrev qz292 := qz560

noncomputable def Ns348p1800 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz170 691247 1000 qz173 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz289 qz291 (Ns348p1791 rfl rfl) (Ns348p1793 rfl rfl)) (Ns348p1794 qz11 qz173 rfl rfl rfl rfl (Ns348p1796 rfl)) (Ns348p1797 qz11 qz191 rfl rfl rfl rfl (Ns348p1799 rfl)) 

noncomputable abbrev qz731 := (@Enclosure.dec_le_dec qz779 qz783 692583 1000 693919 1000 (@Eq.refl Real qz779) qz786 rfl rfl rfl)

noncomputable abbrev qz562 := (RS349to360.d3 qz687 qz697 qz731)

noncomputable abbrev qz293 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz562)

noncomputable def Ns348p1801 := @Enclosure.Real.IsNear.of_eq qz293 (hardyZApproximantRS₀ qz188) Bool.false 23864354732909523355 73786976294838206464 45546500069151904569003 Ns348p218 

noncomputable abbrev qz563 := qz731

noncomputable abbrev qz294 := qz563

noncomputable def Ns348p1802 := @Enclosure.Real.IsNear.pos_val qz293 23864354732909523355 73786976294838206464 45546500069151904569003 Ns348p218 (Ns348p1801 (RS349to360.d4 qz188 qz206 qz294) RS349to360.d60) rfl 

noncomputable abbrev qz295 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz562)

noncomputable def Ns348p1803 := @Enclosure.Real.IsNear.of_eq qz295 (hardyZApproximantRS₀ qz206) Bool.true 3059401153349967551743 2361183241434822606848 912732150272999912144177 Ns348p748 

noncomputable def Ns348p1804 := @Enclosure.Real.IsNear.neg_val qz295 3059401153349967551743 2361183241434822606848 912732150272999912144177 Ns348p748 (Ns348p1803 (RS349to360.d50 qz188 qz206 qz294) RS349to360.d61) rfl 

noncomputable def Ns348p1805 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz293 qz4 qz188 681206 1000 692583 1000 

noncomputable def Ns348p1806 := @Enclosure.norm_gt_of_isNear qz293 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 23864354732909523355 73786976294838206464 45546500069151904569003 

noncomputable def Ns348p1807 := @Ns348p1806 Ns348p218 303638237 5368709120 1213 5368709120 (Ns348p1801 (RS349to360.d4 qz188 qz206 qz294) RS349to360.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable def Ns348p1808 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz295 qz4 qz206 681206 1000 693919 1000 

noncomputable def Ns348p1809 := @Enclosure.norm_gt_of_isNear qz295 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 3059401153349967551743 2361183241434822606848 912732150272999912144177 

noncomputable def Ns348p1810 := @Ns348p1809 Ns348p748 303638237 5368709120 1213 5368709120 (Ns348p1803 (RS349to360.d50 qz188 qz206 qz294) RS349to360.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable abbrev qz296 := qz562

noncomputable def Ns348p1811 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz296 (@BSN.thirtyTwoPi_le_dec qz188 692583 1000 qz191 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz293 qz295 (Ns348p1802 rfl rfl) (Ns348p1804 rfl rfl)) (Ns348p1805 qz11 qz191 rfl rfl rfl rfl (Ns348p1807 rfl)) (Ns348p1808 qz11 qz209 rfl rfl rfl rfl (Ns348p1810 rfl)) 

noncomputable abbrev qz732 := (@Enclosure.dec_le_dec qz783 qz788 693919 1000 695254 1000 qz786 qz791 rfl rfl rfl)

noncomputable abbrev qz564 := (RS349to360.d3 qz697 qz708 qz732)

noncomputable abbrev qz297 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz564)

noncomputable def Ns348p1812 := @Enclosure.Real.IsNear.of_eq qz297 (hardyZApproximantRS₀ qz206) Bool.true 3059401153349967551743 2361183241434822606848 912732150272999912144177 Ns348p748 

noncomputable abbrev qz565 := qz732

noncomputable abbrev qz298 := qz565

noncomputable def Ns348p1813 := @Enclosure.Real.IsNear.neg_val qz297 3059401153349967551743 2361183241434822606848 912732150272999912144177 Ns348p748 (Ns348p1812 (RS349to360.d4 qz206 qz223 qz298) RS349to360.d61) rfl 

noncomputable abbrev qz299 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz564)

noncomputable def Ns348p1814 := @Enclosure.Real.IsNear.of_eq qz299 (hardyZApproximantRS₀ qz223) Bool.false 1325069366208262183901 1180591620717411303424 11431069178738857876833 Ns348p1469 

noncomputable def Ns348p1815 := @Enclosure.Real.IsNear.pos_val qz299 1325069366208262183901 1180591620717411303424 11431069178738857876833 Ns348p1469 (Ns348p1814 (RS349to360.d50 qz206 qz223 qz298) RS349to360.d62) rfl 

noncomputable def Ns348p1816 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz297 qz4 qz206 681206 1000 693919 1000 

noncomputable def Ns348p1817 := @Enclosure.norm_gt_of_isNear qz297 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 3059401153349967551743 2361183241434822606848 912732150272999912144177 

noncomputable def Ns348p1818 := @Ns348p1817 Ns348p748 303638237 5368709120 1213 5368709120 (Ns348p1812 (RS349to360.d4 qz206 qz223 qz298) RS349to360.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable def Ns348p1819 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz299 qz4 qz223 681206 1000 695254 1000 

noncomputable def Ns348p1820 := @Enclosure.norm_gt_of_isNear qz299 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1325069366208262183901 1180591620717411303424 11431069178738857876833 

noncomputable def Ns348p1821 := @Ns348p1820 Ns348p1469 303638237 5368709120 1213 5368709120 (Ns348p1814 (RS349to360.d50 qz206 qz223 qz298) RS349to360.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable abbrev qz300 := qz564

noncomputable def Ns348p1822 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz206 693919 1000 qz209 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz297 qz299 (Ns348p1813 rfl rfl) (Ns348p1815 rfl rfl)) (Ns348p1816 qz11 qz209 rfl rfl rfl rfl (Ns348p1818 rfl)) (Ns348p1819 qz11 qz226 rfl rfl rfl rfl (Ns348p1821 rfl)) 

noncomputable abbrev qz798 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 695254 1000) (Enclosure.sfrac Bool.false 696589 1000) 695254 1000 696589 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 695254 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 696589 1000)) rfl rfl rfl)

noncomputable abbrev qz733 := qz798

noncomputable abbrev qz566 := (RS349to360.d3 qz708 qz719 qz733)

noncomputable abbrev qz301 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz566)

noncomputable def Ns348p1823 := @Enclosure.Real.IsNear.of_eq qz301 (hardyZApproximantRS₀ qz223) Bool.false 1325069366208262183901 1180591620717411303424 11431069178738857876833 Ns348p1469 

noncomputable abbrev qz567 := qz733

noncomputable abbrev qz302 := qz567

noncomputable def Ns348p1824 := @Enclosure.Real.IsNear.pos_val qz301 1325069366208262183901 1180591620717411303424 11431069178738857876833 Ns348p1469 (Ns348p1823 (RS349to360.d4 qz223 qz240 qz302) RS349to360.d62) rfl 

noncomputable abbrev qz303 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz566)

noncomputable def Ns348p1825 := @Enclosure.Real.IsNear.of_eq qz303 (hardyZApproximantRS₀ qz240) Bool.true 860720205796705063197 4722366482869645213696 366527951523047376868231 Ns348p74 

noncomputable def Ns348p1826 := @Enclosure.Real.IsNear.neg_val qz303 860720205796705063197 4722366482869645213696 366527951523047376868231 Ns348p74 (Ns348p1825 (RS349to360.d50 qz223 qz240 qz302) RS349to360.d63) rfl 

noncomputable def Ns348p1827 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz301 qz4 qz223 681206 1000 695254 1000 

noncomputable def Ns348p1828 := @Enclosure.norm_gt_of_isNear qz301 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1325069366208262183901 1180591620717411303424 11431069178738857876833 

noncomputable def Ns348p1829 := @Ns348p1828 Ns348p1469 303638237 5368709120 1213 5368709120 (Ns348p1823 (RS349to360.d4 qz223 qz240 qz302) RS349to360.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable def Ns348p1830 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz303 qz4 qz240 681206 1000 696589 1000 

noncomputable def Ns348p1831 := @Enclosure.norm_gt_of_isNear qz303 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 860720205796705063197 4722366482869645213696 366527951523047376868231 

noncomputable def Ns348p1832 := @Ns348p1831 Ns348p74 303638237 5368709120 1213 5368709120 (Ns348p1825 (RS349to360.d50 qz223 qz240 qz302) RS349to360.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 303638237 5368709120 1213 5368709120 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS349to360.d52) rfl rfl rfl rfl 

noncomputable abbrev qz304 := qz566

noncomputable def Ns348p1833 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz304 (@BSN.thirtyTwoPi_le_dec qz223 695254 1000 qz226 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz301 qz303 (Ns348p1824 rfl rfl) (Ns348p1826 rfl rfl)) (Ns348p1827 qz11 qz226 rfl rfl rfl rfl (Ns348p1829 rfl)) (Ns348p1830 qz11 qz243 rfl rfl rfl rfl (Ns348p1832 rfl)) 

noncomputable def Ns348p1834 := @List.cons RS349to360.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns348p1822)) (@List.cons RS349to360.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz304 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz304) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz304) Ns348p1833)) (@List.nil RS349to360.d0)) 

noncomputable def Ns348p1835 := @List.cons RS349to360.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns348p1800)) (@List.cons RS349to360.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns348p1811)) Ns348p1834) 

noncomputable def Ns348p1836 := @List.cons RS349to360.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns348p1778)) (@List.cons RS349to360.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns348p1789)) Ns348p1835) 

noncomputable def Ns348p1837 := @List.cons RS349to360.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz276 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz276) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz276) Ns348p1756)) (@List.cons RS349to360.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz280 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz280) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz280) Ns348p1767)) Ns348p1836) 

noncomputable def Ns348p1838 := @List.cons RS349to360.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz268 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz268) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz268) Ns348p1734)) (@List.cons RS349to360.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz272 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz272) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz272) Ns348p1745)) Ns348p1837) 

noncomputable def Ns348p1839 := @List.cons RS349to360.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz260 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz260) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz260) Ns348p1712)) (@List.cons RS349to360.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz264 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz264) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz264) Ns348p1723)) Ns348p1838) 

noncomputable abbrev qz568 := (RS349to360.d2 qz677 qz687 qz730)

noncomputable abbrev qz734 := (RS349to360.d2 qz783 qz788 (@Enclosure.dec_le_dec qz783 qz788 693919 1000 695254 1000 qz786 qz791 rfl rfl rfl))

noncomputable abbrev qz735 := (@List.cons RS349to360.d1 (RS349to360.d2 qz788 qz793 qz798) (@List.nil RS349to360.d1))

noncomputable abbrev qz569 := (@List.cons RS349to360.d1 (RS349to360.d2 qz687 qz697 qz731) (@List.cons RS349to360.d1 qz734 qz735))

noncomputable abbrev qz305 := (@List.cons RS349to360.d1 (RS349to360.d2 qz469 qz482 qz559) (@List.cons RS349to360.d1 qz568 qz569))

noncomputable def Ns348p1840 := @List.cons RS349to360.d1 (RS349to360.d2 qz116 qz134 qz278) (@List.cons RS349to360.d1 (RS349to360.d2 qz134 qz152 qz282) qz305) 

noncomputable abbrev qz306 := (RS349to360.d2 qz430 qz443 qz553)

noncomputable def Ns348p1841 := @List.IsChain.cons_cons RS349to360.d1 RS349to360.d64 qz306 (RS349to360.d2 qz116 qz134 qz278) (@List.cons RS349to360.d1 (RS349to360.d2 qz134 qz152 qz282) qz305) 

noncomputable def Ns348p1842 := @List.IsChain.cons_cons RS349to360.d1 RS349to360.d64 (RS349to360.d2 qz116 qz134 qz278) (RS349to360.d2 qz134 qz152 qz282) qz305 (@Enclosure.dec_le_dec qz134 qz134 688572 1000 688572 1000 qz137 qz137 rfl rfl rfl) 

noncomputable abbrev qz307 := (RS349to360.d2 qz469 qz482 qz559)

noncomputable abbrev qz308 := qz568

noncomputable abbrev qz309 := qz569

noncomputable abbrev qz570 := (RS349to360.d2 qz687 qz697 qz731)

noncomputable abbrev qz310 := qz570

noncomputable abbrev qz571 := (@List.cons RS349to360.d1 qz734 qz735)

noncomputable abbrev qz311 := qz571

noncomputable abbrev qz572 := qz734

noncomputable abbrev qz312 := qz572

noncomputable abbrev qz573 := qz735

noncomputable abbrev qz313 := qz573

noncomputable abbrev qz736 := (RS349to360.d2 qz788 qz793 qz798)

noncomputable abbrev qz574 := qz736

noncomputable abbrev qz314 := qz574

noncomputable def Ns348p1843 := @List.IsChain.cons_cons RS349to360.d1 RS349to360.d64 qz307 qz308 qz309 (@Enclosure.dec_le_dec qz170 qz170 691247 1000 691247 1000 qz173 qz173 rfl rfl rfl) (@List.IsChain.cons_cons RS349to360.d1 RS349to360.d64 qz308 qz310 qz311 (@Enclosure.dec_le_dec qz188 qz188 692583 1000 692583 1000 qz191 qz191 rfl rfl rfl) (@List.IsChain.cons_cons RS349to360.d1 RS349to360.d64 qz310 qz312 qz313 (@Enclosure.dec_le_dec qz206 qz206 693919 1000 693919 1000 qz209 qz209 rfl rfl rfl) (@List.IsChain.cons_cons RS349to360.d1 RS349to360.d64 qz312 qz314 (@List.nil RS349to360.d1) (@Enclosure.dec_le_dec qz223 qz223 695254 1000 695254 1000 qz226 qz226 rfl rfl rfl) (@List.IsChain.singleton RS349to360.d1 RS349to360.d64 qz314)))) 

noncomputable abbrev qz315 := (@List.cons RS349to360.d1 qz568 qz569)

noncomputable def Ns348p1844 := @List.IsChain.cons_cons RS349to360.d1 RS349to360.d64 (RS349to360.d2 qz134 qz152 qz282) qz307 qz315 (@Enclosure.dec_le_dec qz152 qz152 689910 1000 689910 1000 qz155 qz155 rfl rfl rfl) Ns348p1843 

noncomputable def Ns348p1845 := @List.IsChain.cons_cons RS349to360.d1 RS349to360.d64 (RS349to360.d2 qz4 qz35 qz258) (RS349to360.d2 qz35 qz62 qz262) (@List.cons RS349to360.d1 (RS349to360.d2 qz62 qz80 qz266) (@List.cons RS349to360.d1 (RS349to360.d2 qz80 qz98 qz270) (@List.cons RS349to360.d1 qz306 Ns348p1840))) (@Enclosure.dec_le_dec qz35 qz35 682295 1000 682295 1000 qz38 qz38 rfl rfl rfl) (@List.IsChain.cons_cons RS349to360.d1 RS349to360.d64 (RS349to360.d2 qz35 qz62 qz262) (RS349to360.d2 qz62 qz80 qz266) (@List.cons RS349to360.d1 (RS349to360.d2 qz80 qz98 qz270) (@List.cons RS349to360.d1 qz306 Ns348p1840)) (@Enclosure.dec_le_dec qz62 qz62 682966 1000 682966 1000 qz65 qz65 rfl rfl rfl) (@List.IsChain.cons_cons RS349to360.d1 RS349to360.d64 (RS349to360.d2 qz62 qz80 qz266) (RS349to360.d2 qz80 qz98 qz270) (@List.cons RS349to360.d1 qz306 Ns348p1840) (@Enclosure.dec_le_dec qz80 qz80 684557 1000 684557 1000 qz83 qz83 rfl rfl rfl) (@List.IsChain.cons_cons RS349to360.d1 RS349to360.d64 (RS349to360.d2 qz80 qz98 qz270) qz306 Ns348p1840 (@Enclosure.dec_le_dec qz98 qz98 685896 1000 685896 1000 qz101 qz101 rfl rfl rfl) (Ns348p1841 (@Enclosure.dec_le_dec qz116 qz116 687234 1000 687234 1000 qz119 qz119 rfl rfl rfl) (Ns348p1842 Ns348p1844))))) 

noncomputable abbrev qz575 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz576 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns348p1839 Ns348p1845)

noncomputable abbrev qz577 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns348p1839 Ns348p1845))

theorem RS349to360.d65 : Zeta.Certificates.BatchSpec 12 681206 1000 696589 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz575 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 12) (And (@Eq (Option Real) (@Option.map qz575 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz575 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz575 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz575 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz240)))) qz576 (@And.intro (@Eq Nat (@List.length qz575 qz577) 12) (And (@Eq (Option Real) (@Option.map qz575 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz575 qz577)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz575 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz575 qz577)) (@Option.some Real qz240))) (@Eq.refl Nat 12) (@And.intro (@Eq (Option Real) (@Option.map qz575 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz575 qz577)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz575 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz575 qz577)) (@Option.some Real qz240)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz240))))

theorem solution : Zeta.Certificates.BatchSpec 12 681206 1000 696589 1000 := RS349to360.d65
#print axioms solution
#check solution
