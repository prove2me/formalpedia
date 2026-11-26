-- Prove2me | solution 1 for RHHeight1000.rs_main_0133_0150
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T22:04:15.964013+00:00
-- url     : https://prove2.me/submissions/218e6b95-5049-48f8-95f7-7255fd60d387

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

noncomputable def RS133to150.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS133to150.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS133to150.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS133to150.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS133to150.d2 a b h 

theorem RS133to150.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS133to150.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS133to150.d3 a b h)) 

noncomputable def Ns132p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns132p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns132p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns132p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns132p0 Ns132p1 Ns132p2 Ns132p1 76821522 67108864 1 27368416 76821522 67108864 1 27368416 38410761 33554432 2 33554432 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns132p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns132p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns132p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns132p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns132p8 := nat_lit 167537954069964697925743468333314178468718661948561187618563575975392713740913527107727581163208035826476740967700482432525301063254420572874757592895482956004842597348203117269212172556829666669574421653274845612596416189641484794702002223261246862056663160605878293700340502480877986491439034432953223334258717026053687371824342493299510132312376251152844516906794910572262907940062760396663270105627554083664899640691826599584783763757814813433640133591539937449421955686657622469485188711283992428713614179785896055117030632677201478317872225272595773536303110412989181984739022579128493081560758017763072115692678596043664844667144619713966763611484179303468167142547433165016751768184247559143333542643815355903304572487929375 

noncomputable def Ns132p9 := nat_lit 17907736863639440849562382641391758203535690054199171304015283257442503423240620144819838407313611418261944516207295868563739563278604805791797182761045687776939279949642059267526948014748996956777332184087524644234759874591635243045607722412471722018588244283882362848653445974523544951031470230725674276297342086185092985546835544820091590454230569790847977790484558207349923322458845585052164126500435851662252152223728079705692133047658564669873831757357628115566356048471439549797170528303905720944834637690907185213991407615774042056720704508980680095051114888612186461088301140868302968264130481206655302741383410655080008578156649725227045954510069588220729495895148666460653631514375880874422615237249871322129146554264800 

noncomputable def Ns132p10 := nat_lit 55164646516618494962085419356369025784335016154267579706247610053041231157772817011486486467101704279863254798704146668052276438579475100451766223896220272709675360577301802978530276301158911649961092601279696986330335403118086533522541958716560166657634553390183479955483588238249446822384543398154260439705049143284278540285021213103458182619368483938376641172730818250587232036579805400979202432024046862170503602539341971086573372247299262086029843105216008583038025403798224342134620653974939981235680083776396058604459065501719125356177784467570909658245422960948263734871602033841948787585406240093531041217463298165642337705122589129757920995868559518021463265498464182174549661735402095023640043996665674913376875 

noncomputable def Ns132p11 := BSN.log_dyadic_bound Ns132p6 Ns132p7 15 14 Ns132p8 67108864 27368416 Ns132p9 Ns132p10 76821522 Ns132p4 Ns132p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns132p6) (BSN.artanhQ Ns132p7) 0 14 Ns132p9 Ns132p8 Ns132p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns132p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns132p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns132p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns132p15 := nat_lit 167537954069966963268140139327979112712430526945422964221951926912223381190141639739514890494967825643602350173964944759828460064784215684919760383437959917620844610857567326816719640593037578236900835917107172977527392439886629774248115214831425484905681376157923696414882114961796820014026232307332015059110330001516939277521159573995394989771587717775443426002499543257897301982481613760098955890450106043861450716722534643739571053080256776912576113428445260435254713579381797931690799491102381747484553243404562568585572234105168360737285205910186933811836504830286397217473365026331067977496463917110493303316865058355012304571237619413071097245713770677768486493924969821719264401216877841676972336093778875903304572487929375 

noncomputable def Ns132p16 := nat_lit 17907736863639702486765313263906285882628955290251965205176678923530777959693011244026517850256414903756943142851250712732214241881959351517241344993825585048584379523049477943740273636414656012170312373198803997844271825165684859407921203335666024680974464565759223251918458072775203410604089667122984485578465112081892102496937045858735135721609691262763214794451343726045584198128451069547586972080574568545086657023793200560105564573365716615162566961587407171758966967827997201380802107846920231945878242774600967607639551032178207663699700360114112068650063802902647517702890145150192721997537569966984346993833704449560383184487996362781528900358997452380059737141488304159449328022742959995775545894292303322129146554264800 

noncomputable def Ns132p17 := nat_lit 55164646516619937449385584700664297411818070214438189962773666351465523500358685366424500506990751111492356556545320273548942244833046464529601272738875466881799996765940232256588350019911833156887888425998391295014189841212513610526066550079316346993943774342801096070086869790972589246312728227659319758310961510342377923950694747797317942483020440897997204711883064182772445608288320382376665481938194224815739627075458138172195220395246294556718284728034954178416253903237031389214179719385823921869528509431462690683227358218086518156757026652846493301460983550768858152506145788622699720737745394141184245149692548799188169247529408201840608223422296381897323845616153036586108326210125693898345963996665674913376875 

noncomputable def Ns132p18 := BSN.log_dyadic_bound Ns132p13 Ns132p14 15 14 Ns132p15 67108864 27368416 Ns132p16 Ns132p17 76821522 Ns132p12 Ns132p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns132p13) (BSN.artanhQ Ns132p14) 0 14 Ns132p16 Ns132p15 Ns132p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns132p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 38410761 33554432 2 33554432 38410761 33554432 1 16777216 (Ns132p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns132p0 Ns132p1 76821522 67108864 1 27368416 Bool.false (BSN.logfrac_isNear Ns132p4 Ns132p5 1 Ns132p0 Ns132p1 76821522 67108864 27368416 rfl rfl rfl (Ns132p11 rfl))) (BSN.isNear_log_sfrac Ns132p2 Ns132p1 76821522 67108864 1 27368416 Bool.false (BSN.logfrac_isNear Ns132p12 Ns132p5 1 Ns132p2 Ns132p1 76821522 67108864 27368416 rfl rfl rfl (Ns132p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS133to150.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 16777216 := Ns132p19 

noncomputable def Ns132p20 := BSN.log_dyadic_bound 1 3 7 6 71816279535 4194304 1710526 2852596872 10395 2907269 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1) (BSN.artanhQ 3) 0 6 2852596872 71816279535 10395 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz316 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz0 := qz316

theorem RS133to150.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 2907269 4194304 1 1710526 := BSN.isNear_log_sfrac 2 1 2907269 4194304 1 1710526 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 2907269 4194304 1710526 rfl rfl rfl (Ns132p20 rfl)) 

theorem RS133to150.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 46516304 67108864 40 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 2907269 4194304 1 1710526 46516304 67108864 40 67108864 RS133to150.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz319 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def Ns132p21 := @Enclosure.Real.IsNear.inv_image qz317 11863283 8388608 1 8388608 2965820 2965822 4194304 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 11863283 8388608 1 8388608 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 11863283 8388608 1 8388608 11863283 8388608 1 8388608 (BSN.sqrt_enclosure 2 1 5931641 5931642 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS133to150.d8 : Enclosure.Real.IsNear qz320 Bool.false 2965821 4194304 1 4194304 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 5931642 8388608 2 8388608 2965821 4194304 1 4194304 (Ns132p21 rfl rfl) rfl 

theorem RS133to150.d9 : Enclosure.Real.IsNear qz320 Bool.false 47453136 67108864 16 67108864 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 2965821 4194304 1 4194304 47453136 67108864 16 67108864 RS133to150.d8 rfl 

noncomputable def Ns132p22 := BSN.log_dyadic_bound 1 2 12 11 1326382131865190400 4194304 1710526 130797573554866995 13749310575 4607913 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 1) (BSN.artanhQ 2) 0 11 130797573554866995 1326382131865190400 13749310575 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS133to150.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 4607913 4194304 1 1710526 := BSN.isNear_log_sfrac 3 1 4607913 4194304 1 1710526 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 4607913 4194304 1710526 rfl rfl rfl (Ns132p22 rfl)) 

theorem RS133to150.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 73726608 67108864 40 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 4607913 4194304 1 1710526 73726608 67108864 40 67108864 RS133to150.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns132p23 := @Enclosure.Real.IsNear.inv_image qz321 14529495 8388608 1 8388608 2421582 2421583 4194304 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 14529495 8388608 1 8388608 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 14529495 8388608 1 8388608 14529495 8388608 1 8388608 (BSN.sqrt_enclosure 3 1 7264747 7264748 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS133to150.d12 : Enclosure.Real.IsNear qz323 Bool.false 4843165 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 4843165 8388608 1 8388608 4843165 8388608 1 8388608 (Ns132p23 rfl rfl) rfl 

theorem RS133to150.d13 : Enclosure.Real.IsNear qz323 Bool.false 38745320 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 4843165 8388608 1 8388608 38745320 67108864 8 67108864 RS133to150.d12 rfl 

noncomputable def Ns132p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns132p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns132p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns132p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns132p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns132p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns132p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns132p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns132p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns132p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns132p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns132p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns132p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns132p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns132p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns132p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns132p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns132p25 Ns132p26 Ns132p27 Ns132p28 200200021673987500790625 Ns132p29 Ns132p30 Ns132p31 Ns132p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns132p32 Ns132p33 151412625 Ns132p34 Ns132p35 1322214852783825 Ns132p27 Ns132p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns132p32 Ns132p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns132p34 Ns132p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns132p36 Ns132p37 1267389585 Ns132p38 Ns132p39 1927077560082675 Ns132p29 Ns132p30 Ns132p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns132p36 Ns132p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns132p38 Ns132p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS133to150.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns132p24 Ns132p25 1 Ns132p26 := Ns132p40 rfl rfl rfl 

noncomputable def Ns132p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns132p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns132p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns132p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns132p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns132p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns132p25 Ns132p26 Ns132p42 Ns132p43 9945 Ns132p44 Ns132p45 65835 Ns132p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns132p42 Ns132p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns132p44 Ns132p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS133to150.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns132p41 Ns132p25 1 Ns132p26 := Ns132p46 rfl 

noncomputable def Ns132p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns132p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS133to150.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns132p47 Ns132p25 1 Ns132p48 := BSN.pi_combine Ns132p24 Ns132p41 Ns132p25 Ns132p26 Ns132p48 Ns132p47 rfl rfl rfl rfl RS133to150.d14 RS133to150.d15 

theorem RS133to150.d17 : Enclosure.Real.IsNear Real.pi Bool.false 3537118876014220 1125899906842624 1 1125899906842624 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns132p47 Ns132p25 1 Ns132p48 3537118876014220 1125899906842624 1 1125899906842624 RS133to150.d16 rfl 

noncomputable def Ns132p49 := nat_lit 178719669545544893480837345123291015625 

noncomputable def Ns132p50 := nat_lit 27745388228251122714770036239987464375 

noncomputable def Ns132p51 := nat_lit 1274524447665412456340166714375 

noncomputable def Ns132p52 := BSN.log_dyadic_bound 3 5 16 15 Ns132p49 4194304 1710526 Ns132p50 Ns132p51 5814539 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP 3) (BSN.artanhQ 5) 0 15 Ns132p50 Ns132p49 Ns132p51 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS133to150.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 5814539 4194304 1 1710526 := BSN.isNear_log_sfrac 4 1 5814539 4194304 1 1710526 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 5814539 4194304 1710526 rfl rfl rfl (Ns132p52 rfl)) 

theorem RS133to150.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 93032624 67108864 40 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 5814539 4194304 1 1710526 93032624 67108864 40 67108864 RS133to150.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns132p53 := @Enclosure.Real.IsNear.inv_image qz325 16777217 8388608 1 8388608 2097151 2097152 4194304 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 16777217 8388608 1 8388608 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 16777217 8388608 1 8388608 16777217 8388608 1 8388608 (BSN.sqrt_enclosure 4 1 8388608 8388609 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS133to150.d20 : Enclosure.Real.IsNear qz327 Bool.false 4194303 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 4194303 8388608 1 8388608 4194303 8388608 1 8388608 (Ns132p53 rfl rfl) rfl 

theorem RS133to150.d21 : Enclosure.Real.IsNear qz327 Bool.false 33554424 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 4194303 8388608 1 8388608 33554424 67108864 8 67108864 RS133to150.d20 rfl 

noncomputable def Ns132p54 := nat_lit 432044237847189949652629901200995702590625 

noncomputable def Ns132p55 := nat_lit 89467042677079332529401996239971435345500 

noncomputable def Ns132p56 := nat_lit 2254217236409302326906244300800000 

noncomputable def Ns132p57 := nat_lit 1703271991756449094855875 

noncomputable def Ns132p58 := BSN.log_dyadic_bound 2 3 20 19 Ns132p54 4194304 1710526 Ns132p55 Ns132p56 6750471 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 19 9 52520441922763380 253655458399017675 9033331507200 1156268355358836200013540 Ns132p57 249544393960587264000 Ns132p55 Ns132p54 Ns132p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 2) (BSN.artanhQ 3) 0 9 52520441922763380 253655458399017675 9033331507200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 9 19 1156268355358836200013540 Ns132p57 249544393960587264000 rfl rfl rfl rfl)) rfl rfl 

theorem RS133to150.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 6750471 4194304 1 1710526 := BSN.isNear_log_sfrac 5 1 6750471 4194304 1 1710526 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 6750471 4194304 1710526 rfl rfl rfl (Ns132p58 rfl rfl)) 

theorem RS133to150.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 108007536 67108864 40 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 6750471 4194304 1 1710526 108007536 67108864 40 67108864 RS133to150.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns132p59 := @Enclosure.Real.IsNear.inv_image qz328 18757497 8388608 1 8388608 1875749 1875750 4194304 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 18757497 8388608 1 8388608 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 18757497 8388608 1 8388608 18757497 8388608 1 8388608 (BSN.sqrt_enclosure 5 1 9378748 9378749 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS133to150.d24 : Enclosure.Real.IsNear qz329 Bool.false 3751499 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 3751499 8388608 1 8388608 3751499 8388608 1 8388608 (Ns132p59 rfl rfl) rfl 

theorem RS133to150.d25 : Enclosure.Real.IsNear qz329 Bool.false 30011992 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 3751499 8388608 1 8388608 30011992 67108864 8 67108864 RS133to150.d24 rfl 

noncomputable def Ns132p60 := BSN.log_dyadic_bound 2 10 5 4 94500000000 4194304 1710526 1291130880 26880 1700643 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 10) 0 4 1291130880 94500000000 26880 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) (@Nat.cast Real Real.instNatCast 1))

theorem RS133to150.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683142479095 2251799813685248 250000000855263 427631500000000000000 := BSN.isNear_log_sfrac 6 1 4034683142479095 2251799813685248 250000000855263 427631500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 270763002291722209198080 151115727451828646838272 1000000003421052 1710526000000000000000 4034683142479095 2251799813685248 250000000855263 427631500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 1700643 4194304 24973259072661432 36028797018963968 1710526 1000000000000000 rfl rfl rfl rfl (Ns132p60 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS133to150.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 120242927 67108864 40 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683142479095 2251799813685248 250000000855263 427631500000000000000 120242927 67108864 40 67108864 RS133to150.d26 rfl 

noncomputable abbrev qz331 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns132p61 := @Enclosure.Real.IsNear.inv_image qz331 20547809 8388608 1 8388608 1712317 1712318 4194304 (@Enclosure.Real.IsNear.of_eq qz331 (Real.sqrt qz330) Bool.false 20547809 8388608 1 8388608 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 20547809 8388608 1 8388608 20547809 8388608 1 8388608 (BSN.sqrt_enclosure 6 1 10273904 10273905 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS133to150.d28 : Enclosure.Real.IsNear qz332 Bool.false 3424635 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 3424635 8388608 1 8388608 3424635 8388608 1 8388608 (Ns132p61 rfl rfl) rfl 

theorem RS133to150.d29 : Enclosure.Real.IsNear qz332 Bool.false 27397080 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 3424635 8388608 1 8388608 27397080 67108864 8 67108864 RS133to150.d28 rfl 

noncomputable def Ns132p62 := BSN.log_dyadic_bound 3 11 6 5 269619528727395 4194304 1710526 6999933372849 55801305 2347198 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 3) (BSN.artanhQ 11) 0 5 6999933372849 269619528727395 55801305 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz842 := (Enclosure.sfrac Bool.false 7 1)

noncomputable abbrev qz629 := qz842

noncomputable abbrev qz333 := qz629

noncomputable abbrev qz1 := qz333

noncomputable abbrev qz334 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) (@Nat.cast Real Real.instNatCast 1))

theorem RS133to150.d30 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 4381799714987255 2251799813685248 250000000855263 427631500000000000000 := BSN.isNear_log_sfrac 7 1 4381799714987255 2251799813685248 250000000855263 427631500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz334) Bool.false 294057601148318457528320 151115727451828646838272 1000000003421052 1710526000000000000000 4381799714987255 2251799813685248 250000000855263 427631500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 2347198 4194304 24973259072661432 36028797018963968 1710526 1000000000000000 rfl rfl rfl rfl (Ns132p62 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS133to150.d31 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 130587807 67108864 40 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 4381799714987255 2251799813685248 250000000855263 427631500000000000000 130587807 67108864 40 67108864 RS133to150.d30 rfl 

noncomputable abbrev qz335 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns132p63 := @Enclosure.Real.IsNear.inv_image qz335 22194171 8388608 1 8388608 1585297 1585298 4194304 (@Enclosure.Real.IsNear.of_eq qz335 (Real.sqrt qz334) Bool.false 22194171 8388608 1 8388608 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz334) Bool.false 22194171 8388608 1 8388608 22194171 8388608 1 8388608 (BSN.sqrt_enclosure 7 1 11097085 11097086 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz336 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS133to150.d32 : Enclosure.Real.IsNear qz336 Bool.false 3170595 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz336 Bool.false 3170595 8388608 1 8388608 3170595 8388608 1 8388608 (Ns132p63 rfl rfl) rfl 

theorem RS133to150.d33 : Enclosure.Real.IsNear qz336 Bool.false 25364760 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz336 Bool.false 3170595 8388608 1 8388608 25364760 67108864 8 67108864 RS133to150.d32 rfl 

theorem RS133to150.d34 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz843 := (@instHMul Real Real.instMul)

noncomputable abbrev qz630 := qz843

noncomputable abbrev qz337 := (@HMul.hMul Real Real Real qz630 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz2 := qz337

theorem RS133to150.d35 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS133to150.d34 rfl 

noncomputable abbrev qz3 := (@Inv.inv Real Real.instInv qz337)

theorem RS133to150.d36 : Enclosure.Real.IsNear qz3 Bool.false 1335089 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 1335089 8388608 1 8388608 1335089 8388608 1 8388608 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 667544 667545 4194304 RS133to150.d35 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns132p64 := nat_lit 63107270706852208975020032 

noncomputable def Ns132p65 := nat_lit 17278883932877718361735168 

noncomputable abbrev qz844 := (Enclosure.sfrac Bool.false 373095 1000)

noncomputable abbrev qz631 := qz844

noncomputable abbrev qz338 := qz631

noncomputable abbrev qz4 := qz338

noncomputable abbrev qz339 := qz630

noncomputable abbrev qz5 := qz339

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 7)

noncomputable abbrev qz7 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz845 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 373095 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz632 := qz845

noncomputable abbrev qz340 := qz632

noncomputable abbrev qz8 := qz340

noncomputable abbrev qz9 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz846 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 373095 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz633 := qz846

noncomputable abbrev qz341 := qz633

noncomputable abbrev qz10 := qz341

noncomputable abbrev qz634 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz8 qz9))

noncomputable def Ns132p66 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 7) (@HMul.hMul Real Real Real qz5 qz634 (Zeta.RiemannSiegel.correction qz10)) 2328307 8388608 25015 16777216 3060197761195748643 18446744073709551616 4734437144030970458889 Ns132p64 Ns132p65 

noncomputable def Ns132p67 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 373095 1000 59 96 67108864 33554432 1125899906842624 Bool.false 38581667152 1215 

noncomputable def Ns132p68 := Ns132p67 120242927 40 27397080 8 130587807 40 25364760 8 Bool.true 55129033 37322 Bool.true 60920630 Bool.true 20212422 3537118876014220 1 Bool.false 52891467 Bool.false Bool.false 64087929 Bool.false Bool.true 9313228 

noncomputable def Ns132p69 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 373095 1000 36 16 67108864 33554432 1125899906842624 Bool.false 38581667152 1215 

noncomputable def Ns132p70 := Ns132p69 93032624 40 33554424 8 108007536 40 30011992 8 Bool.true 96327495 22015 Bool.false 76743446 Bool.true 28774778 3537118876014220 1 Bool.false 27806641 Bool.false Bool.false 61033810 Bool.false Bool.true 55129033 

noncomputable def Ns132p71 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 373095 1000 201 105 67108864 33554432 1125899906842624 Bool.false 38581667152 1215 

noncomputable def Ns132p72 := Ns132p71 46516304 40 47453136 16 73726608 40 38745320 8 Bool.true 67108856 1256 Bool.false 38380940 Bool.false 6130848 3537118876014220 1 Bool.false 36322537 Bool.true Bool.false 6122323 Bool.true Bool.true 96327495 

noncomputable def Ns132p73 := nat_lit 357560677684819689863039775516995480785803905044747 

noncomputable def Ns132p74 := nat_lit 621940228646779777606471840471529508349725900800 

noncomputable def Ns132p75 := nat_lit 35031572480000000000000000 

noncomputable def Ns132p76 := nat_lit 3470086957049960043955648500000000 

noncomputable def Ns132p77 := nat_lit 7768039070073254335283339472645000000 

noncomputable abbrev qz11 := (@Eq.refl Real qz338)

noncomputable def Ns132p78 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 373095 1000 556800516100 16000000 746190 4000 2000 Ns132p76 Ns132p77 qz11 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns132p79 := nat_lit 16090230495816886043836789898264796635361175727013615000000 

noncomputable abbrev qz847 := (@instHSub Real Real.instSub)

noncomputable abbrev qz635 := qz847

noncomputable abbrev qz342 := qz635

noncomputable abbrev qz12 := qz342

noncomputable abbrev qz343 := (Real.log (Enclosure.sfrac Bool.false 556800516100 16000000))

noncomputable abbrev qz344 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz345 := (@HMul.hMul Real Real Real qz630 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz346 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz347 := (Enclosure.sfrac Bool.false 373095 2000)

noncomputable abbrev qz13 := (@HSub.hSub Real Real Real qz342 (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 373095 4000) qz343) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 746190)))))) qz347)

noncomputable abbrev qz348 := (@HSub.hSub Real Real Real qz12 qz13 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 373095 2000) (Real.log Real.pi)))

noncomputable def Ns132p80 := @Enclosure.Real.IsNear.addLit_ft_p qz348 (Enclosure.sfrac Bool.true Ns132p76 Ns132p77) 2071339092527377420387 3602879701896396800 633420317993101028781 Ns132p75 Ns132p76 Ns132p77 0 1 Ns132p79 

noncomputable def Ns132p81 := nat_lit 27801042691660637516284402073600 

noncomputable abbrev qz349 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 373095 2000) (Real.log Real.pi))

noncomputable def Ns132p82 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz349 2840721434688034312291 3602879701896396800 952737691473714651 136842080000000000000000 2866172575059 13421772800 74619 6710886400 Ns132p81 2071339092527377420387 3602879701896396800 

noncomputable def Ns132p83 := nat_lit 5681442869376068624582000 

noncomputable abbrev qz14 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 373095 4000) qz343) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 746190))))))

noncomputable def Ns132p84 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz347 3512829635877552394339 3602879701896396800 952737691473714651 136842080000000000000000 373095 2000 0 1 Ns132p83 2840721434688034312291 3602879701896396800 952737691473714651 136842080000000000000000 

noncomputable def Ns132p85 := nat_lit 7910189119577090054796083481723011072 

noncomputable def Ns132p86 := nat_lit 12642188938923405251444736 

noncomputable def Ns132p87 := nat_lit 1208925819614629174706176 

noncomputable def Ns132p88 := nat_lit 20489731873828145353326236380493814957361500000000 

noncomputable def Ns132p89 := nat_lit 6180580743489299895035220424868478592800000000 

noncomputable def Ns132p90 := nat_lit 3352151017569073924209733908719472300000000 

noncomputable def Ns132p91 := BSN.log_dyadic_bound 32512516100 1081088516100 3 2 Ns132p88 33554432 13684208 Ns132p89 Ns132p90 2018832 1113601032200 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 32512516100) (BSN.artanhQ 1081088516100) 0 2 Ns132p89 Ns132p88 Ns132p90 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz350 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns132p92 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 373095 4000) qz343 373095 4000 0 1 47095823805493881 4503599627370496 12500002565789 171052600000000000000 3514243276542147906339 3602879701896396800 932737691456609391 136842080000000000000000 (Enclosure.Real.IsNear.const Bool.false 373095 4000) (BSN.isNear_log_sfrac 556800516100 16000000 47095823805493881 4503599627370496 12500002565789 171052600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 556800516100) qz350)) Bool.false Ns132p86 Ns132p87 1000000205263120 13684208000000000000000 47095823805493881 4503599627370496 12500002565789 171052600000000000000 (BSN.log_rat_reduce_isNear 556800516100 16000000 15 1113601032200 1048576000000 2018832 33554432 24973259072661432 36028797018963968 13684208 1000000000000000 rfl rfl rfl rfl (Ns132p91 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns132p93 := BSN.arctan_dyadic_bound_f 1000 746190 1 0 4194304 1710526 0 1 1 0 1 1 5620 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 746190) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 746190) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz15 := qz345

noncomputable abbrev qz16 := qz346

noncomputable abbrev qz351 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz17 := (@Enclosure.Real.IsNear.mulLit_ff qz351 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz352 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 746190)))

noncomputable def Ns132p94 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz352 884279719003555 562949953421312 1 2000000000000000 5620 4194304 1 1710526 3705774183797258977280 883525415372195 562949953421312 1000000000855263 1710526000000000000000 qz17 (Ns132p93 rfl) rfl rfl 

noncomputable abbrev qz18 := qz344

noncomputable abbrev qz353 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns132p95 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 373095 4000) qz343) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz352)) 3514243276542147906339 3602879701896396800 932737691456609391 136842080000000000000000 883525415372195 2251799813685248 1000000000855263 6842104000000000000000 Ns132p85 3512829635877552394339 3602879701896396800 952737691473714651 136842080000000000000000 (Ns132p92 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz352) 1 4 0 1 883525415372195 562949953421312 1000000000855263 1710526000000000000000 883525415372195 2251799813685248 1000000000855263 6842104000000000000000 qz353 Ns132p94 rfl) 

noncomputable def Ns132p96 := @Ns132p80 Ns132p73 Ns132p74 633420317993101028781 Ns132p75 (@Ns132p82 633420317993101028781 Ns132p75 (Ns132p84 (Ns132p95 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 373095 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz347 (Real.log Real.pi) 373095 2000 0 1 38410761 33554432 1 16777216 2866172575059 13421772800 74619 6710886400 (Enclosure.Real.IsNear.const Bool.false 373095 2000) RS133to150.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns132p76 Ns132p77) 

noncomputable abbrev qz354 := (@instHAdd Real Real.instAdd)

noncomputable def Ns132p97 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns132p73 Ns132p74 633420317993101028781 Ns132p75 2411354197 4194304 19 1048576 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz354 qz348 (Enclosure.sfrac Bool.true Ns132p76 Ns132p77)) Bool.false Ns132p73 Ns132p74 633420317993101028781 Ns132p75 Ns132p78 (Ns132p96 rfl rfl)) 

noncomputable def Ns132p98 := nat_lit 140055254885267937781768871233927963401961700176946024109004076504479165525412590240000 

noncomputable def Ns132p99 := nat_lit 2753733154729970958028337252922338050165611694356407771374444090804896824278383046164480 

noncomputable def Ns132p100 := nat_lit 281532584809092880696067310867764720379739214732363347771812883843378594608100000000 

noncomputable def Ns132p101 := nat_lit 366355567181248924764458172823644475553094398877672903436713455699794249127667479200000 

noncomputable def Ns132p102 := nat_lit 50485107836716134230519516303576197586369547729867475808531474998089775111770355846348800 

noncomputable abbrev qz355 := (BSN.sinEvenQ 17179869184)

noncomputable abbrev qz356 := (BSN.sinOddQ 17179869184)

noncomputable def Ns132p103 := BSN.sin_dyadic_bound_f 26989266610 17179869184 3 2 8388608 3424393 Ns132p98 Ns132p99 Ns132p100 Ns132p101 Ns132p102 Ns132p100 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26989266610) qz355 0 2 Ns132p98 Ns132p99 Ns132p100 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26989266610) qz356 0 2 Ns132p101 Ns132p102 Ns132p100 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz357 := (@Nat.cast Real Real.instNatCast 4194304)

noncomputable abbrev qz358 := (@Nat.cast Real Real.instNatCast 604462909807314587353088)

noncomputable def Ns132p104 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2411354197) qz357) Bool.false 2411354197 4194304 19 1048576 Bool.true 8388607 8388608 1 1710526 (Ns132p97 rfl) (Enclosure.sfrac_false_div 2411354197 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2411354197) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949600398843529327017984) qz358) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 91 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q1 2411354197 4194304 226375608064910080 72057594037927936 91 949600398843529327017984 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 949600398843529327017984 604462909807314587353088 26989266610 17179869184 3424393 3421052 (Ns132p103 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p105 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns132p73 Ns132p74 633420317993101028781 Ns132p75 38581667152 67108864 1215 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz354 qz348 (Enclosure.sfrac Bool.true Ns132p76 Ns132p77)) Bool.false Ns132p73 Ns132p74 633420317993101028781 Ns132p75 Ns132p78 (Ns132p96 rfl rfl)) 

noncomputable def Ns132p106 := Ns132p72 22015 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 201 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 36322537 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 105 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 6122323 67108864) qz11 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 8388607 8388608 16774285 896808255488 67108856 67108864 1256 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 8388607 8388608 16774285 896808255488 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 8388607 8388608 33548570 1793616510976 8388607 8388608 16774285 896808255488 (Ns132p104 rfl rfl) rfl)) rfl) (Ns132p105 rfl) RS133to150.d7 

noncomputable def Ns132p107 := nat_lit 133100328998971534320701618928981234141179261329722239721840640000 

noncomputable def Ns132p108 := nat_lit 149280173440179812144298804241602837812033797730278365202985810657280 

noncomputable def Ns132p109 := nat_lit 4708958421738896010637903967848469715764648105926681600000000 

noncomputable def Ns132p110 := nat_lit 348588475731290250722582254874241001418786827385672460834611200000 

noncomputable def Ns132p111 := nat_lit 2736803179736629889312144744429385359887286291721770028721406528716800 

noncomputable abbrev qz359 := (BSN.sinEvenQ 67108864)

noncomputable def Ns132p112 := BSN.sin_dyadic_bound_f 38380940 67108864 3 2 67108864 33554432 Ns132p107 Ns132p108 Ns132p109 Ns132p110 Ns132p111 Ns132p109 36322537 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 38380940) qz359 0 2 Ns132p107 Ns132p108 Ns132p109 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 38380940) (BSN.sinOddQ 67108864) 0 2 Ns132p110 Ns132p111 Ns132p109 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p113 := nat_lit 1412804910733771403418402816 

noncomputable def Ns132p114 := nat_lit 2433889152438200450873670154321920 

noncomputable def Ns132p115 := nat_lit 17037224067067403156115691080253440 

noncomputable def Ns132p116 := BSN.sin_dyadic_bound_f 6130848 67108864 2 1 67108864 33554432 Ns132p113 Ns132p114 Ns132p113 Ns132p113 Ns132p115 Ns132p113 6122323 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 6130848) qz359 0 1 Ns132p113 Ns132p114 Ns132p113 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 6130848) (BSN.sinOddQ 67108864) 0 1 Ns132p113 Ns132p115 Ns132p113 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p117 := nat_lit 285083409909816420984493674642363484407992003596573190415208212995030249272075825051241327833148624896 

noncomputable def Ns132p118 := nat_lit 3996645342911614855169325114413848961633120431781532997847909552396155328908156533147964360867027353600 

noncomputable def Ns132p119 := nat_lit 41734532822397148196467882545841016190616879002329763256637883710629083875095741415777366511616 

noncomputable def Ns132p120 := nat_lit 1728333275231566367433232054351955805650445868953893499802733065703549281634090865996743033948713062400 

noncomputable def Ns132p121 := nat_lit 363694726204956951820408585411660255508613959292119502804159769268050134930642244516464756838899489177600 

noncomputable abbrev qz360 := (BSN.cosEvenQ 67108864)

noncomputable def Ns132p122 := BSN.cos_dyadic_bound_f 76743446 67108864 4 3 67108864 33554432 Ns132p117 Ns132p118 Ns132p119 Ns132p120 Ns132p121 Ns132p119 27806641 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 76743446) qz360 0 3 Ns132p117 Ns132p118 Ns132p119 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 76743446) (BSN.cosOddQ 67108864) 0 3 Ns132p120 Ns132p121 Ns132p119 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p123 := nat_lit 23360680801639240816945385928135814922034460716398497753122447616 

noncomputable def Ns132p124 := nat_lit 16586685937797756904922089360178093090225977525586485022553978961920 

noncomputable def Ns132p125 := nat_lit 469997830828904927625993158109599358301124449847787539374336 

noncomputable def Ns132p126 := nat_lit 70081102409256064640980905798091225567386779900295797684288594176 

noncomputable def Ns132p127 := nat_lit 746400867200899060721494021208014189060168988651391826014929053286400 

noncomputable def Ns132p128 := BSN.cos_dyadic_bound_f 28774778 67108864 3 2 67108864 33554432 Ns132p123 Ns132p124 Ns132p125 Ns132p126 Ns132p127 Ns132p125 61033810 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 28774778) qz360 0 2 Ns132p123 Ns132p124 Ns132p125 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 28774778) (BSN.cosOddQ 67108864) 0 2 Ns132p126 Ns132p127 Ns132p125 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p129 := Ns132p70 37322 BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 27806641 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 16 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 61033810 67108864) qz11 rfl rfl (Ns132p106 RS133to150.d9 RS133to150.d11 RS133to150.d13 RS133to150.d17 (Ns132p112 rfl rfl) (Ns132p116 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns132p105 rfl) RS133to150.d19 RS133to150.d21 RS133to150.d23 RS133to150.d25 RS133to150.d17 (Ns132p122 rfl rfl) (Ns132p128 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns132p130 := nat_lit 844999396777001580996883335158062383021270452459963779224430240000 

noncomputable def Ns132p131 := nat_lit 189720861008431779501825787706765867695328941355117952100000000 

noncomputable def Ns132p132 := nat_lit 2212786491117180965444072445567209572698487319109139706998679200000 

noncomputable def Ns132p133 := BSN.sin_dyadic_bound_f 60920630 67108864 3 2 67108864 33554432 Ns132p130 Ns132p108 Ns132p131 Ns132p132 Ns132p111 Ns132p131 52891467 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 60920630) qz359 0 2 Ns132p130 Ns132p108 Ns132p131 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 60920630) (BSN.sinOddQ 67108864) 0 2 Ns132p132 Ns132p111 Ns132p131 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p134 := nat_lit 166906568301931548703757815056 

noncomputable def Ns132p135 := nat_lit 486777830487640090174734030864384 

noncomputable def Ns132p136 := nat_lit 7301667457314601352621010462965760 

noncomputable def Ns132p137 := BSN.cos_dyadic_bound_f 20212422 67108864 2 1 67108864 33554432 Ns132p134 Ns132p135 Ns132p134 Ns132p134 Ns132p136 Ns132p134 64087929 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 20212422) qz360 0 1 Ns132p134 Ns132p135 Ns132p134 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 20212422) (BSN.cosOddQ 67108864) 0 1 Ns132p134 Ns132p136 Ns132p134 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p138 := Ns132p68 50030 BSN.abs_quadSignPos (BSN.cos_quad_nat3 59 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 52891467 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 96 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 64087929 67108864) qz11 rfl rfl (Ns132p129 rfl rfl) (Ns132p105 rfl) RS133to150.d27 RS133to150.d29 RS133to150.d31 RS133to150.d33 RS133to150.d17 (Ns132p133 rfl rfl) (Ns132p137 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns132p139 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 7) 9313228 67108864 50030 67108864 9313228 67108864 50030 67108864 1250000302505984 2328307 8388608 25015 16777216 (Ns132p138 rfl) 

noncomputable def Ns132p140 := @Enclosure.Real.IsNear.mulLit_tf qz634 (Zeta.RiemannSiegel.correction qz10) 3021899 8388608 1 8388608 1012673739657 2199023255552 6262249226656831 30091891625810722816 3060197761195748643 18446744073709551616 

noncomputable abbrev qz636 := (@HPow.hPow Real Real Real qz7 qz8 qz9)

noncomputable def Ns132p141 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz636 1 1 0 1 3021899 8388608 1 8388608 3021899 8388608 1 8388608 

noncomputable abbrev qz361 := (@Enclosure.Real.IsNear.of_eq qz8 (@HMul.hMul Real Real Real qz5 qz4 qz3) Bool.false 99623006091 1677721600 74619 1677721600 (BSN.t_div_two_pi_mk qz4 373095 1000 qz11) (@Enclosure.Real.IsNear.mulLit_ff qz4 qz3 373095 1000 0 1 1335089 8388608 1 8388608 99623006091 1677721600 74619 1677721600 (Enclosure.Real.IsNear.const Bool.false 373095 1000) RS133to150.d36 rfl))

noncomputable def Ns132p142 := @Enclosure.Real.IsNear.sqrt_image qz8 99623006091 1677721600 74619 1677721600 32320614 32320640 4194304 qz361 

noncomputable abbrev qz848 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 373095 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz637 := qz848

noncomputable abbrev qz362 := qz637

noncomputable abbrev qz19 := qz362

noncomputable def Ns132p143 := @Enclosure.Real.IsNear.sqrt_image qz19 32320627 4194304 13 4194304 11643130 11643135 4194304 (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 64641254 8388608 26 8388608 32320627 4194304 13 4194304 (Ns132p142 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz638 := (Real.sqrt qz848)

noncomputable abbrev qz363 := qz638

noncomputable abbrev qz20 := qz363

noncomputable def Ns132p144 := @Enclosure.Real.IsNear.inv_image qz20 23286265 8388608 5 8388608 1510949 1510950 4194304 (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 23286265 8388608 5 8388608 23286265 8388608 5 8388608 (Ns132p143 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns132p145 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz20) Bool.false 3021899 8388608 1 8388608 3021899 8388608 1 8388608 (Ns132p144 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz21 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz341))

noncomputable abbrev qz639 := (@HMul.hMul Real Real Real qz843 qz846 qz846)

noncomputable abbrev qz640 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz364 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz639 qz633) qz640)

noncomputable abbrev qz22 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz364))

noncomputable def Ns132p146 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz10) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz21) qz22) Bool.false 1012673739657 

noncomputable def Ns132p147 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz21) qz22 30623053 8388608 2265 

noncomputable abbrev qz641 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz21))

noncomputable def Ns132p148 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz21) (@Neg.neg Real Real.instNeg qz641) Bool.true 30623053 8388608 2265 8388608 (BSN.inv_eq_neg_inv_neg qz21) 

noncomputable def Ns132p149 := @Enclosure.Real.IsNear.recentre' qz641 Bool.false 30623053 8388608 2265 8388608 30623053 8388608 

noncomputable def Ns132p150 := @Enclosure.Real.IsNear.recentre' qz21 Bool.true 2297901 8388608 290625398 14348932087808 2297901 8388608 145312699 7174466043904 

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz339 qz337 qz341)

noncomputable abbrev qz365 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable def Ns132p151 := @Enclosure.Real.IsNear.cos_image qz23 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 37202727) qz365) Bool.false 37202727 8388608 165 8388608 Bool.true 2297901 8388608 1 

noncomputable def Ns132p152 := nat_lit 350818980343003083686877979 

noncomputable def Ns132p153 := nat_lit 18014398509481984000000000000000 

noncomputable def Ns132p154 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz10 884279719003555 140737488355328 1 500000000000000 2960499 4194304 13 4194304 2617909223830305573945 590295810358705651712 Ns132p152 

noncomputable def Ns132p155 := @Enclosure.Real.IsNear.subLit_ff_p qz19 qz1 32320627 4194304 13 4194304 7 1 0 1 2960499 2960499 4194304 13 

noncomputable abbrev qz366 := (Enclosure.Real.IsNear.const Bool.false 7 1)

noncomputable def Ns132p156 := @Ns132p155 4194304 (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 64641254 8388608 26 8388608 32320627 4194304 13 4194304 (Ns132p142 rfl rfl rfl rfl rfl rfl) rfl) qz366 

noncomputable def Ns132p157 := @Enclosure.Real.IsNear.recentre' qz23 Bool.false 2617909223830305573945 590295810358705651712 Ns132p152 Ns132p153 37202727 8388608 165 8388608 (@Ns132p154 Ns132p153 RS133to150.d35 (Ns132p156 rfl rfl) rfl) 

noncomputable def Ns132p158 := nat_lit 1563525524903382864625664 

noncomputable def Ns132p159 := nat_lit 35728275426465517507506852521938412088185372929146393240982452187188346453276530099361 

noncomputable def Ns132p160 := nat_lit 305970350525552328669815250324704227796179077150711974597160454533877424919820338462720 

noncomputable def Ns132p161 := nat_lit 59402045519426627052901993851546268844836786758785100114411450593534958072083563681 

noncomputable def Ns132p162 := nat_lit 107066022188357699268414753578112143726866445213921609522718533660377969443685423170721 

noncomputable def Ns132p163 := nat_lit 13768665773649854790141686264611690250828058471782038856872220454024484121391915230822400 

noncomputable def Ns132p164 := BSN.cos_dyadic_bound_f 22219034077 17179869184 3 2 8388608 3424393 Ns132p159 Ns132p160 Ns132p161 Ns132p162 Ns132p163 Ns132p161 2297901 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 22219034077) (BSN.cosEvenQ 17179869184) 0 2 Ns132p159 Ns132p160 Ns132p161 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 22219034077) (BSN.cosOddQ 17179869184) 0 2 Ns132p162 Ns132p163 Ns132p161 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz367 := (@Nat.cast Real Real.instNatCast Ns132p87)

noncomputable def Ns132p165 := @Ns132p151 1710526 (Ns132p157 rfl) (Enclosure.sfrac_false_div 37202727 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 37202727) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns132p158) qz367) 226375608064910080 72057594037927936 Bool.false 2297901 8388608 0 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q2 37202727 8388608 226375608064910080 72057594037927936 0 Ns132p158 Ns132p87 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 2297901 8388608 Ns132p158 Ns132p87 22219034077 17179869184 3424393 3421052 (Ns132p164 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p166 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz21) 2297901 8388608 145312699 7174466043904 15310394 15312659 4194304 (@Enclosure.Real.IsNear.neg qz21 Bool.true 2297901 8388608 145312699 7174466043904 (Ns132p150 (Ns132p165 rfl rfl) rfl)) 

noncomputable def Ns132p167 := Ns132p148 (@Enclosure.Real.IsNear.neg qz641 Bool.false 30623053 8388608 2265 8388608 (@Ns132p149 2265 8388608 (Ns132p166 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns132p168 := @Enclosure.Real.IsNear.recentre' qz22 Bool.true 529104 4194304 

noncomputable abbrev qz24 := (@HMul.hMul Real Real Real qz339 qz337 qz364)

noncomputable abbrev qz368 := (@Nat.cast Real Real.instNatCast 2097152)

noncomputable def Ns132p169 := @Enclosure.Real.IsNear.cos_image qz24 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 3559457)) qz368) Bool.true 3559457 2097152 

noncomputable def Ns132p170 := nat_lit 4202265323158852807441954405 

noncomputable def Ns132p171 := nat_lit 2475880078570760549798248448 

noncomputable def Ns132p172 := nat_lit 3548644493931867794591018292609697 

noncomputable def Ns132p173 := @Enclosure.Real.IsNear.recentre' qz24 Bool.true Ns132p170 Ns132p171 Ns132p172 

noncomputable def Ns132p174 := nat_lit 75557863725914323419136000000000000000 

noncomputable abbrev qz25 := qz364

noncomputable def Ns132p175 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz25 884279719003555 140737488355328 1 500000000000000 4752190096471 

noncomputable abbrev qz369 := (@HSub.hSub Real Real Real qz635 qz639 qz633)

noncomputable abbrev qz26 := qz369

noncomputable abbrev qz370 := qz640

noncomputable abbrev qz27 := qz370

noncomputable def Ns132p176 := @Enclosure.Real.IsNear.subLit_tf qz26 qz27 3652678468695 17592186044416 131499095 17592186044416 1 16 

noncomputable abbrev qz371 := qz639

noncomputable abbrev qz28 := qz371

noncomputable def Ns132p177 := @Enclosure.Real.IsNear.subLit_ff_n qz28 qz10 8764554329001 17592186044416 76973143 17592186044416 2960499 4194304 13 4194304 

noncomputable def Ns132p178 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz10 2960499 4194304 13 4194304 2960499 4194304 13 4194304 8764554329001 17592186044416 

noncomputable def Ns132p179 := nat_lit 1204596283195567395319882937927065641881680899931034712889665909732067765657848170881 

noncomputable def Ns132p180 := nat_lit 3466537250751077332112698720796095110148055492926080949987665366995300109908547993600 

noncomputable def Ns132p181 := nat_lit 4136233138477036082050166925596237078380023207519674850940076428835298024278401 

noncomputable def Ns132p182 := nat_lit 7283915397827055834128163621897652953431146738296286119088395844013668692711192054145 

noncomputable def Ns132p183 := nat_lit 315454889818348037222255583592444655023473049856273366448877548396572310001677867417600 

noncomputable def Ns132p184 := BSN.cos_dyadic_bound_t 3559457 2097152 4 3 4194304 1710526 Ns132p179 Ns132p180 Ns132p181 Ns132p182 Ns132p183 Ns132p181 529104 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 3559457) (BSN.cosEvenQ 2097152) 0 3 Ns132p179 Ns132p180 Ns132p181 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 3559457) (BSN.cosOddQ 2097152) 0 3 Ns132p182 Ns132p183 Ns132p181 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz372 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns132p185 := @Ns132p168 684046378 14348932087808 33069 262144 342023189 7174466043904 (@Ns132p169 395 8388608 Bool.true 529104 4194304 1 1710526 (@Ns132p173 Ns132p174 3559457 2097152 395 8388608 (@Ns132p175 17592186044416 131499095 17592186044416 Ns132p170 Ns132p171 Ns132p172 Ns132p174 RS133to150.d35 (@Ns132p176 0 1 76035041543536 4752190096471 17592186044416 131499095 17592186044416 (@Ns132p177 15320443911961313280 3652678468695 17592186044416 131499095 17592186044416 (@Ns132p178 76973143 17592186044416 (Ns132p156 rfl rfl) (Ns132p156 rfl rfl) rfl) (Ns132p156 rfl rfl) rfl rfl) qz372 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 3559457 2097152) (BSN.cos_neg_of_bound 3559457 2097152 Bool.true 529104 4194304 1 1710526 (Ns132p184 rfl rfl)) rfl rfl) 

noncomputable abbrev qz29 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 7) (Enclosure.sfrac Bool.true 1 1) Bool.true 1 1 0 1 (BSN.neg_one_pow_odd_mk 7 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1))

noncomputable def Ns132p186 := @Ns132p140 4734437144030970458889 Ns132p64 (Ns132p141 qz29 (@Enclosure.Real.IsNear.of_eq qz636 (@Inv.inv Real Real.instInv qz20) Bool.false 3021899 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz8 (BSN.t_div_two_pi_nonneg qz4 373095 1000 qz11)) Ns132p145) rfl) (@Ns132p146 2199023255552 6262249226656831 30091891625810722816 (BSN.correction_mk qz10 (BSN.cos_two_pi_p_ne_zero_mk qz4 373095 1000 7 qz11 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 373095 1000 7 qz11 rfl rfl rfl))) (@Ns132p147 8388608 33069 262144 342023189 7174466043904 1012673739657 2199023255552 6262249226656831 30091891625810722816 Ns132p167 (Ns132p185 rfl) rfl)) 

noncomputable def Ns132p187 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 2059803477868761821 18446744073709551616 98828020771487874364169 Ns132p64 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 7) (@HMul.hMul Real Real Real qz5 qz634 (Zeta.RiemannSiegel.correction qz10))) Bool.true 2059803477868761821 18446744073709551616 98828020771487874364169 Ns132p64 (BSN.hardyZApproximantRS₀_eq qz4 7 (@BSN.floor_sqrt_eq_dec qz4 373095 1000 7 qz11 rfl rfl rfl)) (@Ns132p66 2059803477868761821 18446744073709551616 98828020771487874364169 Ns132p64 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 7)) Bool.true 2328307 8388608 25015 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 7) (Ns132p139 (Ns132p138 rfl) rfl rfl)) (Ns132p186 rfl) rfl rfl)) 

theorem RS133to150.d37 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 2059803477868761821 18446744073709551616 98828020771487874364169 Ns132p64 := Ns132p187 

theorem RS133to150.d38 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS133to150.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS133to150.d3 a b h)) 

noncomputable def Ns132p188 := nat_lit 126214541413704417950040064 

noncomputable def Ns132p189 := nat_lit 9006631488005212663311237120 

noncomputable abbrev qz849 := (Enclosure.sfrac Bool.false 374633 1000)

noncomputable abbrev qz642 := qz849

noncomputable abbrev qz373 := qz642

noncomputable abbrev qz30 := qz373

noncomputable abbrev qz850 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 374633 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz643 := qz850

noncomputable abbrev qz374 := qz643

noncomputable abbrev qz31 := qz374

noncomputable abbrev qz851 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 374633 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz644 := qz851

noncomputable abbrev qz375 := qz644

noncomputable abbrev qz32 := qz375

noncomputable abbrev qz645 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz31 qz9))

noncomputable def Ns132p190 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz30) qz30 7) (@HMul.hMul Real Real Real qz5 qz645 (Zeta.RiemannSiegel.correction qz32)) 55311987 33554432 12559 8388608 25153843785119491137 147573952589676412928 14308426511584395346547 Ns132p188 Ns132p189 

noncomputable def Ns132p191 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz30) qz30 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 374633 1000 59 96 67108864 33554432 1125899906842624 Bool.false 38792532914 1219 

noncomputable def Ns132p192 := Ns132p191 120242927 40 27397080 8 130587807 40 25364760 8 Bool.false 16593511 37476 Bool.true 34988489 Bool.true 10190707 3537118876014220 1 Bool.false 33424765 Bool.false Bool.false 66336603 Bool.false Bool.false 55311987 

noncomputable def Ns132p193 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz30) qz30 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 374633 1000 37 15 67108864 33554432 1125899906842624 Bool.false 38792532914 1219 

noncomputable def Ns132p194 := Ns132p193 93032624 40 33554424 8 108007536 40 30011992 8 Bool.false 5894870 22107 Bool.false 39110675 Bool.true 89438964 3537118876014220 1 Bool.false 36933985 Bool.true Bool.false 65216339 Bool.false Bool.false 16593511 

noncomputable def Ns132p195 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz30) qz30 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 374633 1000 202 105 67108864 33554432 1125899906842624 Bool.false 38792532914 1219 

noncomputable def Ns132p196 := Ns132p195 46516304 40 47453136 16 73726608 40 38745320 8 Bool.false 67108840 1264 Bool.false 72290270 Bool.false 103605087 3537118876014220 1 Bool.false 31795380 Bool.true Bool.false 67084476 Bool.true Bool.false 5894870 

noncomputable def Ns132p197 := nat_lit 259100962662154323183036965355906350098351910974968747977 

noncomputable def Ns132p198 := nat_lit 448229851449818818021472262754548887065477999755264000 

noncomputable def Ns132p199 := nat_lit 175157862400000000000000000 

noncomputable def Ns132p200 := nat_lit 3542202192462671510325664828640000 

noncomputable def Ns132p201 := nat_lit 7962161622462439290285947328743334720 

noncomputable abbrev qz376 := (@Eq.refl Real qz642)

noncomputable abbrev qz33 := qz376

noncomputable def Ns132p202 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz30 374633 1000 561400538756 16000000 749266 4000 2000 Ns132p200 Ns132p201 qz33 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns132p203 := nat_lit 82912308051889383418571828913890032031472611511989999352640 

noncomputable abbrev qz377 := (Real.log (Enclosure.sfrac Bool.false 561400538756 16000000))

noncomputable abbrev qz378 := (Enclosure.sfrac Bool.false 374633 2000)

noncomputable abbrev qz34 := (@HSub.hSub Real Real Real qz342 (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 374633 4000) qz377) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 749266)))))) qz378)

noncomputable abbrev qz379 := (@HSub.hSub Real Real Real qz12 qz34 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 374633 2000) (Real.log Real.pi)))

noncomputable def Ns132p204 := @Enclosure.Real.IsNear.addLit_ft_p qz379 (Enclosure.sfrac Bool.true Ns132p200 Ns132p201) 10413299276495867251937 18014398509481984000 3180051721822896084047 Ns132p199 Ns132p200 Ns132p201 0 1 Ns132p203 

noncomputable def Ns132p205 := nat_lit 139764936987531910394458773913600 

noncomputable abbrev qz380 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 374633 2000) (Real.log Real.pi))

noncomputable def Ns132p206 := @Enclosure.Real.IsNear.subLit_ff_p qz34 qz380 2855213802660229946413 3602879701896396800 4782913461314756737 684210400000000000000000 14389938625713 67108864000 374633 33554432000 Ns132p205 10413299276495867251937 18014398509481984000 

noncomputable def Ns132p207 := nat_lit 28552138026602299464130000 

noncomputable abbrev qz35 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 374633 4000) qz377) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 749266))))))

noncomputable def Ns132p208 := @Enclosure.Real.IsNear.subLit_ff_p qz35 qz378 17650463091702531788001 18014398509481984000 4782913461314756737 684210400000000000000000 374633 2000 0 1 Ns132p207 2855213802660229946413 3602879701896396800 4782913461314756737 684210400000000000000000 

noncomputable def Ns132p209 := nat_lit 39745309501354107464510183946477109248 

noncomputable def Ns132p210 := nat_lit 12652135480974024672018432 

noncomputable def Ns132p211 := nat_lit 20840698544029317596246128145711928243656493469440 

noncomputable def Ns132p212 := nat_lit 8123182632883151576326923688269906796977850368 

noncomputable def Ns132p213 := nat_lit 5691200830836703776755258553396102306693888 

noncomputable def Ns132p214 := BSN.log_dyadic_bound 37112538756 1085688538756 3 2 Ns132p211 33554432 13684208 Ns132p212 Ns132p213 2294904 1122801077512 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 37112538756) (BSN.artanhQ 1085688538756) 0 2 Ns132p212 Ns132p211 Ns132p213 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns132p215 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 374633 4000) qz377 374633 4000 0 1 47132877562098297 4503599627370496 12500002565789 171052600000000000000 17657531319721571300001 18014398509481984000 4682913461229230437 684210400000000000000000 (Enclosure.Real.IsNear.const Bool.false 374633 4000) (BSN.isNear_log_sfrac 561400538756 16000000 47132877562098297 4503599627370496 12500002565789 171052600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 561400538756) qz350)) Bool.false Ns132p210 Ns132p87 1000000205263120 13684208000000000000000 47132877562098297 4503599627370496 12500002565789 171052600000000000000 (BSN.log_rat_reduce_isNear 561400538756 16000000 15 1122801077512 1048576000000 2294904 33554432 24973259072661432 36028797018963968 13684208 1000000000000000 rfl rfl rfl rfl (Ns132p214 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns132p216 := BSN.arctan_dyadic_bound_f 1000 749266 1 0 4194304 1710526 0 1 1 0 1 1 5597 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 749266) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 749266) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz381 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 749266)))

noncomputable def Ns132p217 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz381 884279719003555 562949953421312 1 2000000000000000 5597 4194304 1 1710526 3705787131646187667456 883528502379939 562949953421312 1000000000855263 1710526000000000000000 qz17 (Ns132p216 rfl) rfl rfl 

noncomputable def Ns132p218 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 374633 4000) qz377) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz381)) 17657531319721571300001 18014398509481984000 4682913461229230437 684210400000000000000000 883528502379939 2251799813685248 1000000000855263 6842104000000000000000 Ns132p209 17650463091702531788001 18014398509481984000 4782913461314756737 684210400000000000000000 (Ns132p215 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz381) 1 4 0 1 883528502379939 562949953421312 1000000000855263 1710526000000000000000 883528502379939 2251799813685248 1000000000855263 6842104000000000000000 qz353 Ns132p217 rfl) 

noncomputable def Ns132p219 := @Ns132p204 Ns132p197 Ns132p198 3180051721822896084047 Ns132p199 (@Ns132p206 3180051721822896084047 Ns132p199 (Ns132p208 (Ns132p218 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 374633 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz378 (Real.log Real.pi) 374633 2000 0 1 38410761 33554432 1 16777216 14389938625713 67108864000 374633 33554432000 (Enclosure.Real.IsNear.const Bool.false 374633 2000) RS133to150.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns132p200 Ns132p201) 

noncomputable def Ns132p220 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz30) Bool.false Ns132p197 Ns132p198 3180051721822896084047 Ns132p199 2424533307 4194304 153 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz30) (@HAdd.hAdd Real Real Real qz354 qz379 (Enclosure.sfrac Bool.true Ns132p200 Ns132p201)) Bool.false Ns132p197 Ns132p198 3180051721822896084047 Ns132p199 Ns132p202 (Ns132p219 rfl rfl)) 

noncomputable def Ns132p221 := nat_lit 140252610868515524652836877527497954837342637926507717736128511982399432426141075374080 

noncomputable def Ns132p222 := nat_lit 282324979343858321110970467660337965679507075280298454157324705457426973855271878656 

noncomputable def Ns132p223 := nat_lit 366871168974793460618488346100568382153368659304685444192653291383162679348889519128576 

noncomputable def Ns132p224 := BSN.sin_dyadic_bound_f 26998750352 17179869184 3 2 8388608 3424393 Ns132p221 Ns132p99 Ns132p222 Ns132p223 Ns132p102 Ns132p222 8388605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26998750352) qz355 0 2 Ns132p221 Ns132p99 Ns132p222 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26998750352) qz356 0 2 Ns132p223 Ns132p102 Ns132p222 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p225 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz30) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2424533307) qz357) Bool.false 2424533307 4194304 153 8388608 Bool.false 8388605 8388608 1 1710526 (Ns132p220 rfl) (Enclosure.sfrac_false_div 2424533307 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2424533307) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949934078347752991883264) qz358) 226375608064910080 72057594037927936 Bool.false 8388605 8388608 91 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 2424533307 4194304 226375608064910080 72057594037927936 91 949934078347752991883264 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388605 8388608 949934078347752991883264 604462909807314587353088 26998750352 17179869184 3424393 3421052 (Ns132p224 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p226 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz30) Bool.false Ns132p197 Ns132p198 3180051721822896084047 Ns132p199 38792532914 67108864 1219 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz30) (@HAdd.hAdd Real Real Real qz354 qz379 (Enclosure.sfrac Bool.true Ns132p200 Ns132p201)) Bool.false Ns132p197 Ns132p198 3180051721822896084047 Ns132p199 Ns132p202 (Ns132p219 rfl rfl)) 

noncomputable def Ns132p227 := Ns132p196 22107 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 202 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 31795380 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 105 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 67084476 67108864) qz33 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 1) Bool.false 8388605 8388608 135049543 7174466043904 67108840 67108864 1264 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz30)) Bool.false 8388605 8388608 135049543 7174466043904 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz30) qz30) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz30)) Bool.false 8388605 8388608 270099086 14348932087808 8388605 8388608 135049543 7174466043904 (Ns132p225 rfl rfl) rfl)) rfl) (Ns132p226 rfl) RS133to150.d7 

noncomputable def Ns132p228 := nat_lit 931314050848850474895933923620017798574195253347957931422640800000 

noncomputable def Ns132p229 := nat_lit 745828155987972037886678725506609130064379145103743248100000000 

noncomputable def Ns132p230 := nat_lit 2792450496234575480612028413409040177462457001753666307771722400000 

noncomputable def Ns132p231 := BSN.cos_dyadic_bound_f 72290270 67108864 3 2 67108864 33554432 Ns132p228 Ns132p124 Ns132p229 Ns132p230 Ns132p127 Ns132p229 31795380 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 72290270) qz360 0 2 Ns132p228 Ns132p124 Ns132p229 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 72290270) (BSN.cosOddQ 67108864) 0 2 Ns132p230 Ns132p127 Ns132p229 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p232 := nat_lit 2464210682899877538114332213866196796257831224832601608560960837818338903881006321938834371765412241281 

noncomputable def Ns132p233 := nat_lit 51956389457850993117201226487380036501230565613159928972022824181150019275806034930923536691271355596800 

noncomputable def Ns132p234 := nat_lit 1529582679008582397050497971849837185476266588888733912857390578657054760718620984743889595998081 

noncomputable def Ns132p235 := nat_lit 12306765865941082898914409613132176988125494873176275460124460799088750186134200818328988602674635808641 

noncomputable def Ns132p236 := nat_lit 1818473631024784759102042927058301277543069796460597514020798846340250674653211222582323784194497445888000 

noncomputable def Ns132p237 := BSN.sin_dyadic_bound_f 103605087 67108864 4 3 67108864 33554432 Ns132p232 Ns132p233 Ns132p234 Ns132p235 Ns132p236 Ns132p234 67084476 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 103605087) qz359 0 3 Ns132p232 Ns132p233 Ns132p234 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 103605087) (BSN.sinOddQ 67108864) 0 3 Ns132p235 Ns132p236 Ns132p234 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p238 := nat_lit 143515612512634899075556957583000760839409133006225475930925390625 

noncomputable def Ns132p239 := nat_lit 5474727293872458757879508552689764483865328497631988525390625 

noncomputable def Ns132p240 := nat_lit 375865359403187037407517369703535733055954804484451508980525390625 

noncomputable def Ns132p241 := BSN.sin_dyadic_bound_f 39110675 67108864 3 2 67108864 33554432 Ns132p238 Ns132p108 Ns132p239 Ns132p240 Ns132p111 Ns132p239 36933985 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 39110675) qz359 0 2 Ns132p238 Ns132p108 Ns132p239 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 39110675) (BSN.sinOddQ 67108864) 0 2 Ns132p240 Ns132p111 Ns132p239 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p242 := nat_lit 3928811890124385144433221529332711080481014298176251863349764096000 

noncomputable def Ns132p243 := nat_lit 4094624493546832194590846168943052377912678340244347847620755456 

noncomputable def Ns132p244 := nat_lit 10283116034479075745200528349693097411695559777910740221781805694976 

noncomputable def Ns132p245 := BSN.sin_dyadic_bound_f 89438964 67108864 3 2 67108864 33554432 Ns132p242 Ns132p108 Ns132p243 Ns132p244 Ns132p111 Ns132p243 65216339 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 89438964) qz359 0 2 Ns132p242 Ns132p108 Ns132p243 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 89438964) (BSN.sinOddQ 67108864) 0 2 Ns132p244 Ns132p111 Ns132p243 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p246 := Ns132p194 37476 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 37 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 36933985 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 15 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 65216339 67108864) qz33 rfl rfl (Ns132p227 RS133to150.d9 RS133to150.d11 RS133to150.d13 RS133to150.d17 (Ns132p231 rfl rfl) (Ns132p237 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns132p226 rfl) RS133to150.d19 RS133to150.d21 RS133to150.d23 RS133to150.d25 RS133to150.d17 (Ns132p241 rfl rfl) (Ns132p245 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns132p247 := nat_lit 91920567692408716963934249904091880106438922285378780391350089025 

noncomputable def Ns132p248 := nat_lit 2245957329096245787351540108151318350978526525447529537090881 

noncomputable def Ns132p249 := nat_lit 240740707644442388602838752017208393382390831228284176453333038401 

noncomputable def Ns132p250 := BSN.sin_dyadic_bound_f 34988489 67108864 3 2 67108864 33554432 Ns132p247 Ns132p108 Ns132p248 Ns132p249 Ns132p111 Ns132p248 33424765 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 34988489) qz359 0 2 Ns132p247 Ns132p108 Ns132p248 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 34988489) (BSN.sinOddQ 67108864) 0 2 Ns132p249 Ns132p111 Ns132p248 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p251 := nat_lit 10784928252759881051833702801 

noncomputable def Ns132p252 := BSN.cos_dyadic_bound_f 10190707 67108864 2 1 67108864 33554432 Ns132p251 Ns132p135 Ns132p251 Ns132p251 Ns132p136 Ns132p251 66336603 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 10190707) qz360 0 1 Ns132p251 Ns132p135 Ns132p251 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 10190707) (BSN.cosOddQ 67108864) 0 1 Ns132p251 Ns132p136 Ns132p251 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p253 := Ns132p192 50236 BSN.abs_quadSignPos (BSN.cos_quad_nat3 59 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 33424765 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 96 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66336603 67108864) qz33 rfl rfl (Ns132p246 rfl rfl) (Ns132p226 rfl) RS133to150.d27 RS133to150.d29 RS133to150.d31 RS133to150.d33 RS133to150.d17 (Ns132p250 rfl rfl) (Ns132p252 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns132p254 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 7) 55311987 67108864 50236 67108864 55311987 67108864 50236 67108864 7423849226305536 55311987 33554432 12559 8388608 (Ns132p253 rfl) 

noncomputable def Ns132p255 := @Enclosure.Real.IsNear.mulLit_tf qz645 (Zeta.RiemannSiegel.correction qz32) 3018793 8388608 1 8388608 8332417554009 17592186044416 2368710833390735 7522972906452680704 25153843785119491137 147573952589676412928 

noncomputable abbrev qz646 := (@HPow.hPow Real Real Real qz7 qz31 qz9)

noncomputable def Ns132p256 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz646 1 1 0 1 3018793 8388608 1 8388608 3018793 8388608 1 8388608 

noncomputable def Ns132p257 := @Enclosure.Real.IsNear.sqrt_image qz31 500168397337 8388608000 374633 8388608000 32387163 32387188 4194304 (@Enclosure.Real.IsNear.of_eq qz31 (@HMul.hMul Real Real Real qz5 qz30 qz3) Bool.false 500168397337 8388608000 374633 8388608000 (BSN.t_div_two_pi_mk qz30 374633 1000 qz33) (@Enclosure.Real.IsNear.mulLit_ff qz30 qz3 374633 1000 0 1 1335089 8388608 1 8388608 500168397337 8388608000 374633 8388608000 (Enclosure.Real.IsNear.const Bool.false 374633 1000) RS133to150.d36 rfl)) 

noncomputable abbrev qz852 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 374633 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz647 := qz852

noncomputable abbrev qz382 := qz647

noncomputable abbrev qz36 := qz382

noncomputable def Ns132p258 := @Enclosure.Real.IsNear.sqrt_image qz36 64774351 8388608 25 8388608 11655110 11655116 4194304 (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 64774351 8388608 25 8388608 64774351 8388608 25 8388608 (Ns132p257 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns132p259 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz36) 11655113 4194304 3 4194304 1509396 1509397 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz36) Bool.false 23310226 8388608 6 8388608 11655113 4194304 3 4194304 (Ns132p258 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns132p260 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz36)) Bool.false 3018793 8388608 1 8388608 3018793 8388608 1 8388608 (Ns132p259 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz37 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz375))

noncomputable abbrev qz648 := (@HMul.hMul Real Real Real qz843 qz851 qz851)

noncomputable abbrev qz383 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz648 qz644) qz640)

noncomputable abbrev qz38 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz383))

noncomputable def Ns132p261 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz32) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz37) qz38) Bool.false 8332417554009 

noncomputable def Ns132p262 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz37) qz38 47433027 8388608 5209 

noncomputable abbrev qz649 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz37))

noncomputable def Ns132p263 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz37) (@Neg.neg Real Real.instNeg qz649) Bool.true 47433027 8388608 5209 8388608 (BSN.inv_eq_neg_inv_neg qz37) 

noncomputable def Ns132p264 := @Enclosure.Real.IsNear.recentre' qz649 Bool.false 47433027 8388608 5209 8388608 47433027 8388608 

noncomputable def Ns132p265 := @Enclosure.Real.IsNear.recentre' qz37 Bool.true 1483539 8388608 139325858 7174466043904 1483539 8388608 69662929 3587233021952 

noncomputable abbrev qz39 := (@HMul.hMul Real Real Real qz339 qz337 qz375)

noncomputable abbrev qz384 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable def Ns132p266 := @Enclosure.Real.IsNear.cos_image qz39 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4754875) qz384) Bool.false 4754875 1048576 79 4194304 Bool.true 1483539 8388608 1 

noncomputable def Ns132p267 := nat_lit 134930377055621083288595683 

noncomputable def Ns132p268 := nat_lit 7205759403792793600000000000000 

noncomputable def Ns132p269 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz32 884279719003555 140737488355328 1 500000000000000 6054095 8388608 25 8388608 5353513425420827307725 1180591620717411303424 Ns132p267 

noncomputable def Ns132p270 := @Enclosure.Real.IsNear.subLit_ff_p qz36 qz1 64774351 8388608 25 8388608 7 1 0 1 6054095 6054095 8388608 25 

noncomputable def Ns132p271 := @Ns132p270 8388608 (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 64774351 8388608 25 8388608 64774351 8388608 25 8388608 (Ns132p257 rfl rfl rfl rfl rfl rfl) rfl) qz366 

noncomputable def Ns132p272 := @Enclosure.Real.IsNear.recentre' qz39 Bool.false 5353513425420827307725 1180591620717411303424 Ns132p267 Ns132p268 4754875 1048576 79 4194304 (@Ns132p269 Ns132p268 RS133to150.d35 (Ns132p271 rfl rfl) rfl) 

noncomputable def Ns132p273 := nat_lit 49791235089295251150043387750727835030655142537084749818193246459907449822139623240343177079410974538194173273318650043809416905841 

noncomputable def Ns132p274 := nat_lit 316646866740079143295725755612190180511469568587383446887297628374512813051459112748418952103360324986451946705925428665111910809600 

noncomputable def Ns132p275 := nat_lit 35292889215466515685615538434782936775335879496584526912225065701482357484147765885135409669250426336730498778434289519592561 

noncomputable def Ns132p276 := nat_lit 301616301504382519887475875313208554056441810913576197134793711552703842631125554187666956358424527745194592198537335396591648146545 

noncomputable def Ns132p277 := nat_lit 28814864873347202039911043760709306426543730741451893666744084182080665987682779260106124641405789573767127150239214008525183883673600 

noncomputable def Ns132p278 := BSN.cos_dyadic_bound_f 23931721181 17179869184 4 3 8388608 3424393 Ns132p273 Ns132p274 Ns132p275 Ns132p276 Ns132p277 Ns132p275 1483539 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 23931721181) (BSN.cosEvenQ 17179869184) 0 3 Ns132p273 Ns132p274 Ns132p275 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 23931721181) (BSN.cosOddQ 17179869184) 0 3 Ns132p276 Ns132p277 Ns132p275 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p279 := @Ns132p266 1710526 (Ns132p272 rfl) (Enclosure.sfrac_false_div 4754875 1048576) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4754875) qz384) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 210505645697642885283840) (@Nat.cast Real Real.instNatCast 151115727451828646838272)) 226375608064910080 72057594037927936 Bool.false 1483539 8388608 0 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q2 4754875 1048576 226375608064910080 72057594037927936 0 210505645697642885283840 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1483539 8388608 210505645697642885283840 151115727451828646838272 23931721181 17179869184 3424393 3421052 (Ns132p278 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p280 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz37) 1483539 8388608 69662929 3587233021952 23713909 23719118 4194304 (@Enclosure.Real.IsNear.neg qz37 Bool.true 1483539 8388608 69662929 3587233021952 (Ns132p265 (Ns132p279 rfl rfl) rfl)) 

noncomputable def Ns132p281 := Ns132p263 (@Enclosure.Real.IsNear.neg qz649 Bool.false 47433027 8388608 5209 8388608 (@Ns132p264 5209 8388608 (Ns132p280 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns132p282 := @Enclosure.Real.IsNear.recentre' qz38 Bool.true 351334 4194304 

noncomputable abbrev qz40 := (@HMul.hMul Real Real Real qz339 qz337 qz383)

noncomputable def Ns132p283 := @Enclosure.Real.IsNear.cos_image qz40 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 6940143)) qz357) Bool.true 6940143 4194304 

noncomputable def Ns132p284 := nat_lit 16386950020323062375761987645 

noncomputable def Ns132p285 := nat_lit 9903520314283042199192993792 

noncomputable def Ns132p286 := nat_lit 13828220278254893572191251056090713 

noncomputable def Ns132p287 := @Enclosure.Real.IsNear.recentre' qz40 Bool.true Ns132p284 Ns132p285 Ns132p286 

noncomputable def Ns132p288 := nat_lit 302231454903657293676544000000000000000 

noncomputable abbrev qz41 := qz383

noncomputable def Ns132p289 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz41 884279719003555 140737488355328 1 500000000000000 18531409991839 

noncomputable abbrev qz385 := (@HSub.hSub Real Real Real qz635 qz648 qz644)

noncomputable abbrev qz42 := qz385

noncomputable def Ns132p290 := @Enclosure.Real.IsNear.subLit_tf qz42 qz27 14133363480735 70368744177664 512420575 70368744177664 1 16 

noncomputable abbrev qz386 := qz648

noncomputable abbrev qz43 := qz386

noncomputable def Ns132p291 := @Enclosure.Real.IsNear.subLit_ff_n qz43 qz32 36652066269025 70368744177664 302705375 70368744177664 6054095 8388608 25 8388608 

noncomputable def Ns132p292 := @Enclosure.Real.IsNear.mulLit_ff qz32 qz32 6054095 8388608 25 8388608 6054095 8388608 25 8388608 36652066269025 70368744177664 

noncomputable def Ns132p293 := nat_lit 4454647494231478124589523653928419234042008346570170631563030056962741095729686108748481 

noncomputable def Ns132p294 := nat_lit 14198936579076412752333613960380805571166435299025227571149477343212749250185412581785600 

noncomputable def Ns132p295 := nat_lit 12485933828608411994884130402667111899830198412736029379852279695846636409125124801 

noncomputable def Ns132p296 := nat_lit 26944766458003752553855908048910550362642531498263723895897822982466617133665494986701505 

noncomputable def Ns132p297 := nat_lit 1292103228695953560462358870394653306976145612211295708974602438232360181766872544942489600 

noncomputable def Ns132p298 := BSN.cos_dyadic_bound_t 6940143 4194304 4 3 4194304 1710526 Ns132p293 Ns132p294 Ns132p295 Ns132p296 Ns132p297 Ns132p295 351334 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 6940143) (BSN.cosEvenQ 4194304) 0 3 Ns132p293 Ns132p294 Ns132p295 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 6940143) (BSN.cosOddQ 4194304) 0 3 Ns132p296 Ns132p297 Ns132p295 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p299 := @Ns132p282 666941118 14348932087808 175667 2097152 333470559 7174466043904 (@Ns132p283 385 8388608 Bool.true 351334 4194304 1 1710526 (@Ns132p287 Ns132p288 6940143 4194304 385 8388608 (@Ns132p289 70368744177664 512420575 70368744177664 Ns132p284 Ns132p285 Ns132p286 Ns132p288 RS133to150.d35 (@Ns132p290 0 1 296502559869424 18531409991839 70368744177664 512420575 70368744177664 (@Ns132p291 118559245961401466880 14133363480735 70368744177664 512420575 70368744177664 (@Ns132p292 302705375 70368744177664 (Ns132p271 rfl rfl) (Ns132p271 rfl rfl) rfl) (Ns132p271 rfl rfl) rfl rfl) qz372 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 6940143 4194304) (BSN.cos_neg_of_bound 6940143 4194304 Bool.true 351334 4194304 1 1710526 (Ns132p298 rfl rfl)) rfl rfl) 

noncomputable def Ns132p300 := @Ns132p255 14308426511584395346547 Ns132p188 (Ns132p256 qz29 (@Enclosure.Real.IsNear.of_eq qz646 (@Inv.inv Real Real.instInv (Real.sqrt qz36)) Bool.false 3018793 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz31 (BSN.t_div_two_pi_nonneg qz30 374633 1000 qz33)) Ns132p260) rfl) (@Ns132p261 17592186044416 2368710833390735 7522972906452680704 (BSN.correction_mk qz32 (BSN.cos_two_pi_p_ne_zero_mk qz30 374633 1000 7 qz33 rfl rfl (@BSN.floor_sqrt_eq_dec qz30 374633 1000 7 qz33 rfl rfl rfl))) (@Ns132p262 8388608 175667 2097152 333470559 7174466043904 8332417554009 17592186044416 2368710833390735 7522972906452680704 Ns132p281 (Ns132p299 rfl) rfl)) 

noncomputable def Ns132p301 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz30) (hardyZApproximantRS₀ qz30) Bool.false 268418535232699294785 147573952589676412928 203270459975862829269619 Ns132p188 (@Eq.refl Real (hardyZApproximantRS₀ qz30)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz30) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz30) qz30 7) (@HMul.hMul Real Real Real qz5 qz645 (Zeta.RiemannSiegel.correction qz32))) Bool.false 268418535232699294785 147573952589676412928 203270459975862829269619 Ns132p188 (BSN.hardyZApproximantRS₀_eq qz30 7 (@BSN.floor_sqrt_eq_dec qz30 374633 1000 7 qz33 rfl rfl rfl)) (@Ns132p190 268418535232699294785 147573952589676412928 203270459975862829269619 Ns132p188 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz30) qz30 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 7)) Bool.false 55311987 33554432 12559 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz30) qz30 7) (Ns132p254 (Ns132p253 rfl) rfl rfl)) (Ns132p300 rfl) rfl rfl)) 

theorem RS133to150.d39 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz30) Bool.false 268418535232699294785 147573952589676412928 203270459975862829269619 Ns132p188 := Ns132p301 

noncomputable abbrev qz650 := (@HMul.hMul Real Real Real qz843 (Real.sqrt qz848) qz845)

noncomputable abbrev qz387 := qz650

noncomputable abbrev qz44 := qz387

noncomputable abbrev qz388 := (@HMul.hMul Real Real Real qz630 (@HMul.hMul Real Real Real qz630 qz650 qz650) qz650)

noncomputable abbrev qz45 := (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz388))

noncomputable abbrev qz46 := (@HMul.hMul Real Real Real qz339 (@HMul.hMul Real Real Real qz339 qz363 qz363) qz363)

noncomputable abbrev qz389 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz44))

noncomputable def Ns132p302 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz354 (@HAdd.hAdd Real Real Real qz354 qz389 qz45) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz46))) Bool.false 

noncomputable def Ns132p303 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz354 qz389 qz45) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz46)) 10178201 268435456 

noncomputable def Ns132p304 := @Enclosure.Real.IsNear.addLit_ff qz389 qz45 1272275 33554432 25 33554432 

noncomputable def Ns132p305 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz44) 25 4 0 1 50891 8388608 1 8388608 1272275 

noncomputable def Ns132p306 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz44) Bool.false 50891 8388608 1 8388608 50891 8388608 1 8388608 

noncomputable def Ns132p307 := @Enclosure.Real.IsNear.mulLit_ff qz20 qz8 23286265 8388608 5 8388608 99623006091 1677721600 74619 1677721600 463969543986328023 2814749767106560 447142642317 

noncomputable def Ns132p308 := @Enclosure.Real.IsNear.sqrt_image qz8 99623006091 1677721600 74619 1677721600 32320614 32320640 4194304 qz361 

noncomputable def Ns132p309 := @Enclosure.Real.IsNear.sqrt_image qz19 32320627 4194304 13 4194304 11643130 11643135 4194304 (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 64641254 8388608 26 8388608 32320627 4194304 13 4194304 (Ns132p308 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz390 := (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 23286265 8388608 5 8388608 23286265 8388608 5 8388608 (Ns132p309 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns132p310 := @Ns132p307 2814749767106560 qz390 

noncomputable def Ns132p311 := Ns132p310 qz361 

noncomputable def Ns132p312 := @Enclosure.Real.IsNear.inv_image qz44 463969543986328023 2814749767106560 447142642317 2814749767106560 25445 25446 4194304 (Ns132p311 rfl) rfl rfl 

noncomputable abbrev qz47 := (@Inv.inv Real Real.instInv qz388)

noncomputable def Ns132p313 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz47 1 32 0 1 1 

noncomputable def Ns132p314 := @Enclosure.Real.IsNear.recentre' qz47 Bool.false 1 8388608 1 8388608 

noncomputable def Ns132p315 := nat_lit 99877674117388910224728830621915700232939585598548167 

noncomputable def Ns132p316 := nat_lit 22300745198530623141535718272648361505980416000 

noncomputable def Ns132p317 := nat_lit 288766433478719203806431151856994983059236755833 

noncomputable abbrev qz48 := qz388

noncomputable def Ns132p318 := @Enclosure.Real.IsNear.inv_image qz48 Ns132p315 Ns132p316 Ns132p317 Ns132p316 0 1 

noncomputable def Ns132p319 := nat_lit 215267737746881174131649946955088529 

noncomputable def Ns132p320 := nat_lit 7922816251426433759354395033600 

noncomputable def Ns132p321 := nat_lit 414921335641863117281644627071 

noncomputable abbrev qz391 := (@HMul.hMul Real Real Real qz630 qz650 qz650)

noncomputable abbrev qz49 := qz391

noncomputable def Ns132p322 := @Enclosure.Real.IsNear.mulLit_ff qz49 qz44 Ns132p319 Ns132p320 Ns132p321 Ns132p320 463969543986328023 2814749767106560 447142642317 

noncomputable def Ns132p323 := @Enclosure.Real.IsNear.mulLit_ff qz44 qz44 463969543986328023 2814749767106560 447142642317 2814749767106560 463969543986328023 2814749767106560 447142642317 2814749767106560 Ns132p319 

noncomputable def Ns132p324 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz46) 13 10 0 1 392157 8388608 1 

noncomputable def Ns132p325 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz46) Bool.false 392157 8388608 1 8388608 392157 8388608 

noncomputable def Ns132p326 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz20 qz20) qz20 542250137650225 70368744177664 232862675 70368744177664 23286265 8388608 5 8388608 12626980401609616659625 

noncomputable def Ns132p327 := @Enclosure.Real.IsNear.mulLit_ff qz20 qz20 23286265 8388608 5 8388608 23286265 8388608 5 8388608 542250137650225 70368744177664 232862675 

noncomputable def Ns132p328 := @Ns132p327 70368744177664 qz390 

noncomputable def Ns132p329 := Ns132p328 qz390 

noncomputable def Ns132p330 := @Ns132p326 590295810358705651712 8133753811223375 590295810358705651712 (Ns132p329 rfl) qz390 

noncomputable def Ns132p331 := @Enclosure.Real.IsNear.inv_image qz46 12626980401609616659625 590295810358705651712 8133753811223375 590295810358705651712 196078 196079 4194304 (Ns132p330 rfl) 

noncomputable def Ns132p332 := @Ns132p303 201 268435456 5098041 83886080 13 83886080 2222304343883776 132459661 1342177280 1213 1342177280 (@Ns132p304 1 268435456 1 268435456 341523753336832 10178201 268435456 201 268435456 (@Ns132p305 33554432 25 33554432 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns132p306 (Ns132p312 rfl rfl rfl rfl) rfl) rfl) (@Ns132p313 8388608 1 8388608 1 268435456 1 268435456 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns132p314 1 8388608 1 8388608 (@Ns132p318 4194304 (@Ns132p322 2814749767106560 Ns132p315 Ns132p316 Ns132p317 Ns132p316 (@Ns132p323 Ns132p320 Ns132p321 Ns132p320 (Ns132p311 rfl) (Ns132p311 rfl) rfl) (Ns132p311 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns132p324 8388608 5098041 83886080 13 83886080 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns132p325 1 8388608 (Ns132p331 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS133to150.d40 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 := @Ns132p302 132459661 1342177280 1213 1342177280 (BSN.hardyZErrorBoundRS₀_mk qz4 373095 1000 qz11 rfl rfl) (Ns132p332 rfl rfl) 

noncomputable def Ns132p333 := nat_lit 31553635353426104487510016 

noncomputable def Ns132p334 := nat_lit 99862841866163842822701056 

noncomputable abbrev qz853 := (Enclosure.sfrac Bool.false 376169 1000)

noncomputable abbrev qz651 := qz853

noncomputable abbrev qz392 := qz651

noncomputable abbrev qz50 := qz392

noncomputable abbrev qz854 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 376169 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz652 := qz854

noncomputable abbrev qz393 := qz652

noncomputable abbrev qz51 := qz393

noncomputable abbrev qz855 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 376169 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz653 := qz855

noncomputable abbrev qz394 := qz653

noncomputable abbrev qz52 := qz394

noncomputable abbrev qz654 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz51 qz9))

noncomputable def Ns132p335 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz50) qz50 7) (@HMul.hMul Real Real Real qz5 qz654 (Zeta.RiemannSiegel.correction qz52)) 11299037 33554432 3153 2097152 3235566674238774423 18446744073709551616 8193129974192713423359 Ns132p333 Ns132p334 

noncomputable def Ns132p336 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz50) qz50 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 376169 1000 59 95 67108864 33554432 1125899906842624 Bool.false 39003335894 1225 

noncomputable def Ns132p337 := Ns132p336 120242927 40 27397080 8 130587807 40 25364760 8 Bool.true 40277920 37635 Bool.true 8878645 Bool.true 105384956 3537118876014220 1 Bool.false 8852765 Bool.false Bool.false 67108857 Bool.false Bool.true 11299037 

noncomputable def Ns132p338 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz50) qz50 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 376169 1000 38 15 67108864 33554432 1125899906842624 Bool.false 39003335894 1225 

noncomputable def Ns132p339 := Ns132p338 93032624 40 33554424 8 108007536 40 30011992 8 Bool.true 25219883 22202 Bool.false 1601188 Bool.true 44535559 3537118876014220 1 Bool.false 67089763 Bool.true Bool.false 41337831 Bool.false Bool.true 40277920 

noncomputable def Ns132p340 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz50) qz50 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 376169 1000 204 106 67108864 33554432 1125899906842624 Bool.false 39003335894 1225 

noncomputable def Ns132p341 := Ns132p340 46516304 40 47453136 16 73726608 40 38745320 8 Bool.true 67108856 1272 Bool.false 815493 Bool.false 95749640 3537118876014220 1 Bool.false 67103909 Bool.false Bool.false 9631343 Bool.true Bool.true 25219883 

noncomputable def Ns132p342 := nat_lit 266983522388385089523583752357056294935127431046687556041 

noncomputable def Ns132p343 := nat_lit 459369961135727341334269071959268313749933036404736000 

noncomputable def Ns132p344 := nat_lit 3615415320826862493439842487520000 

noncomputable def Ns132p345 := nat_lit 8160049722784765104220189470383465280 

noncomputable abbrev qz395 := (@Eq.refl Real qz651)

noncomputable abbrev qz53 := qz395

noncomputable def Ns132p346 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz50 376169 1000 566013466244 16000000 752338 4000 2000 Ns132p344 Ns132p345 qz53 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns132p347 := nat_lit 85434727164283228647546800754258014379240777934940017933120 

noncomputable abbrev qz396 := (Real.log (Enclosure.sfrac Bool.false 566013466244 16000000))

noncomputable abbrev qz397 := (Enclosure.sfrac Bool.false 376169 2000)

noncomputable abbrev qz54 := (@HSub.hSub Real Real Real qz342 (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 376169 4000) qz396) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 752338)))))) qz397)

noncomputable abbrev qz398 := (@HSub.hSub Real Real Real qz12 qz54 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 376169 2000) (Real.log Real.pi)))

noncomputable def Ns132p348 := @Enclosure.Real.IsNear.addLit_ft_p qz398 (Enclosure.sfrac Bool.true Ns132p344 Ns132p345) 10469886237979861410529 18014398509481984000 3192985013456805371471 Ns132p199 Ns132p344 Ns132p345 0 1 Ns132p347 

noncomputable def Ns132p349 := nat_lit 702622171640062154138038829056000 

noncomputable abbrev qz399 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 376169 2000) (Real.log Real.pi))

noncomputable def Ns132p350 := @Enclosure.Real.IsNear.subLit_ff_p qz54 qz399 14348493379166853227233 18014398509481984000 4802113465255808641 684210400000000000000000 14448937554609 67108864000 376169 33554432000 Ns132p349 10469886237979861410529 18014398509481984000 

noncomputable def Ns132p351 := nat_lit 28696986758333706454466000 

noncomputable abbrev qz55 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 376169 4000) qz396) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 752338))))))

noncomputable def Ns132p352 := @Enclosure.Real.IsNear.subLit_ff_p qz55 qz397 17736722515623517446881 18014398509481984000 4802113465255808641 684210400000000000000000 376169 2000 0 1 Ns132p351 14348493379166853227233 18014398509481984000 4802113465255808641 684210400000000000000000 

noncomputable def Ns132p353 := nat_lit 39939548456067979795674857316693311488 

noncomputable def Ns132p354 := nat_lit 12662028412174679874207744 

noncomputable def Ns132p355 := nat_lit 21197158321412292548681028138731232140626528669440 

noncomputable def Ns132p356 := nat_lit 10357311963415626755024504858527231273967290368 

noncomputable def Ns132p357 := nat_lit 9093394815267999113354888429764274297733888 

noncomputable def Ns132p358 := BSN.log_dyadic_bound 41725466244 1090301466244 3 2 Ns132p355 33554432 13684208 Ns132p356 Ns132p357 2569488 1132026932488 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 41725466244) (BSN.artanhQ 1090301466244) 0 2 Ns132p356 Ns132p355 Ns132p357 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns132p359 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 376169 4000) qz396 376169 4000 0 1 47169731602723449 4503599627370496 12500002565789 171052600000000000000 17743790767264877086881 18014398509481984000 4702113465170282341 684210400000000000000000 (Enclosure.Real.IsNear.const Bool.false 376169 4000) (BSN.isNear_log_sfrac 566013466244 16000000 47169731602723449 4503599627370496 12500002565789 171052600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 566013466244) qz350)) Bool.false Ns132p354 Ns132p87 1000000205263120 13684208000000000000000 47169731602723449 4503599627370496 12500002565789 171052600000000000000 (BSN.log_rat_reduce_isNear 566013466244 16000000 15 1132026932488 1048576000000 2569488 33554432 24973259072661432 36028797018963968 13684208 1000000000000000 rfl rfl rfl rfl (Ns132p358 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns132p360 := BSN.arctan_dyadic_bound_f 1000 752338 1 0 4194304 1710526 0 1 1 0 1 1 5575 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 752338) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 752338) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz400 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 752338)))

noncomputable def Ns132p361 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz400 884279719003555 562949953421312 1 2000000000000000 5575 4194304 1 1710526 3705799516545162936320 883531455169955 562949953421312 1000000000855263 1710526000000000000000 qz17 (Ns132p360 rfl) rfl rfl 

noncomputable def Ns132p362 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 376169 4000) qz396) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz400)) 17743790767264877086881 18014398509481984000 4702113465170282341 684210400000000000000000 883531455169955 2251799813685248 1000000000855263 6842104000000000000000 Ns132p353 17736722515623517446881 18014398509481984000 4802113465255808641 684210400000000000000000 (Ns132p359 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz400) 1 4 0 1 883531455169955 562949953421312 1000000000855263 1710526000000000000000 883531455169955 2251799813685248 1000000000855263 6842104000000000000000 qz353 Ns132p361 rfl) 

noncomputable def Ns132p363 := @Ns132p348 Ns132p342 Ns132p343 3192985013456805371471 Ns132p199 (@Ns132p350 3192985013456805371471 Ns132p199 (Ns132p352 (Ns132p362 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 376169 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz397 (Real.log Real.pi) 376169 2000 0 1 38410761 33554432 1 16777216 14448937554609 67108864000 376169 33554432000 (Enclosure.Real.IsNear.const Bool.false 376169 2000) RS133to150.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns132p344 Ns132p345) 

noncomputable def Ns132p364 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz50) Bool.false Ns132p342 Ns132p343 3192985013456805371471 Ns132p199 2437708493 4194304 77 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz50) (@HAdd.hAdd Real Real Real qz354 qz398 (Enclosure.sfrac Bool.true Ns132p344 Ns132p345)) Bool.false Ns132p342 Ns132p343 3192985013456805371471 Ns132p199 Ns132p346 (Ns132p363 rfl rfl)) 

noncomputable def Ns132p365 := nat_lit 140115472874078074230879391376480296489501274060855341640048446563742207070726382240000 

noncomputable def Ns132p366 := nat_lit 281774245588874442545553161123231297249959643031883076673685476974179459568100000000 

noncomputable def Ns132p367 := nat_lit 366512889701155826269134177058486973467431973594474274552179012132795204155458839200000 

noncomputable def Ns132p368 := BSN.sin_dyadic_bound_f 26992161390 17179869184 3 2 8388608 3424393 Ns132p365 Ns132p99 Ns132p366 Ns132p367 Ns132p102 Ns132p366 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26992161390) qz355 0 2 Ns132p365 Ns132p99 Ns132p366 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26992161390) qz356 0 2 Ns132p367 Ns132p102 Ns132p366 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p369 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz50) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2437708493) qz357) Bool.false 2437708493 4194304 77 4194304 Bool.true 8388607 8388608 1 1710526 (Ns132p364 rfl) (Enclosure.sfrac_false_div 2437708493 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2437708493) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949702249853966998306816) qz358) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 92 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q1 2437708493 4194304 226375608064910080 72057594037927936 92 949702249853966998306816 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 949702249853966998306816 604462909807314587353088 26992161390 17179869184 3424393 3421052 (Ns132p368 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p370 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz50) Bool.false Ns132p342 Ns132p343 3192985013456805371471 Ns132p199 39003335894 67108864 1225 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz50) (@HAdd.hAdd Real Real Real qz354 qz398 (Enclosure.sfrac Bool.true Ns132p344 Ns132p345)) Bool.false Ns132p342 Ns132p343 3192985013456805371471 Ns132p199 Ns132p346 (Ns132p363 rfl rfl)) 

noncomputable def Ns132p371 := Ns132p341 22202 BSN.abs_quadSignPos (BSN.cos_quad_nat0 204 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 67103909 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 106 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 9631343 67108864) qz53 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz50) qz50 1) Bool.true 8388607 8388608 67952403 3587233021952 67108856 67108864 1272 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz50) qz50 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz50)) Bool.true 8388607 8388608 67952403 3587233021952 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz50) qz50) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz50)) Bool.true 8388607 8388608 135904806 7174466043904 8388607 8388608 67952403 3587233021952 (Ns132p369 rfl rfl) rfl)) rfl) (Ns132p370 rfl) RS133to150.d7 

noncomputable def Ns132p372 := BSN.cos_dyadic_bound_f 815493 67108864 1 0 67108864 33554432 0 1 1 0 1 1 67103909 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 815493) qz360 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 815493) (BSN.cosOddQ 67108864) 0 0 rfl) rfl rfl 

noncomputable def Ns132p373 := nat_lit 691805094621272916335316363107204251460707931227301274781365890580799208323315750997088444350464000000 

noncomputable def Ns132p374 := nat_lit 593807662412665415520905255538029229929996848552297994277927737642719721484395216896000000000000 

noncomputable def Ns132p375 := nat_lit 4190063087116785513250418559133606565225137940997013239096851013795033200742908007568799392438681600000 

noncomputable def Ns132p376 := BSN.cos_dyadic_bound_f 95749640 67108864 4 3 67108864 33554432 Ns132p373 Ns132p118 Ns132p374 Ns132p375 Ns132p121 Ns132p374 9631343 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 95749640) qz360 0 3 Ns132p373 Ns132p118 Ns132p374 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 95749640) (BSN.cosOddQ 67108864) 0 3 Ns132p375 Ns132p121 Ns132p374 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p377 := nat_lit 6573085880976562592686336 

noncomputable def Ns132p378 := BSN.cos_dyadic_bound_f 1601188 67108864 2 1 67108864 33554432 Ns132p377 Ns132p135 Ns132p377 Ns132p377 Ns132p136 Ns132p377 67089763 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1601188) qz360 0 1 Ns132p377 Ns132p135 Ns132p377 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1601188) (BSN.cosOddQ 67108864) 0 1 Ns132p377 Ns132p136 Ns132p377 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p379 := nat_lit 241299722169099355581864944580286745433684798203843391666537610945 

noncomputable def Ns132p380 := nat_lit 15475876766298402011264316161817014702536694576785841657200321 

noncomputable def Ns132p381 := nat_lit 631950406642400495777818522150774724778703697790275039192534466241 

noncomputable def Ns132p382 := BSN.sin_dyadic_bound_f 44535559 67108864 3 2 67108864 33554432 Ns132p379 Ns132p108 Ns132p380 Ns132p381 Ns132p111 Ns132p380 41337831 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 44535559) qz359 0 2 Ns132p379 Ns132p108 Ns132p380 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 44535559) (BSN.sinOddQ 67108864) 0 2 Ns132p381 Ns132p111 Ns132p380 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p383 := Ns132p339 37635 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 38 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 67089763 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 15 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 41337831 67108864) qz53 rfl rfl (Ns132p371 RS133to150.d9 RS133to150.d11 RS133to150.d13 RS133to150.d17 (Ns132p372 rfl rfl) (Ns132p376 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns132p370 rfl) RS133to150.d19 RS133to150.d21 RS133to150.d23 RS133to150.d25 RS133to150.d17 (Ns132p378 rfl rfl) (Ns132p382 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns132p384 := nat_lit 6214222037213294782147800625 

noncomputable def Ns132p385 := BSN.sin_dyadic_bound_f 8878645 67108864 2 1 67108864 33554432 Ns132p384 Ns132p114 Ns132p384 Ns132p384 Ns132p115 Ns132p384 8852765 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 8878645) qz359 0 1 Ns132p384 Ns132p114 Ns132p384 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 8878645) (BSN.sinOddQ 67108864) 0 1 Ns132p384 Ns132p115 Ns132p384 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p386 := nat_lit 2638307687068770294036366184243382143145215443111945743415760674821222122787279813135699256291975233536 

noncomputable def Ns132p387 := nat_lit 1876477764012730585772842030709488466422542382178038366386501092425672129557799861352134120308736 

noncomputable def Ns132p388 := nat_lit 13175164572714424194297834560498401922107384690894329258687739536541707457827230528507679736891489386496 

noncomputable def Ns132p389 := BSN.sin_dyadic_bound_f 105384956 67108864 4 3 67108864 33554432 Ns132p386 Ns132p233 Ns132p387 Ns132p388 Ns132p236 Ns132p387 67108857 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 105384956) qz359 0 3 Ns132p386 Ns132p233 Ns132p387 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 105384956) (BSN.sinOddQ 67108864) 0 3 Ns132p388 Ns132p236 Ns132p387 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz655 := (BSN.cos_quad_nat3 95 rfl)

noncomputable def Ns132p390 := Ns132p337 50448 BSN.abs_quadSignPos (BSN.cos_quad_nat3 59 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 8852765 67108864) BSN.abs_quadSignPos qz655 (BSN.sfrac_eq_quadSignPos_mul Bool.false 67108857 67108864) qz53 rfl rfl (Ns132p383 rfl rfl) (Ns132p370 rfl) RS133to150.d27 RS133to150.d29 RS133to150.d31 RS133to150.d33 RS133to150.d17 (Ns132p385 rfl rfl) (Ns132p389 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns132p391 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz50) qz50 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz50) qz50 7) 11299037 67108864 50448 67108864 11299037 67108864 50448 67108864 1516531074727936 11299037 33554432 3153 2097152 (Ns132p390 rfl) 

noncomputable def Ns132p392 := @Enclosure.Real.IsNear.mulLit_tf qz654 (Zeta.RiemannSiegel.correction qz52) 1507853 4194304 1 4194304 2145810416691 4398046511104 10862403799948659 15045945812905361408 3235566674238774423 18446744073709551616 

noncomputable abbrev qz656 := (@HPow.hPow Real Real Real qz7 qz51 qz9)

noncomputable def Ns132p393 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz656 1 1 0 1 1507853 4194304 1 4194304 1507853 4194304 1 4194304 

noncomputable def Ns132p394 := @Enclosure.Real.IsNear.sqrt_image qz51 502219094041 8388608000 376169 8388608000 32453489 32453514 4194304 (@Enclosure.Real.IsNear.of_eq qz51 (@HMul.hMul Real Real Real qz5 qz50 qz3) Bool.false 502219094041 8388608000 376169 8388608000 (BSN.t_div_two_pi_mk qz50 376169 1000 qz53) (@Enclosure.Real.IsNear.mulLit_ff qz50 qz3 376169 1000 0 1 1335089 8388608 1 8388608 502219094041 8388608000 376169 8388608000 (Enclosure.Real.IsNear.const Bool.false 376169 1000) RS133to150.d36 rfl)) 

noncomputable abbrev qz856 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 376169 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz657 := qz856

noncomputable abbrev qz401 := qz657

noncomputable abbrev qz56 := qz401

noncomputable def Ns132p395 := @Enclosure.Real.IsNear.sqrt_image qz56 64907003 8388608 25 8388608 11667038 11667044 4194304 (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 64907003 8388608 25 8388608 64907003 8388608 25 8388608 (Ns132p394 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns132p396 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz56) 11667041 4194304 3 4194304 1507852 1507854 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz56) Bool.false 23334082 8388608 6 8388608 11667041 4194304 3 4194304 (Ns132p395 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns132p397 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz56)) Bool.false 3015706 8388608 2 8388608 1507853 4194304 1 4194304 (Ns132p396 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz57 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz394))

noncomputable abbrev qz658 := (@HMul.hMul Real Real Real qz843 qz855 qz855)

noncomputable abbrev qz402 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz658 qz653) qz640)

noncomputable abbrev qz58 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz402))

noncomputable def Ns132p398 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz52) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz57) qz58) Bool.false 2145810416691 

noncomputable def Ns132p399 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz57) qz58 53534177 4194304 6635 

noncomputable abbrev qz659 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz57))

noncomputable def Ns132p400 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz57) (@Neg.neg Real Real.instNeg qz659) Bool.true 53534177 4194304 6635 2097152 (BSN.inv_eq_neg_inv_neg qz57) 

noncomputable def Ns132p401 := @Enclosure.Real.IsNear.recentre' qz659 Bool.false 107068354 8388608 26540 8388608 53534177 4194304 

noncomputable def Ns132p402 := @Enclosure.Real.IsNear.recentre' qz57 Bool.true 657232 8388608 139325858 7174466043904 41077 524288 69662929 3587233021952 

noncomputable abbrev qz59 := (@HMul.hMul Real Real Real qz339 qz337 qz394)

noncomputable def Ns132p403 := @Enclosure.Real.IsNear.cos_image qz59 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 38872477) qz365) Bool.false 38872477 8388608 79 4194304 Bool.true 657232 8388608 1 

noncomputable def Ns132p404 := nat_lit 674651885279244888446476399 

noncomputable def Ns132p405 := nat_lit 36028797018963968000000000000000 

noncomputable def Ns132p406 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz52 884279719003555 140737488355328 1 500000000000000 6186747 8388608 25 8388608 5470814898706086885585 1180591620717411303424 Ns132p404 

noncomputable def Ns132p407 := @Enclosure.Real.IsNear.subLit_ff_p qz56 qz1 64907003 8388608 25 8388608 7 1 0 1 6186747 6186747 8388608 25 

noncomputable def Ns132p408 := @Ns132p407 8388608 (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 64907003 8388608 25 8388608 64907003 8388608 25 8388608 (Ns132p394 rfl rfl rfl rfl rfl rfl) rfl) qz366 

noncomputable def Ns132p409 := @Enclosure.Real.IsNear.recentre' qz59 Bool.false 5470814898706086885585 1180591620717411303424 Ns132p404 Ns132p405 38872477 8388608 79 4194304 (@Ns132p406 Ns132p405 RS133to150.d35 (Ns132p408 rfl rfl) rfl) 

noncomputable def Ns132p410 := nat_lit 1804161860193043206897664 

noncomputable def Ns132p411 := nat_lit 65636927406755807340694124765546639361041446527963763533733456204308905802085426968248458167280476918415768241025666571271886988401 

noncomputable def Ns132p412 := nat_lit 80676744477899344807916874308433496901369173492144606132638178059330620870711866804057142236811941075171062708416676866679921 

noncomputable def Ns132p413 := nat_lit 397415466459073991924759259155155969300124243003870572838456957713051046172297081032093435637164889140767466364732541358201292055665 

noncomputable def Ns132p414 := BSN.cos_dyadic_bound_f 25638682077 17179869184 4 3 8388608 3424393 Ns132p411 Ns132p274 Ns132p412 Ns132p413 Ns132p277 Ns132p412 657232 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 25638682077) (BSN.cosEvenQ 17179869184) 0 3 Ns132p411 Ns132p274 Ns132p412 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 25638682077) (BSN.cosOddQ 17179869184) 0 3 Ns132p413 Ns132p277 Ns132p412 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p415 := @Ns132p403 1710526 (Ns132p409 rfl) (Enclosure.sfrac_false_div 38872477 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 38872477) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns132p410) qz367) 226375608064910080 72057594037927936 Bool.false 657232 8388608 0 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q2 38872477 8388608 226375608064910080 72057594037927936 0 Ns132p410 Ns132p87 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 657232 8388608 Ns132p410 Ns132p87 25638682077 17179869184 3424393 3421052 (Ns132p414 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p416 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz57) 41077 524288 69662929 3587233021952 53520907 53547447 4194304 (@Enclosure.Real.IsNear.neg qz57 Bool.true 41077 524288 69662929 3587233021952 (Ns132p402 (Ns132p415 rfl rfl) rfl)) 

noncomputable def Ns132p417 := Ns132p400 (@Enclosure.Real.IsNear.neg qz659 Bool.false 53534177 4194304 6635 2097152 (@Ns132p401 6635 2097152 (Ns132p416 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns132p418 := @Enclosure.Real.IsNear.recentre' qz58 Bool.true 160332 4194304 

noncomputable abbrev qz60 := (@HMul.hMul Real Real Real qz339 qz337 qz402)

noncomputable def Ns132p419 := @Enclosure.Real.IsNear.cos_image qz60 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 13497535)) qz365) Bool.true 13497535 8388608 

noncomputable def Ns132p420 := nat_lit 15935077296683493731104048405 

noncomputable def Ns132p421 := nat_lit 14007208122008529595283281693718657 

noncomputable def Ns132p422 := @Enclosure.Real.IsNear.recentre' qz60 Bool.true Ns132p420 Ns132p285 Ns132p421 

noncomputable abbrev qz61 := qz402

noncomputable def Ns132p423 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz61 884279719003555 140737488355328 1 500000000000000 18020403447271 

noncomputable abbrev qz403 := (@HSub.hSub Real Real Real qz635 qz658 qz653)

noncomputable abbrev qz62 := qz403

noncomputable def Ns132p424 := @Enclosure.Real.IsNear.subLit_tf qz62 qz27 13622356936167 70368744177664 519053175 70368744177664 1 16 

noncomputable abbrev qz404 := qz658

noncomputable abbrev qz63 := qz404

noncomputable def Ns132p425 := @Enclosure.Real.IsNear.subLit_ff_n qz63 qz52 38275838442009 70368744177664 309337975 70368744177664 6186747 8388608 25 8388608 

noncomputable def Ns132p426 := @Enclosure.Real.IsNear.mulLit_ff qz52 qz52 6186747 8388608 25 8388608 6186747 8388608 25 8388608 38275838442009 70368744177664 

noncomputable def Ns132p427 := nat_lit 16307712243379428021561251894366318513198474435226515177189907885645688117176971116096890625 

noncomputable def Ns132p428 := nat_lit 58158844227896986633558482781719779619497718984807332131428259197799420928759449934993817600 

noncomputable def Ns132p429 := nat_lit 36563987145441407903910249459826883900087656096701728883509621277859170539355712890625 

noncomputable def Ns132p430 := nat_lit 98671166850321964817354792357397029621434580452202764233201779770741101880784728545242490625 

noncomputable def Ns132p431 := nat_lit 5292454824738625783653821933136499945374292427617467223959971586999747304517109944084437401600 

noncomputable def Ns132p432 := BSN.cos_dyadic_bound_t 13497535 8388608 4 3 4194304 1710526 Ns132p427 Ns132p428 Ns132p429 Ns132p430 Ns132p431 Ns132p429 160332 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 13497535) (BSN.cosEvenQ 8388608) 0 3 Ns132p427 Ns132p428 Ns132p429 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 13497535) (BSN.cosOddQ 8388608) 0 3 Ns132p430 Ns132p431 Ns132p429 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p433 := @Ns132p418 337746874 7174466043904 40083 1048576 168873437 3587233021952 (@Ns132p419 195 4194304 Bool.true 160332 4194304 1 1710526 (@Ns132p422 Ns132p288 13497535 8388608 195 4194304 (@Ns132p423 70368744177664 519053175 70368744177664 Ns132p420 Ns132p285 Ns132p421 Ns132p288 RS133to150.d35 (@Ns132p424 0 1 288326455156336 18020403447271 70368744177664 519053175 70368744177664 (@Ns132p425 114272612373585985536 13622356936167 70368744177664 519053175 70368744177664 (@Ns132p426 309337975 70368744177664 (Ns132p408 rfl rfl) (Ns132p408 rfl rfl) rfl) (Ns132p408 rfl rfl) rfl rfl) qz372 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 13497535 8388608) (BSN.cos_neg_of_bound 13497535 8388608 Bool.true 160332 4194304 1 1710526 (Ns132p432 rfl rfl)) rfl rfl) 

noncomputable def Ns132p434 := @Ns132p392 8193129974192713423359 Ns132p333 (Ns132p393 qz29 (@Enclosure.Real.IsNear.of_eq qz656 (@Inv.inv Real Real.instInv (Real.sqrt qz56)) Bool.false 1507853 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz51 (BSN.t_div_two_pi_nonneg qz50 376169 1000 qz53)) Ns132p397) rfl) (@Ns132p398 4398046511104 10862403799948659 15045945812905361408 (BSN.correction_mk qz52 (BSN.cos_two_pi_p_ne_zero_mk qz50 376169 1000 7 qz53 rfl rfl (@BSN.floor_sqrt_eq_dec qz50 376169 1000 7 qz53 rfl rfl rfl))) (@Ns132p399 2097152 40083 1048576 168873437 3587233021952 2145810416691 4398046511104 10862403799948659 15045945812905361408 Ns132p417 (Ns132p433 rfl) rfl)) 

noncomputable def Ns132p435 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz50) (hardyZApproximantRS₀ qz50) Bool.true 2976144607846851433 18446744073709551616 55632997122283317942783 Ns132p333 (@Eq.refl Real (hardyZApproximantRS₀ qz50)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz50) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz50) qz50 7) (@HMul.hMul Real Real Real qz5 qz654 (Zeta.RiemannSiegel.correction qz52))) Bool.true 2976144607846851433 18446744073709551616 55632997122283317942783 Ns132p333 (BSN.hardyZApproximantRS₀_eq qz50 7 (@BSN.floor_sqrt_eq_dec qz50 376169 1000 7 qz53 rfl rfl rfl)) (@Ns132p335 2976144607846851433 18446744073709551616 55632997122283317942783 Ns132p333 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz50) qz50 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz50) qz50 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz50) qz50 7)) Bool.true 11299037 33554432 3153 2097152 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz50) qz50 7) (Ns132p391 (Ns132p390 rfl) rfl rfl)) (Ns132p434 rfl) rfl rfl)) 

theorem RS133to150.d41 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz50) Bool.true 2976144607846851433 18446744073709551616 55632997122283317942783 Ns132p333 := Ns132p435 

noncomputable def Ns132p436 := nat_lit 3944204419178263060938752 

noncomputable def Ns132p437 := nat_lit 25321327811230208319553536 

noncomputable abbrev qz857 := (Enclosure.sfrac Bool.false 377703 1000)

noncomputable abbrev qz660 := qz857

noncomputable abbrev qz405 := qz660

noncomputable abbrev qz64 := qz405

noncomputable abbrev qz858 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 377703 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz661 := qz858

noncomputable abbrev qz406 := qz661

noncomputable abbrev qz65 := qz406

noncomputable abbrev qz859 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 377703 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz662 := qz859

noncomputable abbrev qz407 := qz662

noncomputable abbrev qz66 := qz407

noncomputable abbrev qz663 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz65 qz9))

noncomputable def Ns132p438 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz64) qz64 7) (@HMul.hMul Real Real Real qz5 qz663 (Zeta.RiemannSiegel.correction qz66)) 2555807 1048576 50653 33554432 1667183872063173605 9223372036854775808 3946083854253285132757 Ns132p436 Ns132p437 

noncomputable def Ns132p439 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz64) qz64 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 377703 1000 58 95 67108864 33554432 1125899906842624 Bool.false 39214074478 1229 

noncomputable def Ns132p440 := Ns132p439 120242927 40 27397080 8 130587807 40 25364760 8 Bool.false 63754820 37789 Bool.true 88007068 Bool.true 94968067 3537118876014220 1 Bool.false 17212743 Bool.true Bool.false 66297459 Bool.false Bool.false 81785824 

noncomputable def Ns132p441 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz64) qz64 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 377703 1000 38 14 67108864 33554432 1125899906842624 Bool.false 39214074478 1229 

noncomputable def Ns132p442 := Ns132p441 93032624 40 33554424 8 108007536 40 30011992 8 Bool.false 81044368 22294 Bool.false 69627726 Bool.true 104894892 3537118876014220 1 Bool.false 34114484 Bool.true Bool.false 519459 Bool.true Bool.false 63754820 

noncomputable def Ns132p443 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz64) qz64 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 377703 1000 205 107 67108864 33554432 1125899906842624 Bool.false 39214074478 1229 

noncomputable def Ns132p444 := Ns132p443 46516304 40 47453136 16 73726608 40 38745320 8 Bool.false 67108824 1280 Bool.false 34783709 Bool.false 87977250 3537118876014220 1 Bool.false 33247036 Bool.true Bool.false 64856211 Bool.false Bool.false 81044368 

noncomputable def Ns132p445 := nat_lit 30562349449800040422434230719929106393328074575558764527 

noncomputable def Ns132p446 := nat_lit 52302765780981114955355848602319705883824132980736000 

noncomputable def Ns132p447 := nat_lit 3689736369596158347493616996640000 

noncomputable def Ns132p448 := nat_lit 8361753814313566738970753487707507520 

noncomputable abbrev qz408 := (@Eq.refl Real qz660)

noncomputable abbrev qz67 := qz408

noncomputable def Ns132p449 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz64 377703 1000 570639224836 16000000 755406 4000 2000 Ns132p447 Ns132p448 qz67 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns132p450 := nat_lit 88019566415424116416610584473395826412784854777609241837760 

noncomputable abbrev qz409 := (Real.log (Enclosure.sfrac Bool.false 570639224836 16000000))

noncomputable abbrev qz410 := (Enclosure.sfrac Bool.false 377703 2000)

noncomputable abbrev qz68 := (@HSub.hSub Real Real Real qz342 (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 377703 4000) qz409) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 755406)))))) qz410)

noncomputable abbrev qz411 := (@HSub.hSub Real Real Real qz12 qz68 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 377703 2000) (Real.log Real.pi)))

noncomputable def Ns132p451 := @Enclosure.Real.IsNear.addLit_ft_p qz411 (Enclosure.sfrac Bool.true Ns132p447 Ns132p448) 10526455913248048993263 18014398509481984000 3205901464867233006177 Ns132p199 Ns132p447 Ns132p448 0 1 Ns132p450 

noncomputable def Ns132p452 := nat_lit 706418498284159118154223583232000 

noncomputable abbrev qz412 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 377703 2000) (Real.log Real.pi))

noncomputable def Ns132p453 := @Enclosure.Real.IsNear.subLit_ff_p qz68 qz412 14420879837196461462511 18014398509481984000 4821288469191728967 684210400000000000000000 14507859661983 67108864000 377703 33554432000 Ns132p452 10526455913248048993263 18014398509481984000 

noncomputable def Ns132p454 := nat_lit 28841759674392922925022000 

noncomputable abbrev qz69 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 377703 4000) qz409) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 755406))))))

noncomputable def Ns132p455 := @Enclosure.Real.IsNear.subLit_ff_p qz69 qz410 17822926017309898363887 18014398509481984000 4821288469191728967 684210400000000000000000 377703 2000 0 1 Ns132p454 14420879837196461462511 18014398509481984000 4821288469191728967 684210400000000000000000 

noncomputable def Ns132p456 := nat_lit 40133661485104388306359325787187838976 

noncomputable def Ns132p457 := nat_lit 12671868236928529123508224 

noncomputable def Ns132p458 := nat_lit 21559181898742487147869799718134600945497826922240 

noncomputable def Ns132p459 := nat_lit 12892277963266420689641951652253701678542358528 

noncomputable def Ns132p460 := nat_lit 13847332302863770362040051883547688493384448 

noncomputable def Ns132p461 := BSN.log_dyadic_bound 46351224836 1094927224836 3 2 Ns132p458 33554432 13684208 Ns132p459 Ns132p460 2842598 1141278449672 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 46351224836) (BSN.artanhQ 1094927224836) 0 2 Ns132p459 Ns132p458 Ns132p460 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns132p462 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 377703 4000) qz409 377703 4000 0 1 47206387806417529 4503599627370496 12500002565789 171052600000000000000 17829994293647319955887 18014398509481984000 4721288469106202667 684210400000000000000000 (Enclosure.Real.IsNear.const Bool.false 377703 4000) (BSN.isNear_log_sfrac 570639224836 16000000 47206387806417529 4503599627370496 12500002565789 171052600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 570639224836) qz350)) Bool.false Ns132p457 Ns132p87 1000000205263120 13684208000000000000000 47206387806417529 4503599627370496 12500002565789 171052600000000000000 (BSN.log_rat_reduce_isNear 570639224836 16000000 15 1141278449672 1048576000000 2842598 33554432 24973259072661432 36028797018963968 13684208 1000000000000000 rfl rfl rfl rfl (Ns132p461 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns132p463 := BSN.arctan_dyadic_bound_f 1000 755406 1 0 4194304 1710526 0 1 1 0 1 1 5552 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 755406) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 755406) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz413 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 755406)))

noncomputable def Ns132p464 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz413 884279719003555 562949953421312 1 2000000000000000 5552 4194304 1 1710526 3705812464394091626496 883534542177699 562949953421312 1000000000855263 1710526000000000000000 qz17 (Ns132p463 rfl) rfl rfl 

noncomputable def Ns132p465 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 377703 4000) qz409) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz413)) 17829994293647319955887 18014398509481984000 4721288469106202667 684210400000000000000000 883534542177699 2251799813685248 1000000000855263 6842104000000000000000 Ns132p456 17822926017309898363887 18014398509481984000 4821288469191728967 684210400000000000000000 (Ns132p462 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz413) 1 4 0 1 883534542177699 562949953421312 1000000000855263 1710526000000000000000 883534542177699 2251799813685248 1000000000855263 6842104000000000000000 qz353 Ns132p464 rfl) 

noncomputable def Ns132p466 := @Ns132p451 Ns132p445 Ns132p446 3205901464867233006177 Ns132p199 (@Ns132p453 3205901464867233006177 Ns132p199 (Ns132p455 (Ns132p465 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 377703 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz410 (Real.log Real.pi) 377703 2000 0 1 38410761 33554432 1 16777216 14507859661983 67108864000 377703 33554432000 (Enclosure.Real.IsNear.const Bool.false 377703 2000) RS133to150.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns132p447 Ns132p448) 

noncomputable def Ns132p467 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz64) Bool.false Ns132p445 Ns132p446 3205901464867233006177 Ns132p199 4901759309 8388608 155 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz64) (@HAdd.hAdd Real Real Real qz354 qz411 (Enclosure.sfrac Bool.true Ns132p447 Ns132p448)) Bool.false Ns132p445 Ns132p446 3205901464867233006177 Ns132p199 Ns132p449 (Ns132p466 rfl rfl)) 

noncomputable def Ns132p468 := nat_lit 1897780859571539445547008 

noncomputable def Ns132p469 := nat_lit 139636036456574429356847943981903312272170559226850543716102001320090431772057931939840 

noncomputable def Ns132p470 := nat_lit 279853081192475693261441570465233526842201113475539912135852278833574700884101758976 

noncomputable def Ns132p471 := nat_lit 365260333350049973383607043124231630240797424743743407017761480720220581315863180804096 

noncomputable def Ns132p472 := BSN.sin_dyadic_bound_f 26969088076 17179869184 3 2 8388608 3424393 Ns132p469 Ns132p99 Ns132p470 Ns132p471 Ns132p102 Ns132p470 8388603 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26969088076) qz355 0 2 Ns132p469 Ns132p99 Ns132p470 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26969088076) qz356 0 2 Ns132p471 Ns132p102 Ns132p470 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p473 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz64) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4901759309) qz365) Bool.false 4901759309 8388608 155 8388608 Bool.false 8388603 8388608 1 1710526 (Ns132p467 rfl) (Enclosure.sfrac_false_div 4901759309 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4901759309) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns132p468) qz367) 226375608064910080 72057594037927936 Bool.false 8388603 8388608 92 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 4901759309 8388608 226375608064910080 72057594037927936 92 Ns132p468 Ns132p87 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388603 8388608 Ns132p468 Ns132p87 26969088076 17179869184 3424393 3421052 (Ns132p472 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p474 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz64) Bool.false Ns132p445 Ns132p446 3205901464867233006177 Ns132p199 39214074478 67108864 1229 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz64) (@HAdd.hAdd Real Real Real qz354 qz411 (Enclosure.sfrac Bool.true Ns132p447 Ns132p448)) Bool.false Ns132p445 Ns132p446 3205901464867233006177 Ns132p199 Ns132p449 (Ns132p466 rfl rfl)) 

noncomputable def Ns132p475 := Ns132p444 22294 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 205 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 33247036 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 107 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 64856211 67108864) qz67 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz64) qz64 1) Bool.false 8388603 8388608 136760069 7174466043904 67108824 67108864 1280 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz64) qz64 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz64)) Bool.false 8388603 8388608 136760069 7174466043904 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz64) qz64) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz64)) Bool.false 8388603 8388608 273520138 14348932087808 8388603 8388608 136760069 7174466043904 (Ns132p473 rfl rfl) rfl)) rfl) (Ns132p474 rfl) RS133to150.d7 

noncomputable def Ns132p476 := nat_lit 1463873525306719820478482615761 

noncomputable def Ns132p477 := BSN.sin_dyadic_bound_f 34783709 67108864 2 1 67108864 33554432 Ns132p476 Ns132p114 Ns132p476 Ns132p476 Ns132p115 Ns132p476 33247036 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 34783709) qz359 0 1 Ns132p476 Ns132p114 Ns132p476 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 34783709) (BSN.sinOddQ 67108864) 0 1 Ns132p476 Ns132p115 Ns132p476 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p478 := nat_lit 3677958743950627500229378553162431204715633595170749043062500000000 

noncomputable def Ns132p479 := nat_lit 3588914078750682014816928642276170227808464370727539062500000000 

noncomputable def Ns132p480 := nat_lit 9626938468505094729719621183337920308172112378370783859062500000000 

noncomputable def Ns132p481 := BSN.sin_dyadic_bound_f 87977250 67108864 3 2 67108864 33554432 Ns132p478 Ns132p108 Ns132p479 Ns132p480 Ns132p111 Ns132p479 64856211 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 87977250) qz359 0 2 Ns132p478 Ns132p108 Ns132p479 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 87977250) (BSN.sinOddQ 67108864) 0 2 Ns132p480 Ns132p111 Ns132p479 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p482 := nat_lit 801414386392323789528140508653244652762052683730352459714094285056 

noncomputable def Ns132p483 := nat_lit 552405117021018305939422051687003422171456324281353182203986176 

noncomputable def Ns132p484 := nat_lit 2403138348942929331972542681856359951441815138542494672777874882816 

noncomputable def Ns132p485 := BSN.cos_dyadic_bound_f 69627726 67108864 3 2 67108864 33554432 Ns132p482 Ns132p124 Ns132p483 Ns132p484 Ns132p127 Ns132p483 34114484 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 69627726) qz360 0 2 Ns132p482 Ns132p124 Ns132p483 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 69627726) (BSN.cosOddQ 67108864) 0 2 Ns132p484 Ns132p127 Ns132p483 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p486 := nat_lit 997523747498781462994754854736962498053541246890735006155791028916853428930699119945800082924362530816 

noncomputable def Ns132p487 := nat_lit 1774402259163082910943027230840976626736296933098563278369051629411286467242932805060951734747136 

noncomputable def Ns132p488 := nat_lit 6037351744076028791735521555735031935308262468708856097359752725173396028503508224070381706195438141440 

noncomputable def Ns132p489 := BSN.cos_dyadic_bound_f 104894892 67108864 4 3 67108864 33554432 Ns132p486 Ns132p118 Ns132p487 Ns132p488 Ns132p121 Ns132p487 519459 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 104894892) qz360 0 3 Ns132p486 Ns132p118 Ns132p487 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 104894892) (BSN.cosOddQ 67108864) 0 3 Ns132p488 Ns132p121 Ns132p487 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p490 := Ns132p442 37789 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 38 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 34114484 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 14 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 519459 67108864) qz67 rfl rfl (Ns132p475 RS133to150.d9 RS133to150.d11 RS133to150.d13 RS133to150.d17 (Ns132p477 rfl rfl) (Ns132p481 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns132p474 rfl) RS133to150.d19 RS133to150.d21 RS133to150.d23 RS133to150.d25 RS133to150.d17 (Ns132p485 rfl rfl) (Ns132p489 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns132p491 := nat_lit 493399986279121656375344565745450676875316728252794379868326683822658778337960954666730698675224313856 

noncomputable def Ns132p492 := nat_lit 215879115453136718659120549212723824236351891725299232998848007243974858363207459294008234213376 

noncomputable def Ns132p493 := nat_lit 2989785160198304962521710015733055694532637475004298322081987576133498419127392023801467368245842411520 

noncomputable def Ns132p494 := BSN.cos_dyadic_bound_f 88007068 67108864 4 3 67108864 33554432 Ns132p491 Ns132p118 Ns132p492 Ns132p493 Ns132p121 Ns132p492 17212743 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 88007068) qz360 0 3 Ns132p491 Ns132p118 Ns132p492 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 88007068) (BSN.cosOddQ 67108864) 0 3 Ns132p493 Ns132p121 Ns132p492 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p495 := nat_lit 1738698486880081296759876874274297452245639772145878261026472766286345919931280164807027505141020901361 

noncomputable def Ns132p496 := nat_lit 538184493526220928458267590339655006211097443277612389400971881490353671837214490172318133272561 

noncomputable def Ns132p497 := nat_lit 8686372513283195581404844579630121227437802801648177680731081127312903036057286296674564806495556878321 

noncomputable def Ns132p498 := BSN.sin_dyadic_bound_f 94968067 67108864 4 3 67108864 33554432 Ns132p495 Ns132p233 Ns132p496 Ns132p497 Ns132p236 Ns132p496 66297459 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 94968067) qz359 0 3 Ns132p495 Ns132p233 Ns132p496 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 94968067) (BSN.sinOddQ 67108864) 0 3 Ns132p497 Ns132p236 Ns132p496 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p499 := Ns132p440 50653 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 58 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 17212743 67108864) BSN.abs_quadSignPos qz655 (BSN.sfrac_eq_quadSignPos_mul Bool.false 66297459 67108864) qz67 rfl rfl (Ns132p490 rfl rfl) (Ns132p474 rfl) RS133to150.d27 RS133to150.d29 RS133to150.d31 RS133to150.d33 RS133to150.d17 (Ns132p494 rfl rfl) (Ns132p498 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns132p500 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz64) qz64 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz64) qz64 7) 81785824 67108864 50653 67108864 81785824 67108864 50653 67108864 10977107479887872 2555807 1048576 50653 33554432 (Ns132p499 rfl) 

noncomputable def Ns132p501 := @Enclosure.Real.IsNear.mulLit_tf qz663 (Zeta.RiemannSiegel.correction qz66) 94145 262144 1 4194304 17708682054949 35184372088832 83819808497368597 30091891625810722816 1667183872063173605 9223372036854775808 

noncomputable abbrev qz664 := (@HPow.hPow Real Real Real qz7 qz65 qz9)

noncomputable def Ns132p502 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz664 1 1 0 1 94145 262144 1 4194304 94145 262144 1 4194304 

noncomputable def Ns132p503 := @Enclosure.Real.IsNear.sqrt_image qz65 504267120567 8388608000 377703 8388608000 32519594 32519619 4194304 (@Enclosure.Real.IsNear.of_eq qz65 (@HMul.hMul Real Real Real qz5 qz64 qz3) Bool.false 504267120567 8388608000 377703 8388608000 (BSN.t_div_two_pi_mk qz64 377703 1000 qz67) (@Enclosure.Real.IsNear.mulLit_ff qz64 qz3 377703 1000 0 1 1335089 8388608 1 8388608 504267120567 8388608000 377703 8388608000 (Enclosure.Real.IsNear.const Bool.false 377703 1000) RS133to150.d36 rfl)) 

noncomputable abbrev qz860 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 377703 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz665 := qz860

noncomputable abbrev qz414 := qz665

noncomputable abbrev qz70 := qz414

noncomputable def Ns132p504 := @Enclosure.Real.IsNear.sqrt_image qz70 65039213 8388608 25 8388608 11678915 11678920 4194304 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 65039213 8388608 25 8388608 65039213 8388608 25 8388608 (Ns132p503 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns132p505 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz70) 23357835 8388608 5 8388608 1506319 1506321 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz70) Bool.false 23357835 8388608 5 8388608 23357835 8388608 5 8388608 (Ns132p504 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns132p506 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz70)) Bool.false 3012640 8388608 2 8388608 94145 262144 1 4194304 (Ns132p505 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz71 := (@HMul.hMul Real Real Real qz339 qz337 qz407)

noncomputable abbrev qz666 := (@HMul.hMul Real Real Real qz843 qz859 qz859)

noncomputable abbrev qz415 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz666 qz662) qz640)

noncomputable abbrev qz72 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz415))

noncomputable def Ns132p507 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz66) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz71)) qz72) Bool.false 17708682054949 

noncomputable def Ns132p508 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz71)) qz72 407274029 8388608 383995 

noncomputable def Ns132p509 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz71)) Bool.false 407274029 8388608 383995 8388608 407274029 8388608 383995 

noncomputable def Ns132p510 := @Enclosure.Real.IsNear.recentre' (Real.cos qz71) Bool.false 172780 8388608 139325858 7174466043904 43195 2097152 69662929 3587233021952 

noncomputable def Ns132p511 := @Enclosure.Real.IsNear.cos_image qz71 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 39703177) qz365) Bool.false 39703177 8388608 79 4194304 Bool.false 172780 8388608 1 

noncomputable def Ns132p512 := nat_lit 674651885280380563698884719 

noncomputable def Ns132p513 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz66 884279719003555 140737488355328 1 500000000000000 6318957 8388608 25 8388608 5587725520355546892135 1180591620717411303424 Ns132p512 

noncomputable def Ns132p514 := @Enclosure.Real.IsNear.subLit_ff_p qz70 qz1 65039213 8388608 25 8388608 7 1 0 1 6318957 6318957 8388608 25 

noncomputable def Ns132p515 := @Ns132p514 8388608 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 65039213 8388608 25 8388608 65039213 8388608 25 8388608 (Ns132p503 rfl rfl rfl rfl rfl rfl) rfl) qz366 

noncomputable def Ns132p516 := @Enclosure.Real.IsNear.recentre' qz71 Bool.false 5587725520355546892135 1180591620717411303424 Ns132p512 Ns132p405 39703177 8388608 79 4194304 (@Ns132p513 Ns132p405 RS133to150.d35 (Ns132p515 rfl rfl) rfl) 

noncomputable def Ns132p517 := BSN.sin_dyadic_bound_f 353880268 17179869184 1 0 8388608 3424393 0 1 1 0 1 1 172780 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 353880268) qz355 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 353880268) qz356 0 0 rfl) rfl rfl 

noncomputable def Ns132p518 := @Ns132p511 1710526 (Ns132p516 rfl) (Enclosure.sfrac_false_div 39703177 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 39703177) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24902110109487463399424) qz367) 226375608064910080 72057594037927936 Bool.false 172780 8388608 0 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 39703177 8388608 226375608064910080 72057594037927936 0 24902110109487463399424 Ns132p87 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 172780 8388608 24902110109487463399424 Ns132p87 353880268 17179869184 3424393 3421052 (Ns132p517 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p519 := @Enclosure.Real.IsNear.inv_image (Real.cos qz71) 43195 2097152 69662929 3587233021952 203445017 203829012 4194304 (Ns132p510 (Ns132p518 rfl rfl) rfl) rfl 

noncomputable def Ns132p520 := @Enclosure.Real.IsNear.recentre' qz72 Bool.false 43481 4194304 

noncomputable abbrev qz73 := (@HMul.hMul Real Real Real qz339 qz337 qz415)

noncomputable def Ns132p521 := @Enclosure.Real.IsNear.cos_image qz73 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 13089831)) qz365) Bool.true 13089831 8388608 

noncomputable def Ns132p522 := nat_lit 15453745043932988535977069605 

noncomputable def Ns132p523 := nat_lit 14185599573495339573725686865433437 

noncomputable def Ns132p524 := @Enclosure.Real.IsNear.recentre' qz73 Bool.true Ns132p522 Ns132p285 Ns132p523 

noncomputable abbrev qz74 := qz415

noncomputable def Ns132p525 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz74 884279719003555 140737488355328 1 500000000000000 17476082185111 

noncomputable abbrev qz416 := (@HSub.hSub Real Real Real qz635 qz666 qz662)

noncomputable abbrev qz75 := qz416

noncomputable def Ns132p526 := @Enclosure.Real.IsNear.subLit_tf qz75 qz27 13078035674007 70368744177664 525663675 70368744177664 1 16 

noncomputable abbrev qz417 := qz666

noncomputable abbrev qz76 := qz417

noncomputable def Ns132p527 := @Enclosure.Real.IsNear.subLit_ff_n qz76 qz66 39929217567849 70368744177664 315948475 70368744177664 6318957 8388608 25 8388608 

noncomputable def Ns132p528 := @Enclosure.Real.IsNear.mulLit_ff qz66 qz66 6318957 8388608 25 8388608 6318957 8388608 25 8388608 39929217567849 70368744177664 

noncomputable def Ns132p529 := nat_lit 14418225944230386728129262903256076695986352804142578026735357805227162434268899168259105441 

noncomputable def Ns132p530 := nat_lit 25305124248904798136644452185785450789545150715641874205770954850299108195847849075361 

noncomputable def Ns132p531 := nat_lit 87265370107250929356304676617123705658015095689668990024442399391397703607610667266031706785 

noncomputable def Ns132p532 := BSN.cos_dyadic_bound_f 13089831 8388608 4 3 4194304 1710526 Ns132p529 Ns132p428 Ns132p530 Ns132p531 Ns132p431 Ns132p530 43481 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 13089831) (BSN.cosEvenQ 8388608) 0 3 Ns132p529 Ns132p428 Ns132p530 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 13089831) (BSN.cosOddQ 8388608) 0 3 Ns132p531 Ns132p431 Ns132p530 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p533 := @Ns132p520 341167926 7174466043904 43481 4194304 170583963 3587233021952 (@Ns132p521 197 4194304 Bool.false 43481 4194304 1 1710526 (@Ns132p524 Ns132p288 13089831 8388608 197 4194304 (@Ns132p525 70368744177664 525663675 70368744177664 Ns132p522 Ns132p285 Ns132p523 Ns132p288 RS133to150.d35 (@Ns132p526 0 1 279617314961776 17476082185111 70368744177664 525663675 70368744177664 (@Ns132p527 109706514679260512256 13078035674007 70368744177664 525663675 70368744177664 (@Ns132p528 315948475 70368744177664 (Ns132p515 rfl rfl) (Ns132p515 rfl rfl) rfl) (Ns132p515 rfl rfl) rfl rfl) qz372 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 13089831 8388608) (BSN.cos_neg_of_bound 13089831 8388608 Bool.false 43481 4194304 1 1710526 (Ns132p532 rfl rfl)) rfl rfl) 

noncomputable def Ns132p534 := @Ns132p501 3946083854253285132757 Ns132p436 (Ns132p502 qz29 (@Enclosure.Real.IsNear.of_eq qz664 (@Inv.inv Real Real.instInv (Real.sqrt qz70)) Bool.false 94145 262144 1 4194304 (BSN.rpow_neg_quarter_mk qz65 (BSN.t_div_two_pi_nonneg qz64 377703 1000 qz67)) Ns132p506) rfl) (@Ns132p507 35184372088832 83819808497368597 30091891625810722816 (BSN.correction_mk qz66 (BSN.cos_two_pi_p_ne_zero_mk qz64 377703 1000 7 qz67 rfl rfl (@BSN.floor_sqrt_eq_dec qz64 377703 1000 7 qz67 rfl rfl rfl))) (@Ns132p508 8388608 43481 4194304 170583963 3587233021952 17708682054949 35184372088832 83819808497368597 30091891625810722816 (@Ns132p509 8388608 (Ns132p519 rfl rfl rfl rfl rfl) rfl) (Ns132p533 rfl) rfl)) 

noncomputable def Ns132p535 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz64) (hardyZApproximantRS₀ qz64) Bool.false 24148299990873535461 9223372036854775808 9900164270355591940565 Ns132p436 (@Eq.refl Real (hardyZApproximantRS₀ qz64)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz64) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz64) qz64 7) (@HMul.hMul Real Real Real qz5 qz663 (Zeta.RiemannSiegel.correction qz66))) Bool.false 24148299990873535461 9223372036854775808 9900164270355591940565 Ns132p436 (BSN.hardyZApproximantRS₀_eq qz64 7 (@BSN.floor_sqrt_eq_dec qz64 377703 1000 7 qz67 rfl rfl rfl)) (@Ns132p438 24148299990873535461 9223372036854775808 9900164270355591940565 Ns132p436 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz64) qz64 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz64) qz64 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz64) qz64 7)) Bool.false 2555807 1048576 50653 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz64) qz64 7) (Ns132p500 (Ns132p499 rfl) rfl rfl)) (Ns132p534 rfl) rfl rfl)) 

theorem RS133to150.d42 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz64) Bool.false 24148299990873535461 9223372036854775808 9900164270355591940565 Ns132p436 := Ns132p535 

noncomputable def Ns132p536 := nat_lit 7888408838356526121877504 

noncomputable def Ns132p537 := nat_lit 619309646445681050740850688 

noncomputable abbrev qz861 := (Enclosure.sfrac Bool.false 379237 1000)

noncomputable abbrev qz667 := qz861

noncomputable abbrev qz418 := qz667

noncomputable abbrev qz77 := qz418

noncomputable abbrev qz862 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 379237 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz668 := qz862

noncomputable abbrev qz419 := qz668

noncomputable abbrev qz78 := qz419

noncomputable abbrev qz863 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 379237 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz669 := qz863

noncomputable abbrev qz420 := qz669

noncomputable abbrev qz79 := qz420

noncomputable abbrev qz670 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz78 qz9))

noncomputable def Ns132p538 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz77) qz77 7) (@HMul.hMul Real Real Real qz5 qz670 (Zeta.RiemannSiegel.correction qz79)) 36702273 16777216 50861 33554432 3440844446941556655 18446744073709551616 1441767728744779372745 Ns132p536 Ns132p537 

noncomputable def Ns132p539 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz77) qz77 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 379237 1000 58 95 67108864 33554432 1125899906842624 Bool.false 39425022103 1234 

noncomputable def Ns132p540 := Ns132p539 120242927 40 27397080 8 130587807 40 25364760 8 Bool.true 80857427 37945 Bool.true 61512093 Bool.true 84342138 3537118876014220 1 Bool.false 40837113 Bool.true Bool.false 63827613 Bool.false Bool.true 73404546 

noncomputable def Ns132p541 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz77) qz77 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 379237 1000 39 14 67108864 33554432 1125899906842624 Bool.false 39425022103 1234 

noncomputable def Ns132p542 := Ns132p541 93032624 40 33554424 8 108007536 40 30011992 8 Bool.true 77533765 22387 Bool.false 32448949 Bool.true 59630828 3537118876014220 1 Bool.false 31199229 Bool.false Bool.false 42313729 Bool.true Bool.true 80857427 

noncomputable def Ns132p543 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz77) qz77 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 379237 1000 206 108 67108864 33554432 1125899906842624 Bool.false 39425022103 1234 

noncomputable def Ns132p544 := Ns132p543 46516304 40 47453136 16 73726608 40 38745320 8 Bool.true 67108832 1288 Bool.false 68960967 Bool.false 80413901 3537118876014220 1 Bool.false 34686972 Bool.true Bool.false 24426182 Bool.false Bool.true 77533765 

noncomputable def Ns132p545 := nat_lit 56669686254261205110957213848443810505711210376082879577 

noncomputable def Ns132p546 := nat_lit 96462552583560664127891526904574505429411971255500800 

noncomputable def Ns132p547 := nat_lit 3765274661729125115442255979360000 

noncomputable def Ns132p548 := nat_lit 8567595751390714309526999317563289920 

noncomputable abbrev qz421 := (@Eq.refl Real qz667)

noncomputable abbrev qz80 := qz421

noncomputable def Ns132p549 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz77 379237 1000 575283808676 16000000 758474 4000 2000 Ns132p547 Ns132p548 qz80 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns132p550 := nat_lit 18134299601363585635506308431502019361827587320346521464640 

noncomputable abbrev qz422 := (Real.log (Enclosure.sfrac Bool.false 575283808676 16000000))

noncomputable abbrev qz423 := (Enclosure.sfrac Bool.false 379237 2000)

noncomputable abbrev qz81 := (@HSub.hSub Real Real Real qz342 (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 379237 4000) qz422) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 758474)))))) qz423)

noncomputable abbrev qz424 := (@HSub.hSub Real Real Real qz12 qz81 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 379237 2000) (Real.log Real.pi)))

noncomputable def Ns132p551 := @Enclosure.Real.IsNear.addLit_ft_p qz424 (Enclosure.sfrac Bool.true Ns132p547 Ns132p548) 2116616340617101105817 3602879701896396800 3218817916277660640883 Ns132p199 Ns132p547 Ns132p548 0 1 Ns132p550 

noncomputable def Ns132p552 := nat_lit 710218590713253570922613309440000 

noncomputable abbrev qz425 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 379237 2000) (Real.log Real.pi))

noncomputable def Ns132p553 := @Enclosure.Real.IsNear.subLit_ff_p qz81 qz425 14493322409795338650877 18014398509481984000 4840463473127649293 684210400000000000000000 14566781769357 67108864000 379237 33554432000 Ns132p552 2116616340617101105817 3602879701896396800 

noncomputable def Ns132p554 := nat_lit 28986644819590677301754000 

noncomputable abbrev qz82 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 379237 4000) qz422) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 758474))))))

noncomputable def Ns132p555 := @Enclosure.Real.IsNear.subLit_ff_p qz82 qz423 17909185633565548233981 18014398509481984000 4840463473127649293 684210400000000000000000 379237 2000 0 1 Ns132p554 14493322409795338650877 18014398509481984000 4840463473127649293 684210400000000000000000 

noncomputable def Ns132p556 := nat_lit 40327900872917421673550420841792012288 

noncomputable def Ns132p557 := nat_lit 12681668177804078379696128 

noncomputable def Ns132p558 := nat_lit 21927324602260843539920734855180397902388746448640 

noncomputable def Ns132p559 := nat_lit 15741505987896954136267988890145690043192772608 

noncomputable def Ns132p560 := nat_lit 20288932022576874678723331214436170037289728 

noncomputable def Ns132p561 := BSN.log_dyadic_bound 50995808676 1099571808676 3 2 Ns132p558 33554432 13684208 Ns132p559 Ns132p560 3114601 1150567617352 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 50995808676) (BSN.artanhQ 1099571808676) 0 2 Ns132p559 Ns132p558 Ns132p560 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns132p562 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 379237 4000) qz422 379237 4000 0 1 47242895431086713 4503599627370496 12500002565789 171052600000000000000 17916253934599031777981 18014398509481984000 4740463473042122993 684210400000000000000000 (Enclosure.Real.IsNear.const Bool.false 379237 4000) (BSN.isNear_log_sfrac 575283808676 16000000 47242895431086713 4503599627370496 12500002565789 171052600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 575283808676) qz350)) Bool.false Ns132p557 Ns132p87 1000000205263120 13684208000000000000000 47242895431086713 4503599627370496 12500002565789 171052600000000000000 (BSN.log_rat_reduce_isNear 575283808676 16000000 15 1150567617352 1048576000000 3114601 33554432 24973259072661432 36028797018963968 13684208 1000000000000000 rfl rfl rfl rfl (Ns132p561 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns132p563 := BSN.arctan_dyadic_bound_f 1000 758474 1 0 4194304 1710526 0 1 1 0 1 1 5529 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 758474) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 758474) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz426 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 758474)))

noncomputable def Ns132p564 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz426 884279719003555 562949953421312 1 2000000000000000 5529 4194304 1 1710526 3705825412243020316672 883537629185443 562949953421312 1000000000855263 1710526000000000000000 qz17 (Ns132p563 rfl) rfl rfl 

noncomputable def Ns132p565 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 379237 4000) qz422) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz426)) 17916253934599031777981 18014398509481984000 4740463473042122993 684210400000000000000000 883537629185443 2251799813685248 1000000000855263 6842104000000000000000 Ns132p556 17909185633565548233981 18014398509481984000 4840463473127649293 684210400000000000000000 (Ns132p562 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz426) 1 4 0 1 883537629185443 562949953421312 1000000000855263 1710526000000000000000 883537629185443 2251799813685248 1000000000855263 6842104000000000000000 qz353 Ns132p564 rfl) 

noncomputable def Ns132p566 := @Ns132p551 Ns132p545 Ns132p546 3218817916277660640883 Ns132p199 (@Ns132p553 3218817916277660640883 Ns132p199 (Ns132p555 (Ns132p565 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 379237 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz423 (Real.log Real.pi) 379237 2000 0 1 38410761 33554432 1 16777216 14566781769357 67108864000 379237 33554432000 (Enclosure.Real.IsNear.const Bool.false 379237 2000) RS133to150.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns132p547 Ns132p548) 

noncomputable def Ns132p567 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz77) Bool.false Ns132p545 Ns132p546 3218817916277660640883 Ns132p199 2464063881 4194304 39 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz77) (@HAdd.hAdd Real Real Real qz354 qz424 (Enclosure.sfrac Bool.true Ns132p547 Ns132p548)) Bool.false Ns132p545 Ns132p546 3218817916277660640883 Ns132p199 Ns132p549 (Ns132p566 rfl rfl)) 

noncomputable def Ns132p568 := nat_lit 140268823809588135417207668474070479615372229200871210822866732738050885336492092186880 

noncomputable def Ns132p569 := nat_lit 282390124443873317146043150420890909067082405727528224317353381507560514274589696256 

noncomputable def Ns132p570 := nat_lit 366913525966488369293497918998074575616056752583484792172899061220073411239129953362176 

noncomputable def Ns132p571 := BSN.sin_dyadic_bound_f 26999529002 17179869184 3 2 8388608 3424393 Ns132p568 Ns132p99 Ns132p569 Ns132p570 Ns132p102 Ns132p569 8388604 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26999529002) qz355 0 2 Ns132p568 Ns132p99 Ns132p569 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26999529002) qz356 0 2 Ns132p570 Ns132p102 Ns132p569 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p572 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz77) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2464063881) qz357) Bool.false 2464063881 4194304 39 2097152 Bool.true 8388604 8388608 1 1710526 (Ns132p567 rfl) (Enclosure.sfrac_false_div 2464063881 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2464063881) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949961474649783504207872) qz358) 226375608064910080 72057594037927936 Bool.false 8388604 8388608 93 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q1 2464063881 4194304 226375608064910080 72057594037927936 93 949961474649783504207872 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388604 8388608 949961474649783504207872 604462909807314587353088 26999529002 17179869184 3424393 3421052 (Ns132p571 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p573 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz77) Bool.false Ns132p545 Ns132p546 3218817916277660640883 Ns132p199 39425022103 67108864 1234 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz77) (@HAdd.hAdd Real Real Real qz354 qz424 (Enclosure.sfrac Bool.true Ns132p547 Ns132p548)) Bool.false Ns132p545 Ns132p546 3218817916277660640883 Ns132p199 Ns132p549 (Ns132p566 rfl rfl)) 

noncomputable def Ns132p574 := Ns132p544 22387 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 206 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 34686972 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 108 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 24426182 67108864) qz80 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz77) qz77 1) Bool.true 2097151 2097152 34403833 1793616510976 67108832 67108864 1288 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz77) qz77 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz77)) Bool.true 2097151 2097152 34403833 1793616510976 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz77) qz77) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz77)) Bool.true 8388604 8388608 68807666 3587233021952 2097151 2097152 34403833 1793616510976 (Ns132p572 rfl rfl) rfl)) rfl) (Ns132p573 rfl) RS133to150.d7 

noncomputable def Ns132p575 := nat_lit 771134894467443894400976425560230000901476483840036555637788438721 

noncomputable def Ns132p576 := nat_lit 511477744971454667745209301314167018154266528458977829085442241 

noncomputable def Ns132p577 := nat_lit 2312381727912388773867438858078061668668120918463191711255194431681 

noncomputable def Ns132p578 := BSN.cos_dyadic_bound_f 68960967 67108864 3 2 67108864 33554432 Ns132p575 Ns132p124 Ns132p576 Ns132p577 Ns132p127 Ns132p576 34686972 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 68960967) qz360 0 2 Ns132p575 Ns132p124 Ns132p576 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 68960967) (BSN.cosOddQ 67108864) 0 2 Ns132p577 Ns132p127 Ns132p576 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p579 := nat_lit 343733651665633199126122388865939719721451910995172838001790187394021699243022050096339459096806383281 

noncomputable def Ns132p580 := nat_lit 73109459120812961457702185658359285277733835586290472226003653681775623407949869937977316826801 

noncomputable def Ns132p581 := nat_lit 2083613217102486308107583616273349809294637808032576593291325946557333662132991853872403807674311597745 

noncomputable def Ns132p582 := BSN.cos_dyadic_bound_f 80413901 67108864 4 3 67108864 33554432 Ns132p579 Ns132p118 Ns132p580 Ns132p581 Ns132p121 Ns132p580 24426182 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 80413901) qz360 0 3 Ns132p579 Ns132p118 Ns132p580 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 80413901) (BSN.cosOddQ 67108864) 0 3 Ns132p581 Ns132p121 Ns132p580 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p583 := nat_lit 1108670621594535498787643569201 

noncomputable def Ns132p584 := BSN.sin_dyadic_bound_f 32448949 67108864 2 1 67108864 33554432 Ns132p583 Ns132p114 Ns132p583 Ns132p583 Ns132p115 Ns132p583 31199229 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 32448949) qz359 0 1 Ns132p583 Ns132p114 Ns132p583 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 32448949) (BSN.sinOddQ 67108864) 0 1 Ns132p583 Ns132p115 Ns132p583 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p585 := nat_lit 430996072949858473367450490878793541509780852442134050774848700416 

noncomputable def Ns132p586 := nat_lit 159869905425388120613826423105466366025250353401428409948635136 

noncomputable def Ns132p587 := nat_lit 1292668479038724643861123819790169691797292056619599295504648830976 

noncomputable def Ns132p588 := BSN.cos_dyadic_bound_f 59630828 67108864 3 2 67108864 33554432 Ns132p585 Ns132p124 Ns132p586 Ns132p587 Ns132p127 Ns132p586 42313729 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 59630828) qz360 0 2 Ns132p585 Ns132p124 Ns132p586 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 59630828) (BSN.cosOddQ 67108864) 0 2 Ns132p587 Ns132p127 Ns132p586 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p589 := Ns132p542 37945 BSN.abs_quadSignPos (BSN.cos_quad_nat3 39 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 31199229 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 14 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 42313729 67108864) qz80 rfl rfl (Ns132p574 RS133to150.d9 RS133to150.d11 RS133to150.d13 RS133to150.d17 (Ns132p578 rfl rfl) (Ns132p582 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns132p573 rfl) RS133to150.d19 RS133to150.d21 RS133to150.d23 RS133to150.d25 RS133to150.d17 (Ns132p584 rfl rfl) (Ns132p588 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns132p590 := nat_lit 488037600294893181429230082725961548229429473782899008080057285281 

noncomputable def Ns132p591 := nat_lit 204967043152033824794820760745767604604948743413873230741322401 

noncomputable def Ns132p592 := nat_lit 1463702866798375476638100606656393109479078523861869277778689211041 

noncomputable def Ns132p593 := BSN.cos_dyadic_bound_f 61512093 67108864 3 2 67108864 33554432 Ns132p590 Ns132p124 Ns132p591 Ns132p592 Ns132p127 Ns132p591 40837113 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 61512093) qz360 0 2 Ns132p590 Ns132p124 Ns132p591 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 61512093) (BSN.cosOddQ 67108864) 0 2 Ns132p592 Ns132p127 Ns132p591 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p594 := nat_lit 3106260852644700444636551213638201987733175703009673419611861131520 

noncomputable def Ns132p595 := nat_lit 2560689062376758436306041172576265020324136343609215080494244096 

noncomputable def Ns132p596 := nat_lit 8131299212730367365151233873820643634030173477611872607900740854016 

noncomputable def Ns132p597 := BSN.sin_dyadic_bound_f 84342138 67108864 3 2 67108864 33554432 Ns132p594 Ns132p108 Ns132p595 Ns132p596 Ns132p111 Ns132p595 63827613 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 84342138) qz359 0 2 Ns132p594 Ns132p108 Ns132p595 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 84342138) (BSN.sinOddQ 67108864) 0 2 Ns132p596 Ns132p111 Ns132p595 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p598 := Ns132p540 50861 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 58 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 40837113 67108864) BSN.abs_quadSignPos qz655 (BSN.sfrac_eq_quadSignPos_mul Bool.false 63827613 67108864) qz80 rfl rfl (Ns132p589 rfl rfl) (Ns132p573 rfl) RS133to150.d27 RS133to150.d29 RS133to150.d31 RS133to150.d33 RS133to150.d17 (Ns132p593 rfl rfl) (Ns132p597 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns132p599 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz77) qz77 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz77) qz77 7) 73404546 67108864 50861 67108864 73404546 67108864 50861 67108864 9852191388991488 36702273 16777216 50861 33554432 (Ns132p598 rfl) 

noncomputable def Ns132p600 := @Enclosure.Real.IsNear.mulLit_tf qz670 (Zeta.RiemannSiegel.correction qz79) 752397 2097152 1 4194304 4573176723115 8796093022208 3829863633342333 7522972906452680704 3440844446941556655 18446744073709551616 

noncomputable abbrev qz671 := (@HPow.hPow Real Real Real qz7 qz78 qz9)

noncomputable def Ns132p601 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz671 1 1 0 1 752397 2097152 1 4194304 752397 2097152 1 4194304 

noncomputable def Ns132p602 := @Enclosure.Real.IsNear.sqrt_image qz78 506315147093 8388608000 379237 8388608000 32585564 32585590 4194304 (@Enclosure.Real.IsNear.of_eq qz78 (@HMul.hMul Real Real Real qz5 qz77 qz3) Bool.false 506315147093 8388608000 379237 8388608000 (BSN.t_div_two_pi_mk qz77 379237 1000 qz80) (@Enclosure.Real.IsNear.mulLit_ff qz77 qz3 379237 1000 0 1 1335089 8388608 1 8388608 506315147093 8388608000 379237 8388608000 (Enclosure.Real.IsNear.const Bool.false 379237 1000) RS133to150.d36 rfl)) 

noncomputable abbrev qz864 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 379237 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz672 := qz864

noncomputable abbrev qz427 := qz672

noncomputable abbrev qz83 := qz427

noncomputable def Ns132p603 := @Enclosure.Real.IsNear.sqrt_image qz83 32585577 4194304 13 4194304 11690755 11690761 4194304 (@Enclosure.Real.IsNear.recentre' qz83 Bool.false 65171154 8388608 26 8388608 32585577 4194304 13 4194304 (Ns132p602 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns132p604 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz83) 5845379 2097152 3 4194304 1504793 1504795 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz83) Bool.false 23381516 8388608 6 8388608 5845379 2097152 3 4194304 (Ns132p603 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns132p605 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz83)) Bool.false 3009588 8388608 2 8388608 752397 2097152 1 4194304 (Ns132p604 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz84 := (@HMul.hMul Real Real Real qz339 qz337 qz420)

noncomputable abbrev qz673 := (@HMul.hMul Real Real Real qz843 qz863 qz863)

noncomputable abbrev qz428 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz673 qz669) qz640)

noncomputable abbrev qz85 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz428))

noncomputable def Ns132p606 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz79) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz84)) qz85) Bool.false 4573176723115 

noncomputable def Ns132p607 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz84)) qz85 17602343 2097152 2975 

noncomputable def Ns132p608 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz84)) Bool.false 70409372 8388608 11900 8388608 17602343 2097152 2975 

noncomputable def Ns132p609 := @Enclosure.Real.IsNear.recentre' (Real.cos qz84) Bool.false 999423 8388608 72228718 3587233021952 999423 8388608 36114359 1793616510976 

noncomputable def Ns132p610 := @Enclosure.Real.IsNear.cos_image qz84 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 40532187) qz365) Bool.false 40532187 8388608 41 2097152 Bool.false 999423 8388608 1 

noncomputable def Ns132p611 := nat_lit 350818980345278986857028379 

noncomputable def Ns132p612 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz79 884279719003555 140737488355328 1 500000000000000 3225449 4194304 13 4194304 2852199135380297471195 590295810358705651712 Ns132p611 

noncomputable def Ns132p613 := @Enclosure.Real.IsNear.subLit_ff_p qz83 qz1 32585577 4194304 13 4194304 7 1 0 1 3225449 3225449 4194304 13 

noncomputable def Ns132p614 := @Ns132p613 4194304 (@Enclosure.Real.IsNear.recentre' qz83 Bool.false 65171154 8388608 26 8388608 32585577 4194304 13 4194304 (Ns132p602 rfl rfl rfl rfl rfl rfl) rfl) qz366 

noncomputable def Ns132p615 := @Enclosure.Real.IsNear.recentre' qz84 Bool.false 2852199135380297471195 590295810358705651712 Ns132p611 Ns132p153 40532187 8388608 41 2097152 (@Ns132p612 Ns132p153 RS133to150.d35 (Ns132p614 rfl rfl) rfl) 

noncomputable def Ns132p616 := nat_lit 17719411483190315827671835369038582016 

noncomputable def Ns132p617 := nat_lit 10453474311811229597594867940303919455928320 

noncomputable def Ns132p618 := nat_lit 73174320182678607183164075582127436191498240 

noncomputable def Ns132p619 := BSN.sin_dyadic_bound_f 2051692748 17179869184 2 1 8388608 3424393 Ns132p616 Ns132p617 Ns132p616 Ns132p616 Ns132p618 Ns132p616 999423 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 2051692748) qz355 0 1 Ns132p616 Ns132p617 Ns132p616 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 2051692748) qz356 0 1 Ns132p616 Ns132p618 Ns132p616 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p620 := @Ns132p610 1710526 (Ns132p615 rfl) (Enclosure.sfrac_false_div 40532187 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 40532187) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 144375042176252739846144) qz367) 226375608064910080 72057594037927936 Bool.false 999423 8388608 0 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 40532187 8388608 226375608064910080 72057594037927936 0 144375042176252739846144 Ns132p87 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 999423 8388608 144375042176252739846144 Ns132p87 2051692748 17179869184 3424393 3421052 (Ns132p619 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p621 := @Enclosure.Real.IsNear.inv_image (Real.cos qz84) 999423 8388608 36114359 1793616510976 35198736 35210636 4194304 (Ns132p609 (Ns132p620 rfl rfl) rfl) rfl 

noncomputable def Ns132p622 := @Enclosure.Real.IsNear.recentre' qz85 Bool.false 259805 4194304 

noncomputable abbrev qz86 := (@HMul.hMul Real Real Real qz339 qz337 qz428)

noncomputable def Ns132p623 := @Enclosure.Real.IsNear.cos_image qz86 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 12656851)) qz365) Bool.true 12656851 8388608 

noncomputable def Ns132p624 := nat_lit 3735643226559780745235375405 

noncomputable def Ns132p625 := nat_lit 3734543471597616721624629732324997 

noncomputable def Ns132p626 := @Enclosure.Real.IsNear.recentre' qz86 Bool.true Ns132p624 Ns132p171 Ns132p625 

noncomputable abbrev qz87 := qz428

noncomputable def Ns132p627 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz87 884279719003555 140737488355328 1 500000000000000 4224504018671 

noncomputable abbrev qz429 := (@HSub.hSub Real Real Real qz635 qz673 qz669)

noncomputable abbrev qz88 := qz429

noncomputable def Ns132p628 := @Enclosure.Real.IsNear.subLit_tf qz88 qz27 3124992390895 17592186044416 138387795 17592186044416 1 16 

noncomputable abbrev qz430 := qz673

noncomputable abbrev qz89 := qz430

noncomputable def Ns132p629 := @Enclosure.Real.IsNear.subLit_ff_n qz89 qz79 10403521251601 17592186044416 83861843 17592186044416 3225449 4194304 13 4194304 

noncomputable def Ns132p630 := @Enclosure.Real.IsNear.mulLit_ff qz79 qz79 3225449 4194304 13 4194304 3225449 4194304 13 4194304 10403521251601 17592186044416 

noncomputable def Ns132p631 := nat_lit 12597542943699567447364275187218258609371341215413698868641597041490718305781932898285260081 

noncomputable def Ns132p632 := nat_lit 16900829089245060486247975968332450252475810896492774526463634199939362673096680017201 

noncomputable def Ns132p633 := nat_lit 76268318597263249989833417903166886854592402365334302524954292923073193943946688834083753265 

noncomputable def Ns132p634 := BSN.cos_dyadic_bound_f 12656851 8388608 4 3 4194304 1710526 Ns132p631 Ns132p428 Ns132p632 Ns132p633 Ns132p431 Ns132p632 259805 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 12656851) (BSN.cosEvenQ 8388608) 0 3 Ns132p631 Ns132p428 Ns132p632 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 12656851) (BSN.cosOddQ 8388608) 0 3 Ns132p633 Ns132p431 Ns132p632 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p635 := @Ns132p622 22498982 448404127744 259805 4194304 11249491 224202063872 (@Ns132p623 13 262144 Bool.false 259805 4194304 1 1710526 (@Ns132p626 Ns132p174 12656851 8388608 13 262144 (@Ns132p627 17592186044416 138387795 17592186044416 Ns132p624 Ns132p171 Ns132p625 Ns132p174 RS133to150.d35 (@Ns132p628 0 1 67592064298736 4224504018671 17592186044416 138387795 17592186044416 (@Ns132p629 13107168085100462080 3124992390895 17592186044416 138387795 17592186044416 (@Ns132p630 83861843 17592186044416 (Ns132p614 rfl rfl) (Ns132p614 rfl rfl) rfl) (Ns132p614 rfl rfl) rfl rfl) qz372 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 12656851 8388608) (BSN.cos_neg_of_bound 12656851 8388608 Bool.false 259805 4194304 1 1710526 (Ns132p634 rfl rfl)) rfl rfl) 

noncomputable def Ns132p636 := @Ns132p600 1441767728744779372745 Ns132p536 (Ns132p601 qz29 (@Enclosure.Real.IsNear.of_eq qz671 (@Inv.inv Real Real.instInv (Real.sqrt qz83)) Bool.false 752397 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz78 (BSN.t_div_two_pi_nonneg qz77 379237 1000 qz80)) Ns132p605) rfl) (@Ns132p606 8796093022208 3829863633342333 7522972906452680704 (BSN.correction_mk qz79 (BSN.cos_two_pi_p_ne_zero_mk qz77 379237 1000 7 qz80 rfl rfl (@BSN.floor_sqrt_eq_dec qz77 379237 1000 7 qz80 rfl rfl rfl))) (@Ns132p607 2097152 259805 4194304 11249491 224202063872 4573176723115 8796093022208 3829863633342333 7522972906452680704 (@Ns132p608 2097152 (Ns132p621 rfl rfl rfl rfl rfl) rfl) (Ns132p635 rfl) rfl)) 

noncomputable def Ns132p637 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz77) (hardyZApproximantRS₀ qz77) Bool.true 36913731482367578193 18446744073709551616 13398827884841335412937 Ns132p536 (@Eq.refl Real (hardyZApproximantRS₀ qz77)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz77) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz77) qz77 7) (@HMul.hMul Real Real Real qz5 qz670 (Zeta.RiemannSiegel.correction qz79))) Bool.true 36913731482367578193 18446744073709551616 13398827884841335412937 Ns132p536 (BSN.hardyZApproximantRS₀_eq qz77 7 (@BSN.floor_sqrt_eq_dec qz77 379237 1000 7 qz80 rfl rfl rfl)) (@Ns132p538 36913731482367578193 18446744073709551616 13398827884841335412937 Ns132p536 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz77) qz77 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz77) qz77 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz77) qz77 7)) Bool.true 36702273 16777216 50861 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz77) qz77 7) (Ns132p599 (Ns132p598 rfl) rfl rfl)) (Ns132p636 rfl) rfl rfl)) 

theorem RS133to150.d43 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz77) Bool.true 36913731482367578193 18446744073709551616 13398827884841335412937 Ns132p536 := Ns132p637 

noncomputable def Ns132p638 := nat_lit 13227147081766555667174260736 

noncomputable abbrev qz865 := (Enclosure.sfrac Bool.false 380768 1000)

noncomputable abbrev qz674 := qz865

noncomputable abbrev qz431 := qz674

noncomputable abbrev qz90 := qz431

noncomputable abbrev qz866 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 380768 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz675 := qz866

noncomputable abbrev qz432 := qz675

noncomputable abbrev qz91 := qz432

noncomputable abbrev qz867 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 380768 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz676 := qz867

noncomputable abbrev qz433 := qz676

noncomputable abbrev qz92 := qz433

noncomputable abbrev qz677 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz91 qz9))

noncomputable def Ns132p639 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz90) qz90 7) (@HMul.hMul Real Real Real qz5 qz677 (Zeta.RiemannSiegel.correction qz92)) 83164027 33554432 25527 16777216 28440442803561286365 147573952589676412928 12397127058517782875805 Ns132p188 Ns132p638 

noncomputable def Ns132p640 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz90) qz90 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 380768 1000 58 95 67108864 33554432 1125899906842624 Bool.false 39635764736 1239 

noncomputable def Ns132p641 := Ns132p640 120242927 40 27397080 8 130587807 40 25364760 8 Bool.false 84391604 38085 Bool.true 34861382 Bool.true 73529438 3537118876014220 1 Bool.false 58255855 Bool.true Bool.false 59675669 Bool.false Bool.false 83164027 

noncomputable def Ns132p642 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz90) qz90 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 380768 1000 39 14 67108864 33554432 1125899906842624 Bool.false 39635764736 1239 

noncomputable def Ns132p643 := Ns132p642 93032624 40 33554424 8 108007536 40 30011992 8 Bool.false 80256037 22464 Bool.false 100758635 Bool.true 14247732 3537118876014220 1 Bool.false 66947431 Bool.false Bool.false 65602084 Bool.true Bool.false 84391604 

noncomputable def Ns132p644 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz90) qz90 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 380768 1000 207 109 67108864 33554432 1125899906842624 Bool.false 39635764736 1239 

noncomputable def Ns132p645 := Ns132p644 46516304 40 47453136 16 73726608 40 38745320 8 Bool.false 67108848 1280 Bool.false 103072781 Bool.false 72866740 3537118876014220 1 Bool.false 67068016 Bool.false Bool.false 59369615 Bool.true Bool.false 80256037 

noncomputable def Ns132p646 := nat_lit 2226509781089862918703701904896203792698439755942357 

noncomputable def Ns132p647 := nat_lit 3769790821178179154096320477043599055416983552000 

noncomputable def Ns132p648 := nat_lit 5473683200000000000000000 

noncomputable def Ns132p649 := nat_lit 3841893738616150915795303792640000 

noncomputable def Ns132p650 := nat_lit 8777228233353651953154058375031685120 

noncomputable abbrev qz434 := (@Eq.refl Real qz674)

noncomputable abbrev qz93 := qz434

noncomputable def Ns132p651 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz90 380768 1000 579938079296 16000000 761536 4000 2000 Ns132p649 Ns132p650 qz93 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns132p652 := nat_lit 2918330900270105124803316160785552235165698956908766167040 

noncomputable abbrev qz435 := (Real.log (Enclosure.sfrac Bool.false 579938079296 16000000))

noncomputable abbrev qz436 := (Enclosure.sfrac Bool.false 380768 2000)

noncomputable abbrev qz94 := (@HSub.hSub Real Real Real qz342 (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 380768 4000) qz435) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 761536)))))) qz436)

noncomputable abbrev qz437 := (@HSub.hSub Real Real Real qz12 qz94 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 380768 2000) (Real.log Real.pi)))

noncomputable def Ns132p653 := @Enclosure.Real.IsNear.addLit_ft_p qz437 (Enclosure.sfrac Bool.true Ns132p649 Ns132p650) 332489139563931958517 562949953421312000 100990909604777056141 Ns132p648 Ns132p649 Ns132p650 0 1 Ns132p652 

noncomputable def Ns132p654 := nat_lit 697280264014779034667843584000 

noncomputable abbrev qz438 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 380768 2000) (Real.log Real.pi))

noncomputable def Ns132p655 := @Enclosure.Real.IsNear.subLit_ff_p qz94 qz438 455177469471457606901 562949953421312000 1214900244263968063 171052600000000000000000 457049645139 2097152000 11899 1048576000 Ns132p654 332489139563931958517 562949953421312000 

noncomputable abbrev qz95 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 380768 4000) qz435) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 761536))))))

noncomputable def Ns132p656 := @Enclosure.Real.IsNear.subLit_ff_p qz95 qz436 562354133403620670709 562949953421312000 1214900244263968063 171052600000000000000000 380768 2000 0 1 910354938942915213802000 455177469471457606901 562949953421312000 1214900244263968063 171052600000000000000000 

noncomputable def Ns132p657 := nat_lit 1266308932823402125032025034779000832 

noncomputable def Ns132p658 := nat_lit 12691409499826877781508096 

noncomputable def Ns132p659 := nat_lit 22300944605188494348719989906407704301471101091840 

noncomputable def Ns132p660 := nat_lit 18909450674055249177713953020676942105461915648 

noncomputable def Ns132p661 := nat_lit 28772950907397013128577351614391923788218368 

noncomputable def Ns132p662 := BSN.log_dyadic_bound 55650079296 1104226079296 3 2 Ns132p659 33554432 13684208 Ns132p660 Ns132p661 3384977 1159876158592 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 55650079296) (BSN.artanhQ 1104226079296) 0 2 Ns132p660 Ns132p659 Ns132p661 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns132p663 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 380768 4000) qz435 380768 4000 0 1 47279184683512441 4503599627370496 12500002565789 171052600000000000000 562575018549114535459 562949953421312000 148737530530323311 21381575000000000000000 (Enclosure.Real.IsNear.const Bool.false 380768 4000) (BSN.isNear_log_sfrac 579938079296 16000000 47279184683512441 4503599627370496 12500002565789 171052600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 579938079296) qz350)) Bool.false Ns132p658 Ns132p87 1000000205263120 13684208000000000000000 47279184683512441 4503599627370496 12500002565789 171052600000000000000 (BSN.log_rat_reduce_isNear 579938079296 16000000 15 1159876158592 1048576000000 3384977 33554432 24973259072661432 36028797018963968 13684208 1000000000000000 rfl rfl rfl rfl (Ns132p662 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns132p664 := BSN.arctan_dyadic_bound_f 1000 761536 1 0 4194304 1710526 0 1 1 0 1 1 5507 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 761536) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 761536) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz439 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 761536)))

noncomputable def Ns132p665 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz439 884279719003555 562949953421312 1 2000000000000000 5507 4194304 1 1710526 3705837797141995585536 883540581975459 562949953421312 1000000000855263 1710526000000000000000 qz17 (Ns132p664 rfl) rfl rfl 

noncomputable def Ns132p666 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 380768 4000) qz435) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz439)) 562575018549114535459 562949953421312000 148737530530323311 21381575000000000000000 883540581975459 2251799813685248 1000000000855263 6842104000000000000000 Ns132p657 562354133403620670709 562949953421312000 1214900244263968063 171052600000000000000000 (Ns132p663 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz439) 1 4 0 1 883540581975459 562949953421312 1000000000855263 1710526000000000000000 883540581975459 2251799813685248 1000000000855263 6842104000000000000000 qz353 Ns132p665 rfl) 

noncomputable def Ns132p667 := @Ns132p653 Ns132p646 Ns132p647 100990909604777056141 Ns132p648 (@Ns132p655 100990909604777056141 Ns132p648 (Ns132p656 (Ns132p666 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 380768 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz436 (Real.log Real.pi) 380768 2000 0 1 38410761 33554432 1 16777216 457049645139 2097152000 11899 1048576000 (Enclosure.Real.IsNear.const Bool.false 380768 2000) RS133to150.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns132p649 Ns132p650) 

noncomputable def Ns132p668 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz90) Bool.false Ns132p646 Ns132p647 100990909604777056141 Ns132p648 77413603 131072 155 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz90) (@HAdd.hAdd Real Real Real qz354 qz437 (Enclosure.sfrac Bool.true Ns132p649 Ns132p650)) Bool.false Ns132p646 Ns132p647 100990909604777056141 Ns132p648 Ns132p651 (Ns132p667 rfl rfl)) 

noncomputable def Ns132p669 := nat_lit 139810559023339972136315667301297892394156782176607226118872143894627385365566523965440 

noncomputable def Ns132p670 := nat_lit 280551658268330348442200830721565997690826248913728017785919994696838601142934962176 

noncomputable def Ns132p671 := nat_lit 365716285233455963602396517777469087512244520345253842092059363542133984888919001399296 

noncomputable def Ns132p672 := BSN.sin_dyadic_bound_f 26977494024 17179869184 3 2 8388608 3424393 Ns132p669 Ns132p99 Ns132p670 Ns132p671 Ns132p102 Ns132p670 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26977494024) qz355 0 2 Ns132p669 Ns132p99 Ns132p670 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26977494024) qz356 0 2 Ns132p671 Ns132p102 Ns132p670 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p673 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz90) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 77413603) (@Nat.cast Real Real.instNatCast 131072)) Bool.false 77413603 131072 155 8388608 Bool.false 8388606 8388608 1 1710526 (Ns132p668 rfl) (Enclosure.sfrac_false_div 77413603 131072) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 77413603) (@Nat.cast Real Real.instNatCast 131072)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 29662068368180108066816) (@Nat.cast Real Real.instNatCast 18889465931478580854784)) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 93 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 77413603 131072 226375608064910080 72057594037927936 93 29662068368180108066816 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388606 8388608 29662068368180108066816 18889465931478580854784 26977494024 17179869184 3424393 3421052 (Ns132p672 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p674 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz90) Bool.false Ns132p646 Ns132p647 100990909604777056141 Ns132p648 39635764736 67108864 1239 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz90) (@HAdd.hAdd Real Real Real qz354 qz437 (Enclosure.sfrac Bool.true Ns132p649 Ns132p650)) Bool.false Ns132p646 Ns132p647 100990909604777056141 Ns132p648 Ns132p651 (Ns132p667 rfl rfl)) 

noncomputable def Ns132p675 := Ns132p645 22464 BSN.abs_quadSignPos (BSN.cos_quad_nat3 207 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 67068016 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 109 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 59369615 67108864) qz93 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz90) qz90 1) Bool.false 4194303 4194304 136760069 7174466043904 67108848 67108864 1280 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz90) qz90 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz90)) Bool.false 4194303 4194304 136760069 7174466043904 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz90) qz90) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz90)) Bool.false 8388606 8388608 273520138 14348932087808 4194303 4194304 136760069 7174466043904 (Ns132p673 rfl rfl) rfl)) rfl) (Ns132p674 rfl) RS133to150.d7 

noncomputable def Ns132p676 := nat_lit 2413864426899707505080667592457091988375961260088802791667558662366245212227634652553156446143286960561 

noncomputable def Ns132p677 := nat_lit 1437897492970548369339061013183508635017255197121253750798704216250464584067804156460745212387761 

noncomputable def Ns132p678 := nat_lit 12055611509906398835948445731201165841819880578524209800752933929446622967546369822030008229377207001521 

noncomputable def Ns132p679 := BSN.sin_dyadic_bound_f 103072781 67108864 4 3 67108864 33554432 Ns132p676 Ns132p233 Ns132p677 Ns132p678 Ns132p236 Ns132p677 67068016 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 103072781) qz359 0 3 Ns132p676 Ns132p233 Ns132p677 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 103072781) (BSN.sinOddQ 67108864) 0 3 Ns132p678 Ns132p236 Ns132p677 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p680 := nat_lit 1729889123855492751637672697486452997179565213808180540920995840000 

noncomputable def Ns132p681 := nat_lit 794757655153308902416006992946484953001813379404931097600000000 

noncomputable def Ns132p682 := nat_lit 4529375240560804230351897815428320683641620243073817242539827200000 

noncomputable def Ns132p683 := BSN.sin_dyadic_bound_f 72866740 67108864 3 2 67108864 33554432 Ns132p680 Ns132p108 Ns132p681 Ns132p682 Ns132p111 Ns132p681 59369615 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 72866740) qz359 0 2 Ns132p680 Ns132p108 Ns132p681 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 72866740) (BSN.sinOddQ 67108864) 0 2 Ns132p682 Ns132p111 Ns132p681 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p684 := nat_lit 2203924369282124848566316852162402299100626883358145760806352251393717081405973451270415378542409540625 

noncomputable def Ns132p685 := nat_lit 1094932393585878724374089210360425728723988596476950995686866670521540324414697876300859619140625 

noncomputable def Ns132p686 := nat_lit 11008189176282388618364863392527141830705568537361776196430407230635245817465670313561991018809571140625 

noncomputable def Ns132p687 := BSN.sin_dyadic_bound_f 100758635 67108864 4 3 67108864 33554432 Ns132p684 Ns132p233 Ns132p685 Ns132p686 Ns132p236 Ns132p685 66947431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 100758635) qz359 0 3 Ns132p684 Ns132p233 Ns132p685 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 100758635) (BSN.sinOddQ 67108864) 0 3 Ns132p686 Ns132p236 Ns132p685 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p688 := nat_lit 41208134064941619467501342976 

noncomputable def Ns132p689 := BSN.cos_dyadic_bound_f 14247732 67108864 2 1 67108864 33554432 Ns132p688 Ns132p135 Ns132p688 Ns132p688 Ns132p136 Ns132p688 65602084 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 14247732) qz360 0 1 Ns132p688 Ns132p135 Ns132p688 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 14247732) (BSN.cosOddQ 67108864) 0 1 Ns132p688 Ns132p136 Ns132p688 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p690 := Ns132p643 38085 BSN.abs_quadSignPos (BSN.cos_quad_nat3 39 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66947431 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 14 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 65602084 67108864) qz93 rfl rfl (Ns132p675 RS133to150.d9 RS133to150.d11 RS133to150.d13 RS133to150.d17 (Ns132p679 rfl rfl) (Ns132p683 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns132p674 rfl) RS133to150.d19 RS133to150.d21 RS133to150.d23 RS133to150.d25 RS133to150.d17 (Ns132p687 rfl rfl) (Ns132p689 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns132p691 := nat_lit 50329898463366240440769374664880544048643471332846809390084301056 

noncomputable def Ns132p692 := nat_lit 2181507939082000027931007923745351222263925474692079508562176 

noncomputable def Ns132p693 := nat_lit 150985332374220557322252261978794141443485886147591044011235778816 

noncomputable def Ns132p694 := BSN.cos_dyadic_bound_f 34861382 67108864 3 2 67108864 33554432 Ns132p691 Ns132p124 Ns132p692 Ns132p693 Ns132p127 Ns132p692 58255855 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 34861382) qz360 0 2 Ns132p691 Ns132p124 Ns132p692 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 34861382) (BSN.cosOddQ 67108864) 0 2 Ns132p693 Ns132p127 Ns132p692 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p695 := nat_lit 1793714226679794055203760698159792209750878236036586915246334705920 

noncomputable def Ns132p696 := nat_lit 854456529132936307275713071178041107362815530643384470064496896 

noncomputable def Ns132p697 := nat_lit 4696439568828483485798069721636596101840379393046209774598391234816 

noncomputable def Ns132p698 := BSN.sin_dyadic_bound_f 73529438 67108864 3 2 67108864 33554432 Ns132p695 Ns132p108 Ns132p696 Ns132p697 Ns132p111 Ns132p696 59675669 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 73529438) qz359 0 2 Ns132p695 Ns132p108 Ns132p696 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 73529438) (BSN.sinOddQ 67108864) 0 2 Ns132p697 Ns132p111 Ns132p696 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p699 := Ns132p641 51054 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 58 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 58255855 67108864) BSN.abs_quadSignPos qz655 (BSN.sfrac_eq_quadSignPos_mul Bool.false 59675669 67108864) qz93 rfl rfl (Ns132p690 rfl rfl) (Ns132p674 rfl) RS133to150.d27 RS133to150.d29 RS133to150.d31 RS133to150.d33 RS133to150.d17 (Ns132p694 rfl rfl) (Ns132p698 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns132p700 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz90) qz90 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz90) qz90 7) 83164027 67108864 51054 67108864 83164027 67108864 51054 67108864 11162086755270656 83164027 33554432 25527 16777216 (Ns132p699 rfl) 

noncomputable def Ns132p701 := @Enclosure.Real.IsNear.mulLit_tf qz677 (Zeta.RiemannSiegel.correction qz92) 3006559 8388608 1 8388608 9459466055235 17592186044416 2060334190437075 7522972906452680704 28440442803561286365 147573952589676412928 

noncomputable abbrev qz678 := (@HPow.hPow Real Real Real qz7 qz91 qz9)

noncomputable def Ns132p702 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz678 1 1 0 1 3006559 8388608 1 8388608 3006559 8388608 1 8388608 

noncomputable def Ns132p703 := @Enclosure.Real.IsNear.sqrt_image qz91 15886224011 262144000 11899 262144000 32651273 32651298 4194304 (@Enclosure.Real.IsNear.of_eq qz91 (@HMul.hMul Real Real Real qz5 qz90 qz3) Bool.false 15886224011 262144000 11899 262144000 (BSN.t_div_two_pi_mk qz90 380768 1000 qz93) (@Enclosure.Real.IsNear.mulLit_ff qz90 qz3 380768 1000 0 1 1335089 8388608 1 8388608 15886224011 262144000 11899 262144000 (Enclosure.Real.IsNear.const Bool.false 380768 1000) RS133to150.d36 rfl)) 

noncomputable abbrev qz868 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 380768 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz679 := qz868

noncomputable abbrev qz440 := qz679

noncomputable abbrev qz96 := qz440

noncomputable def Ns132p704 := @Enclosure.Real.IsNear.sqrt_image qz96 65302571 8388608 25 8388608 11702536 11702542 4194304 (@Enclosure.Real.IsNear.recentre' qz96 Bool.false 65302571 8388608 25 8388608 65302571 8388608 25 8388608 (Ns132p703 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns132p705 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz96) 11702539 4194304 3 4194304 1503279 1503280 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz96) Bool.false 23405078 8388608 6 8388608 11702539 4194304 3 4194304 (Ns132p704 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns132p706 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz96)) Bool.false 3006559 8388608 1 8388608 3006559 8388608 1 8388608 (Ns132p705 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz97 := (@HMul.hMul Real Real Real qz339 qz337 qz433)

noncomputable abbrev qz680 := (@HMul.hMul Real Real Real qz843 qz867 qz867)

noncomputable abbrev qz441 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz680 qz676) qz640)

noncomputable abbrev qz98 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz441))

noncomputable def Ns132p707 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz92) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz97)) qz98) Bool.false 9459466055235 

noncomputable def Ns132p708 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz97)) qz98 19405665 4194304 109 

noncomputable def Ns132p709 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz97)) Bool.false 38811330 8388608 3488 8388608 19405665 4194304 109 

noncomputable def Ns132p710 := @Enclosure.Real.IsNear.recentre' (Real.cos qz97) Bool.false 1813098 8388608 139325858 7174466043904 906549 4194304 69662929 3587233021952 

noncomputable def Ns132p711 := @Enclosure.Real.IsNear.cos_image qz97 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2584869) (@Nat.cast Real Real.instNatCast 524288)) Bool.false 2584869 524288 79 4194304 Bool.false 1813098 8388608 1 

noncomputable def Ns132p712 := nat_lit 134930377056528558338632931 

noncomputable def Ns132p713 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz92 884279719003555 140737488355328 1 500000000000000 6582315 8388608 25 8388608 5820607658592885129825 1180591620717411303424 Ns132p712 

noncomputable def Ns132p714 := @Enclosure.Real.IsNear.subLit_ff_p qz96 qz1 65302571 8388608 25 8388608 7 1 0 1 6582315 6582315 8388608 25 

noncomputable def Ns132p715 := @Ns132p714 8388608 (@Enclosure.Real.IsNear.recentre' qz96 Bool.false 65302571 8388608 25 8388608 65302571 8388608 25 8388608 (Ns132p703 rfl rfl rfl rfl rfl rfl) rfl) qz366 

noncomputable def Ns132p716 := @Enclosure.Real.IsNear.recentre' qz97 Bool.false 5820607658592885129825 1180591620717411303424 Ns132p712 Ns132p268 2584869 524288 79 4194304 (@Ns132p713 Ns132p268 RS133to150.d35 (Ns132p715 rfl rfl) rfl) 

noncomputable def Ns132p717 := nat_lit 196231379907186990084434248627924930816 

noncomputable def Ns132p718 := BSN.sin_dyadic_bound_f 3742761164 17179869184 2 1 8388608 3424393 Ns132p717 Ns132p617 Ns132p717 Ns132p717 Ns132p618 Ns132p717 1813098 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 3742761164) qz355 0 1 Ns132p717 Ns132p617 Ns132p717 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 3742761164) qz356 0 1 Ns132p717 Ns132p618 Ns132p717 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p719 := @Ns132p711 1710526 (Ns132p716 rfl) (Enclosure.sfrac_false_div 2584869 524288) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2584869) (@Nat.cast Real Real.instNatCast 524288)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16460837683042763931648) (@Nat.cast Real Real.instNatCast 75557863725914323419136)) 226375608064910080 72057594037927936 Bool.false 1813098 8388608 0 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 2584869 524288 226375608064910080 72057594037927936 0 16460837683042763931648 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1813098 8388608 16460837683042763931648 75557863725914323419136 3742761164 17179869184 3424393 3421052 (Ns132p718 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p720 := @Enclosure.Real.IsNear.inv_image (Real.cos qz97) 906549 4194304 69662929 3587233021952 19403921 19407409 4194304 (Ns132p710 (Ns132p719 rfl rfl) rfl) rfl 

noncomputable def Ns132p721 := @Enclosure.Real.IsNear.recentre' qz98 Bool.false 487459 4194304 

noncomputable abbrev qz99 := (@HMul.hMul Real Real Real qz339 qz337 qz441)

noncomputable def Ns132p722 := @Enclosure.Real.IsNear.cos_image qz99 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 3049917)) qz368) Bool.true 3049917 2097152 

noncomputable def Ns132p723 := nat_lit 14402826202466328814929963445 

noncomputable def Ns132p724 := nat_lit 14540949515863881985045227032883233 

noncomputable def Ns132p725 := @Enclosure.Real.IsNear.recentre' qz99 Bool.true Ns132p723 Ns132p285 Ns132p724 

noncomputable abbrev qz100 := qz441

noncomputable def Ns132p726 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz100 884279719003555 140737488355328 1 500000000000000 16287636019399 

noncomputable abbrev qz442 := (@HSub.hSub Real Real Real qz635 qz680 qz676)

noncomputable abbrev qz101 := qz442

noncomputable def Ns132p727 := @Enclosure.Real.IsNear.subLit_tf qz101 qz27 11889589508295 70368744177664 538831575 70368744177664 1 16 

noncomputable abbrev qz443 := qz680

noncomputable abbrev qz102 := qz443

noncomputable def Ns132p728 := @Enclosure.Real.IsNear.subLit_ff_n qz102 qz92 43326870759225 70368744177664 329116375 70368744177664 6582315 8388608 25 8388608 

noncomputable def Ns132p729 := @Enclosure.Real.IsNear.mulLit_ff qz92 qz92 6582315 8388608 25 8388608 6582315 8388608 25 8388608 43326870759225 70368744177664 

noncomputable def Ns132p730 := nat_lit 647846881330514894308128351786439761288523062221136758180024445512132531198571545841 

noncomputable def Ns132p731 := nat_lit 647822828804294125259837020222157401466589186464618237729540144112338752210161 

noncomputable def Ns132p732 := nat_lit 3923309562384689315730984923205323274300353380348329975929332601781345500565208270065 

noncomputable def Ns132p733 := BSN.cos_dyadic_bound_f 3049917 2097152 4 3 4194304 1710526 Ns132p730 Ns132p180 Ns132p731 Ns132p732 Ns132p183 Ns132p731 487459 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 3049917) (BSN.cosEvenQ 2097152) 0 3 Ns132p730 Ns132p180 Ns132p731 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 3049917) (BSN.cosOddQ 2097152) 0 3 Ns132p732 Ns132p183 Ns132p731 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p734 := @Ns132p721 174860278 3587233021952 487459 4194304 87430139 1793616510976 (@Ns132p722 101 2097152 Bool.false 487459 4194304 1 1710526 (@Ns132p725 Ns132p288 3049917 2097152 101 2097152 (@Ns132p726 70368744177664 538831575 70368744177664 Ns132p723 Ns132p285 Ns132p724 Ns132p288 RS133to150.d35 (@Ns132p727 0 1 260602176310384 16287636019399 70368744177664 538831575 70368744177664 (@Ns132p728 99737105665999503360 11889589508295 70368744177664 538831575 70368744177664 (@Ns132p729 329116375 70368744177664 (Ns132p715 rfl rfl) (Ns132p715 rfl rfl) rfl) (Ns132p715 rfl rfl) rfl rfl) qz372 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 3049917 2097152) (BSN.cos_neg_of_bound 3049917 2097152 Bool.false 487459 4194304 1 1710526 (Ns132p733 rfl rfl)) rfl rfl) 

noncomputable def Ns132p735 := @Ns132p701 12397127058517782875805 Ns132p188 (Ns132p702 qz29 (@Enclosure.Real.IsNear.of_eq qz678 (@Inv.inv Real Real.instInv (Real.sqrt qz96)) Bool.false 3006559 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz91 (BSN.t_div_two_pi_nonneg qz90 380768 1000 qz93)) Ns132p706) rfl) (@Ns132p707 17592186044416 2060334190437075 7522972906452680704 (BSN.correction_mk qz92 (BSN.cos_two_pi_p_ne_zero_mk qz90 380768 1000 7 qz93 rfl rfl (@BSN.floor_sqrt_eq_dec qz90 380768 1000 7 qz93 rfl rfl rfl))) (@Ns132p708 262144 487459 4194304 87430139 1793616510976 9459466055235 17592186044416 2060334190437075 7522972906452680704 (@Ns132p709 262144 (Ns132p720 rfl rfl rfl rfl rfl) rfl) (Ns132p734 rfl) rfl)) 

noncomputable def Ns132p736 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz90) (hardyZApproximantRS₀ qz90) Bool.false 394199701600270142173 147573952589676412928 204436056441535363206813 Ns132p188 (@Eq.refl Real (hardyZApproximantRS₀ qz90)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz90) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz90) qz90 7) (@HMul.hMul Real Real Real qz5 qz677 (Zeta.RiemannSiegel.correction qz92))) Bool.false 394199701600270142173 147573952589676412928 204436056441535363206813 Ns132p188 (BSN.hardyZApproximantRS₀_eq qz90 7 (@BSN.floor_sqrt_eq_dec qz90 380768 1000 7 qz93 rfl rfl rfl)) (@Ns132p639 394199701600270142173 147573952589676412928 204436056441535363206813 Ns132p188 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz90) qz90 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz90) qz90 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz90) qz90 7)) Bool.false 83164027 33554432 25527 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz90) qz90 7) (Ns132p700 (Ns132p699 rfl) rfl rfl)) (Ns132p735 rfl) rfl rfl)) 

theorem RS133to150.d44 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz90) Bool.false 394199701600270142173 147573952589676412928 204436056441535363206813 Ns132p188 := Ns132p736 

noncomputable def Ns132p737 := nat_lit 4251813848656669323558912 

noncomputable abbrev qz869 := (Enclosure.sfrac Bool.false 382298 1000)

noncomputable abbrev qz681 := qz869

noncomputable abbrev qz444 := qz681

noncomputable abbrev qz103 := qz444

noncomputable abbrev qz870 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 382298 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz682 := qz870

noncomputable abbrev qz445 := qz682

noncomputable abbrev qz104 := qz445

noncomputable abbrev qz871 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 382298 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz683 := qz871

noncomputable abbrev qz446 := qz683

noncomputable abbrev qz105 := qz446

noncomputable abbrev qz684 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz104 qz9))

noncomputable def Ns132p738 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz103) qz103 7) (@HMul.hMul Real Real Real qz5 qz684 (Zeta.RiemannSiegel.correction qz105)) 15587553 4194304 51269 33554432 57457069353598005 288230376151711744 2195630695878652550875 Ns132p333 Ns132p737 

noncomputable def Ns132p739 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz103) qz103 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 382298 1000 58 95 67108864 33554432 1125899906842624 Bool.false 39846576167 1244 

noncomputable def Ns132p740 := Ns132p739 120242927 40 27397080 8 130587807 40 25364760 8 Bool.true 117855681 38248 Bool.true 8021629 Bool.true 62517352 3537118876014220 1 Bool.false 66630015 Bool.true Bool.false 53859171 Bool.false Bool.true 124700424 

noncomputable def Ns132p741 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz103) qz103 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 382298 1000 40 13 67108864 33554432 1125899906842624 Bool.false 39846576167 1244 

noncomputable def Ns132p742 := Ns132p741 93032624 40 33554424 8 108007536 40 30011992 8 Bool.true 110544381 22565 Bool.false 63815794 Bool.true 74102188 3537118876014220 1 Bool.false 38985339 Bool.false Bool.false 59935496 Bool.true Bool.true 117855681 

noncomputable def Ns132p743 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz103) qz103 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 382298 1000 209 110 67108864 33554432 1125899906842624 Bool.false 39846576167 1244 

noncomputable def Ns132p744 := Ns132p743 46516304 40 47453136 16 73726608 40 38745320 8 Bool.true 67108840 1296 Bool.false 31885553 Bool.false 65462104 3537118876014220 1 Bool.false 30699326 Bool.true Bool.false 37633719 Bool.true Bool.true 110544381 

noncomputable def Ns132p745 := nat_lit 2347890364190130139952569397377457829854427195876197521 

noncomputable def Ns132p746 := nat_lit 3954273372807045708751311656382032773673782345728000 

noncomputable def Ns132p747 := nat_lit 87578931200000000000000000 

noncomputable def Ns132p748 := nat_lit 3919703794621140609242712304640000 

noncomputable def Ns132p749 := nat_lit 8990976704824437794630538647611576320 

noncomputable abbrev qz447 := (@Eq.refl Real qz681)

noncomputable abbrev qz106 := qz447

noncomputable def Ns132p750 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz103 382298 1000 584608043216 16000000 764596 4000 2000 Ns132p748 Ns132p749 qz106 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns132p751 := nat_lit 48084794658613865266228621258290336355418668971544525230080 

noncomputable abbrev qz448 := (Real.log (Enclosure.sfrac Bool.false 584608043216 16000000))

noncomputable abbrev qz449 := (Enclosure.sfrac Bool.false 382298 2000)

noncomputable abbrev qz107 := (@HSub.hSub Real Real Real qz342 (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 382298 4000) qz448) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 764596)))))) qz449)

noncomputable abbrev qz450 := (@HSub.hSub Real Real Real qz12 qz107 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 382298 2000) (Real.log Real.pi)))

noncomputable def Ns132p752 := @Enclosure.Real.IsNear.addLit_ft_p qz450 (Enclosure.sfrac Bool.true Ns132p748 Ns132p749) 5348120848579808535269 9007199254740992000 1622295939158165062891 Ns132p747 Ns132p748 Ns132p749 0 1 Ns132p751 

noncomputable def Ns132p753 := nat_lit 179453157341453482069703262208000 

noncomputable abbrev qz451 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 382298 2000) (Real.log Real.pi))

noncomputable def Ns132p754 := @Enclosure.Real.IsNear.subLit_ff_p qz107 qz451 7319021896860640551653 9007199254740992000 2439362990490764711 342105200000000000000000 7342178554389 33554432000 191149 16777216000 Ns132p753 5348120848579808535269 9007199254740992000 

noncomputable def Ns132p755 := nat_lit 14638043793721281103306000 

noncomputable abbrev qz108 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 382298 4000) qz448) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 764596))))))

noncomputable def Ns132p756 := @Enclosure.Real.IsNear.subLit_ff_p qz108 qz449 9040739027205126431461 9007199254740992000 2439362990490764711 342105200000000000000000 382298 2000 0 1 Ns132p755 7319021896860640551653 9007199254740992000 2439362990490764711 342105200000000000000000 

noncomputable def Ns132p757 := nat_lit 20357934457037453947919495593698787328 

noncomputable def Ns132p758 := nat_lit 12701105425565433288720384 

noncomputable def Ns132p759 := nat_lit 22680602871896627553260201156341820129035027415040 

noncomputable def Ns132p760 := nat_lit 22410178555726570861886745812150452617635954688 

noncomputable def Ns132p761 := nat_lit 39716212962241229316368698242358788253483008 

noncomputable def Ns132p762 := BSN.log_dyadic_bound 60320043216 1108896043216 3 2 Ns132p759 33554432 13684208 Ns132p760 Ns132p761 3654093 1169216086432 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 60320043216) (BSN.artanhQ 1108896043216) 0 2 Ns132p760 Ns132p759 Ns132p761 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns132p763 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 382298 4000) qz448 382298 4000 0 1 47315304821600889 4503599627370496 12500002565789 171052600000000000000 9044273201344188331461 9007199254740992000 2389362990448001561 342105200000000000000000 (Enclosure.Real.IsNear.const Bool.false 382298 4000) (BSN.isNear_log_sfrac 584608043216 16000000 47315304821600889 4503599627370496 12500002565789 171052600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 584608043216) qz350)) Bool.false Ns132p758 Ns132p87 1000000205263120 13684208000000000000000 47315304821600889 4503599627370496 12500002565789 171052600000000000000 (BSN.log_rat_reduce_isNear 584608043216 16000000 15 1169216086432 1048576000000 3654093 33554432 24973259072661432 36028797018963968 13684208 1000000000000000 rfl rfl rfl rfl (Ns132p762 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns132p764 := BSN.arctan_dyadic_bound_f 1000 764596 1 0 4194304 1710526 0 1 1 0 1 1 5485 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 764596) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 764596) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz452 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 764596)))

noncomputable def Ns132p765 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz452 884279719003555 562949953421312 1 2000000000000000 5485 4194304 1 1710526 3705850182040970854400 883543534765475 562949953421312 1000000000855263 1710526000000000000000 qz17 (Ns132p764 rfl) rfl rfl 

noncomputable def Ns132p766 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 382298 4000) qz448) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz452)) 9044273201344188331461 9007199254740992000 2389362990448001561 342105200000000000000000 883543534765475 2251799813685248 1000000000855263 6842104000000000000000 Ns132p757 9040739027205126431461 9007199254740992000 2439362990490764711 342105200000000000000000 (Ns132p763 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz452) 1 4 0 1 883543534765475 562949953421312 1000000000855263 1710526000000000000000 883543534765475 2251799813685248 1000000000855263 6842104000000000000000 qz353 Ns132p765 rfl) 

noncomputable def Ns132p767 := @Ns132p752 Ns132p745 Ns132p746 1622295939158165062891 Ns132p747 (@Ns132p754 1622295939158165062891 Ns132p747 (Ns132p756 (Ns132p766 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 382298 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz449 (Real.log Real.pi) 382298 2000 0 1 38410761 33554432 1 16777216 7342178554389 33554432000 191149 16777216000 (Enclosure.Real.IsNear.const Bool.false 382298 2000) RS133to150.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns132p748 Ns132p749) 

noncomputable def Ns132p768 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz103) Bool.false Ns132p745 Ns132p746 1622295939158165062891 Ns132p747 1245205505 2097152 157 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz103) (@HAdd.hAdd Real Real Real qz354 qz450 (Enclosure.sfrac Bool.true Ns132p748 Ns132p749)) Bool.false Ns132p745 Ns132p746 1622295939158165062891 Ns132p747 Ns132p750 (Ns132p767 rfl rfl)) 

noncomputable def Ns132p769 := nat_lit 139718641184778803679949260785764103016235533132795491577405817121728571853062500000000 

noncomputable def Ns132p770 := nat_lit 280183622413085365854336134537972456663363577947697153451977041030883789062500000000 

noncomputable def Ns132p771 := nat_lit 365476143904799490474198186411558790588876188602549063501902510585715304909062500000000 

noncomputable def Ns132p772 := BSN.sin_dyadic_bound_f 26973067750 17179869184 3 2 8388608 3424393 Ns132p769 Ns132p99 Ns132p770 Ns132p771 Ns132p102 Ns132p770 8388605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26973067750) qz355 0 2 Ns132p769 Ns132p99 Ns132p770 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26973067750) qz356 0 2 Ns132p771 Ns132p102 Ns132p770 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz453 := (@Nat.cast Real Real.instNatCast 302231454903657293676544)

noncomputable def Ns132p773 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz103) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1245205505) qz368) Bool.false 1245205505 2097152 157 8388608 Bool.true 8388605 8388608 1 1710526 (Ns132p768 rfl) (Enclosure.sfrac_false_div 1245205505 2097152) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1245205505) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474515226053640758231040) qz453) 226375608064910080 72057594037927936 Bool.false 8388605 8388608 94 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q1 1245205505 2097152 226375608064910080 72057594037927936 94 474515226053640758231040 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388605 8388608 474515226053640758231040 302231454903657293676544 26973067750 17179869184 3424393 3421052 (Ns132p772 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p774 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz103) Bool.false Ns132p745 Ns132p746 1622295939158165062891 Ns132p747 39846576167 67108864 1244 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz103) (@HAdd.hAdd Real Real Real qz354 qz450 (Enclosure.sfrac Bool.true Ns132p748 Ns132p749)) Bool.false Ns132p745 Ns132p746 1622295939158165062891 Ns132p747 Ns132p750 (Ns132p767 rfl rfl)) 

noncomputable def Ns132p775 := Ns132p744 22565 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 209 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 30699326 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 110 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 37633719 67108864) qz106 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz103) qz103 1) Bool.true 8388605 8388608 138470595 7174466043904 67108840 67108864 1296 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz103) qz103 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz103)) Bool.true 8388605 8388608 138470595 7174466043904 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz103) qz103) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz103)) Bool.true 8388605 8388608 276941190 14348932087808 8388605 8388608 138470595 7174466043904 (Ns132p773 rfl rfl) rfl)) rfl) (Ns132p774 rfl) RS133to150.d7 

noncomputable def Ns132p776 := nat_lit 1033655485933963454690231724481 

noncomputable def Ns132p777 := BSN.sin_dyadic_bound_f 31885553 67108864 2 1 67108864 33554432 Ns132p776 Ns132p114 Ns132p776 Ns132p776 Ns132p115 Ns132p776 30699326 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 31885553) qz359 0 1 Ns132p776 Ns132p114 Ns132p776 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 31885553) (BSN.sinOddQ 67108864) 0 1 Ns132p776 Ns132p115 Ns132p776 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p778 := nat_lit 626069663407359279474735322629643496945134996061222475743956566016 

noncomputable def Ns132p779 := nat_lit 337224933666301720209571312123484034001179818365960958022516736 

noncomputable def Ns132p780 := nat_lit 1877534540354745234983786825264683522767402628546935505315824664576 

noncomputable def Ns132p781 := BSN.cos_dyadic_bound_f 65462104 67108864 3 2 67108864 33554432 Ns132p778 Ns132p124 Ns132p779 Ns132p780 Ns132p127 Ns132p779 37633719 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 65462104) qz360 0 2 Ns132p778 Ns132p124 Ns132p779 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 65462104) (BSN.cosOddQ 67108864) 0 2 Ns132p780 Ns132p127 Ns132p779 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p782 := nat_lit 565396180020739289642088084695956440972197874590342151577010749696 

noncomputable def Ns132p783 := nat_lit 275058719590189839802320971829895089633614352065937454158889216 

noncomputable def Ns132p784 := nat_lit 1695638422623037489246659612144209532737326395066894579822714470656 

noncomputable def Ns132p785 := BSN.cos_dyadic_bound_f 63815794 67108864 3 2 67108864 33554432 Ns132p782 Ns132p124 Ns132p783 Ns132p784 Ns132p127 Ns132p783 38985339 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 63815794) qz360 0 2 Ns132p782 Ns132p124 Ns132p783 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 63815794) (BSN.cosOddQ 67108864) 0 2 Ns132p784 Ns132p127 Ns132p783 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p786 := nat_lit 1850286217830156643083466287315745974958175639493264854853441617920 

noncomputable def Ns132p787 := nat_lit 909176605079785670196261907764212339984717889342504181023440896 

noncomputable def Ns132p788 := nat_lit 4844515713146947745562093947500097400149532369709139136894499618816 

noncomputable def Ns132p789 := BSN.sin_dyadic_bound_f 74102188 67108864 3 2 67108864 33554432 Ns132p786 Ns132p108 Ns132p787 Ns132p788 Ns132p111 Ns132p787 59935496 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 74102188) qz359 0 2 Ns132p786 Ns132p108 Ns132p787 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 74102188) (BSN.sinOddQ 67108864) 0 2 Ns132p788 Ns132p111 Ns132p787 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p790 := Ns132p742 38248 BSN.abs_quadSignPos (BSN.cos_quad_nat0 40 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 38985339 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 13 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 59935496 67108864) qz106 rfl rfl (Ns132p775 RS133to150.d9 RS133to150.d11 RS133to150.d13 RS133to150.d17 (Ns132p777 rfl rfl) (Ns132p781 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns132p774 rfl) RS133to150.d19 RS133to150.d21 RS133to150.d23 RS133to150.d25 RS133to150.d17 (Ns132p785 rfl rfl) (Ns132p789 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns132p791 := nat_lit 4140476156443913320753676881 

noncomputable def Ns132p792 := BSN.cos_dyadic_bound_f 8021629 67108864 2 1 67108864 33554432 Ns132p791 Ns132p135 Ns132p791 Ns132p791 Ns132p136 Ns132p791 66630015 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 8021629) qz360 0 1 Ns132p791 Ns132p135 Ns132p791 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 8021629) (BSN.cosOddQ 67108864) 0 1 Ns132p791 Ns132p136 Ns132p791 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p793 := nat_lit 937155774789975779887184036183500250131960586194642854395615641600 

noncomputable def Ns132p794 := nat_lit 233348276332386182660202770511699241461812015286610413702086656 

noncomputable def Ns132p795 := nat_lit 2454077798669207941123079766471195999192768125342172011318713778176 

noncomputable def Ns132p796 := BSN.sin_dyadic_bound_f 62517352 67108864 3 2 67108864 33554432 Ns132p793 Ns132p108 Ns132p794 Ns132p795 Ns132p111 Ns132p794 53859171 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 62517352) qz359 0 2 Ns132p793 Ns132p108 Ns132p794 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 62517352) (BSN.sinOddQ 67108864) 0 2 Ns132p795 Ns132p111 Ns132p794 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p797 := Ns132p740 51269 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 58 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66630015 67108864) BSN.abs_quadSignPos qz655 (BSN.sfrac_eq_quadSignPos_mul Bool.false 53859171 67108864) qz106 rfl rfl (Ns132p790 rfl rfl) (Ns132p774 rfl) RS133to150.d27 RS133to150.d29 RS133to150.d31 RS133to150.d33 RS133to150.d17 (Ns132p792 rfl rfl) (Ns132p796 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns132p798 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz103) qz103 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz103) qz103 7) 124700424 67108864 51269 67108864 124700424 67108864 51269 67108864 16737007589916672 15587553 4194304 51269 33554432 (Ns132p797 rfl) 

noncomputable def Ns132p799 := @Enclosure.Real.IsNear.mulLit_tf qz684 (Zeta.RiemannSiegel.correction qz105) 1501773 4194304 1 4194304 38259490185 68719476736 2918471473477805 15045945812905361408 57457069353598005 288230376151711744 

noncomputable abbrev qz685 := (@HPow.hPow Real Real Real qz7 qz104 qz9)

noncomputable def Ns132p800 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz685 1 1 0 1 1501773 4194304 1 4194304 1501773 4194304 1 4194304 

noncomputable def Ns132p801 := @Enclosure.Real.IsNear.sqrt_image qz104 255200927261 4194304000 191149 4194304000 32716807 32716832 4194304 (@Enclosure.Real.IsNear.of_eq qz104 (@HMul.hMul Real Real Real qz5 qz103 qz3) Bool.false 255200927261 4194304000 191149 4194304000 (BSN.t_div_two_pi_mk qz103 382298 1000 qz106) (@Enclosure.Real.IsNear.mulLit_ff qz103 qz3 382298 1000 0 1 1335089 8388608 1 8388608 255200927261 4194304000 191149 4194304000 (Enclosure.Real.IsNear.const Bool.false 382298 1000) RS133to150.d36 rfl)) 

noncomputable abbrev qz872 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 382298 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz686 := qz872

noncomputable abbrev qz454 := qz686

noncomputable abbrev qz109 := qz454

noncomputable def Ns132p802 := @Enclosure.Real.IsNear.sqrt_image qz109 65433639 8388608 25 8388608 11714274 11714280 4194304 (@Enclosure.Real.IsNear.recentre' qz109 Bool.false 65433639 8388608 25 8388608 65433639 8388608 25 8388608 (Ns132p801 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns132p803 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz109) 11714277 4194304 3 4194304 1501772 1501774 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz109) Bool.false 23428554 8388608 6 8388608 11714277 4194304 3 4194304 (Ns132p802 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns132p804 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz109)) Bool.false 3003546 8388608 2 8388608 1501773 4194304 1 4194304 (Ns132p803 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz110 := (@HMul.hMul Real Real Real qz339 qz337 qz446)

noncomputable abbrev qz687 := (@HMul.hMul Real Real Real qz843 qz871 qz871)

noncomputable abbrev qz455 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz687 qz683) qz640)

noncomputable abbrev qz111 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz455))

noncomputable def Ns132p805 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz105) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz110)) qz111) Bool.false 38259490185 

noncomputable def Ns132p806 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz110)) qz111 13495411 4194304 211 

noncomputable def Ns132p807 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz110)) Bool.false 26990822 8388608 1688 8388608 13495411 4194304 211 

noncomputable def Ns132p808 := @Enclosure.Real.IsNear.recentre' (Real.cos qz110) Bool.false 2607136 8388608 139325858 7174466043904 81473 262144 69662929 3587233021952 

noncomputable def Ns132p809 := @Enclosure.Real.IsNear.cos_image qz110 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 42181429) qz365) Bool.false 42181429 8388608 79 4194304 Bool.false 2607136 8388608 1 

noncomputable def Ns132p810 := nat_lit 674651885283768657240268911 

noncomputable def Ns132p811 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz105 884279719003555 140737488355328 1 500000000000000 6713383 8388608 25 8388608 5936508432803243076565 1180591620717411303424 Ns132p810 

noncomputable def Ns132p812 := @Enclosure.Real.IsNear.subLit_ff_p qz109 qz1 65433639 8388608 25 8388608 7 1 0 1 6713383 6713383 8388608 25 

noncomputable def Ns132p813 := @Ns132p812 8388608 (@Enclosure.Real.IsNear.recentre' qz109 Bool.false 65433639 8388608 25 8388608 65433639 8388608 25 8388608 (Ns132p801 rfl rfl rfl rfl rfl rfl) rfl) qz366 

noncomputable def Ns132p814 := @Enclosure.Real.IsNear.recentre' qz110 Bool.false 5936508432803243076565 1180591620717411303424 Ns132p810 Ns132p405 42181429 8388608 79 4194304 (@Ns132p811 Ns132p405 RS133to150.d35 (Ns132p813 rfl rfl) rfl) 

noncomputable def Ns132p815 := nat_lit 868936966152020945453295934615479030016 

noncomputable def Ns132p816 := BSN.sin_dyadic_bound_f 5429340364 17179869184 2 1 8388608 3424393 Ns132p815 Ns132p617 Ns132p815 Ns132p815 Ns132p618 Ns132p815 2607136 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 5429340364) qz355 0 1 Ns132p815 Ns132p617 Ns132p815 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 5429340364) qz356 0 1 Ns132p815 Ns132p618 Ns132p815 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p817 := @Ns132p809 1710526 (Ns132p814 rfl) (Enclosure.sfrac_false_div 42181429 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 42181429) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 382055863188853429895168) qz367) 226375608064910080 72057594037927936 Bool.false 2607136 8388608 0 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 42181429 8388608 226375608064910080 72057594037927936 0 382055863188853429895168 Ns132p87 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 2607136 8388608 382055863188853429895168 Ns132p87 5429340364 17179869184 3424393 3421052 (Ns132p816 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p818 := @Enclosure.Real.IsNear.inv_image (Real.cos qz110) 81473 262144 69662929 3587233021952 13494567 13496255 4194304 (Ns132p808 (Ns132p817 rfl rfl) rfl) rfl 

noncomputable def Ns132p819 := @Enclosure.Real.IsNear.recentre' qz111 Bool.false 725760 4194304 

noncomputable abbrev qz112 := (@HMul.hMul Real Real Real qz339 qz337 qz455)

noncomputable def Ns132p820 := @Enclosure.Real.IsNear.cos_image qz112 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 5858965)) qz357) Bool.true 5858965 4194304 

noncomputable def Ns132p821 := nat_lit 13834090672346423438061576845 

noncomputable def Ns132p822 := nat_lit 14717800062443986508963591517645993 

noncomputable def Ns132p823 := @Enclosure.Real.IsNear.recentre' qz112 Bool.true Ns132p821 Ns132p285 Ns132p822 

noncomputable abbrev qz113 := qz455

noncomputable def Ns132p824 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz113 884279719003555 140737488355328 1 500000000000000 15644473547279 

noncomputable abbrev qz456 := (@HSub.hSub Real Real Real qz635 qz687 qz683)

noncomputable abbrev qz114 := qz456

noncomputable def Ns132p825 := @Enclosure.Real.IsNear.subLit_tf qz114 qz27 11246427036175 70368744177664 545384975 70368744177664 1 16 

noncomputable abbrev qz457 := qz687

noncomputable abbrev qz115 := qz457

noncomputable def Ns132p826 := @Enclosure.Real.IsNear.subLit_ff_n qz115 qz105 45069511304689 70368744177664 335669775 70368744177664 6713383 8388608 25 8388608 

noncomputable def Ns132p827 := @Enclosure.Real.IsNear.mulLit_ff qz105 qz105 6713383 8388608 25 8388608 6713383 8388608 25 8388608 45069511304689 70368744177664 

noncomputable def Ns132p828 := nat_lit 614066890956935273148295301859987212438838983270999190625 

noncomputable def Ns132p829 := nat_lit 3861888762982039923063034508418779142719222587902677483520 

noncomputable def Ns132p830 := nat_lit 1388568244930647676611249569763987835545164666250390625 

noncomputable def Ns132p831 := nat_lit 1839423536380944524091663406440433661645426620480496790625 

noncomputable def Ns132p832 := nat_lit 173784994334191796537836552878845061422365016455620486758400 

noncomputable def Ns132p833 := BSN.cos_dyadic_bound_f 5858965 4194304 3 2 4194304 1710526 Ns132p828 Ns132p829 Ns132p830 Ns132p831 Ns132p832 Ns132p830 725760 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 5858965) (BSN.cosEvenQ 4194304) 0 2 Ns132p828 Ns132p829 Ns132p830 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 5858965) (BSN.cosOddQ 4194304) 0 2 Ns132p831 Ns132p832 Ns132p830 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p834 := @Ns132p819 354852134 7174466043904 2835 16384 177426067 3587233021952 (@Ns132p820 205 4194304 Bool.false 725760 4194304 1 1710526 (@Ns132p823 Ns132p288 5858965 4194304 205 4194304 (@Ns132p824 70368744177664 545384975 70368744177664 Ns132p821 Ns132p285 Ns132p822 Ns132p288 RS133to150.d35 (@Ns132p825 0 1 250311576756464 15644473547279 70368744177664 545384975 70368744177664 (@Ns132p826 94341867807073894400 11246427036175 70368744177664 545384975 70368744177664 (@Ns132p827 335669775 70368744177664 (Ns132p813 rfl rfl) (Ns132p813 rfl rfl) rfl) (Ns132p813 rfl rfl) rfl rfl) qz372 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 5858965 4194304) (BSN.cos_neg_of_bound 5858965 4194304 Bool.false 725760 4194304 1 1710526 (Ns132p833 rfl rfl)) rfl rfl) 

noncomputable def Ns132p835 := @Ns132p799 2195630695878652550875 Ns132p333 (Ns132p800 qz29 (@Enclosure.Real.IsNear.of_eq qz685 (@Inv.inv Real Real.instInv (Real.sqrt qz109)) Bool.false 1501773 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz104 (BSN.t_div_two_pi_nonneg qz103 382298 1000 qz106)) Ns132p804) rfl) (@Ns132p805 68719476736 2918471473477805 15045945812905361408 (BSN.correction_mk qz105 (BSN.cos_two_pi_p_ne_zero_mk qz103 382298 1000 7 qz106 rfl rfl (@BSN.floor_sqrt_eq_dec qz103 382298 1000 7 qz106 rfl rfl rfl))) (@Ns132p806 1048576 2835 16384 177426067 3587233021952 38259490185 68719476736 2918471473477805 15045945812905361408 (@Ns132p807 1048576 (Ns132p818 rfl rfl rfl rfl rfl) rfl) (Ns132p834 rfl) rfl)) 

noncomputable def Ns132p836 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz103) (hardyZApproximantRS₀ qz103) Bool.true 1013711416401069003 288230376151711744 50407542938493963427547 Ns132p333 (@Eq.refl Real (hardyZApproximantRS₀ qz103)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz103) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz103) qz103 7) (@HMul.hMul Real Real Real qz5 qz684 (Zeta.RiemannSiegel.correction qz105))) Bool.true 1013711416401069003 288230376151711744 50407542938493963427547 Ns132p333 (BSN.hardyZApproximantRS₀_eq qz103 7 (@BSN.floor_sqrt_eq_dec qz103 382298 1000 7 qz106 rfl rfl rfl)) (@Ns132p738 1013711416401069003 288230376151711744 50407542938493963427547 Ns132p333 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz103) qz103 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz103) qz103 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz103) qz103 7)) Bool.true 15587553 4194304 51269 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz103) qz103 7) (Ns132p798 (Ns132p797 rfl) rfl rfl)) (Ns132p835 rfl) rfl rfl)) 

theorem RS133to150.d45 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz103) Bool.true 1013711416401069003 288230376151711744 50407542938493963427547 Ns132p333 := Ns132p836 

noncomputable def Ns132p837 := nat_lit 199243386284920627986956288 

noncomputable abbrev qz873 := (Enclosure.sfrac Bool.false 383827 1000)

noncomputable abbrev qz688 := qz873

noncomputable abbrev qz458 := qz688

noncomputable abbrev qz116 := qz458

noncomputable abbrev qz874 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 383827 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz689 := qz874

noncomputable abbrev qz459 := qz689

noncomputable abbrev qz117 := qz459

noncomputable abbrev qz875 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 383827 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz690 := qz875

noncomputable abbrev qz460 := qz690

noncomputable abbrev qz118 := qz460

noncomputable abbrev qz691 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz117 qz9))

noncomputable def Ns132p838 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 7) (@HMul.hMul Real Real Real qz5 qz691 (Zeta.RiemannSiegel.correction qz118)) 36278047 33554432 51469 33554432 951898817991286025 4611686018427387904 26934528970236760237 493025552397282882617344 Ns132p837 

noncomputable def Ns132p839 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 383827 1000 57 95 67108864 33554432 1125899906842624 Bool.false 40057455020 1249 

noncomputable def Ns132p840 := Ns132p839 120242927 40 27397080 8 130587807 40 25364760 8 Bool.false 45026160 38396 Bool.true 86408568 Bool.true 51307256 3537118876014220 1 Bool.false 64435505 Bool.true Bool.false 46452985 Bool.false Bool.false 36278047 

noncomputable def Ns132p841 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 383827 1000 41 13 67108864 33554432 1125899906842624 Bool.false 40057455020 1249 

noncomputable def Ns132p842 := Ns132p841 93032624 40 33554424 8 108007536 40 30011992 8 Bool.false 70491878 22650 Bool.false 27033408 Bool.true 28366858 3537118876014220 1 Bool.false 26308192 Bool.true Bool.false 27529633 Bool.true Bool.false 45026160 

noncomputable def Ns132p843 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 383827 1000 210 111 67108864 33554432 1125899906842624 Bool.false 40057455020 1249 

noncomputable def Ns132p844 := Ns132p843 46516304 40 47453136 16 73726608 40 38745320 8 Bool.false 67108856 1296 Bool.false 66226620 Bool.false 58198616 3537118876014220 1 Bool.false 36998301 Bool.true Bool.false 51173050 Bool.false Bool.false 70491878 

noncomputable def Ns132p845 := nat_lit 309443298712664490068852048610558519088638859566019729483 

noncomputable def Ns132p846 := nat_lit 518415067512332924756838350474603190679058654429184000 

noncomputable def Ns132p847 := nat_lit 3998717397663779358083549395360000 

noncomputable def Ns132p848 := nat_lit 9208901508236751794044720584413056320 

noncomputable abbrev qz461 := (@Eq.refl Real qz688)

noncomputable abbrev qz119 := qz461

noncomputable def Ns132p849 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz116 383827 1000 589293663716 16000000 767654 4000 2000 Ns132p847 Ns132p848 qz119 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns132p850 := nat_lit 99021855588052636822032655555378726108364435061126313434560 

noncomputable abbrev qz462 := (Real.log (Enclosure.sfrac Bool.false 589293663716 16000000))

noncomputable abbrev qz463 := (Enclosure.sfrac Bool.false 383827 2000)

noncomputable abbrev qz120 := (@HSub.hSub Real Real Real qz342 (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 383827 4000) qz462) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 767654)))))) qz463)

noncomputable abbrev qz464 := (@HSub.hSub Real Real Real qz12 qz120 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 383827 2000) (Real.log Real.pi)))

noncomputable def Ns132p851 := @Enclosure.Real.IsNear.addLit_ft_p qz464 (Enclosure.sfrac Bool.true Ns132p847 Ns132p848) 10752849026995545193083 18014398509481984000 3257466229168053628693 Ns132p199 Ns132p847 Ns132p848 0 1 Ns132p850 

noncomputable def Ns132p852 := nat_lit 144322296593035274193692157542400 

noncomputable abbrev qz465 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 383827 2000) (Real.log Real.pi))

noncomputable def Ns132p853 := @Enclosure.Real.IsNear.subLit_ff_p qz120 qz465 2942083270453581633663 3602879701896396800 4897838484904620803 684210400000000000000000 14743087162347 67108864000 383827 33554432000 Ns132p852 10752849026995545193083 18014398509481984000 

noncomputable def Ns132p854 := nat_lit 29420832704535816336630000 

noncomputable abbrev qz121 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 383827 4000) qz462) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 767654))))))

noncomputable def Ns132p855 := @Enclosure.Real.IsNear.subLit_ff_p qz121 qz463 18167622620617378904699 18014398509481984000 4897838484904620803 684210400000000000000000 383827 2000 0 1 Ns132p854 2942083270453581633663 3602879701896396800 4897838484904620803 684210400000000000000000 

noncomputable def Ns132p856 := nat_lit 40909849232210110827684170680974180352 

noncomputable def Ns132p857 := nat_lit 12710756315307715090972672 

noncomputable def Ns132p858 := nat_lit 23066385391313206034888838749141953923292829495040 

noncomputable def Ns132p859 := nat_lit 26254490504537418768294441608815782120463730688 

noncomputable def Ns132p860 := nat_lit 53570542215727195124666307989466311813899008 

noncomputable def Ns132p861 := BSN.log_dyadic_bound 65005663716 1113581663716 3 2 Ns132p858 33554432 13684208 Ns132p859 Ns132p860 3921959 1178587327432 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 65005663716) (BSN.artanhQ 1113581663716) 0 2 Ns132p859 Ns132p858 Ns132p860 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns132p862 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 383827 4000) qz462 383827 4000 0 1 47351257187529337 4503599627370496 12500002565789 171052600000000000000 18174690992517822832699 18014398509481984000 4797838484819094503 684210400000000000000000 (Enclosure.Real.IsNear.const Bool.false 383827 4000) (BSN.isNear_log_sfrac 589293663716 16000000 47351257187529337 4503599627370496 12500002565789 171052600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 589293663716) qz350)) Bool.false Ns132p857 Ns132p87 1000000205263120 13684208000000000000000 47351257187529337 4503599627370496 12500002565789 171052600000000000000 (BSN.log_rat_reduce_isNear 589293663716 16000000 15 1178587327432 1048576000000 3921959 33554432 24973259072661432 36028797018963968 13684208 1000000000000000 rfl rfl rfl rfl (Ns132p861 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns132p863 := BSN.arctan_dyadic_bound_f 1000 767654 1 0 4194304 1710526 0 1 1 0 1 1 5463 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 767654) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 767654) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz466 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 767654)))

noncomputable def Ns132p864 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz466 884279719003555 562949953421312 1 2000000000000000 5463 4194304 1 1710526 3705862566939946123264 883546487555491 562949953421312 1000000000855263 1710526000000000000000 qz17 (Ns132p863 rfl) rfl rfl 

noncomputable def Ns132p865 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 383827 4000) qz462) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz466)) 18174690992517822832699 18014398509481984000 4797838484819094503 684210400000000000000000 883546487555491 2251799813685248 1000000000855263 6842104000000000000000 Ns132p856 18167622620617378904699 18014398509481984000 4897838484904620803 684210400000000000000000 (Ns132p862 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz466) 1 4 0 1 883546487555491 562949953421312 1000000000855263 1710526000000000000000 883546487555491 2251799813685248 1000000000855263 6842104000000000000000 qz353 Ns132p864 rfl) 

noncomputable def Ns132p866 := @Ns132p851 Ns132p845 Ns132p846 3257466229168053628693 Ns132p199 (@Ns132p853 3257466229168053628693 Ns132p199 (Ns132p855 (Ns132p865 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 383827 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz463 (Real.log Real.pi) 383827 2000 0 1 38410761 33554432 1 16777216 14743087162347 67108864000 383827 33554432000 (Enclosure.Real.IsNear.const Bool.false 383827 2000) RS133to150.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns132p847 Ns132p848) 

noncomputable def Ns132p867 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns132p845 Ns132p846 3257466229168053628693 Ns132p199 5007181877 8388608 157 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz354 qz464 (Enclosure.sfrac Bool.true Ns132p847 Ns132p848)) Bool.false Ns132p845 Ns132p846 3257466229168053628693 Ns132p199 Ns132p849 (Ns132p866 rfl rfl)) 

noncomputable def Ns132p868 := nat_lit 1898964179785890538717184 

noncomputable def Ns132p869 := nat_lit 139985330837751376794753222443623946824447975596128675458726525405345230629172364247040 

noncomputable def Ns132p870 := nat_lit 281252102213993197268631242937708713874962068634353968762601912641844801604251877376 

noncomputable def Ns132p871 := nat_lit 366172886885764283571633036768544522812994759402548053109144306298293569588092165226496 

noncomputable def Ns132p872 := BSN.sin_dyadic_bound_f 26985904068 17179869184 3 2 8388608 3424393 Ns132p869 Ns132p99 Ns132p870 Ns132p871 Ns132p102 Ns132p870 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26985904068) qz355 0 2 Ns132p869 Ns132p99 Ns132p870 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26985904068) qz356 0 2 Ns132p871 Ns132p102 Ns132p870 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p873 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz116) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5007181877) qz365) Bool.false 5007181877 8388608 157 8388608 Bool.false 8388607 8388608 1 1710526 (Ns132p867 rfl) (Enclosure.sfrac_false_div 5007181877 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5007181877) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns132p868) qz367) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 94 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 5007181877 8388608 226375608064910080 72057594037927936 94 Ns132p868 Ns132p87 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns132p868 Ns132p87 26985904068 17179869184 3424393 3421052 (Ns132p872 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p874 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns132p845 Ns132p846 3257466229168053628693 Ns132p199 40057455020 67108864 1249 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz354 qz464 (Enclosure.sfrac Bool.true Ns132p847 Ns132p848)) Bool.false Ns132p845 Ns132p846 3257466229168053628693 Ns132p199 Ns132p849 (Ns132p866 rfl rfl)) 

noncomputable def Ns132p875 := Ns132p844 22650 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 210 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 36998301 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 111 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 51173050 67108864) qz119 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) Bool.false 8388607 8388608 138470595 7174466043904 67108856 67108864 1296 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 8388607 8388608 138470595 7174466043904 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz116) qz116) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 8388607 8388608 276941190 14348932087808 8388607 8388608 138470595 7174466043904 (Ns132p873 rfl rfl) rfl)) rfl) (Ns132p874 rfl) RS133to150.d7 

noncomputable def Ns132p876 := nat_lit 655849670003325834111248337369658441246086910252961610576076800000 

noncomputable def Ns132p877 := nat_lit 370050269318326467310308619618209699640182936626991129600000000 

noncomputable def Ns132p878 := nat_lit 1966808909471340849399124394869738904338980364885630849469030400000 

noncomputable def Ns132p879 := BSN.cos_dyadic_bound_f 66226620 67108864 3 2 67108864 33554432 Ns132p876 Ns132p124 Ns132p877 Ns132p878 Ns132p127 Ns132p877 36998301 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 66226620) qz360 0 2 Ns132p876 Ns132p124 Ns132p877 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 66226620) (BSN.cosOddQ 67108864) 0 2 Ns132p878 Ns132p127 Ns132p877 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p880 := nat_lit 703773953058276863092949027489301659779309087433931123752194539520 

noncomputable def Ns132p881 := nat_lit 131613747689239590121578928261090420222560531471118963201540096 

noncomputable def Ns132p882 := nat_lit 1843004407180180634478479182302414962551163464323628274362945110016 

noncomputable def Ns132p883 := BSN.sin_dyadic_bound_f 58198616 67108864 3 2 67108864 33554432 Ns132p880 Ns132p108 Ns132p881 Ns132p882 Ns132p111 Ns132p881 51173050 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 58198616) qz359 0 2 Ns132p880 Ns132p108 Ns132p881 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 58198616) (BSN.sinOddQ 67108864) 0 2 Ns132p882 Ns132p111 Ns132p881 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p884 := nat_lit 534076164481371459010267447296 

noncomputable def Ns132p885 := BSN.sin_dyadic_bound_f 27033408 67108864 2 1 67108864 33554432 Ns132p884 Ns132p114 Ns132p884 Ns132p884 Ns132p115 Ns132p884 26308192 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 27033408) qz359 0 1 Ns132p884 Ns132p114 Ns132p884 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 27033408) (BSN.sinOddQ 67108864) 0 1 Ns132p884 Ns132p115 Ns132p884 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p886 := nat_lit 647507702072266312306819802896 

noncomputable def Ns132p887 := BSN.sin_dyadic_bound_f 28366858 67108864 2 1 67108864 33554432 Ns132p886 Ns132p114 Ns132p886 Ns132p886 Ns132p115 Ns132p886 27529633 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 28366858) qz359 0 1 Ns132p886 Ns132p114 Ns132p886 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 28366858) (BSN.sinOddQ 67108864) 0 1 Ns132p886 Ns132p115 Ns132p886 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p888 := Ns132p842 38396 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 41 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 26308192 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 13 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 27529633 67108864) qz119 rfl rfl (Ns132p875 RS133to150.d9 RS133to150.d11 RS133to150.d13 RS133to150.d17 (Ns132p879 rfl rfl) (Ns132p883 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns132p874 rfl) RS133to150.d19 RS133to150.d21 RS133to150.d23 RS133to150.d25 RS133to150.d17 (Ns132p885 rfl rfl) (Ns132p887 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns132p889 := nat_lit 3422339794877631105961453887120850905762025246426360519788865781760 

noncomputable def Ns132p890 := nat_lit 3107810023288745853328109731819723577636739512367212533043429376 

noncomputable def Ns132p891 := nat_lit 8958239198927518736612705145750710915012939971906159207726863876096 

noncomputable def Ns132p892 := BSN.sin_dyadic_bound_f 86408568 67108864 3 2 67108864 33554432 Ns132p889 Ns132p108 Ns132p890 Ns132p891 Ns132p111 Ns132p890 64435505 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 86408568) qz359 0 2 Ns132p889 Ns132p108 Ns132p890 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 86408568) (BSN.sinOddQ 67108864) 0 2 Ns132p891 Ns132p111 Ns132p890 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p893 := nat_lit 425074991628446712440778906081429212222100488935835397120096993280 

noncomputable def Ns132p894 := nat_lit 48020901374437663337014326231875736228717301153635668240367616 

noncomputable def Ns132p895 := nat_lit 1113213896615135157318541968923177280818273833487224915661198196736 

noncomputable def Ns132p896 := BSN.sin_dyadic_bound_f 51307256 67108864 3 2 67108864 33554432 Ns132p893 Ns132p108 Ns132p894 Ns132p895 Ns132p111 Ns132p894 46452985 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 51307256) qz359 0 2 Ns132p893 Ns132p108 Ns132p894 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 51307256) (BSN.sinOddQ 67108864) 0 2 Ns132p895 Ns132p111 Ns132p894 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p897 := Ns132p840 51469 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 57 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 64435505 67108864) BSN.abs_quadSignPos qz655 (BSN.sfrac_eq_quadSignPos_mul Bool.false 46452985 67108864) qz119 rfl rfl (Ns132p888 rfl rfl) (Ns132p874 rfl) RS133to150.d27 RS133to150.d29 RS133to150.d31 RS133to150.d33 RS133to150.d17 (Ns132p892 rfl rfl) (Ns132p896 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns132p898 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 7) 36278047 67108864 51469 67108864 36278047 67108864 51469 67108864 4869157044617216 36278047 33554432 51469 33554432 (Ns132p897 rfl) 

noncomputable def Ns132p899 := @Enclosure.Real.IsNear.mulLit_tf qz691 (Zeta.RiemannSiegel.correction qz118) 1500275 4194304 1 4194304 634482890131 1099511627776 573050777381847 3761486453226340352 951898817991286025 4611686018427387904 

noncomputable abbrev qz692 := (@HPow.hPow Real Real Real qz7 qz117 qz9)

noncomputable def Ns132p900 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz692 1 1 0 1 1500275 4194304 1 4194304 1500275 4194304 1 4194304 

noncomputable def Ns132p901 := @Enclosure.Real.IsNear.sqrt_image qz117 512443205603 8388608000 383827 8388608000 32782167 32782192 4194304 (@Enclosure.Real.IsNear.of_eq qz117 (@HMul.hMul Real Real Real qz5 qz116 qz3) Bool.false 512443205603 8388608000 383827 8388608000 (BSN.t_div_two_pi_mk qz116 383827 1000 qz119) (@Enclosure.Real.IsNear.mulLit_ff qz116 qz3 383827 1000 0 1 1335089 8388608 1 8388608 512443205603 8388608000 383827 8388608000 (Enclosure.Real.IsNear.const Bool.false 383827 1000) RS133to150.d36 rfl)) 

noncomputable abbrev qz876 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 383827 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz693 := qz876

noncomputable abbrev qz467 := qz693

noncomputable abbrev qz122 := qz467

noncomputable def Ns132p902 := @Enclosure.Real.IsNear.sqrt_image qz122 65564359 8388608 25 8388608 11725970 11725975 4194304 (@Enclosure.Real.IsNear.recentre' qz122 Bool.false 65564359 8388608 25 8388608 65564359 8388608 25 8388608 (Ns132p901 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns132p903 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz122) 23451945 8388608 5 8388608 1500274 1500276 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz122) Bool.false 23451945 8388608 5 8388608 23451945 8388608 5 8388608 (Ns132p902 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns132p904 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz122)) Bool.false 3000550 8388608 2 8388608 1500275 4194304 1 4194304 (Ns132p903 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz123 := (@HMul.hMul Real Real Real qz339 qz337 qz460)

noncomputable abbrev qz694 := (@HMul.hMul Real Real Real qz843 qz875 qz875)

noncomputable abbrev qz468 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz694 qz690) qz640)

noncomputable abbrev qz124 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz468))

noncomputable def Ns132p905 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz118) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz123)) qz124) Bool.false 634482890131 

noncomputable def Ns132p906 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz123)) qz124 651743 262144 63 

noncomputable def Ns132p907 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz123)) Bool.false 20855776 8388608 1008 8388608 651743 262144 63 

noncomputable def Ns132p908 := @Enclosure.Real.IsNear.recentre' (Real.cos qz123) Bool.false 3374065 8388608 139325858 7174466043904 3374065 8388608 69662929 3587233021952 

noncomputable def Ns132p909 := @Enclosure.Real.IsNear.cos_image qz123 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 43002767) qz365) Bool.false 43002767 8388608 79 4194304 Bool.false 3374065 8388608 1 

noncomputable def Ns132p910 := nat_lit 674651885284891533490135151 

noncomputable def Ns132p911 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz118 884279719003555 140737488355328 1 500000000000000 6844103 8388608 25 8388608 6052101477671387786165 1180591620717411303424 Ns132p910 

noncomputable def Ns132p912 := @Enclosure.Real.IsNear.subLit_ff_p qz122 qz1 65564359 8388608 25 8388608 7 1 0 1 6844103 6844103 8388608 25 

noncomputable def Ns132p913 := @Ns132p912 8388608 (@Enclosure.Real.IsNear.recentre' qz122 Bool.false 65564359 8388608 25 8388608 65564359 8388608 25 8388608 (Ns132p901 rfl rfl rfl rfl rfl rfl) rfl) qz366 

noncomputable def Ns132p914 := @Enclosure.Real.IsNear.recentre' qz123 Bool.false 6052101477671387786165 1180591620717411303424 Ns132p910 Ns132p405 43002767 8388608 79 4194304 (@Ns132p911 Ns132p405 RS133to150.d35 (Ns132p913 rfl rfl) rfl) 

noncomputable def Ns132p915 := nat_lit 2557586579808957392840613762967057633536 

noncomputable def Ns132p916 := BSN.sin_dyadic_bound_f 7111440588 17179869184 2 1 8388608 3424393 Ns132p915 Ns132p617 Ns132p915 Ns132p915 Ns132p618 Ns132p915 3374065 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 7111440588) qz355 0 1 Ns132p915 Ns132p617 Ns132p915 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 7111440588) qz356 0 1 Ns132p915 Ns132p618 Ns132p915 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p917 := @Ns132p909 1710526 (Ns132p914 rfl) (Enclosure.sfrac_false_div 43002767 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 43002767) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 500423143532700740091904) qz367) 226375608064910080 72057594037927936 Bool.false 3374065 8388608 0 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 43002767 8388608 226375608064910080 72057594037927936 0 500423143532700740091904 Ns132p87 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 3374065 8388608 500423143532700740091904 Ns132p87 7111440588 17179869184 3424393 3421052 (Ns132p916 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p918 := @Enclosure.Real.IsNear.inv_image (Real.cos qz123) 3374065 8388608 69662929 3587233021952 10427384 10428392 4194304 (Ns132p908 (Ns132p917 rfl rfl) rfl) rfl 

noncomputable def Ns132p919 := @Enclosure.Real.IsNear.recentre' qz124 Bool.false 973517 4194304 

noncomputable abbrev qz125 := (@HMul.hMul Real Real Real qz339 qz337 qz468)

noncomputable def Ns132p920 := @Enclosure.Real.IsNear.cos_image qz125 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 11211839)) qz365) Bool.true 11211839 8388608 

noncomputable def Ns132p921 := nat_lit 13236604325774457347793748045 

noncomputable def Ns132p922 := nat_lit 14894181051311694379713919775079273 

noncomputable def Ns132p923 := @Enclosure.Real.IsNear.recentre' qz125 Bool.true Ns132p921 Ns132p285 Ns132p922 

noncomputable abbrev qz126 := qz468

noncomputable def Ns132p924 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz126 884279719003555 140737488355328 1 500000000000000 14968797815119 

noncomputable abbrev qz469 := (@HSub.hSub Real Real Real qz635 qz694 qz690)

noncomputable abbrev qz127 := qz469

noncomputable def Ns132p925 := @Enclosure.Real.IsNear.subLit_tf qz127 qz27 10570751304015 70368744177664 551920975 70368744177664 1 16 

noncomputable abbrev qz470 := qz694

noncomputable abbrev qz128 := qz470

noncomputable def Ns132p926 := @Enclosure.Real.IsNear.subLit_ff_n qz128 qz118 46841745874609 70368744177664 342205775 70368744177664 6844103 8388608 25 8388608 

noncomputable def Ns132p927 := @Enclosure.Real.IsNear.mulLit_ff qz118 qz118 6844103 8388608 25 8388608 6844103 8388608 25 8388608 46841745874609 70368744177664 

noncomputable def Ns132p928 := nat_lit 131704450951701729885289410224689099249625141359556736130561 

noncomputable def Ns132p929 := nat_lit 988643523323402220304136834155207460536120982503085435781120 

noncomputable def Ns132p930 := nat_lit 249697860936119551565616490588765703287667383968532078081 

noncomputable def Ns132p931 := nat_lit 394613957133232950552736997692889766342300089310733144235521 

noncomputable def Ns132p932 := nat_lit 44488958549553099913686157536984335724125444212638844610150400 

noncomputable def Ns132p933 := BSN.cos_dyadic_bound_f 11211839 8388608 3 2 4194304 1710526 Ns132p928 Ns132p929 Ns132p930 Ns132p931 Ns132p932 Ns132p930 973517 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 11211839) (BSN.cosEvenQ 8388608) 0 2 Ns132p928 Ns132p929 Ns132p930 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 11211839) (BSN.cosOddQ 8388608) 0 2 Ns132p931 Ns132p932 Ns132p930 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p934 := @Ns132p919 718256898 14348932087808 973517 4194304 359128449 7174466043904 (@Ns132p920 415 8388608 Bool.false 973517 4194304 1 1710526 (@Ns132p923 Ns132p288 11211839 8388608 415 8388608 (@Ns132p924 70368744177664 551920975 70368744177664 Ns132p921 Ns132p285 Ns132p922 Ns132p288 RS133to150.d35 (@Ns132p925 0 1 239500765041904 14968797815119 70368744177664 551920975 70368744177664 (@Ns132p926 88673888954870661120 10570751304015 70368744177664 551920975 70368744177664 (@Ns132p927 342205775 70368744177664 (Ns132p913 rfl rfl) (Ns132p913 rfl rfl) rfl) (Ns132p913 rfl rfl) rfl rfl) qz372 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 11211839 8388608) (BSN.cos_neg_of_bound 11211839 8388608 Bool.false 973517 4194304 1 1710526 (Ns132p933 rfl rfl)) rfl rfl) 

noncomputable def Ns132p935 := @Ns132p899 26934528970236760237 493025552397282882617344 (Ns132p900 qz29 (@Enclosure.Real.IsNear.of_eq qz692 (@Inv.inv Real Real.instInv (Real.sqrt qz122)) Bool.false 1500275 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz117 (BSN.t_div_two_pi_nonneg qz116 383827 1000 qz119)) Ns132p904) rfl) (@Ns132p905 1099511627776 573050777381847 3761486453226340352 (BSN.correction_mk qz118 (BSN.cos_two_pi_p_ne_zero_mk qz116 383827 1000 7 qz119 rfl rfl (@BSN.floor_sqrt_eq_dec qz116 383827 1000 7 qz119 rfl rfl rfl))) (@Ns132p906 524288 973517 4194304 359128449 7174466043904 634482890131 1099511627776 573050777381847 3761486453226340352 (@Ns132p907 524288 (Ns132p918 rfl rfl rfl rfl rfl) rfl) (Ns132p934 rfl) rfl)) 

noncomputable def Ns132p936 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (hardyZApproximantRS₀ qz116) Bool.false 5937915631679315209 4611686018427387904 783184319052684071085 493025552397282882617344 (@Eq.refl Real (hardyZApproximantRS₀ qz116)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 7) (@HMul.hMul Real Real Real qz5 qz691 (Zeta.RiemannSiegel.correction qz118))) Bool.false 5937915631679315209 4611686018427387904 783184319052684071085 493025552397282882617344 (BSN.hardyZApproximantRS₀_eq qz116 7 (@BSN.floor_sqrt_eq_dec qz116 383827 1000 7 qz119 rfl rfl rfl)) (@Ns132p838 5937915631679315209 4611686018427387904 783184319052684071085 493025552397282882617344 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 7)) Bool.false 36278047 33554432 51469 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz116) qz116 7) (Ns132p898 (Ns132p897 rfl) rfl rfl)) (Ns132p935 rfl) rfl rfl)) 

theorem RS133to150.d46 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz116) Bool.false 5937915631679315209 4611686018427387904 783184319052684071085 493025552397282882617344 := Ns132p936 

noncomputable def Ns132p937 := nat_lit 1249351325468773169909202944 

noncomputable abbrev qz877 := (Enclosure.sfrac Bool.false 385354 1000)

noncomputable abbrev qz695 := qz877

noncomputable abbrev qz471 := qz695

noncomputable abbrev qz129 := qz471

noncomputable abbrev qz878 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 385354 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz696 := qz878

noncomputable abbrev qz472 := qz696

noncomputable abbrev qz130 := qz472

noncomputable abbrev qz879 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 385354 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz697 := qz879

noncomputable abbrev qz473 := qz697

noncomputable abbrev qz131 := qz473

noncomputable abbrev qz698 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz130 qz9))

noncomputable def Ns132p938 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz129) qz129 7) (@HMul.hMul Real Real Real qz5 qz698 (Zeta.RiemannSiegel.correction qz131)) 12054909 16777216 25833 16777216 31568958984022756063 147573952589676412928 5747061963453729814507 Ns132p188 Ns132p937 

noncomputable def Ns132p939 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz129) qz129 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 385354 1000 57 95 67108864 33554432 1125899906842624 Bool.false 40268261867 1253 

noncomputable def Ns132p940 := Ns132p939 120242927 40 27397080 8 130587807 40 25364760 8 Bool.true 17163427 38542 Bool.true 59212671 Bool.true 39907990 3537118876014220 1 Bool.false 51823219 Bool.true Bool.false 37597063 Bool.false Bool.true 24109818 

noncomputable def Ns132p941 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz129) qz129 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 385354 1000 41 12 67108864 33554432 1125899906842624 Bool.false 40268261867 1253 

noncomputable def Ns132p942 := Ns132p941 93032624 40 33554424 8 108007536 40 30011992 8 Bool.false 8302534 22734 Bool.false 95779438 Bool.true 87901875 3537118876014220 1 Bool.false 66418401 Bool.true Bool.false 17314396 Bool.false Bool.true 17163427 

noncomputable def Ns132p943 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz129) qz129 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 385354 1000 211 112 67108864 33554432 1125899906842624 Bool.false 40268261867 1253 

noncomputable def Ns132p944 := Ns132p943 46516304 40 47453136 16 73726608 40 38745320 8 Bool.true 67108856 1296 Bool.false 100588714 Bool.false 51010576 3537118876014220 1 Bool.false 66935438 Bool.false Bool.false 48637520 Bool.false Bool.false 8302534 

noncomputable def Ns132p945 := nat_lit 497767708983219443814442654143453698992603387109942629 

noncomputable def Ns132p946 := nat_lit 829552206550995932587710353628890895876262094438400 

noncomputable def Ns132p947 := nat_lit 4078894254526971923354247531520000 

noncomputable def Ns132p948 := nat_lit 9430916708777157652863369931184148480 

noncomputable abbrev qz699 := (@Eq.refl Real qz877)

noncomputable abbrev qz474 := qz699

noncomputable abbrev qz132 := qz474

noncomputable def Ns132p949 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz129 385354 1000 593991821264 16000000 770708 4000 2000 Ns132p947 Ns132p948 qz132 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns132p950 := nat_lit 10194282679976334209319785556857931755368517368011625041920 

noncomputable abbrev qz475 := (Enclosure.sfrac Bool.false 385354 2000)

noncomputable abbrev qz700 := (Real.log (Enclosure.sfrac Bool.false 593991821264 16000000))

noncomputable abbrev qz133 := (@HSub.hSub Real Real Real qz342 (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 385354 4000) qz700) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 770708)))))) qz475)

noncomputable abbrev qz476 := (@HSub.hSub Real Real Real qz12 qz133 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 385354 2000) (Real.log Real.pi)))

noncomputable def Ns132p951 := @Enclosure.Real.IsNear.addLit_ft_p qz476 (Enclosure.sfrac Bool.true Ns132p947 Ns132p948) 1080943702786748060729 1801439850948198400 1635161869898147739443 Ns132p747 Ns132p947 Ns132p948 0 1 Ns132p950 

noncomputable def Ns132p952 := nat_lit 181352259854930741524315504640000 

noncomputable abbrev qz477 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 385354 2000) (Real.log Real.pi))

noncomputable def Ns132p953 := @Enclosure.Real.IsNear.subLit_ff_p qz133 qz477 7391374480115126920477 9007199254740992000 2458462994411290303 342105200000000000000000 7400870197197 33554432000 192677 16777216000 Ns132p952 1080943702786748060729 1801439850948198400 

noncomputable def Ns132p954 := nat_lit 14782748960230253840954000 

noncomputable abbrev qz134 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 385354 4000) qz700) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 770708))))))

noncomputable def Ns132p955 := @Enclosure.Real.IsNear.subLit_ff_p qz134 qz475 9126854610920857036061 9007199254740992000 2458462994411290303 342105200000000000000000 385354 2000 0 1 Ns132p954 7391374480115126920477 9007199254740992000 2458462994411290303 342105200000000000000000 

noncomputable def Ns132p956 := nat_lit 20551849512403932500026189498839728128 

noncomputable def Ns132p957 := nat_lit 12720356260331012078174208 

noncomputable def Ns132p958 := nat_lit 23458120482752678792926377050093474178977052426240 

noncomputable def Ns132p959 := nat_lit 30450565860298374585730171266218760245126627328 

noncomputable def Ns132p960 := nat_lit 70818643587990439873119970334922044882485248 

noncomputable def Ns132p961 := BSN.log_dyadic_bound 69703821264 1118279821264 3 2 Ns132p958 33554432 13684208 Ns132p959 Ns132p960 4188411 1187983642528 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 69703821264) (BSN.artanhQ 1118279821264) 0 2 Ns132p959 Ns132p958 Ns132p960 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns132p962 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 385354 4000) qz700 385354 4000 0 1 47387019769590393 4503599627370496 12500002565789 171052600000000000000 9130388808145368152061 9007199254740992000 2408462994368527153 342105200000000000000000 (Enclosure.Real.IsNear.const Bool.false 385354 4000) (BSN.isNear_log_sfrac 593991821264 16000000 47387019769590393 4503599627370496 12500002565789 171052600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 593991821264) qz350)) Bool.false Ns132p957 Ns132p87 1000000205263120 13684208000000000000000 47387019769590393 4503599627370496 12500002565789 171052600000000000000 (BSN.log_rat_reduce_isNear 593991821264 16000000 15 1187983642528 1048576000000 4188411 33554432 24973259072661432 36028797018963968 13684208 1000000000000000 rfl rfl rfl rfl (Ns132p961 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns132p963 := BSN.arctan_dyadic_bound_f 1000 770708 1 0 4194304 1710526 0 1 1 0 1 1 5442 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 770708) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 770708) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz478 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 770708)))

noncomputable def Ns132p964 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz478 884279719003555 562949953421312 1 2000000000000000 5442 4194304 1 1710526 3705874388888967970816 883549306127779 562949953421312 1000000000855263 1710526000000000000000 qz17 (Ns132p963 rfl) rfl rfl 

noncomputable def Ns132p965 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 385354 4000) qz700) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz478)) 9130388808145368152061 9007199254740992000 2408462994368527153 342105200000000000000000 883549306127779 2251799813685248 1000000000855263 6842104000000000000000 Ns132p956 9126854610920857036061 9007199254740992000 2458462994411290303 342105200000000000000000 (Ns132p962 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz478) 1 4 0 1 883549306127779 562949953421312 1000000000855263 1710526000000000000000 883549306127779 2251799813685248 1000000000855263 6842104000000000000000 qz353 Ns132p964 rfl) 

noncomputable def Ns132p966 := @Ns132p951 Ns132p945 Ns132p946 1635161869898147739443 Ns132p747 (@Ns132p953 1635161869898147739443 Ns132p747 (Ns132p955 (Ns132p965 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 385354 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz475 (Real.log Real.pi) 385354 2000 0 1 38410761 33554432 1 16777216 7400870197197 33554432000 192677 16777216000 (Enclosure.Real.IsNear.const Bool.false 385354 2000) RS133to150.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns132p947 Ns132p948) 

noncomputable def Ns132p967 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz129) Bool.false Ns132p945 Ns132p946 1635161869898147739443 Ns132p747 5033532733 8388608 157 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz129) (@HAdd.hAdd Real Real Real qz354 qz476 (Enclosure.sfrac Bool.true Ns132p947 Ns132p948)) Bool.false Ns132p945 Ns132p946 1635161869898147739443 Ns132p747 Ns132p949 (Ns132p966 rfl rfl)) 

noncomputable def Ns132p968 := nat_lit 1898570274549347265806336 

noncomputable def Ns132p969 := nat_lit 139868984336168220994393758728310830543499254563098556154009467595609919589833694675200 

noncomputable def Ns132p970 := nat_lit 280785716270174449075290477993577322948682881137195124544108739497035570791658455296 

noncomputable def Ns132p971 := nat_lit 365868924958860296353480802562157811948200180143416950201715286695983160382568419983616 

noncomputable def Ns132p972 := BSN.sin_dyadic_bound_f 26980306338 17179869184 3 2 8388608 3424393 Ns132p969 Ns132p99 Ns132p970 Ns132p971 Ns132p102 Ns132p970 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26980306338) qz355 0 2 Ns132p969 Ns132p99 Ns132p970 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26980306338) qz356 0 2 Ns132p971 Ns132p102 Ns132p970 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p973 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz129) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5033532733) qz365) Bool.false 5033532733 8388608 157 8388608 Bool.true 8388607 8388608 1 1710526 (Ns132p967 rfl) (Enclosure.sfrac_false_div 5033532733 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5033532733) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns132p968) qz367) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 95 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q1 5033532733 8388608 226375608064910080 72057594037927936 95 Ns132p968 Ns132p87 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns132p968 Ns132p87 26980306338 17179869184 3424393 3421052 (Ns132p972 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p974 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz129) Bool.false Ns132p945 Ns132p946 1635161869898147739443 Ns132p747 40268261867 67108864 1253 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz129) (@HAdd.hAdd Real Real Real qz354 qz476 (Enclosure.sfrac Bool.true Ns132p947 Ns132p948)) Bool.false Ns132p945 Ns132p946 1635161869898147739443 Ns132p747 Ns132p949 (Ns132p966 rfl rfl)) 

noncomputable def Ns132p975 := Ns132p944 22734 BSN.abs_quadSignPos (BSN.cos_quad_nat3 211 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66935438 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 112 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 48637520 67108864) qz132 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz129) qz129 1) Bool.true 8388607 8388608 138470595 7174466043904 67108856 67108864 1296 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz129) qz129 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz129)) Bool.true 8388607 8388608 138470595 7174466043904 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz129) qz129) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz129)) Bool.true 8388607 8388608 276941190 14348932087808 8388607 8388608 138470595 7174466043904 (Ns132p973 rfl rfl) rfl)) rfl) (Ns132p974 rfl) RS133to150.d7 

noncomputable def Ns132p976 := nat_lit 2189070273737624945672298390010048240390947442898576665371024055812075493765018889790433619585625296896 

noncomputable def Ns132p977 := nat_lit 1072978624353559205434329768947301379075595489295231448819495563345494782225363021913348205776896 

noncomputable def Ns132p978 := nat_lit 10934072062218078585632999374192647862352565816272554766556033330806565830518427698449258840574917677056 

noncomputable def Ns132p979 := BSN.sin_dyadic_bound_f 100588714 67108864 4 3 67108864 33554432 Ns132p976 Ns132p233 Ns132p977 Ns132p978 Ns132p236 Ns132p977 66935438 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 100588714) qz359 0 3 Ns132p976 Ns132p233 Ns132p977 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 100588714) (BSN.sinOddQ 67108864) 0 3 Ns132p978 Ns132p236 Ns132p977 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p980 := nat_lit 230757608493439230651221767000884072857881194790340232955461369856 

noncomputable def Ns132p981 := nat_lit 45843927824823864666001553375221531332056586448981217536638976 

noncomputable def Ns132p982 := nat_lit 692181137624668044224333297895901775510979471198122736431310831616 

noncomputable def Ns132p983 := BSN.cos_dyadic_bound_f 51010576 67108864 3 2 67108864 33554432 Ns132p980 Ns132p124 Ns132p981 Ns132p982 Ns132p127 Ns132p981 48637520 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 51010576) qz360 0 2 Ns132p980 Ns132p124 Ns132p981 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 51010576) (BSN.cosOddQ 67108864) 0 2 Ns132p982 Ns132p127 Ns132p981 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p984 := nat_lit 1798965935751839960367818417541658568319977756707117978048453232965911003994961991289656531598004064256 

noncomputable def Ns132p985 := nat_lit 596029030357509333282820794976472320633377504080435854842052595870237909553810607300257127469056 

noncomputable def Ns132p986 := nat_lit 8987208235586619734735561342812777957667978639668108441504429077523236844707722091345102272636326383616 

noncomputable def Ns132p987 := BSN.sin_dyadic_bound_f 95779438 67108864 4 3 67108864 33554432 Ns132p984 Ns132p233 Ns132p985 Ns132p986 Ns132p236 Ns132p985 66418401 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 95779438) qz359 0 3 Ns132p984 Ns132p233 Ns132p985 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 95779438) (BSN.sinOddQ 67108864) 0 3 Ns132p986 Ns132p236 Ns132p985 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p988 := nat_lit 491041089202671854703692584116906824591834248856370285069479132379833042749887001378025974273681640625 

noncomputable def Ns132p989 := nat_lit 212802961327812022823256523217019272836423341317440576297552471629614956327714025974273681640625 

noncomputable def Ns132p990 := nat_lit 2975507928273888756411532056267167018497499337806048017195625825476296735966869081275625974273681640625 

noncomputable def Ns132p991 := BSN.cos_dyadic_bound_f 87901875 67108864 4 3 67108864 33554432 Ns132p988 Ns132p118 Ns132p989 Ns132p990 Ns132p121 Ns132p989 17314396 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 87901875) qz360 0 3 Ns132p988 Ns132p118 Ns132p989 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 87901875) (BSN.cosOddQ 67108864) 0 3 Ns132p990 Ns132p121 Ns132p989 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p992 := Ns132p942 38542 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 41 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66418401 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 12 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 17314396 67108864) qz132 rfl rfl (Ns132p975 RS133to150.d9 RS133to150.d11 RS133to150.d13 RS133to150.d17 (Ns132p979 rfl rfl) (Ns132p983 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns132p974 rfl) RS133to150.d19 RS133to150.d21 RS133to150.d23 RS133to150.d25 RS133to150.d17 (Ns132p987 rfl rfl) (Ns132p991 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns132p993 := nat_lit 754131322612421207424289711043104257282187150792167177418295665665 

noncomputable def Ns132p994 := nat_lit 151118354323296922700429492068793070593231014506390860393538561 

noncomputable def Ns132p995 := nat_lit 1974861177125532110141148547840018818386672544717903688988232442881 

noncomputable def Ns132p996 := BSN.sin_dyadic_bound_f 59212671 67108864 3 2 67108864 33554432 Ns132p993 Ns132p108 Ns132p994 Ns132p995 Ns132p111 Ns132p994 51823219 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 59212671) qz359 0 2 Ns132p993 Ns132p108 Ns132p994 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 59212671) (BSN.sinOddQ 67108864) 0 2 Ns132p995 Ns132p111 Ns132p994 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p997 := nat_lit 155581772531413014666064838294115727284252339887829275152135840000 

noncomputable def Ns132p998 := nat_lit 6433967129124421707945820078796369962468846006599360100000000 

noncomputable def Ns132p999 := nat_lit 407465654016444075061690283252080282097864512050780274053527200000 

noncomputable def Ns132p1000 := BSN.sin_dyadic_bound_f 39907990 67108864 3 2 67108864 33554432 Ns132p997 Ns132p108 Ns132p998 Ns132p999 Ns132p111 Ns132p998 37597063 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 39907990) qz359 0 2 Ns132p997 Ns132p108 Ns132p998 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 39907990) (BSN.sinOddQ 67108864) 0 2 Ns132p999 Ns132p111 Ns132p998 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1001 := Ns132p940 51666 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 57 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 51823219 67108864) BSN.abs_quadSignPos qz655 (BSN.sfrac_eq_quadSignPos_mul Bool.false 37597063 67108864) qz132 rfl rfl (Ns132p992 rfl rfl) (Ns132p974 rfl) RS133to150.d27 RS133to150.d29 RS133to150.d31 RS133to150.d33 RS133to150.d17 (Ns132p996 rfl rfl) (Ns132p1000 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns132p1002 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz129) qz129 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz129) qz129 7) 24109818 67108864 51666 67108864 24109818 67108864 51666 67108864 3235964994453504 12054909 16777216 25833 16777216 (Ns132p1001 rfl) 

noncomputable def Ns132p1003 := @Enclosure.Real.IsNear.mulLit_tf qz698 (Zeta.RiemannSiegel.correction qz131) 1498787 4194304 1 4194304 21063005606549 35184372088832 477806697318905 3761486453226340352 31568958984022756063 147573952589676412928 

noncomputable abbrev qz701 := (@HPow.hPow Real Real Real qz7 qz130 qz9)

noncomputable def Ns132p1004 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz701 1 1 0 1 1498787 4194304 1 4194304 1498787 4194304 1 4194304 

noncomputable def Ns132p1005 := @Enclosure.Real.IsNear.sqrt_image qz130 257240943253 4194304000 192677 4194304000 32847312 32847337 4194304 (@Enclosure.Real.IsNear.of_eq qz130 (@HMul.hMul Real Real Real qz5 qz129 qz3) Bool.false 257240943253 4194304000 192677 4194304000 (BSN.t_div_two_pi_mk qz129 385354 1000 qz132) (@Enclosure.Real.IsNear.mulLit_ff qz129 qz3 385354 1000 0 1 1335089 8388608 1 8388608 257240943253 4194304000 192677 4194304000 (Enclosure.Real.IsNear.const Bool.false 385354 1000) RS133to150.d36 rfl)) 

noncomputable abbrev qz880 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 385354 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz702 := qz880

noncomputable abbrev qz479 := qz702

noncomputable abbrev qz135 := qz479

noncomputable def Ns132p1006 := @Enclosure.Real.IsNear.sqrt_image qz135 65694649 8388608 25 8388608 11737615 11737620 4194304 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 65694649 8388608 25 8388608 65694649 8388608 25 8388608 (Ns132p1005 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns132p1007 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz135) 23475235 8388608 5 8388608 1498786 1498788 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz135) Bool.false 23475235 8388608 5 8388608 23475235 8388608 5 8388608 (Ns132p1006 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns132p1008 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz135)) Bool.false 2997574 8388608 2 8388608 1498787 4194304 1 4194304 (Ns132p1007 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz136 := (@HMul.hMul Real Real Real qz339 qz337 qz473)

noncomputable abbrev qz703 := (@HMul.hMul Real Real Real qz843 qz879 qz879)

noncomputable abbrev qz480 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz703 qz697) qz640)

noncomputable abbrev qz137 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz480))

noncomputable def Ns132p1009 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz131) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz136)) qz137) Bool.false 21063005606549 

noncomputable def Ns132p1010 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz136)) qz137 17136697 8388608 681 

noncomputable def Ns132p1011 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz136)) Bool.false 17136697 8388608 681 8388608 17136697 8388608 681 

noncomputable def Ns132p1012 := @Enclosure.Real.IsNear.recentre' (Real.cos qz136) Bool.false 4106319 8388608 139325858 7174466043904 4106319 8388608 69662929 3587233021952 

noncomputable def Ns132p1013 := @Enclosure.Real.IsNear.cos_image qz136 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 43821403) qz365) Bool.false 43821403 8388608 79 4194304 Bool.false 4106319 8388608 1 

noncomputable def Ns132p1014 := nat_lit 674651885286010716068126831 

noncomputable def Ns132p1015 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz131 884279719003555 140737488355328 1 500000000000000 6974393 8388608 25 8388608 6167314282260360967115 1180591620717411303424 Ns132p1014 

noncomputable def Ns132p1016 := @Enclosure.Real.IsNear.subLit_ff_p qz135 qz1 65694649 8388608 25 8388608 7 1 0 1 6974393 6974393 8388608 25 

noncomputable def Ns132p1017 := @Ns132p1016 8388608 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 65694649 8388608 25 8388608 65694649 8388608 25 8388608 (Ns132p1005 rfl rfl rfl rfl rfl rfl) rfl) qz366 

noncomputable def Ns132p1018 := @Enclosure.Real.IsNear.recentre' qz136 Bool.false 6167314282260360967115 1180591620717411303424 Ns132p1014 Ns132p405 43821403 8388608 79 4194304 (@Ns132p1015 Ns132p405 RS133to150.d35 (Ns132p1017 rfl rfl) rfl) 

noncomputable def Ns132p1019 := nat_lit 5964329109552689872796897232320142151936 

noncomputable def Ns132p1020 := BSN.sin_dyadic_bound_f 8788007116 17179869184 2 1 8388608 3424393 Ns132p1019 Ns132p617 Ns132p1019 Ns132p1019 Ns132p618 Ns132p1019 4106319 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 8788007116) qz355 0 1 Ns132p1019 Ns132p617 Ns132p1019 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 8788007116) qz356 0 1 Ns132p1019 Ns132p618 Ns132p1019 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1021 := @Ns132p1013 1710526 (Ns132p1018 rfl) (Enclosure.sfrac_false_div 43821403 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 43821403) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 618401024638367087722496) qz367) 226375608064910080 72057594037927936 Bool.false 4106319 8388608 0 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 43821403 8388608 226375608064910080 72057594037927936 0 618401024638367087722496 Ns132p87 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 4106319 8388608 618401024638367087722496 Ns132p87 8788007116 17179869184 3424393 3421052 (Ns132p1020 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p1022 := @Enclosure.Real.IsNear.inv_image (Real.cos qz136) 4106319 8388608 69662929 3587233021952 8568008 8568689 4194304 (Ns132p1012 (Ns132p1021 rfl rfl) rfl) rfl 

noncomputable def Ns132p1023 := @Enclosure.Real.IsNear.recentre' qz137 Bool.false 1229117 4194304 

noncomputable abbrev qz138 := (@HMul.hMul Real Real Real qz339 qz337 qz480)

noncomputable def Ns132p1024 := @Enclosure.Real.IsNear.cos_image qz138 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 5340971)) qz357) Bool.true 5340971 4194304 

noncomputable def Ns132p1025 := nat_lit 12611011700690446940231514445 

noncomputable def Ns132p1026 := nat_lit 15069981839557834777781571923268933 

noncomputable def Ns132p1027 := @Enclosure.Real.IsNear.recentre' qz138 Bool.true Ns132p1025 Ns132p285 Ns132p1026 

noncomputable abbrev qz139 := qz480

noncomputable def Ns132p1028 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz139 884279719003555 140737488355328 1 500000000000000 14261337707599 

noncomputable abbrev qz481 := (@HSub.hSub Real Real Real qz635 qz703 qz697)

noncomputable abbrev qz140 := qz481

noncomputable def Ns132p1029 := @Enclosure.Real.IsNear.subLit_tf qz140 qz27 9863291196495 70368744177664 558435475 70368744177664 1 16 

noncomputable abbrev qz482 := qz703

noncomputable abbrev qz141 := qz482

noncomputable def Ns132p1030 := @Enclosure.Real.IsNear.subLit_ff_n qz141 qz131 48642157718449 70368744177664 348720275 70368744177664 6974393 8388608 25 8388608 

noncomputable def Ns132p1031 := @Enclosure.Real.IsNear.mulLit_ff qz131 qz131 6974393 8388608 25 8388608 6974393 8388608 25 8388608 48642157718449 70368744177664 

noncomputable def Ns132p1032 := nat_lit 423749254146351682493705680910996588128248259375307257441 

noncomputable def Ns132p1033 := nat_lit 662158196030540603238395434988972797638932938943460961 

noncomputable def Ns132p1034 := nat_lit 1269923446046993966274640251863011818789466912248034850401 

noncomputable def Ns132p1035 := BSN.cos_dyadic_bound_f 5340971 4194304 3 2 4194304 1710526 Ns132p1032 Ns132p829 Ns132p1033 Ns132p1034 Ns132p832 Ns132p1033 1229117 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 5340971) (BSN.cosEvenQ 4194304) 0 2 Ns132p1032 Ns132p829 Ns132p1033 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 5340971) (BSN.cosOddQ 4194304) 0 2 Ns132p1034 Ns132p832 Ns132p1033 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1036 := @Ns132p1023 725099002 14348932087808 1229117 4194304 362549501 7174466043904 (@Ns132p1024 419 8388608 Bool.false 1229117 4194304 1 1710526 (@Ns132p1027 Ns132p288 5340971 4194304 419 8388608 (@Ns132p1028 70368744177664 558435475 70368744177664 Ns132p1025 Ns132p285 Ns132p1026 Ns132p288 RS133to150.d35 (@Ns132p1029 0 1 228181403321584 14261337707599 70368744177664 558435475 70368744177664 (@Ns132p1030 82739283437247528960 9863291196495 70368744177664 558435475 70368744177664 (@Ns132p1031 348720275 70368744177664 (Ns132p1017 rfl rfl) (Ns132p1017 rfl rfl) rfl) (Ns132p1017 rfl rfl) rfl rfl) qz372 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 5340971 4194304) (BSN.cos_neg_of_bound 5340971 4194304 Bool.false 1229117 4194304 1 1710526 (Ns132p1035 rfl rfl)) rfl rfl) 

noncomputable def Ns132p1037 := @Ns132p1003 5747061963453729814507 Ns132p188 (Ns132p1004 qz29 (@Enclosure.Real.IsNear.of_eq qz701 (@Inv.inv Real Real.instInv (Real.sqrt qz135)) Bool.false 1498787 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz130 (BSN.t_div_two_pi_nonneg qz129 385354 1000 qz132)) Ns132p1008) rfl) (@Ns132p1009 35184372088832 477806697318905 3761486453226340352 (BSN.correction_mk qz131 (BSN.cos_two_pi_p_ne_zero_mk qz129 385354 1000 7 qz132 rfl rfl (@BSN.floor_sqrt_eq_dec qz129 385354 1000 7 qz132 rfl rfl rfl))) (@Ns132p1010 8388608 1229117 4194304 362549501 7174466043904 21063005606549 35184372088832 477806697318905 3761486453226340352 (@Ns132p1011 8388608 (Ns132p1022 rfl rfl rfl rfl rfl) rfl) (Ns132p1036 rfl) rfl)) 

noncomputable def Ns132p1038 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz129) (hardyZApproximantRS₀ qz129) Bool.true 74467141954229663009 147573952589676412928 200088021055845830440939 Ns132p188 (@Eq.refl Real (hardyZApproximantRS₀ qz129)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz129) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz129) qz129 7) (@HMul.hMul Real Real Real qz5 qz698 (Zeta.RiemannSiegel.correction qz131))) Bool.true 74467141954229663009 147573952589676412928 200088021055845830440939 Ns132p188 (BSN.hardyZApproximantRS₀_eq qz129 7 (@BSN.floor_sqrt_eq_dec qz129 385354 1000 7 qz132 rfl rfl rfl)) (@Ns132p938 74467141954229663009 147573952589676412928 200088021055845830440939 Ns132p188 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz129) qz129 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz129) qz129 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz129) qz129 7)) Bool.true 12054909 16777216 25833 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz129) qz129 7) (Ns132p1002 (Ns132p1001 rfl) rfl rfl)) (Ns132p1037 rfl) rfl rfl)) 

theorem RS133to150.d47 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz129) Bool.true 74467141954229663009 147573952589676412928 200088021055845830440939 Ns132p188 := Ns132p1038 

noncomputable def Ns132p1039 := nat_lit 1165843432947704464932864000 

noncomputable abbrev qz881 := (Enclosure.sfrac Bool.false 386880 1000)

noncomputable abbrev qz704 := qz881

noncomputable abbrev qz483 := qz704

noncomputable abbrev qz142 := qz483

noncomputable abbrev qz882 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 386880 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz705 := qz882

noncomputable abbrev qz484 := qz705

noncomputable abbrev qz143 := qz484

noncomputable abbrev qz883 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 386880 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz706 := qz883

noncomputable abbrev qz485 := qz706

noncomputable abbrev qz144 := qz485

noncomputable abbrev qz707 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz143 qz9))

noncomputable def Ns132p1040 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz142) qz142 7) (@HMul.hMul Real Real Real qz5 qz707 (Zeta.RiemannSiegel.correction qz144)) 12077541 16777216 51875 33554432 16372096626804348111 73786976294838206464 5189982099103264302423 Ns132p188 Ns132p1039 

noncomputable def Ns132p1041 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz142) qz142 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 386880 1000 57 95 67108864 33554432 1125899906842624 Bool.false 40479133724 1259 

noncomputable def Ns132p1042 := Ns132p1041 120242927 40 27397080 8 130587807 40 25364760 8 Bool.false 26281715 38699 Bool.true 31831520 Bool.true 28313126 3537118876014220 1 Bool.false 30651268 Bool.true Bool.false 27480621 Bool.false Bool.false 24155082 

noncomputable def Ns132p1043 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz142) qz142 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 386880 1000 42 12 67108864 33554432 1125899906842624 Bool.false 40479133724 1259 

noncomputable def Ns132p1044 := Ns132p1043 93032624 40 33554424 8 108007536 40 30011992 8 Bool.false 23215561 22828 Bool.false 59269154 Bool.true 41849518 3537118876014220 1 Bool.false 42593833 Bool.true Bool.false 54477480 Bool.false Bool.false 26281715 

noncomputable def Ns132p1045 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz142) qz142 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 386880 1000 213 113 67108864 33554432 1125899906842624 Bool.false 40479133724 1259 

noncomputable def Ns132p1046 := Ns132p1045 46516304 40 47453136 16 73726608 40 38745320 8 Bool.false 67108856 1304 Bool.false 29647977 Bool.false 43961272 3537118876014220 1 Bool.false 28692907 Bool.true Bool.false 40883923 Bool.true Bool.false 23215561 

noncomputable def Ns132p1047 := nat_lit 889551285603318781403439973700183555263411251 

noncomputable def Ns132p1048 := nat_lit 1474754293234500625395446753392961624473600 

noncomputable def Ns132p1049 := nat_lit 4160298295996930618712064000000000 

noncomputable def Ns132p1050 := nat_lit 9657224756018335486121228881920000000 

noncomputable abbrev qz708 := (@Eq.refl Real qz881)

noncomputable abbrev qz486 := qz708

noncomputable abbrev qz145 := qz486

noncomputable def Ns132p1051 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz142 386880 1000 598705537600 16000000 773760 4000 2000 Ns132p1049 Ns132p1050 qz145 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns132p1052 := nat_lit 163962092962403717788282055952417832906151961784320000000 

noncomputable abbrev qz487 := (Enclosure.sfrac Bool.false 386880 2000)

noncomputable abbrev qz709 := (Real.log (Enclosure.sfrac Bool.false 598705537600 16000000))

noncomputable abbrev qz146 := (@HSub.hSub Real Real Real qz342 (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 386880 4000) qz709) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 773760)))))) qz487)

noncomputable abbrev qz488 := (@HSub.hSub Real Real Real qz12 qz146 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 386880 2000) (Real.log Real.pi)))

noncomputable def Ns132p1053 := @Enclosure.Real.IsNear.addLit_ft_p qz488 (Enclosure.sfrac Bool.true Ns132p1049 Ns132p1050) 16978191375551227971 28147497671065600 10259915094727489071 547368320000000000000000 Ns132p1049 Ns132p1050 0 1 Ns132p1052 

noncomputable def Ns132p1054 := nat_lit 3560584799962000884183859200 

noncomputable abbrev qz489 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 386880 2000) (Real.log Real.pi))

noncomputable def Ns132p1055 := @Enclosure.Real.IsNear.subLit_ff_p qz146 qz489 23211076107805976643 28147497671065600 246800049636898731 34210520000000000000000 46438610049 209715200 1209 104857600 Ns132p1054 16978191375551227971 28147497671065600 

noncomputable abbrev qz147 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 386880 4000) qz709) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 773760))))))

noncomputable def Ns132p1056 := @Enclosure.Real.IsNear.subLit_ff_p qz147 qz487 28655928057296906307 28147497671065600 246800049636898731 34210520000000000000000 386880 2000 0 1 46422152215611953286000 23211076107805976643 28147497671065600 246800049636898731 34210520000000000000000 

noncomputable def Ns132p1057 := nat_lit 129054826920798088593975422088118272 

noncomputable def Ns132p1058 := nat_lit 12729912034049163815550976 

noncomputable def Ns132p1059 := nat_lit 23856146182742163666627447681015884120064000000000 

noncomputable def Ns132p1060 := nat_lit 35012077652879349301007759676666858700800000000 

noncomputable def Ns132p1061 := nat_lit 92007331921240252432324446337912012800000000 

noncomputable def Ns132p1062 := BSN.log_dyadic_bound 74417537600 1122993537600 3 2 Ns132p1059 33554432 13684208 Ns132p1060 Ns132p1061 4453637 1197411075200 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 74417537600) (BSN.artanhQ 1122993537600) 0 2 Ns132p1060 Ns132p1059 Ns132p1061 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns132p1063 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 386880 4000) qz709 386880 4000 0 1 47422617800716921 4503599627370496 12500002565789 171052600000000000000 57333944921066757489 56294995342131200 15112503102038901 2138157500000000000000 (Enclosure.Real.IsNear.const Bool.false 386880 4000) (BSN.isNear_log_sfrac 598705537600 16000000 47422617800716921 4503599627370496 12500002565789 171052600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 598705537600) qz350)) Bool.false Ns132p1058 Ns132p87 1000000205263120 13684208000000000000000 47422617800716921 4503599627370496 12500002565789 171052600000000000000 (BSN.log_rat_reduce_isNear 598705537600 16000000 15 1197411075200 1048576000000 4453637 33554432 24973259072661432 36028797018963968 13684208 1000000000000000 rfl rfl rfl rfl (Ns132p1062 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns132p1064 := BSN.arctan_dyadic_bound_f 1000 773760 1 0 4194304 1710526 0 1 1 0 1 1 5420 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 773760) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 773760) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz490 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 773760)))

noncomputable def Ns132p1065 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz490 884279719003555 562949953421312 1 2000000000000000 5420 4194304 1 1710526 3705886773787943239680 883552258917795 562949953421312 1000000000855263 1710526000000000000000 qz17 (Ns132p1064 rfl) rfl rfl 

noncomputable def Ns132p1066 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 386880 4000) qz709) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz490)) 57333944921066757489 56294995342131200 15112503102038901 2138157500000000000000 883552258917795 2251799813685248 1000000000855263 6842104000000000000000 Ns132p1057 28655928057296906307 28147497671065600 246800049636898731 34210520000000000000000 (Ns132p1063 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz490) 1 4 0 1 883552258917795 562949953421312 1000000000855263 1710526000000000000000 883552258917795 2251799813685248 1000000000855263 6842104000000000000000 qz353 Ns132p1065 rfl) 

noncomputable def Ns132p1067 := @Ns132p1053 Ns132p1047 Ns132p1048 10259915094727489071 547368320000000000000000 (@Ns132p1055 10259915094727489071 547368320000000000000000 (Ns132p1056 (Ns132p1066 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 386880 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz487 (Real.log Real.pi) 386880 2000 0 1 38410761 33554432 1 16777216 46438610049 209715200 1209 104857600 (Enclosure.Real.IsNear.const Bool.false 386880 2000) RS133to150.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns132p1049 Ns132p1050) 

noncomputable def Ns132p1068 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz142) Bool.false Ns132p1047 Ns132p1048 10259915094727489071 547368320000000000000000 5059891715 8388608 79 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz142) (@HAdd.hAdd Real Real Real qz354 qz488 (Enclosure.sfrac Bool.true Ns132p1049 Ns132p1050)) Bool.false Ns132p1047 Ns132p1048 10259915094727489071 547368320000000000000000 Ns132p1051 (Ns132p1067 rfl rfl)) 

noncomputable def Ns132p1069 := nat_lit 1899347449331108397711360 

noncomputable def Ns132p1070 := nat_lit 140098605804485013765653713426146903991512356498472288640747303044488841695032256757760 

noncomputable def Ns132p1071 := nat_lit 281706545949992936922004656604666307422001502105877721514748421076998472104270626816 

noncomputable def Ns132p1072 := nat_lit 366468823651636952250266956195881955480039597921160763462361915291917540246439472398336 

noncomputable def Ns132p1073 := BSN.sin_dyadic_bound_f 26991350656 17179869184 3 2 8388608 3424393 Ns132p1070 Ns132p99 Ns132p1071 Ns132p1072 Ns132p102 Ns132p1071 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26991350656) qz355 0 2 Ns132p1070 Ns132p99 Ns132p1071 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26991350656) qz356 0 2 Ns132p1072 Ns132p102 Ns132p1071 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1074 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz142) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5059891715) qz365) Bool.false 5059891715 8388608 79 4194304 Bool.false 8388607 8388608 1 1710526 (Ns132p1068 rfl) (Enclosure.sfrac_false_div 5059891715 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5059891715) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns132p1069) qz367) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 95 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 5059891715 8388608 226375608064910080 72057594037927936 95 Ns132p1069 Ns132p87 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns132p1069 Ns132p87 26991350656 17179869184 3424393 3421052 (Ns132p1073 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p1075 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz142) Bool.false Ns132p1047 Ns132p1048 10259915094727489071 547368320000000000000000 40479133724 67108864 1259 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz142) (@HAdd.hAdd Real Real Real qz354 qz488 (Enclosure.sfrac Bool.true Ns132p1049 Ns132p1050)) Bool.false Ns132p1047 Ns132p1048 10259915094727489071 547368320000000000000000 Ns132p1051 (Ns132p1067 rfl rfl)) 

noncomputable def Ns132p1076 := Ns132p1046 22828 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 213 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 28692907 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 113 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 40883923 67108864) qz145 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz142) qz142 1) Bool.false 8388607 8388608 69662929 3587233021952 67108856 67108864 1304 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz142) qz142 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz142)) Bool.false 8388607 8388608 69662929 3587233021952 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz142) qz142) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz142)) Bool.false 8388607 8388608 139325858 7174466043904 8388607 8388608 69662929 3587233021952 (Ns132p1074 rfl rfl) rfl)) rfl) (Ns132p1075 rfl) RS133to150.d7 

noncomputable def Ns132p1077 := nat_lit 772645465664918560084387415841 

noncomputable def Ns132p1078 := BSN.sin_dyadic_bound_f 29647977 67108864 2 1 67108864 33554432 Ns132p1077 Ns132p114 Ns132p1077 Ns132p1077 Ns132p115 Ns132p1077 28692907 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 29647977) qz359 0 1 Ns132p1077 Ns132p114 Ns132p1077 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 29647977) (BSN.sinOddQ 67108864) 0 1 Ns132p1077 Ns132p115 Ns132p1077 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1079 := nat_lit 229091397508439994984582586715716643424247935096883145533649059840 

noncomputable def Ns132p1080 := nat_lit 13949607897585306293974007115332346615768885630228886806593536 

noncomputable def Ns132p1081 := nat_lit 599978694109318182082764150148690194692795251819864058199965433856 

noncomputable def Ns132p1082 := BSN.sin_dyadic_bound_f 43961272 67108864 3 2 67108864 33554432 Ns132p1079 Ns132p108 Ns132p1080 Ns132p1081 Ns132p111 Ns132p1080 40883923 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 43961272) qz359 0 2 Ns132p1079 Ns132p108 Ns132p1080 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 43961272) (BSN.sinOddQ 67108864) 0 2 Ns132p1081 Ns132p111 Ns132p1080 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1083 := nat_lit 420630726443501510320925777700556327150989104617962961734767247616 

noncomputable def Ns132p1084 := nat_lit 152275426923163549662676372222163985032461358238597538912174336 

noncomputable def Ns132p1085 := nat_lit 1261587628476658203863451980357224653482902391137411690126477394176 

noncomputable def Ns132p1086 := BSN.cos_dyadic_bound_f 59269154 67108864 3 2 67108864 33554432 Ns132p1083 Ns132p124 Ns132p1084 Ns132p1085 Ns132p127 Ns132p1084 42593833 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 59269154) qz360 0 2 Ns132p1083 Ns132p124 Ns132p1084 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 59269154) (BSN.cosOddQ 67108864) 0 2 Ns132p1085 Ns132p127 Ns132p1084 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1087 := nat_lit 104527307886061030582129310656735566315116827253545201680407347456 

noncomputable def Ns132p1088 := nat_lit 9408571358398721445804075253386033402676704217961375221432576 

noncomputable def Ns132p1089 := nat_lit 313563106515466294303496323819699926878545128352199682290779177216 

noncomputable def Ns132p1090 := BSN.cos_dyadic_bound_f 41849518 67108864 3 2 67108864 33554432 Ns132p1087 Ns132p124 Ns132p1088 Ns132p1089 Ns132p127 Ns132p1088 54477480 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 41849518) qz360 0 2 Ns132p1087 Ns132p124 Ns132p1088 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 41849518) (BSN.cosOddQ 67108864) 0 2 Ns132p1089 Ns132p127 Ns132p1088 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1091 := Ns132p1044 38699 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 42 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 42593833 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 12 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 54477480 67108864) qz145 rfl rfl (Ns132p1076 RS133to150.d9 RS133to150.d11 RS133to150.d13 RS133to150.d17 (Ns132p1078 rfl rfl) (Ns132p1082 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns132p1075 rfl) RS133to150.d19 RS133to150.d21 RS133to150.d23 RS133to150.d25 RS133to150.d17 (Ns132p1086 rfl rfl) (Ns132p1090 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns132p1092 := nat_lit 1026666778675613400092508160000 

noncomputable def Ns132p1093 := BSN.sin_dyadic_bound_f 31831520 67108864 2 1 67108864 33554432 Ns132p1092 Ns132p114 Ns132p1092 Ns132p1092 Ns132p115 Ns132p1092 30651268 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 31831520) qz359 0 1 Ns132p1092 Ns132p114 Ns132p1092 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 31831520) (BSN.sinOddQ 67108864) 0 1 Ns132p1092 Ns132p115 Ns132p1092 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1094 := nat_lit 642615633255323260537898799376 

noncomputable def Ns132p1095 := BSN.sin_dyadic_bound_f 28313126 67108864 2 1 67108864 33554432 Ns132p1094 Ns132p114 Ns132p1094 Ns132p1094 Ns132p115 Ns132p1094 27480621 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 28313126) qz359 0 1 Ns132p1094 Ns132p114 Ns132p1094 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 28313126) (BSN.sinOddQ 67108864) 0 1 Ns132p1094 Ns132p115 Ns132p1094 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1096 := Ns132p1042 51875 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 57 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 30651268 67108864) BSN.abs_quadSignPos qz655 (BSN.sfrac_eq_quadSignPos_mul Bool.false 27480621 67108864) qz145 rfl rfl (Ns132p1091 rfl rfl) (Ns132p1075 rfl) RS133to150.d27 RS133to150.d29 RS133to150.d31 RS133to150.d33 RS133to150.d17 (Ns132p1093 rfl rfl) (Ns132p1095 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns132p1097 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz142) qz142 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz142) qz142 7) 24155082 67108864 51875 67108864 24155082 67108864 51875 67108864 3242040225693696 12077541 16777216 51875 33554432 (Ns132p1096 rfl) 

noncomputable def Ns132p1098 := @Enclosure.Real.IsNear.mulLit_tf qz707 (Zeta.RiemannSiegel.correction qz144) 2994613 8388608 1 8388608 5467182780147 8796093022208 3459965351668743 30091891625810722816 16372096626804348111 73786976294838206464 

noncomputable abbrev qz710 := (@HPow.hPow Real Real Real qz7 qz143 qz9)

noncomputable def Ns132p1099 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz710 1 1 0 1 2994613 8388608 1 8388608 2994613 8388608 1 8388608 

noncomputable def Ns132p1100 := @Enclosure.Real.IsNear.sqrt_image qz143 1614122601 26214400 1209 26214400 32912285 32912311 4194304 (@Enclosure.Real.IsNear.of_eq qz143 (@HMul.hMul Real Real Real qz5 qz142 qz3) Bool.false 1614122601 26214400 1209 26214400 (BSN.t_div_two_pi_mk qz142 386880 1000 qz145) (@Enclosure.Real.IsNear.mulLit_ff qz142 qz3 386880 1000 0 1 1335089 8388608 1 8388608 1614122601 26214400 1209 26214400 (Enclosure.Real.IsNear.const Bool.false 386880 1000) RS133to150.d36 rfl)) 

noncomputable abbrev qz884 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 386880 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz711 := qz884

noncomputable abbrev qz491 := qz711

noncomputable abbrev qz148 := qz491

noncomputable def Ns132p1101 := @Enclosure.Real.IsNear.sqrt_image qz148 16456149 2097152 13 4194304 11749218 11749223 4194304 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 65824596 8388608 26 8388608 16456149 2097152 13 4194304 (Ns132p1100 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns132p1102 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz148) 23498441 8388608 5 8388608 1497306 1497307 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz148) Bool.false 23498441 8388608 5 8388608 23498441 8388608 5 8388608 (Ns132p1101 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns132p1103 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz148)) Bool.false 2994613 8388608 1 8388608 2994613 8388608 1 8388608 (Ns132p1102 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz149 := (@HMul.hMul Real Real Real qz339 qz337 qz485)

noncomputable abbrev qz712 := (@HMul.hMul Real Real Real qz843 qz883 qz883)

noncomputable abbrev qz492 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz712 qz706) qz640)

noncomputable abbrev qz150 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz492))

noncomputable def Ns132p1104 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz144) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz149)) qz150) Bool.false 5467182780147 

noncomputable def Ns132p1105 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz149)) qz150 7333549 4194304 65 

noncomputable def Ns132p1106 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz149)) Bool.false 14667098 8388608 520 8388608 7333549 4194304 65 

noncomputable def Ns132p1107 := @Enclosure.Real.IsNear.recentre' (Real.cos qz149) Bool.false 4797728 8388608 290625398 14348932087808 149929 262144 145312699 7174466043904 

noncomputable def Ns132p1108 := @Enclosure.Real.IsNear.cos_image qz149 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11159471) qz368) Bool.false 11159471 2097152 165 8388608 Bool.false 4797728 8388608 1 

noncomputable def Ns132p1109 := nat_lit 350818980348085498876861211 

noncomputable def Ns132p1110 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz144 884279719003555 140737488355328 1 500000000000000 1776085 2097152 13 4194304 1570555944726428982175 295147905179352825856 Ns132p1109 

noncomputable def Ns132p1111 := @Enclosure.Real.IsNear.subLit_ff_p qz148 qz1 16456149 2097152 13 4194304 7 1 0 1 1776085 1776085 2097152 13 

noncomputable def Ns132p1112 := @Ns132p1111 4194304 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 65824596 8388608 26 8388608 16456149 2097152 13 4194304 (Ns132p1100 rfl rfl rfl rfl rfl rfl) rfl) qz366 

noncomputable def Ns132p1113 := @Enclosure.Real.IsNear.recentre' qz149 Bool.false 1570555944726428982175 295147905179352825856 Ns132p1109 Ns132p153 11159471 2097152 165 8388608 (@Ns132p1110 Ns132p153 RS133to150.d35 (Ns132p1112 rfl rfl) rfl) 

noncomputable def Ns132p1114 := nat_lit 11971631610291109624777367992394476851456 

noncomputable def Ns132p1115 := BSN.sin_dyadic_bound_f 10460160204 17179869184 2 1 8388608 3424393 Ns132p1114 Ns132p617 Ns132p1114 Ns132p1114 Ns132p618 Ns132p1114 4797728 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 10460160204) qz355 0 1 Ns132p1114 Ns132p617 Ns132p1114 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 10460160204) qz356 0 1 Ns132p1114 Ns132p618 Ns132p1114 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1116 := @Ns132p1108 1710526 (Ns132p1113 rfl) (Enclosure.sfrac_false_div 11159471 2097152) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11159471) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 184017084378432491487232) qz453) 226375608064910080 72057594037927936 Bool.false 4797728 8388608 0 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 11159471 2097152 226375608064910080 72057594037927936 0 184017084378432491487232 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 4797728 8388608 184017084378432491487232 302231454903657293676544 10460160204 17179869184 3424393 3421052 (Ns132p1115 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p1117 := @Enclosure.Real.IsNear.inv_image (Real.cos qz149) 149929 262144 145312699 7174466043904 7333289 7333809 4194304 (Ns132p1107 (Ns132p1116 rfl rfl) rfl) rfl 

noncomputable def Ns132p1118 := @Enclosure.Real.IsNear.recentre' qz150 Bool.false 1491006 4194304 

noncomputable abbrev qz151 := (@HMul.hMul Real Real Real qz339 qz337 qz492)

noncomputable def Ns132p1119 := @Enclosure.Real.IsNear.cos_image qz151 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 5064055)) qz357) Bool.true 5064055 4194304 

noncomputable def Ns132p1120 := nat_lit 747322643818206033715166645 

noncomputable def Ns132p1121 := nat_lit 618970019642690137449562112 

noncomputable def Ns132p1122 := nat_lit 3963783327727041885980230041674299 

noncomputable def Ns132p1123 := @Enclosure.Real.IsNear.recentre' qz151 Bool.true Ns132p1120 Ns132p1121 Ns132p1122 

noncomputable abbrev qz152 := qz492

noncomputable def Ns132p1124 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz152 884279719003555 140737488355328 1 500000000000000 845120189639 

noncomputable abbrev qz493 := (@HSub.hSub Real Real Real qz635 qz712 qz706)

noncomputable abbrev qz153 := qz493

noncomputable def Ns132p1125 := @Enclosure.Real.IsNear.subLit_tf qz153 qz27 570242282695 4398046511104 146882541 17592186044416 1 16 

noncomputable abbrev qz494 := qz712

noncomputable abbrev qz154 := qz494

noncomputable def Ns132p1126 := @Enclosure.Real.IsNear.subLit_ff_n qz154 qz144 3154477927225 4398046511104 92356589 17592186044416 1776085 2097152 13 4194304 

noncomputable def Ns132p1127 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz144 1776085 2097152 13 4194304 1776085 2097152 13 4194304 3154477927225 4398046511104 

noncomputable def Ns132p1128 := nat_lit 342366712823059374148336516663397327254158236369238690625 

noncomputable def Ns132p1129 := nat_lit 432501194023770892803363356397579579866991948937890625 

noncomputable def Ns132p1130 := nat_lit 1026235136081130580659402823277396822602740725209840290625 

noncomputable def Ns132p1131 := BSN.cos_dyadic_bound_f 5064055 4194304 3 2 4194304 1710526 Ns132p1128 Ns132p829 Ns132p1129 Ns132p1130 Ns132p832 Ns132p1129 1491006 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 5064055) (BSN.cosEvenQ 4194304) 0 2 Ns132p1128 Ns132p829 Ns132p1129 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 5064055) (BSN.cosOddQ 4194304) 0 2 Ns132p1130 Ns132p832 Ns132p1129 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1132 := @Ns132p1118 762730574 14348932087808 745503 2097152 381365287 7174466043904 (@Ns132p1119 441 8388608 Bool.false 1491006 4194304 1 1710526 (@Ns132p1123 Ns132p174 5064055 4194304 441 8388608 (@Ns132p1124 4398046511104 146882541 17592186044416 Ns132p1120 Ns132p1121 Ns132p1122 Ns132p174 RS133to150.d35 (@Ns132p1125 0 1 13521923034224 845120189639 4398046511104 146882541 17592186044416 (@Ns132p1126 1195884743638384640 570242282695 4398046511104 146882541 17592186044416 (@Ns132p1127 92356589 17592186044416 (Ns132p1112 rfl rfl) (Ns132p1112 rfl rfl) rfl) (Ns132p1112 rfl rfl) rfl rfl) qz372 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 5064055 4194304) (BSN.cos_neg_of_bound 5064055 4194304 Bool.false 1491006 4194304 1 1710526 (Ns132p1131 rfl rfl)) rfl rfl) 

noncomputable def Ns132p1133 := @Ns132p1098 5189982099103264302423 Ns132p188 (Ns132p1099 qz29 (@Enclosure.Real.IsNear.of_eq qz710 (@Inv.inv Real Real.instInv (Real.sqrt qz148)) Bool.false 2994613 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz143 (BSN.t_div_two_pi_nonneg qz142 386880 1000 qz145)) Ns132p1103) rfl) (@Ns132p1104 8796093022208 3459965351668743 30091891625810722816 (BSN.correction_mk qz144 (BSN.cos_two_pi_p_ne_zero_mk qz142 386880 1000 7 qz145 rfl rfl (@BSN.floor_sqrt_eq_dec qz142 386880 1000 7 qz145 rfl rfl rfl))) (@Ns132p1105 1048576 745503 2097152 381365287 7174466043904 5467182780147 8796093022208 3459965351668743 30091891625810722816 (@Ns132p1106 1048576 (Ns132p1117 rfl rfl rfl rfl rfl) rfl) (Ns132p1132 rfl) rfl)) 

noncomputable def Ns132p1134 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz142) (hardyZApproximantRS₀ qz142) Bool.false 69489683684569863375 73786976294838206464 200317091860219670062423 Ns132p188 (@Eq.refl Real (hardyZApproximantRS₀ qz142)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz142) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz142) qz142 7) (@HMul.hMul Real Real Real qz5 qz707 (Zeta.RiemannSiegel.correction qz144))) Bool.false 69489683684569863375 73786976294838206464 200317091860219670062423 Ns132p188 (BSN.hardyZApproximantRS₀_eq qz142 7 (@BSN.floor_sqrt_eq_dec qz142 386880 1000 7 qz145 rfl rfl rfl)) (@Ns132p1040 69489683684569863375 73786976294838206464 200317091860219670062423 Ns132p188 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz142) qz142 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz142) qz142 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz142) qz142 7)) Bool.false 12077541 16777216 51875 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz142) qz142 7) (Ns132p1097 (Ns132p1096 rfl) rfl rfl)) (Ns132p1133 rfl) rfl rfl)) 

theorem RS133to150.d48 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz142) Bool.false 69489683684569863375 73786976294838206464 200317091860219670062423 Ns132p188 := Ns132p1134 

noncomputable def Ns132p1135 := nat_lit 1368167606880188771891937280 

noncomputable abbrev qz885 := (Enclosure.sfrac Bool.false 388404 1000)

noncomputable abbrev qz713 := qz885

noncomputable abbrev qz495 := qz713

noncomputable abbrev qz155 := qz495

noncomputable abbrev qz886 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 388404 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz714 := qz886

noncomputable abbrev qz496 := qz714

noncomputable abbrev qz156 := qz496

noncomputable abbrev qz887 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 388404 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz715 := qz887

noncomputable abbrev qz497 := qz715

noncomputable abbrev qz157 := qz497

noncomputable abbrev qz716 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz156 qz9))

noncomputable def Ns132p1136 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz155) qz155 7) (@HMul.hMul Real Real Real qz5 qz716 (Zeta.RiemannSiegel.correction qz157)) 40948055 16777216 3255 2097152 8496581013332413155 36893488147419103232 1164925427957043163075 Ns132p333 Ns132p1135 

noncomputable def Ns132p1137 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz155) qz155 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 388404 1000 57 95 67108864 33554432 1125899906842624 Bool.false 40689930718 1263 

noncomputable def Ns132p1138 := Ns132p1137 120242927 40 27397080 8 130587807 40 25364760 8 Bool.true 86333538 38852 Bool.true 4284747 Bool.true 16531950 3537118876014220 1 Bool.false 4281836 Bool.true Bool.false 16365247 Bool.false Bool.true 81896110 

noncomputable def Ns132p1139 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz155) qz155 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 388404 1000 43 11 67108864 33554432 1125899906842624 Bool.false 40689930718 1263 

noncomputable def Ns132p1140 := Ns132p1139 93032624 40 33554424 8 108007536 40 30011992 8 Bool.true 127497649 22919 Bool.false 22870072 Bool.true 101070366 3537118876014220 1 Bool.false 22429953 Bool.false Bool.false 66968318 Bool.false Bool.true 86333538 

noncomputable def Ns132p1141 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz155) qz155 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 388404 1000 214 114 67108864 33554432 1125899906842624 Bool.false 40689930718 1263 

noncomputable def Ns132p1142 := Ns132p1141 46516304 40 47453136 16 73726608 40 38745320 8 Bool.true 67108856 1312 Bool.false 64139766 Bool.false 36984558 3537118876014220 1 Bool.false 38721186 Bool.true Bool.false 57172881 Bool.true Bool.true 127497649 

noncomputable def Ns132p1143 := nat_lit 286102218218575233483306177861688036057559712116637 

noncomputable def Ns132p1144 := nat_lit 471861084884630751489139716498645846182592512000 

noncomputable def Ns132p1145 := nat_lit 43789465600000000000000000 

noncomputable def Ns132p1146 := nat_lit 4242887630321087815738921451520000 

noncomputable def Ns132p1147 := nat_lit 9887734809801161204004328345153044480 

noncomputable abbrev qz888 := (@Eq.refl Real (Enclosure.sfrac Bool.false 388404 1000))

noncomputable abbrev qz717 := qz888

noncomputable abbrev qz498 := qz717

noncomputable abbrev qz158 := qz498

noncomputable def Ns132p1148 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz155 388404 1000 603431668864 16000000 776808 4000 2000 Ns132p1146 Ns132p1147 qz158 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns132p1149 := nat_lit 26999992761368466962249213288174765468738255942317328302080 

noncomputable abbrev qz499 := (Enclosure.sfrac Bool.false 388404 2000)

noncomputable abbrev qz718 := (Real.log (Enclosure.sfrac Bool.false 603431668864 16000000))

noncomputable abbrev qz159 := (@HSub.hSub Real Real Real qz342 (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 388404 4000) qz718) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 776808)))))) qz499)

noncomputable abbrev qz500 := (@HSub.hSub Real Real Real qz12 qz159 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 388404 2000) (Real.log Real.pi)))

noncomputable def Ns132p1150 := @Enclosure.Real.IsNear.addLit_ft_p qz500 (Enclosure.sfrac Bool.true Ns132p1146 Ns132p1147) 2730656959253398341621 4503599627370496000 824001270151453968459 Ns132p1145 Ns132p1146 Ns132p1147 0 1 Ns132p1149 

noncomputable def Ns132p1151 := nat_lit 45812821627297462711417307136000 

noncomputable abbrev qz501 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 388404 2000) (Real.log Real.pi))

noncomputable def Ns132p1152 := @Enclosure.Real.IsNear.subLit_ff_p qz159 qz501 3731846935079152437237 4503599627370496000 2419458494457147 334087109375000000000 3729723303861 16777216000 97101 8388608000 Ns132p1151 2730656959253398341621 4503599627370496000 

noncomputable def Ns132p1153 := nat_lit 7463693870158304874474000 

noncomputable abbrev qz160 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 388404 4000) qz718) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 776808))))))

noncomputable def Ns132p1154 := @Enclosure.Real.IsNear.subLit_ff_p qz160 qz499 4606454989913757501429 4503599627370496000 2419458494457147 334087109375000000000 388404 2000 0 1 Ns132p1153 3731846935079152437237 4503599627370496000 2419458494457147 334087109375000000000 

noncomputable def Ns132p1155 := nat_lit 10372814488037280096773591933116219392 

noncomputable def Ns132p1156 := nat_lit 12739417727739459193012224 

noncomputable def Ns132p1157 := nat_lit 24260283948024913016929924688110486351125927690240 

noncomputable def Ns132p1158 := nat_lit 39947185893574423878288655766526584810926768128 

noncomputable def Ns132p1159 := nat_lit 117702576788689093051645470844265249057538048 

noncomputable def Ns132p1160 := BSN.log_dyadic_bound 79143668864 1127719668864 3 2 Ns132p1157 33554432 13684208 Ns132p1158 Ns132p1159 4717473 1206863337728 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 79143668864) (BSN.artanhQ 1127719668864) 0 2 Ns132p1158 Ns132p1157 Ns132p1159 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns132p1161 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 388404 4000) qz718 388404 4000 0 1 47458029269201529 4503599627370496 12500002565789 171052600000000000000 4608222100068737667429 4503599627370496000 1213762749140677689 171052600000000000000000 (Enclosure.Real.IsNear.const Bool.false 388404 4000) (BSN.isNear_log_sfrac 603431668864 16000000 47458029269201529 4503599627370496 12500002565789 171052600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 603431668864) qz350)) Bool.false Ns132p1156 Ns132p87 1000000205263120 13684208000000000000000 47458029269201529 4503599627370496 12500002565789 171052600000000000000 (BSN.log_rat_reduce_isNear 603431668864 16000000 15 1206863337728 1048576000000 4717473 33554432 24973259072661432 36028797018963968 13684208 1000000000000000 rfl rfl rfl rfl (Ns132p1160 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns132p1162 := BSN.arctan_dyadic_bound_f 1000 776808 1 0 4194304 1710526 0 1 1 0 1 1 5399 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 776808) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 776808) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz502 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 776808)))

noncomputable def Ns132p1163 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz502 884279719003555 562949953421312 1 2000000000000000 5399 4194304 1 1710526 3705898595736965087232 883555077490083 562949953421312 1000000000855263 1710526000000000000000 qz17 (Ns132p1162 rfl) rfl rfl 

noncomputable def Ns132p1164 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 388404 4000) qz718) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz502)) 4608222100068737667429 4503599627370496000 1213762749140677689 171052600000000000000000 883555077490083 2251799813685248 1000000000855263 6842104000000000000000 Ns132p1155 4606454989913757501429 4503599627370496000 2419458494457147 334087109375000000000 (Ns132p1161 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz502) 1 4 0 1 883555077490083 562949953421312 1000000000855263 1710526000000000000000 883555077490083 2251799813685248 1000000000855263 6842104000000000000000 qz353 Ns132p1163 rfl) 

noncomputable def Ns132p1165 := @Ns132p1150 Ns132p1143 Ns132p1144 824001270151453968459 Ns132p1145 (@Ns132p1152 824001270151453968459 Ns132p1145 (Ns132p1154 (Ns132p1164 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 388404 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz499 (Real.log Real.pi) 388404 2000 0 1 38410761 33554432 1 16777216 3729723303861 16777216000 97101 8388608000 (Enclosure.Real.IsNear.const Bool.false 388404 2000) RS133to150.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns132p1146 Ns132p1147) 

noncomputable def Ns132p1166 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz155) Bool.false Ns132p1143 Ns132p1144 824001270151453968459 Ns132p1145 5086241339 8388608 159 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz155) (@HAdd.hAdd Real Real Real qz354 qz500 (Enclosure.sfrac Bool.true Ns132p1146 Ns132p1147)) Bool.false Ns132p1143 Ns132p1144 824001270151453968459 Ns132p1145 Ns132p1148 (Ns132p1165 rfl rfl)) 

noncomputable def Ns132p1167 := nat_lit 1898775994182855670366208 

noncomputable def Ns132p1168 := nat_lit 139929737994655297662769879598304147769483825020692288218725119377389874473140103840000 

noncomputable def Ns132p1169 := nat_lit 281029204962239870926573292776239390513557474855732571228714022896674091536100000000 

noncomputable def Ns132p1170 := nat_lit 366027647463682153135278089807254094668769020094903854505147870903712198900498967200000 

noncomputable def Ns132p1171 := BSN.sin_dyadic_bound_f 26983229790 17179869184 3 2 8388608 3424393 Ns132p1168 Ns132p99 Ns132p1169 Ns132p1170 Ns132p102 Ns132p1169 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26983229790) qz355 0 2 Ns132p1168 Ns132p99 Ns132p1169 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26983229790) qz356 0 2 Ns132p1170 Ns132p102 Ns132p1169 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1172 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz155) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5086241339) qz365) Bool.false 5086241339 8388608 159 8388608 Bool.true 8388607 8388608 1 1710526 (Ns132p1166 rfl) (Enclosure.sfrac_false_div 5086241339 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5086241339) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns132p1167) qz367) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 96 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q1 5086241339 8388608 226375608064910080 72057594037927936 96 Ns132p1167 Ns132p87 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns132p1167 Ns132p87 26983229790 17179869184 3424393 3421052 (Ns132p1171 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p1173 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz155) Bool.false Ns132p1143 Ns132p1144 824001270151453968459 Ns132p1145 40689930718 67108864 1263 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz155) (@HAdd.hAdd Real Real Real qz354 qz500 (Enclosure.sfrac Bool.true Ns132p1146 Ns132p1147)) Bool.false Ns132p1143 Ns132p1144 824001270151453968459 Ns132p1145 Ns132p1148 (Ns132p1165 rfl rfl)) 

noncomputable def Ns132p1174 := Ns132p1142 22919 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 214 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 38721186 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 114 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 57172881 67108864) qz158 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz155) qz155 1) Bool.true 8388607 8388608 140181121 7174466043904 67108856 67108864 1312 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz155) qz155 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz155)) Bool.true 8388607 8388608 140181121 7174466043904 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz155) qz155) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz155)) Bool.true 8388607 8388608 280362242 14348932087808 8388607 8388608 140181121 7174466043904 (Ns132p1172 rfl rfl) rfl)) rfl) (Ns132p1173 rfl) RS133to150.d7 

noncomputable def Ns132p1175 := nat_lit 576970979105779742891578612925899041635115241486432576038301982976 

noncomputable def Ns132p1176 := nat_lit 286430307562657488660133950510255830187234655355574928674775296 

noncomputable def Ns132p1177 := nat_lit 1730340076702213913697415570876676613244971255148586578257556398336 

noncomputable def Ns132p1178 := BSN.cos_dyadic_bound_f 64139766 67108864 3 2 67108864 33554432 Ns132p1175 Ns132p124 Ns132p1176 Ns132p1177 Ns132p127 Ns132p1176 38721186 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 64139766) qz360 0 2 Ns132p1175 Ns132p124 Ns132p1176 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 64139766) (BSN.cosOddQ 67108864) 0 2 Ns132p1177 Ns132p127 Ns132p1176 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1179 := nat_lit 63757959379114301565579398779376829510743817399280021773836042496 

noncomputable def Ns132p1180 := nat_lit 3500769065970195273382834262846478869602281077944845185270016 

noncomputable def Ns132p1181 := nat_lit 191266876599210964306191430669604795574492247635684175631137587456 

noncomputable def Ns132p1182 := BSN.cos_dyadic_bound_f 36984558 67108864 3 2 67108864 33554432 Ns132p1179 Ns132p124 Ns132p1180 Ns132p1181 Ns132p127 Ns132p1180 57172881 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 36984558) qz360 0 2 Ns132p1179 Ns132p124 Ns132p1180 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 36984558) (BSN.cosOddQ 67108864) 0 2 Ns132p1181 Ns132p127 Ns132p1180 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1183 := nat_lit 273571043791802637882353913856 

noncomputable def Ns132p1184 := BSN.sin_dyadic_bound_f 22870072 67108864 2 1 67108864 33554432 Ns132p1183 Ns132p114 Ns132p1183 Ns132p1183 Ns132p115 Ns132p1183 22429953 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 22870072) qz359 0 1 Ns132p1183 Ns132p114 Ns132p1183 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 22870072) (BSN.sinOddQ 67108864) 0 1 Ns132p1183 Ns132p115 Ns132p1183 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1185 := nat_lit 2231372121908926530915798664397498950050854476050404520045282342498837751810689332260720658301574189056 

noncomputable def Ns132p1186 := nat_lit 1136281826381777021870246554519701757835869088991881018089994945752556771417351076233569937657856 

noncomputable def Ns132p1187 := nat_lit 11145141833750101537651663651555885925444158856202517636956231488386586603116936243206073542662790844416 

noncomputable def Ns132p1188 := BSN.sin_dyadic_bound_f 101070366 67108864 4 3 67108864 33554432 Ns132p1185 Ns132p233 Ns132p1186 Ns132p1187 Ns132p236 Ns132p1186 66968318 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 101070366) qz359 0 3 Ns132p1185 Ns132p233 Ns132p1186 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 101070366) (BSN.sinOddQ 67108864) 0 3 Ns132p1187 Ns132p236 Ns132p1186 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1189 := Ns132p1140 38852 BSN.abs_quadSignPos (BSN.cos_quad_nat3 43 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 22429953 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 11 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66968318 67108864) qz158 rfl rfl (Ns132p1174 RS133to150.d9 RS133to150.d11 RS133to150.d13 RS133to150.d17 (Ns132p1178 rfl rfl) (Ns132p1182 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns132p1173 rfl) RS133to150.d19 RS133to150.d21 RS133to150.d23 RS133to150.d25 RS133to150.d17 (Ns132p1184 rfl rfl) (Ns132p1188 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns132p1190 := nat_lit 337054968568734840339372081 

noncomputable def Ns132p1191 := BSN.sin_dyadic_bound_f 4284747 67108864 2 1 67108864 33554432 Ns132p1190 Ns132p114 Ns132p1190 Ns132p1190 Ns132p115 Ns132p1190 4281836 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 4284747) qz359 0 1 Ns132p1190 Ns132p114 Ns132p1190 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 4284747) (BSN.sinOddQ 67108864) 0 1 Ns132p1190 Ns132p115 Ns132p1190 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1192 := nat_lit 74695825709492019494006250000 

noncomputable def Ns132p1193 := BSN.sin_dyadic_bound_f 16531950 67108864 2 1 67108864 33554432 Ns132p1192 Ns132p114 Ns132p1192 Ns132p1192 Ns132p115 Ns132p1192 16365247 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 16531950) qz359 0 1 Ns132p1192 Ns132p114 Ns132p1192 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 16531950) (BSN.sinOddQ 67108864) 0 1 Ns132p1192 Ns132p115 Ns132p1192 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1194 := Ns132p1138 52080 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 57 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 4281836 67108864) BSN.abs_quadSignPos qz655 (BSN.sfrac_eq_quadSignPos_mul Bool.false 16365247 67108864) qz158 rfl rfl (Ns132p1189 rfl rfl) (Ns132p1173 rfl) RS133to150.d27 RS133to150.d29 RS133to150.d31 RS133to150.d33 RS133to150.d17 (Ns132p1191 rfl rfl) (Ns132p1193 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns132p1195 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz155) qz155 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz155) qz155 7) 81896110 67108864 52080 67108864 81896110 67108864 52080 67108864 10991909816238080 40948055 16777216 3255 2097152 (Ns132p1194 rfl) 

noncomputable def Ns132p1196 := @Enclosure.Real.IsNear.mulLit_tf qz716 (Zeta.RiemannSiegel.correction qz157) 373959 1048576 1 4194304 22720621815045 35184372088832 3102122493729445 30091891625810722816 8496581013332413155 36893488147419103232 

noncomputable abbrev qz719 := (@HPow.hPow Real Real Real qz7 qz156 qz9)

noncomputable def Ns132p1197 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz719 1 1 0 1 373959 1048576 1 4194304 373959 1048576 1 4194304 

noncomputable def Ns132p1198 := @Enclosure.Real.IsNear.sqrt_image qz156 129638476989 2097152000 97101 2097152000 32977045 32977071 4194304 (@Enclosure.Real.IsNear.of_eq qz156 (@HMul.hMul Real Real Real qz5 qz155 qz3) Bool.false 129638476989 2097152000 97101 2097152000 (BSN.t_div_two_pi_mk qz155 388404 1000 qz158) (@Enclosure.Real.IsNear.mulLit_ff qz155 qz3 388404 1000 0 1 1335089 8388608 1 8388608 129638476989 2097152000 97101 2097152000 (Enclosure.Real.IsNear.const Bool.false 388404 1000) RS133to150.d36 rfl)) 

noncomputable abbrev qz889 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 388404 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz720 := qz889

noncomputable abbrev qz503 := qz720

noncomputable abbrev qz161 := qz503

noncomputable def Ns132p1199 := @Enclosure.Real.IsNear.sqrt_image qz161 16488529 2097152 13 4194304 11760771 11760777 4194304 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 65954116 8388608 26 8388608 16488529 2097152 13 4194304 (Ns132p1198 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns132p1200 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz161) 5880387 2097152 3 4194304 1495835 1495837 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz161) Bool.false 23521548 8388608 6 8388608 5880387 2097152 3 4194304 (Ns132p1199 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns132p1201 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 2991672 8388608 2 8388608 373959 1048576 1 4194304 (Ns132p1200 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz162 := (@HMul.hMul Real Real Real qz339 qz337 qz497)

noncomputable abbrev qz721 := (@HMul.hMul Real Real Real qz843 qz887 qz887)

noncomputable abbrev qz504 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz721 qz715) qz640)

noncomputable abbrev qz163 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz504))

noncomputable def Ns132p1202 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz157) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz162)) qz163) Bool.false 22720621815045 

noncomputable def Ns132p1203 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz162)) qz163 12931435 8388608 405 

noncomputable def Ns132p1204 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz162)) Bool.false 12931435 8388608 405 8388608 12931435 8388608 405 

noncomputable def Ns132p1205 := @Enclosure.Real.IsNear.recentre' (Real.cos qz162) Bool.false 5441681 8388608 290625398 14348932087808 5441681 8388608 145312699 7174466043904 

noncomputable def Ns132p1206 := @Enclosure.Real.IsNear.cos_image qz162 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 22725841) qz357) Bool.false 22725841 4194304 165 8388608 Bool.false 5441681 8388608 1 

noncomputable def Ns132p1207 := nat_lit 350818980348641783041039131 

noncomputable def Ns132p1208 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz157 884279719003555 140737488355328 1 500000000000000 1808465 2097152 13 4194304 1599188922027764093075 295147905179352825856 Ns132p1207 

noncomputable def Ns132p1209 := @Enclosure.Real.IsNear.subLit_ff_p qz161 qz1 16488529 2097152 13 4194304 7 1 0 1 1808465 1808465 2097152 13 

noncomputable def Ns132p1210 := @Ns132p1209 4194304 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 65954116 8388608 26 8388608 16488529 2097152 13 4194304 (Ns132p1198 rfl rfl rfl rfl rfl rfl) rfl) qz366 

noncomputable def Ns132p1211 := @Enclosure.Real.IsNear.recentre' qz162 Bool.false 1599188922027764093075 295147905179352825856 Ns132p1207 Ns132p153 22725841 4194304 165 8388608 (@Ns132p1208 Ns132p153 RS133to150.d35 (Ns132p1210 rfl rfl) rfl) 

noncomputable def Ns132p1212 := nat_lit 5697500361916749046229538303868581770540388784114310454788178594767274252129139752960 

noncomputable def Ns132p1213 := nat_lit 467708242001332198029574536147164952981600648312514399308261100385469918536073216 

noncomputable def Ns132p1214 := nat_lit 14921267515485388202280552437073475893872381366868783310655873420704141804279640948736 

noncomputable def Ns132p1215 := BSN.sin_dyadic_bound_f 12126818508 17179869184 3 2 8388608 3424393 Ns132p1212 Ns132p99 Ns132p1213 Ns132p1214 Ns132p102 Ns132p1213 5441681 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 12126818508) qz355 0 2 Ns132p1212 Ns132p99 Ns132p1213 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 12126818508) qz356 0 2 Ns132p1214 Ns132p102 Ns132p1213 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1216 := @Ns132p1206 1710526 (Ns132p1211 rfl) (Enclosure.sfrac_false_div 22725841 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 22725841) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 426674494669742661435392) qz358) 226375608064910080 72057594037927936 Bool.false 5441681 8388608 0 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 22725841 4194304 226375608064910080 72057594037927936 0 426674494669742661435392 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 5441681 8388608 426674494669742661435392 604462909807314587353088 12126818508 17179869184 3424393 3421052 (Ns132p1215 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p1217 := @Enclosure.Real.IsNear.inv_image (Real.cos qz162) 5441681 8388608 145312699 7174466043904 6465515 6465920 4194304 (Ns132p1205 (Ns132p1216 rfl rfl) rfl) rfl 

noncomputable def Ns132p1218 := @Enclosure.Real.IsNear.recentre' qz163 Bool.false 1757007 4194304 

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz339 qz337 qz504)

noncomputable def Ns132p1219 := @Enclosure.Real.IsNear.cos_image qz164 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 4775463)) qz357) Bool.true 4775463 4194304 

noncomputable def Ns132p1220 := nat_lit 704734010646154792432728445 

noncomputable def Ns132p1221 := nat_lit 4009221402056119056049365521845899 

noncomputable def Ns132p1222 := @Enclosure.Real.IsNear.recentre' qz164 Bool.true Ns132p1220 Ns132p1121 Ns132p1221 

noncomputable abbrev qz165 := qz504

noncomputable def Ns132p1223 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz165 884279719003555 140737488355328 1 500000000000000 796958242399 

noncomputable abbrev qz505 := (@HSub.hSub Real Real Real qz635 qz721 qz715)

noncomputable abbrev qz166 := qz505

noncomputable def Ns132p1224 := @Enclosure.Real.IsNear.subLit_tf qz166 qz27 522080335455 4398046511104 148566301 17592186044416 1 16 

noncomputable abbrev qz506 := qz721

noncomputable abbrev qz167 := qz506

noncomputable def Ns132p1225 := @Enclosure.Real.IsNear.subLit_ff_n qz167 qz157 3270545656225 4398046511104 94040349 17592186044416 1808465 2097152 13 4194304 

noncomputable def Ns132p1226 := @Enclosure.Real.IsNear.mulLit_ff qz157 qz157 1808465 2097152 13 4194304 1808465 2097152 13 4194304 3270545656225 4398046511104 

noncomputable def Ns132p1227 := nat_lit 270673057473153421875715789781437506816879108639106788801 

noncomputable def Ns132p1228 := nat_lit 270472973908283464457071182906430549605477630153321921 

noncomputable def Ns132p1229 := nat_lit 811478226471643698698233226978499659351426370657013722561 

noncomputable def Ns132p1230 := BSN.cos_dyadic_bound_f 4775463 4194304 3 2 4194304 1710526 Ns132p1227 Ns132p829 Ns132p1228 Ns132p1229 Ns132p832 Ns132p1228 1757007 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 4775463) (BSN.cosEvenQ 4194304) 0 2 Ns132p1227 Ns132p829 Ns132p1228 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 4775463) (BSN.cosOddQ 4194304) 0 2 Ns132p1229 Ns132p832 Ns132p1228 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1231 := @Ns132p1218 385641602 7174466043904 1757007 4194304 192820801 3587233021952 (@Ns132p1219 223 4194304 Bool.false 1757007 4194304 1 1710526 (@Ns132p1222 Ns132p174 4775463 4194304 223 4194304 (@Ns132p1223 4398046511104 148566301 17592186044416 Ns132p1220 Ns132p1121 Ns132p1221 Ns132p174 RS133to150.d35 (@Ns132p1224 0 1 12751331878384 796958242399 4398046511104 148566301 17592186044416 (@Ns132p1225 1094881819660124160 522080335455 4398046511104 148566301 17592186044416 (@Ns132p1226 94040349 17592186044416 (Ns132p1210 rfl rfl) (Ns132p1210 rfl rfl) rfl) (Ns132p1210 rfl rfl) rfl rfl) qz372 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 4775463 4194304) (BSN.cos_neg_of_bound 4775463 4194304 Bool.false 1757007 4194304 1 1710526 (Ns132p1230 rfl rfl)) rfl rfl) 

noncomputable def Ns132p1232 := @Ns132p1196 1164925427957043163075 Ns132p333 (Ns132p1197 qz29 (@Enclosure.Real.IsNear.of_eq qz719 (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 373959 1048576 1 4194304 (BSN.rpow_neg_quarter_mk qz156 (BSN.t_div_two_pi_nonneg qz155 388404 1000 qz158)) Ns132p1201) rfl) (@Ns132p1202 35184372088832 3102122493729445 30091891625810722816 (BSN.correction_mk qz157 (BSN.cos_two_pi_p_ne_zero_mk qz155 388404 1000 7 qz158 rfl rfl (@BSN.floor_sqrt_eq_dec qz155 388404 1000 7 qz158 rfl rfl rfl))) (@Ns132p1203 8388608 1757007 4194304 192820801 3587233021952 22720621815045 35184372088832 3102122493729445 30091891625810722816 (@Ns132p1204 8388608 (Ns132p1217 rfl rfl rfl rfl rfl) rfl) (Ns132p1231 rfl) rfl)) 

noncomputable def Ns132p1233 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz155) (hardyZApproximantRS₀ qz155) Bool.true 81549144201289938205 36893488147419103232 50139479048963994546115 Ns132p333 (@Eq.refl Real (hardyZApproximantRS₀ qz155)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz155) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz155) qz155 7) (@HMul.hMul Real Real Real qz5 qz716 (Zeta.RiemannSiegel.correction qz157))) Bool.true 81549144201289938205 36893488147419103232 50139479048963994546115 Ns132p333 (BSN.hardyZApproximantRS₀_eq qz155 7 (@BSN.floor_sqrt_eq_dec qz155 388404 1000 7 qz158 rfl rfl rfl)) (@Ns132p1136 81549144201289938205 36893488147419103232 50139479048963994546115 Ns132p333 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz155) qz155 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz155) qz155 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz155) qz155 7)) Bool.true 40948055 16777216 3255 2097152 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz155) qz155 7) (Ns132p1195 (Ns132p1194 rfl) rfl rfl)) (Ns132p1232 rfl) rfl rfl)) 

theorem RS133to150.d49 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz155) Bool.true 81549144201289938205 36893488147419103232 50139479048963994546115 Ns132p333 := Ns132p1233 

noncomputable def Ns132p1234 := nat_lit 1210241985727103756406882304 

noncomputable abbrev qz890 := (Enclosure.sfrac Bool.false 390688 1000)

noncomputable abbrev qz722 := qz890

noncomputable abbrev qz507 := qz722

noncomputable abbrev qz168 := qz507

noncomputable abbrev qz891 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 390688 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz723 := qz891

noncomputable abbrev qz508 := qz723

noncomputable abbrev qz169 := qz508

noncomputable abbrev qz892 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 390688 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz724 := qz892

noncomputable abbrev qz509 := qz724

noncomputable abbrev qz170 := qz509

noncomputable abbrev qz725 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz169 qz9))

noncomputable def Ns132p1235 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 7) (@HMul.hMul Real Real Real qz5 qz725 (Zeta.RiemannSiegel.correction qz170)) 7689653 2097152 26195 16777216 35977124440212611535 147573952589676412928 3959699575057074826263 Ns132p188 Ns132p1234 

noncomputable def Ns132p1236 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 390688 1000 56 94 67108864 33554432 1125899906842624 Bool.false 41006224871 1272 

noncomputable def Ns132p1237 := Ns132p1236 120242927 40 27397080 8 130587807 40 25364760 8 Bool.false 109119727 39084 Bool.true 68039797 Bool.true 103914705 3537118876014220 1 Bool.false 35472257 Bool.false Bool.false 1499527 Bool.true Bool.false 123034448 

noncomputable def Ns132p1238 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 390688 1000 44 11 67108864 33554432 1125899906842624 Bool.false 41006224871 1272 

noncomputable def Ns132p1239 := Ns132p1238 93032624 40 33554424 8 108007536 40 30011992 8 Bool.false 63673764 23056 Bool.false 21263354 Bool.true 31465426 3537118876014220 1 Bool.false 63768319 Bool.false Bool.false 30325137 Bool.false Bool.false 109119727 

noncomputable def Ns132p1240 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 390688 1000 216 115 67108864 33554432 1125899906842624 Bool.false 41006224871 1272 

noncomputable def Ns132p1241 := Ns132p1240 46516304 40 47453136 16 73726608 40 38745320 8 Bool.true 39968 1320 Bool.false 63361967 Bool.false 79472782 3537118876014220 1 Bool.false 39353839 Bool.false Bool.false 62157007 Bool.false Bool.false 63673764 

noncomputable def Ns132p1242 := nat_lit 2687848690861778982523955143547137292882594343258779 

noncomputable def Ns132p1243 := nat_lit 4398807078950118200707594707286391356057976832000 

noncomputable def Ns132p1244 := nat_lit 4369114232138748467922845040640000 

noncomputable def Ns132p1245 := nat_lit 10241770835011541379400516644321361920 

noncomputable abbrev qz893 := (@Eq.refl Real (Enclosure.sfrac Bool.false 390688 1000))

noncomputable abbrev qz726 := qz893

noncomputable abbrev qz510 := qz726

noncomputable abbrev qz171 := qz510

noncomputable def Ns132p1246 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz168 390688 1000 610549453376 16000000 781376 4000 2000 Ns132p1244 Ns132p1245 qz171 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns132p1247 := nat_lit 3523017036086350947973798485750103792527074057596146810880 

noncomputable abbrev qz511 := (Enclosure.sfrac Bool.false 390688 2000)

noncomputable abbrev qz727 := (Real.log (Enclosure.sfrac Bool.false 610549453376 16000000))

noncomputable abbrev qz172 := (@HSub.hSub Real Real Real qz342 (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 390688 4000) qz727) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 781376)))))) qz511)

noncomputable abbrev qz512 := (@HSub.hSub Real Real Real qz12 qz172 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 390688 2000) (Real.log Real.pi)))

noncomputable def Ns132p1248 := @Enclosure.Real.IsNear.addLit_ft_p qz512 (Enclosure.sfrac Bool.true Ns132p1244 Ns132p1245) 343985386163449961339 562949953421312000 103601144244433227431 Ns132p648 Ns132p1244 Ns132p1245 0 1 Ns132p1247 

noncomputable def Ns132p1249 := nat_lit 721389640563451413322006528000 

noncomputable abbrev qz513 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 390688 2000) (Real.log Real.pi))

noncomputable def Ns132p1250 := @Enclosure.Real.IsNear.subLit_ff_p qz172 qz513 469870067215721634683 562949953421312000 1245900250627124783 171052600000000000000000 468956981049 2097152000 12209 1048576000 Ns132p1249 343985386163449961339 562949953421312000 

noncomputable abbrev qz173 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 390688 4000) qz727) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 781376))))))

noncomputable def Ns132p1251 := @Enclosure.Real.IsNear.subLit_ff_p qz173 qz511 579838962916854406011 562949953421312000 1245900250627124783 171052600000000000000000 390688 2000 0 1 939740134431443269366000 469870067215721634683 562949953421312000 1245900250627124783 171052600000000000000000 

noncomputable def Ns132p1252 := nat_lit 1305681268663620175664644523953225728 

noncomputable def Ns132p1253 := nat_lit 12753594158646496040321024 

noncomputable def Ns132p1254 := nat_lit 224280369088724953635796876714764478983930882704133101380114718694813204480 

noncomputable def Ns132p1255 := nat_lit 433456370144966655449497451144777624981868469098277770763683775377309696 

noncomputable def Ns132p1256 := nat_lit 6180048530909286729372930625818844881235658199961089643498847600640 

noncomputable def Ns132p1257 := BSN.log_dyadic_bound 86261453376 1134837453376 4 3 Ns132p1254 33554432 13684208 Ns132p1255 Ns132p1256 5110948 1221098906752 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 86261453376) (BSN.artanhQ 1134837453376) 0 3 Ns132p1255 Ns132p1254 Ns132p1256 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns132p1258 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 390688 4000) qz727 390688 4000 0 1 47510840589726329 4503599627370496 12500002565789 171052600000000000000 580059852759968750761 562949953421312000 152612531325717901 21381575000000000000000 (Enclosure.Real.IsNear.const Bool.false 390688 4000) (BSN.isNear_log_sfrac 610549453376 16000000 47510840589726329 4503599627370496 12500002565789 171052600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 610549453376) qz350)) Bool.false Ns132p1253 Ns132p87 1000000205263120 13684208000000000000000 47510840589726329 4503599627370496 12500002565789 171052600000000000000 (BSN.log_rat_reduce_isNear 610549453376 16000000 15 1221098906752 1048576000000 5110948 33554432 24973259072661432 36028797018963968 13684208 1000000000000000 rfl rfl rfl rfl (Ns132p1257 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns132p1259 := BSN.arctan_dyadic_bound_f 1000 781376 1 0 4194304 1710526 0 1 1 0 1 1 5367 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 781376) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 781376) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz514 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 781376)))

noncomputable def Ns132p1260 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz514 884279719003555 562949953421312 1 2000000000000000 5367 4194304 1 1710526 3705916610135474569216 883559372457379 562949953421312 1000000000855263 1710526000000000000000 qz17 (Ns132p1259 rfl) rfl rfl 

noncomputable def Ns132p1261 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 390688 4000) qz727) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz514)) 580059852759968750761 562949953421312000 152612531325717901 21381575000000000000000 883559372457379 2251799813685248 1000000000855263 6842104000000000000000 Ns132p1252 579838962916854406011 562949953421312000 1245900250627124783 171052600000000000000000 (Ns132p1258 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz514) 1 4 0 1 883559372457379 562949953421312 1000000000855263 1710526000000000000000 883559372457379 2251799813685248 1000000000855263 6842104000000000000000 qz353 Ns132p1260 rfl) 

noncomputable def Ns132p1262 := @Ns132p1248 Ns132p1242 Ns132p1243 103601144244433227431 Ns132p648 (@Ns132p1250 103601144244433227431 Ns132p648 (Ns132p1251 (Ns132p1261 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 390688 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz511 (Real.log Real.pi) 390688 2000 0 1 38410761 33554432 1 16777216 468956981049 2097152000 12209 1048576000 (Enclosure.Real.IsNear.const Bool.false 390688 2000) RS133to150.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns132p1244 Ns132p1245) 

noncomputable def Ns132p1263 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz168) Bool.false Ns132p1242 Ns132p1243 103601144244433227431 Ns132p648 1281444527 2097152 5 262144 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz168) (@HAdd.hAdd Real Real Real qz354 qz512 (Enclosure.sfrac Bool.true Ns132p1244 Ns132p1245)) Bool.false Ns132p1242 Ns132p1243 103601144244433227431 Ns132p648 Ns132p1246 (Ns132p1262 rfl rfl)) 

noncomputable def Ns132p1264 := nat_lit 80737649360857812829839416718049919343904130898953354468722629287676486211773614469045924062913064293511381892520608087375687520256 

noncomputable def Ns132p1265 := nat_lit 149848430176071114398771339538561761068265955307409329463808447482412234033372073901768717225347217268702601332430354245554176 

noncomputable def Ns132p1266 := nat_lit 488626811057448812875095500547646708315740019843337703474118636249202366702987705731291930354701306720059514100047981380649686732800 

noncomputable def Ns132p1267 := BSN.cos_dyadic_bound_t 26996306474 17179869184 4 3 8388608 3424393 Ns132p1264 Ns132p274 Ns132p1265 Ns132p1266 Ns132p277 Ns132p1265 4996 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 26996306474) (BSN.cosEvenQ 17179869184) 0 3 Ns132p1264 Ns132p274 Ns132p1265 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 26996306474) (BSN.cosOddQ 17179869184) 0 3 Ns132p1266 Ns132p277 Ns132p1265 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1268 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz168) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1281444527) qz368) Bool.false 1281444527 2097152 5 262144 Bool.true 4996 8388608 1 1710526 (Ns132p1263 rfl) (Enclosure.sfrac_false_div 1281444527 2097152) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1281444527) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474924046018754027454464) qz453) 226375608064910080 72057594037927936 Bool.true 4996 8388608 97 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q0 1281444527 2097152 226375608064910080 72057594037927936 97 474924046018754027454464 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.true 4996 8388608 474924046018754027454464 302231454903657293676544 26996306474 17179869184 3424393 3421052 (Ns132p1267 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p1269 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz168) Bool.false Ns132p1242 Ns132p1243 103601144244433227431 Ns132p648 41006224871 67108864 1272 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz168) (@HAdd.hAdd Real Real Real qz354 qz512 (Enclosure.sfrac Bool.true Ns132p1244 Ns132p1245)) Bool.false Ns132p1242 Ns132p1243 103601144244433227431 Ns132p648 Ns132p1246 (Ns132p1262 rfl rfl)) 

noncomputable def Ns132p1270 := Ns132p1241 23056 BSN.abs_quadSignPos (BSN.cos_quad_nat0 216 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 39353839 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 115 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 62157007 67108864) qz171 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 1) Bool.true 1249 2097152 4407387 224202063872 39968 67108864 1320 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz168)) Bool.true 1249 2097152 4407387 224202063872 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz168) qz168) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz168)) Bool.true 4996 8388608 8814774 448404127744 1249 2097152 4407387 224202063872 (Ns132p1268 rfl rfl) rfl)) rfl) (Ns132p1269 rfl) RS133to150.d7 

noncomputable def Ns132p1271 := nat_lit 549476115071123853228565527719014537008448020132001457853767982721 

noncomputable def Ns132p1272 := nat_lit 259794054445044222550739683702309124152387999225239324947226241 

noncomputable def Ns132p1273 := nat_lit 1647908757104481471240595103789638992777039284397553894911409495681 

noncomputable def Ns132p1274 := BSN.cos_dyadic_bound_f 63361967 67108864 3 2 67108864 33554432 Ns132p1271 Ns132p124 Ns132p1272 Ns132p1273 Ns132p127 Ns132p1272 39353839 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 63361967) qz360 0 2 Ns132p1271 Ns132p124 Ns132p1272 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 63361967) (BSN.cosOddQ 67108864) 0 2 Ns132p1273 Ns132p127 Ns132p1272 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1275 := nat_lit 2448259047546471183667027866361473077485737373054943223376309960960 

noncomputable def Ns132p1276 := nat_lit 1591282653232996222005929182818929600846002768536648990247403776 

noncomputable def Ns132p1277 := nat_lit 6409530666897428249054206240841198840727942448756744343810887434496 

noncomputable def Ns132p1278 := BSN.sin_dyadic_bound_f 79472782 67108864 3 2 67108864 33554432 Ns132p1275 Ns132p108 Ns132p1276 Ns132p1277 Ns132p111 Ns132p1276 62157007 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 79472782) qz359 0 2 Ns132p1275 Ns132p108 Ns132p1276 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 79472782) (BSN.sinOddQ 67108864) 0 2 Ns132p1277 Ns132p111 Ns132p1276 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1279 := nat_lit 204421738847817162143385027856 

noncomputable def Ns132p1280 := BSN.cos_dyadic_bound_f 21263354 67108864 2 1 67108864 33554432 Ns132p1279 Ns132p135 Ns132p1279 Ns132p1279 Ns132p136 Ns132p1279 63768319 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 21263354) qz360 0 1 Ns132p1279 Ns132p135 Ns132p1279 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 21263354) (BSN.cosOddQ 67108864) 0 1 Ns132p1279 Ns132p136 Ns132p1279 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1281 := nat_lit 980244611389594368484080898576 

noncomputable def Ns132p1282 := BSN.sin_dyadic_bound_f 31465426 67108864 2 1 67108864 33554432 Ns132p1281 Ns132p114 Ns132p1281 Ns132p1281 Ns132p115 Ns132p1281 30325137 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 31465426) qz359 0 1 Ns132p1281 Ns132p114 Ns132p1281 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 31465426) (BSN.sinOddQ 67108864) 0 1 Ns132p1281 Ns132p115 Ns132p1281 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1283 := Ns132p1239 39084 BSN.abs_quadSignPos (BSN.cos_quad_nat0 44 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 63768319 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 11 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 30325137 67108864) qz171 rfl rfl (Ns132p1270 RS133to150.d9 RS133to150.d11 RS133to150.d13 RS133to150.d17 (Ns132p1274 rfl rfl) (Ns132p1278 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns132p1269 rfl) RS133to150.d19 RS133to150.d21 RS133to150.d23 RS133to150.d25 RS133to150.d17 (Ns132p1280 rfl rfl) (Ns132p1282 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns132p1284 := nat_lit 730724949118320557165315153415506049048319919447746998043593011041 

noncomputable def Ns132p1285 := nat_lit 459308067497431451825321456936097507609960984421645719064145761 

noncomputable def Ns132p1286 := nat_lit 2191256231219966808592294817332645952129739836374397702692650741601 

noncomputable def Ns132p1287 := BSN.cos_dyadic_bound_f 68039797 67108864 3 2 67108864 33554432 Ns132p1284 Ns132p124 Ns132p1285 Ns132p1286 Ns132p127 Ns132p1285 35472257 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 68039797) qz360 0 2 Ns132p1284 Ns132p124 Ns132p1285 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 68039797) (BSN.cosOddQ 67108864) 0 2 Ns132p1286 Ns132p127 Ns132p1285 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1288 := nat_lit 960632309314660222480214581283977600088321217168470732084381511965549510993723785139524976571771890625 

noncomputable def Ns132p1289 := nat_lit 1585346172813508796251359573588576265568069033528750715234913247526320230312045708679902587890625 

noncomputable def Ns132p1290 := nat_lit 5814578128197915417300067742777855399046336407891997067821978153136292184961670868884945926786837490625 

noncomputable def Ns132p1291 := BSN.cos_dyadic_bound_f 103914705 67108864 4 3 67108864 33554432 Ns132p1288 Ns132p118 Ns132p1289 Ns132p1290 Ns132p121 Ns132p1289 1499527 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 103914705) qz360 0 3 Ns132p1288 Ns132p118 Ns132p1289 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 103914705) (BSN.cosOddQ 67108864) 0 3 Ns132p1290 Ns132p121 Ns132p1289 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz728 := (BSN.cos_quad_nat2 94 rfl)

noncomputable def Ns132p1292 := Ns132p1237 52390 BSN.abs_quadSignPos (BSN.cos_quad_nat0 56 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 35472257 67108864) BSN.abs_quadSignNeg qz728 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 1499527 67108864) qz171 rfl rfl (Ns132p1283 rfl rfl) (Ns132p1269 rfl) RS133to150.d27 RS133to150.d29 RS133to150.d31 RS133to150.d33 RS133to150.d17 (Ns132p1287 rfl rfl) (Ns132p1291 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns132p1293 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 7) 123034448 67108864 52390 67108864 123034448 67108864 52390 67108864 16513404076294144 7689653 2097152 26195 16777216 (Ns132p1292 rfl) 

noncomputable def Ns132p1294 := @Enclosure.Real.IsNear.mulLit_tf qz725 (Zeta.RiemannSiegel.correction qz170) 1493645 4194304 1 4194304 24086797358283 35184372088832 2637237356433879 30091891625810722816 35977124440212611535 147573952589676412928 

noncomputable abbrev qz729 := (@HPow.hPow Real Real Real qz7 qz169 qz9)

noncomputable def Ns132p1295 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz729 1 1 0 1 1493645 4194304 1 4194304 1493645 4194304 1 4194304 

noncomputable def Ns132p1296 := @Enclosure.Real.IsNear.sqrt_image qz169 16300101601 262144000 12209 262144000 33073864 33073889 4194304 (@Enclosure.Real.IsNear.of_eq qz169 (@HMul.hMul Real Real Real qz5 qz168 qz3) Bool.false 16300101601 262144000 12209 262144000 (BSN.t_div_two_pi_mk qz168 390688 1000 qz171) (@Enclosure.Real.IsNear.mulLit_ff qz168 qz3 390688 1000 0 1 1335089 8388608 1 8388608 16300101601 262144000 12209 262144000 (Enclosure.Real.IsNear.const Bool.false 390688 1000) RS133to150.d36 rfl)) 

noncomputable abbrev qz894 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 390688 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz730 := qz894

noncomputable abbrev qz515 := qz730

noncomputable abbrev qz174 := qz515

noncomputable def Ns132p1297 := @Enclosure.Real.IsNear.sqrt_image qz174 66147753 8388608 25 8388608 11778023 11778029 4194304 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 66147753 8388608 25 8388608 66147753 8388608 25 8388608 (Ns132p1296 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns132p1298 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz174) 5889013 2097152 3 4194304 1493644 1493646 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz174) Bool.false 23556052 8388608 6 8388608 5889013 2097152 3 4194304 (Ns132p1297 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns132p1299 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz174)) Bool.false 2987290 8388608 2 8388608 1493645 4194304 1 4194304 (Ns132p1298 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz339 qz337 qz509)

noncomputable abbrev qz731 := (@HMul.hMul Real Real Real qz843 qz892 qz892)

noncomputable abbrev qz516 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz731 qz724) qz640)

noncomputable abbrev qz176 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz516))

noncomputable def Ns132p1300 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz170) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz175)) qz176) Bool.false 24086797358283 

noncomputable def Ns132p1301 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz175)) qz176 11156827 8388608 289 

noncomputable def Ns132p1302 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz175)) Bool.false 11156827 8388608 289 8388608 11156827 8388608 289 

noncomputable def Ns132p1303 := @Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.false 6307236 8388608 139325858 7174466043904 1576809 2097152 69662929 3587233021952 

noncomputable def Ns132p1304 := @Enclosure.Real.IsNear.cos_image qz175 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11667085) qz368) Bool.false 11667085 2097152 79 4194304 Bool.false 6307236 8388608 1 

noncomputable def Ns132p1305 := nat_lit 674651885289902849791500399 

noncomputable def Ns132p1306 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz170 884279719003555 140737488355328 1 500000000000000 7427497 8388608 25 8388608 6567984960059747751835 1180591620717411303424 Ns132p1305 

noncomputable def Ns132p1307 := @Enclosure.Real.IsNear.subLit_ff_p qz174 qz1 66147753 8388608 25 8388608 7 1 0 1 7427497 7427497 8388608 25 

noncomputable def Ns132p1308 := @Ns132p1307 8388608 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 66147753 8388608 25 8388608 66147753 8388608 25 8388608 (Ns132p1296 rfl rfl rfl rfl rfl rfl) rfl) qz366 

noncomputable def Ns132p1309 := @Enclosure.Real.IsNear.recentre' qz175 Bool.false 6567984960059747751835 1180591620717411303424 Ns132p1305 Ns132p405 11667085 2097152 79 4194304 (@Ns132p1306 Ns132p405 RS133to150.d35 (Ns132p1308 rfl rfl) rfl) 

noncomputable def Ns132p1310 := nat_lit 12032386685096064492104109222442666949334050518018804304959401905646729262812704604160 

noncomputable def Ns132p1311 := nat_lit 2085597988089770941945678258782762740711729625285444906413822828525179855259631616 

noncomputable def Ns132p1312 := nat_lit 31510017016604214040652374008264193727628027603989263411711858801638107301886663131136 

noncomputable def Ns132p1313 := BSN.sin_dyadic_bound_f 14618534092 17179869184 3 2 8388608 3424393 Ns132p1310 Ns132p99 Ns132p1311 Ns132p1312 Ns132p102 Ns132p1311 6307236 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 14618534092) qz355 0 2 Ns132p1310 Ns132p99 Ns132p1311 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 14618534092) qz356 0 2 Ns132p1312 Ns132p102 Ns132p1311 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1314 := @Ns132p1304 1710526 (Ns132p1309 rfl) (Enclosure.sfrac_false_div 11667085 2097152) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11667085) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 257171971458369994096640) qz453) 226375608064910080 72057594037927936 Bool.false 6307236 8388608 0 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 11667085 2097152 226375608064910080 72057594037927936 0 257171971458369994096640 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 6307236 8388608 257171971458369994096640 302231454903657293676544 14618534092 17179869184 3424393 3421052 (Ns132p1313 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p1315 := @Enclosure.Real.IsNear.inv_image (Real.cos qz175) 1576809 2097152 69662929 3587233021952 5578269 5578558 4194304 (Ns132p1303 (Ns132p1314 rfl rfl) rfl) rfl 

noncomputable def Ns132p1316 := @Enclosure.Real.IsNear.recentre' qz176 Bool.false 2158929 4194304 

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz339 qz337 qz516)

noncomputable def Ns132p1317 := @Enclosure.Real.IsNear.cos_image qz177 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8641147)) qz365) Bool.true 8641147 8388608 

noncomputable def Ns132p1318 := nat_lit 10201665925951594776636863405 

noncomputable def Ns132p1319 := nat_lit 15681356775141404938717160648717157 

noncomputable def Ns132p1320 := @Enclosure.Real.IsNear.recentre' qz177 Bool.true Ns132p1318 Ns132p285 Ns132p1319 

noncomputable abbrev qz178 := qz516

noncomputable def Ns132p1321 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz178 884279719003555 140737488355328 1 500000000000000 11536695580271 

noncomputable abbrev qz517 := (@HSub.hSub Real Real Real qz635 qz731 qz724)

noncomputable abbrev qz179 := qz517

noncomputable def Ns132p1322 := @Enclosure.Real.IsNear.subLit_tf qz179 qz27 7138649069167 70368744177664 581090675 70368744177664 1 16 

noncomputable abbrev qz518 := qz731

noncomputable abbrev qz180 := qz518

noncomputable def Ns132p1323 := @Enclosure.Real.IsNear.subLit_ff_n qz180 qz170 55167711685009 70368744177664 371375475 70368744177664 7427497 8388608 25 8388608 

noncomputable def Ns132p1324 := @Enclosure.Real.IsNear.mulLit_ff qz170 qz170 7427497 8388608 25 8388608 7427497 8388608 25 8388608 55167711685009 70368744177664 

noncomputable def Ns132p1325 := nat_lit 46413618767174624271820266835997980573271332337621807247841 

noncomputable def Ns132p1326 := nat_lit 31086451187058754367478268220658851802487458476543816161 

noncomputable def Ns132p1327 := nat_lit 139178683399149755306725843971552624016209022095912334111201 

noncomputable def Ns132p1328 := BSN.cos_dyadic_bound_f 8641147 8388608 3 2 4194304 1710526 Ns132p1325 Ns132p929 Ns132p1326 Ns132p1327 Ns132p932 Ns132p1326 2158929 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 8641147) (BSN.cosEvenQ 8388608) 0 2 Ns132p1325 Ns132p929 Ns132p1326 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 8641147) (BSN.cosOddQ 8388608) 0 2 Ns132p1327 Ns132p932 Ns132p1326 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1329 := @Ns132p1316 188544486 3587233021952 2158929 4194304 94272243 1793616510976 (@Ns132p1317 109 2097152 Bool.false 2158929 4194304 1 1710526 (@Ns132p1320 Ns132p288 8641147 8388608 109 2097152 (@Ns132p1321 70368744177664 581090675 70368744177664 Ns132p1318 Ns132p285 Ns132p1319 Ns132p288 RS133to150.d35 (@Ns132p1322 0 1 184587129284336 11536695580271 70368744177664 581090675 70368744177664 (@Ns132p1323 59883328690806849536 7138649069167 70368744177664 581090675 70368744177664 (@Ns132p1324 371375475 70368744177664 (Ns132p1308 rfl rfl) (Ns132p1308 rfl rfl) rfl) (Ns132p1308 rfl rfl) rfl rfl) qz372 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 8641147 8388608) (BSN.cos_neg_of_bound 8641147 8388608 Bool.false 2158929 4194304 1 1710526 (Ns132p1328 rfl rfl)) rfl rfl) 

noncomputable def Ns132p1330 := @Ns132p1294 3959699575057074826263 Ns132p188 (Ns132p1295 qz29 (@Enclosure.Real.IsNear.of_eq qz729 (@Inv.inv Real Real.instInv (Real.sqrt qz174)) Bool.false 1493645 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz169 (BSN.t_div_two_pi_nonneg qz168 390688 1000 qz171)) Ns132p1299) rfl) (@Ns132p1300 35184372088832 2637237356433879 30091891625810722816 (BSN.correction_mk qz170 (BSN.cos_two_pi_p_ne_zero_mk qz168 390688 1000 7 qz171 rfl rfl (@BSN.floor_sqrt_eq_dec qz168 390688 1000 7 qz171 rfl rfl rfl))) (@Ns132p1301 8388608 2158929 4194304 94272243 1793616510976 24086797358283 35184372088832 2637237356433879 30091891625810722816 (@Ns132p1302 8388608 (Ns132p1315 rfl rfl rfl rfl rfl) rfl) (Ns132p1329 rfl) rfl)) 

noncomputable def Ns132p1331 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz168) (hardyZApproximantRS₀ qz168) Bool.false 577088349212219122127 147573952589676412928 201023974859585045867543 Ns132p188 (@Eq.refl Real (hardyZApproximantRS₀ qz168)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz168) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 7) (@HMul.hMul Real Real Real qz5 qz725 (Zeta.RiemannSiegel.correction qz170))) Bool.false 577088349212219122127 147573952589676412928 201023974859585045867543 Ns132p188 (BSN.hardyZApproximantRS₀_eq qz168 7 (@BSN.floor_sqrt_eq_dec qz168 390688 1000 7 qz171 rfl rfl rfl)) (@Ns132p1235 577088349212219122127 147573952589676412928 201023974859585045867543 Ns132p188 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 7)) Bool.false 7689653 2097152 26195 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz168) qz168 7) (Ns132p1293 (Ns132p1292 rfl) rfl rfl)) (Ns132p1330 rfl) rfl rfl)) 

theorem RS133to150.d50 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz168) Bool.false 577088349212219122127 147573952589676412928 201023974859585045867543 Ns132p188 := Ns132p1331 

noncomputable def Ns132p1332 := nat_lit 15776817676713052243755008 

noncomputable def Ns132p1333 := nat_lit 147028647179389452819628032 

noncomputable abbrev qz895 := (Enclosure.sfrac Bool.false 391923 1000)

noncomputable abbrev qz732 := qz895

noncomputable abbrev qz519 := qz732

noncomputable abbrev qz181 := qz519

noncomputable abbrev qz896 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 391923 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz733 := qz896

noncomputable abbrev qz520 := qz733

noncomputable abbrev qz182 := qz520

noncomputable abbrev qz897 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 391923 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz734 := qz897

noncomputable abbrev qz521 := qz734

noncomputable abbrev qz183 := qz521

noncomputable abbrev qz735 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz182 qz9))

noncomputable def Ns132p1334 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz181) qz181 7) (@HMul.hMul Real Real Real qz5 qz735 (Zeta.RiemannSiegel.correction qz183)) 24380613 33554432 13139 8388608 2319896727984803121 9223372036854775808 488083297088853323379 Ns132p1332 Ns132p1333 

noncomputable def Ns132p1335 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz181) qz181 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 391923 1000 56 94 67108864 33554432 1125899906842624 Bool.false 41177437831 1275 

noncomputable def Ns132p1336 := Ns132p1335 120242927 40 27397080 8 130587807 40 25364760 8 Bool.true 41460704 39208 Bool.true 45326851 Bool.true 93977687 3537118876014220 1 Bool.false 52374624 Bool.false Bool.false 11381391 Bool.true Bool.true 24380613 

noncomputable def Ns132p1337 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz181) qz181 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 391923 1000 44 10 67108864 33554432 1125899906842624 Bool.false 41177437831 1275 

noncomputable def Ns132p1338 := Ns132p1337 93032624 40 33554424 8 108007536 40 30011992 8 Bool.true 52142568 23131 Bool.false 77581024 Bool.true 99056130 3537118876014220 1 Bool.false 27042201 Bool.false Bool.false 6348718 Bool.true Bool.true 41460704 

noncomputable def Ns132p1339 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz181) qz181 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 391923 1000 217 116 67108864 33554432 1125899906842624 Bool.false 41177437831 1275 

noncomputable def Ns132p1340 := Ns132p1339 46516304 40 47453136 16 73726608 40 38745320 8 Bool.true 37321424 1328 Bool.false 71712934 Bool.false 54219024 3537118876014220 1 Bool.false 58822956 Bool.true Bool.false 46372145 Bool.false Bool.true 52142568 

noncomputable def Ns132p1341 := nat_lit 8011905528818956420946731080294587744833197396186462007 

noncomputable def Ns132p1342 := nat_lit 13057390329116140255119017741955077530546628408115200 

noncomputable def Ns132p1343 := nat_lit 4438607902326162975534084404640000 

noncomputable def Ns132p1344 := nat_lit 10437563077129864401377471210494336320 

noncomputable abbrev qz522 := (@Eq.refl Real qz732)

noncomputable abbrev qz184 := qz522

noncomputable def Ns132p1345 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz181 391923 1000 614415551716 16000000 783846 4000 2000 Ns132p1343 Ns132p1344 qz184 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns132p1346 := nat_lit 23074287922998594492326585511248412705119608501017010580160 

noncomputable abbrev qz523 := (Enclosure.sfrac Bool.false 391923 2000)

noncomputable abbrev qz736 := (Real.log (Enclosure.sfrac Bool.false 614415551716 16000000))

noncomputable abbrev qz185 := (@HSub.hSub Real Real Real qz342 (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 391923 4000) qz736) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 783846)))))) qz523)

noncomputable abbrev qz524 := (@HSub.hSub Real Real Real qz12 qz185 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 391923 2000) (Real.log Real.pi)))

noncomputable def Ns132p1347 := @Enclosure.Real.IsNear.addLit_ft_p qz524 (Enclosure.sfrac Bool.true Ns132p1343 Ns132p1344) 2210698392360174805663 3602879701896396800 3325635453821783831157 Ns132p199 Ns132p1343 Ns132p1344 0 1 Ns132p1346 

noncomputable def Ns132p1348 := nat_lit 741787288789588050247323484160000 

noncomputable abbrev qz525 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 391923 2000) (Real.log Real.pi))

noncomputable def Ns132p1349 := @Enclosure.Real.IsNear.subLit_ff_p qz185 qz525 15094535606001829965083 18014398509481984000 4999038505677248547 684210400000000000000000 15054060683403 67108864000 391923 33554432000 Ns132p1348 2210698392360174805663 3602879701896396800 

noncomputable def Ns132p1350 := nat_lit 30189071212003659930166000 

noncomputable abbrev qz186 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 391923 4000) qz736) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 783846))))))

noncomputable def Ns132p1351 := @Enclosure.Real.IsNear.subLit_ff_p qz186 qz523 18624664159517683772699 18014398509481984000 4999038505677248547 684210400000000000000000 391923 2000 0 1 Ns132p1350 15094535606001829965083 18014398509481984000 4999038505677248547 684210400000000000000000 

noncomputable def Ns132p1352 := nat_lit 41939015284352236355537916475161444352 

noncomputable def Ns132p1353 := nat_lit 12761225165941503665635328 

noncomputable def Ns132p1354 := nat_lit 228903983526345149211557330885270156031334436834599985172898326349298503680 

noncomputable def Ns132p1355 := nat_lit 479802515146621524058296862967806574196809174317067166189024194848321536 

noncomputable def Ns132p1356 := nat_lit 8039641839374984748542635779078728029900490670673126612510059786240 

noncomputable def Ns132p1357 := BSN.log_dyadic_bound 90127551716 1138703551716 4 3 Ns132p1354 33554432 13684208 Ns132p1355 Ns132p1356 5322751 1228831103432 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 90127551716) (BSN.artanhQ 1138703551716) 0 3 Ns132p1355 Ns132p1354 Ns132p1356 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns132p1358 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 391923 4000) qz736 391923 4000 0 1 47539268307169913 4503599627370496 12500002565789 171052600000000000000 18631732652750953812699 18014398509481984000 4899038505591722247 684210400000000000000000 (Enclosure.Real.IsNear.const Bool.false 391923 4000) (BSN.isNear_log_sfrac 614415551716 16000000 47539268307169913 4503599627370496 12500002565789 171052600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 614415551716) qz350)) Bool.false Ns132p1353 Ns132p87 1000000205263120 13684208000000000000000 47539268307169913 4503599627370496 12500002565789 171052600000000000000 (BSN.log_rat_reduce_isNear 614415551716 16000000 15 1228831103432 1048576000000 5322751 33554432 24973259072661432 36028797018963968 13684208 1000000000000000 rfl rfl rfl rfl (Ns132p1357 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns132p1359 := BSN.arctan_dyadic_bound_f 1000 783846 1 0 4194304 1710526 0 1 1 0 1 1 5350 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 783846) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 783846) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz526 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 783846)))

noncomputable def Ns132p1360 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz526 884279719003555 562949953421312 1 2000000000000000 5350 4194304 1 1710526 3705926180284682731520 883561654158755 562949953421312 1000000000855263 1710526000000000000000 qz17 (Ns132p1359 rfl) rfl rfl 

noncomputable def Ns132p1361 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 391923 4000) qz736) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz526)) 18631732652750953812699 18014398509481984000 4899038505591722247 684210400000000000000000 883561654158755 2251799813685248 1000000000855263 6842104000000000000000 Ns132p1352 18624664159517683772699 18014398509481984000 4999038505677248547 684210400000000000000000 (Ns132p1358 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz526) 1 4 0 1 883561654158755 562949953421312 1000000000855263 1710526000000000000000 883561654158755 2251799813685248 1000000000855263 6842104000000000000000 qz353 Ns132p1360 rfl) 

noncomputable def Ns132p1362 := @Ns132p1347 Ns132p1341 Ns132p1342 3325635453821783831157 Ns132p199 (@Ns132p1349 3325635453821783831157 Ns132p199 (Ns132p1351 (Ns132p1361 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 391923 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz523 (Real.log Real.pi) 391923 2000 0 1 38410761 33554432 1 16777216 15054060683403 67108864000 391923 33554432000 (Enclosure.Real.IsNear.const Bool.false 391923 2000) RS133to150.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns132p1343 Ns132p1344) 

noncomputable def Ns132p1363 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz181) Bool.false Ns132p1341 Ns132p1342 3325635453821783831157 Ns132p199 321698733 524288 161 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz181) (@HAdd.hAdd Real Real Real qz354 qz524 (Enclosure.sfrac Bool.true Ns132p1343 Ns132p1344)) Bool.false Ns132p1341 Ns132p1342 3325635453821783831157 Ns132p199 Ns132p1345 (Ns132p1362 rfl rfl)) 

noncomputable def Ns132p1364 := nat_lit 11817061008138958297778893896147053690498141187419754668843889103197307330974267211776 

noncomputable def Ns132p1365 := nat_lit 6512724914628339713791292280749166229602180025762041419747651314752388603362410496 

noncomputable def Ns132p1366 := nat_lit 35438157574587618213909099103879662739035219202207739923692172006962417215716076814336 

noncomputable def Ns132p1367 := BSN.cos_dyadic_bound_f 16854673416 17179869184 3 2 8388608 3424393 Ns132p1364 Ns132p160 Ns132p1365 Ns132p1366 Ns132p163 Ns132p1365 4665178 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 16854673416) (BSN.cosEvenQ 17179869184) 0 2 Ns132p1364 Ns132p160 Ns132p1365 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 16854673416) (BSN.cosOddQ 17179869184) 0 2 Ns132p1366 Ns132p163 Ns132p1365 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1368 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz181) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 321698733) (@Nat.cast Real Real.instNatCast 524288)) Bool.false 321698733 524288 161 8388608 Bool.true 4665178 8388608 1 1710526 (Ns132p1363 rfl) (Enclosure.sfrac_false_div 321698733 524288) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 321698733) (@Nat.cast Real Real.instNatCast 524288)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 74127637616667264024576) (@Nat.cast Real Real.instNatCast 75557863725914323419136)) 226375608064910080 72057594037927936 Bool.false 4665178 8388608 97 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q2 321698733 524288 226375608064910080 72057594037927936 97 74127637616667264024576 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 4665178 8388608 74127637616667264024576 75557863725914323419136 16854673416 17179869184 3424393 3421052 (Ns132p1367 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p1369 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz181) Bool.false Ns132p1341 Ns132p1342 3325635453821783831157 Ns132p199 41177437831 67108864 1275 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz181) (@HAdd.hAdd Real Real Real qz354 qz524 (Enclosure.sfrac Bool.true Ns132p1343 Ns132p1344)) Bool.false Ns132p1341 Ns132p1342 3325635453821783831157 Ns132p199 Ns132p1345 (Ns132p1362 rfl rfl)) 

noncomputable def Ns132p1370 := Ns132p1340 23131 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 217 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 58822956 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 116 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 46372145 67108864) qz184 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz181) qz181 1) Bool.true 2332589 4194304 141891647 7174466043904 37321424 67108864 1328 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz181) qz181 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz181)) Bool.true 2332589 4194304 141891647 7174466043904 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz181) qz181) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz181)) Bool.true 4665178 8388608 283783294 14348932087808 2332589 4194304 141891647 7174466043904 (Ns132p1368 rfl rfl) rfl)) rfl) (Ns132p1369 rfl) RS133to150.d7 

noncomputable def Ns132p1371 := nat_lit 1622850570008867719024191706812222341908503366472111981955657048320 

noncomputable def Ns132p1372 := nat_lit 699487454434175008615614965189108889096196468009593727286845696 

noncomputable def Ns132p1373 := nat_lit 4249190417954141076001791093612180909654210213145420610515875471616 

noncomputable def Ns132p1374 := BSN.sin_dyadic_bound_f 71712934 67108864 3 2 67108864 33554432 Ns132p1371 Ns132p108 Ns132p1372 Ns132p1373 Ns132p111 Ns132p1372 58822956 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 71712934) qz359 0 2 Ns132p1371 Ns132p108 Ns132p1372 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 71712934) (BSN.sinOddQ 67108864) 0 2 Ns132p1373 Ns132p111 Ns132p1372 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1375 := nat_lit 294540990791342622814797435408861892901402906367965874037305901056 

noncomputable def Ns132p1376 := nat_lit 74681591504819723874014114542862984231518398250675709386162176 

noncomputable def Ns132p1377 := nat_lit 883473609191018228996644277997499952735745682307396270693145378816 

noncomputable def Ns132p1378 := BSN.cos_dyadic_bound_f 54219024 67108864 3 2 67108864 33554432 Ns132p1375 Ns132p124 Ns132p1376 Ns132p1377 Ns132p127 Ns132p1376 46372145 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 54219024) qz360 0 2 Ns132p1375 Ns132p124 Ns132p1376 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 54219024) (BSN.cosOddQ 67108864) 0 2 Ns132p1377 Ns132p127 Ns132p1376 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1379 := nat_lit 297747685134676818437586291718824508435731913236189070371534907863306608945461093407855958822859309056 

noncomputable def Ns132p1380 := nat_lit 47540756825115680343618356829264078210859916320797058717263897514613740554448878098967823384576 

noncomputable def Ns132p1381 := nat_lit 1805056808727573202423474680724178729646668106452511638343059464008751722646531500722540971567265873920 

noncomputable def Ns132p1382 := BSN.cos_dyadic_bound_f 77581024 67108864 4 3 67108864 33554432 Ns132p1379 Ns132p118 Ns132p1380 Ns132p1381 Ns132p121 Ns132p1380 27042201 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 77581024) qz360 0 3 Ns132p1379 Ns132p118 Ns132p1380 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 77581024) (BSN.cosOddQ 67108864) 0 3 Ns132p1381 Ns132p121 Ns132p1380 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1383 := nat_lit 792713233406731529376839737390200804144143515064252926205694627409758641675585381175286599994944000000 

noncomputable def Ns132p1384 := nat_lit 892434353194288204268811273143715906526474498352328232933379939378698782728426248881000000000000 

noncomputable def Ns132p1385 := nat_lit 4800089142572554635476695611178935115556372361175052758340800847231649301898774741871498588383193600000 

noncomputable def Ns132p1386 := BSN.cos_dyadic_bound_f 99056130 67108864 4 3 67108864 33554432 Ns132p1383 Ns132p118 Ns132p1384 Ns132p1385 Ns132p121 Ns132p1384 6348718 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 99056130) qz360 0 3 Ns132p1383 Ns132p118 Ns132p1384 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 99056130) (BSN.cosOddQ 67108864) 0 3 Ns132p1385 Ns132p121 Ns132p1384 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1387 := Ns132p1338 39208 BSN.abs_quadSignPos (BSN.cos_quad_nat0 44 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 27042201 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 10 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 6348718 67108864) qz184 rfl rfl (Ns132p1370 RS133to150.d9 RS133to150.d11 RS133to150.d13 RS133to150.d17 (Ns132p1374 rfl rfl) (Ns132p1378 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns132p1369 rfl) RS133to150.d19 RS133to150.d21 RS133to150.d23 RS133to150.d25 RS133to150.d17 (Ns132p1382 rfl rfl) (Ns132p1386 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns132p1388 := nat_lit 143848328579912433102261495887013551381520216562510918844193163681 

noncomputable def Ns132p1389 := nat_lit 17817402311356224941013815342022418081333250192145044636944801 

noncomputable def Ns132p1390 := nat_lit 431509350935114586856902460030356609308397983187148466443305601441 

noncomputable def Ns132p1391 := BSN.cos_dyadic_bound_f 45326851 67108864 3 2 67108864 33554432 Ns132p1388 Ns132p124 Ns132p1389 Ns132p1390 Ns132p127 Ns132p1389 52374624 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 45326851) qz360 0 2 Ns132p1388 Ns132p124 Ns132p1389 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 45326851) (BSN.cosOddQ 67108864) 0 2 Ns132p1390 Ns132p127 Ns132p1389 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1392 := nat_lit 641884914059086697489181099797336702615675050346749579917221171325411128342147745914579841064995569761 

noncomputable def Ns132p1393 := nat_lit 474566439444729490920869105452896362830064828003587204443465827464775278516194327026186601283681 

noncomputable def Ns132p1394 := nat_lit 3888170251464489587260585703507997368716192313568087483559752818026461794544634913906166889203515179105 

noncomputable def Ns132p1395 := BSN.cos_dyadic_bound_f 93977687 67108864 4 3 67108864 33554432 Ns132p1392 Ns132p118 Ns132p1393 Ns132p1394 Ns132p121 Ns132p1393 11381391 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 93977687) qz360 0 3 Ns132p1392 Ns132p118 Ns132p1393 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 93977687) (BSN.cosOddQ 67108864) 0 3 Ns132p1394 Ns132p121 Ns132p1393 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1396 := Ns132p1336 52556 BSN.abs_quadSignPos (BSN.cos_quad_nat0 56 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 52374624 67108864) BSN.abs_quadSignNeg qz728 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 11381391 67108864) qz184 rfl rfl (Ns132p1387 rfl rfl) (Ns132p1369 rfl) RS133to150.d27 RS133to150.d29 RS133to150.d31 RS133to150.d33 RS133to150.d17 (Ns132p1391 rfl rfl) (Ns132p1395 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns132p1397 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz181) qz181 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz181) qz181 7) 24380613 67108864 52556 67108864 24380613 67108864 52556 67108864 3272310484107264 24380613 33554432 13139 8388608 (Ns132p1396 rfl) 

noncomputable def Ns132p1398 := @Enclosure.Real.IsNear.mulLit_tf qz735 (Zeta.RiemannSiegel.correction qz183) 2984933 8388608 1 8388608 777202278237 1099511627776 326140458974751 3761486453226340352 2319896727984803121 9223372036854775808 

noncomputable abbrev qz737 := (@HPow.hPow Real Real Real qz7 qz182 qz9)

noncomputable def Ns132p1399 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz737 1 1 0 1 2984933 8388608 1 8388608 2984933 8388608 1 8388608 

noncomputable def Ns132p1400 := @Enclosure.Real.IsNear.sqrt_image qz182 523252086147 8388608000 391923 8388608000 33126097 33126123 4194304 (@Enclosure.Real.IsNear.of_eq qz182 (@HMul.hMul Real Real Real qz5 qz181 qz3) Bool.false 523252086147 8388608000 391923 8388608000 (BSN.t_div_two_pi_mk qz181 391923 1000 qz184) (@Enclosure.Real.IsNear.mulLit_ff qz181 qz3 391923 1000 0 1 1335089 8388608 1 8388608 523252086147 8388608000 391923 8388608000 (Enclosure.Real.IsNear.const Bool.false 391923 1000) RS133to150.d36 rfl)) 

noncomputable abbrev qz898 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 391923 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz738 := qz898

noncomputable abbrev qz527 := qz738

noncomputable abbrev qz187 := qz527

noncomputable def Ns132p1401 := @Enclosure.Real.IsNear.sqrt_image qz187 16563055 2097152 13 4194304 11787320 11787325 4194304 (@Enclosure.Real.IsNear.recentre' qz187 Bool.false 66252220 8388608 26 8388608 16563055 2097152 13 4194304 (Ns132p1400 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns132p1402 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz187) 23574645 8388608 5 8388608 1492466 1492467 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz187) Bool.false 23574645 8388608 5 8388608 23574645 8388608 5 8388608 (Ns132p1401 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns132p1403 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz187)) Bool.false 2984933 8388608 1 8388608 2984933 8388608 1 8388608 (Ns132p1402 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz188 := (@HMul.hMul Real Real Real qz339 qz337 qz521)

noncomputable abbrev qz739 := (@HMul.hMul Real Real Real qz843 qz897 qz897)

noncomputable abbrev qz528 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz739 qz734) qz640)

noncomputable abbrev qz189 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz528))

noncomputable def Ns132p1404 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz183) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz188)) qz189) Bool.false 777202278237 

noncomputable def Ns132p1405 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz188)) qz189 654447 524288 33 

noncomputable def Ns132p1406 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz188)) Bool.false 10471152 8388608 264 8388608 654447 524288 33 

noncomputable def Ns132p1407 := @Enclosure.Real.IsNear.recentre' (Real.cos qz188) Bool.false 6720249 8388608 72228718 3587233021952 6720249 8388608 36114359 1793616510976 

noncomputable def Ns132p1408 := @Enclosure.Real.IsNear.cos_image qz188 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 47324725) qz365) Bool.false 47324725 8388608 41 2097152 Bool.false 6720249 8388608 1 

noncomputable def Ns132p1409 := nat_lit 70163796069984425994369183 

noncomputable def Ns132p1410 := nat_lit 3602879701896396800000000000000 

noncomputable def Ns132p1411 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz183 884279719003555 140737488355328 1 500000000000000 1882991 2097152 13 4194304 1665090752366223033005 295147905179352825856 Ns132p1409 

noncomputable def Ns132p1412 := @Enclosure.Real.IsNear.subLit_ff_p qz187 qz1 16563055 2097152 13 4194304 7 1 0 1 1882991 1882991 2097152 13 

noncomputable def Ns132p1413 := @Ns132p1412 4194304 (@Enclosure.Real.IsNear.recentre' qz187 Bool.false 66252220 8388608 26 8388608 16563055 2097152 13 4194304 (Ns132p1400 rfl rfl rfl rfl rfl rfl) rfl) qz366 

noncomputable def Ns132p1414 := @Enclosure.Real.IsNear.recentre' qz188 Bool.false 1665090752366223033005 295147905179352825856 Ns132p1409 Ns132p1410 47324725 8388608 41 2097152 (@Ns132p1411 Ns132p1410 RS133to150.d35 (Ns132p1413 rfl rfl) rfl) 

noncomputable def Ns132p1415 := nat_lit 17108253131749506729757795459879292315084341094424785918187637928509927002793347973120 

noncomputable def Ns132p1416 := nat_lit 4215750302046240958814738985428451605661743207930097256406658529935645292835700736 

noncomputable def Ns132p1417 := nat_lit 44800504130283490378289478531802690951192679091633028675885821889429913010175129747456 

noncomputable def Ns132p1418 := BSN.sin_dyadic_bound_f 15962810572 17179869184 3 2 8388608 3424393 Ns132p1415 Ns132p99 Ns132p1416 Ns132p1417 Ns132p102 Ns132p1416 6720249 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 15962810572) qz355 0 2 Ns132p1415 Ns132p99 Ns132p1416 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 15962810572) qz356 0 2 Ns132p1417 Ns132p102 Ns132p1416 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1419 := @Ns132p1408 1710526 (Ns132p1414 rfl) (Enclosure.sfrac_false_div 47324725 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 47324725) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1123282933558650632929280) qz367) 226375608064910080 72057594037927936 Bool.false 6720249 8388608 0 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 47324725 8388608 226375608064910080 72057594037927936 0 1123282933558650632929280 Ns132p87 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 6720249 8388608 1123282933558650632929280 Ns132p87 15962810572 17179869184 3424393 3421052 (Ns132p1418 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p1420 := @Enclosure.Real.IsNear.inv_image (Real.cos qz188) 6720249 8388608 36114359 1793616510976 5235444 5235708 4194304 (Ns132p1407 (Ns132p1419 rfl rfl) rfl) rfl 

noncomputable def Ns132p1421 := @Enclosure.Real.IsNear.recentre' qz189 Bool.false 2375142 4194304 

noncomputable abbrev qz190 := (@HMul.hMul Real Real Real qz339 qz337 qz528)

noncomputable def Ns132p1422 := @Enclosure.Real.IsNear.cos_image qz190 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8126995)) qz365) Bool.true 8126995 8388608 

noncomputable def Ns132p1423 := nat_lit 599666458930228350666569725 

noncomputable def Ns132p1424 := nat_lit 4113801943360626191225799530530611 

noncomputable def Ns132p1425 := @Enclosure.Real.IsNear.recentre' qz190 Bool.true Ns132p1423 Ns132p1121 Ns132p1424 

noncomputable abbrev qz191 := qz528

noncomputable def Ns132p1426 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz191 884279719003555 140737488355328 1 500000000000000 678141142495 

noncomputable abbrev qz529 := (@HSub.hSub Real Real Real qz635 qz739 qz734)

noncomputable abbrev qz192 := qz529

noncomputable def Ns132p1427 := @Enclosure.Real.IsNear.subLit_tf qz192 qz27 403263235551 4398046511104 152441653 17592186044416 1 16 

noncomputable abbrev qz530 := qz739

noncomputable abbrev qz193 := qz530

noncomputable def Ns132p1428 := @Enclosure.Real.IsNear.subLit_ff_n qz193 qz183 3545655106081 4398046511104 97915701 17592186044416 1882991 2097152 13 4194304 

noncomputable def Ns132p1429 := @Enclosure.Real.IsNear.mulLit_ff qz183 qz183 1882991 2097152 13 4194304 1882991 2097152 13 4194304 3545655106081 4398046511104 

noncomputable def Ns132p1430 := nat_lit 36309187550684881587892960081191716944394763869062586190625 

noncomputable def Ns132p1431 := nat_lit 19030050487214717492034764321360678707672776358125390625 

noncomputable def Ns132p1432 := nat_lit 108889502551080215328694810714932429475768946054471507790625 

noncomputable def Ns132p1433 := BSN.cos_dyadic_bound_f 8126995 8388608 3 2 4194304 1710526 Ns132p1430 Ns132p929 Ns132p1431 Ns132p1432 Ns132p932 Ns132p1431 2375142 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 8126995) (BSN.cosEvenQ 8388608) 0 2 Ns132p1430 Ns132p929 Ns132p1431 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 8126995) (BSN.cosOddQ 8388608) 0 2 Ns132p1432 Ns132p932 Ns132p1431 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1434 := @Ns132p1421 395904758 7174466043904 1187571 2097152 197952379 3587233021952 (@Ns132p1422 229 4194304 Bool.false 2375142 4194304 1 1710526 (@Ns132p1425 Ns132p174 8126995 8388608 229 4194304 (@Ns132p1426 4398046511104 152441653 17592186044416 Ns132p1423 Ns132p1121 Ns132p1424 Ns132p174 RS133to150.d35 (@Ns132p1427 0 1 10850258279920 678141142495 4398046511104 152441653 17592186044416 (@Ns132p1428 845704300962250752 403263235551 4398046511104 152441653 17592186044416 (@Ns132p1429 97915701 17592186044416 (Ns132p1413 rfl rfl) (Ns132p1413 rfl rfl) rfl) (Ns132p1413 rfl rfl) rfl rfl) qz372 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 8126995 8388608) (BSN.cos_neg_of_bound 8126995 8388608 Bool.false 2375142 4194304 1 1710526 (Ns132p1433 rfl rfl)) rfl rfl) 

noncomputable def Ns132p1435 := @Ns132p1398 488083297088853323379 Ns132p1332 (Ns132p1399 qz29 (@Enclosure.Real.IsNear.of_eq qz737 (@Inv.inv Real Real.instInv (Real.sqrt qz187)) Bool.false 2984933 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz182 (BSN.t_div_two_pi_nonneg qz181 391923 1000 qz184)) Ns132p1403) rfl) (@Ns132p1404 1099511627776 326140458974751 3761486453226340352 (BSN.correction_mk qz183 (BSN.cos_two_pi_p_ne_zero_mk qz181 391923 1000 7 qz184 rfl rfl (@BSN.floor_sqrt_eq_dec qz181 391923 1000 7 qz184 rfl rfl rfl))) (@Ns132p1405 1048576 1187571 2097152 197952379 3587233021952 777202278237 1099511627776 326140458974751 3761486453226340352 (@Ns132p1406 1048576 (Ns132p1420 rfl rfl rfl rfl rfl) rfl) (Ns132p1434 rfl) rfl)) 

noncomputable def Ns132p1436 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz181) (hardyZApproximantRS₀ qz181) Bool.true 4381795143466873551 9223372036854775808 25199168551559296265843 Ns132p1332 (@Eq.refl Real (hardyZApproximantRS₀ qz181)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz181) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz181) qz181 7) (@HMul.hMul Real Real Real qz5 qz735 (Zeta.RiemannSiegel.correction qz183))) Bool.true 4381795143466873551 9223372036854775808 25199168551559296265843 Ns132p1332 (BSN.hardyZApproximantRS₀_eq qz181 7 (@BSN.floor_sqrt_eq_dec qz181 391923 1000 7 qz184 rfl rfl rfl)) (@Ns132p1334 4381795143466873551 9223372036854775808 25199168551559296265843 Ns132p1332 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz181) qz181 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz181) qz181 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz181) qz181 7)) Bool.true 24380613 33554432 13139 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz181) qz181 7) (Ns132p1397 (Ns132p1396 rfl) rfl rfl)) (Ns132p1435 rfl) rfl rfl)) 

theorem RS133to150.d51 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz181) Bool.true 4381795143466873551 9223372036854775808 25199168551559296265843 Ns132p1332 := Ns132p1436 

noncomputable def Ns132p1437 := nat_lit 7601565670119166923767808 

noncomputable abbrev qz899 := (Enclosure.sfrac Bool.false 392683 1000)

noncomputable abbrev qz740 := qz899

noncomputable abbrev qz531 := qz740

noncomputable abbrev qz194 := qz531

noncomputable abbrev qz900 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 392683 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz741 := qz900

noncomputable abbrev qz532 := qz741

noncomputable abbrev qz195 := qz532

noncomputable abbrev qz901 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 392683 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz742 := qz901

noncomputable abbrev qz533 := qz742

noncomputable abbrev qz196 := qz533

noncomputable abbrev qz743 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz195 qz9))

noncomputable def Ns132p1438 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz194) qz194 7) (@HMul.hMul Real Real Real qz5 qz743 (Zeta.RiemannSiegel.correction qz196)) 17768691 33554432 52657 33554432 73912417276669497 288230376151711744 954022412558224649207 Ns132p333 Ns132p1437 

noncomputable def Ns132p1439 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz194) qz194 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 392683 1000 56 94 67108864 33554432 1125899906842624 Bool.false 41282864422 1278 

noncomputable def Ns132p1440 := Ns132p1439 120242927 40 27397080 8 130587807 40 25364760 8 Bool.true 122670 39283 Bool.true 31284885 Bool.true 87797829 3537118876014220 1 Bool.false 59947764 Bool.false Bool.false 17414898 Bool.true Bool.false 17768691 

noncomputable def Ns132p1441 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz194) qz194 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 392683 1000 45 10 67108864 33554432 1125899906842624 Bool.false 41282864422 1278 

noncomputable def Ns132p1442 := Ns132p1441 93032624 40 33554424 8 108007536 40 30011992 8 Bool.false 16168032 23174 Bool.false 6888463 Bool.true 75715266 3537118876014220 1 Bool.false 6876372 Bool.true Bool.false 28739105 Bool.true Bool.true 122670 

noncomputable def Ns132p1443 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz194) qz194 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 392683 1000 218 116 67108864 33554432 1125899906842624 Bool.false 41282864422 1278 

noncomputable def Ns132p1444 := Ns132p1443 46516304 40 47453136 16 73726608 40 38745320 8 Bool.false 55780544 1328 Bool.false 36372777 Bool.false 103613393 3537118876014220 1 Bool.false 57490851 Bool.true Bool.false 1800747 Bool.false Bool.false 16168032 

noncomputable def Ns132p1445 := nat_lit 365684813628191049552509697697876383217358830488582450547 

noncomputable def Ns132p1446 := nat_lit 594452268948863962483476277861186199824286733041664000 

noncomputable def Ns132p1447 := nat_lit 4481810835993464062263742548640000 

noncomputable def Ns132p1448 := nat_lit 10559593536443116379137241940021606720 

noncomputable abbrev qz534 := (@Eq.refl Real qz740)

noncomputable abbrev qz197 := qz534

noncomputable def Ns132p1449 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz194 392683 1000 616800753956 16000000 785366 4000 2000 Ns132p1447 Ns132p1448 qz197 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns132p1450 := nat_lit 117019140361021135856803103263320442629554825756346384175040 

noncomputable abbrev qz535 := (Enclosure.sfrac Bool.false 392683 2000)

noncomputable abbrev qz744 := (Real.log (Enclosure.sfrac Bool.false 616800753956 16000000))

noncomputable abbrev qz198 := (@HSub.hSub Real Real Real qz342 (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 392683 4000) qz744) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 785366)))))) qz535)

noncomputable abbrev qz536 := (@HSub.hSub Real Real Real qz12 qz198 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 392683 2000) (Real.log Real.pi)))

noncomputable def Ns132p1451 := @Enclosure.Real.IsNear.addLit_ft_p qz536 (Enclosure.sfrac Bool.true Ns132p1447 Ns132p1448) 11081792182084711629907 18014398509481984000 3332034738744811863997 Ns132p199 Ns132p1447 Ns132p1448 0 1 Ns132p1450 

noncomputable def Ns132p1452 := nat_lit 148737296884757229850129439129600 

noncomputable abbrev qz537 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 392683 2000) (Real.log Real.pi))

noncomputable def Ns132p1453 := @Enclosure.Real.IsNear.subLit_ff_p qz198 qz537 3026134408399073499767 3602879701896396800 5008538507627248187 684210400000000000000000 15083252861763 67108864000 392683 33554432000 Ns132p1452 11081792182084711629907 18014398509481984000 

noncomputable def Ns132p1454 := nat_lit 30261344083990734997670000 

noncomputable abbrev qz199 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 392683 4000) qz744) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 785366))))))

noncomputable def Ns132p1455 := @Enclosure.Real.IsNear.subLit_ff_p qz199 qz535 18667646066944824460371 18014398509481984000 5008538507627248187 684210400000000000000000 392683 2000 0 1 Ns132p1454 3026134408399073499767 3602879701896396800 5008538507627248187 684210400000000000000000 

noncomputable def Ns132p1456 := nat_lit 42035801935488508333263050782443307008 

noncomputable def Ns132p1457 := nat_lit 12765909197784345133187072 

noncomputable def Ns132p1458 := nat_lit 231795953517558865193189869976125638121497318605205655604038283297828474880 

noncomputable def Ns132p1459 := nat_lit 509878123271635816922651095911210102901597993640731244388159404768587776 

noncomputable def Ns132p1460 := nat_lit 9403746548788037895052380752627740172043091008046422698117564067840 

noncomputable def Ns132p1461 := BSN.log_dyadic_bound 92512753956 1141088753956 4 3 Ns132p1458 33554432 13684208 Ns132p1459 Ns132p1460 5452759 1233601507912 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 92512753956) (BSN.artanhQ 1141088753956) 0 3 Ns132p1459 Ns132p1458 Ns132p1460 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns132p1462 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 392683 4000) qz744 392683 4000 0 1 47556717685551737 4503599627370496 12500002565789 171052600000000000000 18674714570915512740371 18014398509481984000 4908538507541721887 684210400000000000000000 (Enclosure.Real.IsNear.const Bool.false 392683 4000) (BSN.isNear_log_sfrac 616800753956 16000000 47556717685551737 4503599627370496 12500002565789 171052600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 616800753956) qz350)) Bool.false Ns132p1457 Ns132p87 1000000205263120 13684208000000000000000 47556717685551737 4503599627370496 12500002565789 171052600000000000000 (BSN.log_rat_reduce_isNear 616800753956 16000000 15 1233601507912 1048576000000 5452759 33554432 24973259072661432 36028797018963968 13684208 1000000000000000 rfl rfl rfl rfl (Ns132p1461 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns132p1463 := BSN.arctan_dyadic_bound_f 1000 785366 1 0 4194304 1710526 0 1 1 0 1 1 5340 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 785366) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 785366) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz538 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 785366)))

noncomputable def Ns132p1464 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz538 884279719003555 562949953421312 1 2000000000000000 5340 4194304 1 1710526 3705931809784216944640 883562996336035 562949953421312 1000000000855263 1710526000000000000000 qz17 (Ns132p1463 rfl) rfl rfl 

noncomputable def Ns132p1465 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 392683 4000) qz744) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz538)) 18674714570915512740371 18014398509481984000 4908538507541721887 684210400000000000000000 883562996336035 2251799813685248 1000000000855263 6842104000000000000000 Ns132p1456 18667646066944824460371 18014398509481984000 5008538507627248187 684210400000000000000000 (Ns132p1462 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz538) 1 4 0 1 883562996336035 562949953421312 1000000000855263 1710526000000000000000 883562996336035 2251799813685248 1000000000855263 6842104000000000000000 qz353 Ns132p1464 rfl) 

noncomputable def Ns132p1466 := @Ns132p1451 Ns132p1445 Ns132p1446 3332034738744811863997 Ns132p199 (@Ns132p1453 3332034738744811863997 Ns132p199 (Ns132p1455 (Ns132p1465 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 392683 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz535 (Real.log Real.pi) 392683 2000 0 1 38410761 33554432 1 16777216 15083252861763 67108864000 392683 33554432000 (Enclosure.Real.IsNear.const Bool.false 392683 2000) RS133to150.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns132p1447 Ns132p1448) 

noncomputable def Ns132p1467 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz194) Bool.false Ns132p1445 Ns132p1446 3332034738744811863997 Ns132p199 1290089513 2097152 161 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz194) (@HAdd.hAdd Real Real Real qz354 qz536 (Enclosure.sfrac Bool.true Ns132p1447 Ns132p1448)) Bool.false Ns132p1445 Ns132p1446 3332034738744811863997 Ns132p199 Ns132p1449 (Ns132p1466 rfl rfl)) 

noncomputable def Ns132p1468 := nat_lit 21281316155776049034293729408867607081761897253184105734316401117593020709339873673025 

noncomputable def Ns132p1469 := nat_lit 6522413412444155899288222221248977661032785664554730621238990864384271560002240321 

noncomputable def Ns132p1470 := nat_lit 55726220310079028361218062758675996393163296867263378787918092179915574941935855992641 

noncomputable def Ns132p1471 := BSN.sin_dyadic_bound_f 16857805559 17179869184 3 2 8388608 3424393 Ns132p1468 Ns132p99 Ns132p1469 Ns132p1470 Ns132p102 Ns132p1469 6972568 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 16857805559) qz355 0 2 Ns132p1468 Ns132p99 Ns132p1469 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 16857805559) qz356 0 2 Ns132p1470 Ns132p102 Ns132p1469 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1472 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz194) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1290089513) qz368) Bool.false 1290089513 2097152 161 8388608 Bool.false 6972568 8388608 1 1710526 (Ns132p1467 rfl) (Enclosure.sfrac_false_div 1290089513 2097152) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1290089513) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 296565651708268066635776) qz453) 226375608064910080 72057594037927936 Bool.false 6972568 8388608 97 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 1290089513 2097152 226375608064910080 72057594037927936 97 296565651708268066635776 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 6972568 8388608 296565651708268066635776 302231454903657293676544 16857805559 17179869184 3424393 3421052 (Ns132p1471 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p1473 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz194) Bool.false Ns132p1445 Ns132p1446 3332034738744811863997 Ns132p199 41282864422 67108864 1278 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz194) (@HAdd.hAdd Real Real Real qz354 qz536 (Enclosure.sfrac Bool.true Ns132p1447 Ns132p1448)) Bool.false Ns132p1445 Ns132p1446 3332034738744811863997 Ns132p199 Ns132p1449 (Ns132p1466 rfl rfl)) 

noncomputable def Ns132p1474 := Ns132p1444 23174 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 218 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 57490851 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 116 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 1800747 67108864) qz197 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz194) qz194 1) Bool.false 871571 1048576 141891647 7174466043904 55780544 67108864 1328 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz194) qz194 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz194)) Bool.false 871571 1048576 141891647 7174466043904 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz194) qz194) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz194)) Bool.false 6972568 8388608 283783294 14348932087808 871571 1048576 141891647 7174466043904 (Ns132p1472 rfl rfl) rfl)) rfl) (Ns132p1473 rfl) RS133to150.d7 

noncomputable def Ns132p1475 := nat_lit 59642656406012678686791573631630273683063588269136387765428586561 

noncomputable def Ns132p1476 := nat_lit 3063456231060787211275572995245556099838538044100081523132481 

noncomputable def Ns132p1477 := nat_lit 178921842305575914485952169748900329936991087731320963133239494721 

noncomputable def Ns132p1478 := BSN.cos_dyadic_bound_f 36372777 67108864 3 2 67108864 33554432 Ns132p1475 Ns132p124 Ns132p1476 Ns132p1477 Ns132p127 Ns132p1476 57490851 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 36372777) qz360 0 2 Ns132p1475 Ns132p124 Ns132p1476 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 36372777) (BSN.cosOddQ 67108864) 0 2 Ns132p1477 Ns132p127 Ns132p1476 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1479 := nat_lit 949501412953038799317867996266627146130102995472748267173794187242253221205356730497196241753193529281 

noncomputable def Ns132p1480 := nat_lit 1531054844231749331886860992829806564970087407418389698078271952371370262358421331539945852452801 

noncomputable def Ns132p1481 := nat_lit 5747355219179922331267157760827321419152712598800814112871919313868482102990247094133672094180727799745 

noncomputable def Ns132p1482 := BSN.cos_dyadic_bound_f 103613393 67108864 4 3 67108864 33554432 Ns132p1479 Ns132p118 Ns132p1480 Ns132p1481 Ns132p121 Ns132p1480 1800747 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 103613393) qz360 0 3 Ns132p1479 Ns132p118 Ns132p1480 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 103613393) (BSN.cosOddQ 67108864) 0 3 Ns132p1481 Ns132p121 Ns132p1480 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1483 := nat_lit 2251590046325828720810612161 

noncomputable def Ns132p1484 := BSN.sin_dyadic_bound_f 6888463 67108864 2 1 67108864 33554432 Ns132p1483 Ns132p114 Ns132p1483 Ns132p1483 Ns132p115 Ns132p1483 6876372 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 6888463) qz359 0 1 Ns132p1483 Ns132p114 Ns132p1483 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 6888463) (BSN.sinOddQ 67108864) 0 1 Ns132p1483 Ns132p115 Ns132p1483 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1485 := nat_lit 270095510280702051584745271334826423303929493420177677726814181667599294422426875121801019675065716736 

noncomputable def Ns132p1486 := nat_lit 35497799265806448593705113237391884171770568411067530416484224267635145956506289877237495238656 

noncomputable def Ns132p1487 := nat_lit 1637526651319162437160314008362421821790965803611186592650265165581890827130542907078395651211496263680 

noncomputable def Ns132p1488 := BSN.cos_dyadic_bound_f 75715266 67108864 4 3 67108864 33554432 Ns132p1485 Ns132p118 Ns132p1486 Ns132p1487 Ns132p121 Ns132p1486 28739105 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 75715266) qz360 0 3 Ns132p1485 Ns132p118 Ns132p1486 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 75715266) (BSN.cosOddQ 67108864) 0 3 Ns132p1487 Ns132p121 Ns132p1486 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1489 := Ns132p1442 39283 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 45 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 6876372 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 10 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 28739105 67108864) qz197 rfl rfl (Ns132p1474 RS133to150.d9 RS133to150.d11 RS133to150.d13 RS133to150.d17 (Ns132p1478 rfl rfl) (Ns132p1482 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns132p1473 rfl) RS133to150.d19 RS133to150.d21 RS133to150.d23 RS133to150.d25 RS133to150.d17 (Ns132p1484 rfl rfl) (Ns132p1488 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns132p1490 := nat_lit 32642190242264172590495948597200331905072024598692189941079190625 

noncomputable def Ns132p1491 := nat_lit 917648804517178416362072895648480609618335481032794250390625 

noncomputable def Ns132p1492 := nat_lit 97924735429183483414655121645809698753996837125114504234736790625 

noncomputable def Ns132p1493 := BSN.cos_dyadic_bound_f 31284885 67108864 3 2 67108864 33554432 Ns132p1490 Ns132p124 Ns132p1491 Ns132p1492 Ns132p127 Ns132p1491 59947764 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 31284885) qz360 0 2 Ns132p1490 Ns132p124 Ns132p1491 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 31284885) (BSN.cosOddQ 67108864) 0 2 Ns132p1492 Ns132p127 Ns132p1491 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1494 := nat_lit 488716267539559366965966216511800076175504070036559701418465165376054200722578663207303822123597840721 

noncomputable def Ns132p1495 := nat_lit 209799923500519029231029432606174249256761333946220524513155225761351121831551020906792453423441 

noncomputable def Ns132p1496 := nat_lit 2961436781979170942759397200975796863094575633031820587691343479256311443681809978635632475612411609425 

noncomputable def Ns132p1497 := BSN.cos_dyadic_bound_f 87797829 67108864 4 3 67108864 33554432 Ns132p1494 Ns132p118 Ns132p1495 Ns132p1496 Ns132p121 Ns132p1495 17414898 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 87797829) qz360 0 3 Ns132p1494 Ns132p118 Ns132p1495 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 87797829) (BSN.cosOddQ 67108864) 0 3 Ns132p1496 Ns132p121 Ns132p1495 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1498 := Ns132p1440 52657 BSN.abs_quadSignPos (BSN.cos_quad_nat0 56 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 59947764 67108864) BSN.abs_quadSignNeg qz728 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 17414898 67108864) qz197 rfl rfl (Ns132p1489 rfl rfl) (Ns132p1473 rfl) RS133to150.d27 RS133to150.d29 RS133to150.d31 RS133to150.d33 RS133to150.d17 (Ns132p1493 rfl rfl) (Ns132p1497 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns132p1499 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz194) qz194 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz194) qz194 7) 17768691 67108864 52657 67108864 17768691 67108864 52657 67108864 2384873335554048 17768691 33554432 52657 33554432 (Ns132p1498 rfl) 

noncomputable def Ns132p1500 := @Enclosure.Real.IsNear.mulLit_tf qz743 (Zeta.RiemannSiegel.correction qz196) 46617 131072 1 4194304 1585524964641 2199023255552 635898393630875 7522972906452680704 73912417276669497 288230376151711744 

noncomputable abbrev qz745 := (@HPow.hPow Real Real Real qz7 qz195 qz9)

noncomputable def Ns132p1501 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz745 1 1 0 1 46617 131072 1 4194304 46617 131072 1 4194304 

noncomputable def Ns132p1502 := @Enclosure.Real.IsNear.sqrt_image qz195 524266753787 8388608000 392683 8388608000 33158200 33158226 4194304 (@Enclosure.Real.IsNear.of_eq qz195 (@HMul.hMul Real Real Real qz5 qz194 qz3) Bool.false 524266753787 8388608000 392683 8388608000 (BSN.t_div_two_pi_mk qz194 392683 1000 qz197) (@Enclosure.Real.IsNear.mulLit_ff qz194 qz3 392683 1000 0 1 1335089 8388608 1 8388608 524266753787 8388608000 392683 8388608000 (Enclosure.Real.IsNear.const Bool.false 392683 1000) RS133to150.d36 rfl)) 

noncomputable abbrev qz902 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 392683 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz746 := qz902

noncomputable abbrev qz539 := qz746

noncomputable abbrev qz200 := qz539

noncomputable def Ns132p1503 := @Enclosure.Real.IsNear.sqrt_image qz200 33158213 4194304 13 4194304 11793030 11793036 4194304 (@Enclosure.Real.IsNear.recentre' qz200 Bool.false 66316426 8388608 26 8388608 33158213 4194304 13 4194304 (Ns132p1502 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns132p1504 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz200) 11793033 4194304 3 4194304 1491743 1491745 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz200) Bool.false 23586066 8388608 6 8388608 11793033 4194304 3 4194304 (Ns132p1503 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns132p1505 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz200)) Bool.false 2983488 8388608 2 8388608 46617 131072 1 4194304 (Ns132p1504 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz201 := (@HMul.hMul Real Real Real qz339 qz337 qz533)

noncomputable abbrev qz747 := (@HMul.hMul Real Real Real qz843 qz901 qz901)

noncomputable abbrev qz540 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz747 qz742) qz640)

noncomputable abbrev qz202 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz540))

noncomputable def Ns132p1506 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz196) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz201)) qz202) Bool.false 1585524964641 

noncomputable def Ns132p1507 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz201)) qz202 5059707 4194304 31 

noncomputable def Ns132p1508 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz201)) Bool.false 10119414 8388608 248 8388608 5059707 4194304 31 

noncomputable def Ns132p1509 := @Enclosure.Real.IsNear.recentre' (Real.cos qz201) Bool.false 6953836 8388608 290625398 14348932087808 1738459 2097152 145312699 7174466043904 

noncomputable def Ns132p1510 := @Enclosure.Real.IsNear.cos_image qz201 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 47728143) qz365) Bool.false 47728143 8388608 165 8388608 Bool.false 6953836 8388608 1 

noncomputable def Ns132p1511 := nat_lit 350818980350197892642052891 

noncomputable def Ns132p1512 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz196 884279719003555 140737488355328 1 500000000000000 3798085 4194304 13 4194304 3358569536551617192175 590295810358705651712 Ns132p1511 

noncomputable def Ns132p1513 := @Enclosure.Real.IsNear.subLit_ff_p qz200 qz1 33158213 4194304 13 4194304 7 1 0 1 3798085 3798085 4194304 13 

noncomputable def Ns132p1514 := @Ns132p1513 4194304 (@Enclosure.Real.IsNear.recentre' qz200 Bool.false 66316426 8388608 26 8388608 33158213 4194304 13 4194304 (Ns132p1502 rfl rfl rfl rfl rfl rfl) rfl) qz366 

noncomputable def Ns132p1515 := @Enclosure.Real.IsNear.recentre' qz201 Bool.false 3358569536551617192175 590295810358705651712 Ns132p1511 Ns132p153 47728143 8388608 165 8388608 (@Ns132p1512 Ns132p153 RS133to150.d35 (Ns132p1514 rfl rfl) rfl) 

noncomputable def Ns132p1516 := nat_lit 20935945540651795053335748700311205147563361490542523354312789094131968009802921082880 

noncomputable def Ns132p1517 := nat_lit 6312491900846028400477159253935642180681709373969050416469335464358931091916128256 

noncomputable def Ns132p1518 := nat_lit 54822018095772379188945235957261070061040081136243992227287782989117620803906452914176 

noncomputable def Ns132p1519 := BSN.sin_dyadic_bound_f 16789010636 17179869184 3 2 8388608 3424393 Ns132p1516 Ns132p99 Ns132p1517 Ns132p1518 Ns132p102 Ns132p1517 6953836 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 16789010636) qz355 0 2 Ns132p1516 Ns132p99 Ns132p1517 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 16789010636) qz356 0 2 Ns132p1518 Ns132p102 Ns132p1517 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1520 := @Ns132p1510 1710526 (Ns132p1515 rfl) (Enclosure.sfrac_false_div 47728143 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 47728143) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1181421594501836257099776) qz367) 226375608064910080 72057594037927936 Bool.false 6953836 8388608 0 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 47728143 8388608 226375608064910080 72057594037927936 0 1181421594501836257099776 Ns132p87 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 6953836 8388608 1181421594501836257099776 Ns132p87 16789010636 17179869184 3424393 3421052 (Ns132p1519 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p1521 := @Enclosure.Real.IsNear.inv_image (Real.cos qz201) 1738459 2097152 145312699 7174466043904 5059583 5059831 4194304 (Ns132p1509 (Ns132p1520 rfl rfl) rfl) rfl 

noncomputable def Ns132p1522 := @Enclosure.Real.IsNear.recentre' qz202 Bool.false 2506904 4194304 

noncomputable abbrev qz203 := (@HMul.hMul Real Real Real qz339 qz337 qz540)

noncomputable def Ns132p1523 := @Enclosure.Real.IsNear.cos_image qz203 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 1950721)) qz368) Bool.true 1950721 2097152 

noncomputable def Ns132p1524 := nat_lit 2303004896453847851047130005 

noncomputable def Ns132p1525 := nat_lit 4136326626809967002155384383501549 

noncomputable def Ns132p1526 := @Enclosure.Real.IsNear.recentre' qz203 Bool.true Ns132p1524 Ns132p171 Ns132p1525 

noncomputable abbrev qz204 := qz540

noncomputable def Ns132p1527 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz204 884279719003555 140737488355328 1 500000000000000 2604385068391 

noncomputable abbrev qz541 := (@HSub.hSub Real Real Real qz635 qz747 qz742)

noncomputable abbrev qz205 := qz541

noncomputable def Ns132p1528 := @Enclosure.Real.IsNear.subLit_tf qz205 qz27 1504873440615 17592186044416 153276331 17592186044416 1 16 

noncomputable abbrev qz542 := qz747

noncomputable abbrev qz206 := qz542

noncomputable def Ns132p1529 := @Enclosure.Real.IsNear.subLit_ff_n qz206 qz196 14425449667225 17592186044416 98750379 17592186044416 3798085 4194304 13 4194304 

noncomputable def Ns132p1530 := @Enclosure.Real.IsNear.mulLit_ff qz196 qz196 3798085 4194304 13 4194304 3798085 4194304 13 4194304 14425449667225 17592186044416 

noncomputable def Ns132p1531 := nat_lit 470763774261340214858698984010352357069040262310666241 

noncomputable def Ns132p1532 := nat_lit 15085502980398593449464978548510856026246963233994833920 

noncomputable def Ns132p1533 := nat_lit 209682059822881900373846996767488416902598586408961 

noncomputable def Ns132p1534 := nat_lit 1411871958664374880775349258037522094373315589759180801 

noncomputable def Ns132p1535 := nat_lit 678847634117936705225924034682988521181113345529767526400 

noncomputable def Ns132p1536 := BSN.cos_dyadic_bound_f 1950721 2097152 3 2 4194304 1710526 Ns132p1531 Ns132p1532 Ns132p1533 Ns132p1534 Ns132p1535 Ns132p1533 2506904 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1950721) (BSN.cosEvenQ 2097152) 0 2 Ns132p1531 Ns132p1532 Ns132p1533 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1950721) (BSN.cosOddQ 2097152) 0 2 Ns132p1534 Ns132p1535 Ns132p1533 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1537 := @Ns132p1522 198807642 3587233021952 313363 524288 99403821 1793616510976 (@Ns132p1523 115 2097152 Bool.false 2506904 4194304 1 1710526 (@Ns132p1526 Ns132p174 1950721 2097152 115 2097152 (@Ns132p1527 17592186044416 153276331 17592186044416 Ns132p1524 Ns132p171 Ns132p1525 Ns132p174 RS133to150.d35 (@Ns132p1528 0 1 41670161094256 2604385068391 17592186044416 153276331 17592186044416 (@Ns132p1529 6311896691465256960 1504873440615 17592186044416 153276331 17592186044416 (@Ns132p1530 98750379 17592186044416 (Ns132p1514 rfl rfl) (Ns132p1514 rfl rfl) rfl) (Ns132p1514 rfl rfl) rfl rfl) qz372 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 1950721 2097152) (BSN.cos_neg_of_bound 1950721 2097152 Bool.false 2506904 4194304 1 1710526 (Ns132p1536 rfl rfl)) rfl rfl) 

noncomputable def Ns132p1538 := @Ns132p1500 954022412558224649207 Ns132p333 (Ns132p1501 qz29 (@Enclosure.Real.IsNear.of_eq qz745 (@Inv.inv Real Real.instInv (Real.sqrt qz200)) Bool.false 46617 131072 1 4194304 (BSN.rpow_neg_quarter_mk qz195 (BSN.t_div_two_pi_nonneg qz194 392683 1000 qz197)) Ns132p1505) rfl) (@Ns132p1506 2199023255552 635898393630875 7522972906452680704 (BSN.correction_mk qz196 (BSN.cos_two_pi_p_ne_zero_mk qz194 392683 1000 7 qz197 rfl rfl (@BSN.floor_sqrt_eq_dec qz194 392683 1000 7 qz197 rfl rfl rfl))) (@Ns132p1507 1048576 313363 524288 99403821 1793616510976 1585524964641 2199023255552 635898393630875 7522972906452680704 (@Ns132p1508 1048576 (Ns132p1521 rfl rfl rfl rfl rfl) rfl) (Ns132p1537 rfl) rfl)) 

noncomputable def Ns132p1539 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz194) (hardyZApproximantRS₀ qz194) Bool.false 226544310752128569 288230376151711744 50471170454443075628023 Ns132p333 (@Eq.refl Real (hardyZApproximantRS₀ qz194)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz194) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz194) qz194 7) (@HMul.hMul Real Real Real qz5 qz743 (Zeta.RiemannSiegel.correction qz196))) Bool.false 226544310752128569 288230376151711744 50471170454443075628023 Ns132p333 (BSN.hardyZApproximantRS₀_eq qz194 7 (@BSN.floor_sqrt_eq_dec qz194 392683 1000 7 qz197 rfl rfl rfl)) (@Ns132p1438 226544310752128569 288230376151711744 50471170454443075628023 Ns132p333 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz194) qz194 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz194) qz194 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz194) qz194 7)) Bool.false 17768691 33554432 52657 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz194) qz194 7) (Ns132p1499 (Ns132p1498 rfl) rfl rfl)) (Ns132p1538 rfl) rfl rfl)) 

theorem RS133to150.d52 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz194) Bool.false 226544310752128569 288230376151711744 50471170454443075628023 Ns132p333 := Ns132p1539 

noncomputable def Ns132p1540 := nat_lit 27376933701655723461574656 

noncomputable abbrev qz903 := (Enclosure.sfrac Bool.false 394487 1000)

noncomputable abbrev qz748 := qz903

noncomputable abbrev qz543 := qz748

noncomputable abbrev qz207 := qz543

noncomputable abbrev qz904 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 394487 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz749 := qz904

noncomputable abbrev qz544 := qz749

noncomputable abbrev qz208 := qz544

noncomputable abbrev qz905 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 394487 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz750 := qz905

noncomputable abbrev qz545 := qz750

noncomputable abbrev qz209 := qz545

noncomputable abbrev qz751 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz208 qz9))

noncomputable def Ns132p1541 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz207) qz207 7) (@HMul.hMul Real Real Real qz5 qz751 (Zeta.RiemannSiegel.correction qz209)) 51997029 16777216 26445 16777216 154811904026699331 576460752303423488 3503126079374741874687 Ns132p188 Ns132p1540 

noncomputable def Ns132p1542 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz207) qz207 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 394487 1000 55 94 67108864 33554432 1125899906842624 Bool.false 41533311458 1283 

noncomputable def Ns132p1543 := Ns132p1542 120242927 40 27397080 8 130587807 40 25364760 8 Bool.true 119572179 39455 Bool.true 103170446 Bool.true 72931197 3537118876014220 1 Bool.false 67071352 Bool.false Bool.false 31229514 Bool.true Bool.true 103994058 

noncomputable def Ns132p1544 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz207) qz207 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 394487 1000 45 10 67108864 33554432 1125899906842624 Bool.false 41533311458 1283 

noncomputable def Ns132p1545 := Ns132p1544 93032624 40 33554424 8 108007536 40 30011992 8 Bool.true 58282249 23273 Bool.false 89504646 Bool.true 20113825 3537118876014220 1 Bool.false 65231797 Bool.true Bool.false 64117109 Bool.true Bool.true 119572179 

noncomputable def Ns132p1546 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz207) qz207 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 394487 1000 219 118 67108864 33554432 1125899906842624 Bool.false 41533311458 1283 

noncomputable def Ns132p1547 := Ns132p1546 46516304 40 47453136 16 73726608 40 38745320 8 Bool.true 67108832 1328 Bool.false 97490044 Bool.false 10228914 3537118876014220 1 Bool.false 66641550 Bool.false Bool.false 66330812 Bool.true Bool.true 58282249 

noncomputable def Ns132p1548 := nat_lit 378161416183419737539311136888365942451814675374266049367 

noncomputable def Ns132p1549 := nat_lit 611027201002762799187053022954681023444600701845504000 

noncomputable def Ns132p1550 := nat_lit 4585708924248457252105088579360000 

noncomputable def Ns132p1551 := nat_lit 10854023475608492773628431090931929920 

noncomputable abbrev qz546 := (@Eq.refl Real qz748)

noncomputable abbrev qz210 := qz546

noncomputable def Ns132p1552 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz207 394487 1000 622480972676 16000000 788974 4000 2000 Ns132p1550 Ns132p1551 qz210 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns132p1553 := nat_lit 121011653178694316012579563804277101584580696119765135797440 

noncomputable abbrev qz752 := (Real.log (Enclosure.sfrac Bool.false 622480972676 16000000))

noncomputable abbrev qz211 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 394487 4000) qz752) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 788974))))))

noncomputable abbrev qz753 := (Enclosure.sfrac Bool.false 394487 2000)

noncomputable abbrev qz547 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz211 qz753) (@HMul.hMul Real Real Real qz5 qz753 (Real.log Real.pi)))

noncomputable def Ns132p1554 := @Enclosure.Real.IsNear.addLit_ft_p qz547 (Enclosure.sfrac Bool.true Ns132p1550 Ns132p1551) 11149021011371843121407 18014398509481984000 3347224620325262615633 Ns132p199 Ns132p1550 Ns132p1551 0 1 Ns132p1553 

noncomputable def Ns132p1555 := nat_lit 748198134785295473463837851648000 

noncomputable abbrev qz548 := (@HSub.hSub Real Real Real qz12 qz211 qz753)

noncomputable abbrev qz549 := (@HMul.hMul Real Real Real qz5 qz753 (Real.log Real.pi))

noncomputable def Ns132p1556 := @Enclosure.Real.IsNear.subLit_ff_p qz548 qz549 15216501572782891987199 18014398509481984000 5031088512255931543 684210400000000000000000 15152545874607 67108864000 394487 33554432000 Ns132p1555 11149021011371843121407 18014398509481984000 

noncomputable def Ns132p1557 := nat_lit 30433003145565783974398000 

noncomputable abbrev qz550 := qz753

noncomputable def Ns132p1558 := @Enclosure.Real.IsNear.subLit_ff_p qz211 qz550 18769724585187901698303 18014398509481984000 5031088512255931543 684210400000000000000000 394487 2000 0 1 Ns132p1557 15216501572782891987199 18014398509481984000 5031088512255931543 684210400000000000000000 

noncomputable def Ns132p1559 := nat_lit 42265662323849535846651917080297734144 

noncomputable def Ns132p1560 := nat_lit 12776991439574596335960064 

noncomputable def Ns132p1561 := nat_lit 238805818004160562976746887114353741994454232411461543749247567119443988480 

noncomputable def Ns132p1562 := nat_lit 586204106775490254242210481360040060717420602292798198734723471270506496 

noncomputable def Ns132p1563 := nat_lit 13445399378717339341522631520185019210730328395230792477570937712640 

noncomputable def Ns132p1564 := BSN.log_dyadic_bound 98192972676 1146768972676 4 3 Ns132p1561 33554432 13684208 Ns132p1562 Ns132p1563 5760353 1244961945352 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 98192972676) (BSN.artanhQ 1146768972676) 0 3 Ns132p1562 Ns132p1561 Ns132p1563 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns132p1565 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 394487 4000) qz752 394487 4000 0 1 47598002253378169 4503599627370496 12500002565789 171052600000000000000 18776793114928393754303 18014398509481984000 4931088512170405243 684210400000000000000000 (Enclosure.Real.IsNear.const Bool.false 394487 4000) (BSN.isNear_log_sfrac 622480972676 16000000 47598002253378169 4503599627370496 12500002565789 171052600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 622480972676) qz350)) Bool.false Ns132p1560 Ns132p87 1000000205263120 13684208000000000000000 47598002253378169 4503599627370496 12500002565789 171052600000000000000 (BSN.log_rat_reduce_isNear 622480972676 16000000 15 1244961945352 1048576000000 5760353 33554432 24973259072661432 36028797018963968 13684208 1000000000000000 rfl rfl rfl rfl (Ns132p1564 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns132p1566 := BSN.arctan_dyadic_bound_f 1000 788974 1 0 4194304 1710526 0 1 1 0 1 1 5316 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 788974) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 788974) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz551 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 788974)))

noncomputable def Ns132p1567 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz551 884279719003555 562949953421312 1 2000000000000000 5316 4194304 1 1710526 3705945320583099056128 883566217561507 562949953421312 1000000000855263 1710526000000000000000 qz17 (Ns132p1566 rfl) rfl rfl 

noncomputable def Ns132p1568 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 394487 4000) qz752) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz551)) 18776793114928393754303 18014398509481984000 4931088512170405243 684210400000000000000000 883566217561507 2251799813685248 1000000000855263 6842104000000000000000 Ns132p1559 18769724585187901698303 18014398509481984000 5031088512255931543 684210400000000000000000 (Ns132p1565 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz551) 1 4 0 1 883566217561507 562949953421312 1000000000855263 1710526000000000000000 883566217561507 2251799813685248 1000000000855263 6842104000000000000000 qz353 Ns132p1567 rfl) 

noncomputable def Ns132p1569 := @Ns132p1554 Ns132p1548 Ns132p1549 3347224620325262615633 Ns132p199 (@Ns132p1556 3347224620325262615633 Ns132p199 (Ns132p1558 (Ns132p1568 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 394487 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz550 (Real.log Real.pi) 394487 2000 0 1 38410761 33554432 1 16777216 15152545874607 67108864000 394487 33554432000 (Enclosure.Real.IsNear.const Bool.false 394487 2000) RS133to150.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns132p1550 Ns132p1551) 

noncomputable def Ns132p1570 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz207) Bool.false Ns132p1548 Ns132p1549 3347224620325262615633 Ns132p199 1297915983 2097152 161 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz207) (@HAdd.hAdd Real Real Real qz354 qz547 (Enclosure.sfrac Bool.true Ns132p1550 Ns132p1551)) Bool.false Ns132p1548 Ns132p1549 3347224620325262615633 Ns132p199 Ns132p1552 (Ns132p1569 rfl rfl)) 

noncomputable def Ns132p1571 := nat_lit 140280651078204689744941948169921454879303318414655726028286903072204150180630559897185 

noncomputable def Ns132p1572 := nat_lit 282437652227139295774832404834672559699205192877559274783245695755901049077726099041 

noncomputable def Ns132p1573 := nat_lit 366944425196454057138831564170538150063424263630867996010149967395977505917430386046561 

noncomputable def Ns132p1574 := BSN.sin_dyadic_bound_f 27000096981 17179869184 3 2 8388608 3424393 Ns132p1571 Ns132p99 Ns132p1572 Ns132p1573 Ns132p102 Ns132p1572 8388604 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 27000096981) qz355 0 2 Ns132p1571 Ns132p99 Ns132p1572 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 27000096981) qz356 0 2 Ns132p1573 Ns132p102 Ns132p1572 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1575 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz207) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1297915983) qz368) Bool.false 1297915983 2097152 161 8388608 Bool.true 8388604 8388608 1 1710526 (Ns132p1570 rfl) (Enclosure.sfrac_false_div 1297915983 2097152) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1297915983) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474990729319227164983296) qz453) 226375608064910080 72057594037927936 Bool.false 8388604 8388608 98 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q1 1297915983 2097152 226375608064910080 72057594037927936 98 474990729319227164983296 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388604 8388608 474990729319227164983296 302231454903657293676544 27000096981 17179869184 3424393 3421052 (Ns132p1574 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p1576 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz207) Bool.false Ns132p1548 Ns132p1549 3347224620325262615633 Ns132p199 41533311458 67108864 1283 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz207) (@HAdd.hAdd Real Real Real qz354 qz547 (Enclosure.sfrac Bool.true Ns132p1550 Ns132p1551)) Bool.false Ns132p1548 Ns132p1549 3347224620325262615633 Ns132p199 Ns132p1552 (Ns132p1569 rfl rfl)) 

noncomputable def Ns132p1577 := Ns132p1547 23273 BSN.abs_quadSignPos (BSN.cos_quad_nat3 219 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66641550 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 118 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66330812 67108864) qz210 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz207) qz207 1) Bool.true 2097151 2097152 141891647 7174466043904 67108832 67108864 1328 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz207) qz207 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz207)) Bool.true 2097151 2097152 141891647 7174466043904 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz207) qz207) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz207)) Bool.true 8388604 8388608 283783294 14348932087808 2097151 2097152 141891647 7174466043904 (Ns132p1575 rfl rfl) rfl)) rfl) (Ns132p1576 rfl) RS133to150.d7 

noncomputable def Ns132p1578 := nat_lit 1931161311247147651143050044296278051051239563776955696946447982056413184138257747906774020141703233536 

noncomputable def Ns132p1579 := nat_lit 737094544420854264545069553469186810151852697101840842553680559992206276960038671132390888308736 

noncomputable def Ns132p1580 := nat_lit 9647025413432476979693896190248613793891980882322010349512668713788016017064073085084844177786977386496 

noncomputable def Ns132p1581 := BSN.sin_dyadic_bound_f 97490044 67108864 4 3 67108864 33554432 Ns132p1578 Ns132p233 Ns132p1579 Ns132p1580 Ns132p236 Ns132p1579 66641550 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 97490044) qz359 0 3 Ns132p1578 Ns132p233 Ns132p1579 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 97490044) (BSN.sinOddQ 67108864) 0 3 Ns132p1580 Ns132p236 Ns132p1579 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1582 := nat_lit 10947579536139411961003404816 

noncomputable def Ns132p1583 := BSN.cos_dyadic_bound_f 10228914 67108864 2 1 67108864 33554432 Ns132p1582 Ns132p135 Ns132p1582 Ns132p1582 Ns132p136 Ns132p1582 66330812 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 10228914) qz360 0 1 Ns132p1582 Ns132p135 Ns132p1582 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 10228914) (BSN.cosOddQ 67108864) 0 1 Ns132p1582 Ns132p136 Ns132p1582 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1584 := nat_lit 3940377616884774072666151626832318018710151373617922741793499357440 

noncomputable def Ns132p1585 := nat_lit 4118742430588133931683560731448740528253594758121739248611860736 

noncomputable def Ns132p1586 := nat_lit 10313368175524884640141004686233725421480843015581410079247126733056 

noncomputable def Ns132p1587 := BSN.sin_dyadic_bound_f 89504646 67108864 3 2 67108864 33554432 Ns132p1584 Ns132p108 Ns132p1585 Ns132p1586 Ns132p111 Ns132p1585 65231797 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 89504646) qz359 0 2 Ns132p1584 Ns132p108 Ns132p1585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 89504646) (BSN.sinOddQ 67108864) 0 2 Ns132p1586 Ns132p111 Ns132p1585 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1588 := nat_lit 163673612859886792022062890625 

noncomputable def Ns132p1589 := BSN.cos_dyadic_bound_f 20113825 67108864 2 1 67108864 33554432 Ns132p1588 Ns132p135 Ns132p1588 Ns132p1588 Ns132p136 Ns132p1588 64117109 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 20113825) qz360 0 1 Ns132p1588 Ns132p135 Ns132p1588 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 20113825) (BSN.cosOddQ 67108864) 0 1 Ns132p1588 Ns132p136 Ns132p1588 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1590 := Ns132p1545 39455 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 45 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 65231797 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 10 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 64117109 67108864) qz210 rfl rfl (Ns132p1577 RS133to150.d9 RS133to150.d11 RS133to150.d13 RS133to150.d17 (Ns132p1581 rfl rfl) (Ns132p1583 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns132p1576 rfl) RS133to150.d19 RS133to150.d21 RS133to150.d23 RS133to150.d25 RS133to150.d17 (Ns132p1587 rfl rfl) (Ns132p1589 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns132p1591 := nat_lit 2423043220176218685650002534011582551496106805271204803278036333027303624325396268018154652640606294016 

noncomputable def Ns132p1592 := nat_lit 1454332454116446469733984991474120363846008412072968169703043835397199917183758598184289669615616 

noncomputable def Ns132p1593 := nat_lit 12101401178665795004235511438466849545454878012607809478319937108230805750934273890931812681444945432576 

noncomputable def Ns132p1594 := BSN.sin_dyadic_bound_f 103170446 67108864 4 3 67108864 33554432 Ns132p1591 Ns132p233 Ns132p1592 Ns132p1593 Ns132p236 Ns132p1592 67071352 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 103170446) qz359 0 3 Ns132p1591 Ns132p233 Ns132p1592 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 103170446) (BSN.sinOddQ 67108864) 0 3 Ns132p1593 Ns132p236 Ns132p1592 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1595 := nat_lit 964811860129165217081052003629535934441374122707926261845300020641 

noncomputable def Ns132p1596 := nat_lit 800399359875233502671643327172680386191139198586489101949011361 

noncomputable def Ns132p1597 := nat_lit 2892834781667745184237812724234262442551740089726605807332002039201 

noncomputable def Ns132p1598 := BSN.cos_dyadic_bound_f 72931197 67108864 3 2 67108864 33554432 Ns132p1595 Ns132p124 Ns132p1596 Ns132p1597 Ns132p127 Ns132p1596 31229514 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 72931197) qz360 0 2 Ns132p1595 Ns132p124 Ns132p1596 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 72931197) (BSN.cosOddQ 67108864) 0 2 Ns132p1597 Ns132p127 Ns132p1596 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1599 := Ns132p1543 52890 BSN.abs_quadSignPos (BSN.cos_quad_nat3 55 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 67071352 67108864) BSN.abs_quadSignNeg qz728 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 31229514 67108864) qz210 rfl rfl (Ns132p1590 rfl rfl) (Ns132p1576 rfl) RS133to150.d27 RS133to150.d29 RS133to150.d31 RS133to150.d33 RS133to150.d17 (Ns132p1594 rfl rfl) (Ns132p1598 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns132p1600 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz207) qz207 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz207) qz207 7) 103994058 67108864 52890 67108864 103994058 67108864 52890 67108864 13957846190260224 51997029 16777216 26445 16777216 (Ns132p1599 rfl) 

noncomputable def Ns132p1601 := @Enclosure.Real.IsNear.mulLit_tf qz751 (Zeta.RiemannSiegel.correction qz209) 372509 1048576 1 4194304 415592385759 549755813888 2335766070758627 30091891625810722816 154811904026699331 576460752303423488 

noncomputable abbrev qz754 := (@HPow.hPow Real Real Real qz7 qz208 qz9)

noncomputable def Ns132p1602 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz754 1 1 0 1 372509 1048576 1 4194304 372509 1048576 1 4194304 

noncomputable def Ns132p1603 := @Enclosure.Real.IsNear.sqrt_image qz208 526675254343 8388608000 394487 8388608000 33234278 33234303 4194304 (@Enclosure.Real.IsNear.of_eq qz208 (@HMul.hMul Real Real Real qz5 qz207 qz3) Bool.false 526675254343 8388608000 394487 8388608000 (BSN.t_div_two_pi_mk qz207 394487 1000 qz210) (@Enclosure.Real.IsNear.mulLit_ff qz207 qz3 394487 1000 0 1 1335089 8388608 1 8388608 526675254343 8388608000 394487 8388608000 (Enclosure.Real.IsNear.const Bool.false 394487 1000) RS133to150.d36 rfl)) 

noncomputable abbrev qz906 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 394487 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz755 := qz906

noncomputable abbrev qz552 := qz755

noncomputable abbrev qz212 := qz552

noncomputable def Ns132p1604 := @Enclosure.Real.IsNear.sqrt_image qz212 66468581 8388608 25 8388608 11806551 11806557 4194304 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 66468581 8388608 25 8388608 66468581 8388608 25 8388608 (Ns132p1603 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns132p1605 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz212) 5903277 2097152 3 4194304 1490035 1490037 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz212) Bool.false 23613108 8388608 6 8388608 5903277 2097152 3 4194304 (Ns132p1604 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns132p1606 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz212)) Bool.false 2980072 8388608 2 8388608 372509 1048576 1 4194304 (Ns132p1605 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz339 qz337 qz545)

noncomputable abbrev qz756 := (@HMul.hMul Real Real Real qz843 qz905 qz905)

noncomputable abbrev qz553 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz756 qz750) qz640)

noncomputable abbrev qz214 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz553))

noncomputable def Ns132p1607 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz209) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz213)) qz214) Bool.false 415592385759 

noncomputable def Ns132p1608 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz213)) qz214 4727637 4194304 13 

noncomputable def Ns132p1609 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz213)) Bool.false 9455274 8388608 208 8388608 4727637 4194304 13 

noncomputable def Ns132p1610 := @Enclosure.Real.IsNear.recentre' (Real.cos qz213) Bool.false 7442274 8388608 139325858 7174466043904 3721137 4194304 69662929 3587233021952 

noncomputable def Ns132p1611 := @Enclosure.Real.IsNear.cos_image qz213 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 48684161) qz365) Bool.false 48684161 8388608 79 4194304 Bool.false 7442274 8388608 1 

noncomputable def Ns132p1612 := nat_lit 26986075411706349653071303 

noncomputable def Ns132p1613 := nat_lit 1441151880758558720000000000000 

noncomputable def Ns132p1614 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz209 884279719003555 140737488355328 1 500000000000000 7748325 8388608 25 8388608 6851686653748220295375 1180591620717411303424 Ns132p1612 

noncomputable def Ns132p1615 := @Enclosure.Real.IsNear.subLit_ff_p qz212 qz1 66468581 8388608 25 8388608 7 1 0 1 7748325 7748325 8388608 25 

noncomputable def Ns132p1616 := @Ns132p1615 8388608 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 66468581 8388608 25 8388608 66468581 8388608 25 8388608 (Ns132p1603 rfl rfl rfl rfl rfl rfl) rfl) qz366 

noncomputable def Ns132p1617 := @Enclosure.Real.IsNear.recentre' qz213 Bool.false 6851686653748220295375 1180591620717411303424 Ns132p1612 Ns132p1613 48684161 8388608 79 4194304 (@Ns132p1614 Ns132p1613 RS133to150.d35 (Ns132p1616 rfl rfl) rfl) 

noncomputable def Ns132p1618 := nat_lit 1319198308375739836137472 

noncomputable def Ns132p1619 := nat_lit 32552617956062640455879329618988625652686402758220917211959290123771620624000000000000 

noncomputable def Ns132p1620 := nat_lit 15256056252402986480057097738475400769356283348352443975672503906250000000000000000 

noncomputable def Ns132p1621 := nat_lit 85232156270041120168240056558155535584361620860395545883932766270220315920000000000000 

noncomputable def Ns132p1622 := BSN.sin_dyadic_bound_f 18746935500 17179869184 3 2 8388608 3424393 Ns132p1619 Ns132p99 Ns132p1620 Ns132p1621 Ns132p102 Ns132p1620 7442274 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 18746935500) qz355 0 2 Ns132p1619 Ns132p99 Ns132p1620 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 18746935500) qz356 0 2 Ns132p1621 Ns132p102 Ns132p1620 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1623 := @Ns132p1611 1710526 (Ns132p1617 rfl) (Enclosure.sfrac_false_div 48684161 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 48684161) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns132p1618) qz367) 226375608064910080 72057594037927936 Bool.false 7442274 8388608 0 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 48684161 8388608 226375608064910080 72057594037927936 0 Ns132p1618 Ns132p87 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 7442274 8388608 Ns132p1618 Ns132p87 18746935500 17179869184 3424393 3421052 (Ns132p1622 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p1624 := @Enclosure.Real.IsNear.inv_image (Real.cos qz213) 3721137 4194304 69662929 3587233021952 4727533 4727741 4194304 (Ns132p1610 (Ns132p1623 rfl rfl) rfl) rfl 

noncomputable def Ns132p1625 := @Enclosure.Real.IsNear.recentre' qz214 Bool.false 2813024 4194304 

noncomputable abbrev qz215 := (@HMul.hMul Real Real Real qz339 qz337 qz553)

noncomputable def Ns132p1626 := @Enclosure.Real.IsNear.cos_image qz215 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7010147)) qz365) Bool.true 7010147 8388608 

noncomputable def Ns132p1627 := nat_lit 8276121818725482290506565845 

noncomputable def Ns132p1628 := nat_lit 16114251205189339263870959437053293 

noncomputable def Ns132p1629 := @Enclosure.Real.IsNear.recentre' qz215 Bool.true Ns132p1627 Ns132p285 Ns132p1628 

noncomputable abbrev qz216 := qz553

noncomputable def Ns132p1630 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz216 884279719003555 140737488355328 1 500000000000000 9359167287079 

noncomputable abbrev qz554 := (@HSub.hSub Real Real Real qz635 qz756 qz750)

noncomputable abbrev qz217 := qz554

noncomputable def Ns132p1631 := @Enclosure.Real.IsNear.subLit_tf qz217 qz27 4961120775975 70368744177664 597132075 70368744177664 1 16 

noncomputable abbrev qz555 := qz756

noncomputable abbrev qz218 := qz555

noncomputable def Ns132p1632 := @Enclosure.Real.IsNear.subLit_ff_n qz218 qz209 60036540305625 70368744177664 387416875 70368744177664 7748325 8388608 25 8388608 

noncomputable def Ns132p1633 := @Enclosure.Real.IsNear.mulLit_ff qz209 qz209 7748325 8388608 25 8388608 7748325 8388608 25 8388608 60036540305625 70368744177664 

noncomputable def Ns132p1634 := nat_lit 20095713859403172537142524153189900324916222326818685063841 

noncomputable def Ns132p1635 := nat_lit 5831993084912939581349492205717840555405496407056192161 

noncomputable def Ns132p1636 := nat_lit 60275477592039691732264873475158265293637855987641942807201 

noncomputable def Ns132p1637 := BSN.cos_dyadic_bound_f 7010147 8388608 3 2 4194304 1710526 Ns132p1634 Ns132p929 Ns132p1635 Ns132p1636 Ns132p932 Ns132p1635 2813024 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 7010147) (BSN.cosEvenQ 8388608) 0 2 Ns132p1634 Ns132p929 Ns132p1635 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 7010147) (BSN.cosOddQ 8388608) 0 2 Ns132p1636 Ns132p932 Ns132p1635 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1638 := @Ns132p1625 776414782 14348932087808 87907 131072 388207391 7174466043904 (@Ns132p1626 449 8388608 Bool.false 2813024 4194304 1 1710526 (@Ns132p1629 Ns132p288 7010147 8388608 449 8388608 (@Ns132p1630 70368744177664 597132075 70368744177664 Ns132p1627 Ns132p285 Ns132p1628 Ns132p288 RS133to150.d35 (@Ns132p1631 0 1 149746676593264 9359167287079 70368744177664 597132075 70368744177664 (@Ns132p1632 41616897430310092800 4961120775975 70368744177664 597132075 70368744177664 (@Ns132p1633 387416875 70368744177664 (Ns132p1616 rfl rfl) (Ns132p1616 rfl rfl) rfl) (Ns132p1616 rfl rfl) rfl rfl) qz372 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7010147 8388608) (BSN.cos_neg_of_bound 7010147 8388608 Bool.false 2813024 4194304 1 1710526 (Ns132p1637 rfl rfl)) rfl rfl) 

noncomputable def Ns132p1639 := @Ns132p1601 3503126079374741874687 Ns132p188 (Ns132p1602 qz29 (@Enclosure.Real.IsNear.of_eq qz754 (@Inv.inv Real Real.instInv (Real.sqrt qz212)) Bool.false 372509 1048576 1 4194304 (BSN.rpow_neg_quarter_mk qz208 (BSN.t_div_two_pi_nonneg qz207 394487 1000 qz210)) Ns132p1606) rfl) (@Ns132p1607 549755813888 2335766070758627 30091891625810722816 (BSN.correction_mk qz209 (BSN.cos_two_pi_p_ne_zero_mk qz207 394487 1000 7 qz210 rfl rfl (@BSN.floor_sqrt_eq_dec qz207 394487 1000 7 qz210 rfl rfl rfl))) (@Ns132p1608 524288 87907 131072 388207391 7174466043904 415592385759 549755813888 2335766070758627 30091891625810722816 (@Ns132p1609 524288 (Ns132p1624 rfl rfl rfl rfl rfl) rfl) (Ns132p1638 rfl) rfl)) 

noncomputable def Ns132p1640 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz207) (hardyZApproximantRS₀ qz207) Bool.true 1631792408326609341 576460752303423488 202448144590515883091967 Ns132p188 (@Eq.refl Real (hardyZApproximantRS₀ qz207)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz207) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz207) qz207 7) (@HMul.hMul Real Real Real qz5 qz751 (Zeta.RiemannSiegel.correction qz209))) Bool.true 1631792408326609341 576460752303423488 202448144590515883091967 Ns132p188 (BSN.hardyZApproximantRS₀_eq qz207 7 (@BSN.floor_sqrt_eq_dec qz207 394487 1000 7 qz210 rfl rfl rfl)) (@Ns132p1541 1631792408326609341 576460752303423488 202448144590515883091967 Ns132p188 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz207) qz207 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz207) qz207 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz207) qz207 7)) Bool.true 51997029 16777216 26445 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz207) qz207 7) (Ns132p1600 (Ns132p1599 rfl) rfl rfl)) (Ns132p1639 rfl) rfl rfl)) 

theorem RS133to150.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz207) Bool.true 1631792408326609341 576460752303423488 202448144590515883091967 Ns132p188 := Ns132p1640 

noncomputable def Ns132p1641 := nat_lit 252429082827408835900080128 

noncomputable def Ns132p1642 := nat_lit 2644800273449072058834092032 

noncomputable abbrev qz907 := (Enclosure.sfrac Bool.false 396004 1000)

noncomputable abbrev qz757 := qz907

noncomputable abbrev qz556 := qz757

noncomputable abbrev qz219 := qz556

noncomputable abbrev qz908 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 396004 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz758 := qz908

noncomputable abbrev qz557 := qz758

noncomputable abbrev qz220 := qz557

noncomputable abbrev qz909 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 396004 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz759 := qz909

noncomputable abbrev qz558 := qz759

noncomputable abbrev qz221 := qz558

noncomputable abbrev qz760 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz220 qz9))

noncomputable def Ns132p1643 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz219) qz219 7) (@HMul.hMul Real Real Real qz5 qz760 (Zeta.RiemannSiegel.correction qz221)) 4275997 16777216 6637 4194304 82418246051423246475 295147905179352825856 7040404959844840912963 Ns132p1641 Ns132p1642 

noncomputable def Ns132p1644 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz219) qz219 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 396004 1000 55 94 67108864 33554432 1125899906842624 Bool.false 41744128998 1288 

noncomputable def Ns132p1645 := Ns132p1644 120242927 40 27397080 8 130587807 40 25364760 8 Bool.true 215458 39610 Bool.true 74761427 Bool.true 60215360 3537118876014220 1 Bool.false 60229152 Bool.false Bool.false 41858433 Bool.true Bool.false 8551994 

noncomputable def Ns132p1646 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz219) qz219 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 396004 1000 46 9 67108864 33554432 1125899906842624 Bool.false 41744128998 1288 

noncomputable def Ns132p1647 := Ns132p1646 93032624 40 33554424 8 108007536 40 30011992 8 Bool.false 50770400 23366 Bool.false 53777338 Bool.true 78558074 3537118876014220 1 Bool.false 46690414 Bool.true Bool.false 61806395 Bool.true Bool.true 215458 

noncomputable def Ns132p1648 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz219) qz219 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 396004 1000 221 119 67108864 33554432 1125899906842624 Bool.false 41744128998 1288 

noncomputable def Ns132p1649 := Ns132p1648 46516304 40 47453136 16 73726608 40 38745320 8 Bool.false 67108840 1336 Bool.false 26913637 Bool.false 3788832 3537118876014220 1 Bool.false 26197966 Bool.true Bool.false 3786819 Bool.false Bool.false 50770400 

noncomputable def Ns132p1650 := nat_lit 2967340464356149521934263469000011973108124583147821 

noncomputable def Ns132p1651 := nat_lit 4770367772452395562663101156645156568650743808000 

noncomputable def Ns132p1652 := nat_lit 4674561252815445893369958891520000 

noncomputable def Ns132p1653 := nat_lit 11106877989257675508649789627280916480 

noncomputable abbrev qz761 := (@Eq.refl Real qz907)

noncomputable abbrev qz559 := qz761

noncomputable abbrev qz222 := qz559

noncomputable def Ns132p1654 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz219 396004 1000 627277672064 16000000 792008 4000 2000 Ns132p1652 Ns132p1653 qz222 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns132p1655 := nat_lit 31114819947527138411117422512701565547138248428988095528960 

noncomputable abbrev qz762 := (Real.log (Enclosure.sfrac Bool.false 627277672064 16000000))

noncomputable abbrev qz223 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 396004 4000) qz762) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 792008))))))

noncomputable abbrev qz763 := (Enclosure.sfrac Bool.false 396004 2000)

noncomputable abbrev qz560 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz223 qz763) (@HMul.hMul Real Real Real qz5 qz763 (Real.log Real.pi)))

noncomputable def Ns132p1656 := @Enclosure.Real.IsNear.addLit_ft_p qz560 (Enclosure.sfrac Bool.true Ns132p1652 Ns132p1653) 2801402971201541464577 4503599627370496000 839999482459024050559 Ns132p1145 Ns132p1652 Ns132p1653 0 1 Ns132p1655 

noncomputable def Ns132p1657 := nat_lit 46999742750890040684164677632000 

noncomputable abbrev qz561 := (@HSub.hSub Real Real Real qz12 qz223 qz763)

noncomputable abbrev qz562 := (@HMul.hMul Real Real Real qz5 qz763 (Real.log Real.pi))

noncomputable def Ns132p1658 := @Enclosure.Real.IsNear.subLit_ff_p qz561 qz562 3822183486301545390593 4503599627370496000 315628188509264591 42763150000000000000000 3802703749761 16777216000 99001 8388608000 Ns132p1657 2801402971201541464577 4503599627370496000 

noncomputable def Ns132p1659 := nat_lit 1528873394520618156237200 

noncomputable abbrev qz563 := qz763

noncomputable def Ns132p1660 := @Enclosure.Real.IsNear.subLit_ff_p qz223 qz563 942781043944031667917 900719925474099200 315628188509264591 42763150000000000000000 396004 2000 0 1 Ns132p1659 3822183486301545390593 4503599627370496000 315628188509264591 42763150000000000000000 

noncomputable def Ns132p1661 := nat_lit 2122954179099154117082138511897788416 

noncomputable def Ns132p1662 := nat_lit 12786271448880364923125760 

noncomputable def Ns132p1663 := nat_lit 244862094528193035103848173264504461313748331476716719424314411603753697280 

noncomputable def Ns132p1664 := nat_lit 655996209968303029688338867653024206698657746253487314378436044186976256 

noncomputable def Ns132p1665 := nat_lit 17900011531183538933938133534992830982144801057253286815992947671040 

noncomputable def Ns132p1666 := BSN.log_dyadic_bound 102989672064 1151565672064 4 3 Ns132p1663 33554432 13684208 Ns132p1664 Ns132p1665 6017925 1254555344128 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 102989672064) (BSN.artanhQ 1151565672064) 0 3 Ns132p1664 Ns132p1663 Ns132p1665 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns132p1667 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 396004 4000) qz762 396004 4000 0 1 47632572982014585 4503599627370496 12500002565789 171052600000000000000 943134471558485185917 900719925474099200 1237512754015676789 171052600000000000000000 (Enclosure.Real.IsNear.const Bool.false 396004 4000) (BSN.isNear_log_sfrac 627277672064 16000000 47632572982014585 4503599627370496 12500002565789 171052600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 627277672064) qz350)) Bool.false Ns132p1662 Ns132p87 1000000205263120 13684208000000000000000 47632572982014585 4503599627370496 12500002565789 171052600000000000000 (BSN.log_rat_reduce_isNear 627277672064 16000000 15 1254555344128 1048576000000 6017925 33554432 24973259072661432 36028797018963968 13684208 1000000000000000 rfl rfl rfl rfl (Ns132p1666 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns132p1668 := BSN.arctan_dyadic_bound_f 1000 792008 1 0 4194304 1710526 0 1 1 0 1 1 5295 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 792008) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 792008) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz564 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 792008)))

noncomputable def Ns132p1669 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz564 884279719003555 562949953421312 1 2000000000000000 5295 4194304 1 1710526 3705957142532120903680 883569036133795 562949953421312 1000000000855263 1710526000000000000000 qz17 (Ns132p1668 rfl) rfl rfl 

noncomputable def Ns132p1670 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 396004 4000) qz762) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz564)) 943134471558485185917 900719925474099200 1237512754015676789 171052600000000000000000 883569036133795 2251799813685248 1000000000855263 6842104000000000000000 Ns132p1661 942781043944031667917 900719925474099200 315628188509264591 42763150000000000000000 (Ns132p1667 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz564) 1 4 0 1 883569036133795 562949953421312 1000000000855263 1710526000000000000000 883569036133795 2251799813685248 1000000000855263 6842104000000000000000 qz353 Ns132p1669 rfl) 

noncomputable def Ns132p1671 := @Ns132p1656 Ns132p1650 Ns132p1651 839999482459024050559 Ns132p1145 (@Ns132p1658 839999482459024050559 Ns132p1145 (Ns132p1660 (Ns132p1670 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 396004 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz563 (Real.log Real.pi) 396004 2000 0 1 38410761 33554432 1 16777216 3802703749761 16777216000 99001 8388608000 (Enclosure.Real.IsNear.const Bool.false 396004 2000) RS133to150.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns132p1652 Ns132p1653) 

noncomputable def Ns132p1672 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz219) Bool.false Ns132p1650 Ns132p1651 839999482459024050559 Ns132p1145 1304504031 2097152 81 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz219) (@HAdd.hAdd Real Real Real qz354 qz560 (Enclosure.sfrac Bool.true Ns132p1652 Ns132p1653)) Bool.false Ns132p1650 Ns132p1651 839999482459024050559 Ns132p1145 Ns132p1654 (Ns132p1671 rfl rfl)) 

noncomputable def Ns132p1673 := nat_lit 140221070354213998959301555174262710806175618892281331891266058690706525524062843290145 

noncomputable def Ns132p1674 := nat_lit 282198268077900323164748358684221751461467404246307862403772605042367125098348528161 

noncomputable def Ns132p1675 := nat_lit 366788768017481968179713528113770740704284245111004704128471664734162781979529168142881 

noncomputable def Ns132p1676 := BSN.sin_dyadic_bound_f 26997235379 17179869184 3 2 8388608 3424393 Ns132p1673 Ns132p99 Ns132p1674 Ns132p1675 Ns132p102 Ns132p1674 8388605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26997235379) qz355 0 2 Ns132p1673 Ns132p99 Ns132p1674 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26997235379) qz356 0 2 Ns132p1675 Ns132p102 Ns132p1674 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1677 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz219) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1304504031) qz368) Bool.false 1304504031 2097152 81 4194304 Bool.false 8388605 8388608 1 1710526 (Ns132p1672 rfl) (Enclosure.sfrac_false_div 1304504031 2097152) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1304504031) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474940387482908682616832) qz453) 226375608064910080 72057594037927936 Bool.false 8388605 8388608 98 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 1304504031 2097152 226375608064910080 72057594037927936 98 474940387482908682616832 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388605 8388608 474940387482908682616832 302231454903657293676544 26997235379 17179869184 3424393 3421052 (Ns132p1676 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p1678 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz219) Bool.false Ns132p1650 Ns132p1651 839999482459024050559 Ns132p1145 41744128998 67108864 1288 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz219) (@HAdd.hAdd Real Real Real qz354 qz560 (Enclosure.sfrac Bool.true Ns132p1652 Ns132p1653)) Bool.false Ns132p1650 Ns132p1651 839999482459024050559 Ns132p1145 Ns132p1654 (Ns132p1671 rfl rfl)) 

noncomputable def Ns132p1679 := Ns132p1649 23366 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 221 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 26197966 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 119 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 3786819 67108864) qz222 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz219) qz219 1) Bool.false 8388605 8388608 71373455 3587233021952 67108840 67108864 1336 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz219) qz219 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz219)) Bool.false 8388605 8388608 71373455 3587233021952 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz219) qz219) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz219)) Bool.false 8388605 8388608 142746910 7174466043904 8388605 8388608 71373455 3587233021952 (Ns132p1677 rfl rfl) rfl)) rfl) (Ns132p1678 rfl) RS133to150.d7 

noncomputable def Ns132p1680 := nat_lit 524674022547468709876889637361 

noncomputable def Ns132p1681 := BSN.sin_dyadic_bound_f 26913637 67108864 2 1 67108864 33554432 Ns132p1680 Ns132p114 Ns132p1680 Ns132p1680 Ns132p115 Ns132p1680 26197966 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 26913637) qz359 0 1 Ns132p1680 Ns132p114 Ns132p1680 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 26913637) (BSN.sinOddQ 67108864) 0 1 Ns132p1680 Ns132p115 Ns132p1680 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1682 := BSN.sin_dyadic_bound_f 3788832 67108864 1 0 67108864 33554432 0 1 1 0 1 1 3786819 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 3788832) qz359 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 3788832) (BSN.sinOddQ 67108864) 0 0 rfl) rfl rfl 

noncomputable def Ns132p1683 := nat_lit 285057596662953715247365735335004312512107514786091038282524958976 

noncomputable def Ns132p1684 := nat_lit 69951076975849272011861443037512434853624610821243234404311296 

noncomputable def Ns132p1685 := nat_lit 855032887834909447198073483118937912666615295136630628378766254336 

noncomputable def Ns132p1686 := BSN.cos_dyadic_bound_f 53777338 67108864 3 2 67108864 33554432 Ns132p1683 Ns132p124 Ns132p1684 Ns132p1685 Ns132p127 Ns132p1684 46690414 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 53777338) qz360 0 2 Ns132p1683 Ns132p124 Ns132p1684 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 53777338) (BSN.cosOddQ 67108864) 0 2 Ns132p1685 Ns132p127 Ns132p1684 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1687 := nat_lit 2337406460583124326032563866221838488412464843750357130917739208960 

noncomputable def Ns132p1688 := nat_lit 1450529677721024018615149643413017697066763170473503454287339776 

noncomputable def Ns132p1689 := nat_lit 6119430348715682053102766550205955917189776021832073480144280330496 

noncomputable def Ns132p1690 := BSN.sin_dyadic_bound_f 78558074 67108864 3 2 67108864 33554432 Ns132p1687 Ns132p108 Ns132p1688 Ns132p1689 Ns132p111 Ns132p1688 61806395 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 78558074) qz359 0 2 Ns132p1687 Ns132p108 Ns132p1688 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 78558074) (BSN.sinOddQ 67108864) 0 2 Ns132p1689 Ns132p111 Ns132p1688 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1691 := Ns132p1647 39610 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 46 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 46690414 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 9 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 61806395 67108864) qz222 rfl rfl (Ns132p1679 RS133to150.d9 RS133to150.d11 RS133to150.d13 RS133to150.d17 (Ns132p1681 rfl rfl) (Ns132p1682 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns132p1678 rfl) RS133to150.d19 RS133to150.d21 RS133to150.d23 RS133to150.d25 RS133to150.d17 (Ns132p1686 rfl rfl) (Ns132p1690 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns132p1692 := nat_lit 1917047231779442737675497157260164485739641374598983984609568398625 

noncomputable def Ns132p1693 := nat_lit 975934472466285241744647281747059100200393370346771903495970081 

noncomputable def Ns132p1694 := nat_lit 5019257903609785565425382173415697462203498201350110900419399949601 

noncomputable def Ns132p1695 := BSN.sin_dyadic_bound_f 74761427 67108864 3 2 67108864 33554432 Ns132p1692 Ns132p108 Ns132p1693 Ns132p1694 Ns132p111 Ns132p1693 60229152 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 74761427) qz359 0 2 Ns132p1692 Ns132p108 Ns132p1693 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 74761427) (BSN.sinOddQ 67108864) 0 2 Ns132p1694 Ns132p111 Ns132p1693 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1696 := nat_lit 448152179167532412529559082470126635316553082365907955403980800000 

noncomputable def Ns132p1697 := nat_lit 172845587519832829608910484647933918601429299679041945600000000 

noncomputable def Ns132p1698 := nat_lit 1344110846327557571929459426441084038112456388498365782320742400000 

noncomputable def Ns132p1699 := BSN.cos_dyadic_bound_f 60215360 67108864 3 2 67108864 33554432 Ns132p1696 Ns132p124 Ns132p1697 Ns132p1698 Ns132p127 Ns132p1697 41858433 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 60215360) qz360 0 2 Ns132p1696 Ns132p124 Ns132p1697 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 60215360) (BSN.cosOddQ 67108864) 0 2 Ns132p1698 Ns132p127 Ns132p1697 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1700 := Ns132p1645 53096 BSN.abs_quadSignPos (BSN.cos_quad_nat3 55 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 60229152 67108864) BSN.abs_quadSignNeg qz728 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 41858433 67108864) qz222 rfl rfl (Ns132p1691 rfl rfl) (Ns132p1678 rfl) RS133to150.d27 RS133to150.d29 RS133to150.d31 RS133to150.d33 RS133to150.d17 (Ns132p1695 rfl rfl) (Ns132p1699 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns132p1701 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz219) qz219 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz219) qz219 7) 8551994 67108864 53096 67108864 8551994 67108864 53096 67108864 1147829204549632 4275997 16777216 6637 4194304 (Ns132p1700 rfl) 

noncomputable def Ns132p1702 := @Enclosure.Real.IsNear.mulLit_tf qz760 (Zeta.RiemannSiegel.correction qz221) 2977213 8388608 1 8388608 27683019673575 35184372088832 2356810325824667 30091891625810722816 82418246051423246475 295147905179352825856 

noncomputable abbrev qz764 := (@HPow.hPow Real Real Real qz7 qz220 qz9)

noncomputable def Ns132p1703 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz764 1 1 0 1 2977213 8388608 1 8388608 2977213 8388608 1 8388608 

noncomputable def Ns132p1704 := @Enclosure.Real.IsNear.sqrt_image qz220 132175146089 2097152000 99001 2097152000 33298117 33298143 4194304 (@Enclosure.Real.IsNear.of_eq qz220 (@HMul.hMul Real Real Real qz5 qz219 qz3) Bool.false 132175146089 2097152000 99001 2097152000 (BSN.t_div_two_pi_mk qz219 396004 1000 qz222) (@Enclosure.Real.IsNear.mulLit_ff qz219 qz3 396004 1000 0 1 1335089 8388608 1 8388608 132175146089 2097152000 99001 2097152000 (Enclosure.Real.IsNear.const Bool.false 396004 1000) RS133to150.d36 rfl)) 

noncomputable abbrev qz910 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 396004 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz765 := qz910

noncomputable abbrev qz565 := qz765

noncomputable abbrev qz224 := qz565

noncomputable def Ns132p1705 := @Enclosure.Real.IsNear.sqrt_image qz224 16649065 2097152 13 4194304 11817885 11817891 4194304 (@Enclosure.Real.IsNear.recentre' qz224 Bool.false 66596260 8388608 26 8388608 16649065 2097152 13 4194304 (Ns132p1704 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns132p1706 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz224) 369309 131072 3 4194304 1488606 1488607 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz224) Bool.false 23635776 8388608 6 8388608 369309 131072 3 4194304 (Ns132p1705 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns132p1707 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz224)) Bool.false 2977213 8388608 1 8388608 2977213 8388608 1 8388608 (Ns132p1706 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz225 := (@HMul.hMul Real Real Real qz339 qz337 qz558)

noncomputable abbrev qz766 := (@HMul.hMul Real Real Real qz843 qz909 qz909)

noncomputable abbrev qz566 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz766 qz759) qz640)

noncomputable abbrev qz226 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz566))

noncomputable def Ns132p1708 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz221) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz225)) qz226) Bool.false 27683019673575 

noncomputable def Ns132p1709 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz225)) qz226 9047315 8388608 197 

noncomputable def Ns132p1710 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz225)) Bool.false 9047315 8388608 197 8388608 9047315 8388608 197 

noncomputable def Ns132p1711 := @Enclosure.Real.IsNear.recentre' (Real.cos qz225) Bool.false 7777859 8388608 72228718 3587233021952 7777859 8388608 36114359 1793616510976 

noncomputable def Ns132p1712 := @Enclosure.Real.IsNear.cos_image qz225 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6185799) qz384) Bool.false 6185799 1048576 41 2097152 Bool.false 7777859 8388608 1 

noncomputable def Ns132p1713 := nat_lit 70163796070279954104072351 

noncomputable def Ns132p1714 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz221 884279719003555 140737488355328 1 500000000000000 1969001 2097152 13 4194304 1741147650997718798555 295147905179352825856 Ns132p1713 

noncomputable def Ns132p1715 := @Enclosure.Real.IsNear.subLit_ff_p qz224 qz1 16649065 2097152 13 4194304 7 1 0 1 1969001 1969001 2097152 13 

noncomputable def Ns132p1716 := @Ns132p1715 4194304 (@Enclosure.Real.IsNear.recentre' qz224 Bool.false 66596260 8388608 26 8388608 16649065 2097152 13 4194304 (Ns132p1704 rfl rfl rfl rfl rfl rfl) rfl) qz366 

noncomputable def Ns132p1717 := @Enclosure.Real.IsNear.recentre' qz225 Bool.false 1741147650997718798555 295147905179352825856 Ns132p1713 Ns132p1410 6185799 1048576 41 2097152 (@Ns132p1714 Ns132p1410 RS133to150.d35 (Ns132p1716 rfl rfl) rfl) 

noncomputable def Ns132p1718 := nat_lit 45562425747705287015043864132311008957292524713496142320135570379545037215396647731200 

noncomputable def Ns132p1719 := nat_lit 29875937927927268060635879917535311786159893667678113359414818950898432911354167296 

noncomputable def Ns132p1720 := nat_lit 119281792106392440891111947969519490097636162993218417702535060334792690482277599215616 

noncomputable def Ns132p1721 := BSN.sin_dyadic_bound_f 20389904588 17179869184 3 2 8388608 3424393 Ns132p1718 Ns132p99 Ns132p1719 Ns132p1720 Ns132p102 Ns132p1719 7777859 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 20389904588) qz355 0 2 Ns132p1718 Ns132p99 Ns132p1719 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 20389904588) qz356 0 2 Ns132p1720 Ns132p102 Ns132p1719 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1722 := @Ns132p1712 1710526 (Ns132p1717 rfl) (Enclosure.sfrac_false_div 6185799 1048576) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6185799) qz384) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 179351497477627721023488) (@Nat.cast Real Real.instNatCast 151115727451828646838272)) 226375608064910080 72057594037927936 Bool.false 7777859 8388608 0 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 6185799 1048576 226375608064910080 72057594037927936 0 179351497477627721023488 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 7777859 8388608 179351497477627721023488 151115727451828646838272 20389904588 17179869184 3424393 3421052 (Ns132p1721 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p1723 := @Enclosure.Real.IsNear.inv_image (Real.cos qz225) 7777859 8388608 36114359 1793616510976 4523559 4523756 4194304 (Ns132p1711 (Ns132p1722 rfl rfl) rfl) rfl 

noncomputable def Ns132p1724 := @Enclosure.Real.IsNear.recentre' qz226 Bool.false 3059805 4194304 

noncomputable abbrev qz227 := (@HMul.hMul Real Real Real qz339 qz337 qz566)

noncomputable def Ns132p1725 := @Enclosure.Real.IsNear.cos_image qz227 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 6318171)) qz365) Bool.true 6318171 8388608 

noncomputable def Ns132p1726 := nat_lit 466198770935734321448807725 

noncomputable def Ns132p1727 := nat_lit 4234497705343897819924636765486251 

noncomputable def Ns132p1728 := @Enclosure.Real.IsNear.recentre' qz227 Bool.true Ns132p1726 Ns132p1121 Ns132p1727 

noncomputable abbrev qz228 := qz566

noncomputable def Ns132p1729 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz228 884279719003555 140737488355328 1 500000000000000 527207354095 

noncomputable abbrev qz567 := (@HSub.hSub Real Real Real qz635 qz766 qz759)

noncomputable abbrev qz229 := qz567

noncomputable def Ns132p1730 := @Enclosure.Real.IsNear.subLit_tf qz229 qz27 252329447151 4398046511104 156914173 17592186044416 1 16 

noncomputable abbrev qz568 := qz766

noncomputable abbrev qz230 := qz568

noncomputable def Ns132p1731 := @Enclosure.Real.IsNear.subLit_ff_n qz230 qz221 3876964938001 4398046511104 102388221 17592186044416 1969001 2097152 13 4194304 

noncomputable def Ns132p1732 := @Enclosure.Real.IsNear.mulLit_ff qz221 qz221 1969001 2097152 13 4194304 1969001 2097152 13 4194304 3876964938001 4398046511104 

noncomputable def Ns132p1733 := nat_lit 13259207586836661334667418757510458108885850517572672790241 

noncomputable def Ns132p1734 := nat_lit 2539399364407877887193751425123108974155519300795342561 

noncomputable def Ns132p1735 := nat_lit 39772543961781168248227868769681128108709240514116427685601 

noncomputable def Ns132p1736 := BSN.cos_dyadic_bound_f 6318171 8388608 3 2 4194304 1710526 Ns132p1733 Ns132p929 Ns132p1734 Ns132p1735 Ns132p932 Ns132p1734 3059805 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 6318171) (BSN.cosEvenQ 8388608) 0 2 Ns132p1733 Ns132p929 Ns132p1734 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 6318171) (BSN.cosOddQ 8388608) 0 2 Ns132p1735 Ns132p932 Ns132p1734 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1737 := @Ns132p1724 814046354 14348932087808 3059805 4194304 407023177 7174466043904 (@Ns132p1725 471 8388608 Bool.false 3059805 4194304 1 1710526 (@Ns132p1728 Ns132p174 6318171 8388608 471 8388608 (@Ns132p1729 4398046511104 156914173 17592186044416 Ns132p1726 Ns132p1121 Ns132p1727 Ns132p174 RS133to150.d35 (@Ns132p1730 0 1 8435317665520 527207354095 4398046511104 156914173 17592186044416 (@Ns132p1731 529173204751613952 252329447151 4398046511104 156914173 17592186044416 (@Ns132p1732 102388221 17592186044416 (Ns132p1716 rfl rfl) (Ns132p1716 rfl rfl) rfl) (Ns132p1716 rfl rfl) rfl rfl) qz372 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 6318171 8388608) (BSN.cos_neg_of_bound 6318171 8388608 Bool.false 3059805 4194304 1 1710526 (Ns132p1736 rfl rfl)) rfl rfl) 

noncomputable def Ns132p1738 := @Ns132p1702 7040404959844840912963 Ns132p1641 (Ns132p1703 qz29 (@Enclosure.Real.IsNear.of_eq qz764 (@Inv.inv Real Real.instInv (Real.sqrt qz224)) Bool.false 2977213 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz220 (BSN.t_div_two_pi_nonneg qz219 396004 1000 qz222)) Ns132p1707) rfl) (@Ns132p1708 35184372088832 2356810325824667 30091891625810722816 (BSN.correction_mk qz221 (BSN.cos_two_pi_p_ne_zero_mk qz219 396004 1000 7 qz222 rfl rfl (@BSN.floor_sqrt_eq_dec qz219 396004 1000 7 qz222 rfl rfl rfl))) (@Ns132p1709 8388608 3059805 4194304 407023177 7174466043904 27683019673575 35184372088832 2356810325824667 30091891625810722816 (@Ns132p1710 8388608 (Ns132p1723 rfl rfl rfl rfl rfl) rfl) (Ns132p1737 rfl) rfl)) 

noncomputable def Ns132p1739 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz219) (hardyZApproximantRS₀ qz219) Bool.false 157642380800787929227 295147905179352825856 406480174400856375572547 Ns132p1641 (@Eq.refl Real (hardyZApproximantRS₀ qz219)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz219) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz219) qz219 7) (@HMul.hMul Real Real Real qz5 qz760 (Zeta.RiemannSiegel.correction qz221))) Bool.false 157642380800787929227 295147905179352825856 406480174400856375572547 Ns132p1641 (BSN.hardyZApproximantRS₀_eq qz219 7 (@BSN.floor_sqrt_eq_dec qz219 396004 1000 7 qz222 rfl rfl rfl)) (@Ns132p1643 157642380800787929227 295147905179352825856 406480174400856375572547 Ns132p1641 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz219) qz219 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz219) qz219 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz219) qz219 7)) Bool.false 4275997 16777216 6637 4194304 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz219) qz219 7) (Ns132p1701 (Ns132p1700 rfl) rfl rfl)) (Ns132p1738 rfl) rfl rfl)) 

theorem RS133to150.d54 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz219) Bool.false 157642380800787929227 295147905179352825856 406480174400856375572547 Ns132p1641 := Ns132p1739 

noncomputable def Ns132p1740 := nat_lit 1988133539508622859419254784 

noncomputable abbrev qz911 := (Enclosure.sfrac Bool.false 397519 1000)

noncomputable abbrev qz767 := qz911

noncomputable abbrev qz569 := qz767

noncomputable abbrev qz231 := qz569

noncomputable abbrev qz912 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 397519 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz768 := qz912

noncomputable abbrev qz570 := qz768

noncomputable abbrev qz232 := qz570

noncomputable abbrev qz913 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 397519 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz769 := qz913

noncomputable abbrev qz571 := qz769

noncomputable abbrev qz233 := qz571

noncomputable abbrev qz770 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz232 qz9))

noncomputable def Ns132p1741 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz231) qz231 7) (@HMul.hMul Real Real Real qz5 qz770 (Zeta.RiemannSiegel.correction qz233)) 31815631 16777216 53303 33554432 21424631529670758375 73786976294838206464 1737873969201384848619 Ns132p64 Ns132p1740 

noncomputable def Ns132p1742 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz231) qz231 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 397519 1000 55 94 67108864 33554432 1125899906842624 Bool.false 41954863102 1293 

noncomputable def Ns132p1743 := Ns132p1742 120242927 40 27397080 8 130587807 40 25364760 8 Bool.true 61720303 39765 Bool.true 46195357 Bool.true 47321784 3537118876014220 1 Bool.false 42632578 Bool.false Bool.false 51104382 Bool.true Bool.true 63631262 

noncomputable def Ns132p1744 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz231) qz231 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 397519 1000 47 9 67108864 33554432 1125899906842624 Bool.false 41954863102 1293 

noncomputable def Ns132p1745 := Ns132p1744 93032624 40 33554424 8 108007536 40 30011992 8 Bool.true 57128546 23458 Bool.false 18152660 Bool.true 31455387 3537118876014220 1 Bool.false 17932103 Bool.false Bool.false 30316181 Bool.true Bool.true 61720303 

noncomputable def Ns132p1746 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz231) qz231 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 397519 1000 222 119 67108864 33554432 1125899906842624 Bool.false 41954863102 1293 

noncomputable def Ns132p1747 := Ns132p1746 46516304 40 47453136 16 73726608 40 38745320 8 Bool.true 67108840 1344 Bool.false 61761183 Bool.false 102827125 3537118876014220 1 Bool.false 40639170 Bool.true Bool.false 67058997 Bool.false Bool.true 57128546 

noncomputable def Ns132p1748 := nat_lit 399957739336762964478346487918239840237313585573292243199 

noncomputable def Ns132p1749 := nat_lit 639752046606640788491793550620933301414364379611136000 

noncomputable def Ns132p1750 := nat_lit 4764665690959075200502558527520000 

noncomputable def Ns132p1751 := nat_lit 11364279235100141613866383327663337280 

noncomputable abbrev qz771 := (@Eq.refl Real qz911)

noncomputable abbrev qz572 := qz771

noncomputable abbrev qz234 := qz572

noncomputable def Ns132p1752 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz231 397519 1000 632086421444 16000000 795038 4000 2000 Ns132p1750 Ns132p1751 qz234 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns132p1753 := nat_lit 127986476587764148633070876133836748875940347383453517823680 

noncomputable abbrev qz772 := (Real.log (Enclosure.sfrac Bool.false 632086421444 16000000))

noncomputable abbrev qz235 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 397519 4000) qz772) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 795038))))))

noncomputable abbrev qz773 := (Enclosure.sfrac Bool.false 397519 2000)

noncomputable abbrev qz573 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz235 qz773) (@HMul.hMul Real Real Real qz5 qz773 (Real.log Real.pi)))

noncomputable def Ns132p1754 := @Enclosure.Real.IsNear.addLit_ft_p qz573 (Enclosure.sfrac Bool.true Ns132p1750 Ns132p1751) 11262180361165936900631 18014398509481984000 3372754399123448136121 Ns132p199 Ns132p1750 Ns132p1751 0 1 Ns132p1753 

noncomputable def Ns132p1755 := nat_lit 151158426040191148179405458636800 

noncomputable abbrev qz574 := (@HSub.hSub Real Real Real qz12 qz235 qz773)

noncomputable abbrev qz575 := (@HMul.hMul Real Real Real qz5 qz773 (Real.log Real.pi))

noncomputable def Ns132p1756 := @Enclosure.Real.IsNear.subLit_ff_p qz574 qz575 3072184659786926151787 3602879701896396800 5068988520035403791 684210400000000000000000 15269007301959 67108864000 397519 33554432000 Ns132p1755 11262180361165936900631 18014398509481984000 

noncomputable def Ns132p1757 := nat_lit 30721846597869261517870000 

noncomputable abbrev qz576 := qz773

noncomputable def Ns132p1758 := @Enclosure.Real.IsNear.subLit_ff_p qz235 qz576 18941456139480015157783 18014398509481984000 5068988520035403791 684210400000000000000000 397519 2000 0 1 Ns132p1757 3072184659786926151787 3602879701896396800 5068988520035403791 684210400000000000000000 

noncomputable def Ns132p1759 := nat_lit 42652367405808394986199326321419485184 

noncomputable def Ns132p1760 := nat_lit 12795503792087677420961792 

noncomputable def Ns132p1761 := nat_lit 251061523062814821026724068113861625088017691512897894309442753814924922880 

noncomputable def Ns132p1762 := nat_lit 731070579507522110052724502933314740531922225444325369488748594902757376 

noncomputable def Ns132p1763 := nat_lit 23537789069031056621975100676166893168422524012030655652189972131840 

noncomputable def Ns132p1764 := BSN.log_dyadic_bound 107798421444 1156374421444 4 3 Ns132p1761 33554432 13684208 Ns132p1762 Ns132p1763 6274174 1264172842888 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 107798421444) (BSN.artanhQ 1156374421444) 0 3 Ns132p1762 Ns132p1761 Ns132p1763 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns132p1765 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 397519 4000) qz772 397519 4000 0 1 47666966140596857 4503599627370496 12500002565789 171052600000000000000 18948524713243921997783 18014398509481984000 4968988519949877491 684210400000000000000000 (Enclosure.Real.IsNear.const Bool.false 397519 4000) (BSN.isNear_log_sfrac 632086421444 16000000 47666966140596857 4503599627370496 12500002565789 171052600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 632086421444) qz350)) Bool.false Ns132p1760 Ns132p87 1000000205263120 13684208000000000000000 47666966140596857 4503599627370496 12500002565789 171052600000000000000 (BSN.log_rat_reduce_isNear 632086421444 16000000 15 1264172842888 1048576000000 6274174 33554432 24973259072661432 36028797018963968 13684208 1000000000000000 rfl rfl rfl rfl (Ns132p1764 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns132p1766 := BSN.arctan_dyadic_bound_f 1000 795038 1 0 4194304 1710526 0 1 1 0 1 1 5275 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 795038) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 795038) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz577 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 795038)))

noncomputable def Ns132p1767 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz577 884279719003555 562949953421312 1 2000000000000000 5275 4194304 1 1710526 3705968401531189329920 883571720488355 562949953421312 1000000000855263 1710526000000000000000 qz17 (Ns132p1766 rfl) rfl rfl 

noncomputable def Ns132p1768 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 397519 4000) qz772) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz577)) 18948524713243921997783 18014398509481984000 4968988519949877491 684210400000000000000000 883571720488355 2251799813685248 1000000000855263 6842104000000000000000 Ns132p1759 18941456139480015157783 18014398509481984000 5068988520035403791 684210400000000000000000 (Ns132p1765 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz577) 1 4 0 1 883571720488355 562949953421312 1000000000855263 1710526000000000000000 883571720488355 2251799813685248 1000000000855263 6842104000000000000000 qz353 Ns132p1767 rfl) 

noncomputable def Ns132p1769 := @Ns132p1754 Ns132p1748 Ns132p1749 3372754399123448136121 Ns132p199 (@Ns132p1756 3372754399123448136121 Ns132p199 (Ns132p1758 (Ns132p1768 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 397519 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz576 (Real.log Real.pi) 397519 2000 0 1 38410761 33554432 1 16777216 15269007301959 67108864000 397519 33554432000 (Enclosure.Real.IsNear.const Bool.false 397519 2000) RS133to150.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns132p1750 Ns132p1751) 

noncomputable def Ns132p1770 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz231) Bool.false Ns132p1748 Ns132p1749 3372754399123448136121 Ns132p199 5244357887 8388608 163 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz231) (@HAdd.hAdd Real Real Real qz354 qz573 (Enclosure.sfrac Bool.true Ns132p1750 Ns132p1751)) Bool.false Ns132p1748 Ns132p1749 3372754399123448136121 Ns132p199 Ns132p1752 (Ns132p1769 rfl rfl)) 

noncomputable def Ns132p1771 := nat_lit 1898057205289917700112384 

noncomputable def Ns132p1772 := nat_lit 139717549871522554783870466917306406216214459580361346728582433081059826640187700330625 

noncomputable def Ns132p1773 := nat_lit 280179254277641959980519584272437385897767374113531306960471634689939551971062890625 

noncomputable def Ns132p1774 := nat_lit 365473292775633366022549429266028070036727199342857809792160846851372977163967018090625 

noncomputable def Ns132p1775 := BSN.sin_dyadic_bound_f 26973015185 17179869184 3 2 8388608 3424393 Ns132p1772 Ns132p99 Ns132p1773 Ns132p1774 Ns132p102 Ns132p1773 8388605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26973015185) qz355 0 2 Ns132p1772 Ns132p99 Ns132p1773 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26973015185) qz356 0 2 Ns132p1774 Ns132p102 Ns132p1773 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1776 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz231) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5244357887) qz365) Bool.false 5244357887 8388608 163 8388608 Bool.true 8388605 8388608 1 1710526 (Ns132p1770 rfl) (Enclosure.sfrac_false_div 5244357887 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5244357887) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns132p1771) qz367) 226375608064910080 72057594037927936 Bool.false 8388605 8388608 99 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q1 5244357887 8388608 226375608064910080 72057594037927936 99 Ns132p1771 Ns132p87 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388605 8388608 Ns132p1771 Ns132p87 26973015185 17179869184 3424393 3421052 (Ns132p1775 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p1777 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz231) Bool.false Ns132p1748 Ns132p1749 3372754399123448136121 Ns132p199 41954863102 67108864 1293 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz231) (@HAdd.hAdd Real Real Real qz354 qz573 (Enclosure.sfrac Bool.true Ns132p1750 Ns132p1751)) Bool.false Ns132p1748 Ns132p1749 3372754399123448136121 Ns132p199 Ns132p1752 (Ns132p1769 rfl rfl)) 

noncomputable def Ns132p1778 := Ns132p1747 23458 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 222 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 40639170 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 119 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 67058997 67108864) qz234 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 1) Bool.true 8388605 8388608 143602173 7174466043904 67108840 67108864 1344 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz231)) Bool.true 8388605 8388608 143602173 7174466043904 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz231) qz231) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz231)) Bool.true 8388605 8388608 287204346 14348932087808 8388605 8388608 143602173 7174466043904 (Ns132p1776 rfl rfl) rfl)) rfl) (Ns132p1777 rfl) RS133to150.d7 

noncomputable def Ns132p1779 := nat_lit 495994272683209510150184466486991615463273751655512128898498149121 

noncomputable def Ns132p1780 := nat_lit 211701945222253944942069597959017886808046222359676710342736641 

noncomputable def Ns132p1781 := nat_lit 1487559414159184022560669260265056810616205162521817033274808974081 

noncomputable def Ns132p1782 := BSN.cos_dyadic_bound_f 61761183 67108864 3 2 67108864 33554432 Ns132p1779 Ns132p124 Ns132p1780 Ns132p1781 Ns132p127 Ns132p1780 40639170 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 61761183) qz360 0 2 Ns132p1779 Ns132p124 Ns132p1780 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 61761183) (BSN.cosOddQ 67108864) 0 2 Ns132p1781 Ns132p127 Ns132p1780 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1783 := nat_lit 2390892718551402003964997483992582597527755141225067051465965006327776754581574893787934509390869140625 

noncomputable def Ns132p1784 := nat_lit 1397308559940268268182819604365106132980059207090831086999548064864056665101088583469390869140625 

noncomputable def Ns132p1785 := nat_lit 11941012266564057696965009174842712127954351130445005384191350267836286078872574064585338669390869140625 

noncomputable def Ns132p1786 := BSN.sin_dyadic_bound_f 102827125 67108864 4 3 67108864 33554432 Ns132p1783 Ns132p233 Ns132p1784 Ns132p1785 Ns132p236 Ns132p1784 67058997 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 102827125) qz359 0 3 Ns132p1783 Ns132p233 Ns132p1784 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 102827125) (BSN.sinOddQ 67108864) 0 3 Ns132p1785 Ns132p236 Ns132p1784 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1787 := nat_lit 108582814248297507633715360000 

noncomputable def Ns132p1788 := BSN.sin_dyadic_bound_f 18152660 67108864 2 1 67108864 33554432 Ns132p1787 Ns132p114 Ns132p1787 Ns132p1787 Ns132p115 Ns132p1787 17932103 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 18152660) qz359 0 1 Ns132p1787 Ns132p114 Ns132p1787 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 18152660) (BSN.sinOddQ 67108864) 0 1 Ns132p1787 Ns132p115 Ns132p1787 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1789 := nat_lit 978994227279144996628850213361 

noncomputable def Ns132p1790 := BSN.sin_dyadic_bound_f 31455387 67108864 2 1 67108864 33554432 Ns132p1789 Ns132p114 Ns132p1789 Ns132p1789 Ns132p115 Ns132p1789 30316181 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 31455387) qz359 0 1 Ns132p1789 Ns132p114 Ns132p1789 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 31455387) (BSN.sinOddQ 67108864) 0 1 Ns132p1789 Ns132p115 Ns132p1789 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1791 := Ns132p1745 39765 BSN.abs_quadSignPos (BSN.cos_quad_nat3 47 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 17932103 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 9 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 30316181 67108864) qz234 rfl rfl (Ns132p1778 RS133to150.d9 RS133to150.d11 RS133to150.d13 RS133to150.d17 (Ns132p1782 rfl rfl) (Ns132p1786 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns132p1777 rfl) RS133to150.d19 RS133to150.d21 RS133to150.d23 RS133to150.d25 RS133to150.d17 (Ns132p1788 rfl rfl) (Ns132p1790 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns132p1792 := nat_lit 279335988196149497753157252628016647870124941254019024349055885985 

noncomputable def Ns132p1793 := nat_lit 20738943176375293235619407514978107550005002174687035821335201 

noncomputable def Ns132p1794 := nat_lit 731560677462867886497792277842162208438103409471290808570483253921 

noncomputable def Ns132p1795 := BSN.sin_dyadic_bound_f 46195357 67108864 3 2 67108864 33554432 Ns132p1792 Ns132p108 Ns132p1793 Ns132p1794 Ns132p111 Ns132p1793 42632578 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 46195357) qz359 0 2 Ns132p1792 Ns132p108 Ns132p1793 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 46195357) (BSN.sinOddQ 67108864) 0 2 Ns132p1794 Ns132p111 Ns132p1793 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1796 := nat_lit 170898077096395455832075504725084344014887891529940238391968792576 

noncomputable def Ns132p1797 := nat_lit 25147155716171525862391595608852148774140263417089074340560896 

noncomputable def Ns132p1798 := nat_lit 512643936977754024444501730984035327747115394062986537027225255936 

noncomputable def Ns132p1799 := BSN.cos_dyadic_bound_f 47321784 67108864 3 2 67108864 33554432 Ns132p1796 Ns132p124 Ns132p1797 Ns132p1798 Ns132p127 Ns132p1797 51104382 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 47321784) qz360 0 2 Ns132p1796 Ns132p124 Ns132p1797 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 47321784) (BSN.cosOddQ 67108864) 0 2 Ns132p1798 Ns132p127 Ns132p1797 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1800 := Ns132p1743 53303 BSN.abs_quadSignPos (BSN.cos_quad_nat3 55 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 42632578 67108864) BSN.abs_quadSignNeg qz728 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 51104382 67108864) qz234 rfl rfl (Ns132p1791 rfl rfl) (Ns132p1777 rfl) RS133to150.d27 RS133to150.d29 RS133to150.d31 RS133to150.d33 RS133to150.d17 (Ns132p1795 rfl rfl) (Ns132p1799 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns132p1801 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 7) 63631262 67108864 53303 67108864 63631262 67108864 53303 67108864 8540443415412736 31815631 16777216 53303 33554432 (Ns132p1800 rfl) 

noncomputable def Ns132p1802 := @Enclosure.Real.IsNear.mulLit_tf qz770 (Zeta.RiemannSiegel.correction qz233) 743593 2097152 1 4194304 28812309327375 35184372088832 2320559442955399 30091891625810722816 21424631529670758375 73786976294838206464 

noncomputable abbrev qz774 := (@HPow.hPow Real Real Real qz7 qz232 qz9)

noncomputable def Ns132p1803 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz774 1 1 0 1 743593 2097152 1 4194304 743593 2097152 1 4194304 

noncomputable def Ns132p1804 := @Enclosure.Real.IsNear.sqrt_image qz232 530723244191 8388608000 397519 8388608000 33361751 33361777 4194304 (@Enclosure.Real.IsNear.of_eq qz232 (@HMul.hMul Real Real Real qz5 qz231 qz3) Bool.false 530723244191 8388608000 397519 8388608000 (BSN.t_div_two_pi_mk qz231 397519 1000 qz234) (@Enclosure.Real.IsNear.mulLit_ff qz231 qz3 397519 1000 0 1 1335089 8388608 1 8388608 530723244191 8388608000 397519 8388608000 (Enclosure.Real.IsNear.const Bool.false 397519 1000) RS133to150.d36 rfl)) 

noncomputable abbrev qz914 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 397519 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz775 := qz914

noncomputable abbrev qz578 := qz775

noncomputable abbrev qz236 := qz578

noncomputable def Ns132p1805 := @Enclosure.Real.IsNear.sqrt_image qz236 8340441 1048576 13 4194304 11829172 11829178 4194304 (@Enclosure.Real.IsNear.recentre' qz236 Bool.false 66723528 8388608 26 8388608 8340441 1048576 13 4194304 (Ns132p1804 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns132p1806 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz236) 11829175 4194304 3 4194304 1487185 1487187 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz236) Bool.false 23658350 8388608 6 8388608 11829175 4194304 3 4194304 (Ns132p1805 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns132p1807 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz236)) Bool.false 2974372 8388608 2 8388608 743593 2097152 1 4194304 (Ns132p1806 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz237 := (@HMul.hMul Real Real Real qz339 qz337 qz571)

noncomputable abbrev qz776 := (@HMul.hMul Real Real Real qz843 qz913 qz913)

noncomputable abbrev qz579 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz776 qz769) qz640)

noncomputable abbrev qz238 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz579))

noncomputable def Ns132p1808 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz233) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz237)) qz238) Bool.false 28812309327375 

noncomputable def Ns132p1809 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz237)) qz238 8750559 8388608 185 

noncomputable def Ns132p1810 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz237)) Bool.false 8750559 8388608 185 8388608 8750559 8388608 185 

noncomputable def Ns132p1811 := @Enclosure.Real.IsNear.recentre' (Real.cos qz237) Bool.false 8041629 8388608 72228718 3587233021952 8041629 8388608 36114359 1793616510976 

noncomputable def Ns132p1812 := @Enclosure.Real.IsNear.cos_image qz237 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50286041) qz365) Bool.false 50286041 8388608 41 2097152 Bool.false 8041629 8388608 1 

noncomputable def Ns132p1813 := nat_lit 350818980351946382418189083 

noncomputable def Ns132p1814 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz233 884279719003555 140737488355328 1 500000000000000 1000409 1048576 13 4194304 884641389408627453995 147573952589676412928 Ns132p1813 

noncomputable def Ns132p1815 := @Enclosure.Real.IsNear.subLit_ff_p qz236 qz1 8340441 1048576 13 4194304 7 1 0 1 1000409 1000409 1048576 13 

noncomputable def Ns132p1816 := @Ns132p1815 4194304 (@Enclosure.Real.IsNear.recentre' qz236 Bool.false 66723528 8388608 26 8388608 8340441 1048576 13 4194304 (Ns132p1804 rfl rfl rfl rfl rfl rfl) rfl) qz366 

noncomputable def Ns132p1817 := @Enclosure.Real.IsNear.recentre' qz237 Bool.false 884641389408627453995 147573952589676412928 Ns132p1813 Ns132p153 50286041 8388608 41 2097152 (@Ns132p1814 Ns132p153 RS133to150.d35 (Ns132p1816 rfl rfl) rfl) 

noncomputable def Ns132p1818 := nat_lit 1550053545850691840376832 

noncomputable def Ns132p1819 := nat_lit 62075005585401612873317683077812803417800798896078588127505660795641874715222384640000 

noncomputable def Ns132p1820 := nat_lit 55428765082633783367293204130446931749697302099606284464164608667628183577600000000 

noncomputable def Ns132p1821 := nat_lit 162487653770679959971332600016155666299978772905377892063858559384076369099790131200000 

noncomputable def Ns132p1822 := BSN.sin_dyadic_bound_f 22027585740 17179869184 3 2 8388608 3424393 Ns132p1819 Ns132p99 Ns132p1820 Ns132p1821 Ns132p102 Ns132p1820 8041629 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 22027585740) qz355 0 2 Ns132p1819 Ns132p99 Ns132p1820 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 22027585740) qz356 0 2 Ns132p1821 Ns132p102 Ns132p1820 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1823 := @Ns132p1812 1710526 (Ns132p1817 rfl) (Enclosure.sfrac_false_div 50286041 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50286041) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns132p1818) qz367) 226375608064910080 72057594037927936 Bool.false 8041629 8388608 0 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 50286041 8388608 226375608064910080 72057594037927936 0 Ns132p1818 Ns132p87 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8041629 8388608 Ns132p1818 Ns132p87 22027585740 17179869184 3424393 3421052 (Ns132p1822 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p1824 := @Enclosure.Real.IsNear.inv_image (Real.cos qz237) 8041629 8388608 36114359 1793616510976 4375187 4375372 4194304 (Ns132p1811 (Ns132p1823 rfl rfl) rfl) rfl 

noncomputable def Ns132p1825 := @Enclosure.Real.IsNear.recentre' qz238 Bool.false 3292625 4194304 

noncomputable abbrev qz239 := (@HMul.hMul Real Real Real qz339 qz337 qz579)

noncomputable def Ns132p1826 := @Enclosure.Real.IsNear.cos_image qz239 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 5604119)) qz365) Bool.true 5604119 8388608 

noncomputable def Ns132p1827 := nat_lit 103377761381826773500373645 

noncomputable def Ns132p1828 := nat_lit 154742504910672534362390528 

noncomputable def Ns132p1829 := nat_lit 4279145735328907404299749320996727 

noncomputable def Ns132p1830 := @Enclosure.Real.IsNear.recentre' qz239 Bool.true Ns132p1827 Ns132p1828 Ns132p1829 

noncomputable abbrev qz240 := qz579

noncomputable def Ns132p1831 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz240 884279719003555 140737488355328 1 500000000000000 116906177039 

noncomputable abbrev qz580 := (@HSub.hSub Real Real Real qz635 qz776 qz769)

noncomputable abbrev qz241 := qz580

noncomputable def Ns132p1832 := @Enclosure.Real.IsNear.subLit_tf qz241 qz27 48186700303 1099511627776 158568657 17592186044416 1 16 

noncomputable abbrev qz581 := qz776

noncomputable abbrev qz242 := qz581

noncomputable def Ns132p1833 := @Enclosure.Real.IsNear.subLit_ff_n qz242 qz233 1000818167281 1099511627776 104042705 17592186044416 1000409 1048576 13 4194304 

noncomputable def Ns132p1834 := @Enclosure.Real.IsNear.mulLit_ff qz233 qz233 1000409 1048576 13 4194304 1000409 1048576 13 4194304 1000818167281 1099511627776 

noncomputable def Ns132p1835 := nat_lit 8206344925783030108436373689270201642383218893484488685121 

noncomputable def Ns132p1836 := nat_lit 972878911345610512551235657952185853308961012736882241 

noncomputable def Ns132p1837 := nat_lit 24617089019526399104284018596494700555443038758427992290881 

noncomputable def Ns132p1838 := BSN.cos_dyadic_bound_f 5604119 8388608 3 2 4194304 1710526 Ns132p1835 Ns132p929 Ns132p1836 Ns132p1837 Ns132p932 Ns132p1836 3292625 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 5604119) (BSN.cosEvenQ 8388608) 0 2 Ns132p1835 Ns132p929 Ns132p1836 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 5604119) (BSN.cosOddQ 8388608) 0 2 Ns132p1837 Ns132p932 Ns132p1836 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1839 := @Ns132p1825 205649746 3587233021952 3292625 4194304 102824873 1793616510976 (@Ns132p1826 119 2097152 Bool.false 3292625 4194304 1 1710526 (@Ns132p1830 Ns132p174 5604119 8388608 119 2097152 (@Ns132p1831 1099511627776 158568657 17592186044416 Ns132p1827 Ns132p1828 Ns132p1829 Ns132p174 RS133to150.d35 (@Ns132p1832 0 1 1870498832624 116906177039 1099511627776 158568657 17592186044416 (@Ns132p1833 50527417456918528 48186700303 1099511627776 158568657 17592186044416 (@Ns132p1834 104042705 17592186044416 (Ns132p1816 rfl rfl) (Ns132p1816 rfl rfl) rfl) (Ns132p1816 rfl rfl) rfl rfl) qz372 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 5604119 8388608) (BSN.cos_neg_of_bound 5604119 8388608 Bool.false 3292625 4194304 1 1710526 (Ns132p1838 rfl rfl)) rfl rfl) 

noncomputable def Ns132p1840 := @Ns132p1802 1737873969201384848619 Ns132p64 (Ns132p1803 qz29 (@Enclosure.Real.IsNear.of_eq qz774 (@Inv.inv Real Real.instInv (Real.sqrt qz236)) Bool.false 743593 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz232 (BSN.t_div_two_pi_nonneg qz231 397519 1000 qz234)) Ns132p1807) rfl) (@Ns132p1808 35184372088832 2320559442955399 30091891625810722816 (BSN.correction_mk qz233 (BSN.cos_two_pi_p_ne_zero_mk qz231 397519 1000 7 qz234 rfl rfl (@BSN.floor_sqrt_eq_dec qz231 397519 1000 7 qz234 rfl rfl rfl))) (@Ns132p1809 8388608 3292625 4194304 102824873 1793616510976 28812309327375 35184372088832 2320559442955399 30091891625810722816 (@Ns132p1810 8388608 (Ns132p1824 rfl rfl rfl rfl rfl) rfl) (Ns132p1839 rfl) rfl)) 

noncomputable def Ns132p1841 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz231) (hardyZApproximantRS₀ qz231) Bool.true 118501993388451508249 73786976294838206464 101987130177363194739947 Ns132p64 (@Eq.refl Real (hardyZApproximantRS₀ qz231)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz231) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz231) qz231 7) (@HMul.hMul Real Real Real qz5 qz770 (Zeta.RiemannSiegel.correction qz233))) Bool.true 118501993388451508249 73786976294838206464 101987130177363194739947 Ns132p64 (BSN.hardyZApproximantRS₀_eq qz231 7 (@BSN.floor_sqrt_eq_dec qz231 397519 1000 7 qz234 rfl rfl rfl)) (@Ns132p1741 118501993388451508249 73786976294838206464 101987130177363194739947 Ns132p64 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz231) qz231 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 7)) Bool.true 31815631 16777216 53303 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz231) qz231 7) (Ns132p1801 (Ns132p1800 rfl) rfl rfl)) (Ns132p1840 rfl) rfl rfl)) 

theorem RS133to150.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz231) Bool.true 118501993388451508249 73786976294838206464 101987130177363194739947 Ns132p64 := Ns132p1841 

noncomputable def Ns132p1842 := nat_lit 5671281684276825777460215808 

noncomputable abbrev qz915 := (Enclosure.sfrac Bool.false 399034 1000)

noncomputable abbrev qz777 := qz915

noncomputable abbrev qz582 := qz777

noncomputable abbrev qz243 := qz582

noncomputable abbrev qz916 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 399034 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz778 := qz916

noncomputable abbrev qz583 := qz778

noncomputable abbrev qz244 := qz583

noncomputable abbrev qz917 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 399034 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz779 := qz917

noncomputable abbrev qz584 := qz779

noncomputable abbrev qz245 := qz584

noncomputable abbrev qz780 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz244 qz9))

noncomputable def Ns132p1843 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz243) qz243 7) (@HMul.hMul Real Real Real qz5 qz780 (Zeta.RiemannSiegel.correction qz245)) 143590469 33554432 13375 8388608 11137974802940356875 36893488147419103232 862693004878700006065 Ns132p333 Ns132p1842 

noncomputable def Ns132p1844 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz243) qz243 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 399034 1000 55 94 67108864 33554432 1125899906842624 Bool.false 42165791093 1298 

noncomputable def Ns132p1845 := Ns132p1844 120242927 40 27397080 8 130587807 40 25364760 8 Bool.false 158687635 39911 Bool.true 17435400 Bool.true 34234321 3537118876014220 1 Bool.false 17239912 Bool.false Bool.false 58564595 Bool.true Bool.false 143590469 

noncomputable def Ns132p1846 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz243) qz243 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 399034 1000 47 8 67108864 33554432 1125899906842624 Bool.false 42165791093 1298 

noncomputable def Ns132p1847 := Ns132p1846 93032624 40 33554424 8 108007536 40 30011992 8 Bool.false 119220422 23542 Bool.false 88136225 Bool.true 89573170 3537118876014220 1 Bool.false 64896872 Bool.false Bool.false 15694483 Bool.false Bool.false 158687635 

noncomputable def Ns132p1848 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz243) qz243 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 399034 1000 223 120 67108864 33554432 1125899906842624 Bool.false 42165791093 1298 

noncomputable def Ns132p1849 := Ns132p1848 46516304 40 47453136 16 73726608 40 38745320 8 Bool.false 67108840 1344 Bool.false 96802616 Bool.false 96644948 3537118876014220 1 Bool.false 66557071 Bool.false Bool.false 8744472 Bool.false Bool.false 119220422 

noncomputable def Ns132p1850 := nat_lit 3212877200747457451574330655787212831329436768826933793 

noncomputable def Ns132p1851 := nat_lit 5113447027174038902522221586465888673877073068032000 

noncomputable def Ns132p1852 := nat_lit 4856154249435745286672778603520000 

noncomputable def Ns132p1853 := nat_lit 11626632447528297467493352056557998080 

noncomputable abbrev qz918 := (@Eq.refl Real (Enclosure.sfrac Bool.false 399034 1000))

noncomputable abbrev qz781 := qz918

noncomputable abbrev qz585 := qz781

noncomputable abbrev qz246 := qz585

noncomputable def Ns132p1854 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz243 399034 1000 636913532624 16000000 798068 4000 2000 Ns132p1852 Ns132p1853 qz246 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns132p1855 := nat_lit 65799725071307928608242291830522118785626865025575604080640 

noncomputable abbrev qz782 := (Real.log (Enclosure.sfrac Bool.false 636913532624 16000000))

noncomputable abbrev qz247 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 399034 4000) qz782) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 798068))))))

noncomputable abbrev qz783 := (Enclosure.sfrac Bool.false 399034 2000)

noncomputable abbrev qz586 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz247 qz783) (@HMul.hMul Real Real Real qz5 qz783 (Real.log Real.pi)))

noncomputable def Ns132p1856 := @Enclosure.Real.IsNear.addLit_ft_p qz586 (Enclosure.sfrac Bool.true Ns132p1852 Ns132p1853) 5659400441926348109333 9007199254740992000 1692755434205400035003 Ns132p747 Ns132p1852 Ns132p1853 0 1 Ns132p1855 

noncomputable def Ns132p1857 := nat_lit 37979593457877519328588542771200 

noncomputable abbrev qz587 := (@HSub.hSub Real Real Real qz12 qz247 qz783)

noncomputable abbrev qz588 := (@HMul.hMul Real Real Real qz5 qz783 (Real.log Real.pi))

noncomputable def Ns132p1858 := @Enclosure.Real.IsNear.subLit_ff_p qz587 qz588 1543316469899006823121 1801439850948198400 2543963011961287063 342105200000000000000000 7663599802437 33554432000 199517 16777216000 Ns132p1857 5659400441926348109333 9007199254740992000 

noncomputable def Ns132p1859 := nat_lit 15433164698990068231210000 

noncomputable abbrev qz589 := qz783

noncomputable def Ns132p1860 := @Enclosure.Real.IsNear.subLit_ff_p qz247 qz589 9513671723203192616469 9007199254740992000 2543963011961287063 342105200000000000000000 399034 2000 0 1 Ns132p1859 1543316469899006823121 1801439850948198400 2543963011961287063 342105200000000000000000 

noncomputable def Ns132p1861 := nat_lit 21422884213771561415749416254347149312 

noncomputable def Ns132p1862 := nat_lit 12804701043246693447892992 

noncomputable def Ns132p1863 := nat_lit 257415622896972861298076522689615264801621722150964397463718405192789524480 

noncomputable def Ns132p1864 := nat_lit 811769882425107079232029215412259817149904713078207030791990076239773696 

noncomputable def Ns132p1865 := nat_lit 30613459211329639563940360453016338638634424884356261002999381360640 

noncomputable def Ns132p1866 := BSN.log_dyadic_bound 112625532624 1161201532624 4 3 Ns132p1863 33554432 13684208 Ns132p1864 Ns132p1865 6529449 1273827065248 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 112625532624) (BSN.artanhQ 1161201532624) 0 3 Ns132p1864 Ns132p1863 Ns132p1865 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns132p1867 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 399034 4000) qz782 399034 4000 0 1 47701228571112057 4503599627370496 12500002565789 171052600000000000000 9517206020822564276469 9007199254740992000 2493963011918523913 342105200000000000000000 (Enclosure.Real.IsNear.const Bool.false 399034 4000) (BSN.isNear_log_sfrac 636913532624 16000000 47701228571112057 4503599627370496 12500002565789 171052600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 636913532624) qz350)) Bool.false Ns132p1862 Ns132p87 1000000205263120 13684208000000000000000 47701228571112057 4503599627370496 12500002565789 171052600000000000000 (BSN.log_rat_reduce_isNear 636913532624 16000000 15 1273827065248 1048576000000 6529449 33554432 24973259072661432 36028797018963968 13684208 1000000000000000 rfl rfl rfl rfl (Ns132p1866 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns132p1868 := BSN.arctan_dyadic_bound_f 1000 798068 1 0 4194304 1710526 0 1 1 0 1 1 5255 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 798068) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 798068) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz590 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 798068)))

noncomputable def Ns132p1869 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz590 884279719003555 562949953421312 1 2000000000000000 5255 4194304 1 1710526 3705979660530257756160 883574404842915 562949953421312 1000000000855263 1710526000000000000000 qz17 (Ns132p1868 rfl) rfl rfl 

noncomputable def Ns132p1870 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 399034 4000) qz782) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz590)) 9517206020822564276469 9007199254740992000 2493963011918523913 342105200000000000000000 883574404842915 2251799813685248 1000000000855263 6842104000000000000000 Ns132p1861 9513671723203192616469 9007199254740992000 2543963011961287063 342105200000000000000000 (Ns132p1867 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz590) 1 4 0 1 883574404842915 562949953421312 1000000000855263 1710526000000000000000 883574404842915 2251799813685248 1000000000855263 6842104000000000000000 qz353 Ns132p1869 rfl) 

noncomputable def Ns132p1871 := @Ns132p1856 Ns132p1850 Ns132p1851 1692755434205400035003 Ns132p747 (@Ns132p1858 1692755434205400035003 Ns132p747 (Ns132p1860 (Ns132p1870 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 399034 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz589 (Real.log Real.pi) 399034 2000 0 1 38410761 33554432 1 16777216 7663599802437 33554432000 199517 16777216000 (Enclosure.Real.IsNear.const Bool.false 399034 2000) RS133to150.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns132p1852 Ns132p1853) 

noncomputable def Ns132p1872 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz243) Bool.false Ns132p1850 Ns132p1851 1692755434205400035003 Ns132p747 2635361943 4194304 163 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz243) (@HAdd.hAdd Real Real Real qz354 qz586 (Enclosure.sfrac Bool.true Ns132p1852 Ns132p1853)) Bool.false Ns132p1850 Ns132p1851 1692755434205400035003 Ns132p747 Ns132p1854 (Ns132p1871 rfl rfl)) 

noncomputable def Ns132p1873 := nat_lit 140245947595205360970318578859950334022332353661965324422792825837305448727824266233985 

noncomputable def Ns132p1874 := nat_lit 282298207864296902122776675523667095774438870724135941149752144863540138835886016641 

noncomputable def Ns132p1875 := nat_lit 366853760888995655175968925253783985236759453800165343869262564196497110252853072300161 

noncomputable def Ns132p1876 := BSN.sin_dyadic_bound_f 26998430319 17179869184 3 2 8388608 3424393 Ns132p1873 Ns132p99 Ns132p1874 Ns132p1875 Ns132p102 Ns132p1874 8388605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26998430319) qz355 0 2 Ns132p1873 Ns132p99 Ns132p1874 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26998430319) qz356 0 2 Ns132p1875 Ns132p102 Ns132p1874 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1877 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz243) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2635361943) qz357) Bool.false 2635361943 4194304 163 8388608 Bool.false 8388605 8388608 1 1710526 (Ns132p1872 rfl) (Enclosure.sfrac_false_div 2635361943 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2635361943) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949922818173203556335616) qz358) 226375608064910080 72057594037927936 Bool.false 8388605 8388608 99 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 2635361943 4194304 226375608064910080 72057594037927936 99 949922818173203556335616 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388605 8388608 949922818173203556335616 604462909807314587353088 26998430319 17179869184 3424393 3421052 (Ns132p1876 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p1878 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz243) Bool.false Ns132p1850 Ns132p1851 1692755434205400035003 Ns132p747 42165791093 67108864 1298 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz243) (@HAdd.hAdd Real Real Real qz354 qz586 (Enclosure.sfrac Bool.true Ns132p1852 Ns132p1853)) Bool.false Ns132p1850 Ns132p1851 1692755434205400035003 Ns132p747 Ns132p1854 (Ns132p1871 rfl rfl)) 

noncomputable def Ns132p1879 := Ns132p1849 23542 BSN.abs_quadSignPos (BSN.cos_quad_nat3 223 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66557071 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 120 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 8744472 67108864) qz246 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 1) Bool.false 8388605 8388608 143602173 7174466043904 67108840 67108864 1344 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz243)) Bool.false 8388605 8388608 143602173 7174466043904 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz243) qz243) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz243)) Bool.false 8388605 8388608 287204346 14348932087808 8388605 8388608 143602173 7174466043904 (Ns132p1877 rfl rfl) rfl)) rfl) (Ns132p1878 rfl) RS133to150.d7 

noncomputable def Ns132p1880 := nat_lit 1877189118945700548302665809670737079258962830102480898238347467420175629286872190526306408009151021056 

noncomputable def Ns132p1881 := nat_lit 677088014869016223602824799235671435084466978507059217575072923731687247200782739750345408249856 

noncomputable def Ns132p1882 := nat_lit 9377647820958154130452255253909576770454383797460628049038032191350367044321122790152679691910345916416 

noncomputable def Ns132p1883 := BSN.sin_dyadic_bound_f 96802616 67108864 4 3 67108864 33554432 Ns132p1880 Ns132p233 Ns132p1881 Ns132p1882 Ns132p236 Ns132p1881 66557071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 96802616) qz359 0 3 Ns132p1880 Ns132p233 Ns132p1881 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 96802616) (BSN.sinOddQ 67108864) 0 3 Ns132p1882 Ns132p236 Ns132p1881 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1884 := nat_lit 718112264944278306855207339754431766533360904903998786274487316036400706322611676133519096678004555776 

noncomputable def Ns132p1885 := nat_lit 663972176414522312717901644203204413294655376881376980160131549810469533906973559179643134672896 

noncomputable def Ns132p1886 := nat_lit 4349127379290473325888854021325157425623077585305048899882222456452580609845030632482937444023570268160 

noncomputable def Ns132p1887 := BSN.cos_dyadic_bound_f 96644948 67108864 4 3 67108864 33554432 Ns132p1884 Ns132p118 Ns132p1885 Ns132p1886 Ns132p121 Ns132p1885 8744472 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 96644948) qz360 0 3 Ns132p1884 Ns132p118 Ns132p1885 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 96644948) (BSN.cosOddQ 67108864) 0 3 Ns132p1886 Ns132p121 Ns132p1885 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1888 := nat_lit 3704641391274724163644238850612593127875084642968407725067112890625 

noncomputable def Ns132p1889 := nat_lit 3641124768848072133198319368208649028156123144831298980712890625 

noncomputable def Ns132p1890 := nat_lit 9696737060855666407043066377389215617436778436968483843492712890625 

noncomputable def Ns132p1891 := BSN.sin_dyadic_bound_f 88136225 67108864 3 2 67108864 33554432 Ns132p1888 Ns132p108 Ns132p1889 Ns132p1890 Ns132p111 Ns132p1889 64896872 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 88136225) qz359 0 2 Ns132p1888 Ns132p108 Ns132p1889 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 88136225) (BSN.sinOddQ 67108864) 0 2 Ns132p1890 Ns132p111 Ns132p1889 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1892 := nat_lit 529537255935073703487587794420232937557408971740633430074672615694861269660246678771246616081984000000 

noncomputable def Ns132p1893 := nat_lit 266768981282753635449619914455954653059470814806664223892962190854735747521825940561000000000000 

noncomputable def Ns132p1894 := nat_lit 3208486183236894216239000320423071712658903344377730999775308404456876591604787017973592873668569600000 

noncomputable def Ns132p1895 := BSN.cos_dyadic_bound_f 89573170 67108864 4 3 67108864 33554432 Ns132p1892 Ns132p118 Ns132p1893 Ns132p1894 Ns132p121 Ns132p1893 15694483 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 89573170) qz360 0 3 Ns132p1892 Ns132p118 Ns132p1893 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 89573170) (BSN.cosOddQ 67108864) 0 3 Ns132p1894 Ns132p121 Ns132p1893 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1896 := Ns132p1847 39911 BSN.abs_quadSignPos (BSN.cos_quad_nat3 47 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 64896872 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 8 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 15694483 67108864) qz246 rfl rfl (Ns132p1879 RS133to150.d9 RS133to150.d11 RS133to150.d13 RS133to150.d17 (Ns132p1883 rfl rfl) (Ns132p1887 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns132p1878 rfl) RS133to150.d19 RS133to150.d21 RS133to150.d23 RS133to150.d25 RS133to150.d17 (Ns132p1891 rfl rfl) (Ns132p1895 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns132p1897 := nat_lit 92411849327885744385600000000 

noncomputable def Ns132p1898 := BSN.sin_dyadic_bound_f 17435400 67108864 2 1 67108864 33554432 Ns132p1897 Ns132p114 Ns132p1897 Ns132p1897 Ns132p115 Ns132p1897 17239912 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 17435400) qz359 0 1 Ns132p1897 Ns132p114 Ns132p1897 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 17435400) (BSN.sinOddQ 67108864) 0 1 Ns132p1897 Ns132p115 Ns132p1897 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1899 := nat_lit 46805103635979388572622662394414989787989688743407079062225255041 

noncomputable def Ns132p1900 := nat_lit 1886660462383710320825655039988313834504778947285679556229761 

noncomputable def Ns132p1901 := nat_lit 140411537587013398297226335873164992736300056672326665827563305601 

noncomputable def Ns132p1902 := BSN.cos_dyadic_bound_f 34234321 67108864 3 2 67108864 33554432 Ns132p1899 Ns132p124 Ns132p1900 Ns132p1901 Ns132p127 Ns132p1900 58564595 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 34234321) qz360 0 2 Ns132p1899 Ns132p124 Ns132p1900 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 34234321) (BSN.cosOddQ 67108864) 0 2 Ns132p1901 Ns132p127 Ns132p1900 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1903 := Ns132p1845 53500 BSN.abs_quadSignPos (BSN.cos_quad_nat3 55 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 17239912 67108864) BSN.abs_quadSignNeg qz728 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 58564595 67108864) qz246 rfl rfl (Ns132p1896 rfl rfl) (Ns132p1878 rfl) RS133to150.d27 RS133to150.d29 RS133to150.d31 RS133to150.d33 RS133to150.d17 (Ns132p1898 rfl rfl) (Ns132p1902 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns132p1904 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 7) 143590469 67108864 53500 67108864 143590469 67108864 53500 67108864 19272386511634432 143590469 33554432 13375 8388608 (Ns132p1903 rfl) 

noncomputable def Ns132p1905 := @Enclosure.Real.IsNear.mulLit_tf qz780 (Zeta.RiemannSiegel.correction qz245) 2971545 8388608 1 8388608 3748210039875 4398046511104 144619551491945 1880743226613170176 11137974802940356875 36893488147419103232 

noncomputable abbrev qz784 := (@HPow.hPow Real Real Real qz7 qz244 qz9)

noncomputable def Ns132p1906 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz784 1 1 0 1 2971545 8388608 1 8388608 2971545 8388608 1 8388608 

noncomputable def Ns132p1907 := @Enclosure.Real.IsNear.sqrt_image qz244 266372952013 4194304000 199517 4194304000 33425264 33425290 4194304 (@Enclosure.Real.IsNear.of_eq qz244 (@HMul.hMul Real Real Real qz5 qz243 qz3) Bool.false 266372952013 4194304000 199517 4194304000 (BSN.t_div_two_pi_mk qz243 399034 1000 qz246) (@Enclosure.Real.IsNear.mulLit_ff qz243 qz3 399034 1000 0 1 1335089 8388608 1 8388608 266372952013 4194304000 199517 4194304000 (Enclosure.Real.IsNear.const Bool.false 399034 1000) RS133to150.d36 rfl)) 

noncomputable abbrev qz919 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 399034 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz785 := qz919

noncomputable abbrev qz591 := qz785

noncomputable abbrev qz248 := qz591

noncomputable def Ns132p1908 := @Enclosure.Real.IsNear.sqrt_image qz248 33425277 4194304 13 4194304 11840427 11840432 4194304 (@Enclosure.Real.IsNear.recentre' qz248 Bool.false 66850554 8388608 26 8388608 33425277 4194304 13 4194304 (Ns132p1907 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns132p1909 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz248) 23680859 8388608 5 8388608 1485772 1485773 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz248) Bool.false 23680859 8388608 5 8388608 23680859 8388608 5 8388608 (Ns132p1908 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns132p1910 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz248)) Bool.false 2971545 8388608 1 8388608 2971545 8388608 1 8388608 (Ns132p1909 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz339 qz337 qz584)

noncomputable abbrev qz786 := (@HMul.hMul Real Real Real qz843 qz917 qz917)

noncomputable abbrev qz592 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz786 qz779) qz640)

noncomputable abbrev qz250 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz592))

noncomputable def Ns132p1911 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz245) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz249)) qz250) Bool.false 3748210039875 

noncomputable def Ns132p1912 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz249)) qz250 1068513 1048576 89 

noncomputable def Ns132p1913 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz249)) Bool.false 8548104 8388608 178 8388608 1068513 1048576 89 

noncomputable def Ns132p1914 := @Enclosure.Real.IsNear.recentre' (Real.cos qz249) Bool.false 8232088 8388608 290625398 14348932087808 1029011 1048576 145312699 7174466043904 

noncomputable def Ns132p1915 := @Enclosure.Real.IsNear.cos_image qz249 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6385521) qz384) Bool.false 6385521 1048576 165 8388608 Bool.false 8232088 8388608 1 

noncomputable def Ns132p1916 := nat_lit 350818980352491954933930779 

noncomputable def Ns132p1917 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz245 884279719003555 140737488355328 1 500000000000000 4065149 4194304 13 4194304 3594728815427582604695 590295810358705651712 Ns132p1916 

noncomputable def Ns132p1918 := @Enclosure.Real.IsNear.subLit_ff_p qz248 qz1 33425277 4194304 13 4194304 7 1 0 1 4065149 4065149 4194304 13 

noncomputable def Ns132p1919 := @Ns132p1918 4194304 (@Enclosure.Real.IsNear.recentre' qz248 Bool.false 66850554 8388608 26 8388608 33425277 4194304 13 4194304 (Ns132p1907 rfl rfl rfl rfl rfl rfl) rfl) qz366 

noncomputable def Ns132p1920 := @Enclosure.Real.IsNear.recentre' qz249 Bool.false 3594728815427582604695 590295810358705651712 Ns132p1916 Ns132p153 6385521 1048576 165 8388608 (@Ns132p1917 Ns132p153 RS133to150.d35 (Ns132p1919 rfl rfl) rfl) 

noncomputable def Ns132p1921 := nat_lit 82678865945889236693811690032131705250135164265690761443663663869127110503642530119680 

noncomputable def Ns132p1922 := nat_lit 98272861265904784203519778884253080775613436136104517697609358485215490338266873856 

noncomputable def Ns132p1923 := nat_lit 216380778559088916928415394251675199238622056084969729799989656886356845287087527755776 

noncomputable def Ns132p1924 := BSN.sin_dyadic_bound_f 23662149836 17179869184 3 2 8388608 3424393 Ns132p1921 Ns132p99 Ns132p1922 Ns132p1923 Ns132p102 Ns132p1922 8232088 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 23662149836) qz355 0 2 Ns132p1921 Ns132p99 Ns132p1922 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 23662149836) qz356 0 2 Ns132p1923 Ns132p102 Ns132p1922 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1925 := @Ns132p1915 1710526 (Ns132p1920 rfl) (Enclosure.sfrac_false_div 6385521 1048576) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6385521) qz384) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 208134471070513807491072) (@Nat.cast Real Real.instNatCast 151115727451828646838272)) 226375608064910080 72057594037927936 Bool.false 8232088 8388608 0 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 6385521 1048576 226375608064910080 72057594037927936 0 208134471070513807491072 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8232088 8388608 208134471070513807491072 151115727451828646838272 23662149836 17179869184 3424393 3421052 (Ns132p1924 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p1926 := @Enclosure.Real.IsNear.inv_image (Real.cos qz249) 1029011 1048576 145312699 7174466043904 4273963 4274141 4194304 (Ns132p1914 (Ns132p1925 rfl rfl) rfl) rfl 

noncomputable def Ns132p1927 := @Enclosure.Real.IsNear.recentre' qz250 Bool.false 3507875 4194304 

noncomputable abbrev qz251 := (@HMul.hMul Real Real Real qz339 qz337 qz592)

noncomputable def Ns132p1928 := @Enclosure.Real.IsNear.cos_image qz251 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 2433615)) qz357) Bool.true 2433615 4194304 

noncomputable def Ns132p1929 := nat_lit 1436553033407452070090126405 

noncomputable def Ns132p1930 := nat_lit 4323708867120614661032265213956797 

noncomputable def Ns132p1931 := @Enclosure.Real.IsNear.recentre' qz251 Bool.true Ns132p1929 Ns132p171 Ns132p1930 

noncomputable abbrev qz252 := qz592

noncomputable def Ns132p1932 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz252 884279719003555 140737488355328 1 500000000000000 1624545946871 

noncomputable abbrev qz593 := (@HSub.hSub Real Real Real qz635 qz786 qz779)

noncomputable abbrev qz253 := qz593

noncomputable def Ns132p1933 := @Enclosure.Real.IsNear.subLit_tf qz253 qz27 525034319095 17592186044416 160219995 17592186044416 1 16 

noncomputable abbrev qz594 := qz786

noncomputable abbrev qz254 := qz594

noncomputable def Ns132p1934 := @Enclosure.Real.IsNear.subLit_ff_n qz254 qz245 16525436392201 17592186044416 105694043 17592186044416 4065149 4194304 13 4194304 

noncomputable def Ns132p1935 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz245 4065149 4194304 13 4194304 4065149 4194304 13 4194304 16525436392201 17592186044416 

noncomputable def Ns132p1936 := nat_lit 18238356133549113586649837768397351937985096201543690625 

noncomputable def Ns132p1937 := nat_lit 1230311231004427572219489143437916157000509562890625 

noncomputable def Ns132p1938 := nat_lit 54712607778185331904805074326905179981641287585505290625 

noncomputable def Ns132p1939 := BSN.cos_dyadic_bound_f 2433615 4194304 3 2 4194304 1710526 Ns132p1936 Ns132p829 Ns132p1937 Ns132p1938 Ns132p832 Ns132p1937 3507875 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2433615) (BSN.cosEvenQ 4194304) 0 2 Ns132p1936 Ns132p829 Ns132p1937 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2433615) (BSN.cosOddQ 4194304) 0 2 Ns132p1938 Ns132p832 Ns132p1937 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1940 := @Ns132p1927 416431070 7174466043904 3507875 4194304 208215535 3587233021952 (@Ns132p1928 241 4194304 Bool.false 3507875 4194304 1 1710526 (@Ns132p1931 Ns132p174 2433615 4194304 241 4194304 (@Ns132p1932 17592186044416 160219995 17592186044416 Ns132p1929 Ns132p171 Ns132p1930 Ns132p174 RS133to150.d35 (@Ns132p1933 0 1 25992735149936 1624545946871 17592186044416 160219995 17592186044416 (@Ns132p1934 2202153544717434880 525034319095 17592186044416 160219995 17592186044416 (@Ns132p1935 105694043 17592186044416 (Ns132p1919 rfl rfl) (Ns132p1919 rfl rfl) rfl) (Ns132p1919 rfl rfl) rfl rfl) qz372 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 2433615 4194304) (BSN.cos_neg_of_bound 2433615 4194304 Bool.false 3507875 4194304 1 1710526 (Ns132p1939 rfl rfl)) rfl rfl) 

noncomputable def Ns132p1941 := @Ns132p1905 862693004878700006065 Ns132p333 (Ns132p1906 qz29 (@Enclosure.Real.IsNear.of_eq qz784 (@Inv.inv Real Real.instInv (Real.sqrt qz248)) Bool.false 2971545 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz244 (BSN.t_div_two_pi_nonneg qz243 399034 1000 qz246)) Ns132p1910) rfl) (@Ns132p1911 4398046511104 144619551491945 1880743226613170176 (BSN.correction_mk qz245 (BSN.cos_two_pi_p_ne_zero_mk qz243 399034 1000 7 qz246 rfl rfl (@BSN.floor_sqrt_eq_dec qz243 399034 1000 7 qz246 rfl rfl rfl))) (@Ns132p1912 4194304 3507875 4194304 208215535 3587233021952 3748210039875 4398046511104 144619551491945 1880743226613170176 (@Ns132p1913 4194304 (Ns132p1926 rfl rfl rfl rfl rfl) rfl) (Ns132p1940 rfl) rfl)) 

noncomputable def Ns132p1942 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz243) (hardyZApproximantRS₀ qz243) Bool.false 169017365106249623819 36893488147419103232 51172574316781002214065 Ns132p333 (@Eq.refl Real (hardyZApproximantRS₀ qz243)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz243) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz243) qz243 7) (@HMul.hMul Real Real Real qz5 qz780 (Zeta.RiemannSiegel.correction qz245))) Bool.false 169017365106249623819 36893488147419103232 51172574316781002214065 Ns132p333 (BSN.hardyZApproximantRS₀_eq qz243 7 (@BSN.floor_sqrt_eq_dec qz243 399034 1000 7 qz246 rfl rfl rfl)) (@Ns132p1843 169017365106249623819 36893488147419103232 51172574316781002214065 Ns132p333 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz243) qz243 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 7)) Bool.false 143590469 33554432 13375 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz243) qz243 7) (Ns132p1904 (Ns132p1903 rfl) rfl rfl)) (Ns132p1941 rfl) rfl rfl)) 

theorem RS133to150.d56 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz243) Bool.false 169017365106249623819 36893488147419103232 51172574316781002214065 Ns132p333 := Ns132p1942 

noncomputable def Ns132p1943 := nat_lit 1723127830188035966083530752 

noncomputable abbrev qz920 := (Enclosure.sfrac Bool.false 400547 1000)

noncomputable abbrev qz787 := qz920

noncomputable abbrev qz595 := qz787

noncomputable abbrev qz255 := qz595

noncomputable abbrev qz921 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 400547 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz788 := qz921

noncomputable abbrev qz596 := qz788

noncomputable abbrev qz256 := qz596

noncomputable abbrev qz922 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 400547 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz789 := qz922

noncomputable abbrev qz597 := qz789

noncomputable abbrev qz257 := qz597

noncomputable abbrev qz790 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz256 qz9))

noncomputable def Ns132p1944 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz255) qz255 7) (@HMul.hMul Real Real Real qz5 qz790 (Zeta.RiemannSiegel.correction qz257)) 103940957 33554432 26853 16777216 5788934301358859805 18446744073709551616 431037777175162284077 Ns132p1332 Ns132p1943 

noncomputable def Ns132p1945 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz255) qz255 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 400547 1000 54 94 67108864 33554432 1125899906842624 Bool.false 42376633141 1303 

noncomputable def Ns132p1946 := Ns132p1945 120242927 40 27397080 8 130587807 40 25364760 8 Bool.true 75141173 40065 Bool.true 93935258 Bool.true 20971625 3537118876014220 1 Bool.false 11423203 Bool.true Bool.false 63858611 Bool.true Bool.true 103940957 

noncomputable def Ns132p1947 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz255) qz255 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 400547 1000 48 8 67108864 33554432 1125899906842624 Bool.false 42376633141 1303 

noncomputable def Ns132p1948 := Ns132p1947 93032624 40 33554424 8 108007536 40 30011992 8 Bool.true 123118188 23634 Bool.false 52805556 Bool.true 42146524 3537118876014220 1 Bool.false 47383518 Bool.false Bool.false 54303505 Bool.false Bool.true 75141173 

noncomputable def Ns132p1949 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz255) qz255 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 400547 1000 225 121 67108864 33554432 1125899906842624 Bool.false 42376633141 1303 

noncomputable def Ns132p1950 := Ns132p1949 46516304 40 47453136 16 73726608 40 38745320 8 Bool.true 67108824 1352 Bool.false 26436782 Bool.false 90524281 3537118876014220 1 Bool.false 25758290 Bool.true Bool.false 65463729 Bool.true Bool.true 123118188 

noncomputable def Ns132p1951 := nat_lit 84559374648993600864471075002216969393296265836853069311 

noncomputable def Ns132p1952 := nat_lit 133910675591195374384614387756698956863901757394124800 

noncomputable def Ns132p1953 := nat_lit 4948919258707503906673254803360000 

noncomputable def Ns132p1954 := nat_lit 11893657222756404080198534579144627520 

noncomputable def Ns132p1955 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz255 400547 1000 641752596836 16000000 801094 4000 2000 Ns132p1953 Ns132p1954 (@Eq.refl Real qz255) rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns132p1956 := nat_lit 27058999887677952276630744000709430205854805067792982179520 

noncomputable abbrev qz791 := (Real.log (Enclosure.sfrac Bool.false 641752596836 16000000))

noncomputable abbrev qz258 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 400547 4000) qz791) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 801094))))))

noncomputable abbrev qz792 := (Enclosure.sfrac Bool.false 400547 2000)

noncomputable abbrev qz598 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz258 qz792) (@HMul.hMul Real Real Real qz5 qz792 (Real.log Real.pi)))

noncomputable def Ns132p1957 := @Enclosure.Real.IsNear.addLit_ft_p qz598 (Enclosure.sfrac Bool.true Ns132p1953 Ns132p1954) 2275079667359680046351 3602879701896396800 3398250497474670351173 Ns132p199 Ns132p1953 Ns132p1954 0 1 Ns132p1956 

noncomputable def Ns132p1958 := nat_lit 763390059930030036570414776320000 

noncomputable abbrev qz599 := (@HSub.hSub Real Real Real qz12 qz258 qz792)

noncomputable abbrev qz600 := (@HMul.hMul Real Real Real qz5 qz792 (Real.log Real.pi))

noncomputable def Ns132p1959 := @Enclosure.Real.IsNear.subLit_ff_p qz599 qz600 15505362407684161714507 18014398509481984000 5106838527804612883 684210400000000000000000 15385315086267 67108864000 400547 33554432000 Ns132p1958 2275079667359680046351 3602879701896396800 

noncomputable def Ns132p1960 := nat_lit 31010724815368323429014000 

noncomputable abbrev qz601 := qz792

noncomputable def Ns132p1961 := @Enclosure.Real.IsNear.subLit_ff_p qz258 qz601 19113169047572901837131 18014398509481984000 5106838527804612883 684210400000000000000000 400547 2000 0 1 Ns132p1960 15505362407684161714507 18014398509481984000 5106838527804612883 684210400000000000000000 

noncomputable def Ns132p1962 := nat_lit 43039030500259309324230178094593343488 

noncomputable def Ns132p1963 := nat_lit 12813851348883193764773888 

noncomputable def Ns132p1964 := nat_lit 263919406252342617088420796081971845295087525752119100180092749060527329280 

noncomputable def Ns132p1965 := nat_lit 898239433476086989261264131252457707503378630968323420746931972231622656 

noncomputable def Ns132p1966 := nat_lit 39403356109971135006417249475879033096361212118441307733450521047040 

noncomputable def Ns132p1967 := BSN.log_dyadic_bound 117464596836 1166040596836 4 3 Ns132p1964 33554432 13684208 Ns132p1965 Ns132p1966 6783421 1283505193672 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 117464596836) (BSN.artanhQ 1166040596836) 0 3 Ns132p1965 Ns132p1964 Ns132p1966 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns132p1968 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 400547 4000) qz791 400547 4000 0 1 47735316115927673 4503599627370496 12500002565789 171052600000000000000 19120237664286481637131 18014398509481984000 5006838527719086583 684210400000000000000000 (Enclosure.Real.IsNear.const Bool.false 400547 4000) (BSN.isNear_log_sfrac 641752596836 16000000 47735316115927673 4503599627370496 12500002565789 171052600000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 641752596836) qz350)) Bool.false Ns132p1963 Ns132p87 1000000205263120 13684208000000000000000 47735316115927673 4503599627370496 12500002565789 171052600000000000000 (BSN.log_rat_reduce_isNear 641752596836 16000000 15 1283505193672 1048576000000 6783421 33554432 24973259072661432 36028797018963968 13684208 1000000000000000 rfl rfl rfl rfl (Ns132p1967 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns132p1969 := BSN.arctan_dyadic_bound_f 1000 801094 1 0 4194304 1710526 0 1 1 0 1 1 5235 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 801094) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 801094) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz602 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 801094)))

noncomputable def Ns132p1970 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz602 884279719003555 562949953421312 1 2000000000000000 5235 4194304 1 1710526 3705990919529326182400 883577089197475 562949953421312 1000000000855263 1710526000000000000000 qz17 (Ns132p1969 rfl) rfl rfl 

noncomputable def Ns132p1971 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 400547 4000) qz791) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz602)) 19120237664286481637131 18014398509481984000 5006838527719086583 684210400000000000000000 883577089197475 2251799813685248 1000000000855263 6842104000000000000000 Ns132p1962 19113169047572901837131 18014398509481984000 5106838527804612883 684210400000000000000000 (Ns132p1968 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz602) 1 4 0 1 883577089197475 562949953421312 1000000000855263 1710526000000000000000 883577089197475 2251799813685248 1000000000855263 6842104000000000000000 qz353 Ns132p1970 rfl) 

noncomputable def Ns132p1972 := @Ns132p1957 Ns132p1951 Ns132p1952 3398250497474670351173 Ns132p199 (@Ns132p1959 3398250497474670351173 Ns132p199 (Ns132p1961 (Ns132p1971 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 400547 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz601 (Real.log Real.pi) 400547 2000 0 1 38410761 33554432 1 16777216 15385315086267 67108864000 400547 33554432000 (Enclosure.Real.IsNear.const Bool.false 400547 2000) RS133to150.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns132p1953 Ns132p1954) 

noncomputable def Ns132p1973 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz255) Bool.false Ns132p1951 Ns132p1952 3398250497474670351173 Ns132p199 2648539571 4194304 41 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz255) (@HAdd.hAdd Real Real Real qz354 qz598 (Enclosure.sfrac Bool.true Ns132p1953 Ns132p1954)) Bool.false Ns132p1951 Ns132p1952 3398250497474670351173 Ns132p199 Ns132p1955 (Ns132p1972 rfl rfl)) 

noncomputable def Ns132p1974 := nat_lit 140317030308219863766845826572621989729227543699939997318091475628794944409878366198305 

noncomputable def Ns132p1975 := nat_lit 282583866837046011966505874486260119151912153455840649045446789357991173868430760481 

noncomputable def Ns132p1976 := nat_lit 367039467403792044893793298179127456716969042394247679544165998511692868696751595002401 

noncomputable def Ns132p1977 := BSN.sin_dyadic_bound_f 27001843789 17179869184 3 2 8388608 3424393 Ns132p1974 Ns132p99 Ns132p1975 Ns132p1976 Ns132p102 Ns132p1975 8388603 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 27001843789) qz355 0 2 Ns132p1974 Ns132p99 Ns132p1975 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 27001843789) qz356 0 2 Ns132p1976 Ns132p102 Ns132p1975 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1978 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz255) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2648539571) qz357) Bool.false 2648539571 4194304 41 2097152 Bool.true 8388603 8388608 1 1710526 (Ns132p1973 rfl) (Enclosure.sfrac_false_div 2648539571 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2648539571) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 950042918968698802798592) qz358) 226375608064910080 72057594037927936 Bool.false 8388603 8388608 100 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q1 2648539571 4194304 226375608064910080 72057594037927936 100 950042918968698802798592 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388603 8388608 950042918968698802798592 604462909807314587353088 27001843789 17179869184 3424393 3421052 (Ns132p1977 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p1979 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz255) Bool.false Ns132p1951 Ns132p1952 3398250497474670351173 Ns132p199 42376633141 67108864 1303 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz255) (@HAdd.hAdd Real Real Real qz354 qz598 (Enclosure.sfrac Bool.true Ns132p1953 Ns132p1954)) Bool.false Ns132p1951 Ns132p1952 3398250497474670351173 Ns132p199 Ns132p1955 (Ns132p1972 rfl rfl)) 

noncomputable def Ns132p1980 := Ns132p1950 23634 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 225 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 25758290 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 121 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 65463729 67108864) (@Eq.refl Real qz255) rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz255) qz255 1) Bool.true 8388603 8388608 36114359 1793616510976 67108824 67108864 1352 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz255) qz255 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz255)) Bool.true 8388603 8388608 36114359 1793616510976 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz255) qz255) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz255)) Bool.true 8388603 8388608 72228718 3587233021952 8388603 8388608 36114359 1793616510976 (Ns132p1978 rfl rfl) rfl)) rfl) (Ns132p1979 rfl) RS133to150.d7 

noncomputable def Ns132p1981 := nat_lit 488466021960050360332980994576 

noncomputable def Ns132p1982 := BSN.sin_dyadic_bound_f 26436782 67108864 2 1 67108864 33554432 Ns132p1981 Ns132p114 Ns132p1981 Ns132p1981 Ns132p115 Ns132p1981 25758290 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 26436782) qz359 0 1 Ns132p1981 Ns132p114 Ns132p1981 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 26436782) (BSN.sinOddQ 67108864) 0 1 Ns132p1981 Ns132p115 Ns132p1981 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1983 := nat_lit 1435072454174335547046732789819713753994431881920619561788097375624736590823106047689544262331621078561 

noncomputable def Ns132p1984 := nat_lit 302817527272552478968363742587333220402014122079541423581921982371098657032556912750658228745761 

noncomputable def Ns132p1985 := nat_lit 7170509920397033807510887503411729674198709410745216296748902707394464871932278230479656491914279679521 

noncomputable def Ns132p1986 := BSN.sin_dyadic_bound_f 90524281 67108864 4 3 67108864 33554432 Ns132p1983 Ns132p233 Ns132p1984 Ns132p1985 Ns132p236 Ns132p1984 65463729 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 90524281) qz359 0 3 Ns132p1983 Ns132p233 Ns132p1984 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 90524281) (BSN.sinOddQ 67108864) 0 3 Ns132p1985 Ns132p236 Ns132p1984 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1987 := nat_lit 265000320116438581214743499677388563639195739008214160726252650496 

noncomputable def Ns132p1988 := nat_lit 60455658783947765429078194680997037478682463242995900329558016 

noncomputable def Ns132p1989 := nat_lit 794880049031747848113372342642803696842629852098156490378098835456 

noncomputable def Ns132p1990 := BSN.cos_dyadic_bound_f 52805556 67108864 3 2 67108864 33554432 Ns132p1987 Ns132p124 Ns132p1988 Ns132p1989 Ns132p127 Ns132p1988 47383518 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 52805556) qz360 0 2 Ns132p1987 Ns132p124 Ns132p1988 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 52805556) (BSN.cosOddQ 67108864) 0 2 Ns132p1989 Ns132p127 Ns132p1988 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1991 := nat_lit 107526644835851167997446283811598976075498364683326246453531181056 

noncomputable def Ns132p1992 := nat_lit 9956211158214559905947317111087639107267190275884503416242176 

noncomputable def Ns132p1993 := nat_lit 322560022085237074872526956800574752948280559669426970353761058816 

noncomputable def Ns132p1994 := BSN.cos_dyadic_bound_f 42146524 67108864 3 2 67108864 33554432 Ns132p1991 Ns132p124 Ns132p1992 Ns132p1993 Ns132p127 Ns132p1992 54303505 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 42146524) qz360 0 2 Ns132p1991 Ns132p124 Ns132p1992 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 42146524) (BSN.cosOddQ 67108864) 0 2 Ns132p1993 Ns132p127 Ns132p1992 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p1995 := Ns132p1948 40065 BSN.abs_quadSignPos (BSN.cos_quad_nat0 48 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 47383518 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 8 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 54303505 67108864) (@Eq.refl Real qz255) rfl rfl (Ns132p1980 RS133to150.d9 RS133to150.d11 RS133to150.d13 RS133to150.d17 (Ns132p1982 rfl rfl) (Ns132p1986 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns132p1979 rfl) RS133to150.d19 RS133to150.d21 RS133to150.d23 RS133to150.d25 RS133to150.d17 (Ns132p1990 rfl rfl) (Ns132p1994 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns132p1996 := nat_lit 640723864688617068107598873825222120120296295881501393052085768410773830371712371224109316492623548416 

noncomputable def Ns132p1997 := nat_lit 472001729923929359916989499371262563590044960362995189966363631835757678183984515549312261492736 

noncomputable def Ns132p1998 := nat_lit 3881147946275247797340382036731152289935211226292362227472082301494346765773404666880291372842665840640 

noncomputable def Ns132p1999 := BSN.cos_dyadic_bound_f 93935258 67108864 4 3 67108864 33554432 Ns132p1996 Ns132p118 Ns132p1997 Ns132p1998 Ns132p121 Ns132p1997 11423203 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 93935258) qz360 0 3 Ns132p1996 Ns132p118 Ns132p1997 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 93935258) (BSN.cosOddQ 67108864) 0 3 Ns132p1998 Ns132p121 Ns132p1997 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p2000 := nat_lit 193432004983689321738525390625 

noncomputable def Ns132p2001 := BSN.cos_dyadic_bound_f 20971625 67108864 2 1 67108864 33554432 Ns132p2000 Ns132p135 Ns132p2000 Ns132p2000 Ns132p136 Ns132p2000 63858611 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 20971625) qz360 0 1 Ns132p2000 Ns132p135 Ns132p2000 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 20971625) (BSN.cosOddQ 67108864) 0 1 Ns132p2000 Ns132p136 Ns132p2000 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p2002 := Ns132p1946 53706 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 54 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 11423203 67108864) BSN.abs_quadSignNeg qz728 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 63858611 67108864) (@Eq.refl Real qz255) rfl rfl (Ns132p1995 rfl rfl) (Ns132p1979 rfl) RS133to150.d27 RS133to150.d29 RS133to150.d31 RS133to150.d33 RS133to150.d17 (Ns132p1999 rfl rfl) (Ns132p2001 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns132p2003 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz255) qz255 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz255) qz255 7) 103940957 67108864 53706 67108864 103940957 67108864 53706 67108864 13950719094685696 103940957 33554432 26853 16777216 (Ns132p2002 rfl) 

noncomputable def Ns132p2004 := @Enclosure.Real.IsNear.mulLit_tf qz790 (Zeta.RiemannSiegel.correction qz257) 2968735 8388608 1 8388608 1949966669763 2199023255552 289261182423281 3761486453226340352 5788934301358859805 18446744073709551616 

noncomputable abbrev qz793 := (@HPow.hPow Real Real Real qz7 qz256 qz9)

noncomputable def Ns132p2005 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz793 1 1 0 1 2968735 8388608 1 8388608 2968735 8388608 1 8388608 

noncomputable def Ns132p2006 := @Enclosure.Real.IsNear.sqrt_image qz256 534765893683 8388608000 400547 8388608000 33488573 33488599 4194304 (@Enclosure.Real.IsNear.of_eq qz256 (@HMul.hMul Real Real Real qz5 qz255 qz3) Bool.false 534765893683 8388608000 400547 8388608000 (BSN.t_div_two_pi_mk qz255 400547 1000 (@Eq.refl Real qz255)) (@Enclosure.Real.IsNear.mulLit_ff qz255 qz3 400547 1000 0 1 1335089 8388608 1 8388608 534765893683 8388608000 400547 8388608000 (Enclosure.Real.IsNear.const Bool.false 400547 1000) RS133to150.d36 rfl)) 

noncomputable abbrev qz923 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 400547 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz794 := qz923

noncomputable abbrev qz603 := qz794

noncomputable abbrev qz259 := qz603

noncomputable def Ns132p2007 := @Enclosure.Real.IsNear.sqrt_image qz259 16744293 2097152 13 4194304 11851635 11851640 4194304 (@Enclosure.Real.IsNear.recentre' qz259 Bool.false 66977172 8388608 26 8388608 16744293 2097152 13 4194304 (Ns132p2006 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns132p2008 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz259) 23703275 8388608 5 8388608 1484367 1484368 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz259) Bool.false 23703275 8388608 5 8388608 23703275 8388608 5 8388608 (Ns132p2007 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns132p2009 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz259)) Bool.false 2968735 8388608 1 8388608 2968735 8388608 1 8388608 (Ns132p2008 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz260 := (@HMul.hMul Real Real Real qz339 qz337 qz597)

noncomputable abbrev qz795 := (@HMul.hMul Real Real Real qz843 qz922 qz922)

noncomputable abbrev qz604 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz795 qz789) qz640)

noncomputable abbrev qz261 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz604))

noncomputable def Ns132p2010 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz257) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz260)) qz261) Bool.false 1949966669763 

noncomputable def Ns132p2011 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz260)) qz261 526849 524288 43 

noncomputable def Ns132p2012 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz260)) Bool.false 8429584 8388608 172 8388608 526849 524288 43 

noncomputable def Ns132p2013 := @Enclosure.Real.IsNear.recentre' (Real.cos qz260) Bool.false 8347831 8388608 72228718 3587233021952 8347831 8388608 36114359 1793616510976 

noncomputable def Ns132p2014 := @Enclosure.Real.IsNear.cos_image qz260 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51879733) qz365) Bool.false 51879733 8388608 41 2097152 Bool.false 8347831 8388608 1 

noncomputable def Ns132p2015 := nat_lit 350818980353035775103015707 

noncomputable def Ns132p2016 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz257 884279719003555 140737488355328 1 500000000000000 2064229 2097152 13 4194304 1825355840078989334095 295147905179352825856 Ns132p2015 

noncomputable def Ns132p2017 := @Enclosure.Real.IsNear.subLit_ff_p qz259 qz1 16744293 2097152 13 4194304 7 1 0 1 2064229 2064229 2097152 13 

noncomputable def Ns132p2018 := @Ns132p2017 4194304 (@Enclosure.Real.IsNear.recentre' qz259 Bool.false 66977172 8388608 26 8388608 16744293 2097152 13 4194304 (Ns132p2006 rfl rfl rfl rfl rfl rfl) rfl) qz366 

noncomputable def Ns132p2019 := @Enclosure.Real.IsNear.recentre' qz260 Bool.false 1825355840078989334095 295147905179352825856 Ns132p2015 Ns132p153 51879733 8388608 41 2097152 (@Ns132p2016 Ns132p153 RS133to150.d35 (Ns132p2018 rfl rfl) rfl) 

noncomputable def Ns132p2020 := nat_lit 1779728768165678736736256 

noncomputable def Ns132p2021 := nat_lit 107952153851092613053685657350940076443719534951163147911697952179971921576483224616960 

noncomputable def Ns132p2022 := nat_lit 167414149248648496929153859043086791839327043607523661956889451881267485926678921216 

noncomputable def Ns132p2023 := nat_lit 282460780035030460431291424909249488261049395372919872887469196596880599627860489076736 

noncomputable def Ns132p2024 := BSN.sin_dyadic_bound_f 25291466956 17179869184 3 2 8388608 3424393 Ns132p2021 Ns132p99 Ns132p2022 Ns132p2023 Ns132p102 Ns132p2022 8347831 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 25291466956) qz355 0 2 Ns132p2021 Ns132p99 Ns132p2022 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 25291466956) qz356 0 2 Ns132p2023 Ns132p102 Ns132p2022 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p2025 := @Ns132p2014 1710526 (Ns132p2019 rfl) (Enclosure.sfrac_false_div 51879733 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51879733) qz365) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns132p2020) qz367) 226375608064910080 72057594037927936 Bool.false 8347831 8388608 0 1000000000000000 3421052 1710526 (BSN.sin_reduce_arg_pos_rat_q3 51879733 8388608 226375608064910080 72057594037927936 0 Ns132p2020 Ns132p87 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8347831 8388608 Ns132p2020 Ns132p87 25291466956 17179869184 3424393 3421052 (Ns132p2024 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns132p2026 := @Enclosure.Real.IsNear.inv_image (Real.cos qz260) 8347831 8388608 36114359 1793616510976 4214706 4214878 4194304 (Ns132p2013 (Ns132p2025 rfl rfl) rfl) rfl 

noncomputable def Ns132p2027 := @Enclosure.Real.IsNear.recentre' qz261 Bool.false 3701187 4194304 

noncomputable abbrev qz262 := (@HMul.hMul Real Real Real qz339 qz337 qz604)

noncomputable def Ns132p2028 := @Enclosure.Real.IsNear.cos_image qz262 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 4108653)) qz365) Bool.true 4108653 8388608 

noncomputable def Ns132p2029 := nat_lit 303165148635646225541595605 

noncomputable def Ns132p2030 := nat_lit 4368128864768290165715336949578491 

noncomputable def Ns132p2031 := @Enclosure.Real.IsNear.recentre' qz262 Bool.true Ns132p2029 Ns132p1121 Ns132p2030 

noncomputable abbrev qz263 := qz604

noncomputable def Ns132p2032 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz263 884279719003555 140737488355328 1 500000000000000 342838518311 

noncomputable abbrev qz605 := (@HSub.hSub Real Real Real qz635 qz795 qz789)

noncomputable abbrev qz264 := qz605

noncomputable def Ns132p2033 := @Enclosure.Real.IsNear.subLit_tf qz264 qz27 67960611367 4398046511104 161866029 17592186044416 1 16 

noncomputable abbrev qz606 := qz795

noncomputable abbrev qz265 := qz606

noncomputable def Ns132p2034 := @Enclosure.Real.IsNear.subLit_ff_n qz265 qz257 4261041364441 4398046511104 107340077 17592186044416 2064229 2097152 13 4194304 

noncomputable def Ns132p2035 := @Enclosure.Real.IsNear.mulLit_ff qz257 qz257 2064229 2097152 13 4194304 2064229 2097152 13 4194304 4261041364441 4398046511104 

noncomputable def Ns132p2036 := nat_lit 284969156115865398785899281 

noncomputable def Ns132p2037 := nat_lit 118842243771396506390315925504 

noncomputable def Ns132p2038 := nat_lit 1782633656570947595854738882560 

noncomputable def Ns132p2039 := BSN.cos_dyadic_bound_f 4108653 8388608 2 1 4194304 1710526 Ns132p2036 Ns132p2037 Ns132p2036 Ns132p2036 Ns132p2038 Ns132p2036 3701187 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 4108653) (BSN.cosEvenQ 8388608) 0 1 Ns132p2036 Ns132p2037 Ns132p2036 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 4108653) (BSN.cosOddQ 8388608) 0 1 Ns132p2036 Ns132p2038 Ns132p2036 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns132p2040 := @Ns132p2027 419852122 7174466043904 3701187 4194304 209926061 3587233021952 (@Ns132p2028 243 4194304 Bool.false 3701187 4194304 1 1710526 (@Ns132p2031 Ns132p174 4108653 8388608 243 4194304 (@Ns132p2032 4398046511104 161866029 17592186044416 Ns132p2029 Ns132p1121 Ns132p2030 Ns132p174 RS133to150.d35 (@Ns132p2033 0 1 5485416292976 342838518311 4398046511104 161866029 17592186044416 (@Ns132p2034 142523732049526784 67960611367 4398046511104 161866029 17592186044416 (@Ns132p2035 107340077 17592186044416 (Ns132p2018 rfl rfl) (Ns132p2018 rfl rfl) rfl) (Ns132p2018 rfl rfl) rfl rfl) qz372 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 4108653 8388608) (BSN.cos_neg_of_bound 4108653 8388608 Bool.false 3701187 4194304 1 1710526 (Ns132p2039 rfl rfl)) rfl rfl) 

noncomputable def Ns132p2041 := @Ns132p2004 431037777175162284077 Ns132p1332 (Ns132p2005 qz29 (@Enclosure.Real.IsNear.of_eq qz793 (@Inv.inv Real Real.instInv (Real.sqrt qz259)) Bool.false 2968735 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz256 (BSN.t_div_two_pi_nonneg qz255 400547 1000 (@Eq.refl Real qz255))) Ns132p2009) rfl) (@Ns132p2010 2199023255552 289261182423281 3761486453226340352 (BSN.correction_mk qz257 (BSN.cos_two_pi_p_ne_zero_mk qz255 400547 1000 7 (@Eq.refl Real qz255) rfl rfl (@BSN.floor_sqrt_eq_dec qz255 400547 1000 7 (@Eq.refl Real qz255) rfl rfl rfl))) (@Ns132p2011 2097152 3701187 4194304 209926061 3587233021952 1949966669763 2199023255552 289261182423281 3761486453226340352 (@Ns132p2012 2097152 (Ns132p2026 rfl rfl rfl rfl rfl) rfl) (Ns132p2040 rfl) rfl)) 

noncomputable def Ns132p2042 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz255) (hardyZApproximantRS₀ qz255) Bool.true 51353211110473751011 18446744073709551616 25682836709296891652141 Ns132p1332 (@Eq.refl Real (hardyZApproximantRS₀ qz255)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz255) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz255) qz255 7) (@HMul.hMul Real Real Real qz5 qz790 (Zeta.RiemannSiegel.correction qz257))) Bool.true 51353211110473751011 18446744073709551616 25682836709296891652141 Ns132p1332 (BSN.hardyZApproximantRS₀_eq qz255 7 (@BSN.floor_sqrt_eq_dec qz255 400547 1000 7 (@Eq.refl Real qz255) rfl rfl rfl)) (@Ns132p1944 51353211110473751011 18446744073709551616 25682836709296891652141 Ns132p1332 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz255) qz255 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz255) qz255 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz255) qz255 7)) Bool.true 103940957 33554432 26853 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz255) qz255 7) (Ns132p2003 (Ns132p2002 rfl) rfl rfl)) (Ns132p2041 rfl) rfl rfl)) 

theorem RS133to150.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz255) Bool.true 51353211110473751011 18446744073709551616 25682836709296891652141 Ns132p1332 := Ns132p2042 

noncomputable def RS133to150.d58 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz266 := (RS133to150.d3 qz338 qz373 (@Enclosure.dec_le_dec qz338 qz373 373095 1000 374633 1000 (@Eq.refl Real qz338) qz376 rfl rfl rfl))

noncomputable abbrev qz796 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz266)

noncomputable def Ns132p2043 := @Enclosure.Real.IsNear.of_eq qz796 (hardyZApproximantRS₀ qz4) Bool.true 2059803477868761821 18446744073709551616 98828020771487874364169 Ns132p64 

noncomputable abbrev qz267 := (@Enclosure.dec_le_dec qz338 qz373 373095 1000 374633 1000 (@Eq.refl Real qz338) qz376 rfl rfl rfl)

noncomputable def Ns132p2044 := @Enclosure.Real.IsNear.neg_val qz796 2059803477868761821 18446744073709551616 98828020771487874364169 Ns132p64 (Ns132p2043 (RS133to150.d4 qz4 qz30 qz267) RS133to150.d37) rfl 

noncomputable abbrev qz797 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz266)

noncomputable def Ns132p2045 := @Enclosure.Real.IsNear.of_eq qz797 (hardyZApproximantRS₀ qz30) Bool.false 268418535232699294785 147573952589676412928 203270459975862829269619 Ns132p188 

noncomputable def Ns132p2046 := @Enclosure.Real.IsNear.pos_val qz797 268418535232699294785 147573952589676412928 203270459975862829269619 Ns132p188 (Ns132p2045 (RS133to150.d38 qz4 qz30 qz267) RS133to150.d39) rfl 

noncomputable def Ns132p2047 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz796 qz4 qz4 373095 1000 373095 1000 

noncomputable def Ns132p2048 := @Enclosure.norm_gt_of_isNear qz796 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2059803477868761821 18446744073709551616 98828020771487874364169 

noncomputable def Ns132p2049 := @Ns132p2048 Ns132p64 132459661 1342177280 1213 1342177280 (Ns132p2043 (RS133to150.d4 qz4 qz30 qz267) RS133to150.d37) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2050 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz797 qz4 qz30 373095 1000 374633 1000 

noncomputable def Ns132p2051 := @Enclosure.norm_gt_of_isNear qz797 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 268418535232699294785 147573952589676412928 203270459975862829269619 

noncomputable def Ns132p2052 := @Ns132p2051 Ns132p188 132459661 1342177280 1213 1342177280 (Ns132p2045 (RS133to150.d38 qz4 qz30 qz267) RS133to150.d39) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2053 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz266 (@BSN.thirtyTwoPi_le_dec qz4 373095 1000 qz11 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz796 qz797 (Ns132p2044 rfl rfl) (Ns132p2046 rfl rfl)) (Ns132p2047 qz11 qz11 rfl rfl rfl rfl (Ns132p2049 rfl)) (Ns132p2050 qz11 qz33 rfl rfl rfl rfl (Ns132p2052 rfl)) 

noncomputable abbrev qz268 := (RS133to150.d3 qz373 qz392 (@Enclosure.dec_le_dec qz373 qz392 374633 1000 376169 1000 qz376 qz395 rfl rfl rfl))

noncomputable abbrev qz798 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz268)

noncomputable def Ns132p2054 := @Enclosure.Real.IsNear.of_eq qz798 (hardyZApproximantRS₀ qz30) Bool.false 268418535232699294785 147573952589676412928 203270459975862829269619 Ns132p188 

noncomputable abbrev qz269 := (@Enclosure.dec_le_dec qz373 qz392 374633 1000 376169 1000 qz376 qz395 rfl rfl rfl)

noncomputable def Ns132p2055 := @Enclosure.Real.IsNear.pos_val qz798 268418535232699294785 147573952589676412928 203270459975862829269619 Ns132p188 (Ns132p2054 (RS133to150.d4 qz30 qz50 qz269) RS133to150.d39) rfl 

noncomputable abbrev qz799 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz268)

noncomputable def Ns132p2056 := @Enclosure.Real.IsNear.of_eq qz799 (hardyZApproximantRS₀ qz50) Bool.true 2976144607846851433 18446744073709551616 55632997122283317942783 Ns132p333 

noncomputable def Ns132p2057 := @Enclosure.Real.IsNear.neg_val qz799 2976144607846851433 18446744073709551616 55632997122283317942783 Ns132p333 (Ns132p2056 (RS133to150.d38 qz30 qz50 qz269) RS133to150.d41) rfl 

noncomputable def Ns132p2058 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz798 qz4 qz30 373095 1000 374633 1000 

noncomputable def Ns132p2059 := @Enclosure.norm_gt_of_isNear qz798 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 268418535232699294785 147573952589676412928 203270459975862829269619 

noncomputable def Ns132p2060 := @Ns132p2059 Ns132p188 132459661 1342177280 1213 1342177280 (Ns132p2054 (RS133to150.d4 qz30 qz50 qz269) RS133to150.d39) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2061 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz799 qz4 qz50 373095 1000 376169 1000 

noncomputable def Ns132p2062 := @Enclosure.norm_gt_of_isNear qz799 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2976144607846851433 18446744073709551616 55632997122283317942783 

noncomputable def Ns132p2063 := @Ns132p2062 Ns132p333 132459661 1342177280 1213 1342177280 (Ns132p2056 (RS133to150.d38 qz30 qz50 qz269) RS133to150.d41) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2064 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz268 (@BSN.thirtyTwoPi_le_dec qz30 374633 1000 qz33 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz798 qz799 (Ns132p2055 rfl rfl) (Ns132p2057 rfl rfl)) (Ns132p2058 qz11 qz33 rfl rfl rfl rfl (Ns132p2060 rfl)) (Ns132p2061 qz11 qz53 rfl rfl rfl rfl (Ns132p2063 rfl)) 

noncomputable abbrev qz270 := (RS133to150.d3 qz392 qz405 (@Enclosure.dec_le_dec qz392 qz405 376169 1000 377703 1000 qz395 qz408 rfl rfl rfl))

noncomputable abbrev qz800 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz270)

noncomputable def Ns132p2065 := @Enclosure.Real.IsNear.of_eq qz800 (hardyZApproximantRS₀ qz50) Bool.true 2976144607846851433 18446744073709551616 55632997122283317942783 Ns132p333 

noncomputable abbrev qz271 := (@Enclosure.dec_le_dec qz392 qz405 376169 1000 377703 1000 qz395 qz408 rfl rfl rfl)

noncomputable def Ns132p2066 := @Enclosure.Real.IsNear.neg_val qz800 2976144607846851433 18446744073709551616 55632997122283317942783 Ns132p333 (Ns132p2065 (RS133to150.d4 qz50 qz64 qz271) RS133to150.d41) rfl 

noncomputable abbrev qz801 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz270)

noncomputable def Ns132p2067 := @Enclosure.Real.IsNear.of_eq qz801 (hardyZApproximantRS₀ qz64) Bool.false 24148299990873535461 9223372036854775808 9900164270355591940565 Ns132p436 

noncomputable def Ns132p2068 := @Enclosure.Real.IsNear.pos_val qz801 24148299990873535461 9223372036854775808 9900164270355591940565 Ns132p436 (Ns132p2067 (RS133to150.d38 qz50 qz64 qz271) RS133to150.d42) rfl 

noncomputable def Ns132p2069 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz800 qz4 qz50 373095 1000 376169 1000 

noncomputable def Ns132p2070 := @Enclosure.norm_gt_of_isNear qz800 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2976144607846851433 18446744073709551616 55632997122283317942783 

noncomputable def Ns132p2071 := @Ns132p2070 Ns132p333 132459661 1342177280 1213 1342177280 (Ns132p2065 (RS133to150.d4 qz50 qz64 qz271) RS133to150.d41) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2072 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz801 qz4 qz64 373095 1000 377703 1000 

noncomputable def Ns132p2073 := @Enclosure.norm_gt_of_isNear qz801 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 24148299990873535461 9223372036854775808 9900164270355591940565 

noncomputable def Ns132p2074 := @Ns132p2073 Ns132p436 132459661 1342177280 1213 1342177280 (Ns132p2067 (RS133to150.d38 qz50 qz64 qz271) RS133to150.d42) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2075 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz270 (@BSN.thirtyTwoPi_le_dec qz50 376169 1000 qz53 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz800 qz801 (Ns132p2066 rfl rfl) (Ns132p2068 rfl rfl)) (Ns132p2069 qz11 qz53 rfl rfl rfl rfl (Ns132p2071 rfl)) (Ns132p2072 qz11 qz67 rfl rfl rfl rfl (Ns132p2074 rfl)) 

noncomputable abbrev qz272 := (RS133to150.d3 qz405 qz418 (@Enclosure.dec_le_dec qz405 qz418 377703 1000 379237 1000 qz408 qz421 rfl rfl rfl))

noncomputable abbrev qz802 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz272)

noncomputable def Ns132p2076 := @Enclosure.Real.IsNear.of_eq qz802 (hardyZApproximantRS₀ qz64) Bool.false 24148299990873535461 9223372036854775808 9900164270355591940565 Ns132p436 

noncomputable abbrev qz273 := (@Enclosure.dec_le_dec qz405 qz418 377703 1000 379237 1000 qz408 qz421 rfl rfl rfl)

noncomputable def Ns132p2077 := @Enclosure.Real.IsNear.pos_val qz802 24148299990873535461 9223372036854775808 9900164270355591940565 Ns132p436 (Ns132p2076 (RS133to150.d4 qz64 qz77 qz273) RS133to150.d42) rfl 

noncomputable abbrev qz803 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz272)

noncomputable def Ns132p2078 := @Enclosure.Real.IsNear.of_eq qz803 (hardyZApproximantRS₀ qz77) Bool.true 36913731482367578193 18446744073709551616 13398827884841335412937 Ns132p536 

noncomputable def Ns132p2079 := @Enclosure.Real.IsNear.neg_val qz803 36913731482367578193 18446744073709551616 13398827884841335412937 Ns132p536 (Ns132p2078 (RS133to150.d38 qz64 qz77 qz273) RS133to150.d43) rfl 

noncomputable def Ns132p2080 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz802 qz4 qz64 373095 1000 377703 1000 

noncomputable def Ns132p2081 := @Enclosure.norm_gt_of_isNear qz802 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 24148299990873535461 9223372036854775808 9900164270355591940565 

noncomputable def Ns132p2082 := @Ns132p2081 Ns132p436 132459661 1342177280 1213 1342177280 (Ns132p2076 (RS133to150.d4 qz64 qz77 qz273) RS133to150.d42) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2083 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz803 qz4 qz77 373095 1000 379237 1000 

noncomputable def Ns132p2084 := @Enclosure.norm_gt_of_isNear qz803 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 36913731482367578193 18446744073709551616 13398827884841335412937 

noncomputable def Ns132p2085 := @Ns132p2084 Ns132p536 132459661 1342177280 1213 1342177280 (Ns132p2078 (RS133to150.d38 qz64 qz77 qz273) RS133to150.d43) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2086 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz272 (@BSN.thirtyTwoPi_le_dec qz64 377703 1000 qz67 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz802 qz803 (Ns132p2077 rfl rfl) (Ns132p2079 rfl rfl)) (Ns132p2080 qz11 qz67 rfl rfl rfl rfl (Ns132p2082 rfl)) (Ns132p2083 qz11 qz80 rfl rfl rfl rfl (Ns132p2085 rfl)) 

noncomputable abbrev qz274 := (RS133to150.d3 qz418 qz431 (@Enclosure.dec_le_dec qz418 qz431 379237 1000 380768 1000 qz421 qz434 rfl rfl rfl))

noncomputable abbrev qz804 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz274)

noncomputable def Ns132p2087 := @Enclosure.Real.IsNear.of_eq qz804 (hardyZApproximantRS₀ qz77) Bool.true 36913731482367578193 18446744073709551616 13398827884841335412937 Ns132p536 

noncomputable abbrev qz275 := (@Enclosure.dec_le_dec qz418 qz431 379237 1000 380768 1000 qz421 qz434 rfl rfl rfl)

noncomputable def Ns132p2088 := @Enclosure.Real.IsNear.neg_val qz804 36913731482367578193 18446744073709551616 13398827884841335412937 Ns132p536 (Ns132p2087 (RS133to150.d4 qz77 qz90 qz275) RS133to150.d43) rfl 

noncomputable abbrev qz805 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz274)

noncomputable def Ns132p2089 := @Enclosure.Real.IsNear.of_eq qz805 (hardyZApproximantRS₀ qz90) Bool.false 394199701600270142173 147573952589676412928 204436056441535363206813 Ns132p188 

noncomputable def Ns132p2090 := @Enclosure.Real.IsNear.pos_val qz805 394199701600270142173 147573952589676412928 204436056441535363206813 Ns132p188 (Ns132p2089 (RS133to150.d38 qz77 qz90 qz275) RS133to150.d44) rfl 

noncomputable def Ns132p2091 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz804 qz4 qz77 373095 1000 379237 1000 

noncomputable def Ns132p2092 := @Enclosure.norm_gt_of_isNear qz804 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 36913731482367578193 18446744073709551616 13398827884841335412937 

noncomputable def Ns132p2093 := @Ns132p2092 Ns132p536 132459661 1342177280 1213 1342177280 (Ns132p2087 (RS133to150.d4 qz77 qz90 qz275) RS133to150.d43) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2094 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz805 qz4 qz90 373095 1000 380768 1000 

noncomputable def Ns132p2095 := @Enclosure.norm_gt_of_isNear qz805 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 394199701600270142173 147573952589676412928 204436056441535363206813 

noncomputable def Ns132p2096 := @Ns132p2095 Ns132p188 132459661 1342177280 1213 1342177280 (Ns132p2089 (RS133to150.d38 qz77 qz90 qz275) RS133to150.d44) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2097 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz274 (@BSN.thirtyTwoPi_le_dec qz77 379237 1000 qz80 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz804 qz805 (Ns132p2088 rfl rfl) (Ns132p2090 rfl rfl)) (Ns132p2091 qz11 qz80 rfl rfl rfl rfl (Ns132p2093 rfl)) (Ns132p2094 qz11 qz93 rfl rfl rfl rfl (Ns132p2096 rfl)) 

noncomputable abbrev qz276 := (RS133to150.d3 qz431 qz444 (@Enclosure.dec_le_dec qz431 qz444 380768 1000 382298 1000 qz434 qz447 rfl rfl rfl))

noncomputable abbrev qz806 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz276)

noncomputable def Ns132p2098 := @Enclosure.Real.IsNear.of_eq qz806 (hardyZApproximantRS₀ qz90) Bool.false 394199701600270142173 147573952589676412928 204436056441535363206813 Ns132p188 

noncomputable abbrev qz277 := (@Enclosure.dec_le_dec qz431 qz444 380768 1000 382298 1000 qz434 qz447 rfl rfl rfl)

noncomputable def Ns132p2099 := @Enclosure.Real.IsNear.pos_val qz806 394199701600270142173 147573952589676412928 204436056441535363206813 Ns132p188 (Ns132p2098 (RS133to150.d4 qz90 qz103 qz277) RS133to150.d44) rfl 

noncomputable abbrev qz807 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz276)

noncomputable def Ns132p2100 := @Enclosure.Real.IsNear.of_eq qz807 (hardyZApproximantRS₀ qz103) Bool.true 1013711416401069003 288230376151711744 50407542938493963427547 Ns132p333 

noncomputable def Ns132p2101 := @Enclosure.Real.IsNear.neg_val qz807 1013711416401069003 288230376151711744 50407542938493963427547 Ns132p333 (Ns132p2100 (RS133to150.d38 qz90 qz103 qz277) RS133to150.d45) rfl 

noncomputable def Ns132p2102 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz806 qz4 qz90 373095 1000 380768 1000 

noncomputable def Ns132p2103 := @Enclosure.norm_gt_of_isNear qz806 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 394199701600270142173 147573952589676412928 204436056441535363206813 

noncomputable def Ns132p2104 := @Ns132p2103 Ns132p188 132459661 1342177280 1213 1342177280 (Ns132p2098 (RS133to150.d4 qz90 qz103 qz277) RS133to150.d44) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2105 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz807 qz4 qz103 373095 1000 382298 1000 

noncomputable def Ns132p2106 := @Enclosure.norm_gt_of_isNear qz807 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1013711416401069003 288230376151711744 50407542938493963427547 

noncomputable def Ns132p2107 := @Ns132p2106 Ns132p333 132459661 1342177280 1213 1342177280 (Ns132p2100 (RS133to150.d38 qz90 qz103 qz277) RS133to150.d45) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2108 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz276 (@BSN.thirtyTwoPi_le_dec qz90 380768 1000 qz93 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz806 qz807 (Ns132p2099 rfl rfl) (Ns132p2101 rfl rfl)) (Ns132p2102 qz11 qz93 rfl rfl rfl rfl (Ns132p2104 rfl)) (Ns132p2105 qz11 qz106 rfl rfl rfl rfl (Ns132p2107 rfl)) 

noncomputable abbrev qz607 := (@Enclosure.dec_le_dec qz681 qz688 382298 1000 383827 1000 (@Eq.refl Real qz681) (@Eq.refl Real qz688) rfl rfl rfl)

noncomputable abbrev qz278 := (RS133to150.d3 qz444 qz458 qz607)

noncomputable abbrev qz808 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz278)

noncomputable def Ns132p2109 := @Enclosure.Real.IsNear.of_eq qz808 (hardyZApproximantRS₀ qz103) Bool.true 1013711416401069003 288230376151711744 50407542938493963427547 Ns132p333 

noncomputable abbrev qz279 := qz607

noncomputable def Ns132p2110 := @Enclosure.Real.IsNear.neg_val qz808 1013711416401069003 288230376151711744 50407542938493963427547 Ns132p333 (Ns132p2109 (RS133to150.d4 qz103 qz116 qz279) RS133to150.d45) rfl 

noncomputable abbrev qz809 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz278)

noncomputable def Ns132p2111 := @Enclosure.Real.IsNear.of_eq qz809 (hardyZApproximantRS₀ qz116) Bool.false 5937915631679315209 4611686018427387904 783184319052684071085 493025552397282882617344 

noncomputable def Ns132p2112 := @Enclosure.Real.IsNear.pos_val qz809 5937915631679315209 4611686018427387904 783184319052684071085 493025552397282882617344 (Ns132p2111 (RS133to150.d38 qz103 qz116 qz279) RS133to150.d46) rfl 

noncomputable def Ns132p2113 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz808 qz4 qz103 373095 1000 382298 1000 

noncomputable def Ns132p2114 := @Enclosure.norm_gt_of_isNear qz808 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1013711416401069003 288230376151711744 50407542938493963427547 

noncomputable def Ns132p2115 := @Ns132p2114 Ns132p333 132459661 1342177280 1213 1342177280 (Ns132p2109 (RS133to150.d4 qz103 qz116 qz279) RS133to150.d45) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2116 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz809 qz4 qz116 373095 1000 383827 1000 

noncomputable def Ns132p2117 := @Enclosure.norm_gt_of_isNear qz809 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 5937915631679315209 4611686018427387904 783184319052684071085 

noncomputable def Ns132p2118 := @Ns132p2117 493025552397282882617344 132459661 1342177280 1213 1342177280 (Ns132p2111 (RS133to150.d38 qz103 qz116 qz279) RS133to150.d46) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2119 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz278 (@BSN.thirtyTwoPi_le_dec qz103 382298 1000 qz106 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz808 qz809 (Ns132p2110 rfl rfl) (Ns132p2112 rfl rfl)) (Ns132p2113 qz11 qz106 rfl rfl rfl rfl (Ns132p2115 rfl)) (Ns132p2116 qz11 qz119 rfl rfl rfl rfl (Ns132p2118 rfl)) 

noncomputable abbrev qz608 := (@Enclosure.dec_le_dec qz688 qz695 383827 1000 385354 1000 (@Eq.refl Real qz688) qz699 rfl rfl rfl)

noncomputable abbrev qz280 := (RS133to150.d3 qz458 qz471 qz608)

noncomputable abbrev qz810 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz280)

noncomputable def Ns132p2120 := @Enclosure.Real.IsNear.of_eq qz810 (hardyZApproximantRS₀ qz116) Bool.false 5937915631679315209 4611686018427387904 783184319052684071085 493025552397282882617344 

noncomputable abbrev qz281 := qz608

noncomputable def Ns132p2121 := @Enclosure.Real.IsNear.pos_val qz810 5937915631679315209 4611686018427387904 783184319052684071085 493025552397282882617344 (Ns132p2120 (RS133to150.d4 qz116 qz129 qz281) RS133to150.d46) rfl 

noncomputable abbrev qz811 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz280)

noncomputable def Ns132p2122 := @Enclosure.Real.IsNear.of_eq qz811 (hardyZApproximantRS₀ qz129) Bool.true 74467141954229663009 147573952589676412928 200088021055845830440939 Ns132p188 

noncomputable def Ns132p2123 := @Enclosure.Real.IsNear.neg_val qz811 74467141954229663009 147573952589676412928 200088021055845830440939 Ns132p188 (Ns132p2122 (RS133to150.d38 qz116 qz129 qz281) RS133to150.d47) rfl 

noncomputable def Ns132p2124 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz810 qz4 qz116 373095 1000 383827 1000 

noncomputable def Ns132p2125 := @Enclosure.norm_gt_of_isNear qz810 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 5937915631679315209 4611686018427387904 783184319052684071085 

noncomputable def Ns132p2126 := @Ns132p2125 493025552397282882617344 132459661 1342177280 1213 1342177280 (Ns132p2120 (RS133to150.d4 qz116 qz129 qz281) RS133to150.d46) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2127 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz811 qz4 qz129 373095 1000 385354 1000 

noncomputable def Ns132p2128 := @Enclosure.norm_gt_of_isNear qz811 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 74467141954229663009 147573952589676412928 200088021055845830440939 

noncomputable def Ns132p2129 := @Ns132p2128 Ns132p188 132459661 1342177280 1213 1342177280 (Ns132p2122 (RS133to150.d38 qz116 qz129 qz281) RS133to150.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2130 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz280 (@BSN.thirtyTwoPi_le_dec qz116 383827 1000 qz119 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz810 qz811 (Ns132p2121 rfl rfl) (Ns132p2123 rfl rfl)) (Ns132p2124 qz11 qz119 rfl rfl rfl rfl (Ns132p2126 rfl)) (Ns132p2127 qz11 qz132 rfl rfl rfl rfl (Ns132p2129 rfl)) 

noncomputable abbrev qz609 := (@Enclosure.dec_le_dec qz695 qz704 385354 1000 386880 1000 qz699 qz708 rfl rfl rfl)

noncomputable abbrev qz282 := (RS133to150.d3 qz471 qz483 qz609)

noncomputable abbrev qz812 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz282)

noncomputable def Ns132p2131 := @Enclosure.Real.IsNear.of_eq qz812 (hardyZApproximantRS₀ qz129) Bool.true 74467141954229663009 147573952589676412928 200088021055845830440939 Ns132p188 

noncomputable abbrev qz283 := qz609

noncomputable def Ns132p2132 := @Enclosure.Real.IsNear.neg_val qz812 74467141954229663009 147573952589676412928 200088021055845830440939 Ns132p188 (Ns132p2131 (RS133to150.d4 qz129 qz142 qz283) RS133to150.d47) rfl 

noncomputable abbrev qz813 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz282)

noncomputable def Ns132p2133 := @Enclosure.Real.IsNear.of_eq qz813 (hardyZApproximantRS₀ qz142) Bool.false 69489683684569863375 73786976294838206464 200317091860219670062423 Ns132p188 

noncomputable def Ns132p2134 := @Enclosure.Real.IsNear.pos_val qz813 69489683684569863375 73786976294838206464 200317091860219670062423 Ns132p188 (Ns132p2133 (RS133to150.d38 qz129 qz142 qz283) RS133to150.d48) rfl 

noncomputable def Ns132p2135 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz812 qz4 qz129 373095 1000 385354 1000 

noncomputable def Ns132p2136 := @Enclosure.norm_gt_of_isNear qz812 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 74467141954229663009 147573952589676412928 200088021055845830440939 

noncomputable def Ns132p2137 := @Ns132p2136 Ns132p188 132459661 1342177280 1213 1342177280 (Ns132p2131 (RS133to150.d4 qz129 qz142 qz283) RS133to150.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2138 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz813 qz4 qz142 373095 1000 386880 1000 

noncomputable def Ns132p2139 := @Enclosure.norm_gt_of_isNear qz813 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 69489683684569863375 73786976294838206464 200317091860219670062423 

noncomputable def Ns132p2140 := @Ns132p2139 Ns132p188 132459661 1342177280 1213 1342177280 (Ns132p2133 (RS133to150.d38 qz129 qz142 qz283) RS133to150.d48) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2141 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz282 (@BSN.thirtyTwoPi_le_dec qz129 385354 1000 qz132 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz812 qz813 (Ns132p2132 rfl rfl) (Ns132p2134 rfl rfl)) (Ns132p2135 qz11 qz132 rfl rfl rfl rfl (Ns132p2137 rfl)) (Ns132p2138 qz11 qz145 rfl rfl rfl rfl (Ns132p2140 rfl)) 

noncomputable abbrev qz814 := (@Enclosure.dec_le_dec qz881 qz885 386880 1000 388404 1000 (@Eq.refl Real qz881) qz888 rfl rfl rfl)

noncomputable abbrev qz610 := qz814

noncomputable abbrev qz284 := (RS133to150.d3 qz483 qz495 qz610)

noncomputable abbrev qz815 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz284)

noncomputable def Ns132p2142 := @Enclosure.Real.IsNear.of_eq qz815 (hardyZApproximantRS₀ qz142) Bool.false 69489683684569863375 73786976294838206464 200317091860219670062423 Ns132p188 

noncomputable abbrev qz285 := qz610

noncomputable def Ns132p2143 := @Enclosure.Real.IsNear.pos_val qz815 69489683684569863375 73786976294838206464 200317091860219670062423 Ns132p188 (Ns132p2142 (RS133to150.d4 qz142 qz155 qz285) RS133to150.d48) rfl 

noncomputable abbrev qz816 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz284)

noncomputable def Ns132p2144 := @Enclosure.Real.IsNear.of_eq qz816 (hardyZApproximantRS₀ qz155) Bool.true 81549144201289938205 36893488147419103232 50139479048963994546115 Ns132p333 

noncomputable def Ns132p2145 := @Enclosure.Real.IsNear.neg_val qz816 81549144201289938205 36893488147419103232 50139479048963994546115 Ns132p333 (Ns132p2144 (RS133to150.d38 qz142 qz155 qz285) RS133to150.d49) rfl 

noncomputable def Ns132p2146 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz815 qz4 qz142 373095 1000 386880 1000 

noncomputable def Ns132p2147 := @Enclosure.norm_gt_of_isNear qz815 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 69489683684569863375 73786976294838206464 200317091860219670062423 

noncomputable def Ns132p2148 := @Ns132p2147 Ns132p188 132459661 1342177280 1213 1342177280 (Ns132p2142 (RS133to150.d4 qz142 qz155 qz285) RS133to150.d48) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2149 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz816 qz4 qz155 373095 1000 388404 1000 

noncomputable def Ns132p2150 := @Enclosure.norm_gt_of_isNear qz816 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 81549144201289938205 36893488147419103232 50139479048963994546115 

noncomputable def Ns132p2151 := @Ns132p2150 Ns132p333 132459661 1342177280 1213 1342177280 (Ns132p2144 (RS133to150.d38 qz142 qz155 qz285) RS133to150.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2152 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz142 386880 1000 qz145 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz815 qz816 (Ns132p2143 rfl rfl) (Ns132p2145 rfl rfl)) (Ns132p2146 qz11 qz145 rfl rfl rfl rfl (Ns132p2148 rfl)) (Ns132p2149 qz11 qz158 rfl rfl rfl rfl (Ns132p2151 rfl)) 

noncomputable abbrev qz924 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 388404 1000) (Enclosure.sfrac Bool.false 390688 1000) 388404 1000 390688 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 388404 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 390688 1000)) rfl rfl rfl)

noncomputable abbrev qz817 := qz924

noncomputable abbrev qz611 := qz817

noncomputable abbrev qz286 := (RS133to150.d3 qz495 qz507 qz611)

noncomputable abbrev qz818 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz286)

noncomputable def Ns132p2153 := @Enclosure.Real.IsNear.of_eq qz818 (hardyZApproximantRS₀ qz155) Bool.true 81549144201289938205 36893488147419103232 50139479048963994546115 Ns132p333 

noncomputable abbrev qz287 := qz611

noncomputable def Ns132p2154 := @Enclosure.Real.IsNear.neg_val qz818 81549144201289938205 36893488147419103232 50139479048963994546115 Ns132p333 (Ns132p2153 (RS133to150.d4 qz155 qz168 qz287) RS133to150.d49) rfl 

noncomputable abbrev qz819 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz286)

noncomputable def Ns132p2155 := @Enclosure.Real.IsNear.of_eq qz819 (hardyZApproximantRS₀ qz168) Bool.false 577088349212219122127 147573952589676412928 201023974859585045867543 Ns132p188 

noncomputable def Ns132p2156 := @Enclosure.Real.IsNear.pos_val qz819 577088349212219122127 147573952589676412928 201023974859585045867543 Ns132p188 (Ns132p2155 (RS133to150.d38 qz155 qz168 qz287) RS133to150.d50) rfl 

noncomputable def Ns132p2157 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz818 qz4 qz155 373095 1000 388404 1000 

noncomputable def Ns132p2158 := @Enclosure.norm_gt_of_isNear qz818 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 81549144201289938205 36893488147419103232 50139479048963994546115 

noncomputable def Ns132p2159 := @Ns132p2158 Ns132p333 132459661 1342177280 1213 1342177280 (Ns132p2153 (RS133to150.d4 qz155 qz168 qz287) RS133to150.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2160 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz819 qz4 qz168 373095 1000 390688 1000 

noncomputable def Ns132p2161 := @Enclosure.norm_gt_of_isNear qz819 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 577088349212219122127 147573952589676412928 201023974859585045867543 

noncomputable def Ns132p2162 := @Ns132p2161 Ns132p188 132459661 1342177280 1213 1342177280 (Ns132p2155 (RS133to150.d38 qz155 qz168 qz287) RS133to150.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2163 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz286 (@BSN.thirtyTwoPi_le_dec qz155 388404 1000 qz158 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz818 qz819 (Ns132p2154 rfl rfl) (Ns132p2156 rfl rfl)) (Ns132p2157 qz11 qz158 rfl rfl rfl rfl (Ns132p2159 rfl)) (Ns132p2160 qz11 qz171 rfl rfl rfl rfl (Ns132p2162 rfl)) 

noncomputable abbrev qz288 := (RS133to150.d3 qz507 qz519 (@Enclosure.dec_le_dec qz507 qz519 390688 1000 391923 1000 qz510 qz522 rfl rfl rfl))

noncomputable abbrev qz820 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz288)

noncomputable def Ns132p2164 := @Enclosure.Real.IsNear.of_eq qz820 (hardyZApproximantRS₀ qz168) Bool.false 577088349212219122127 147573952589676412928 201023974859585045867543 Ns132p188 

noncomputable abbrev qz289 := (@Enclosure.dec_le_dec qz507 qz519 390688 1000 391923 1000 qz510 qz522 rfl rfl rfl)

noncomputable def Ns132p2165 := @Enclosure.Real.IsNear.pos_val qz820 577088349212219122127 147573952589676412928 201023974859585045867543 Ns132p188 (Ns132p2164 (RS133to150.d4 qz168 qz181 qz289) RS133to150.d50) rfl 

noncomputable abbrev qz821 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz288)

noncomputable def Ns132p2166 := @Enclosure.Real.IsNear.of_eq qz821 (hardyZApproximantRS₀ qz181) Bool.true 4381795143466873551 9223372036854775808 25199168551559296265843 Ns132p1332 

noncomputable def Ns132p2167 := @Enclosure.Real.IsNear.neg_val qz821 4381795143466873551 9223372036854775808 25199168551559296265843 Ns132p1332 (Ns132p2166 (RS133to150.d38 qz168 qz181 qz289) RS133to150.d51) rfl 

noncomputable def Ns132p2168 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz820 qz4 qz168 373095 1000 390688 1000 

noncomputable def Ns132p2169 := @Enclosure.norm_gt_of_isNear qz820 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 577088349212219122127 147573952589676412928 201023974859585045867543 

noncomputable def Ns132p2170 := @Ns132p2169 Ns132p188 132459661 1342177280 1213 1342177280 (Ns132p2164 (RS133to150.d4 qz168 qz181 qz289) RS133to150.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2171 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz821 qz4 qz181 373095 1000 391923 1000 

noncomputable def Ns132p2172 := @Enclosure.norm_gt_of_isNear qz821 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 4381795143466873551 9223372036854775808 25199168551559296265843 

noncomputable def Ns132p2173 := @Ns132p2172 Ns132p1332 132459661 1342177280 1213 1342177280 (Ns132p2166 (RS133to150.d38 qz168 qz181 qz289) RS133to150.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2174 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz168 390688 1000 qz171 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz820 qz821 (Ns132p2165 rfl rfl) (Ns132p2167 rfl rfl)) (Ns132p2168 qz11 qz171 rfl rfl rfl rfl (Ns132p2170 rfl)) (Ns132p2171 qz11 qz184 rfl rfl rfl rfl (Ns132p2173 rfl)) 

noncomputable abbrev qz290 := (RS133to150.d3 qz519 qz531 (@Enclosure.dec_le_dec qz519 qz531 391923 1000 392683 1000 qz522 qz534 rfl rfl rfl))

noncomputable abbrev qz822 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz290)

noncomputable def Ns132p2175 := @Enclosure.Real.IsNear.of_eq qz822 (hardyZApproximantRS₀ qz181) Bool.true 4381795143466873551 9223372036854775808 25199168551559296265843 Ns132p1332 

noncomputable abbrev qz291 := (@Enclosure.dec_le_dec qz519 qz531 391923 1000 392683 1000 qz522 qz534 rfl rfl rfl)

noncomputable def Ns132p2176 := @Enclosure.Real.IsNear.neg_val qz822 4381795143466873551 9223372036854775808 25199168551559296265843 Ns132p1332 (Ns132p2175 (RS133to150.d4 qz181 qz194 qz291) RS133to150.d51) rfl 

noncomputable abbrev qz823 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz290)

noncomputable def Ns132p2177 := @Enclosure.Real.IsNear.of_eq qz823 (hardyZApproximantRS₀ qz194) Bool.false 226544310752128569 288230376151711744 50471170454443075628023 Ns132p333 

noncomputable def Ns132p2178 := @Enclosure.Real.IsNear.pos_val qz823 226544310752128569 288230376151711744 50471170454443075628023 Ns132p333 (Ns132p2177 (RS133to150.d38 qz181 qz194 qz291) RS133to150.d52) rfl 

noncomputable def Ns132p2179 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz822 qz4 qz181 373095 1000 391923 1000 

noncomputable def Ns132p2180 := @Enclosure.norm_gt_of_isNear qz822 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 4381795143466873551 9223372036854775808 25199168551559296265843 

noncomputable def Ns132p2181 := @Ns132p2180 Ns132p1332 132459661 1342177280 1213 1342177280 (Ns132p2175 (RS133to150.d4 qz181 qz194 qz291) RS133to150.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2182 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz823 qz4 qz194 373095 1000 392683 1000 

noncomputable def Ns132p2183 := @Enclosure.norm_gt_of_isNear qz823 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 226544310752128569 288230376151711744 50471170454443075628023 

noncomputable def Ns132p2184 := @Ns132p2183 Ns132p333 132459661 1342177280 1213 1342177280 (Ns132p2177 (RS133to150.d38 qz181 qz194 qz291) RS133to150.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2185 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz290 (@BSN.thirtyTwoPi_le_dec qz181 391923 1000 qz184 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz822 qz823 (Ns132p2176 rfl rfl) (Ns132p2178 rfl rfl)) (Ns132p2179 qz11 qz184 rfl rfl rfl rfl (Ns132p2181 rfl)) (Ns132p2182 qz11 qz197 rfl rfl rfl rfl (Ns132p2184 rfl)) 

noncomputable abbrev qz612 := (@Enclosure.dec_le_dec qz740 qz748 392683 1000 394487 1000 (@Eq.refl Real qz740) (@Eq.refl Real qz748) rfl rfl rfl)

noncomputable abbrev qz292 := (RS133to150.d3 qz531 qz543 qz612)

noncomputable abbrev qz824 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz292)

noncomputable def Ns132p2186 := @Enclosure.Real.IsNear.of_eq qz824 (hardyZApproximantRS₀ qz194) Bool.false 226544310752128569 288230376151711744 50471170454443075628023 Ns132p333 

noncomputable abbrev qz293 := qz612

noncomputable def Ns132p2187 := @Enclosure.Real.IsNear.pos_val qz824 226544310752128569 288230376151711744 50471170454443075628023 Ns132p333 (Ns132p2186 (RS133to150.d4 qz194 qz207 qz293) RS133to150.d52) rfl 

noncomputable abbrev qz825 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz292)

noncomputable def Ns132p2188 := @Enclosure.Real.IsNear.of_eq qz825 (hardyZApproximantRS₀ qz207) Bool.true 1631792408326609341 576460752303423488 202448144590515883091967 Ns132p188 

noncomputable def Ns132p2189 := @Enclosure.Real.IsNear.neg_val qz825 1631792408326609341 576460752303423488 202448144590515883091967 Ns132p188 (Ns132p2188 (RS133to150.d38 qz194 qz207 qz293) RS133to150.d53) rfl 

noncomputable def Ns132p2190 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz824 qz4 qz194 373095 1000 392683 1000 

noncomputable def Ns132p2191 := @Enclosure.norm_gt_of_isNear qz824 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 226544310752128569 288230376151711744 50471170454443075628023 

noncomputable def Ns132p2192 := @Ns132p2191 Ns132p333 132459661 1342177280 1213 1342177280 (Ns132p2186 (RS133to150.d4 qz194 qz207 qz293) RS133to150.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2193 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz825 qz4 qz207 373095 1000 394487 1000 

noncomputable def Ns132p2194 := @Enclosure.norm_gt_of_isNear qz825 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1631792408326609341 576460752303423488 202448144590515883091967 

noncomputable def Ns132p2195 := @Ns132p2194 Ns132p188 132459661 1342177280 1213 1342177280 (Ns132p2188 (RS133to150.d38 qz194 qz207 qz293) RS133to150.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2196 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz194 392683 1000 qz197 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz824 qz825 (Ns132p2187 rfl rfl) (Ns132p2189 rfl rfl)) (Ns132p2190 qz11 qz197 rfl rfl rfl rfl (Ns132p2192 rfl)) (Ns132p2193 qz11 qz210 rfl rfl rfl rfl (Ns132p2195 rfl)) 

noncomputable abbrev qz613 := (@Enclosure.dec_le_dec qz748 qz757 394487 1000 396004 1000 (@Eq.refl Real qz748) qz761 rfl rfl rfl)

noncomputable abbrev qz294 := (RS133to150.d3 qz543 qz556 qz613)

noncomputable abbrev qz826 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz294)

noncomputable def Ns132p2197 := @Enclosure.Real.IsNear.of_eq qz826 (hardyZApproximantRS₀ qz207) Bool.true 1631792408326609341 576460752303423488 202448144590515883091967 Ns132p188 

noncomputable abbrev qz295 := qz613

noncomputable def Ns132p2198 := @Enclosure.Real.IsNear.neg_val qz826 1631792408326609341 576460752303423488 202448144590515883091967 Ns132p188 (Ns132p2197 (RS133to150.d4 qz207 qz219 qz295) RS133to150.d53) rfl 

noncomputable abbrev qz827 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz294)

noncomputable def Ns132p2199 := @Enclosure.Real.IsNear.of_eq qz827 (hardyZApproximantRS₀ qz219) Bool.false 157642380800787929227 295147905179352825856 406480174400856375572547 Ns132p1641 

noncomputable def Ns132p2200 := @Enclosure.Real.IsNear.pos_val qz827 157642380800787929227 295147905179352825856 406480174400856375572547 Ns132p1641 (Ns132p2199 (RS133to150.d38 qz207 qz219 qz295) RS133to150.d54) rfl 

noncomputable def Ns132p2201 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz826 qz4 qz207 373095 1000 394487 1000 

noncomputable def Ns132p2202 := @Enclosure.norm_gt_of_isNear qz826 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1631792408326609341 576460752303423488 202448144590515883091967 

noncomputable def Ns132p2203 := @Ns132p2202 Ns132p188 132459661 1342177280 1213 1342177280 (Ns132p2197 (RS133to150.d4 qz207 qz219 qz295) RS133to150.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2204 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz827 qz4 qz219 373095 1000 396004 1000 

noncomputable def Ns132p2205 := @Enclosure.norm_gt_of_isNear qz827 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 157642380800787929227 295147905179352825856 406480174400856375572547 

noncomputable def Ns132p2206 := @Ns132p2205 Ns132p1641 132459661 1342177280 1213 1342177280 (Ns132p2199 (RS133to150.d38 qz207 qz219 qz295) RS133to150.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2207 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz294 (@BSN.thirtyTwoPi_le_dec qz207 394487 1000 qz210 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz826 qz827 (Ns132p2198 rfl rfl) (Ns132p2200 rfl rfl)) (Ns132p2201 qz11 qz210 rfl rfl rfl rfl (Ns132p2203 rfl)) (Ns132p2204 qz11 qz222 rfl rfl rfl rfl (Ns132p2206 rfl)) 

noncomputable abbrev qz614 := (@Enclosure.dec_le_dec qz757 qz767 396004 1000 397519 1000 qz761 qz771 rfl rfl rfl)

noncomputable abbrev qz296 := (RS133to150.d3 qz556 qz569 qz614)

noncomputable abbrev qz828 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz296)

noncomputable def Ns132p2208 := @Enclosure.Real.IsNear.of_eq qz828 (hardyZApproximantRS₀ qz219) Bool.false 157642380800787929227 295147905179352825856 406480174400856375572547 Ns132p1641 

noncomputable abbrev qz297 := qz614

noncomputable def Ns132p2209 := @Enclosure.Real.IsNear.pos_val qz828 157642380800787929227 295147905179352825856 406480174400856375572547 Ns132p1641 (Ns132p2208 (RS133to150.d4 qz219 qz231 qz297) RS133to150.d54) rfl 

noncomputable abbrev qz829 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz296)

noncomputable def Ns132p2210 := @Enclosure.Real.IsNear.of_eq qz829 (hardyZApproximantRS₀ qz231) Bool.true 118501993388451508249 73786976294838206464 101987130177363194739947 Ns132p64 

noncomputable def Ns132p2211 := @Enclosure.Real.IsNear.neg_val qz829 118501993388451508249 73786976294838206464 101987130177363194739947 Ns132p64 (Ns132p2210 (RS133to150.d38 qz219 qz231 qz297) RS133to150.d55) rfl 

noncomputable def Ns132p2212 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz828 qz4 qz219 373095 1000 396004 1000 

noncomputable def Ns132p2213 := @Enclosure.norm_gt_of_isNear qz828 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 157642380800787929227 295147905179352825856 406480174400856375572547 

noncomputable def Ns132p2214 := @Ns132p2213 Ns132p1641 132459661 1342177280 1213 1342177280 (Ns132p2208 (RS133to150.d4 qz219 qz231 qz297) RS133to150.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2215 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz829 qz4 qz231 373095 1000 397519 1000 

noncomputable def Ns132p2216 := @Enclosure.norm_gt_of_isNear qz829 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 118501993388451508249 73786976294838206464 101987130177363194739947 

noncomputable def Ns132p2217 := @Ns132p2216 Ns132p64 132459661 1342177280 1213 1342177280 (Ns132p2210 (RS133to150.d38 qz219 qz231 qz297) RS133to150.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2218 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz296 (@BSN.thirtyTwoPi_le_dec qz219 396004 1000 qz222 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz828 qz829 (Ns132p2209 rfl rfl) (Ns132p2211 rfl rfl)) (Ns132p2212 qz11 qz222 rfl rfl rfl rfl (Ns132p2214 rfl)) (Ns132p2215 qz11 qz234 rfl rfl rfl rfl (Ns132p2217 rfl)) 

noncomputable abbrev qz830 := (@Enclosure.dec_le_dec qz911 qz915 397519 1000 399034 1000 (@Eq.refl Real qz911) qz918 rfl rfl rfl)

noncomputable abbrev qz615 := qz830

noncomputable abbrev qz298 := (RS133to150.d3 qz569 qz582 qz615)

noncomputable abbrev qz831 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz298)

noncomputable def Ns132p2219 := @Enclosure.Real.IsNear.of_eq qz831 (hardyZApproximantRS₀ qz231) Bool.true 118501993388451508249 73786976294838206464 101987130177363194739947 Ns132p64 

noncomputable abbrev qz299 := qz615

noncomputable def Ns132p2220 := @Enclosure.Real.IsNear.neg_val qz831 118501993388451508249 73786976294838206464 101987130177363194739947 Ns132p64 (Ns132p2219 (RS133to150.d4 qz231 qz243 qz299) RS133to150.d55) rfl 

noncomputable abbrev qz832 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz298)

noncomputable def Ns132p2221 := @Enclosure.Real.IsNear.of_eq qz832 (hardyZApproximantRS₀ qz243) Bool.false 169017365106249623819 36893488147419103232 51172574316781002214065 Ns132p333 

noncomputable def Ns132p2222 := @Enclosure.Real.IsNear.pos_val qz832 169017365106249623819 36893488147419103232 51172574316781002214065 Ns132p333 (Ns132p2221 (RS133to150.d38 qz231 qz243 qz299) RS133to150.d56) rfl 

noncomputable def Ns132p2223 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz831 qz4 qz231 373095 1000 397519 1000 

noncomputable def Ns132p2224 := @Enclosure.norm_gt_of_isNear qz831 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 118501993388451508249 73786976294838206464 101987130177363194739947 

noncomputable def Ns132p2225 := @Ns132p2224 Ns132p64 132459661 1342177280 1213 1342177280 (Ns132p2219 (RS133to150.d4 qz231 qz243 qz299) RS133to150.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2226 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz832 qz4 qz243 373095 1000 399034 1000 

noncomputable def Ns132p2227 := @Enclosure.norm_gt_of_isNear qz832 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 169017365106249623819 36893488147419103232 51172574316781002214065 

noncomputable def Ns132p2228 := @Ns132p2227 Ns132p333 132459661 1342177280 1213 1342177280 (Ns132p2221 (RS133to150.d38 qz231 qz243 qz299) RS133to150.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2229 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz298 (@BSN.thirtyTwoPi_le_dec qz231 397519 1000 qz234 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz831 qz832 (Ns132p2220 rfl rfl) (Ns132p2222 rfl rfl)) (Ns132p2223 qz11 qz234 rfl rfl rfl rfl (Ns132p2225 rfl)) (Ns132p2226 qz11 qz246 rfl rfl rfl rfl (Ns132p2228 rfl)) 

noncomputable abbrev qz925 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 399034 1000) (Enclosure.sfrac Bool.false 400547 1000) 399034 1000 400547 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 399034 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 400547 1000)) rfl rfl rfl)

noncomputable abbrev qz833 := qz925

noncomputable abbrev qz616 := qz833

noncomputable abbrev qz300 := (RS133to150.d3 qz582 qz595 qz616)

noncomputable abbrev qz834 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz300)

noncomputable def Ns132p2230 := @Enclosure.Real.IsNear.of_eq qz834 (hardyZApproximantRS₀ qz243) Bool.false 169017365106249623819 36893488147419103232 51172574316781002214065 Ns132p333 

noncomputable abbrev qz301 := qz616

noncomputable def Ns132p2231 := @Enclosure.Real.IsNear.pos_val qz834 169017365106249623819 36893488147419103232 51172574316781002214065 Ns132p333 (Ns132p2230 (RS133to150.d4 qz243 qz255 qz301) RS133to150.d56) rfl 

noncomputable abbrev qz835 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz300)

noncomputable def Ns132p2232 := @Enclosure.Real.IsNear.of_eq qz835 (hardyZApproximantRS₀ qz255) Bool.true 51353211110473751011 18446744073709551616 25682836709296891652141 Ns132p1332 

noncomputable def Ns132p2233 := @Enclosure.Real.IsNear.neg_val qz835 51353211110473751011 18446744073709551616 25682836709296891652141 Ns132p1332 (Ns132p2232 (RS133to150.d38 qz243 qz255 qz301) RS133to150.d57) rfl 

noncomputable def Ns132p2234 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz834 qz4 qz243 373095 1000 399034 1000 

noncomputable def Ns132p2235 := @Enclosure.norm_gt_of_isNear qz834 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 169017365106249623819 36893488147419103232 51172574316781002214065 

noncomputable def Ns132p2236 := @Ns132p2235 Ns132p333 132459661 1342177280 1213 1342177280 (Ns132p2230 (RS133to150.d4 qz243 qz255 qz301) RS133to150.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2237 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz835 qz4 qz255 373095 1000 400547 1000 

noncomputable def Ns132p2238 := @Enclosure.norm_gt_of_isNear qz835 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 51353211110473751011 18446744073709551616 25682836709296891652141 

noncomputable def Ns132p2239 := @Ns132p2238 Ns132p1332 132459661 1342177280 1213 1342177280 (Ns132p2232 (RS133to150.d38 qz243 qz255 qz301) RS133to150.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 132459661 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS133to150.d40) rfl rfl rfl rfl 

noncomputable def Ns132p2240 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz243 399034 1000 qz246 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz834 qz835 (Ns132p2231 rfl rfl) (Ns132p2233 rfl rfl)) (Ns132p2234 qz11 qz246 rfl rfl rfl rfl (Ns132p2236 rfl)) (Ns132p2237 qz11 (@Eq.refl Real qz255) rfl rfl rfl rfl (Ns132p2239 rfl)) 

noncomputable def Ns132p2241 := @List.cons RS133to150.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz298 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz298) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz298) Ns132p2229)) (@List.cons RS133to150.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns132p2240)) (@List.nil RS133to150.d0)) 

noncomputable def Ns132p2242 := @List.cons RS133to150.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz294 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz294) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz294) Ns132p2207)) (@List.cons RS133to150.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns132p2218)) Ns132p2241) 

noncomputable def Ns132p2243 := @List.cons RS133to150.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz290 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz290) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz290) Ns132p2185)) (@List.cons RS133to150.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns132p2196)) Ns132p2242) 

noncomputable def Ns132p2244 := @List.cons RS133to150.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz286 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz286) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz286) Ns132p2163)) (@List.cons RS133to150.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns132p2174)) Ns132p2243) 

noncomputable def Ns132p2245 := @List.cons RS133to150.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz282 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz282) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz282) Ns132p2141)) (@List.cons RS133to150.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns132p2152)) Ns132p2244) 

noncomputable def Ns132p2246 := @List.cons RS133to150.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz278 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz278) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz278) Ns132p2119)) (@List.cons RS133to150.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz280 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz280) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz280) Ns132p2130)) Ns132p2245) 

noncomputable def Ns132p2247 := @List.cons RS133to150.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz274 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz274) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz274) Ns132p2097)) (@List.cons RS133to150.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz276 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz276) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz276) Ns132p2108)) Ns132p2246) 

noncomputable def Ns132p2248 := @List.cons RS133to150.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz270 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz270) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz270) Ns132p2075)) (@List.cons RS133to150.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz272 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz272) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz272) Ns132p2086)) Ns132p2247) 

noncomputable def Ns132p2249 := @List.cons RS133to150.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz266 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz266) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz266) Ns132p2053)) (@List.cons RS133to150.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz268 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz268) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz268) Ns132p2064)) Ns132p2248) 

noncomputable abbrev qz836 := (RS133to150.d2 qz911 qz915 (@Enclosure.dec_le_dec qz911 qz915 397519 1000 399034 1000 (@Eq.refl Real qz911) qz918 rfl rfl rfl))

noncomputable abbrev qz837 := (@List.cons RS133to150.d1 (RS133to150.d2 qz915 qz920 qz925) (@List.nil RS133to150.d1))

noncomputable abbrev qz617 := (@List.cons RS133to150.d1 (RS133to150.d2 qz757 qz767 (@Enclosure.dec_le_dec qz757 qz767 396004 1000 397519 1000 qz761 qz771 rfl rfl rfl)) (@List.cons RS133to150.d1 qz836 qz837))

noncomputable abbrev qz302 := (@List.cons RS133to150.d1 (RS133to150.d2 qz531 qz543 qz612) (@List.cons RS133to150.d1 (RS133to150.d2 qz543 qz556 qz613) qz617))

noncomputable def Ns132p2250 := @List.cons RS133to150.d1 (RS133to150.d2 qz168 qz181 qz289) (@List.cons RS133to150.d1 (RS133to150.d2 qz181 qz194 qz291) qz302) 

noncomputable abbrev qz838 := (RS133to150.d2 qz881 qz885 (@Enclosure.dec_le_dec qz881 qz885 386880 1000 388404 1000 (@Eq.refl Real qz881) qz888 rfl rfl rfl))

noncomputable abbrev qz839 := (@List.cons RS133to150.d1 (RS133to150.d2 qz885 qz890 qz924) Ns132p2250)

noncomputable abbrev qz618 := (@List.cons RS133to150.d1 (RS133to150.d2 qz695 qz704 (@Enclosure.dec_le_dec qz695 qz704 385354 1000 386880 1000 qz699 qz708 rfl rfl rfl)) (@List.cons RS133to150.d1 qz838 qz839))

noncomputable abbrev qz303 := (@List.cons RS133to150.d1 (RS133to150.d2 qz444 qz458 qz607) (@List.cons RS133to150.d1 (RS133to150.d2 qz458 qz471 qz608) qz618))

noncomputable def Ns132p2251 := @List.cons RS133to150.d1 (RS133to150.d2 qz77 qz90 qz275) (@List.cons RS133to150.d1 (RS133to150.d2 qz90 qz103 qz277) qz303) 

noncomputable def Ns132p2252 := @List.IsChain.cons_cons RS133to150.d1 RS133to150.d58 (RS133to150.d2 qz64 qz77 qz273) (RS133to150.d2 qz77 qz90 qz275) (@List.cons RS133to150.d1 (RS133to150.d2 qz90 qz103 qz277) qz303) 

noncomputable def Ns132p2253 := @List.IsChain.cons_cons RS133to150.d1 RS133to150.d58 (RS133to150.d2 qz77 qz90 qz275) (RS133to150.d2 qz90 qz103 qz277) qz303 (@Enclosure.dec_le_dec qz90 qz90 380768 1000 380768 1000 qz93 qz93 rfl rfl rfl) 

noncomputable abbrev qz840 := (RS133to150.d2 qz885 qz890 qz924)

noncomputable abbrev qz619 := qz840

noncomputable abbrev qz304 := qz619

noncomputable def Ns132p2254 := @List.IsChain.cons_cons RS133to150.d1 RS133to150.d58 qz304 (RS133to150.d2 qz168 qz181 qz289) (@List.cons RS133to150.d1 (RS133to150.d2 qz181 qz194 qz291) qz302) 

noncomputable def Ns132p2255 := @List.IsChain.cons_cons RS133to150.d1 RS133to150.d58 (RS133to150.d2 qz168 qz181 qz289) (RS133to150.d2 qz181 qz194 qz291) qz302 (@Enclosure.dec_le_dec qz181 qz181 391923 1000 391923 1000 qz184 qz184 rfl rfl rfl) 

noncomputable abbrev qz305 := qz617

noncomputable abbrev qz620 := (@List.cons RS133to150.d1 qz836 qz837)

noncomputable abbrev qz306 := qz620

noncomputable abbrev qz621 := qz836

noncomputable abbrev qz307 := qz621

noncomputable abbrev qz622 := qz837

noncomputable abbrev qz308 := qz622

noncomputable abbrev qz841 := (RS133to150.d2 qz915 qz920 qz925)

noncomputable abbrev qz623 := qz841

noncomputable abbrev qz309 := qz623

noncomputable def Ns132p2256 := @List.IsChain.cons_cons RS133to150.d1 RS133to150.d58 (RS133to150.d2 qz194 qz207 qz293) (RS133to150.d2 qz207 qz219 qz295) qz305 (@Enclosure.dec_le_dec qz207 qz207 394487 1000 394487 1000 qz210 qz210 rfl rfl rfl) (@List.IsChain.cons_cons RS133to150.d1 RS133to150.d58 (RS133to150.d2 qz207 qz219 qz295) (RS133to150.d2 qz219 qz231 qz297) qz306 (@Enclosure.dec_le_dec qz219 qz219 396004 1000 396004 1000 qz222 qz222 rfl rfl rfl) (@List.IsChain.cons_cons RS133to150.d1 RS133to150.d58 (RS133to150.d2 qz219 qz231 qz297) qz307 qz308 (@Enclosure.dec_le_dec qz231 qz231 397519 1000 397519 1000 qz234 qz234 rfl rfl rfl) (@List.IsChain.cons_cons RS133to150.d1 RS133to150.d58 qz307 qz309 (@List.nil RS133to150.d1) (@Enclosure.dec_le_dec qz243 qz243 399034 1000 399034 1000 qz246 qz246 rfl rfl rfl) (@List.IsChain.singleton RS133to150.d1 RS133to150.d58 qz309)))) 

noncomputable abbrev qz310 := (@List.cons RS133to150.d1 (RS133to150.d2 qz543 qz556 qz613) qz617)

noncomputable def Ns132p2257 := @List.IsChain.cons_cons RS133to150.d1 RS133to150.d58 (RS133to150.d2 qz181 qz194 qz291) (RS133to150.d2 qz194 qz207 qz293) qz310 (@Enclosure.dec_le_dec qz194 qz194 392683 1000 392683 1000 qz197 qz197 rfl rfl rfl) Ns132p2256 

noncomputable abbrev qz311 := qz618

noncomputable abbrev qz624 := (@List.cons RS133to150.d1 qz838 qz839)

noncomputable abbrev qz312 := qz624

noncomputable abbrev qz625 := qz838

noncomputable abbrev qz313 := qz625

noncomputable abbrev qz626 := qz839

noncomputable abbrev qz314 := qz626

noncomputable def Ns132p2258 := @List.IsChain.cons_cons RS133to150.d1 RS133to150.d58 (RS133to150.d2 qz103 qz116 qz279) (RS133to150.d2 qz116 qz129 qz281) qz311 (@Enclosure.dec_le_dec qz116 qz116 383827 1000 383827 1000 qz119 qz119 rfl rfl rfl) (@List.IsChain.cons_cons RS133to150.d1 RS133to150.d58 (RS133to150.d2 qz116 qz129 qz281) (RS133to150.d2 qz129 qz142 qz283) qz312 (@Enclosure.dec_le_dec qz129 qz129 385354 1000 385354 1000 qz132 qz132 rfl rfl rfl) (@List.IsChain.cons_cons RS133to150.d1 RS133to150.d58 (RS133to150.d2 qz129 qz142 qz283) qz313 qz314 (@Enclosure.dec_le_dec qz142 qz142 386880 1000 386880 1000 qz145 qz145 rfl rfl rfl) (@List.IsChain.cons_cons RS133to150.d1 RS133to150.d58 qz313 qz304 Ns132p2250 (@Enclosure.dec_le_dec qz155 qz155 388404 1000 388404 1000 qz158 qz158 rfl rfl rfl) (Ns132p2254 (@Enclosure.dec_le_dec qz168 qz168 390688 1000 390688 1000 qz171 qz171 rfl rfl rfl) (Ns132p2255 Ns132p2257))))) 

noncomputable abbrev qz315 := (@List.cons RS133to150.d1 (RS133to150.d2 qz458 qz471 qz608) qz618)

noncomputable def Ns132p2259 := @List.IsChain.cons_cons RS133to150.d1 RS133to150.d58 (RS133to150.d2 qz90 qz103 qz277) (RS133to150.d2 qz103 qz116 qz279) qz315 (@Enclosure.dec_le_dec qz103 qz103 382298 1000 382298 1000 qz106 qz106 rfl rfl rfl) Ns132p2258 

noncomputable def Ns132p2260 := Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns132p2249 (@List.IsChain.cons_cons RS133to150.d1 RS133to150.d58 (RS133to150.d2 qz4 qz30 qz267) (RS133to150.d2 qz30 qz50 qz269) (@List.cons RS133to150.d1 (RS133to150.d2 qz50 qz64 qz271) (@List.cons RS133to150.d1 (RS133to150.d2 qz64 qz77 qz273) Ns132p2251)) (@Enclosure.dec_le_dec qz30 qz30 374633 1000 374633 1000 qz33 qz33 rfl rfl rfl) (@List.IsChain.cons_cons RS133to150.d1 RS133to150.d58 (RS133to150.d2 qz30 qz50 qz269) (RS133to150.d2 qz50 qz64 qz271) (@List.cons RS133to150.d1 (RS133to150.d2 qz64 qz77 qz273) Ns132p2251) (@Enclosure.dec_le_dec qz50 qz50 376169 1000 376169 1000 qz53 qz53 rfl rfl rfl) (@List.IsChain.cons_cons RS133to150.d1 RS133to150.d58 (RS133to150.d2 qz50 qz64 qz271) (RS133to150.d2 qz64 qz77 qz273) Ns132p2251 (@Enclosure.dec_le_dec qz64 qz64 377703 1000 377703 1000 qz67 qz67 rfl rfl rfl) (Ns132p2252 (@Enclosure.dec_le_dec qz77 qz77 379237 1000 379237 1000 qz80 qz80 rfl rfl rfl) (Ns132p2253 Ns132p2259))))) 

noncomputable abbrev qz627 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz628 := (Zeta.Certificates.CertifiedZeroIntervals.intervals Ns132p2260)

theorem RS133to150.d59 : Zeta.Certificates.BatchSpec 18 373095 1000 400547 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz627 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 18) (And (@Eq (Option Real) (@Option.map qz627 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz627 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz627 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz627 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz255)))) Ns132p2260 (@And.intro (@Eq Nat (@List.length qz627 qz628) 18) (And (@Eq (Option Real) (@Option.map qz627 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz627 qz628)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz627 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz627 qz628)) (@Option.some Real qz255))) (@Eq.refl Nat 18) (@And.intro (@Eq (Option Real) (@Option.map qz627 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz627 qz628)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz627 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz627 qz628)) (@Option.some Real qz255)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz255))))

theorem solution : Zeta.Certificates.BatchSpec 18 373095 1000 400547 1000 := RS133to150.d59
#print axioms solution
#check solution
