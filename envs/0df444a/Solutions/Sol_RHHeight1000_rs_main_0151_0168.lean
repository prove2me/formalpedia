-- Prove2me | solution 1 for RHHeight1000.rs_main_0151_0168
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T07:46:09.016875+00:00
-- url     : https://prove2.me/submissions/64e9a986-9852-456c-96f9-fb32c9253c94

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

noncomputable def RS151to168.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS151to168.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS151to168.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS151to168.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS151to168.d2 a b h 

theorem RS151to168.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS151to168.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS151to168.d3 a b h)) 

noncomputable def Ns150p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns150p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns150p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns150p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns150p0 Ns150p1 Ns150p2 Ns150p1 76821522 67108864 1 31360000 76821522 67108864 1 31360000 38410761 33554432 2 33554432 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns150p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns150p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns150p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns150p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns150p8 := nat_lit 167537954069964697925743468333314178468718661948561187618563575975392713740913527107727581163208035826476740967700482432525301063254420572874757592895482956004842597348203117269212172556829666669574421653274845612596416189641484794702002223261246862056663160605878293700340502480877986491439034432953223334258717026053687371824342493299510132312376251152844516906794910572262907940062760396663270105627554083664899640691826599584783763757814813433640133591539937449421955686657622469485188711283992428713614179785896055117030632677201478317872225272595773536303110412989181984739022579128493081560758017763072115692678596043664844667144619713966763611484179303468167142547433165016751768184247559143333542643815355903304572487929375 

noncomputable def Ns150p9 := nat_lit 17907736863639440849562382641391758203535690054199171304015283257442503423240620144819838407313611418261944516207295868563739563278604805791797182761045687776939279949642059267526948014748996956777332184087524644234759874591635243045607722412471722018588244283882362848653445974523544951031470230725674276297342086185092985546835544820091590454230569790847977790484558207349923322458845585052164126500435851662252152223728079705692133047658564669873831757357628115566356048471439549797170528303905720944834637690907185213991407615774042056720704508980680095051114888612186461088301140868302968264130481206655302741383410655080008578156649725227045954510069588220729495895148666460653631514375880874422615237249871322129146554264800 

noncomputable def Ns150p10 := nat_lit 55164646516618494962085419356369025784335016154267579706247610053041231157772817011486486467101704279863254798704146668052276438579475100451766223896220272709675360577301802978530276301158911649961092601279696986330335403118086533522541958716560166657634553390183479955483588238249446822384543398154260439705049143284278540285021213103458182619368483938376641172730818250587232036579805400979202432024046862170503602539341971086573372247299262086029843105216008583038025403798224342134620653974939981235680083776396058604459065501719125356177784467570909658245422960948263734871602033841948787585406240093531041217463298165642337705122589129757920995868559518021463265498464182174549661735402095023640043996665674913376875 

noncomputable def Ns150p11 := BSN.log_dyadic_bound Ns150p6 Ns150p7 15 14 Ns150p8 67108864 31360000 Ns150p9 Ns150p10 76821522 Ns150p4 Ns150p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns150p6) (BSN.artanhQ Ns150p7) 0 14 Ns150p9 Ns150p8 Ns150p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns150p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns150p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns150p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns150p15 := nat_lit 167537954069966963268140139327979112712430526945422964221951926912223381190141639739514890494967825643602350173964944759828460064784215684919760383437959917620844610857567326816719640593037578236900835917107172977527392439886629774248115214831425484905681376157923696414882114961796820014026232307332015059110330001516939277521159573995394989771587717775443426002499543257897301982481613760098955890450106043861450716722534643739571053080256776912576113428445260435254713579381797931690799491102381747484553243404562568585572234105168360737285205910186933811836504830286397217473365026331067977496463917110493303316865058355012304571237619413071097245713770677768486493924969821719264401216877841676972336093778875903304572487929375 

noncomputable def Ns150p16 := nat_lit 17907736863639702486765313263906285882628955290251965205176678923530777959693011244026517850256414903756943142851250712732214241881959351517241344993825585048584379523049477943740273636414656012170312373198803997844271825165684859407921203335666024680974464565759223251918458072775203410604089667122984485578465112081892102496937045858735135721609691262763214794451343726045584198128451069547586972080574568545086657023793200560105564573365716615162566961587407171758966967827997201380802107846920231945878242774600967607639551032178207663699700360114112068650063802902647517702890145150192721997537569966984346993833704449560383184487996362781528900358997452380059737141488304159449328022742959995775545894292303322129146554264800 

noncomputable def Ns150p17 := nat_lit 55164646516619937449385584700664297411818070214438189962773666351465523500358685366424500506990751111492356556545320273548942244833046464529601272738875466881799996765940232256588350019911833156887888425998391295014189841212513610526066550079316346993943774342801096070086869790972589246312728227659319758310961510342377923950694747797317942483020440897997204711883064182772445608288320382376665481938194224815739627075458138172195220395246294556718284728034954178416253903237031389214179719385823921869528509431462690683227358218086518156757026652846493301460983550768858152506145788622699720737745394141184245149692548799188169247529408201840608223422296381897323845616153036586108326210125693898345963996665674913376875 

noncomputable def Ns150p18 := BSN.log_dyadic_bound Ns150p13 Ns150p14 15 14 Ns150p15 67108864 31360000 Ns150p16 Ns150p17 76821522 Ns150p12 Ns150p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns150p13) (BSN.artanhQ Ns150p14) 0 14 Ns150p16 Ns150p15 Ns150p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns150p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 38410761 33554432 2 33554432 38410761 33554432 1 16777216 (Ns150p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns150p0 Ns150p1 76821522 67108864 1 31360000 Bool.false (BSN.logfrac_isNear Ns150p4 Ns150p5 1 Ns150p0 Ns150p1 76821522 67108864 31360000 rfl rfl rfl (Ns150p11 rfl))) (BSN.isNear_log_sfrac Ns150p2 Ns150p1 76821522 67108864 1 31360000 Bool.false (BSN.logfrac_isNear Ns150p12 Ns150p5 1 Ns150p2 Ns150p1 76821522 67108864 31360000 rfl rfl rfl (Ns150p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS151to168.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 16777216 := Ns150p19 

noncomputable def Ns150p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 4194304 1960000 385100712855 135135 2907269 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz317 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz0 := qz317

theorem RS151to168.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 2907269 4194304 1 1960000 := BSN.isNear_log_sfrac 2 1 2907269 4194304 1 1960000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 2907269 4194304 1960000 rfl rfl rfl (Ns150p20 rfl)) 

theorem RS151to168.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 46516304 67108864 35 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 2907269 4194304 1 1960000 46516304 67108864 35 67108864 RS151to168.d6 rfl 

noncomputable abbrev qz318 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz319 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz320 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def Ns150p21 := @Enclosure.Real.IsNear.inv_image qz318 11863283 8388608 1 8388608 2965820 2965822 4194304 (@Enclosure.Real.IsNear.of_eq qz318 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz320)) Bool.false 11863283 8388608 1 8388608 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz320)) Bool.false 11863283 8388608 1 8388608 11863283 8388608 1 8388608 (BSN.sqrt_enclosure 2 1 5931641 5931642 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz321 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS151to168.d8 : Enclosure.Real.IsNear qz321 Bool.false 2965821 4194304 1 4194304 := @Enclosure.Real.IsNear.recentre' qz321 Bool.false 5931642 8388608 2 8388608 2965821 4194304 1 4194304 (Ns150p21 rfl rfl) rfl 

theorem RS151to168.d9 : Enclosure.Real.IsNear qz321 Bool.false 47453136 67108864 16 67108864 := @Enclosure.Real.IsNear.recentre' qz321 Bool.false 2965821 4194304 1 4194304 47453136 67108864 16 67108864 RS151to168.d8 rfl 

noncomputable def Ns150p22 := BSN.log_dyadic_bound 1 2 12 11 1326382131865190400 4194304 1960000 130797573554866995 13749310575 4607913 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 1) (BSN.artanhQ 2) 0 11 130797573554866995 1326382131865190400 13749310575 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS151to168.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 4607913 4194304 1 1960000 := BSN.isNear_log_sfrac 3 1 4607913 4194304 1 1960000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 4607913 4194304 1960000 rfl rfl rfl (Ns150p22 rfl)) 

theorem RS151to168.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 73726608 67108864 35 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 4607913 4194304 1 1960000 73726608 67108864 35 67108864 RS151to168.d10 rfl 

noncomputable abbrev qz322 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz323 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns150p23 := @Enclosure.Real.IsNear.inv_image qz322 14529495 8388608 1 8388608 2421582 2421583 4194304 (@Enclosure.Real.IsNear.of_eq qz322 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz323 qz320)) Bool.false 14529495 8388608 1 8388608 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz323 qz320)) Bool.false 14529495 8388608 1 8388608 14529495 8388608 1 8388608 (BSN.sqrt_enclosure 3 1 7264747 7264748 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz324 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS151to168.d12 : Enclosure.Real.IsNear qz324 Bool.false 4843165 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz324 Bool.false 4843165 8388608 1 8388608 4843165 8388608 1 8388608 (Ns150p23 rfl rfl) rfl 

theorem RS151to168.d13 : Enclosure.Real.IsNear qz324 Bool.false 38745320 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz324 Bool.false 4843165 8388608 1 8388608 38745320 67108864 8 67108864 RS151to168.d12 rfl 

noncomputable def Ns150p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns150p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns150p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns150p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns150p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns150p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns150p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns150p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns150p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns150p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns150p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns150p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns150p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns150p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns150p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns150p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns150p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns150p25 Ns150p26 Ns150p27 Ns150p28 200200021673987500790625 Ns150p29 Ns150p30 Ns150p31 Ns150p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns150p32 Ns150p33 151412625 Ns150p34 Ns150p35 1322214852783825 Ns150p27 Ns150p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns150p32 Ns150p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns150p34 Ns150p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns150p36 Ns150p37 1267389585 Ns150p38 Ns150p39 1927077560082675 Ns150p29 Ns150p30 Ns150p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns150p36 Ns150p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns150p38 Ns150p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz325 := (@Nat.cast Real Real.instNatCast 5)

theorem RS151to168.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz320 qz325)) Bool.false Ns150p24 Ns150p25 1 Ns150p26 := Ns150p40 rfl rfl rfl 

noncomputable def Ns150p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns150p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns150p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns150p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns150p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns150p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns150p25 Ns150p26 Ns150p42 Ns150p43 9945 Ns150p44 Ns150p45 65835 Ns150p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns150p42 Ns150p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns150p44 Ns150p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS151to168.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz320 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns150p41 Ns150p25 1 Ns150p26 := Ns150p46 rfl 

noncomputable def Ns150p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns150p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS151to168.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns150p47 Ns150p25 1 Ns150p48 := BSN.pi_combine Ns150p24 Ns150p41 Ns150p25 Ns150p26 Ns150p48 Ns150p47 rfl rfl rfl rfl RS151to168.d14 RS151to168.d15 

theorem RS151to168.d17 : Enclosure.Real.IsNear Real.pi Bool.false 3537118876014220 1125899906842624 1 1125899906842624 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns150p47 Ns150p25 1 Ns150p48 3537118876014220 1125899906842624 1 1125899906842624 RS151to168.d16 rfl 

noncomputable def Ns150p49 := nat_lit 178719669545544893480837345123291015625 

noncomputable def Ns150p50 := nat_lit 27745388228251122714770036239987464375 

noncomputable def Ns150p51 := nat_lit 1274524447665412456340166714375 

noncomputable def Ns150p52 := BSN.log_dyadic_bound 3 5 16 15 Ns150p49 4194304 1960000 Ns150p50 Ns150p51 5814539 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP 3) (BSN.artanhQ 5) 0 15 Ns150p50 Ns150p49 Ns150p51 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS151to168.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 5814539 4194304 1 1960000 := BSN.isNear_log_sfrac 4 1 5814539 4194304 1 1960000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 5814539 4194304 1960000 rfl rfl rfl (Ns150p52 rfl)) 

theorem RS151to168.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 93032624 67108864 35 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 5814539 4194304 1 1960000 93032624 67108864 35 67108864 RS151to168.d18 rfl 

noncomputable abbrev qz326 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz327 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns150p53 := @Enclosure.Real.IsNear.inv_image qz326 16777217 8388608 1 8388608 2097151 2097152 4194304 (@Enclosure.Real.IsNear.of_eq qz326 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz327 qz320)) Bool.false 16777217 8388608 1 8388608 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz327 qz320)) Bool.false 16777217 8388608 1 8388608 16777217 8388608 1 8388608 (BSN.sqrt_enclosure 4 1 8388608 8388609 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz328 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS151to168.d20 : Enclosure.Real.IsNear qz328 Bool.false 4194303 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz328 Bool.false 4194303 8388608 1 8388608 4194303 8388608 1 8388608 (Ns150p53 rfl rfl) rfl 

theorem RS151to168.d21 : Enclosure.Real.IsNear qz328 Bool.false 33554424 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz328 Bool.false 4194303 8388608 1 8388608 33554424 67108864 8 67108864 RS151to168.d20 rfl 

noncomputable def Ns150p54 := nat_lit 432044237847189949652629901200995702590625 

noncomputable def Ns150p55 := nat_lit 89467042677079332529401996239971435345500 

noncomputable def Ns150p56 := nat_lit 2254217236409302326906244300800000 

noncomputable def Ns150p57 := nat_lit 1703271991756449094855875 

noncomputable def Ns150p58 := BSN.log_dyadic_bound 2 3 20 19 Ns150p54 4194304 1960000 Ns150p55 Ns150p56 6750471 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 19 9 52520441922763380 253655458399017675 9033331507200 1156268355358836200013540 Ns150p57 249544393960587264000 Ns150p55 Ns150p54 Ns150p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 2) (BSN.artanhQ 3) 0 9 52520441922763380 253655458399017675 9033331507200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 9 19 1156268355358836200013540 Ns150p57 249544393960587264000 rfl rfl rfl rfl)) rfl rfl 

theorem RS151to168.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 6750471 4194304 1 1960000 := BSN.isNear_log_sfrac 5 1 6750471 4194304 1 1960000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 6750471 4194304 1960000 rfl rfl rfl (Ns150p58 rfl rfl)) 

theorem RS151to168.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 108007536 67108864 35 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 6750471 4194304 1 1960000 108007536 67108864 35 67108864 RS151to168.d22 rfl 

noncomputable abbrev qz329 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns150p59 := @Enclosure.Real.IsNear.inv_image qz329 18757497 8388608 1 8388608 1875749 1875750 4194304 (@Enclosure.Real.IsNear.of_eq qz329 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz325 qz320)) Bool.false 18757497 8388608 1 8388608 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz325 qz320)) Bool.false 18757497 8388608 1 8388608 18757497 8388608 1 8388608 (BSN.sqrt_enclosure 5 1 9378748 9378749 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz330 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS151to168.d24 : Enclosure.Real.IsNear qz330 Bool.false 3751499 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz330 Bool.false 3751499 8388608 1 8388608 3751499 8388608 1 8388608 (Ns150p59 rfl rfl) rfl 

theorem RS151to168.d25 : Enclosure.Real.IsNear qz330 Bool.false 30011992 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz330 Bool.false 3751499 8388608 1 8388608 30011992 67108864 8 67108864 RS151to168.d24 rfl 

noncomputable def Ns150p60 := BSN.log_dyadic_bound 2 10 5 4 94500000000 4194304 1960000 1291130880 26880 1700643 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 10) 0 4 1291130880 94500000000 26880 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz331 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) (@Nat.cast Real Real.instNatCast 1))

theorem RS151to168.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683142479095 2251799813685248 12500000049 24500000000000000 := BSN.isNear_log_sfrac 6 1 4034683142479095 2251799813685248 12500000049 24500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz331) Bool.false 270763002291722209198080 151115727451828646838272 1000000003920000 1960000000000000000000 4034683142479095 2251799813685248 12500000049 24500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 1700643 4194304 24973259072661432 36028797018963968 1960000 1000000000000000 rfl rfl rfl rfl (Ns150p60 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS151to168.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 120242927 67108864 35 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683142479095 2251799813685248 12500000049 24500000000000000 120242927 67108864 35 67108864 RS151to168.d26 rfl 

noncomputable abbrev qz332 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns150p61 := @Enclosure.Real.IsNear.inv_image qz332 20547809 8388608 1 8388608 1712317 1712318 4194304 (@Enclosure.Real.IsNear.of_eq qz332 (Real.sqrt qz331) Bool.false 20547809 8388608 1 8388608 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz331) Bool.false 20547809 8388608 1 8388608 20547809 8388608 1 8388608 (BSN.sqrt_enclosure 6 1 10273904 10273905 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz333 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS151to168.d28 : Enclosure.Real.IsNear qz333 Bool.false 3424635 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz333 Bool.false 3424635 8388608 1 8388608 3424635 8388608 1 8388608 (Ns150p61 rfl rfl) rfl 

theorem RS151to168.d29 : Enclosure.Real.IsNear qz333 Bool.false 27397080 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz333 Bool.false 3424635 8388608 1 8388608 27397080 67108864 8 67108864 RS151to168.d28 rfl 

noncomputable def Ns150p62 := BSN.log_dyadic_bound 3 11 6 5 269619528727395 4194304 1960000 6999933372849 55801305 2347198 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 3) (BSN.artanhQ 11) 0 5 6999933372849 269619528727395 55801305 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz838 := (Enclosure.sfrac Bool.false 7 1)

noncomputable abbrev qz629 := qz838

noncomputable abbrev qz334 := qz629

noncomputable abbrev qz335 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) (@Nat.cast Real Real.instNatCast 1))

theorem RS151to168.d30 : Enclosure.Real.IsNear (Real.log qz334) Bool.false 4381799714987255 2251799813685248 12500000049 24500000000000000 := BSN.isNear_log_sfrac 7 1 4381799714987255 2251799813685248 12500000049 24500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz335) Bool.false 294057601148318457528320 151115727451828646838272 1000000003920000 1960000000000000000000 4381799714987255 2251799813685248 12500000049 24500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 2347198 4194304 24973259072661432 36028797018963968 1960000 1000000000000000 rfl rfl rfl rfl (Ns150p62 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS151to168.d31 : Enclosure.Real.IsNear (Real.log qz334) Bool.false 130587807 67108864 35 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log qz334) Bool.false 4381799714987255 2251799813685248 12500000049 24500000000000000 130587807 67108864 35 67108864 RS151to168.d30 rfl 

noncomputable abbrev qz336 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns150p63 := @Enclosure.Real.IsNear.inv_image qz336 22194171 8388608 1 8388608 1585297 1585298 4194304 (@Enclosure.Real.IsNear.of_eq qz336 (Real.sqrt qz335) Bool.false 22194171 8388608 1 8388608 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz335) Bool.false 22194171 8388608 1 8388608 22194171 8388608 1 8388608 (BSN.sqrt_enclosure 7 1 11097085 11097086 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz337 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS151to168.d32 : Enclosure.Real.IsNear qz337 Bool.false 3170595 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz337 Bool.false 3170595 8388608 1 8388608 3170595 8388608 1 8388608 (Ns150p63 rfl rfl) rfl 

theorem RS151to168.d33 : Enclosure.Real.IsNear qz337 Bool.false 25364760 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz337 Bool.false 3170595 8388608 1 8388608 25364760 67108864 8 67108864 RS151to168.d32 rfl 

theorem RS151to168.d34 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz839 := (@instHMul Real Real.instMul)

noncomputable abbrev qz630 := qz839

noncomputable abbrev qz338 := (@HMul.hMul Real Real Real qz630 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz1 := qz338

theorem RS151to168.d35 : Enclosure.Real.IsNear qz1 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS151to168.d34 rfl 

noncomputable abbrev qz2 := (@Inv.inv Real Real.instInv qz338)

theorem RS151to168.d36 : Enclosure.Real.IsNear qz2 Bool.false 1335089 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz2 Bool.false 1335089 8388608 1 8388608 1335089 8388608 1 8388608 (@Enclosure.Real.IsNear.inv_image qz1 884279719003555 140737488355328 1 500000000000000 667544 667545 4194304 RS151to168.d35 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns150p64 := nat_lit 9038904596117680291840000 

noncomputable def Ns150p65 := nat_lit 27570044914317731653109153792 

noncomputable abbrev qz840 := (Enclosure.sfrac Bool.false 400547 1000)

noncomputable abbrev qz631 := qz840

noncomputable abbrev qz339 := qz631

noncomputable abbrev qz3 := qz339

noncomputable abbrev qz340 := qz630

noncomputable abbrev qz4 := qz340

noncomputable abbrev qz5 := (@Neg.neg Real Real.instNeg (1 : Real))

noncomputable abbrev qz6 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz841 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 400547 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz632 := qz841

noncomputable abbrev qz341 := qz632

noncomputable abbrev qz7 := qz341

noncomputable abbrev qz8 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz842 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 400547 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz633 := qz842

noncomputable abbrev qz342 := qz633

noncomputable abbrev qz9 := qz342

noncomputable abbrev qz343 := (@HMul.hMul Real Real Real qz4 (@HPow.hPow Real Nat Real RSCompact.c1 qz5 7) (@HPow.hPow Real Real Real qz6 qz7 qz8))

noncomputable def Ns150p66 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz3) qz3 7) (@HMul.hMul Real Real Real qz4 qz343 (Zeta.RiemannSiegel.correction qz9)) 103940957 33554432 5925 4194304 92622959809585145325 295147905179352825856 246375831933892772851 Ns150p64 Ns150p65 

noncomputable def Ns150p67 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz3) qz3 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 400547 1000 54 94 67108864 33554432 1125899906842624 Bool.false 42376633141 1239 

noncomputable def Ns150p68 := Ns150p67 120242927 35 27397080 8 130587807 35 25364760 8 Bool.true 75141173 35384 Bool.true 93935258 Bool.true 20971625 3537118876014220 1 Bool.false 11423203 Bool.true Bool.false 63858611 Bool.true Bool.true 103940957 

noncomputable def Ns150p69 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz3) qz3 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 400547 1000 48 8 67108864 33554432 1125899906842624 Bool.false 42376633141 1239 

noncomputable def Ns150p70 := Ns150p69 93032624 35 33554424 8 108007536 35 30011992 8 Bool.true 123118188 20911 Bool.false 52805556 Bool.true 42146524 3537118876014220 1 Bool.false 47383518 Bool.false Bool.false 54303505 Bool.false Bool.true 75141173 

noncomputable def Ns150p71 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz3) qz3 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 400547 1000 225 121 67108864 33554432 1125899906842624 Bool.false 42376633141 1239 

noncomputable def Ns150p72 := Ns150p71 46516304 35 47453136 16 73726608 35 38745320 8 Bool.true 67108824 1283 Bool.false 26436782 Bool.false 90524281 3537118876014220 1 Bool.false 25758290 Bool.true Bool.false 65463729 Bool.true Bool.true 123118188 

noncomputable def Ns150p73 := nat_lit 84559374648993600864471075002216969393296265836853069311 

noncomputable def Ns150p74 := nat_lit 133910675591195374384614387756698956863901757394124800 

noncomputable def Ns150p75 := nat_lit 4948919258707503906673254803360000 

noncomputable def Ns150p76 := nat_lit 11893657222756404080198534579144627520 

noncomputable abbrev qz10 := (@Eq.refl Real qz339)

noncomputable def Ns150p77 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz3 400547 1000 641752596836 16000000 801094 4000 2000 Ns150p75 Ns150p76 qz10 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns150p78 := nat_lit 27058999887677952276630744000709430205854805067792982179520 

noncomputable abbrev qz843 := (@instHSub Real Real.instSub)

noncomputable abbrev qz634 := qz843

noncomputable abbrev qz344 := qz634

noncomputable abbrev qz11 := qz344

noncomputable abbrev qz345 := (Real.log (Enclosure.sfrac Bool.false 641752596836 16000000))

noncomputable abbrev qz346 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz347 := (@HMul.hMul Real Real Real qz630 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz348 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz349 := (Enclosure.sfrac Bool.false 400547 2000)

noncomputable abbrev qz12 := (@HSub.hSub Real Real Real qz344 (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 400547 4000) qz345) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 801094)))))) qz349)

noncomputable abbrev qz350 := (@HSub.hSub Real Real Real qz11 qz12 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 400547 2000) (Real.log Real.pi)))

noncomputable def Ns150p79 := @Enclosure.Real.IsNear.addLit_ft_p qz350 (Enclosure.sfrac Bool.true Ns150p75 Ns150p76) 2275079667359680046351 3602879701896396800 185160033853935979 10035200000000000000000 Ns150p75 Ns150p76 0 1 Ns150p78 

noncomputable def Ns150p80 := nat_lit 763390059930030036570414776320000 

noncomputable abbrev qz351 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 400547 2000) (Real.log Real.pi))

noncomputable def Ns150p81 := @Enclosure.Real.IsNear.subLit_ff_p qz12 qz351 15505362407684161714507 18014398509481984000 255341933885309 39200000000000000000 15385315086267 67108864000 400547 33554432000 Ns150p80 2275079667359680046351 3602879701896396800 

noncomputable def Ns150p82 := nat_lit 31010724815368323429014000 

noncomputable abbrev qz13 := (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 400547 4000) qz345) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 801094))))))

noncomputable def Ns150p83 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz349 19113169047572901837131 18014398509481984000 255341933885309 39200000000000000000 400547 2000 0 1 Ns150p82 15505362407684161714507 18014398509481984000 255341933885309 39200000000000000000 

noncomputable def Ns150p84 := nat_lit 43039030500259309324230178094593343488 

noncomputable def Ns150p85 := nat_lit 12813851348883193764773888 

noncomputable def Ns150p86 := nat_lit 1208925819614629174706176 

noncomputable def Ns150p87 := nat_lit 263919406252342617088420796081971845295087525752119100180092749060527329280 

noncomputable def Ns150p88 := nat_lit 898239433476086989261264131252457707503378630968323420746931972231622656 

noncomputable def Ns150p89 := nat_lit 39403356109971135006417249475879033096361212118441307733450521047040 

noncomputable def Ns150p90 := BSN.log_dyadic_bound 117464596836 1166040596836 4 3 Ns150p87 33554432 15680000 Ns150p88 Ns150p89 6783421 1283505193672 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 117464596836) (BSN.artanhQ 1166040596836) 0 3 Ns150p88 Ns150p87 Ns150p89 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz352 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns150p91 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 400547 4000) qz345 400547 4000 0 1 47735316115927673 4503599627370496 625000147 9800000000000000 19120237664286481637131 18014398509481984000 35763133411487 5600000000000000000 (Enclosure.Real.IsNear.const Bool.false 400547 4000) (BSN.isNear_log_sfrac 641752596836 16000000 47735316115927673 4503599627370496 625000147 9800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 641752596836) qz352)) Bool.false Ns150p85 Ns150p86 1000000235200000 15680000000000000000000 47735316115927673 4503599627370496 625000147 9800000000000000 (BSN.log_rat_reduce_isNear 641752596836 16000000 15 1283505193672 1048576000000 6783421 33554432 24973259072661432 36028797018963968 15680000 1000000000000000 rfl rfl rfl rfl (Ns150p90 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns150p92 := BSN.arctan_dyadic_bound_f 1000 801094 1 0 4194304 1960000 0 1 1 0 1 1 5235 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 801094) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 801094) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz14 := qz347

noncomputable abbrev qz15 := qz348

noncomputable abbrev qz353 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz16 := (@Enclosure.Real.IsNear.mulLit_ff qz353 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz354 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 801094)))

noncomputable def Ns150p93 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz354 884279719003555 562949953421312 1 2000000000000000 5235 4194304 1 1960000 3705990919529326182400 883577089197475 562949953421312 50000000049 98000000000000000 qz16 (Ns150p92 rfl) rfl rfl 

noncomputable abbrev qz17 := qz346

noncomputable abbrev qz355 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns150p94 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 400547 4000) qz345) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz354)) 19120237664286481637131 18014398509481984000 35763133411487 5600000000000000000 883577089197475 2251799813685248 50000000049 392000000000000000 Ns150p84 19113169047572901837131 18014398509481984000 255341933885309 39200000000000000000 (Ns150p91 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz354) 1 4 0 1 883577089197475 562949953421312 50000000049 98000000000000000 883577089197475 2251799813685248 50000000049 392000000000000000 qz355 Ns150p93 rfl) 

noncomputable def Ns150p95 := @Ns150p79 Ns150p73 Ns150p74 185160033853935979 10035200000000000000000 (@Ns150p81 185160033853935979 10035200000000000000000 (Ns150p83 (Ns150p94 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 400547 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz349 (Real.log Real.pi) 400547 2000 0 1 38410761 33554432 1 16777216 15385315086267 67108864000 400547 33554432000 (Enclosure.Real.IsNear.const Bool.false 400547 2000) RS151to168.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns150p75 Ns150p76) 

noncomputable abbrev qz356 := (@instHAdd Real Real.instAdd)

noncomputable def Ns150p96 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz3) Bool.false Ns150p73 Ns150p74 185160033853935979 10035200000000000000000 2648539571 4194304 39 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz3) (@HAdd.hAdd Real Real Real qz356 qz350 (Enclosure.sfrac Bool.true Ns150p75 Ns150p76)) Bool.false Ns150p73 Ns150p74 185160033853935979 10035200000000000000000 Ns150p77 (Ns150p95 rfl rfl)) 

noncomputable def Ns150p97 := nat_lit 140317030308219863766845826572621989729227543699939997318091475628794944409878366198305 

noncomputable def Ns150p98 := nat_lit 2753733154729970958028337252922338050165611694356407771374444090804896824278383046164480 

noncomputable def Ns150p99 := nat_lit 282583866837046011966505874486260119151912153455840649045446789357991173868430760481 

noncomputable def Ns150p100 := nat_lit 367039467403792044893793298179127456716969042394247679544165998511692868696751595002401 

noncomputable def Ns150p101 := nat_lit 50485107836716134230519516303576197586369547729867475808531474998089775111770355846348800 

noncomputable abbrev qz357 := (BSN.sinEvenQ 17179869184)

noncomputable abbrev qz358 := (BSN.sinOddQ 17179869184)

noncomputable def Ns150p102 := BSN.sin_dyadic_bound_f 27001843789 17179869184 3 2 8388608 3923829 Ns150p97 Ns150p98 Ns150p99 Ns150p100 Ns150p101 Ns150p99 8388603 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 27001843789) qz357 0 2 Ns150p97 Ns150p98 Ns150p99 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 27001843789) qz358 0 2 Ns150p100 Ns150p101 Ns150p99 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz359 := (@Nat.cast Real Real.instNatCast 4194304)

noncomputable abbrev qz360 := (@Nat.cast Real Real.instNatCast 604462909807314587353088)

noncomputable def Ns150p103 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz3) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2648539571) qz359) Bool.false 2648539571 4194304 39 2097152 Bool.true 8388603 8388608 1 1960000 (Ns150p96 rfl) (Enclosure.sfrac_false_div 2648539571 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2648539571) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 950042918968698802798592) qz360) 226375608064910080 72057594037927936 Bool.false 8388603 8388608 100 1000000000000000 3920000 1960000 (BSN.sin_reduce_arg_pos_rat_q1 2648539571 4194304 226375608064910080 72057594037927936 100 950042918968698802798592 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388603 8388608 950042918968698802798592 604462909807314587353088 27001843789 17179869184 3923829 3920000 (Ns150p102 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns150p104 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz3) Bool.false Ns150p73 Ns150p74 185160033853935979 10035200000000000000000 42376633141 67108864 1239 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz3) (@HAdd.hAdd Real Real Real qz356 qz350 (Enclosure.sfrac Bool.true Ns150p75 Ns150p76)) Bool.false Ns150p73 Ns150p74 185160033853935979 10035200000000000000000 Ns150p77 (Ns150p95 rfl rfl)) 

noncomputable def Ns150p105 := Ns150p72 20911 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 225 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 25758290 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 121 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 65463729 67108864) qz10 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz3) qz3 1) Bool.true 8388603 8388608 1227143 64225280000 67108824 67108864 1283 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz3) qz3 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz3)) Bool.true 8388603 8388608 1227143 64225280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz3) qz3) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz3)) Bool.true 8388603 8388608 78537152 4110417920000 8388603 8388608 1227143 64225280000 (Ns150p103 rfl rfl) rfl)) rfl) (Ns150p104 rfl) RS151to168.d7 

noncomputable def Ns150p106 := nat_lit 488466021960050360332980994576 

noncomputable def Ns150p107 := nat_lit 2433889152438200450873670154321920 

noncomputable def Ns150p108 := nat_lit 17037224067067403156115691080253440 

noncomputable abbrev qz361 := (BSN.sinEvenQ 67108864)

noncomputable def Ns150p109 := BSN.sin_dyadic_bound_f 26436782 67108864 2 1 67108864 33554432 Ns150p106 Ns150p107 Ns150p106 Ns150p106 Ns150p108 Ns150p106 25758290 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 26436782) qz361 0 1 Ns150p106 Ns150p107 Ns150p106 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 26436782) (BSN.sinOddQ 67108864) 0 1 Ns150p106 Ns150p108 Ns150p106 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p110 := nat_lit 1435072454174335547046732789819713753994431881920619561788097375624736590823106047689544262331621078561 

noncomputable def Ns150p111 := nat_lit 51956389457850993117201226487380036501230565613159928972022824181150019275806034930923536691271355596800 

noncomputable def Ns150p112 := nat_lit 302817527272552478968363742587333220402014122079541423581921982371098657032556912750658228745761 

noncomputable def Ns150p113 := nat_lit 7170509920397033807510887503411729674198709410745216296748902707394464871932278230479656491914279679521 

noncomputable def Ns150p114 := nat_lit 1818473631024784759102042927058301277543069796460597514020798846340250674653211222582323784194497445888000 

noncomputable def Ns150p115 := BSN.sin_dyadic_bound_f 90524281 67108864 4 3 67108864 33554432 Ns150p110 Ns150p111 Ns150p112 Ns150p113 Ns150p114 Ns150p112 65463729 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 90524281) qz361 0 3 Ns150p110 Ns150p111 Ns150p112 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 90524281) (BSN.sinOddQ 67108864) 0 3 Ns150p113 Ns150p114 Ns150p112 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p116 := nat_lit 265000320116438581214743499677388563639195739008214160726252650496 

noncomputable def Ns150p117 := nat_lit 16586685937797756904922089360178093090225977525586485022553978961920 

noncomputable def Ns150p118 := nat_lit 60455658783947765429078194680997037478682463242995900329558016 

noncomputable def Ns150p119 := nat_lit 794880049031747848113372342642803696842629852098156490378098835456 

noncomputable def Ns150p120 := nat_lit 746400867200899060721494021208014189060168988651391826014929053286400 

noncomputable abbrev qz362 := (BSN.cosEvenQ 67108864)

noncomputable def Ns150p121 := BSN.cos_dyadic_bound_f 52805556 67108864 3 2 67108864 33554432 Ns150p116 Ns150p117 Ns150p118 Ns150p119 Ns150p120 Ns150p118 47383518 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 52805556) qz362 0 2 Ns150p116 Ns150p117 Ns150p118 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 52805556) (BSN.cosOddQ 67108864) 0 2 Ns150p119 Ns150p120 Ns150p118 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p122 := nat_lit 107526644835851167997446283811598976075498364683326246453531181056 

noncomputable def Ns150p123 := nat_lit 9956211158214559905947317111087639107267190275884503416242176 

noncomputable def Ns150p124 := nat_lit 322560022085237074872526956800574752948280559669426970353761058816 

noncomputable def Ns150p125 := BSN.cos_dyadic_bound_f 42146524 67108864 3 2 67108864 33554432 Ns150p122 Ns150p117 Ns150p123 Ns150p124 Ns150p120 Ns150p123 54303505 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 42146524) qz362 0 2 Ns150p122 Ns150p117 Ns150p123 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 42146524) (BSN.cosOddQ 67108864) 0 2 Ns150p124 Ns150p120 Ns150p123 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p126 := Ns150p70 35384 BSN.abs_quadSignPos (BSN.cos_quad_nat0 48 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 47383518 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 8 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 54303505 67108864) qz10 rfl rfl (Ns150p105 RS151to168.d9 RS151to168.d11 RS151to168.d13 RS151to168.d17 (Ns150p109 rfl rfl) (Ns150p115 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns150p104 rfl) RS151to168.d19 RS151to168.d21 RS151to168.d23 RS151to168.d25 RS151to168.d17 (Ns150p121 rfl rfl) (Ns150p125 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns150p127 := nat_lit 640723864688617068107598873825222120120296295881501393052085768410773830371712371224109316492623548416 

noncomputable def Ns150p128 := nat_lit 3996645342911614855169325114413848961633120431781532997847909552396155328908156533147964360867027353600 

noncomputable def Ns150p129 := nat_lit 472001729923929359916989499371262563590044960362995189966363631835757678183984515549312261492736 

noncomputable def Ns150p130 := nat_lit 3881147946275247797340382036731152289935211226292362227472082301494346765773404666880291372842665840640 

noncomputable def Ns150p131 := nat_lit 363694726204956951820408585411660255508613959292119502804159769268050134930642244516464756838899489177600 

noncomputable def Ns150p132 := BSN.cos_dyadic_bound_f 93935258 67108864 4 3 67108864 33554432 Ns150p127 Ns150p128 Ns150p129 Ns150p130 Ns150p131 Ns150p129 11423203 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 93935258) qz362 0 3 Ns150p127 Ns150p128 Ns150p129 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 93935258) (BSN.cosOddQ 67108864) 0 3 Ns150p130 Ns150p131 Ns150p129 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p133 := nat_lit 193432004983689321738525390625 

noncomputable def Ns150p134 := nat_lit 486777830487640090174734030864384 

noncomputable def Ns150p135 := nat_lit 7301667457314601352621010462965760 

noncomputable def Ns150p136 := BSN.cos_dyadic_bound_f 20971625 67108864 2 1 67108864 33554432 Ns150p133 Ns150p134 Ns150p133 Ns150p133 Ns150p135 Ns150p133 63858611 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 20971625) qz362 0 1 Ns150p133 Ns150p134 Ns150p133 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 20971625) (BSN.cosOddQ 67108864) 0 1 Ns150p133 Ns150p135 Ns150p133 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p137 := Ns150p68 47400 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 54 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 11423203 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 94 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 63858611 67108864) qz10 rfl rfl (Ns150p126 rfl rfl) (Ns150p104 rfl) RS151to168.d27 RS151to168.d29 RS151to168.d31 RS151to168.d33 RS151to168.d17 (Ns150p132 rfl rfl) (Ns150p136 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns150p138 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz3) qz3 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz3) qz3 7) 103940957 67108864 47400 67108864 103940957 67108864 47400 67108864 13950719094685696 103940957 33554432 5925 4194304 (Ns150p137 rfl) 

noncomputable def Ns150p139 := @Enclosure.Real.IsNear.mulLit_tf qz343 (Zeta.RiemannSiegel.correction qz9) 2968735 8388608 1 8388608 31199470417395 35184372088832 82668296592341 1077521395220480000 92622959809585145325 295147905179352825856 

noncomputable abbrev qz363 := (@HPow.hPow Real Nat Real RSCompact.c1 qz5 7)

noncomputable def Ns150p140 := @Enclosure.Real.IsNear.mulLit_tf qz363 (@HPow.hPow Real Real Real qz6 qz7 qz8) 1 1 0 1 2968735 8388608 1 8388608 2968735 8388608 1 8388608 

noncomputable abbrev qz364 := (@Enclosure.Real.IsNear.of_eq qz7 (@HMul.hMul Real Real Real qz4 qz3 qz2) Bool.false 534765893683 8388608000 400547 8388608000 (BSN.t_div_two_pi_mk qz3 400547 1000 qz10) (@Enclosure.Real.IsNear.mulLit_ff qz3 qz2 400547 1000 0 1 1335089 8388608 1 8388608 534765893683 8388608000 400547 8388608000 (Enclosure.Real.IsNear.const Bool.false 400547 1000) RS151to168.d36 rfl))

noncomputable def Ns150p141 := @Enclosure.Real.IsNear.sqrt_image qz7 534765893683 8388608000 400547 8388608000 33488573 33488599 4194304 qz364 

noncomputable abbrev qz844 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 400547 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz635 := qz844

noncomputable abbrev qz365 := qz635

noncomputable abbrev qz18 := qz365

noncomputable def Ns150p142 := @Enclosure.Real.IsNear.sqrt_image qz18 16744293 2097152 13 4194304 11851635 11851640 4194304 (@Enclosure.Real.IsNear.recentre' qz18 Bool.false 66977172 8388608 26 8388608 16744293 2097152 13 4194304 (Ns150p141 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz636 := (Real.sqrt qz844)

noncomputable abbrev qz366 := qz636

noncomputable abbrev qz19 := qz366

noncomputable def Ns150p143 := @Enclosure.Real.IsNear.inv_image qz19 23703275 8388608 5 8388608 1484367 1484368 4194304 (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 23703275 8388608 5 8388608 23703275 8388608 5 8388608 (Ns150p142 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns150p144 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz19) Bool.false 2968735 8388608 1 8388608 2968735 8388608 1 8388608 (Ns150p143 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz20 := (@HMul.hMul Real Real Real qz340 qz338 qz342)

noncomputable abbrev qz637 := (@HMul.hMul Real Real Real qz839 qz842 qz842)

noncomputable abbrev qz638 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz367 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz637 qz633) qz638)

noncomputable abbrev qz21 := (Real.cos (@HMul.hMul Real Real Real qz340 qz338 qz367))

noncomputable def Ns150p145 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz9) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz20)) qz21) Bool.false 31199470417395 

noncomputable def Ns150p146 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz20)) qz21 8429585 8388608 171 

noncomputable def Ns150p147 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz20)) Bool.false 8429585 8388608 171 8388608 8429585 8388608 171 

noncomputable def Ns150p148 := @Enclosure.Real.IsNear.recentre' (Real.cos qz20) Bool.false 8347831 8388608 82457152 4110417920000 8347831 8388608 1288393 64225280000 

noncomputable abbrev qz368 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable def Ns150p149 := @Enclosure.Real.IsNear.cos_image qz20 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51879733) qz368) Bool.false 51879733 8388608 41 2097152 Bool.false 8347831 8388608 1 

noncomputable def Ns150p150 := nat_lit 350818980353035775103015707 

noncomputable def Ns150p151 := nat_lit 18014398509481984000000000000000 

noncomputable def Ns150p152 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz9 884279719003555 140737488355328 1 500000000000000 2064229 2097152 13 4194304 1825355840078989334095 295147905179352825856 Ns150p150 

noncomputable def Ns150p153 := @Enclosure.Real.IsNear.subLit_ff_p qz18 qz334 16744293 2097152 13 4194304 7 1 0 1 2064229 2064229 2097152 13 

noncomputable def Ns150p154 := @Ns150p153 4194304 (@Enclosure.Real.IsNear.recentre' qz18 Bool.false 66977172 8388608 26 8388608 16744293 2097152 13 4194304 (Ns150p141 rfl rfl rfl rfl rfl rfl) rfl) (Enclosure.Real.IsNear.const Bool.false 7 1) 

noncomputable def Ns150p155 := @Enclosure.Real.IsNear.recentre' qz20 Bool.false 1825355840078989334095 295147905179352825856 Ns150p150 Ns150p151 51879733 8388608 41 2097152 (@Ns150p152 Ns150p151 RS151to168.d35 (Ns150p154 rfl rfl) rfl) 

noncomputable def Ns150p156 := nat_lit 1779728768165678736736256 

noncomputable def Ns150p157 := nat_lit 107952153851092613053685657350940076443719534951163147911697952179971921576483224616960 

noncomputable def Ns150p158 := nat_lit 167414149248648496929153859043086791839327043607523661956889451881267485926678921216 

noncomputable def Ns150p159 := nat_lit 282460780035030460431291424909249488261049395372919872887469196596880599627860489076736 

noncomputable def Ns150p160 := BSN.sin_dyadic_bound_f 25291466956 17179869184 3 2 8388608 3923829 Ns150p157 Ns150p98 Ns150p158 Ns150p159 Ns150p101 Ns150p158 8347831 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 25291466956) qz357 0 2 Ns150p157 Ns150p98 Ns150p158 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 25291466956) qz358 0 2 Ns150p159 Ns150p101 Ns150p158 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz369 := (@Nat.cast Real Real.instNatCast Ns150p86)

noncomputable def Ns150p161 := @Ns150p149 1960000 (Ns150p155 rfl) (Enclosure.sfrac_false_div 51879733 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51879733) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns150p156) qz369) 226375608064910080 72057594037927936 Bool.false 8347831 8388608 0 1000000000000000 3920000 1960000 (BSN.sin_reduce_arg_pos_rat_q3 51879733 8388608 226375608064910080 72057594037927936 0 Ns150p156 Ns150p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8347831 8388608 Ns150p156 Ns150p86 25291466956 17179869184 3923829 3920000 (Ns150p160 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns150p162 := @Enclosure.Real.IsNear.inv_image (Real.cos qz20) 8347831 8388608 1288393 64225280000 4214707 4214878 4194304 (Ns150p148 (Ns150p161 rfl rfl) rfl) rfl 

noncomputable def Ns150p163 := @Enclosure.Real.IsNear.recentre' qz21 Bool.false 3701187 4194304 

noncomputable abbrev qz22 := (@HMul.hMul Real Real Real qz340 qz338 qz367)

noncomputable def Ns150p164 := @Enclosure.Real.IsNear.cos_image qz22 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 4108653)) qz368) Bool.true 4108653 8388608 

noncomputable def Ns150p165 := nat_lit 303165148635646225541595605 

noncomputable def Ns150p166 := nat_lit 618970019642690137449562112 

noncomputable def Ns150p167 := nat_lit 4368128864768290165715336949578491 

noncomputable def Ns150p168 := @Enclosure.Real.IsNear.recentre' qz22 Bool.true Ns150p165 Ns150p166 Ns150p167 

noncomputable def Ns150p169 := nat_lit 75557863725914323419136000000000000000 

noncomputable abbrev qz23 := qz367

noncomputable def Ns150p170 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz23 884279719003555 140737488355328 1 500000000000000 342838518311 

noncomputable abbrev qz370 := (@HSub.hSub Real Real Real qz634 qz637 qz633)

noncomputable abbrev qz24 := qz370

noncomputable abbrev qz371 := qz638

noncomputable abbrev qz25 := qz371

noncomputable def Ns150p171 := @Enclosure.Real.IsNear.subLit_tf qz24 qz25 67960611367 4398046511104 161866029 17592186044416 1 16 

noncomputable abbrev qz372 := qz637

noncomputable abbrev qz26 := qz372

noncomputable def Ns150p172 := @Enclosure.Real.IsNear.subLit_ff_n qz26 qz9 4261041364441 4398046511104 107340077 17592186044416 2064229 2097152 13 4194304 

noncomputable def Ns150p173 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz9 2064229 2097152 13 4194304 2064229 2097152 13 4194304 4261041364441 4398046511104 

noncomputable def Ns150p174 := nat_lit 284969156115865398785899281 

noncomputable def Ns150p175 := nat_lit 118842243771396506390315925504 

noncomputable def Ns150p176 := nat_lit 1782633656570947595854738882560 

noncomputable def Ns150p177 := BSN.cos_dyadic_bound_f 4108653 8388608 2 1 4194304 1960000 Ns150p174 Ns150p175 Ns150p174 Ns150p174 Ns150p176 Ns150p174 3701187 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 4108653) (BSN.cosEvenQ 8388608) 0 1 Ns150p174 Ns150p175 Ns150p174 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 4108653) (BSN.cosOddQ 8388608) 0 1 Ns150p174 Ns150p176 Ns150p174 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz373 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns150p178 := @Ns150p163 480474304 8220835840000 3701187 4194304 7507411 128450560000 (@Ns150p164 243 4194304 Bool.false 3701187 4194304 1 1960000 (@Ns150p168 Ns150p169 4108653 8388608 243 4194304 (@Ns150p170 4398046511104 161866029 17592186044416 Ns150p165 Ns150p166 Ns150p167 Ns150p169 RS151to168.d35 (@Ns150p171 0 1 5485416292976 342838518311 4398046511104 161866029 17592186044416 (@Ns150p172 142523732049526784 67960611367 4398046511104 161866029 17592186044416 (@Ns150p173 107340077 17592186044416 (Ns150p154 rfl rfl) (Ns150p154 rfl rfl) rfl) (Ns150p154 rfl rfl) rfl rfl) qz373 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 4108653 8388608) (BSN.cos_neg_of_bound 4108653 8388608 Bool.false 3701187 4194304 1 1960000 (Ns150p177 rfl rfl)) rfl rfl) 

noncomputable def Ns150p179 := @Ns150p139 246375831933892772851 Ns150p64 (Ns150p140 (@Enclosure.Real.IsNear.of_eq qz363 (Enclosure.sfrac Bool.true 1 1) Bool.true 1 1 0 1 (BSN.neg_one_pow_odd_mk 7 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Real Real qz6 qz7 qz8) (@Inv.inv Real Real.instInv qz19) Bool.false 2968735 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz7 (BSN.t_div_two_pi_nonneg qz3 400547 1000 qz10)) Ns150p144) rfl) (@Ns150p145 35184372088832 82668296592341 1077521395220480000 (BSN.correction_mk qz9 (BSN.cos_two_pi_p_ne_zero_mk qz3 400547 1000 7 qz10 rfl rfl (@BSN.floor_sqrt_eq_dec qz3 400547 1000 7 qz10 rfl rfl rfl))) (@Ns150p146 8388608 3701187 4194304 7507411 128450560000 31199470417395 35184372088832 82668296592341 1077521395220480000 (@Ns150p147 8388608 (Ns150p162 rfl rfl rfl rfl rfl) rfl) (Ns150p178 rfl) rfl)) 

noncomputable def Ns150p180 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz3) (hardyZApproximantRS₀ qz3) Bool.true 821651366779736627731 295147905179352825856 13015004365296580772851 Ns150p64 (@Eq.refl Real (hardyZApproximantRS₀ qz3)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz3) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz3) qz3 7) (@HMul.hMul Real Real Real qz4 qz343 (Zeta.RiemannSiegel.correction qz9))) Bool.true 821651366779736627731 295147905179352825856 13015004365296580772851 Ns150p64 (BSN.hardyZApproximantRS₀_eq qz3 7 (@BSN.floor_sqrt_eq_dec qz3 400547 1000 7 qz10 rfl rfl rfl)) (@Ns150p66 821651366779736627731 295147905179352825856 13015004365296580772851 Ns150p64 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz3) qz3 7) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz3) qz3 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz3) qz3 7)) Bool.true 103940957 33554432 5925 4194304 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz3) qz3 7) (Ns150p138 (Ns150p137 rfl) rfl rfl)) (Ns150p179 rfl) rfl rfl)) 

theorem RS151to168.d37 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz3) Bool.true 821651366779736627731 295147905179352825856 13015004365296580772851 Ns150p64 := Ns150p180 

theorem RS151to168.d38 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS151to168.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS151to168.d3 a b h)) 

noncomputable def Ns150p181 := nat_lit 40862158656278473765552128 

noncomputable abbrev qz845 := (Enclosure.sfrac Bool.false 402058 1000)

noncomputable abbrev qz639 := qz845

noncomputable abbrev qz374 := qz639

noncomputable abbrev qz27 := qz374

noncomputable abbrev qz846 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 402058 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz640 := qz846

noncomputable abbrev qz375 := qz640

noncomputable abbrev qz28 := qz375

noncomputable abbrev qz847 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 402058 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz641 := qz847

noncomputable abbrev qz376 := qz641

noncomputable abbrev qz29 := qz376

noncomputable abbrev qz377 := (@HMul.hMul Real Real Real qz4 (@HPow.hPow Real Nat Real RSCompact.c1 qz5 7) (@HPow.hPow Real Real Real qz6 qz28 qz8))

noncomputable def Ns150p182 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz27) qz27 7) (@HMul.hMul Real Real Real qz4 qz377 (Zeta.RiemannSiegel.correction qz29)) 3389537 16777216 47575 33554432 1503865615393886605 4611686018427387904 1252086341971743517 45194522980588401459200 Ns150p181 

noncomputable def Ns150p183 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz27) qz27 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 402058 1000 54 94 67108864 33554432 1125899906842624 Bool.false 42587387944 1244 

noncomputable def Ns150p184 := Ns150p183 120242927 35 27397080 8 130587807 35 25364760 8 Bool.false 47548392 35513 Bool.true 64867518 Bool.true 7534998 3537118876014220 1 Bool.false 38124529 Bool.true Bool.false 66686292 Bool.true Bool.false 6779074 

noncomputable def Ns150p185 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz27) qz27 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 402058 1000 49 7 67108864 33554432 1125899906842624 Bool.false 42587387944 1244 

noncomputable def Ns150p186 := Ns150p185 93032624 35 33554424 8 108007536 35 30011992 8 Bool.false 26320598 20985 Bool.false 17573707 Bool.true 100005465 3537118876014220 1 Bool.false 17373541 Bool.true Bool.false 66891006 Bool.false Bool.false 47548392 

noncomputable def Ns150p187 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz27) qz27 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 402058 1000 226 122 67108864 33554432 1125899906842624 Bool.false 42587387944 1244 

noncomputable def Ns150p188 := Ns150p187 46516304 35 47453136 16 73726608 35 38745320 8 Bool.false 67108856 1283 Bool.false 61491093 Bool.false 84463822 3537118876014220 1 Bool.false 40853776 Bool.true Bool.false 20611879 Bool.true Bool.false 26320598 

noncomputable def Ns150p189 := nat_lit 3395374518260872124716471875741356776252573815073843673 

noncomputable def Ns150p190 := nat_lit 5350403905305525598163219810635562836675566501888000 

noncomputable def Ns150p191 := nat_lit 5042971093082287600830840048640000 

noncomputable def Ns150p192 := nat_lit 12165410010551398950527117928312606720 

noncomputable abbrev qz378 := (@Eq.refl Real qz639)

noncomputable abbrev qz30 := qz378

noncomputable def Ns150p193 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz27 402058 1000 646603541456 16000000 804116 4000 2000 Ns150p191 Ns150p192 qz30 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns150p194 := nat_lit 69537270133982661114193344015182986777652711732712318423040 

noncomputable abbrev qz379 := (Real.log (Enclosure.sfrac Bool.false 646603541456 16000000))

noncomputable abbrev qz380 := (Enclosure.sfrac Bool.false 402058 2000)

noncomputable abbrev qz31 := (@HSub.hSub Real Real Real qz344 (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 402058 4000) qz379) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 804116)))))) qz380)

noncomputable abbrev qz381 := (@HSub.hSub Real Real Real qz11 qz31 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 402058 2000) (Real.log Real.pi)))

noncomputable def Ns150p195 := @Enclosure.Real.IsNear.addLit_ft_p qz381 (Enclosure.sfrac Bool.true Ns150p191 Ns150p192) 5715986185152533434557 9007199254740992000 92926846052078653 5017600000000000000000 Ns150p191 Ns150p192 0 1 Ns150p194 

noncomputable def Ns150p196 := nat_lit 191796669762640092757569306624000 

noncomputable abbrev qz382 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 402058 2000) (Real.log Real.pi))

noncomputable def Ns150p197 := @Enclosure.Real.IsNear.subLit_ff_p qz31 qz382 7788758037659464569021 9007199254740992000 128143154553713 19600000000000000000 7721676873069 33554432000 201029 16777216000 Ns150p196 5715986185152533434557 9007199254740992000 

noncomputable def Ns150p198 := nat_lit 15577516075318929138042000 

noncomputable abbrev qz32 := (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 402058 4000) qz379) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 804116))))))

noncomputable def Ns150p199 := @Enclosure.Real.IsNear.subLit_ff_p qz32 qz380 9599466296640791449789 9007199254740992000 128143154553713 19600000000000000000 402058 2000 0 1 Ns150p198 7788758037659464569021 9007199254740992000 128143154553713 19600000000000000000 

noncomputable def Ns150p200 := nat_lit 21616076418253551795647378148842012672 

noncomputable def Ns150p201 := nat_lit 12822955141342742599172096 

noncomputable def Ns150p202 := nat_lit 270576024195329216552150506207139921947879603496144206871039499177956474880 

noncomputable def Ns150p203 := nat_lit 990727766958821105844061299240345474397002588421343897638252428474187776 

noncomputable def Ns150p204 := nat_lit 50232074247062837218844091614143623205334422181551318094671868067840 

noncomputable def Ns150p205 := BSN.log_dyadic_bound 122315541456 1170891541456 4 3 Ns150p202 33554432 15680000 Ns150p203 Ns150p204 7036102 1293207082912 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 122315541456) (BSN.artanhQ 1170891541456) 0 3 Ns150p203 Ns150p202 Ns150p204 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns150p206 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 402058 4000) qz379 402058 4000 0 1 47769230385656441 4503599627370496 625000147 9800000000000000 9603000615198128677789 9007199254740992000 125643154551263 19600000000000000000 (Enclosure.Real.IsNear.const Bool.false 402058 4000) (BSN.isNear_log_sfrac 646603541456 16000000 47769230385656441 4503599627370496 625000147 9800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 646603541456) qz352)) Bool.false Ns150p201 Ns150p86 1000000235200000 15680000000000000000000 47769230385656441 4503599627370496 625000147 9800000000000000 (BSN.log_rat_reduce_isNear 646603541456 16000000 15 1293207082912 1048576000000 7036102 33554432 24973259072661432 36028797018963968 15680000 1000000000000000 rfl rfl rfl rfl (Ns150p205 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns150p207 := BSN.arctan_dyadic_bound_f 1000 804116 1 0 4194304 1960000 0 1 1 0 1 1 5216 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 804116) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 804116) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz383 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 804116)))

noncomputable def Ns150p208 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz383 884279719003555 562949953421312 1 2000000000000000 5216 4194304 1 1960000 3706001615578441187328 883579639334307 562949953421312 50000000049 98000000000000000 qz16 (Ns150p207 rfl) rfl rfl 

noncomputable def Ns150p209 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 402058 4000) qz379) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz383)) 9603000615198128677789 9007199254740992000 125643154551263 19600000000000000000 883579639334307 2251799813685248 50000000049 392000000000000000 Ns150p200 9599466296640791449789 9007199254740992000 128143154553713 19600000000000000000 (Ns150p206 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz383) 1 4 0 1 883579639334307 562949953421312 50000000049 98000000000000000 883579639334307 2251799813685248 50000000049 392000000000000000 qz355 Ns150p208 rfl) 

noncomputable def Ns150p210 := @Ns150p195 Ns150p189 Ns150p190 92926846052078653 5017600000000000000000 (@Ns150p197 92926846052078653 5017600000000000000000 (Ns150p199 (Ns150p209 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 402058 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz380 (Real.log Real.pi) 402058 2000 0 1 38410761 33554432 1 16777216 7721676873069 33554432000 201029 16777216000 (Enclosure.Real.IsNear.const Bool.false 402058 2000) RS151to168.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns150p191 Ns150p192) 

noncomputable def Ns150p211 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz27) Bool.false Ns150p189 Ns150p190 92926846052078653 5017600000000000000000 5323423493 8388608 39 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz27) (@HAdd.hAdd Real Real Real qz356 qz381 (Enclosure.sfrac Bool.true Ns150p191 Ns150p192)) Bool.false Ns150p189 Ns150p190 92926846052078653 5017600000000000000000 Ns150p193 (Ns150p210 rfl rfl)) 

noncomputable def Ns150p212 := nat_lit 1898754463402420890238976 

noncomputable def Ns150p213 := nat_lit 139923378534294349158156017783704172339082225161578198315286311218834967035042800229985 

noncomputable def Ns150p214 := nat_lit 281003712573074461446937074261577168862690587144086563094394958419562000770297388641 

noncomputable def Ns150p215 := nat_lit 366011033007557365333780243694230278805151947805900093533120842307126575185769709592161 

noncomputable def Ns150p216 := BSN.sin_dyadic_bound_f 26982923819 17179869184 3 2 8388608 3923829 Ns150p213 Ns150p98 Ns150p214 Ns150p215 Ns150p101 Ns150p214 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26982923819) qz357 0 2 Ns150p213 Ns150p98 Ns150p214 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26982923819) qz358 0 2 Ns150p215 Ns150p101 Ns150p214 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p217 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz27) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5323423493) qz368) Bool.false 5323423493 8388608 39 2097152 Bool.false 8388607 8388608 1 1960000 (Ns150p211 rfl) (Enclosure.sfrac_false_div 5323423493 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5323423493) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns150p212) qz369) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 100 1000000000000000 3920000 1960000 (BSN.sin_reduce_arg_pos_rat_q3 5323423493 8388608 226375608064910080 72057594037927936 100 Ns150p212 Ns150p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns150p212 Ns150p86 26982923819 17179869184 3923829 3920000 (Ns150p216 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns150p218 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz27) Bool.false Ns150p189 Ns150p190 92926846052078653 5017600000000000000000 42587387944 67108864 1244 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz27) (@HAdd.hAdd Real Real Real qz356 qz381 (Enclosure.sfrac Bool.true Ns150p191 Ns150p192)) Bool.false Ns150p189 Ns150p190 92926846052078653 5017600000000000000000 Ns150p193 (Ns150p210 rfl rfl)) 

noncomputable def Ns150p219 := Ns150p188 20985 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 226 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 40853776 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 122 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 20611879 67108864) qz30 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz27) qz27 1) Bool.false 8388607 8388608 1227143 64225280000 67108856 67108864 1283 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz27) qz27 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz27)) Bool.false 8388607 8388608 1227143 64225280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz27) qz27) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz27)) Bool.false 8388607 8388608 78537152 4110417920000 8388607 8388608 1227143 64225280000 (Ns150p217 rfl rfl) rfl)) rfl) (Ns150p218 rfl) RS151to168.d7 

noncomputable def Ns150p220 := nat_lit 487371205237590998253319788113226785496072286806300305974456669281 

noncomputable def Ns150p221 := nat_lit 204407911697363319566666894825219806277252434194724268498146401 

noncomputable def Ns150p222 := nat_lit 1461704799889378268120826030550029916875662355550511469386373715041 

noncomputable def Ns150p223 := BSN.cos_dyadic_bound_f 61491093 67108864 3 2 67108864 33554432 Ns150p220 Ns150p117 Ns150p221 Ns150p222 Ns150p120 Ns150p221 40853776 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 61491093) qz362 0 2 Ns150p220 Ns150p117 Ns150p221 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 61491093) (BSN.cosOddQ 67108864) 0 2 Ns150p222 Ns150p120 Ns150p221 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p224 := nat_lit 418500597886904904470171006166368569383887797042796591700467054342133464724049885875469278599410487296 

noncomputable def Ns150p225 := nat_lit 131840473178813145306875610386886108197495955792212102467711775538562690899057918650560215126016 

noncomputable def Ns150p226 := nat_lit 2536378544495735293201368557734296498288350178959209784326132112844063607714669455512067963983568179200 

noncomputable def Ns150p227 := BSN.cos_dyadic_bound_f 84463822 67108864 4 3 67108864 33554432 Ns150p224 Ns150p128 Ns150p225 Ns150p226 Ns150p131 Ns150p225 20611879 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 84463822) qz362 0 3 Ns150p224 Ns150p128 Ns150p225 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 84463822) (BSN.cosOddQ 67108864) 0 3 Ns150p226 Ns150p131 Ns150p225 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p228 := nat_lit 95379166998486056885611978801 

noncomputable def Ns150p229 := BSN.sin_dyadic_bound_f 17573707 67108864 2 1 67108864 33554432 Ns150p228 Ns150p107 Ns150p228 Ns150p228 Ns150p108 Ns150p228 17373541 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 17573707) qz361 0 1 Ns150p228 Ns150p107 Ns150p228 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 17573707) (BSN.sinOddQ 67108864) 0 1 Ns150p228 Ns150p108 Ns150p228 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p230 := nat_lit 2138656149378743222226428279669006023329059834929620935210713707960787669137413490734092291729849790625 

noncomputable def Ns150p231 := nat_lit 1000655997152997578061012434330941250986339205163045085244258375721671715205964832377832275390625 

noncomputable def Ns150p232 := nat_lit 10682514250010415987104967306088570081303059161929002106211697329858555302695297689178536843576147390625 

noncomputable def Ns150p233 := BSN.sin_dyadic_bound_f 100005465 67108864 4 3 67108864 33554432 Ns150p230 Ns150p111 Ns150p231 Ns150p232 Ns150p114 Ns150p231 66891006 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 100005465) qz361 0 3 Ns150p230 Ns150p111 Ns150p231 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 100005465) (BSN.sinOddQ 67108864) 0 3 Ns150p232 Ns150p114 Ns150p231 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p234 := Ns150p186 35513 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 49 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 17373541 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 7 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66891006 67108864) qz30 rfl rfl (Ns150p219 RS151to168.d9 RS151to168.d11 RS151to168.d13 RS151to168.d17 (Ns150p223 rfl rfl) (Ns150p227 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns150p218 rfl) RS151to168.d19 RS151to168.d21 RS151to168.d23 RS151to168.d25 RS151to168.d17 (Ns150p229 rfl rfl) (Ns150p233 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns150p235 := nat_lit 603619917185317111872226144621095445378669712521601313832391475456 

noncomputable def Ns150p236 := nat_lit 313486070514153047880207539741942362598173085715335287226040576 

noncomputable def Ns150p237 := nat_lit 1810232779414923029520918018783802451410812791393373270922722345216 

noncomputable def Ns150p238 := BSN.cos_dyadic_bound_f 64867518 67108864 3 2 67108864 33554432 Ns150p235 Ns150p117 Ns150p236 Ns150p237 Ns150p120 Ns150p236 38124529 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 64867518) qz362 0 2 Ns150p235 Ns150p117 Ns150p236 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 64867518) (BSN.cosOddQ 67108864) 0 2 Ns150p237 Ns150p120 Ns150p236 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p239 := nat_lit 3223536302781144629158880016 

noncomputable def Ns150p240 := BSN.cos_dyadic_bound_f 7534998 67108864 2 1 67108864 33554432 Ns150p239 Ns150p134 Ns150p239 Ns150p239 Ns150p135 Ns150p239 66686292 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 7534998) qz362 0 1 Ns150p239 Ns150p134 Ns150p239 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 7534998) (BSN.cosOddQ 67108864) 0 1 Ns150p239 Ns150p135 Ns150p239 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p241 := Ns150p184 47575 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 54 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 38124529 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 94 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66686292 67108864) qz30 rfl rfl (Ns150p234 rfl rfl) (Ns150p218 rfl) RS151to168.d27 RS151to168.d29 RS151to168.d31 RS151to168.d33 RS151to168.d17 (Ns150p238 rfl rfl) (Ns150p240 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns150p242 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz27) qz27 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz27) qz27 7) 6779074 67108864 47575 67108864 6779074 67108864 47575 67108864 909871910223872 3389537 16777216 47575 33554432 (Ns150p241 rfl) 

noncomputable def Ns150p243 := @Enclosure.Real.IsNear.mulLit_tf qz377 (Zeta.RiemannSiegel.correction qz29) 1482971 4194304 1 4194304 1014089699255 1099511627776 3350429442819 43100855808819200 1503865615393886605 4611686018427387904 

noncomputable def Ns150p244 := @Enclosure.Real.IsNear.mulLit_tf qz363 (@HPow.hPow Real Real Real qz6 qz28 qz8) 1 1 0 1 1482971 4194304 1 4194304 1482971 4194304 1 4194304 

noncomputable def Ns150p245 := @Enclosure.Real.IsNear.sqrt_image qz28 268391606581 4194304000 201029 4194304000 33551678 33551704 4194304 (@Enclosure.Real.IsNear.of_eq qz28 (@HMul.hMul Real Real Real qz4 qz27 qz2) Bool.false 268391606581 4194304000 201029 4194304000 (BSN.t_div_two_pi_mk qz27 402058 1000 qz30) (@Enclosure.Real.IsNear.mulLit_ff qz27 qz2 402058 1000 0 1 1335089 8388608 1 8388608 268391606581 4194304000 201029 4194304000 (Enclosure.Real.IsNear.const Bool.false 402058 1000) RS151to168.d36 rfl)) 

noncomputable abbrev qz848 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 402058 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz642 := qz848

noncomputable abbrev qz384 := qz642

noncomputable abbrev qz33 := qz384

noncomputable def Ns150p246 := @Enclosure.Real.IsNear.sqrt_image qz33 33551691 4194304 13 4194304 11862796 11862801 4194304 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 67103382 8388608 26 8388608 33551691 4194304 13 4194304 (Ns150p245 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns150p247 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz33) 23725597 8388608 5 8388608 1482970 1482972 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz33) Bool.false 23725597 8388608 5 8388608 23725597 8388608 5 8388608 (Ns150p246 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns150p248 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz33)) Bool.false 2965942 8388608 2 8388608 1482971 4194304 1 4194304 (Ns150p247 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz34 := (@HMul.hMul Real Real Real qz340 qz338 qz376)

noncomputable abbrev qz643 := (@HMul.hMul Real Real Real qz839 qz847 qz847)

noncomputable abbrev qz385 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz643 qz641) qz638)

noncomputable abbrev qz35 := (Real.cos (@HMul.hMul Real Real Real qz340 qz338 qz385))

noncomputable def Ns150p249 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz29) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz34)) qz35) Bool.false 1014089699255 

noncomputable def Ns150p250 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz34)) qz35 1048585 1048576 85 

noncomputable def Ns150p251 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz34)) Bool.false 8388680 8388608 170 8388608 1048585 1048576 85 

noncomputable def Ns150p252 := @Enclosure.Real.IsNear.recentre' (Real.cos qz34) Bool.false 8388536 8388608 82457152 4110417920000 1048567 1048576 1288393 64225280000 

noncomputable def Ns150p253 := @Enclosure.Real.IsNear.cos_image qz34 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 26336367) qz359) Bool.false 26336367 4194304 41 2097152 Bool.false 8388536 8388608 1 

noncomputable def Ns150p254 := nat_lit 350818980353577842925443867 

noncomputable def Ns150p255 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz29 884279719003555 140737488355328 1 500000000000000 4191563 4194304 13 4194304 3706514151825698006465 590295810358705651712 Ns150p254 

noncomputable def Ns150p256 := @Enclosure.Real.IsNear.subLit_ff_p qz33 qz334 33551691 4194304 13 4194304 7 1 0 1 4191563 4191563 4194304 13 

noncomputable def Ns150p257 := @Ns150p256 4194304 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 67103382 8388608 26 8388608 33551691 4194304 13 4194304 (Ns150p245 rfl rfl rfl rfl rfl rfl) rfl) (Enclosure.Real.IsNear.const Bool.false 7 1) 

noncomputable def Ns150p258 := @Enclosure.Real.IsNear.recentre' qz34 Bool.false 3706514151825698006465 590295810358705651712 Ns150p254 Ns150p151 26336367 4194304 41 2097152 (@Ns150p255 Ns150p151 RS151to168.d35 (Ns150p257 rfl rfl) rfl) 

noncomputable def Ns150p259 := nat_lit 138527983153814687133013488401883280864625477492541602220604836849098420910549299691520 

noncomputable def Ns150p260 := nat_lit 275438012547049490182906221331088071670100053373379455259484118281581481119973441536 

noncomputable def Ns150p261 := nat_lit 362365437192057529030929669075158259672267517155956820031163979365659018082006304096256 

noncomputable def Ns150p262 := BSN.sin_dyadic_bound_f 26915533004 17179869184 3 2 8388608 3923829 Ns150p259 Ns150p98 Ns150p260 Ns150p261 Ns150p101 Ns150p260 8388536 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26915533004) qz357 0 2 Ns150p259 Ns150p98 Ns150p260 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26915533004) qz358 0 2 Ns150p261 Ns150p101 Ns150p260 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p263 := @Ns150p253 1960000 (Ns150p258 rfl) (Enclosure.sfrac_false_div 26336367 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 26336367) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 947006128212510259544064) qz360) 226375608064910080 72057594037927936 Bool.false 8388536 8388608 0 1000000000000000 3920000 1960000 (BSN.sin_reduce_arg_pos_rat_q3 26336367 4194304 226375608064910080 72057594037927936 0 947006128212510259544064 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388536 8388608 947006128212510259544064 604462909807314587353088 26915533004 17179869184 3923829 3920000 (Ns150p262 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns150p264 := @Enclosure.Real.IsNear.inv_image (Real.cos qz34) 1048567 1048576 1288393 64225280000 4194255 4194425 4194304 (Ns150p252 (Ns150p263 rfl rfl) rfl) rfl 

noncomputable def Ns150p265 := @Enclosure.Real.IsNear.recentre' qz35 Bool.false 3868412 4194304 

noncomputable abbrev qz36 := (@HMul.hMul Real Real Real qz340 qz338 qz385)

noncomputable abbrev qz386 := (@Nat.cast Real Real.instNatCast 2097152)

noncomputable def Ns150p266 := @Enclosure.Real.IsNear.cos_image qz36 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 832155)) qz386) Bool.true 832155 2097152 

noncomputable def Ns150p267 := nat_lit 982435388541056877016464245 

noncomputable def Ns150p268 := nat_lit 2475880078570760549798248448 

noncomputable def Ns150p269 := nat_lit 4412405728271934583984851487813681 

noncomputable def Ns150p270 := @Enclosure.Real.IsNear.recentre' qz36 Bool.true Ns150p267 Ns150p268 Ns150p269 

noncomputable abbrev qz37 := qz385

noncomputable def Ns150p271 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz37 884279719003555 140737488355328 1 500000000000000 1111000701959 

noncomputable abbrev qz387 := (@HSub.hSub Real Real Real qz634 qz643 qz641)

noncomputable abbrev qz38 := qz387

noncomputable def Ns150p272 := @Enclosure.Real.IsNear.subLit_tf qz38 qz25 11489074183 17592186044416 163506759 17592186044416 1 16 

noncomputable abbrev qz388 := qz643

noncomputable abbrev qz39 := qz388

noncomputable def Ns150p273 := @Enclosure.Real.IsNear.subLit_ff_n qz39 qz29 17569200382969 17592186044416 108980807 17592186044416 4191563 4194304 13 4194304 

noncomputable def Ns150p274 := @Enclosure.Real.IsNear.mulLit_ff qz29 qz29 4191563 4194304 13 4194304 4191563 4194304 13 4194304 17569200382969 17592186044416 

noncomputable def Ns150p275 := nat_lit 464227514732017603087171584 

noncomputable def Ns150p276 := nat_lit 6963412720980264046307573760 

noncomputable def Ns150p277 := BSN.cos_dyadic_bound_f 832155 2097152 2 1 4194304 1960000 479531242800643233200625 Ns150p275 479531242800643233200625 479531242800643233200625 Ns150p276 479531242800643233200625 3868412 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 832155) (BSN.cosEvenQ 2097152) 0 1 479531242800643233200625 Ns150p275 479531242800643233200625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 832155) (BSN.cosOddQ 2097152) 0 1 479531242800643233200625 Ns150p276 479531242800643233200625 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p278 := @Ns150p265 970748608 16441671680000 967103 1048576 15167947 256901120000 (@Ns150p266 491 8388608 Bool.false 3868412 4194304 1 1960000 (@Ns150p270 Ns150p169 832155 2097152 491 8388608 (@Ns150p271 17592186044416 163506759 17592186044416 Ns150p267 Ns150p268 Ns150p269 Ns150p169 RS151to168.d35 (@Ns150p272 0 1 17776011231344 1111000701959 17592186044416 163506759 17592186044416 (@Ns150p273 48188669802053632 11489074183 17592186044416 163506759 17592186044416 (@Ns150p274 108980807 17592186044416 (Ns150p257 rfl rfl) (Ns150p257 rfl rfl) rfl) (Ns150p257 rfl rfl) rfl rfl) qz373 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 832155 2097152) (BSN.cos_neg_of_bound 832155 2097152 Bool.false 3868412 4194304 1 1960000 (Ns150p277 rfl rfl)) rfl rfl) 

noncomputable def Ns150p279 := @Ns150p243 1252086341971743517 45194522980588401459200 (Ns150p244 (@Enclosure.Real.IsNear.of_eq qz363 (Enclosure.sfrac Bool.true 1 1) Bool.true 1 1 0 1 (BSN.neg_one_pow_odd_mk 7 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Real Real qz6 qz28 qz8) (@Inv.inv Real Real.instInv (Real.sqrt qz33)) Bool.false 1482971 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz28 (BSN.t_div_two_pi_nonneg qz27 402058 1000 qz30)) Ns150p248) rfl) (@Ns150p249 1099511627776 3350429442819 43100855808819200 (BSN.correction_mk qz29 (BSN.cos_two_pi_p_ne_zero_mk qz27 402058 1000 7 qz30 rfl rfl (@BSN.floor_sqrt_eq_dec qz27 402058 1000 7 qz30 rfl rfl rfl))) (@Ns150p250 4194304 967103 1048576 15167947 256901120000 1014089699255 1099511627776 3350429442819 43100855808819200 (@Ns150p251 4194304 (Ns150p264 rfl rfl rfl rfl rfl) rfl) (Ns150p278 rfl) rfl)) 

noncomputable def Ns150p280 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz27) (hardyZApproximantRS₀ qz27) Bool.false 2435574451463131533 4611686018427387904 65330936813989663517 45194522980588401459200 (@Eq.refl Real (hardyZApproximantRS₀ qz27)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz27) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz27) qz27 7) (@HMul.hMul Real Real Real qz4 qz377 (Zeta.RiemannSiegel.correction qz29))) Bool.false 2435574451463131533 4611686018427387904 65330936813989663517 45194522980588401459200 (BSN.hardyZApproximantRS₀_eq qz27 7 (@BSN.floor_sqrt_eq_dec qz27 402058 1000 7 qz30 rfl rfl rfl)) (@Ns150p182 2435574451463131533 4611686018427387904 65330936813989663517 45194522980588401459200 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz27) qz27 7) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz27) qz27 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz27) qz27 7)) Bool.false 3389537 16777216 47575 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz27) qz27 7) (Ns150p242 (Ns150p241 rfl) rfl rfl)) (Ns150p279 rfl) rfl rfl)) 

theorem RS151to168.d39 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz27) Bool.false 2435574451463131533 4611686018427387904 65330936813989663517 45194522980588401459200 := Ns150p280 

noncomputable abbrev qz644 := (@HMul.hMul Real Real Real qz839 (Real.sqrt qz844) qz841)

noncomputable abbrev qz389 := qz644

noncomputable abbrev qz40 := qz389

noncomputable abbrev qz390 := (@HMul.hMul Real Real Real qz630 (@HMul.hMul Real Real Real qz630 qz644 qz644) qz644)

noncomputable abbrev qz41 := (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz390))

noncomputable abbrev qz42 := (@HMul.hMul Real Real Real qz340 (@HMul.hMul Real Real Real qz340 qz366 qz366) qz366)

noncomputable abbrev qz391 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz40))

noncomputable def Ns150p281 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (@HAdd.hAdd Real Real Real qz356 (@HAdd.hAdd Real Real Real qz356 qz391 qz41) (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz42))) Bool.false 

noncomputable def Ns150p282 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz356 qz391 qz41) (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz42)) 9313801 268435456 

noncomputable def Ns150p283 := @Enclosure.Real.IsNear.addLit_ff qz391 qz41 1164225 33554432 25 33554432 

noncomputable def Ns150p284 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz40) 25 4 0 1 46569 8388608 1 8388608 1164225 

noncomputable def Ns150p285 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz40) Bool.false 46569 8388608 1 8388608 46569 8388608 1 8388608 

noncomputable def Ns150p286 := @Enclosure.Real.IsNear.mulLit_ff qz19 qz7 23703275 8388608 5 8388608 534765893683 8388608000 400547 8388608000 507028121543556473 2814749767106560 486724286503 

noncomputable def Ns150p287 := @Enclosure.Real.IsNear.sqrt_image qz7 534765893683 8388608000 400547 8388608000 33488573 33488599 4194304 qz364 

noncomputable def Ns150p288 := @Enclosure.Real.IsNear.sqrt_image qz18 16744293 2097152 13 4194304 11851635 11851640 4194304 (@Enclosure.Real.IsNear.recentre' qz18 Bool.false 66977172 8388608 26 8388608 16744293 2097152 13 4194304 (Ns150p287 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz392 := (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 23703275 8388608 5 8388608 23703275 8388608 5 8388608 (Ns150p288 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns150p289 := @Ns150p286 2814749767106560 qz392 

noncomputable def Ns150p290 := Ns150p289 qz364 

noncomputable def Ns150p291 := @Enclosure.Real.IsNear.inv_image qz40 507028121543556473 2814749767106560 486724286503 2814749767106560 23284 23285 4194304 (Ns150p290 rfl) rfl rfl 

noncomputable abbrev qz43 := (@Inv.inv Real Real.instInv qz390)

noncomputable def Ns150p292 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz43 1 32 0 1 1 

noncomputable def Ns150p293 := @Enclosure.Real.IsNear.recentre' qz43 Bool.false 1 8388608 1 8388608 

noncomputable def Ns150p294 := nat_lit 130345530046810246047572529848522762213510638810795817 

noncomputable def Ns150p295 := nat_lit 22300745198530623141535718272648361505980416000 

noncomputable def Ns150p296 := nat_lit 375377972051547726169263051414086243724293894359 

noncomputable abbrev qz44 := qz390

noncomputable def Ns150p297 := @Enclosure.Real.IsNear.inv_image qz44 Ns150p294 Ns150p295 Ns150p296 Ns150p295 0 1 

noncomputable def Ns150p298 := nat_lit 257077516035987475620608105340199729 

noncomputable def Ns150p299 := nat_lit 7922816251426433759354395033600 

noncomputable def Ns150p300 := nat_lit 493566038291018846570452336847 

noncomputable abbrev qz393 := (@HMul.hMul Real Real Real qz630 qz644 qz644)

noncomputable abbrev qz45 := qz393

noncomputable def Ns150p301 := @Enclosure.Real.IsNear.mulLit_ff qz45 qz40 Ns150p298 Ns150p299 Ns150p300 Ns150p299 507028121543556473 2814749767106560 486724286503 

noncomputable def Ns150p302 := @Enclosure.Real.IsNear.mulLit_ff qz40 qz40 507028121543556473 2814749767106560 486724286503 2814749767106560 507028121543556473 2814749767106560 486724286503 2814749767106560 Ns150p298 

noncomputable def Ns150p303 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz42) 13 10 0 1 371821 8388608 1 

noncomputable def Ns150p304 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz42) Bool.false 371821 8388608 1 8388608 371821 8388608 

noncomputable def Ns150p305 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz4 qz19 qz19) qz19 561845245725625 70368744177664 237032775 70368744177664 23703275 8388608 5 8388608 13317572366877063921875 

noncomputable def Ns150p306 := @Enclosure.Real.IsNear.mulLit_ff qz19 qz19 23703275 8388608 5 8388608 23703275 8388608 5 8388608 561845245725625 70368744177664 237032775 

noncomputable def Ns150p307 := @Ns150p306 70368744177664 qz392 

noncomputable def Ns150p308 := Ns150p307 qz392 

noncomputable def Ns150p309 := @Ns150p305 590295810358705651712 8427680463630125 590295810358705651712 (Ns150p308 rfl) qz392 

noncomputable def Ns150p310 := @Enclosure.Real.IsNear.inv_image qz42 13317572366877063921875 590295810358705651712 8427680463630125 590295810358705651712 185910 185911 4194304 (Ns150p309 rfl) 

noncomputable def Ns150p311 := @Ns150p282 201 268435456 4833673 83886080 13 83886080 2078827471699968 123907773 1342177280 1213 1342177280 (@Ns150p283 1 268435456 1 268435456 312519302316032 9313801 268435456 201 268435456 (@Ns150p284 33554432 25 33554432 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns150p285 (Ns150p291 rfl rfl rfl rfl) rfl) rfl) (@Ns150p292 8388608 1 8388608 1 268435456 1 268435456 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns150p293 1 8388608 1 8388608 (@Ns150p297 4194304 (@Ns150p301 2814749767106560 Ns150p294 Ns150p295 Ns150p296 Ns150p295 (@Ns150p302 Ns150p299 Ns150p300 Ns150p299 (Ns150p290 rfl) (Ns150p290 rfl) rfl) (Ns150p290 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns150p303 8388608 4833673 83886080 13 83886080 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns150p304 1 8388608 (Ns150p310 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS151to168.d40 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 := @Ns150p281 123907773 1342177280 1213 1342177280 (BSN.hardyZErrorBoundRS₀_mk qz3 400547 1000 qz10 rfl rfl) (Ns150p311 rfl rfl) 

noncomputable def Ns150p312 := BSN.log_dyadic_bound 0 16 1 0 1 4194304 1960000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz849 := (Enclosure.sfrac Bool.false 8 1)

noncomputable abbrev qz645 := qz849

noncomputable abbrev qz394 := qz645

noncomputable abbrev qz46 := qz394

noncomputable abbrev qz395 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) (@Nat.cast Real Real.instNatCast 1))

theorem RS151to168.d41 : Enclosure.Real.IsNear (Real.log qz46) Bool.false 9364972152248037 4503599627370496 25000000147 49000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 25000000147 49000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz395) Bool.false 314236321264500404649984 151115727451828646838272 1000000005880000 1960000000000000000000 9364972152248037 4503599627370496 25000000147 49000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 4194304 24973259072661432 36028797018963968 1960000 1000000000000000 rfl rfl rfl rfl (Ns150p312 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS151to168.d42 : Enclosure.Real.IsNear (Real.log qz46) Bool.false 139548959 67108864 35 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log qz46) Bool.false 9364972152248037 4503599627370496 25000000147 49000000000000000 139548959 67108864 35 67108864 RS151to168.d41 rfl 

noncomputable abbrev qz396 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns150p313 := @Enclosure.Real.IsNear.inv_image qz396 23726567 8388608 1 8388608 1482910 1482911 4194304 (@Enclosure.Real.IsNear.of_eq qz396 (Real.sqrt qz395) Bool.false 23726567 8388608 1 8388608 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz395) Bool.false 23726567 8388608 1 8388608 23726567 8388608 1 8388608 (BSN.sqrt_enclosure 8 1 11863283 11863284 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz397 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS151to168.d43 : Enclosure.Real.IsNear qz397 Bool.false 2965821 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz397 Bool.false 2965821 8388608 1 8388608 2965821 8388608 1 8388608 (Ns150p313 rfl rfl) rfl 

theorem RS151to168.d44 : Enclosure.Real.IsNear qz397 Bool.false 23726568 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz397 Bool.false 2965821 8388608 1 8388608 23726568 67108864 8 67108864 RS151to168.d43 rfl 

noncomputable def Ns150p314 := nat_lit 2450675674302535886033649664 

noncomputable abbrev qz850 := (Enclosure.sfrac Bool.false 403568 1000)

noncomputable abbrev qz646 := qz850

noncomputable abbrev qz398 := qz646

noncomputable abbrev qz47 := qz398

noncomputable abbrev qz48 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 8)

noncomputable abbrev qz851 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 403568 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz647 := qz851

noncomputable abbrev qz399 := qz647

noncomputable abbrev qz49 := qz399

noncomputable abbrev qz852 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 403568 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz648 := qz852

noncomputable abbrev qz400 := qz648

noncomputable abbrev qz50 := qz400

noncomputable abbrev qz649 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz49 qz8))

noncomputable def Ns150p315 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz47) qz47 8) (@HMul.hMul Real Real Real qz4 qz649 (Zeta.RiemannSiegel.correction qz50)) 22665471 33554432 53203 33554432 23193928686207326285 73786976294838206464 7864069723646045107 564931537257355018240000 Ns150p314 

noncomputable def Ns150p316 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz47) qz47 Real.cos BSN.quadSignPos 7 8 403568 1000 128 67108864 33554432 1125899906842624 Bool.false 42798193640 1249 139548959 35 23726568 8 

noncomputable def Ns150p317 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz47) qz47 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 403568 1000 54 93 67108864 33554432 1125899906842624 Bool.false 42798193640 1249 

noncomputable def Ns150p318 := Ns150p317 120242927 35 27397080 8 130587807 35 25364760 8 Bool.false 4288227 35650 Bool.true 35628641 Bool.true 99331248 3537118876014220 1 Bool.false 57871169 Bool.true Bool.false 66833349 Bool.true Bool.true 44598205 

noncomputable def Ns150p319 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz47) qz47 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 403568 1000 49 7 67108864 33554432 1125899906842624 Bool.false 42798193640 1249 

noncomputable def Ns150p320 := Ns150p319 93032624 35 33554424 8 108007536 35 30011992 8 Bool.false 15616683 21067 Bool.false 87900141 Bool.true 52291148 3537118876014220 1 Bool.false 64836357 Bool.true Bool.false 47158044 Bool.false Bool.false 4288227 

noncomputable def Ns150p321 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz47) qz47 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 403568 1000 227 123 67108864 33554432 1125899906842624 Bool.false 42798193640 1249 

noncomputable def Ns150p322 := Ns150p321 46516304 35 47453136 16 73726608 35 38745320 8 Bool.true 67108848 1291 Bool.false 96642813 Bool.false 78527983 3537118876014220 1 Bool.false 66536432 Bool.false Bool.false 61794666 Bool.false Bool.false 15616683 

noncomputable def Ns150p323 := nat_lit 6816010204659193107642404876190001192332078646734947 

noncomputable def Ns150p324 := nat_lit 10687710460030962627558805670681761295319957504000 

noncomputable def Ns150p325 := nat_lit 5138383789611057158899334512640000 

noncomputable def Ns150p326 := nat_lit 12442132527976020504206891253918597120 

noncomputable abbrev qz401 := (@Eq.refl Real qz646)

noncomputable abbrev qz51 := qz401

noncomputable def Ns150p327 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz47 403568 1000 651469522496 16000000 807136 4000 2000 Ns150p325 Ns150p326 qz51 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns150p328 := nat_lit 8933880895450897590049052919319758362813502123848429731840 

noncomputable abbrev qz402 := (Real.log (Enclosure.sfrac Bool.false 651469522496 16000000))

noncomputable abbrev qz403 := (Enclosure.sfrac Bool.false 403568 2000)

noncomputable abbrev qz52 := (@HSub.hSub Real Real Real qz344 (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 403568 4000) qz402) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 807136)))))) qz403)

noncomputable abbrev qz404 := (@HSub.hSub Real Real Real qz11 qz52 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 403568 2000) (Real.log Real.pi)))

noncomputable def Ns150p329 := @Enclosure.Real.IsNear.addLit_ft_p qz404 (Enclosure.sfrac Bool.true Ns150p325 Ns150p326) 718035004101504757107 1125899906842624000 11659180705129711 627200000000000000000 Ns150p325 Ns150p326 0 1 Ns150p328 

noncomputable def Ns150p330 := nat_lit 120466283593718312350116741120 

noncomputable abbrev qz405 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 403568 2000) (Real.log Real.pi))

noncomputable def Ns150p331 := @Enclosure.Real.IsNear.subLit_ff_p qz52 qz405 39124182734889737067 45035996273704960 64307514832349 9800000000000000000 968834624703 4194304000 25223 2097152000 Ns150p330 718035004101504757107 1125899906842624000 

noncomputable def Ns150p332 := nat_lit 1956209136744486853350000 

noncomputable abbrev qz53 := (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 403568 4000) qz402) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 807136))))))

noncomputable def Ns150p333 := @Enclosure.Real.IsNear.subLit_ff_p qz53 qz403 1205293155174575467891 1125899906842624000 64307514832349 9800000000000000000 403568 2000 0 1 Ns150p332 39124182734889737067 45035996273704960 64307514832349 9800000000000000000 

noncomputable def Ns150p334 := nat_lit 2714078902258213744948408794604371968 

noncomputable def Ns150p335 := nat_lit 12832018797722412307709952 

noncomputable def Ns150p336 := nat_lit 277393254117505944121461863332284156293335988813243347328091129427085230080 

noncomputable def Ns150p337 := nat_lit 1089558951510950067948089034211092361027803452652363091440972179561250816 

noncomputable def Ns150p338 := nat_lit 63479774726621400523807573645752808265457862606813051406110886461440 

noncomputable def Ns150p339 := BSN.log_dyadic_bound 127181522496 1175757522496 4 3 Ns150p336 33554432 15680000 Ns150p337 Ns150p338 7287669 1302939044992 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 127181522496) (BSN.artanhQ 1175757522496) 0 3 Ns150p337 Ns150p336 Ns150p338 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns150p340 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 403568 4000) qz402 403568 4000 0 1 47802995136836217 4503599627370496 625000147 9800000000000000 1205734946336419901391 1125899906842624000 15764378707781 2450000000000000000 (Enclosure.Real.IsNear.const Bool.false 403568 4000) (BSN.isNear_log_sfrac 651469522496 16000000 47802995136836217 4503599627370496 625000147 9800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 651469522496) qz352)) Bool.false Ns150p335 Ns150p86 1000000235200000 15680000000000000000000 47802995136836217 4503599627370496 625000147 9800000000000000 (BSN.log_rat_reduce_isNear 651469522496 16000000 15 1302939044992 1048576000000 7287669 33554432 24973259072661432 36028797018963968 15680000 1000000000000000 rfl rfl rfl rfl (Ns150p339 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns150p341 := BSN.arctan_dyadic_bound_f 1000 807136 1 0 4194304 1960000 0 1 1 0 1 1 5196 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 807136) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 807136) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz406 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 807136)))

noncomputable def Ns150p342 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz406 884279719003555 562949953421312 1 2000000000000000 5196 4194304 1 1960000 3706012874577509613568 883582323688867 562949953421312 50000000049 98000000000000000 qz16 (Ns150p341 rfl) rfl rfl 

noncomputable def Ns150p343 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 403568 4000) qz402) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz406)) 1205734946336419901391 1125899906842624000 15764378707781 2450000000000000000 883582323688867 2251799813685248 50000000049 392000000000000000 Ns150p334 1205293155174575467891 1125899906842624000 64307514832349 9800000000000000000 (Ns150p340 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz406) 1 4 0 1 883582323688867 562949953421312 50000000049 98000000000000000 883582323688867 2251799813685248 50000000049 392000000000000000 qz355 Ns150p342 rfl) 

noncomputable def Ns150p344 := @Ns150p329 Ns150p323 Ns150p324 11659180705129711 627200000000000000000 (@Ns150p331 11659180705129711 627200000000000000000 (Ns150p333 (Ns150p343 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 403568 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz403 (Real.log Real.pi) 403568 2000 0 1 38410761 33554432 1 16777216 968834624703 4194304000 25223 2097152000 (Enclosure.Real.IsNear.const Bool.false 403568 2000) RS151to168.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns150p325 Ns150p326) 

noncomputable def Ns150p345 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz47) Bool.false Ns150p323 Ns150p324 11659180705129711 627200000000000000000 5349774205 8388608 157 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz47) (@HAdd.hAdd Real Real Real qz356 qz404 (Enclosure.sfrac Bool.true Ns150p325 Ns150p326)) Bool.false Ns150p323 Ns150p324 11659180705129711 627200000000000000000 Ns150p327 (Ns150p344 rfl rfl)) 

noncomputable def Ns150p346 := nat_lit 1898339805578794694082560 

noncomputable def Ns150p347 := nat_lit 139800945221158327889438460445058265330515492007070041935286847563275296526869546039105 

noncomputable def Ns150p348 := nat_lit 280513153670075798461052449364099427203869773906452273256614100491743993083571894081 

noncomputable def Ns150p349 := nat_lit 365691168568520259846259025771420248221591451813144425197621511264924857772046837512001 

noncomputable def Ns150p350 := BSN.sin_dyadic_bound_f 26977031177 17179869184 3 2 8388608 3923829 Ns150p347 Ns150p98 Ns150p348 Ns150p349 Ns150p101 Ns150p348 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26977031177) qz357 0 2 Ns150p347 Ns150p98 Ns150p348 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26977031177) qz358 0 2 Ns150p349 Ns150p101 Ns150p348 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p351 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz47) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5349774205) qz368) Bool.false 5349774205 8388608 157 8388608 Bool.true 8388606 8388608 1 1960000 (Ns150p345 rfl) (Enclosure.sfrac_false_div 5349774205 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5349774205) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns150p346) qz369) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 101 1000000000000000 3920000 1960000 (BSN.sin_reduce_arg_pos_rat_q1 5349774205 8388608 226375608064910080 72057594037927936 101 Ns150p346 Ns150p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388606 8388608 Ns150p346 Ns150p86 26977031177 17179869184 3923829 3920000 (Ns150p350 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns150p352 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz47) Bool.false Ns150p323 Ns150p324 11659180705129711 627200000000000000000 42798193640 67108864 1249 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz47) (@HAdd.hAdd Real Real Real qz356 qz404 (Enclosure.sfrac Bool.true Ns150p325 Ns150p326)) Bool.false Ns150p323 Ns150p324 11659180705129711 627200000000000000000 Ns150p327 (Ns150p344 rfl rfl)) 

noncomputable def Ns150p353 := Ns150p322 21067 BSN.abs_quadSignPos (BSN.cos_quad_nat3 227 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66536432 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 123 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 61794666 67108864) qz51 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz47) qz47 1) Bool.true 4194303 4194304 4939197 256901120000 67108848 67108864 1291 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz47) qz47 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz47)) Bool.true 4194303 4194304 4939197 256901120000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz47) qz47) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz47)) Bool.true 8388606 8388608 316108608 16441671680000 4194303 4194304 4939197 256901120000 (Ns150p351 rfl rfl) rfl)) rfl) (Ns150p352 rfl) RS151to168.d7 

noncomputable def Ns150p354 := nat_lit 1864806658101704613671185707272810367468024993207766403877837364884130310268626593624575341017262800881 

noncomputable def Ns150p355 := nat_lit 663796182730351815182310165803903221608910205269518785102809149327848552651410848741662275485681 

noncomputable def Ns150p356 := nat_lit 9315844487838011766823597179933215880813871903035142181170337360084246966294681947722445697132735840241 

noncomputable def Ns150p357 := BSN.sin_dyadic_bound_f 96642813 67108864 4 3 67108864 33554432 Ns150p354 Ns150p111 Ns150p355 Ns150p356 Ns150p114 Ns150p355 66536432 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 96642813) qz361 0 3 Ns150p354 Ns150p111 Ns150p355 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 96642813) (BSN.sinOddQ 67108864) 0 3 Ns150p356 Ns150p114 Ns150p355 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p358 := nat_lit 2333825005550622239109372729986239584721789454754281178485453925505 

noncomputable def Ns150p359 := nat_lit 149280173440179812144298804241602837812033797730278365202985810657280 

noncomputable def Ns150p360 := nat_lit 1446090728058420033286791878607278944587972535283271007157005441 

noncomputable def Ns150p361 := nat_lit 6110057534310963660470654725017644270265829949775515885831267986561 

noncomputable def Ns150p362 := nat_lit 2736803179736629889312144744429385359887286291721770028721406528716800 

noncomputable def Ns150p363 := BSN.sin_dyadic_bound_f 78527983 67108864 3 2 67108864 33554432 Ns150p358 Ns150p359 Ns150p360 Ns150p361 Ns150p362 Ns150p360 61794666 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 78527983) qz361 0 2 Ns150p358 Ns150p359 Ns150p360 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 78527983) (BSN.sinOddQ 67108864) 0 2 Ns150p361 Ns150p362 Ns150p360 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p364 := nat_lit 3665068752880869539272987153466322240276343061018557517436869843745 

noncomputable def Ns150p365 := nat_lit 3563826671797826003609934941716620215896535940581611586747013921 

noncomputable def Ns150p366 := nat_lit 9593219585790795170280550269172826577517066006382899460241830615841 

noncomputable def Ns150p367 := BSN.sin_dyadic_bound_f 87900141 67108864 3 2 67108864 33554432 Ns150p364 Ns150p359 Ns150p365 Ns150p366 Ns150p362 Ns150p365 64836357 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 87900141) qz361 0 2 Ns150p364 Ns150p359 Ns150p365 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 87900141) (BSN.sinOddQ 67108864) 0 2 Ns150p366 Ns150p362 Ns150p365 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p368 := nat_lit 458634773672055945405461822143317760163537069830315388495739289600 

noncomputable def Ns150p369 := nat_lit 55901751008814407003274909580971652656854359164045958179782656 

noncomputable def Ns150p370 := nat_lit 1201095804401370347974394708140796370133533609164560419270835634176 

noncomputable def Ns150p371 := BSN.sin_dyadic_bound_f 52291148 67108864 3 2 67108864 33554432 Ns150p368 Ns150p359 Ns150p369 Ns150p370 Ns150p362 Ns150p369 47158044 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 52291148) qz361 0 2 Ns150p368 Ns150p359 Ns150p369 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 52291148) (BSN.sinOddQ 67108864) 0 2 Ns150p370 Ns150p362 Ns150p369 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p372 := Ns150p320 35650 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 49 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 64836357 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 7 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 47158044 67108864) qz51 rfl rfl (Ns150p353 RS151to168.d9 RS151to168.d11 RS151to168.d13 RS151to168.d17 (Ns150p357 rfl rfl) (Ns150p363 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns150p352 rfl) RS151to168.d19 RS151to168.d21 RS151to168.d23 RS151to168.d25 RS151to168.d17 (Ns150p367 rfl rfl) (Ns150p371 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns150p373 := nat_lit 54909361885485198202979920139781204511276079805610091878423929601 

noncomputable def Ns150p374 := nat_lit 2596534260447697688571918715270963044593039007426558508081921 

noncomputable def Ns150p375 := nat_lit 164722892587934699213562616581913071607739053338815422518255624961 

noncomputable def Ns150p376 := BSN.cos_dyadic_bound_f 35628641 67108864 3 2 67108864 33554432 Ns150p373 Ns150p117 Ns150p374 Ns150p375 Ns150p120 Ns150p374 57871169 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 35628641) qz362 0 2 Ns150p373 Ns150p117 Ns150p374 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 35628641) (BSN.cosOddQ 67108864) 0 2 Ns150p375 Ns150p120 Ns150p374 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p377 := nat_lit 2081472662843794497341718736657484945216846375100671963206768163761262692004694104060191988865979908096 

noncomputable def Ns150p378 := nat_lit 922636653726841833125513758889402239254903958787045704760614195843761657478958716487918835204096 

noncomputable def Ns150p379 := nat_lit 10397164084434372230691845888905539728245979175402081153784296009253388216863525879375158063228052832256 

noncomputable def Ns150p380 := BSN.sin_dyadic_bound_f 99331248 67108864 4 3 67108864 33554432 Ns150p377 Ns150p111 Ns150p378 Ns150p379 Ns150p114 Ns150p378 66833349 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 99331248) qz361 0 3 Ns150p377 Ns150p111 Ns150p378 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 99331248) (BSN.sinOddQ 67108864) 0 3 Ns150p379 Ns150p114 Ns150p378 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz650 := (BSN.cos_quad_nat1 93 rfl)

noncomputable def Ns150p381 := Ns150p318 47757 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 54 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 57871169 67108864) BSN.abs_quadSignNeg qz650 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66833349 67108864) qz51 rfl rfl (Ns150p372 rfl rfl) (Ns150p352 rfl) RS151to168.d27 RS151to168.d29 RS151to168.d31 RS151to168.d33 RS151to168.d17 (Ns150p376 rfl rfl) (Ns150p380 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns150p382 := nat_lit 16210944779676657345154106775308957560365525056856859276975332001 

noncomputable def Ns150p383 := nat_lit 226332470650661999688201015009609991552173220629145238428321 

noncomputable def Ns150p384 := nat_lit 48632381674088670711462943923896853461113470824129319540449139361 

noncomputable def Ns150p385 := BSN.cos_dyadic_bound_f 26262941 67108864 3 2 67108864 33554432 Ns150p382 Ns150p117 Ns150p383 Ns150p384 Ns150p120 Ns150p383 62035138 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 26262941) qz362 0 2 Ns150p382 Ns150p117 Ns150p383 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 26262941) (BSN.cosOddQ 67108864) 0 2 Ns150p384 Ns150p120 Ns150p383 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz407 := (BSN.cos_quad_nat0 128 rfl)

noncomputable def Ns150p386 := Ns150p316 Bool.true 44598205 47757 Bool.true 26262941 3537118876014220 1 Bool.false 62035138 Bool.false Bool.true 22665471 53203 BSN.abs_quadSignPos qz407 (BSN.sfrac_eq_quadSignPos_mul Bool.false 62035138 67108864) qz51 rfl (Ns150p381 rfl) (Ns150p352 rfl) RS151to168.d42 RS151to168.d44 RS151to168.d17 (Ns150p385 rfl rfl) rfl 

noncomputable def Ns150p387 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz47) qz47 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz47) qz47 8) 22665471 67108864 53203 67108864 22665471 67108864 53203 67108864 3042108021669888 22665471 33554432 53203 33554432 (Ns150p386 rfl rfl rfl rfl) 

noncomputable def Ns150p388 := @Enclosure.Real.IsNear.mulLit_ff qz649 (Zeta.RiemannSiegel.correction qz50) 740791 2097152 1 4194304 31309679364635 35184372088832 41815881296307 1077521395220480000 23193928686207326285 73786976294838206464 

noncomputable abbrev qz651 := (@HPow.hPow Real Real Real qz6 qz49 qz8)

noncomputable def Ns150p389 := @Enclosure.Real.IsNear.mulLit_ff qz48 qz651 1 1 0 1 740791 2097152 1 4194304 740791 2097152 1 4194304 

noncomputable def Ns150p390 := @Enclosure.Real.IsNear.sqrt_image qz49 33674949847 524288000 25223 524288000 33614624 33614650 4194304 (@Enclosure.Real.IsNear.of_eq qz49 (@HMul.hMul Real Real Real qz4 qz47 qz2) Bool.false 33674949847 524288000 25223 524288000 (BSN.t_div_two_pi_mk qz47 403568 1000 qz51) (@Enclosure.Real.IsNear.mulLit_ff qz47 qz2 403568 1000 0 1 1335089 8388608 1 8388608 33674949847 524288000 25223 524288000 (Enclosure.Real.IsNear.const Bool.false 403568 1000) RS151to168.d36 rfl)) 

noncomputable abbrev qz853 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 403568 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz652 := qz853

noncomputable abbrev qz408 := qz652

noncomputable abbrev qz54 := qz408

noncomputable def Ns150p391 := @Enclosure.Real.IsNear.sqrt_image qz54 33614637 4194304 13 4194304 11873918 11873924 4194304 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 67229274 8388608 26 8388608 33614637 4194304 13 4194304 (Ns150p390 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns150p392 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz54) 11873921 4194304 3 4194304 1481581 1481583 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz54) Bool.false 23747842 8388608 6 8388608 11873921 4194304 3 4194304 (Ns150p391 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns150p393 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz54)) Bool.false 2963164 8388608 2 8388608 740791 2097152 1 4194304 (Ns150p392 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz55 := (@HMul.hMul Real Real Real qz340 qz338 qz400)

noncomputable abbrev qz653 := (@HMul.hMul Real Real Real qz839 qz852 qz852)

noncomputable abbrev qz409 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz653 qz648) qz638)

noncomputable abbrev qz56 := (Real.cos (@HMul.hMul Real Real Real qz340 qz338 qz409))

noncomputable def Ns150p394 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz50) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz55)) qz56) Bool.false 31309679364635 

noncomputable def Ns150p395 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz55)) qz56 8422841 8388608 171 

noncomputable def Ns150p396 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz55)) Bool.false 8422841 8388608 171 8388608 8422841 8388608 171 

noncomputable def Ns150p397 := @Enclosure.Real.IsNear.recentre' (Real.cos qz55) Bool.false 4177257 4194304 82457152 4110417920000 4177257 4194304 1288393 64225280000 

noncomputable def Ns150p398 := @Enclosure.Real.IsNear.cos_image qz55 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 378279) qz359) Bool.false 378279 4194304 41 2097152 Bool.false 4177257 4194304 1 

noncomputable def Ns150p399 := nat_lit 350818980318089747929307931 

noncomputable def Ns150p400 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz50 884279719003555 140737488355328 1 500000000000000 60205 4194304 13 4194304 53238060482609028775 590295810358705651712 Ns150p399 

noncomputable def Ns150p401 := @Enclosure.Real.IsNear.subLit_ff_p qz54 qz46 33614637 4194304 13 4194304 8 1 0 1 60205 60205 4194304 13 

noncomputable abbrev qz410 := (Enclosure.Real.IsNear.const Bool.false 8 1)

noncomputable def Ns150p402 := @Ns150p401 4194304 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 67229274 8388608 26 8388608 33614637 4194304 13 4194304 (Ns150p390 rfl rfl rfl rfl rfl rfl) rfl) qz410 

noncomputable def Ns150p403 := @Enclosure.Real.IsNear.recentre' qz55 Bool.false 53238060482609028775 590295810358705651712 Ns150p399 Ns150p151 378279 4194304 41 2097152 (@Ns150p400 Ns150p151 RS151to168.d35 (Ns150p402 rfl rfl) rfl) 

noncomputable def Ns150p404 := nat_lit 7427640235712281649394745344 

noncomputable def Ns150p405 := nat_lit 111414603535684224740921180160 

noncomputable def Ns150p406 := BSN.cos_dyadic_bound_f 378279 4194304 2 1 4194304 1960000 20476179551875793389281 Ns150p404 20476179551875793389281 20476179551875793389281 Ns150p405 20476179551875793389281 4177257 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 378279) (BSN.cosEvenQ 4194304) 0 1 20476179551875793389281 Ns150p404 20476179551875793389281 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 378279) (BSN.cosOddQ 4194304) 0 1 20476179551875793389281 Ns150p405 20476179551875793389281 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p407 := @Enclosure.Real.IsNear.inv_image (Real.cos qz55) 4177257 4194304 1288393 64225280000 4211335 4211506 4194304 (Ns150p397 (@Ns150p398 1960000 (Ns150p403 rfl) (Enclosure.sfrac_false_div 378279 4194304) (Ns150p406 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns150p408 := @Enclosure.Real.IsNear.recentre' qz56 Bool.false 3717235 4194304 

noncomputable abbrev qz57 := (@HMul.hMul Real Real Real qz340 qz338 qz409)

noncomputable def Ns150p409 := @Enclosure.Real.IsNear.cos_image qz57 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 4039897)) qz368) Bool.true 4039897 8388608 

noncomputable def Ns150p410 := nat_lit 1192367245853996142030442405 

noncomputable def Ns150p411 := nat_lit 1513688126500281743742734660893149 

noncomputable def Ns150p412 := @Enclosure.Real.IsNear.recentre' qz57 Bool.true Ns150p410 Ns150p268 Ns150p411 

noncomputable abbrev qz58 := qz409

noncomputable def Ns150p413 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz58 884279719003555 140737488355328 1 500000000000000 1348405058071 

noncomputable abbrev qz411 := (@HSub.hSub Real Real Real qz634 qz653 qz648)

noncomputable abbrev qz59 := qz411

noncomputable def Ns150p414 := @Enclosure.Real.IsNear.subLit_tf qz59 qz25 248893430295 17592186044416 56091451 17592186044416 1 16 

noncomputable abbrev qz412 := qz653

noncomputable abbrev qz60 := qz412

noncomputable def Ns150p415 := @Enclosure.Real.IsNear.subLit_ff_n qz60 qz50 3624642025 17592186044416 1565499 17592186044416 60205 4194304 13 4194304 

noncomputable def Ns150p416 := @Enclosure.Real.IsNear.mulLit_ff qz50 qz50 60205 4194304 13 4194304 60205 4194304 13 4194304 3624642025 17592186044416 

noncomputable def Ns150p417 := nat_lit 266367460622149468044230881 

noncomputable def Ns150p418 := BSN.cos_dyadic_bound_f 4039897 8388608 2 1 4194304 1960000 Ns150p417 Ns150p175 Ns150p417 Ns150p417 Ns150p176 Ns150p417 3717235 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 4039897) (BSN.cosEvenQ 8388608) 0 1 Ns150p417 Ns150p175 Ns150p417 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 4039897) (BSN.cosOddQ 8388608) 0 1 Ns150p417 Ns150p176 Ns150p417 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p419 := @Ns150p408 339628608 16441671680000 3717235 4194304 5306697 256901120000 (@Ns150p409 169 8388608 Bool.false 3717235 4194304 1 1960000 (@Ns150p412 Ns150p169 4039897 8388608 169 8388608 (@Ns150p413 17592186044416 56091451 17592186044416 Ns150p410 Ns150p268 Ns150p411 Ns150p169 RS151to168.d35 (@Ns150p414 0 1 21574480929136 1348405058071 17592186044416 56091451 17592186044416 (@Ns150p415 1043934710260039680 248893430295 17592186044416 56091451 17592186044416 (@Ns150p416 1565499 17592186044416 (Ns150p402 rfl rfl) (Ns150p402 rfl rfl) rfl) (Ns150p402 rfl rfl) rfl rfl) qz373 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 4039897 8388608) (BSN.cos_neg_of_bound 4039897 8388608 Bool.false 3717235 4194304 1 1960000 (Ns150p418 rfl rfl)) rfl rfl) 

noncomputable abbrev qz61 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 8) (Enclosure.sfrac Bool.false 1 1) Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 8 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1))

noncomputable def Ns150p420 := @Ns150p388 7864069723646045107 564931537257355018240000 (Ns150p389 qz61 (@Enclosure.Real.IsNear.of_eq qz651 (@Inv.inv Real Real.instInv (Real.sqrt qz54)) Bool.false 740791 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz49 (BSN.t_div_two_pi_nonneg qz47 403568 1000 qz51)) Ns150p393) rfl) (@Ns150p394 35184372088832 41815881296307 1077521395220480000 (BSN.correction_mk qz50 (BSN.cos_two_pi_p_ne_zero_mk qz47 403568 1000 8 qz51 rfl rfl (@BSN.floor_sqrt_eq_dec qz47 403568 1000 8 qz51 rfl rfl rfl))) (@Ns150p395 8388608 3717235 4194304 5306697 256901120000 31309679364635 35184372088832 41815881296307 1077521395220480000 (@Ns150p396 8388608 (Ns150p407 rfl rfl rfl rfl rfl) rfl) (Ns150p419 rfl) rfl)) 

noncomputable def Ns150p421 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz47) (hardyZApproximantRS₀ qz47) Bool.true 73035826513246771277 73786976294838206464 903604238316071005107 564931537257355018240000 (@Eq.refl Real (hardyZApproximantRS₀ qz47)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz47) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz47) qz47 8) (@HMul.hMul Real Real Real qz4 qz649 (Zeta.RiemannSiegel.correction qz50))) Bool.true 73035826513246771277 73786976294838206464 903604238316071005107 564931537257355018240000 (BSN.hardyZApproximantRS₀_eq qz47 8 (@BSN.floor_sqrt_eq_dec qz47 403568 1000 8 qz51 rfl rfl rfl)) (@Ns150p315 73035826513246771277 73786976294838206464 903604238316071005107 564931537257355018240000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz47) qz47 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz47) qz47 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz47) qz47 8)) Bool.true 22665471 33554432 53203 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz47) qz47 8) (Ns150p387 (Ns150p386 rfl rfl rfl rfl) rfl rfl)) (Ns150p420 rfl) rfl rfl)) 

theorem RS151to168.d45 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz47) Bool.true 73035826513246771277 73786976294838206464 903604238316071005107 564931537257355018240000 := Ns150p421 

noncomputable def Ns150p422 := nat_lit 2259726149029420072960000 

noncomputable def Ns150p423 := nat_lit 52067680913122262696067072 

noncomputable abbrev qz854 := (Enclosure.sfrac Bool.false 405077 1000)

noncomputable abbrev qz654 := qz854

noncomputable abbrev qz413 := qz654

noncomputable abbrev qz62 := qz413

noncomputable abbrev qz855 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 405077 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz655 := qz855

noncomputable abbrev qz414 := qz655

noncomputable abbrev qz63 := qz414

noncomputable abbrev qz856 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 405077 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz656 := qz856

noncomputable abbrev qz415 := qz656

noncomputable abbrev qz64 := qz415

noncomputable abbrev qz657 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz63 qz8))

noncomputable def Ns150p424 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 8) (@HMul.hMul Real Real Real qz4 qz657 (Zeta.RiemannSiegel.correction qz64)) 15776259 33554432 53403 33554432 2784807240773922975 9223372036854775808 31694027973904147683 Ns150p422 Ns150p423 

noncomputable def Ns150p425 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos BSN.quadSignPos 7 8 405077 1000 128 67108864 33554432 1125899906842624 Bool.false 43009048958 1253 139548959 35 23726568 8 

noncomputable def Ns150p426 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 405077 1000 54 93 67108864 33554432 1125899906842624 Bool.false 43009048958 1253 

noncomputable def Ns150p427 := Ns150p426 120242927 35 27397080 8 130587807 35 25364760 8 Bool.false 45345760 35785 Bool.true 6219900 Bool.true 85532930 3537118876014220 1 Bool.false 66820828 Bool.true Bool.false 64185341 Bool.true Bool.true 6193503 

noncomputable def Ns150p428 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 405077 1000 50 7 67108864 33554432 1125899906842624 Bool.false 43009048958 1253 

noncomputable def Ns150p429 := Ns150p428 93032624 35 33554424 8 108007536 35 30011992 8 Bool.false 67009688 21148 Bool.false 52954872 Bool.true 4419202 3537118876014220 1 Bool.false 47277664 Bool.true Bool.false 4416008 Bool.false Bool.false 45345760 

noncomputable def Ns150p430 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 405077 1000 229 124 67108864 33554432 1125899906842624 Bool.false 43009048958 1253 

noncomputable def Ns150p431 := Ns150p430 46516304 35 47453136 16 73726608 35 38745320 8 Bool.false 67108856 1299 Bool.false 26476314 Bool.false 72715492 3537118876014220 1 Bool.false 25794790 Bool.true Bool.false 31420277 Bool.false Bool.false 67009688 

noncomputable def Ns150p432 := nat_lit 459060284994484322963278817474311793653101216302735548109 

noncomputable def Ns150p433 := nat_lit 716291454460516064518257505650735916147336946909184000 

noncomputable def Ns150p434 := nat_lit 5235170594954575419841140395360000 

noncomputable def Ns150p435 := nat_lit 12723892241348907541689383749363456320 

noncomputable abbrev qz416 := (@Eq.refl Real qz654)

noncomputable abbrev qz65 := qz416

noncomputable def Ns150p436 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz62 405077 1000 656350503716 16000000 810154 4000 2000 Ns150p434 Ns150p435 qz65 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns150p437 := nat_lit 146899291198234983348249221591779773968992389216875375394880 

noncomputable abbrev qz417 := (Real.log (Enclosure.sfrac Bool.false 656350503716 16000000))

noncomputable abbrev qz418 := (Enclosure.sfrac Bool.false 405077 2000)

noncomputable abbrev qz66 := (@HSub.hSub Real Real Real qz344 (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 405077 4000) qz417) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 810154)))))) qz418)

noncomputable abbrev qz419 := (@HSub.hSub Real Real Real qz11 qz66 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 405077 2000) (Real.log Real.pi)))

noncomputable def Ns150p438 := @Enclosure.Real.IsNear.addLit_ft_p qz419 (Enclosure.sfrac Bool.true Ns150p434 Ns150p435) 11545161081237747980909 18014398509481984000 26748518769670027 1433600000000000000000 Ns150p434 Ns150p435 0 1 Ns150p437 

noncomputable def Ns150p439 := nat_lit 774782644858876980917096677376000 

noncomputable abbrev qz420 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 405077 2000) (Real.log Real.pi))

noncomputable def Ns150p440 := @Enclosure.Real.IsNear.subLit_ff_p qz66 qz420 15721833122077378796141 18014398509481984000 36881883507317 5600000000000000000 15559315833597 67108864000 405077 33554432000 Ns150p439 11545161081237747980909 18014398509481984000 

noncomputable def Ns150p441 := nat_lit 1257746649766190303691280 

noncomputable abbrev qz67 := (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 405077 4000) qz417) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 810154))))))

noncomputable def Ns150p442 := @Enclosure.Real.IsNear.subLit_ff_p qz67 qz418 774817694983603824501 720575940379279360 36881883507317 5600000000000000000 405077 2000 0 1 Ns150p441 15721833122077378796141 18014398509481984000 36881883507317 5600000000000000000 

noncomputable def Ns150p443 := nat_lit 1744734341204112405929561171844661248 

noncomputable def Ns150p444 := nat_lit 12841042606252579042099200 

noncomputable def Ns150p445 := nat_lit 284374699221139408525669044975387037517935157580666019387316797900520263680 

noncomputable def Ns150p446 := nat_lit 1195011086895178366285817093445560502045454926298515636628315975198273536 

noncomputable def Ns150p447 := nat_lit 79573492314103494084240317443450684170026627140544829628903091466240 

noncomputable def Ns150p448 := BSN.log_dyadic_bound 132062503716 1180638503716 4 3 Ns150p445 33554432 15680000 Ns150p446 Ns150p447 7538130 1312701007432 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 132062503716) (BSN.artanhQ 1180638503716) 0 3 Ns150p446 Ns150p445 Ns150p447 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns150p449 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 405077 4000) qz417 405077 4000 0 1 47836611443208825 4503599627370496 625000147 9800000000000000 775100442143228048181 720575940379279360 253173184546319 39200000000000000000 (Enclosure.Real.IsNear.const Bool.false 405077 4000) (BSN.isNear_log_sfrac 656350503716 16000000 47836611443208825 4503599627370496 625000147 9800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 656350503716) qz352)) Bool.false Ns150p444 Ns150p86 1000000235200000 15680000000000000000000 47836611443208825 4503599627370496 625000147 9800000000000000 (BSN.log_rat_reduce_isNear 656350503716 16000000 15 1312701007432 1048576000000 7538130 33554432 24973259072661432 36028797018963968 15680000 1000000000000000 rfl rfl rfl rfl (Ns150p448 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns150p450 := BSN.arctan_dyadic_bound_f 1000 810154 1 0 4194304 1960000 0 1 1 0 1 1 5177 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 810154) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 810154) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz421 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 810154)))

noncomputable def Ns150p451 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz421 884279719003555 562949953421312 1 2000000000000000 5177 4194304 1 1960000 3706023570626624618496 883584873825699 562949953421312 50000000049 98000000000000000 qz16 (Ns150p450 rfl) rfl rfl 

noncomputable def Ns150p452 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 405077 4000) qz417) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz421)) 775100442143228048181 720575940379279360 253173184546319 39200000000000000000 883584873825699 2251799813685248 50000000049 392000000000000000 Ns150p443 774817694983603824501 720575940379279360 36881883507317 5600000000000000000 (Ns150p449 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz421) 1 4 0 1 883584873825699 562949953421312 50000000049 98000000000000000 883584873825699 2251799813685248 50000000049 392000000000000000 qz355 Ns150p451 rfl) 

noncomputable def Ns150p453 := @Ns150p438 Ns150p432 Ns150p433 26748518769670027 1433600000000000000000 (@Ns150p440 26748518769670027 1433600000000000000000 (Ns150p442 (Ns150p452 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 405077 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz418 (Real.log Real.pi) 405077 2000 0 1 38410761 33554432 1 16777216 15559315833597 67108864000 405077 33554432000 (Enclosure.Real.IsNear.const Bool.false 405077 2000) RS151to168.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns150p434 Ns150p435) 

noncomputable def Ns150p454 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns150p432 Ns150p433 26748518769670027 1433600000000000000000 5376131119 8388608 79 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz356 qz419 (Enclosure.sfrac Bool.true Ns150p434 Ns150p435)) Bool.false Ns150p432 Ns150p433 26748518769670027 1433600000000000000000 Ns150p436 (Ns150p453 rfl rfl)) 

noncomputable def Ns150p455 := nat_lit 1898818950151614956044288 

noncomputable def Ns150p456 := nat_lit 139942426367639512783019836960272425419253830011808323845732228021578011261225841205185 

noncomputable def Ns150p457 := nat_lit 281080070728686937184341720516576137827267442085796471667875528590095860986622255041 

noncomputable def Ns150p458 := nat_lit 366060796562637992723896353062734276636801597981835272927550703486415588575898862362561 

noncomputable def Ns150p459 := BSN.sin_dyadic_bound_f 26983840231 17179869184 3 2 8388608 3923829 Ns150p456 Ns150p98 Ns150p457 Ns150p458 Ns150p101 Ns150p457 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26983840231) qz357 0 2 Ns150p456 Ns150p98 Ns150p457 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26983840231) qz358 0 2 Ns150p458 Ns150p101 Ns150p457 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p460 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz62) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5376131119) qz368) Bool.false 5376131119 8388608 79 4194304 Bool.false 8388607 8388608 1 1960000 (Ns150p454 rfl) (Enclosure.sfrac_false_div 5376131119 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5376131119) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns150p455) qz369) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 101 1000000000000000 3920000 1960000 (BSN.sin_reduce_arg_pos_rat_q3 5376131119 8388608 226375608064910080 72057594037927936 101 Ns150p455 Ns150p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns150p455 Ns150p86 26983840231 17179869184 3923829 3920000 (Ns150p459 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns150p461 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns150p432 Ns150p433 26748518769670027 1433600000000000000000 43009048958 67108864 1253 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz356 qz419 (Enclosure.sfrac Bool.true Ns150p434 Ns150p435)) Bool.false Ns150p432 Ns150p433 26748518769670027 1433600000000000000000 Ns150p436 (Ns150p453 rfl rfl)) 

noncomputable def Ns150p462 := Ns150p431 21148 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 229 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 25794790 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 124 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 31420277 67108864) qz65 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) Bool.false 8388607 8388608 2484911 128450560000 67108856 67108864 1299 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.false 8388607 8388608 2484911 128450560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz62) qz62) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.false 8388607 8388608 159034304 8220835840000 8388607 8388608 2484911 128450560000 (Ns150p460 rfl rfl) rfl)) rfl) (Ns150p461 rfl) RS151to168.d7 

noncomputable def Ns150p463 := nat_lit 491394274666298545838683347216 

noncomputable def Ns150p464 := BSN.sin_dyadic_bound_f 26476314 67108864 2 1 67108864 33554432 Ns150p463 Ns150p107 Ns150p463 Ns150p463 Ns150p108 Ns150p463 25794790 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 26476314) qz361 0 1 Ns150p463 Ns150p107 Ns150p463 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 26476314) (BSN.sinOddQ 67108864) 0 1 Ns150p463 Ns150p108 Ns150p463 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p465 := nat_lit 953438777819247384762128617794981660434533926384009614605324189696 

noncomputable def Ns150p466 := nat_lit 781655837412664734665980464218980652839263866730039261454729216 

noncomputable def Ns150p467 := nat_lit 2858753021782916824817053892456507019997923251418568765293063110656 

noncomputable def Ns150p468 := BSN.cos_dyadic_bound_f 72715492 67108864 3 2 67108864 33554432 Ns150p465 Ns150p117 Ns150p466 Ns150p467 Ns150p120 Ns150p466 31420277 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 72715492) qz362 0 2 Ns150p465 Ns150p117 Ns150p466 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 72715492) (BSN.cosOddQ 67108864) 0 2 Ns150p467 Ns150p120 Ns150p466 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p469 := nat_lit 268011071725045014994914018699358204882845182733152642775662985216 

noncomputable def Ns150p470 := nat_lit 61836853225567982784055177829595049020639077270831546222247936 

noncomputable def Ns150p471 := nat_lit 803909541468683909019173945742415424550494270044916265234544459776 

noncomputable def Ns150p472 := BSN.cos_dyadic_bound_f 52954872 67108864 3 2 67108864 33554432 Ns150p469 Ns150p117 Ns150p470 Ns150p471 Ns150p120 Ns150p470 47277664 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 52954872) qz362 0 2 Ns150p469 Ns150p117 Ns150p470 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 52954872) (BSN.cosOddQ 67108864) 0 2 Ns150p471 Ns150p120 Ns150p470 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p473 := nat_lit 381395367561665960732774416 

noncomputable def Ns150p474 := BSN.sin_dyadic_bound_f 4419202 67108864 2 1 67108864 33554432 Ns150p473 Ns150p107 Ns150p473 Ns150p473 Ns150p108 Ns150p473 4416008 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 4419202) qz361 0 1 Ns150p473 Ns150p107 Ns150p473 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 4419202) (BSN.sinOddQ 67108864) 0 1 Ns150p473 Ns150p108 Ns150p473 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p475 := Ns150p429 35785 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 50 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 47277664 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 7 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 4416008 67108864) qz65 rfl rfl (Ns150p462 RS151to168.d9 RS151to168.d11 RS151to168.d13 RS151to168.d17 (Ns150p464 rfl rfl) (Ns150p468 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns150p461 rfl) RS151to168.d19 RS151to168.d21 RS151to168.d23 RS151to168.d25 RS151to168.d17 (Ns150p472 rfl rfl) (Ns150p474 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns150p476 := nat_lit 1496696040142079120100000000 

noncomputable def Ns150p477 := BSN.cos_dyadic_bound_f 6219900 67108864 2 1 67108864 33554432 Ns150p476 Ns150p134 Ns150p476 Ns150p476 Ns150p135 Ns150p476 66820828 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 6219900) qz362 0 1 Ns150p476 Ns150p134 Ns150p476 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 6219900) (BSN.cosOddQ 67108864) 0 1 Ns150p476 Ns150p135 Ns150p476 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p478 := nat_lit 3285591363580345235638460573952110162675932003630284233278855840000 

noncomputable def Ns150p479 := nat_lit 2864618518724825258175823964150240175743295589551210960100000000 

noncomputable def Ns150p480 := nat_lit 8600482284156302090539873978694521465771475626172423412271127200000 

noncomputable def Ns150p481 := BSN.sin_dyadic_bound_f 85532930 67108864 3 2 67108864 33554432 Ns150p478 Ns150p359 Ns150p479 Ns150p480 Ns150p362 Ns150p479 64185341 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 85532930) qz361 0 2 Ns150p478 Ns150p359 Ns150p479 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 85532930) (BSN.sinOddQ 67108864) 0 2 Ns150p480 Ns150p362 Ns150p479 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p482 := Ns150p427 47937 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 54 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66820828 67108864) BSN.abs_quadSignNeg qz650 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 64185341 67108864) qz65 rfl rfl (Ns150p475 rfl rfl) (Ns150p461 rfl) RS151to168.d27 RS151to168.d29 RS151to168.d31 RS151to168.d33 RS151to168.d17 (Ns150p477 rfl rfl) (Ns150p481 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns150p483 := nat_lit 15540298726848329415204951789219542648637643672471524886604718336 

noncomputable def Ns150p484 := nat_lit 207993344706161884178785487134559847373686704707913458688256 

noncomputable def Ns150p485 := nat_lit 46620480193855575921846497796684358826218183644005158832896778496 

noncomputable def Ns150p486 := BSN.cos_dyadic_bound_f 25987002 67108864 3 2 67108864 33554432 Ns150p483 Ns150p117 Ns150p484 Ns150p485 Ns150p120 Ns150p484 62139867 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 25987002) qz362 0 2 Ns150p483 Ns150p117 Ns150p484 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 25987002) (BSN.cosOddQ 67108864) 0 2 Ns150p485 Ns150p120 Ns150p484 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p487 := Ns150p425 Bool.true 6193503 47937 Bool.true 25987002 3537118876014220 1 Bool.false 62139867 Bool.false Bool.false 15776259 53403 BSN.abs_quadSignPos qz407 (BSN.sfrac_eq_quadSignPos_mul Bool.false 62139867 67108864) qz65 rfl (Ns150p482 rfl) (Ns150p461 rfl) RS151to168.d42 RS151to168.d44 RS151to168.d17 (Ns150p486 rfl rfl) rfl 

noncomputable def Ns150p488 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 8) 15776259 67108864 53403 67108864 15776259 67108864 53403 67108864 2117453639319552 15776259 33554432 53403 33554432 (Ns150p487 rfl rfl rfl rfl) 

noncomputable def Ns150p489 := @Enclosure.Real.IsNear.mulLit_ff qz657 (Zeta.RiemannSiegel.correction qz64) 185025 524288 1 4194304 15050978196319 17592186044416 5275143674177 134690174402560000 2784807240773922975 9223372036854775808 

noncomputable abbrev qz658 := (@HPow.hPow Real Real Real qz6 qz63 qz8)

noncomputable def Ns150p490 := @Enclosure.Real.IsNear.mulLit_ff qz48 qz658 1 1 0 1 185025 524288 1 4194304 185025 524288 1 4194304 

noncomputable def Ns150p491 := @Enclosure.Real.IsNear.sqrt_image qz63 540813846853 8388608000 405077 8388608000 33677410 33677436 4194304 (@Enclosure.Real.IsNear.of_eq qz63 (@HMul.hMul Real Real Real qz4 qz62 qz2) Bool.false 540813846853 8388608000 405077 8388608000 (BSN.t_div_two_pi_mk qz62 405077 1000 qz65) (@Enclosure.Real.IsNear.mulLit_ff qz62 qz2 405077 1000 0 1 1335089 8388608 1 8388608 540813846853 8388608000 405077 8388608000 (Enclosure.Real.IsNear.const Bool.false 405077 1000) RS151to168.d36 rfl)) 

noncomputable abbrev qz857 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 405077 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz659 := qz857

noncomputable abbrev qz422 := qz659

noncomputable abbrev qz68 := qz422

noncomputable def Ns150p492 := @Enclosure.Real.IsNear.sqrt_image qz68 33677423 4194304 13 4194304 11885002 11885008 4194304 (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 67354846 8388608 26 8388608 33677423 4194304 13 4194304 (Ns150p491 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns150p493 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz68) 11885005 4194304 3 4194304 1480199 1480201 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz68) Bool.false 23770010 8388608 6 8388608 11885005 4194304 3 4194304 (Ns150p492 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns150p494 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz68)) Bool.false 2960400 8388608 2 8388608 185025 524288 1 4194304 (Ns150p493 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz69 := (@HMul.hMul Real Real Real qz340 qz338 qz415)

noncomputable abbrev qz660 := (@HMul.hMul Real Real Real qz839 qz856 qz856)

noncomputable abbrev qz423 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz660 qz656) qz638)

noncomputable abbrev qz70 := (Real.cos (@HMul.hMul Real Real Real qz340 qz338 qz423))

noncomputable def Ns150p495 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz64) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz69)) qz70) Bool.false 15050978196319 

noncomputable def Ns150p496 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz69)) qz70 8533031 8388608 175 

noncomputable def Ns150p497 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz69)) Bool.false 8533031 8388608 175 8388608 8533031 8388608 175 

noncomputable def Ns150p498 := @Enclosure.Real.IsNear.recentre' (Real.cos qz69) Bool.false 4123315 4194304 82457152 4110417920000 4123315 4194304 1288393 64225280000 

noncomputable def Ns150p499 := @Enclosure.Real.IsNear.cos_image qz69 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 772775) qz359) Bool.false 772775 4194304 41 2097152 Bool.false 4123315 4194304 1 

noncomputable def Ns150p500 := nat_lit 350818980318629075562601243 

noncomputable def Ns150p501 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz64 884279719003555 140737488355328 1 500000000000000 122991 4194304 13 4194304 108758446919966233005 590295810358705651712 Ns150p500 

noncomputable def Ns150p502 := @Enclosure.Real.IsNear.subLit_ff_p qz68 qz46 33677423 4194304 13 4194304 8 1 0 1 122991 122991 4194304 13 

noncomputable def Ns150p503 := @Ns150p502 4194304 (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 67354846 8388608 26 8388608 33677423 4194304 13 4194304 (Ns150p491 rfl rfl rfl rfl rfl rfl) rfl) qz410 

noncomputable def Ns150p504 := @Enclosure.Real.IsNear.recentre' qz69 Bool.false 108758446919966233005 590295810358705651712 Ns150p500 Ns150p151 772775 4194304 41 2097152 (@Ns150p501 Ns150p151 RS151to168.d35 (Ns150p503 rfl rfl) rfl) 

noncomputable def Ns150p505 := BSN.cos_dyadic_bound_f 772775 4194304 2 1 4194304 1960000 356625386379916500390625 Ns150p404 356625386379916500390625 356625386379916500390625 Ns150p405 356625386379916500390625 4123315 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 772775) (BSN.cosEvenQ 4194304) 0 1 356625386379916500390625 Ns150p404 356625386379916500390625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 772775) (BSN.cosOddQ 4194304) 0 1 356625386379916500390625 Ns150p405 356625386379916500390625 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p506 := @Enclosure.Real.IsNear.inv_image (Real.cos qz69) 4123315 4194304 1288393 64225280000 4266428 4266603 4194304 (Ns150p498 (@Ns150p499 1960000 (Ns150p504 rfl) (Enclosure.sfrac_false_div 772775 4194304) (Ns150p505 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns150p507 := @Enclosure.Real.IsNear.recentre' qz70 Bool.false 3527698 4194304 

noncomputable abbrev qz71 := (@HMul.hMul Real Real Real qz340 qz338 qz423)

noncomputable def Ns150p508 := @Enclosure.Real.IsNear.cos_image qz71 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 1198607)) qz386) Bool.true 1198607 2097152 

noncomputable def Ns150p509 := nat_lit 1415065512055971122775029245 

noncomputable def Ns150p510 := nat_lit 1557741167498883270513912738816457 

noncomputable def Ns150p511 := @Enclosure.Real.IsNear.recentre' qz71 Bool.true Ns150p509 Ns150p268 Ns150p510 

noncomputable abbrev qz72 := qz423

noncomputable def Ns150p512 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz72 884279719003555 140737488355328 1 500000000000000 1600246484959 

noncomputable abbrev qz424 := (@HSub.hSub Real Real Real qz634 qz660 qz656)

noncomputable abbrev qz73 := qz424

noncomputable def Ns150p513 := @Enclosure.Real.IsNear.subLit_tf qz73 qz25 500734857183 17592186044416 57723887 17592186044416 1 16 

noncomputable abbrev qz425 := qz660

noncomputable abbrev qz74 := qz425

noncomputable def Ns150p514 := @Enclosure.Real.IsNear.subLit_ff_n qz74 qz64 15126786081 17592186044416 3197935 17592186044416 122991 4194304 13 4194304 

noncomputable def Ns150p515 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz64 122991 4194304 13 4194304 122991 4194304 13 4194304 15126786081 17592186044416 

noncomputable def Ns150p516 := nat_lit 67075472360378328742060239039821346162462725997022081 

noncomputable def Ns150p517 := nat_lit 15085502980398593449464978548510856026246963233994833920 

noncomputable def Ns150p518 := nat_lit 4260047853243154543726583070792844437528604003201 

noncomputable def Ns150p519 := nat_lit 201217896985428499917093263953322452798513120783059841 

noncomputable def Ns150p520 := nat_lit 678847634117936705225924034682988521181113345529767526400 

noncomputable def Ns150p521 := BSN.cos_dyadic_bound_f 1198607 2097152 3 2 4194304 1960000 Ns150p516 Ns150p517 Ns150p518 Ns150p519 Ns150p520 Ns150p518 3527698 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1198607) (BSN.cosEvenQ 2097152) 0 2 Ns150p516 Ns150p517 Ns150p518 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1198607) (BSN.cosOddQ 2097152) 0 2 Ns150p519 Ns150p520 Ns150p518 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p522 := @Ns150p507 174714304 8220835840000 1763849 2097152 2729911 128450560000 (@Ns150p508 87 4194304 Bool.false 3527698 4194304 1 1960000 (@Ns150p511 Ns150p169 1198607 2097152 87 4194304 (@Ns150p512 17592186044416 57723887 17592186044416 Ns150p509 Ns150p268 Ns150p510 Ns150p169 RS151to168.d35 (@Ns150p513 0 1 25603943759344 1600246484959 17592186044416 57723887 17592186044416 (@Ns150p514 2100234214422085632 500734857183 17592186044416 57723887 17592186044416 (@Ns150p515 3197935 17592186044416 (Ns150p503 rfl rfl) (Ns150p503 rfl rfl) rfl) (Ns150p503 rfl rfl) rfl rfl) qz373 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 1198607 2097152) (BSN.cos_neg_of_bound 1198607 2097152 Bool.false 3527698 4194304 1 1960000 (Ns150p521 rfl rfl)) rfl rfl) 

noncomputable def Ns150p523 := @Ns150p489 31694027973904147683 Ns150p422 (Ns150p490 qz61 (@Enclosure.Real.IsNear.of_eq qz658 (@Inv.inv Real Real.instInv (Real.sqrt qz68)) Bool.false 185025 524288 1 4194304 (BSN.rpow_neg_quarter_mk qz63 (BSN.t_div_two_pi_nonneg qz62 405077 1000 qz65)) Ns150p494) rfl) (@Ns150p495 17592186044416 5275143674177 134690174402560000 (BSN.correction_mk qz64 (BSN.cos_two_pi_p_ne_zero_mk qz62 405077 1000 8 qz65 rfl rfl (@BSN.floor_sqrt_eq_dec qz62 405077 1000 8 qz65 rfl rfl rfl))) (@Ns150p496 8388608 1763849 2097152 2729911 128450560000 15050978196319 17592186044416 5275143674177 134690174402560000 (@Ns150p497 8388608 (Ns150p506 rfl rfl rfl rfl rfl) rfl) (Ns150p522 rfl) rfl)) 

noncomputable def Ns150p524 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (hardyZApproximantRS₀ qz62) Bool.false 1551737812552519521 9223372036854775808 3628123719783859987683 Ns150p422 (@Eq.refl Real (hardyZApproximantRS₀ qz62)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 8) (@HMul.hMul Real Real Real qz4 qz657 (Zeta.RiemannSiegel.correction qz64))) Bool.false 1551737812552519521 9223372036854775808 3628123719783859987683 Ns150p422 (BSN.hardyZApproximantRS₀_eq qz62 8 (@BSN.floor_sqrt_eq_dec qz62 405077 1000 8 qz65 rfl rfl rfl)) (@Ns150p424 1551737812552519521 9223372036854775808 3628123719783859987683 Ns150p422 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 8)) Bool.false 15776259 33554432 53403 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz62) qz62 8) (Ns150p488 (Ns150p487 rfl rfl rfl rfl) rfl rfl)) (Ns150p523 rfl) rfl rfl)) 

theorem RS151to168.d46 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz62) Bool.false 1551737812552519521 9223372036854775808 3628123719783859987683 Ns150p422 := Ns150p524 

noncomputable def Ns150p525 := nat_lit 1597866308562758771532627968 

noncomputable abbrev qz858 := (Enclosure.sfrac Bool.false 406585 1000)

noncomputable abbrev qz661 := qz858

noncomputable abbrev qz426 := qz661

noncomputable abbrev qz75 := qz426

noncomputable abbrev qz859 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 406585 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz662 := qz859

noncomputable abbrev qz427 := qz662

noncomputable abbrev qz76 := qz427

noncomputable abbrev qz860 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 406585 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz663 := qz860

noncomputable abbrev qz428 := qz663

noncomputable abbrev qz77 := qz428

noncomputable abbrev qz664 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz76 qz8))

noncomputable def Ns150p526 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz75) qz75 8) (@HMul.hMul Real Real Real qz4 qz664 (Zeta.RiemannSiegel.correction qz77)) 163509961 33554432 53593 33554432 2674851016048902765 9223372036854775808 9567818252245453731 645636042579834306560000 Ns150p525 

noncomputable def Ns150p527 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz75) qz75 Real.cos BSN.quadSignPos 7 8 406585 1000 128 67108864 33554432 1125899906842624 Bool.false 43219953043 1257 139548959 35 23726568 8 

noncomputable def Ns150p528 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz75) qz75 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 406585 1000 53 93 67108864 33554432 1125899906842624 Bool.false 43219953043 1257 

noncomputable def Ns150p529 := Ns150p528 120242927 35 27397080 8 130587807 35 25364760 8 Bool.true 137582691 35911 Bool.true 82056506 Bool.true 71555258 3537118876014220 1 Bool.false 63084779 Bool.true Bool.false 58746897 Bool.true Bool.true 185541180 

noncomputable def Ns150p530 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz75) qz75 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 406585 1000 51 6 67108864 33554432 1125899906842624 Bool.false 43219953043 1257 

noncomputable def Ns150p531 := Ns150p530 93032624 35 33554424 8 108007536 35 30011992 8 Bool.true 128389288 21221 Bool.false 18151403 Bool.true 61804839 3537118876014220 1 Bool.false 17930891 Bool.false Bool.false 40604420 Bool.true Bool.true 137582691 

noncomputable def Ns150p532 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz75) qz75 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 406585 1000 230 125 67108864 33554432 1125899906842624 Bool.false 43219953043 1257 

noncomputable def Ns150p533 := Ns150p532 46516304 35 47453136 16 73726608 35 38745320 8 Bool.true 67108824 1299 Bool.false 61819455 Bool.false 67025495 3537118876014220 1 Bool.false 40592782 Bool.true Bool.false 56425073 Bool.true Bool.true 128389288 

noncomputable def Ns150p534 := nat_lit 6037911354613682272306324425508462365251559907430909 

noncomputable def Ns150p535 := nat_lit 9375238597247397664186546742554043036648393932800 

noncomputable def Ns150p536 := nat_lit 5333344814228925165103535500000000 

noncomputable def Ns150p537 := nat_lit 13010757190023144547456261297605000000 

noncomputable abbrev qz429 := (@Eq.refl Real qz661)

noncomputable abbrev qz78 := qz429

noncomputable def Ns150p538 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz75 406585 1000 661246448900 16000000 813170 4000 2000 Ns150p536 Ns150p537 qz78 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns150p539 := nat_lit 30189556773068411361531622127542311826257799537154545000000 

noncomputable abbrev qz430 := (Enclosure.sfrac Bool.false 406585 2000)

noncomputable abbrev qz665 := (Real.log (Enclosure.sfrac Bool.false 661246448900 16000000))

noncomputable abbrev qz79 := (@HSub.hSub Real Real Real qz344 (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 406585 4000) qz665) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 813170)))))) qz430)

noncomputable abbrev qz431 := (@HSub.hSub Real Real Real qz11 qz79 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 406585 2000) (Real.log Real.pi)))

noncomputable def Ns150p540 := @Enclosure.Real.IsNear.addLit_ft_p qz431 (Enclosure.sfrac Bool.true Ns150p536 Ns150p537) 2320355037569837408829 3602879701896396800 37586382484200349 2007040000000000000000 Ns150p536 Ns150p537 0 1 Ns150p539 

noncomputable def Ns150p541 := nat_lit 31143278129597821834243552051200 

noncomputable abbrev qz432 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 406585 2000) (Real.log Real.pi))

noncomputable def Ns150p542 := @Enclosure.Real.IsNear.subLit_ff_p qz79 qz432 3158799186077297123901 3602879701896396800 51823136954579 7840000000000000000 3123447852237 13421772800 81317 6710886400 Ns150p541 2320355037569837408829 3602879701896396800 

noncomputable def Ns150p543 := nat_lit 1263519674430918849560400 

noncomputable abbrev qz80 := (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 406585 4000) qz665) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 813170))))))

noncomputable def Ns150p544 := @Enclosure.Real.IsNear.subLit_ff_p qz80 qz430 778247521575014074073 720575940379279360 51823136954579 7840000000000000000 406585 2000 0 1 Ns150p543 3158799186077297123901 3602879701896396800 51823136954579 7840000000000000000 

noncomputable def Ns150p545 := nat_lit 1752457624083622715134184792579375104 

noncomputable def Ns150p546 := nat_lit 12850026927221212991979520 

noncomputable def Ns150p547 := nat_lit 291524035812427218566587331291276757356593764242626696225978905000000000000 

noncomputable def Ns150p548 := nat_lit 1307371741608382672082996405726708176951637068164730237863831000000000000 

noncomputable def Ns150p549 := nat_lit 98997501052575825348829185481446624637813550861784968415000000000000 

noncomputable def Ns150p550 := BSN.log_dyadic_bound 136958448900 1185534448900 4 3 Ns150p547 33554432 15680000 Ns150p548 Ns150p549 7787495 1322492897800 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 136958448900) (BSN.artanhQ 1185534448900) 0 3 Ns150p548 Ns150p547 Ns150p549 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns150p551 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 406585 4000) qz665 406585 4000 0 1 47870080646951545 4503599627370496 625000147 9800000000000000 778530269593631756953 720575940379279360 50823136953599 7840000000000000000 (Enclosure.Real.IsNear.const Bool.false 406585 4000) (BSN.isNear_log_sfrac 661246448900 16000000 47870080646951545 4503599627370496 625000147 9800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 661246448900) qz352)) Bool.false Ns150p546 Ns150p86 1000000235200000 15680000000000000000000 47870080646951545 4503599627370496 625000147 9800000000000000 (BSN.log_rat_reduce_isNear 661246448900 16000000 15 1322492897800 1048576000000 7787495 33554432 24973259072661432 36028797018963968 15680000 1000000000000000 rfl rfl rfl rfl (Ns150p550 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns150p552 := BSN.arctan_dyadic_bound_f 1000 813170 1 0 4194304 1960000 0 1 1 0 1 1 5157 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 813170) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 813170) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz433 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 813170)))

noncomputable def Ns150p553 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz433 884279719003555 562949953421312 1 2000000000000000 5157 4194304 1 1960000 3706034829625693044736 883587558180259 562949953421312 50000000049 98000000000000000 qz16 (Ns150p552 rfl) rfl rfl 

noncomputable def Ns150p554 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 406585 4000) qz665) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz433)) 778530269593631756953 720575940379279360 50823136953599 7840000000000000000 883587558180259 2251799813685248 50000000049 392000000000000000 Ns150p545 778247521575014074073 720575940379279360 51823136954579 7840000000000000000 (Ns150p551 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz433) 1 4 0 1 883587558180259 562949953421312 50000000049 98000000000000000 883587558180259 2251799813685248 50000000049 392000000000000000 qz355 Ns150p553 rfl) 

noncomputable def Ns150p555 := @Ns150p540 Ns150p534 Ns150p535 37586382484200349 2007040000000000000000 (@Ns150p542 37586382484200349 2007040000000000000000 (Ns150p544 (Ns150p554 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 406585 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz430 (Real.log Real.pi) 406585 2000 0 1 38410761 33554432 1 16777216 3123447852237 13421772800 81317 6710886400 (Enclosure.Real.IsNear.const Bool.false 406585 2000) RS151to168.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns150p536 Ns150p537) 

noncomputable def Ns150p556 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz75) Bool.false Ns150p534 Ns150p535 37586382484200349 2007040000000000000000 2701247065 4194304 79 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz75) (@HAdd.hAdd Real Real Real qz356 qz431 (Enclosure.sfrac Bool.true Ns150p536 Ns150p537)) Bool.false Ns150p534 Ns150p535 37586382484200349 2007040000000000000000 Ns150p538 (Ns150p555 rfl rfl)) 

noncomputable def Ns150p557 := nat_lit 140343945365535808591224643706538648849470551460623781240025257926772637136711229440000 

noncomputable def Ns150p558 := nat_lit 282692067504276213294096305265735664476148654391583737244611187950886752281600000000 

noncomputable def Ns150p559 := nat_lit 367109784038539241965016958546694794006128156004047339101670114551531661568644915200000 

noncomputable def Ns150p560 := BSN.sin_dyadic_bound_f 27003135940 17179869184 3 2 8388608 3923829 Ns150p557 Ns150p98 Ns150p558 Ns150p559 Ns150p101 Ns150p558 8388603 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 27003135940) qz357 0 2 Ns150p557 Ns150p98 Ns150p558 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 27003135940) qz358 0 2 Ns150p559 Ns150p101 Ns150p558 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p561 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz75) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2701247065) qz359) Bool.false 2701247065 4194304 79 4194304 Bool.true 8388603 8388608 1 1960000 (Ns150p556 rfl) (Enclosure.sfrac_false_div 2701247065 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2701247065) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 950088382513066855628800) qz360) 226375608064910080 72057594037927936 Bool.false 8388603 8388608 102 1000000000000000 3920000 1960000 (BSN.sin_reduce_arg_pos_rat_q1 2701247065 4194304 226375608064910080 72057594037927936 102 950088382513066855628800 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388603 8388608 950088382513066855628800 604462909807314587353088 27003135940 17179869184 3923829 3920000 (Ns150p560 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns150p562 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz75) Bool.false Ns150p534 Ns150p535 37586382484200349 2007040000000000000000 43219953043 67108864 1257 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz75) (@HAdd.hAdd Real Real Real qz356 qz431 (Enclosure.sfrac Bool.true Ns150p536 Ns150p537)) Bool.false Ns150p534 Ns150p535 37586382484200349 2007040000000000000000 Ns150p538 (Ns150p555 rfl rfl)) 

noncomputable def Ns150p563 := Ns150p533 21221 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 230 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 40592782 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 125 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 56425073 67108864) qz78 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz75) qz75 1) Bool.true 8388603 8388608 2484911 128450560000 67108824 67108864 1299 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz75) qz75 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz75)) Bool.true 8388603 8388608 2484911 128450560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz75) qz75) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz75)) Bool.true 8388603 8388608 159034304 8220835840000 8388603 8388608 2484911 128450560000 (Ns150p561 rfl rfl) rfl)) rfl) (Ns150p562 rfl) RS151to168.d7 

noncomputable def Ns150p564 := nat_lit 497869619471782286852501514444378171769089099371680839507017690625 

noncomputable def Ns150p565 := nat_lit 213305167164986795387916842033669626591046520348508114812890625 

noncomputable def Ns150p566 := nat_lit 1493182248081016886966728709649067176054085205074345502291427290625 

noncomputable def Ns150p567 := BSN.cos_dyadic_bound_f 61819455 67108864 3 2 67108864 33554432 Ns150p564 Ns150p117 Ns150p565 Ns150p566 Ns150p120 Ns150p565 40592782 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 61819455) qz362 0 2 Ns150p564 Ns150p117 Ns150p565 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 61819455) (BSN.cosOddQ 67108864) 0 2 Ns150p566 Ns150p120 Ns150p565 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p568 := nat_lit 1238238593802817176743362923509222002196536079560400970171512130625 

noncomputable def Ns150p569 := nat_lit 407305467879144255714909056396058640254317053989923843437890625 

noncomputable def Ns150p570 := nat_lit 3242346393964145419818602565956654482240039885523161711845537090625 

noncomputable def Ns150p571 := BSN.sin_dyadic_bound_f 67025495 67108864 3 2 67108864 33554432 Ns150p568 Ns150p359 Ns150p569 Ns150p570 Ns150p362 Ns150p569 56425073 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 67025495) qz361 0 2 Ns150p568 Ns150p359 Ns150p569 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 67025495) (BSN.sinOddQ 67108864) 0 2 Ns150p570 Ns150p362 Ns150p569 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p572 := nat_lit 108552741648200284499874191281 

noncomputable def Ns150p573 := BSN.sin_dyadic_bound_f 18151403 67108864 2 1 67108864 33554432 Ns150p572 Ns150p107 Ns150p572 Ns150p572 Ns150p108 Ns150p572 17930891 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 18151403) qz361 0 1 Ns150p572 Ns150p107 Ns150p572 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 18151403) (BSN.sinOddQ 67108864) 0 1 Ns150p572 Ns150p108 Ns150p572 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p574 := nat_lit 497398738861532015794409260938654565916440654891903045027406452161 

noncomputable def Ns150p575 := nat_lit 212902046218405527104920351534122696785019359531036251347654081 

noncomputable def Ns150p576 := nat_lit 1491770412492159236329017942112895452355751925956647062579524048321 

noncomputable def Ns150p577 := BSN.cos_dyadic_bound_f 61804839 67108864 3 2 67108864 33554432 Ns150p574 Ns150p117 Ns150p575 Ns150p576 Ns150p120 Ns150p575 40604420 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 61804839) qz362 0 2 Ns150p574 Ns150p117 Ns150p575 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 61804839) (BSN.cosOddQ 67108864) 0 2 Ns150p576 Ns150p120 Ns150p575 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p578 := Ns150p531 35911 BSN.abs_quadSignPos (BSN.cos_quad_nat3 51 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 17930891 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 6 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 40604420 67108864) qz78 rfl rfl (Ns150p563 RS151to168.d9 RS151to168.d11 RS151to168.d13 RS151to168.d17 (Ns150p567 rfl rfl) (Ns150p571 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns150p562 rfl) RS151to168.d19 RS151to168.d21 RS151to168.d23 RS151to168.d25 RS151to168.d17 (Ns150p573 rfl rfl) (Ns150p577 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns150p579 := nat_lit 2782750835593425895414318757813516798044731340449209442380380545280 

noncomputable def Ns150p580 := nat_lit 2055436974784747053888053259917943377449045303572567409796751616 

noncomputable def Ns150p581 := nat_lit 7284829100023606802283587517566962562744140770685002478047040020736 

noncomputable def Ns150p582 := BSN.sin_dyadic_bound_f 82056506 67108864 3 2 67108864 33554432 Ns150p579 Ns150p359 Ns150p580 Ns150p581 Ns150p362 Ns150p580 63084779 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 82056506) qz361 0 2 Ns150p579 Ns150p359 Ns150p580 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 82056506) (BSN.sinOddQ 67108864) 0 2 Ns150p581 Ns150p362 Ns150p580 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p583 := nat_lit 1608618779460516261675065729250866373386141057937787498934437454080 

noncomputable def Ns150p584 := nat_lit 687277957913268826704375034602520229976202199355463882833961216 

noncomputable def Ns150p585 := nat_lit 4211936448559968726286698397981960230877074633895248889017985966336 

noncomputable def Ns150p586 := BSN.sin_dyadic_bound_f 71555258 67108864 3 2 67108864 33554432 Ns150p583 Ns150p359 Ns150p584 Ns150p585 Ns150p362 Ns150p584 58746897 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 71555258) qz361 0 2 Ns150p583 Ns150p359 Ns150p584 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 71555258) (BSN.sinOddQ 67108864) 0 2 Ns150p585 Ns150p362 Ns150p584 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p587 := Ns150p529 48107 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 53 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 63084779 67108864) BSN.abs_quadSignNeg qz650 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 58746897 67108864) qz78 rfl rfl (Ns150p578 rfl rfl) (Ns150p562 rfl) RS151to168.d27 RS151to168.d29 RS151to168.d31 RS151to168.d33 RS151to168.d17 (Ns150p582 rfl rfl) (Ns150p586 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns150p588 := nat_lit 14459187880521988994378282138668517632899602751902654047399119841 

noncomputable def Ns150p589 := nat_lit 180060861475641311396830633186440787404376757621693002222561 

noncomputable def Ns150p590 := nat_lit 43377203519843015700512052754739180017123999502192718756192914401 

noncomputable def Ns150p591 := BSN.cos_dyadic_bound_f 25522747 67108864 3 2 67108864 33554432 Ns150p588 Ns150p117 Ns150p589 Ns150p590 Ns150p120 Ns150p589 62313695 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 25522747) qz362 0 2 Ns150p588 Ns150p117 Ns150p589 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 25522747) (BSN.cosOddQ 67108864) 0 2 Ns150p590 Ns150p120 Ns150p589 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p592 := Ns150p527 Bool.true 185541180 48107 Bool.true 25522747 3537118876014220 1 Bool.false 62313695 Bool.false Bool.true 163509961 53593 BSN.abs_quadSignPos qz407 (BSN.sfrac_eq_quadSignPos_mul Bool.false 62313695 67108864) qz78 rfl (Ns150p587 rfl) (Ns150p562 rfl) RS151to168.d42 RS151to168.d44 RS151to168.d17 (Ns150p591 rfl rfl) rfl 

noncomputable def Ns150p593 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz75) qz75 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz75) qz75 8) 163509961 67108864 53593 67108864 163509961 67108864 53593 67108864 21945935470788608 163509961 33554432 53593 33554432 (Ns150p592 rfl rfl rfl rfl) 

noncomputable def Ns150p594 := @Enclosure.Real.IsNear.mulLit_ff qz664 (Zeta.RiemannSiegel.correction qz77) 739413 2097152 1 4194304 3617533118905 4398046511104 44689765707271 1077521395220480000 2674851016048902765 9223372036854775808 

noncomputable abbrev qz666 := (@HPow.hPow Real Real Real qz6 qz76 qz8)

noncomputable def Ns150p595 := @Enclosure.Real.IsNear.mulLit_ff qz48 qz666 1 1 0 1 739413 2097152 1 4194304 739413 2097152 1 4194304 

noncomputable def Ns150p596 := @Enclosure.Real.IsNear.sqrt_image qz76 108565432213 1677721600 81317 1677721600 33740038 33740065 4194304 (@Enclosure.Real.IsNear.of_eq qz76 (@HMul.hMul Real Real Real qz4 qz75 qz2) Bool.false 108565432213 1677721600 81317 1677721600 (BSN.t_div_two_pi_mk qz75 406585 1000 qz78) (@Enclosure.Real.IsNear.mulLit_ff qz75 qz2 406585 1000 0 1 1335089 8388608 1 8388608 108565432213 1677721600 81317 1677721600 (Enclosure.Real.IsNear.const Bool.false 406585 1000) RS151to168.d36 rfl)) 

noncomputable abbrev qz861 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 406585 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz667 := qz861

noncomputable abbrev qz434 := qz667

noncomputable abbrev qz81 := qz434

noncomputable def Ns150p597 := @Enclosure.Real.IsNear.sqrt_image qz81 67480103 8388608 27 8388608 11896048 11896054 4194304 (@Enclosure.Real.IsNear.recentre' qz81 Bool.false 67480103 8388608 27 8388608 67480103 8388608 27 8388608 (Ns150p596 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns150p598 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz81) 11896051 4194304 3 4194304 1478825 1478827 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz81) Bool.false 23792102 8388608 6 8388608 11896051 4194304 3 4194304 (Ns150p597 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns150p599 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz81)) Bool.false 2957652 8388608 2 8388608 739413 2097152 1 4194304 (Ns150p598 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz82 := (@HMul.hMul Real Real Real qz340 qz338 qz428)

noncomputable abbrev qz668 := (@HMul.hMul Real Real Real qz839 qz860 qz860)

noncomputable abbrev qz435 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz668 qz663) qz638)

noncomputable abbrev qz83 := (Real.cos (@HMul.hMul Real Real Real qz340 qz338 qz435))

noncomputable def Ns150p600 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz77) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz82)) qz83) Bool.false 3617533118905 

noncomputable def Ns150p601 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz82)) qz83 8723695 8388608 191 

noncomputable def Ns150p602 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz82)) Bool.false 8723695 8388608 191 8388608 8723695 8388608 191 

noncomputable def Ns150p603 := @Enclosure.Real.IsNear.recentre' (Real.cos qz82) Bool.false 4033196 4194304 343548608 16441671680000 1008299 1048576 5367947 256901120000 

noncomputable def Ns150p604 := @Enclosure.Real.IsNear.cos_image qz82 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2332563) qz368) Bool.false 2332563 8388608 171 8388608 Bool.false 4033196 4194304 1 

noncomputable def Ns150p605 := nat_lit 728624036047378146017561597 

noncomputable def Ns150p606 := nat_lit 36028797018963968000000000000000 

noncomputable def Ns150p607 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz77 884279719003555 140737488355328 1 500000000000000 371239 8388608 27 8388608 328279118603160754645 1180591620717411303424 Ns150p605 

noncomputable def Ns150p608 := @Enclosure.Real.IsNear.subLit_ff_p qz81 qz46 67480103 8388608 27 8388608 8 1 0 1 371239 371239 8388608 27 

noncomputable def Ns150p609 := @Ns150p608 8388608 (@Enclosure.Real.IsNear.recentre' qz81 Bool.false 67480103 8388608 27 8388608 67480103 8388608 27 8388608 (Ns150p596 rfl rfl rfl rfl rfl rfl) rfl) qz410 

noncomputable def Ns150p610 := @Enclosure.Real.IsNear.recentre' qz82 Bool.false 328279118603160754645 1180591620717411303424 Ns150p605 Ns150p606 2332563 8388608 171 8388608 (@Ns150p607 Ns150p606 RS151to168.d35 (Ns150p609 rfl rfl) rfl) 

noncomputable def Ns150p611 := nat_lit 29602850343535989491762961 

noncomputable def Ns150p612 := BSN.cos_dyadic_bound_f 2332563 8388608 2 1 4194304 1960000 Ns150p611 Ns150p175 Ns150p611 Ns150p611 Ns150p176 Ns150p611 4033196 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 2332563) (BSN.cosEvenQ 8388608) 0 1 Ns150p611 Ns150p175 Ns150p611 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 2332563) (BSN.cosOddQ 8388608) 0 1 Ns150p611 Ns150p176 Ns150p611 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p613 := @Enclosure.Real.IsNear.inv_image (Real.cos qz82) 1008299 1048576 5367947 256901120000 4361752 4361943 4194304 (Ns150p603 (@Ns150p604 1960000 (Ns150p610 rfl) (Enclosure.sfrac_false_div 2332563 8388608) (Ns150p612 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns150p614 := @Enclosure.Real.IsNear.recentre' qz83 Bool.false 3317432 4194304 

noncomputable abbrev qz84 := (@HMul.hMul Real Real Real qz340 qz338 qz435)

noncomputable def Ns150p615 := @Enclosure.Real.IsNear.cos_image qz84 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 2761767)) qz359) Bool.true 2761767 4194304 

noncomputable def Ns150p616 := nat_lit 6521038161839914891430403725 

noncomputable def Ns150p617 := nat_lit 9903520314283042199192993792 

noncomputable def Ns150p618 := nat_lit 6653148407698910497780015026613957 

noncomputable def Ns150p619 := @Enclosure.Real.IsNear.recentre' qz84 Bool.true Ns150p616 Ns150p617 Ns150p618 

noncomputable def Ns150p620 := nat_lit 302231454903657293676544000000000000000 

noncomputable abbrev qz85 := qz435

noncomputable def Ns150p621 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz85 884279719003555 140737488355328 1 500000000000000 7374406561295 

noncomputable abbrev qz436 := (@HSub.hSub Real Real Real qz634 qz668 qz663)

noncomputable abbrev qz86 := qz436

noncomputable def Ns150p622 := @Enclosure.Real.IsNear.subLit_tf qz86 qz25 2976360050191 70368744177664 246540051 70368744177664 1 16 

noncomputable abbrev qz437 := qz668

noncomputable abbrev qz87 := qz437

noncomputable def Ns150p623 := @Enclosure.Real.IsNear.subLit_ff_n qz87 qz77 137818395121 70368744177664 20047635 70368744177664 371239 8388608 27 8388608 

noncomputable def Ns150p624 := @Enclosure.Real.IsNear.mulLit_ff qz77 qz77 371239 8388608 27 8388608 371239 8388608 27 8388608 137818395121 70368744177664 

noncomputable def Ns150p625 := nat_lit 30251410960747475873271973704148815449705156629059485121 

noncomputable def Ns150p626 := nat_lit 3861888762982039923063034508418779142719222587902677483520 

noncomputable def Ns150p627 := nat_lit 3384513789159467008563445777678638730462800541269441 

noncomputable def Ns150p628 := nat_lit 90747463854664108685798794220891089071654544286095916481 

noncomputable def Ns150p629 := nat_lit 173784994334191796537836552878845061422365016455620486758400 

noncomputable def Ns150p630 := BSN.cos_dyadic_bound_f 2761767 4194304 3 2 4194304 1960000 Ns150p625 Ns150p626 Ns150p627 Ns150p628 Ns150p629 Ns150p627 3317432 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2761767) (BSN.cosEvenQ 4194304) 0 2 Ns150p625 Ns150p626 Ns150p627 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2761767) (BSN.cosOddQ 4194304) 0 2 Ns150p628 Ns150p629 Ns150p627 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p631 := @Ns150p614 370988608 16441671680000 414679 524288 5796697 256901120000 (@Ns150p615 185 8388608 Bool.false 3317432 4194304 1 1960000 (@Ns150p619 Ns150p620 2761767 4194304 185 8388608 (@Ns150p621 70368744177664 246540051 70368744177664 Ns150p616 Ns150p617 Ns150p618 Ns150p620 RS151to168.d35 (@Ns150p622 0 1 117990504980720 7374406561295 70368744177664 246540051 70368744177664 (@Ns150p623 24967517727912624128 2976360050191 70368744177664 246540051 70368744177664 (@Ns150p624 20047635 70368744177664 (Ns150p609 rfl rfl) (Ns150p609 rfl rfl) rfl) (Ns150p609 rfl rfl) rfl rfl) qz373 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 2761767 4194304) (BSN.cos_neg_of_bound 2761767 4194304 Bool.false 3317432 4194304 1 1960000 (Ns150p630 rfl rfl)) rfl rfl) 

noncomputable def Ns150p632 := @Ns150p594 9567818252245453731 645636042579834306560000 (Ns150p595 qz61 (@Enclosure.Real.IsNear.of_eq qz666 (@Inv.inv Real Real.instInv (Real.sqrt qz81)) Bool.false 739413 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz76 (BSN.t_div_two_pi_nonneg qz75 406585 1000 qz78)) Ns150p599) rfl) (@Ns150p600 4398046511104 44689765707271 1077521395220480000 (BSN.correction_mk qz77 (BSN.cos_two_pi_p_ne_zero_mk qz75 406585 1000 8 qz78 rfl rfl (@BSN.floor_sqrt_eq_dec qz75 406585 1000 8 qz78 rfl rfl rfl))) (@Ns150p601 8388608 414679 524288 5796697 256901120000 3617533118905 4398046511104 44689765707271 1077521395220480000 (@Ns150p602 8388608 (Ns150p613 rfl rfl rfl rfl rfl) rfl) (Ns150p631 rfl) rfl)) 

noncomputable def Ns150p633 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz75) (hardyZApproximantRS₀ qz75) Bool.true 47620126860223971949 9223372036854775808 1040775034931730893731 645636042579834306560000 (@Eq.refl Real (hardyZApproximantRS₀ qz75)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz75) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz75) qz75 8) (@HMul.hMul Real Real Real qz4 qz664 (Zeta.RiemannSiegel.correction qz77))) Bool.true 47620126860223971949 9223372036854775808 1040775034931730893731 645636042579834306560000 (BSN.hardyZApproximantRS₀_eq qz75 8 (@BSN.floor_sqrt_eq_dec qz75 406585 1000 8 qz78 rfl rfl rfl)) (@Ns150p526 47620126860223971949 9223372036854775808 1040775034931730893731 645636042579834306560000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz75) qz75 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz75) qz75 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz75) qz75 8)) Bool.true 163509961 33554432 53593 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz75) qz75 8) (Ns150p593 (Ns150p592 rfl rfl rfl rfl) rfl rfl)) (Ns150p632 rfl) rfl rfl)) 

theorem RS151to168.d47 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz75) Bool.true 47620126860223971949 9223372036854775808 1040775034931730893731 645636042579834306560000 := Ns150p633 

noncomputable def Ns150p634 := nat_lit 1807780919223536058368000 

noncomputable def Ns150p635 := nat_lit 10045758428264372628919156736 

noncomputable abbrev qz862 := (Enclosure.sfrac Bool.false 408091 1000)

noncomputable abbrev qz669 := qz862

noncomputable abbrev qz438 := qz669

noncomputable abbrev qz88 := qz438

noncomputable abbrev qz863 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 408091 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz670 := qz863

noncomputable abbrev qz439 := qz670

noncomputable abbrev qz89 := qz439

noncomputable abbrev qz864 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 408091 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz671 := qz864

noncomputable abbrev qz440 := qz671

noncomputable abbrev qz90 := qz440

noncomputable abbrev qz672 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz89 qz8))

noncomputable def Ns150p636 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz88) qz88 8) (@HMul.hMul Real Real Real qz4 qz672 (Zeta.RiemannSiegel.correction qz90)) 38710361 16777216 53789 33554432 82226009942421019455 295147905179352825856 27436655662300912037 Ns150p634 Ns150p635 

noncomputable def Ns150p637 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz88) qz88 Real.cos BSN.quadSignPos 7 8 408091 1000 128 67108864 33554432 1125899906842624 Bool.false 43430764729 1262 139548959 35 23726568 8 

noncomputable def Ns150p638 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz88) qz88 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 408091 1000 53 93 67108864 33554432 1125899906842624 Bool.false 43430764729 1262 

noncomputable def Ns150p639 := Ns150p638 120242927 35 27397080 8 130587807 35 25364760 8 Bool.false 93715904 36040 Bool.true 52330668 Bool.true 57408810 3537118876014220 1 Bool.false 47186154 Bool.true Bool.false 50658558 Bool.true Bool.false 55305106 

noncomputable def Ns150p640 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz88) qz88 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 408091 1000 51 6 67108864 33554432 1125899906842624 Bool.false 43430764729 1262 

noncomputable def Ns150p641 := Ns150p640 93032624 35 33554424 8 108007536 35 30011992 8 Bool.false 90570788 21295 Bool.false 88855957 Bool.true 13652502 3537118876014220 1 Bool.false 65076401 Bool.false Bool.false 65724927 Bool.true Bool.false 93715904 

noncomputable def Ns150p642 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz88) qz88 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 408091 1000 231 126 67108864 33554432 1125899906842624 Bool.false 43430764729 1262 

noncomputable def Ns150p643 := Ns150p642 46516304 35 47453136 16 73726608 35 38745320 8 Bool.false 67108840 1299 Bool.false 97163230 Bool.false 61390553 3537118876014220 1 Bool.false 66602258 Bool.false Bool.false 40933493 Bool.true Bool.false 90570788 

noncomputable def Ns150p644 := nat_lit 484645207270391313503207980098089613232641813770372051779 

noncomputable def Ns150p645 := nat_lit 748869827774703915029945656937978812093199963652096000 

noncomputable def Ns150p646 := nat_lit 5432853246300092709389949496480000 

noncomputable def Ns150p647 := nat_lit 13302600403880829472135361458704118080 

noncomputable abbrev qz441 := (@Eq.refl Real qz669)

noncomputable abbrev qz91 := qz441

noncomputable def Ns150p648 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz88 408091 1000 666154057124 16000000 816182 4000 2000 Ns150p646 Ns150p647 qz91 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns150p649 := nat_lit 155086466326525220321026553631388676234445380406519056569280 

noncomputable abbrev qz442 := (Enclosure.sfrac Bool.false 408091 2000)

noncomputable abbrev qz673 := (Real.log (Enclosure.sfrac Bool.false 666154057124 16000000))

noncomputable abbrev qz92 := (@HSub.hSub Real Real Real qz344 (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 408091 4000) qz673) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 816182)))))) qz442)

noncomputable abbrev qz443 := (@HSub.hSub Real Real Real qz11 qz92 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 408091 2000) (Real.log Real.pi)))

noncomputable def Ns150p650 := @Enclosure.Real.IsNear.addLit_ft_p qz443 (Enclosure.sfrac Bool.true Ns150p646 Ns150p647) 11658364491717312517891 18014398509481984000 188623275309706787 10035200000000000000000 Ns150p646 Ns150p647 0 1 Ns150p649 

noncomputable def Ns150p651 := nat_lit 782379597137086252208644685824000 

noncomputable abbrev qz444 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 408091 2000) (Real.log Real.pi))

noncomputable def Ns150p652 := @Enclosure.Real.IsNear.subLit_ff_p qz92 qz444 15866113314331990169347 18014398509481984000 260056934994277 39200000000000000000 15675085867251 67108864000 408091 33554432000 Ns150p651 11658364491717312517891 18014398509481984000 

noncomputable def Ns150p653 := nat_lit 31732226628663980338694000 

noncomputable abbrev qz93 := (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 408091 4000) qz673) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 816182))))))

noncomputable def Ns150p654 := @Enclosure.Real.IsNear.subLit_ff_p qz93 qz442 19541870265398496335619 18014398509481984000 260056934994277 39200000000000000000 408091 2000 0 1 Ns150p653 15866113314331990169347 18014398509481984000 260056934994277 39200000000000000000 

noncomputable def Ns150p655 := nat_lit 44004379822685621934651838256237248512 

noncomputable def Ns150p656 := nat_lit 12858966140135979198971904 

noncomputable def Ns150p657 := nat_lit 298840097229776041267489095074413627194272454748261698578479825349330964480 

noncomputable def Ns150p658 := nat_lit 1426856389770873238682248362612299582988344370809312419164400399234461696 

noncomputable def Ns150p659 := nat_lit 122281920388427053120852031677353286548273246580600039855478887280640 

noncomputable def Ns150p660 := BSN.log_dyadic_bound 141866057124 1190442057124 4 3 Ns150p657 33554432 15680000 Ns150p658 Ns150p659 8035608 1332308114248 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 141866057124) (BSN.artanhQ 1190442057124) 0 3 Ns150p658 Ns150p657 Ns150p659 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns150p661 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 408091 4000) qz673 408091 4000 0 1 47903381810098809 4503599627370496 625000147 9800000000000000 19548938986265033063619 18014398509481984000 255056934989377 39200000000000000000 (Enclosure.Real.IsNear.const Bool.false 408091 4000) (BSN.isNear_log_sfrac 666154057124 16000000 47903381810098809 4503599627370496 625000147 9800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 666154057124) qz352)) Bool.false Ns150p656 Ns150p86 1000000235200000 15680000000000000000000 47903381810098809 4503599627370496 625000147 9800000000000000 (BSN.log_rat_reduce_isNear 666154057124 16000000 15 1332308114248 1048576000000 8035608 33554432 24973259072661432 36028797018963968 15680000 1000000000000000 rfl rfl rfl rfl (Ns150p660 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns150p662 := BSN.arctan_dyadic_bound_f 1000 816182 1 0 4194304 1960000 0 1 1 0 1 1 5138 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 816182) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 816182) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz445 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 816182)))

noncomputable def Ns150p663 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz445 884279719003555 562949953421312 1 2000000000000000 5138 4194304 1 1960000 3706045525674808049664 883590108317091 562949953421312 50000000049 98000000000000000 qz16 (Ns150p662 rfl) rfl rfl 

noncomputable def Ns150p664 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 408091 4000) qz673) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz445)) 19548938986265033063619 18014398509481984000 255056934989377 39200000000000000000 883590108317091 2251799813685248 50000000049 392000000000000000 Ns150p655 19541870265398496335619 18014398509481984000 260056934994277 39200000000000000000 (Ns150p661 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz445) 1 4 0 1 883590108317091 562949953421312 50000000049 98000000000000000 883590108317091 2251799813685248 50000000049 392000000000000000 qz355 Ns150p663 rfl) 

noncomputable def Ns150p665 := @Ns150p650 Ns150p644 Ns150p645 188623275309706787 10035200000000000000000 (@Ns150p652 188623275309706787 10035200000000000000000 (Ns150p654 (Ns150p664 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 408091 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz442 (Real.log Real.pi) 408091 2000 0 1 38410761 33554432 1 16777216 15675085867251 67108864000 408091 33554432000 (Enclosure.Real.IsNear.const Bool.false 408091 2000) RS151to168.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns150p646 Ns150p647) 

noncomputable def Ns150p666 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz88) Bool.false Ns150p644 Ns150p645 188623275309706787 10035200000000000000000 5428845591 8388608 79 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz88) (@HAdd.hAdd Real Real Real qz356 qz443 (Enclosure.sfrac Bool.true Ns150p646 Ns150p647)) Bool.false Ns150p644 Ns150p645 188623275309706787 10035200000000000000000 Ns150p648 (Ns150p665 rfl rfl)) 

noncomputable def Ns150p667 := BSN.cos_dyadic_bound_f 12701841 17179869184 1 0 8388608 3923829 0 1 1 0 1 1 8388605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 12701841) (BSN.cosEvenQ 17179869184) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 12701841) (BSN.cosOddQ 17179869184) 0 0 rfl) rfl rfl 

noncomputable def Ns150p668 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz88) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5428845591) qz368) Bool.false 5428845591 8388608 79 4194304 Bool.false 8388605 8388608 1 1960000 (Ns150p666 rfl) (Enclosure.sfrac_false_div 5428845591 8388608) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5428845591) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 893812660207114780672) qz369) 226375608064910080 72057594037927936 Bool.false 8388605 8388608 103 1000000000000000 3920000 1960000 (BSN.sin_reduce_arg_pos_rat_q0 5428845591 8388608 226375608064910080 72057594037927936 103 893812660207114780672 Ns150p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 8388605 8388608 893812660207114780672 Ns150p86 12701841 17179869184 3923829 3920000 (Ns150p667 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns150p669 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz88) Bool.false Ns150p644 Ns150p645 188623275309706787 10035200000000000000000 43430764729 67108864 1262 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz88) (@HAdd.hAdd Real Real Real qz356 qz443 (Enclosure.sfrac Bool.true Ns150p646 Ns150p647)) Bool.false Ns150p644 Ns150p645 188623275309706787 10035200000000000000000 Ns150p648 (Ns150p665 rfl rfl)) 

noncomputable def Ns150p670 := Ns150p643 21295 BSN.abs_quadSignPos (BSN.cos_quad_nat3 231 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66602258 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 126 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 40933493 67108864) qz91 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz88) qz88 1) Bool.false 8388605 8388608 2484911 128450560000 67108840 67108864 1299 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz88) qz88 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz88)) Bool.false 8388605 8388608 2484911 128450560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz88) qz88) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz88)) Bool.false 8388605 8388608 159034304 8220835840000 8388605 8388608 2484911 128450560000 (Ns150p668 rfl rfl) rfl)) rfl) (Ns150p669 rfl) RS151to168.d7 

noncomputable def Ns150p671 := nat_lit 1905358647986263470529580512449087952224148125124604842011012800235641141148221125999665832125606400000 

noncomputable def Ns150p672 := nat_lit 707983805399415470604307590522393057249824363292606381470385416335207917650484401521000000000000 

noncomputable def Ns150p673 := nat_lit 9518244885662320354710402575091714754574456873415050765528202943799792525923601170296235482644032000000 

noncomputable def Ns150p674 := BSN.sin_dyadic_bound_f 97163230 67108864 4 3 67108864 33554432 Ns150p671 Ns150p111 Ns150p672 Ns150p673 Ns150p114 Ns150p672 66602258 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 97163230) qz361 0 3 Ns150p671 Ns150p111 Ns150p672 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 97163230) (BSN.sinOddQ 67108864) 0 3 Ns150p673 Ns150p114 Ns150p672 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p675 := nat_lit 484190216193523775545832959137100893317950175769574962133000328641 

noncomputable def Ns150p676 := nat_lit 201749452040906493553999998493021103599162376974547000780199361 

noncomputable def Ns150p677 := nat_lit 1452167149676489513650390877414316637746652202554775792397440587201 

noncomputable def Ns150p678 := BSN.cos_dyadic_bound_f 61390553 67108864 3 2 67108864 33554432 Ns150p675 Ns150p117 Ns150p676 Ns150p677 Ns150p120 Ns150p676 40933493 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 61390553) qz362 0 2 Ns150p675 Ns150p117 Ns150p676 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 61390553) (BSN.cosOddQ 67108864) 0 2 Ns150p677 Ns150p120 Ns150p676 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p679 := nat_lit 3827266493288857952546375427456484379953148727663022401915939161185 

noncomputable def Ns150p680 := nat_lit 3885906883304061901348175676896057282753413982627196741803541601 

noncomputable def Ns150p681 := nat_lit 10017501728421659489781181454147246426181407806955090829340730164321 

noncomputable def Ns150p682 := BSN.sin_dyadic_bound_f 88855957 67108864 3 2 67108864 33554432 Ns150p679 Ns150p359 Ns150p680 Ns150p681 Ns150p362 Ns150p680 65076401 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 88855957) qz361 0 2 Ns150p679 Ns150p359 Ns150p680 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 88855957) (BSN.sinOddQ 67108864) 0 2 Ns150p681 Ns150p362 Ns150p680 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p683 := nat_lit 34741534373049785066086880016 

noncomputable def Ns150p684 := BSN.cos_dyadic_bound_f 13652502 67108864 2 1 67108864 33554432 Ns150p683 Ns150p134 Ns150p683 Ns150p683 Ns150p135 Ns150p683 65724927 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 13652502) qz362 0 1 Ns150p683 Ns150p134 Ns150p683 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 13652502) (BSN.cosOddQ 67108864) 0 1 Ns150p683 Ns150p135 Ns150p683 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p685 := Ns150p641 36040 BSN.abs_quadSignPos (BSN.cos_quad_nat3 51 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 65076401 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 6 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 65724927 67108864) qz91 rfl rfl (Ns150p670 RS151to168.d9 RS151to168.d11 RS151to168.d13 RS151to168.d17 (Ns150p674 rfl rfl) (Ns150p678 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns150p669 rfl) RS151to168.d19 RS151to168.d21 RS151to168.d23 RS151to168.d25 RS151to168.d17 (Ns150p682 rfl rfl) (Ns150p684 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns150p686 := nat_lit 460023002729956624309268039741685432219218746244043985634956738560 

noncomputable def Ns150p687 := nat_lit 56240636648524382602509024596009576463759840815855653030526976 

noncomputable def Ns150p688 := nat_lit 1204731093738169738476250327569354021259869676611175243700932509696 

noncomputable def Ns150p689 := BSN.sin_dyadic_bound_f 52330668 67108864 3 2 67108864 33554432 Ns150p686 Ns150p359 Ns150p687 Ns150p688 Ns150p362 Ns150p687 47186154 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 52330668) qz361 0 2 Ns150p686 Ns150p359 Ns150p687 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 52330668) (BSN.sinOddQ 67108864) 0 2 Ns150p688 Ns150p362 Ns150p687 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p690 := nat_lit 666334684922650604312099253396522354737946912779577513134036640000 

noncomputable def Ns150p691 := nat_lit 117985423953741367038035262911313387309669781863324224100000000 

noncomputable def Ns150p692 := nat_lit 1744971246015778858604103130374749755019931020490162390416791200000 

noncomputable def Ns150p693 := BSN.sin_dyadic_bound_f 57408810 67108864 3 2 67108864 33554432 Ns150p690 Ns150p359 Ns150p691 Ns150p692 Ns150p362 Ns150p691 50658558 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 57408810) qz361 0 2 Ns150p690 Ns150p359 Ns150p691 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 57408810) (BSN.sinOddQ 67108864) 0 2 Ns150p692 Ns150p362 Ns150p691 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p694 := Ns150p639 48282 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 53 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 47186154 67108864) BSN.abs_quadSignNeg qz650 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 50658558 67108864) qz91 rfl rfl (Ns150p685 rfl rfl) (Ns150p669 rfl) RS151to168.d27 RS151to168.d29 RS151to168.d31 RS151to168.d33 RS151to168.d17 (Ns150p689 rfl rfl) (Ns150p693 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns150p695 := nat_lit 13039534457545525435862937378642975114417354836841682661784516481 

noncomputable def Ns150p696 := nat_lit 146439000650272020999341683888739829622750411494774908745601 

noncomputable def Ns150p697 := nat_lit 39118310494635275763546813452561147863592819009702058435536058241 

noncomputable def Ns150p698 := BSN.cos_dyadic_bound_f 24871793 67108864 3 2 67108864 33554432 Ns150p695 Ns150p117 Ns150p696 Ns150p697 Ns150p120 Ns150p696 62552405 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 24871793) qz362 0 2 Ns150p695 Ns150p117 Ns150p696 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 24871793) (BSN.cosOddQ 67108864) 0 2 Ns150p697 Ns150p120 Ns150p696 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p699 := Ns150p637 Bool.false 55305106 48282 Bool.true 24871793 3537118876014220 1 Bool.false 62552405 Bool.false Bool.false 77420722 53789 BSN.abs_quadSignPos qz407 (BSN.sfrac_eq_quadSignPos_mul Bool.false 62552405 67108864) qz91 rfl (Ns150p694 rfl) (Ns150p669 rfl) RS151to168.d42 RS151to168.d44 RS151to168.d17 (Ns150p698 rfl rfl) rfl 

noncomputable def Ns150p700 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz88) qz88 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz88) qz88 8) 77420722 67108864 53789 67108864 77420722 67108864 53789 67108864 10391233406959616 38710361 16777216 53789 33554432 (Ns150p699 rfl rfl rfl rfl) 

noncomputable def Ns150p701 := @Enclosure.Real.IsNear.mulLit_ff qz672 (Zeta.RiemannSiegel.correction qz90) 2954919 8388608 1 8388608 27826823659945 35184372088832 23068489474659 538760697610240000 82226009942421019455 295147905179352825856 

noncomputable abbrev qz674 := (@HPow.hPow Real Real Real qz6 qz89 qz8)

noncomputable def Ns150p702 := @Enclosure.Real.IsNear.mulLit_ff qz48 qz674 1 1 0 1 2954919 8388608 1 8388608 2954919 8388608 1 8388608 

noncomputable def Ns150p703 := @Enclosure.Real.IsNear.sqrt_image qz89 544837805099 8388608000 408091 8388608000 33802467 33802494 4194304 (@Enclosure.Real.IsNear.of_eq qz89 (@HMul.hMul Real Real Real qz4 qz88 qz2) Bool.false 544837805099 8388608000 408091 8388608000 (BSN.t_div_two_pi_mk qz88 408091 1000 qz91) (@Enclosure.Real.IsNear.mulLit_ff qz88 qz2 408091 1000 0 1 1335089 8388608 1 8388608 544837805099 8388608000 408091 8388608000 (Enclosure.Real.IsNear.const Bool.false 408091 1000) RS151to168.d36 rfl)) 

noncomputable abbrev qz865 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 408091 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz675 := qz865

noncomputable abbrev qz446 := qz675

noncomputable abbrev qz94 := qz446

noncomputable def Ns150p704 := @Enclosure.Real.IsNear.sqrt_image qz94 67604961 8388608 27 8388608 11907049 11907055 4194304 (@Enclosure.Real.IsNear.recentre' qz94 Bool.false 67604961 8388608 27 8388608 67604961 8388608 27 8388608 (Ns150p703 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns150p705 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz94) 2976763 1048576 3 4194304 1477459 1477460 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz94) Bool.false 23814104 8388608 6 8388608 2976763 1048576 3 4194304 (Ns150p704 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns150p706 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz94)) Bool.false 2954919 8388608 1 8388608 2954919 8388608 1 8388608 (Ns150p705 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz95 := (@HMul.hMul Real Real Real qz340 qz338 qz440)

noncomputable abbrev qz676 := (@HMul.hMul Real Real Real qz839 qz864 qz864)

noncomputable abbrev qz447 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz676 qz671) qz638)

noncomputable abbrev qz96 := (Real.cos (@HMul.hMul Real Real Real qz340 qz338 qz447))

noncomputable def Ns150p707 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz90) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz95)) qz96) Bool.false 27826823659945 

noncomputable def Ns150p708 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz95)) qz96 9003035 8388608 203 

noncomputable def Ns150p709 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz95)) Bool.false 9003035 8388608 203 8388608 9003035 8388608 203 

noncomputable def Ns150p710 := @Enclosure.Real.IsNear.recentre' (Real.cos qz95) Bool.false 3908057 4194304 343548608 16441671680000 3908057 4194304 5367947 256901120000 

noncomputable def Ns150p711 := @Enclosure.Real.IsNear.cos_image qz95 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3117069) qz368) Bool.false 3117069 8388608 171 8388608 Bool.false 3908057 4194304 1 

noncomputable def Ns150p712 := nat_lit 728624036048450668070849533 

noncomputable def Ns150p713 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz90 884279719003555 140737488355328 1 500000000000000 496097 8388608 27 8388608 438688515758506624835 1180591620717411303424 Ns150p712 

noncomputable def Ns150p714 := @Enclosure.Real.IsNear.subLit_ff_p qz94 qz46 67604961 8388608 27 8388608 8 1 0 1 496097 496097 8388608 27 

noncomputable def Ns150p715 := @Ns150p714 8388608 (@Enclosure.Real.IsNear.recentre' qz94 Bool.false 67604961 8388608 27 8388608 67604961 8388608 27 8388608 (Ns150p703 rfl rfl rfl rfl rfl rfl) rfl) qz410 

noncomputable def Ns150p716 := @Enclosure.Real.IsNear.recentre' qz95 Bool.false 438688515758506624835 1180591620717411303424 Ns150p712 Ns150p606 3117069 8388608 171 8388608 (@Ns150p713 Ns150p606 RS151to168.d35 (Ns150p715 rfl rfl) rfl) 

noncomputable def Ns150p717 := nat_lit 94402971351784655846879121 

noncomputable def Ns150p718 := BSN.cos_dyadic_bound_f 3117069 8388608 2 1 4194304 1960000 Ns150p717 Ns150p175 Ns150p717 Ns150p717 Ns150p176 Ns150p717 3908057 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 3117069) (BSN.cosEvenQ 8388608) 0 1 Ns150p717 Ns150p175 Ns150p717 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 3117069) (BSN.cosOddQ 8388608) 0 1 Ns150p717 Ns150p176 Ns150p717 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p719 := @Enclosure.Real.IsNear.inv_image (Real.cos qz95) 3908057 4194304 5367947 256901120000 4501416 4501619 4194304 (Ns150p710 (@Ns150p711 1960000 (Ns150p716 rfl) (Enclosure.sfrac_false_div 3117069 8388608) (Ns150p718 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns150p720 := @Enclosure.Real.IsNear.recentre' qz96 Bool.false 3090827 4194304 

noncomputable abbrev qz97 := (@HMul.hMul Real Real Real qz340 qz338 qz447)

noncomputable def Ns150p721 := @Enclosure.Real.IsNear.cos_image qz97 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 3113463)) qz359) Bool.true 3113463 4194304 

noncomputable def Ns150p722 := nat_lit 7351457269201297435206085405 

noncomputable def Ns150p723 := nat_lit 6835097487491787984950632379199593 

noncomputable def Ns150p724 := @Enclosure.Real.IsNear.recentre' qz97 Bool.true Ns150p722 Ns150p617 Ns150p723 

noncomputable abbrev qz98 := qz447

noncomputable def Ns150p725 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz98 884279719003555 140737488355328 1 500000000000000 8313497540671 

noncomputable abbrev qz448 := (@HSub.hSub Real Real Real qz634 qz676 qz671)

noncomputable abbrev qz99 := qz448

noncomputable def Ns150p726 := @Enclosure.Real.IsNear.subLit_tf qz99 qz25 3915451029567 70368744177664 253282383 70368744177664 1 16 

noncomputable abbrev qz449 := qz676

noncomputable abbrev qz100 := qz449

noncomputable def Ns150p727 := @Enclosure.Real.IsNear.subLit_ff_n qz100 qz90 246112233409 70368744177664 26789967 70368744177664 496097 8388608 27 8388608 

noncomputable def Ns150p728 := @Enclosure.Real.IsNear.mulLit_ff qz90 qz90 496097 8388608 27 8388608 496097 8388608 27 8388608 246112233409 70368744177664 

noncomputable def Ns150p729 := nat_lit 48865485527333823853194349897860098567184191991518676801 

noncomputable def Ns150p730 := nat_lit 8829775708689582305735320809666700938222392377689921 

noncomputable def Ns150p731 := nat_lit 146578797030584092394971579051960962299676131189800650561 

noncomputable def Ns150p732 := BSN.cos_dyadic_bound_f 3113463 4194304 3 2 4194304 1960000 Ns150p729 Ns150p626 Ns150p730 Ns150p731 Ns150p629 Ns150p730 3090827 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3113463) (BSN.cosEvenQ 4194304) 0 2 Ns150p729 Ns150p626 Ns150p730 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3113463) (BSN.cosOddQ 4194304) 0 2 Ns150p731 Ns150p629 Ns150p730 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p733 := @Ns150p720 382748608 16441671680000 3090827 4194304 5980447 256901120000 (@Ns150p721 191 8388608 Bool.false 3090827 4194304 1 1960000 (@Ns150p724 Ns150p620 3113463 4194304 191 8388608 (@Ns150p725 70368744177664 253282383 70368744177664 Ns150p722 Ns150p617 Ns150p723 Ns150p620 RS151to168.d35 (@Ns150p726 0 1 133015960650736 8313497540671 70368744177664 253282383 70368744177664 (@Ns150p727 32845183830233972736 3915451029567 70368744177664 253282383 70368744177664 (@Ns150p728 26789967 70368744177664 (Ns150p715 rfl rfl) (Ns150p715 rfl rfl) rfl) (Ns150p715 rfl rfl) rfl rfl) qz373 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 3113463 4194304) (BSN.cos_neg_of_bound 3113463 4194304 Bool.false 3090827 4194304 1 1960000 (Ns150p732 rfl rfl)) rfl rfl) 

noncomputable def Ns150p734 := @Ns150p701 27436655662300912037 Ns150p634 (Ns150p702 qz61 (@Enclosure.Real.IsNear.of_eq qz674 (@Inv.inv Real Real.instInv (Real.sqrt qz94)) Bool.false 2954919 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz89 (BSN.t_div_two_pi_nonneg qz88 408091 1000 qz91)) Ns150p706) rfl) (@Ns150p707 35184372088832 23068489474659 538760697610240000 (BSN.correction_mk qz90 (BSN.cos_two_pi_p_ne_zero_mk qz88 408091 1000 8 qz91 rfl rfl (@BSN.floor_sqrt_eq_dec qz88 408091 1000 8 qz91 rfl rfl rfl))) (@Ns150p708 8388608 3090827 4194304 5980447 256901120000 27826823659945 35184372088832 23068489474659 538760697610240000 (@Ns150p709 8388608 (Ns150p719 rfl rfl rfl rfl rfl) rfl) (Ns150p733 rfl) rfl)) 

noncomputable def Ns150p735 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz88) (hardyZApproximantRS₀ qz88) Bool.false 598773862616084374721 295147905179352825856 2925376572038020848037 Ns150p634 (@Eq.refl Real (hardyZApproximantRS₀ qz88)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz88) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz88) qz88 8) (@HMul.hMul Real Real Real qz4 qz672 (Zeta.RiemannSiegel.correction qz90))) Bool.false 598773862616084374721 295147905179352825856 2925376572038020848037 Ns150p634 (BSN.hardyZApproximantRS₀_eq qz88 8 (@BSN.floor_sqrt_eq_dec qz88 408091 1000 8 qz91 rfl rfl rfl)) (@Ns150p636 598773862616084374721 295147905179352825856 2925376572038020848037 Ns150p634 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz88) qz88 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz88) qz88 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz88) qz88 8)) Bool.false 38710361 16777216 53789 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz88) qz88 8) (Ns150p700 (Ns150p699 rfl rfl rfl rfl) rfl rfl)) (Ns150p734 rfl) rfl rfl)) 

theorem RS151to168.d48 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz88) Bool.false 598773862616084374721 295147905179352825856 2925376572038020848037 Ns150p634 := Ns150p735 

noncomputable def Ns150p736 := nat_lit 654801373204382419806846976 

noncomputable abbrev qz866 := (Enclosure.sfrac Bool.false 409595 1000)

noncomputable abbrev qz677 := qz866

noncomputable abbrev qz450 := qz677

noncomputable abbrev qz101 := qz450

noncomputable abbrev qz867 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 409595 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz678 := qz867

noncomputable abbrev qz451 := qz678

noncomputable abbrev qz102 := qz451

noncomputable abbrev qz868 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 409595 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz679 := qz868

noncomputable abbrev qz452 := qz679

noncomputable abbrev qz103 := qz452

noncomputable abbrev qz680 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz102 qz8))

noncomputable def Ns150p737 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz101) qz101 8) (@HMul.hMul Real Real Real qz4 qz680 (Zeta.RiemannSiegel.correction qz103)) 7751443 4194304 6749 4194304 19751985624454705281 73786976294838206464 8627385601815796401 564931537257355018240000 Ns150p736 

noncomputable def Ns150p738 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz101) qz101 Real.cos BSN.quadSignPos 7 8 409595 1000 128 67108864 33554432 1125899906842624 Bool.false 43641482697 1267 139548959 35 23726568 8 

noncomputable def Ns150p739 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz101) qz101 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 409595 1000 53 93 67108864 33554432 1125899906842624 Bool.false 43641482697 1267 

noncomputable def Ns150p740 := Ns150p739 120242927 35 27397080 8 130587807 35 25364760 8 Bool.true 60042533 36178 Bool.true 22458063 Bool.true 43094903 3537118876014220 1 Bool.false 22041218 Bool.true Bool.false 40193502 Bool.true Bool.true 84232535 

noncomputable def Ns150p741 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz101) qz101 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 409595 1000 52 5 67108864 33554432 1125899906842624 Bool.false 43641482697 1267 

noncomputable def Ns150p742 := Ns150p741 93032624 35 33554424 8 108007536 35 30011992 8 Bool.true 57115803 21378 Bool.false 54238502 Bool.true 70792225 3537118876014220 1 Bool.false 46358064 Bool.false Bool.false 58374254 Bool.true Bool.true 60042533 

noncomputable def Ns150p743 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz101) qz101 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 409595 1000 233 127 67108864 33554432 1125899906842624 Bool.false 43641482697 1267 

noncomputable def Ns150p744 := Ns150p743 46516304 35 47453136 16 73726608 35 38745320 8 Bool.true 67108832 1307 Bool.false 27091963 Bool.false 55809345 3537118876014220 1 Bool.false 26362050 Bool.true Bool.false 49595223 Bool.false Bool.true 57115803 

noncomputable def Ns150p745 := nat_lit 6372673602280837805799688843277392309907176085647567 

noncomputable def Ns150p746 := nat_lit 9799458214040852843147316740969013977606730547200 

noncomputable def Ns150p747 := nat_lit 5533706350335572566480398500000000 

noncomputable def Ns150p748 := nat_lit 13599480172600337872717164351645000000 

noncomputable abbrev qz453 := (@Eq.refl Real qz677)

noncomputable abbrev qz104 := qz453

noncomputable def Ns150p749 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz101 409595 1000 671073256100 16000000 819190 4000 2000 Ns150p747 Ns150p748 qz104 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns150p750 := nat_lit 31863368011404189028998444216386961549535880428237835000000 

noncomputable abbrev qz454 := (Enclosure.sfrac Bool.false 409595 2000)

noncomputable abbrev qz681 := (Real.log (Enclosure.sfrac Bool.false 671073256100 16000000))

noncomputable abbrev qz105 := (@HSub.hSub Real Real Real qz344 (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 409595 4000) qz681) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 819190)))))) qz454)

noncomputable abbrev qz455 := (@HSub.hSub Real Real Real qz11 qz105 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 409595 2000) (Real.log Real.pi)))

noncomputable def Ns150p751 := @Enclosure.Real.IsNear.addLit_ft_p qz455 (Enclosure.sfrac Bool.true Ns150p747 Ns150p748) 2342985727710349710023 3602879701896396800 37862744010761063 2007040000000000000000 Ns150p747 Ns150p748 0 1 Ns150p750 

noncomputable def Ns150p752 := nat_lit 31447022110970978016474588774400 

noncomputable abbrev qz456 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 409595 2000) (Real.log Real.pi))

noncomputable def Ns150p753 := @Enclosure.Real.IsNear.subLit_ff_p qz105 qz456 3187636983924703318727 3602879701896396800 52199387043073 7840000000000000000 3146571130359 13421772800 81919 6710886400 Ns150p752 2342985727710349710023 3602879701896396800 

noncomputable abbrev qz106 := (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 409595 4000) qz681) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 819190))))))

noncomputable def Ns150p754 := @Enclosure.Real.IsNear.subLit_ff_p qz106 qz454 157019909586953225695 144115188075855872 52199387043073 7840000000000000000 409595 2000 0 1 255010958713976265498160 3187636983924703318727 3602879701896396800 52199387043073 7840000000000000000 

noncomputable def Ns150p755 := nat_lit 353577403152775759864388319036047360 

noncomputable def Ns150p756 := nat_lit 12867860641313644871680000 

noncomputable def Ns150p757 := nat_lit 306326346812803477121434505705979222414615440680969278271432905000000000000 

noncomputable def Ns150p758 := nat_lit 1553756890353396709697489452005753630194426348871129271814631000000000000 

noncomputable def Ns150p759 := nat_lit 150032680486456760304171265095262140532286322402686090415000000000000 

noncomputable def Ns150p760 := BSN.log_dyadic_bound 146785256100 1195361256100 4 3 Ns150p757 33554432 15680000 Ns150p758 Ns150p759 8282480 1342146512200 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 146785256100) (BSN.artanhQ 1195361256100) 0 3 Ns150p758 Ns150p757 Ns150p759 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns150p761 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 409595 4000) qz681 409595 4000 0 1 47936516409045625 4503599627370496 625000147 9800000000000000 157076459508504342175 144115188075855872 51199387042093 7840000000000000000 (Enclosure.Real.IsNear.const Bool.false 409595 4000) (BSN.isNear_log_sfrac 671073256100 16000000 47936516409045625 4503599627370496 625000147 9800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 671073256100) qz352)) Bool.false Ns150p756 Ns150p86 1000000235200000 15680000000000000000000 47936516409045625 4503599627370496 625000147 9800000000000000 (BSN.log_rat_reduce_isNear 671073256100 16000000 15 1342146512200 1048576000000 8282480 33554432 24973259072661432 36028797018963968 15680000 1000000000000000 rfl rfl rfl rfl (Ns150p760 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns150p762 := BSN.arctan_dyadic_bound_f 1000 819190 1 0 4194304 1960000 0 1 1 0 1 1 5120 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 819190) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 819190) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz457 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 819190)))

noncomputable def Ns150p763 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz457 884279719003555 562949953421312 1 2000000000000000 5120 4194304 1 1960000 3706055658773969633280 883592524236195 562949953421312 50000000049 98000000000000000 qz16 (Ns150p762 rfl) rfl rfl 

noncomputable def Ns150p764 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 409595 4000) qz681) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz457)) 157076459508504342175 144115188075855872 51199387042093 7840000000000000000 883592524236195 2251799813685248 50000000049 392000000000000000 Ns150p755 157019909586953225695 144115188075855872 52199387043073 7840000000000000000 (Ns150p761 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz457) 1 4 0 1 883592524236195 562949953421312 50000000049 98000000000000000 883592524236195 2251799813685248 50000000049 392000000000000000 qz355 Ns150p763 rfl) 

noncomputable def Ns150p765 := @Ns150p751 Ns150p745 Ns150p746 37862744010761063 2007040000000000000000 (@Ns150p753 37862744010761063 2007040000000000000000 (Ns150p754 (Ns150p764 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 409595 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz454 (Real.log Real.pi) 409595 2000 0 1 38410761 33554432 1 16777216 3146571130359 13421772800 81919 6710886400 (Enclosure.Real.IsNear.const Bool.false 409595 2000) RS151to168.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns150p747 Ns150p748) 

noncomputable def Ns150p766 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz101) Bool.false Ns150p745 Ns150p746 37862744010761063 2007040000000000000000 5455185337 8388608 159 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz101) (@HAdd.hAdd Real Real Real qz356 qz455 (Enclosure.sfrac Bool.true Ns150p747 Ns150p748)) Bool.false Ns150p745 Ns150p746 37862744010761063 2007040000000000000000 Ns150p749 (Ns150p765 rfl rfl)) 

noncomputable def Ns150p767 := nat_lit 1897875024502310299500544 

noncomputable def Ns150p768 := nat_lit 139663808165547056677714633107078626707909507990788291823963399914493748947074416640000 

noncomputable def Ns150p769 := nat_lit 279964187466281045869426476811395368823221586262288372882050598598782589337600000000 

noncomputable def Ns150p770 := nat_lit 365332888891963550557844967651320810780715876455258964078095108330704646859600691200000 

noncomputable def Ns150p771 := BSN.sin_dyadic_bound_f 26970426240 17179869184 3 2 8388608 3923829 Ns150p768 Ns150p98 Ns150p769 Ns150p770 Ns150p101 Ns150p769 8388604 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26970426240) qz357 0 2 Ns150p768 Ns150p98 Ns150p769 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26970426240) qz358 0 2 Ns150p770 Ns150p101 Ns150p769 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p772 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz101) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5455185337) qz368) Bool.false 5455185337 8388608 159 8388608 Bool.true 8388604 8388608 1 1960000 (Ns150p766 rfl) (Enclosure.sfrac_false_div 5455185337 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5455185337) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns150p767) qz369) 226375608064910080 72057594037927936 Bool.false 8388604 8388608 103 1000000000000000 3920000 1960000 (BSN.sin_reduce_arg_pos_rat_q1 5455185337 8388608 226375608064910080 72057594037927936 103 Ns150p767 Ns150p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388604 8388608 Ns150p767 Ns150p86 26970426240 17179869184 3923829 3920000 (Ns150p771 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns150p773 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz101) Bool.false Ns150p745 Ns150p746 37862744010761063 2007040000000000000000 43641482697 67108864 1267 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz101) (@HAdd.hAdd Real Real Real qz356 qz455 (Enclosure.sfrac Bool.true Ns150p747 Ns150p748)) Bool.false Ns150p745 Ns150p746 37862744010761063 2007040000000000000000 Ns150p749 (Ns150p765 rfl rfl)) 

noncomputable def Ns150p774 := Ns150p744 21378 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 233 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 26362050 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 127 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 49595223 67108864) qz104 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz101) qz101 1) Bool.true 2097151 2097152 5000447 256901120000 67108832 67108864 1307 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz101) qz101 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz101)) Bool.true 2097151 2097152 5000447 256901120000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz101) qz101) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz101)) Bool.true 8388604 8388608 320028608 16441671680000 2097151 2097152 5000447 256901120000 (Ns150p772 rfl rfl) rfl)) rfl) (Ns150p773 rfl) RS151to168.d7 

noncomputable def Ns150p775 := nat_lit 538718506748198495362133570161 

noncomputable def Ns150p776 := BSN.sin_dyadic_bound_f 27091963 67108864 2 1 67108864 33554432 Ns150p775 Ns150p107 Ns150p775 Ns150p775 Ns150p108 Ns150p775 26362050 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 27091963) qz361 0 1 Ns150p775 Ns150p107 Ns150p775 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 27091963) (BSN.sinOddQ 67108864) 0 1 Ns150p775 Ns150p108 Ns150p775 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p777 := nat_lit 595110653790637332157757635615114362924044557290756369429443930625 

noncomputable def Ns150p778 := nat_lit 94114253968712524841204249879090377427052481261110136812890625 

noncomputable def Ns150p779 := nat_lit 1558470765421434144896765191158828613713806231744224884474656090625 

noncomputable def Ns150p780 := BSN.sin_dyadic_bound_f 55809345 67108864 3 2 67108864 33554432 Ns150p777 Ns150p359 Ns150p778 Ns150p779 Ns150p362 Ns150p778 49595223 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 55809345) qz361 0 2 Ns150p777 Ns150p359 Ns150p778 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 55809345) (BSN.sinOddQ 67108864) 0 2 Ns150p779 Ns150p362 Ns150p778 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p781 := nat_lit 294964577849478657294650287104147644700520241803024363305368494336 

noncomputable def Ns150p782 := nat_lit 74896494432592932154786145486672295058625120270324916532224256 

noncomputable def Ns150p783 := nat_lit 884743940559570786019641289021469589511443475168532440083041034496 

noncomputable def Ns150p784 := BSN.cos_dyadic_bound_f 54238502 67108864 3 2 67108864 33554432 Ns150p781 Ns150p117 Ns150p782 Ns150p783 Ns150p120 Ns150p782 46358064 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 54238502) qz362 0 2 Ns150p781 Ns150p117 Ns150p782 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 54238502) (BSN.cosOddQ 67108864) 0 2 Ns150p783 Ns150p120 Ns150p782 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p785 := nat_lit 1541066527206049815792804471146153949752061916948113326163112890625 

noncomputable def Ns150p786 := nat_lit 630789563667135829492360843587569662826844146959423980712890625 

noncomputable def Ns150p787 := nat_lit 4035105340531812250019119316397928088944156796721410120172712890625 

noncomputable def Ns150p788 := BSN.sin_dyadic_bound_f 70792225 67108864 3 2 67108864 33554432 Ns150p785 Ns150p359 Ns150p786 Ns150p787 Ns150p362 Ns150p786 58374254 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 70792225) qz361 0 2 Ns150p785 Ns150p359 Ns150p786 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 70792225) (BSN.sinOddQ 67108864) 0 2 Ns150p787 Ns150p362 Ns150p786 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p789 := Ns150p742 36178 BSN.abs_quadSignPos (BSN.cos_quad_nat0 52 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 46358064 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 5 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 58374254 67108864) qz104 rfl rfl (Ns150p774 RS151to168.d9 RS151to168.d11 RS151to168.d13 RS151to168.d17 (Ns150p776 rfl rfl) (Ns150p780 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns150p773 rfl) RS151to168.d19 RS151to168.d21 RS151to168.d23 RS151to168.d25 RS151to168.d17 (Ns150p784 rfl rfl) (Ns150p788 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns150p790 := nat_lit 254383643390239559334133856961 

noncomputable def Ns150p791 := BSN.sin_dyadic_bound_f 22458063 67108864 2 1 67108864 33554432 Ns150p790 Ns150p107 Ns150p790 Ns150p790 Ns150p108 Ns150p790 22041218 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 22458063) qz361 0 1 Ns150p790 Ns150p107 Ns150p790 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 22458063) (BSN.sinOddQ 67108864) 0 1 Ns150p790 Ns150p108 Ns150p790 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p792 := nat_lit 211557968280457895874902464505915524697133714520426743330855852865 

noncomputable def Ns150p793 := nat_lit 11896172694996743994278450632566343776122207026881357656496961 

noncomputable def Ns150p794 := nat_lit 554061132645407351610658575262087933459712673504026519858892905281 

noncomputable def Ns150p795 := BSN.sin_dyadic_bound_f 43094903 67108864 3 2 67108864 33554432 Ns150p792 Ns150p359 Ns150p793 Ns150p794 Ns150p362 Ns150p793 40193502 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 43094903) qz361 0 2 Ns150p792 Ns150p359 Ns150p793 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 43094903) (BSN.sinOddQ 67108864) 0 2 Ns150p794 Ns150p362 Ns150p793 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p796 := Ns150p740 48465 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 53 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 22041218 67108864) BSN.abs_quadSignNeg qz650 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 40193502 67108864) qz104 rfl rfl (Ns150p789 rfl rfl) (Ns150p773 rfl) RS151to168.d27 RS151to168.d29 RS151to168.d31 RS151to168.d33 RS151to168.d17 (Ns150p791 rfl rfl) (Ns150p795 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns150p797 := nat_lit 333741146056500956187814560000 

noncomputable def Ns150p798 := BSN.cos_dyadic_bound_f 24035460 67108864 2 1 67108864 33554432 Ns150p797 Ns150p134 Ns150p797 Ns150p797 Ns150p135 Ns150p797 62850452 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 24035460) qz362 0 1 Ns150p797 Ns150p134 Ns150p797 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 24035460) (BSN.cosOddQ 67108864) 0 1 Ns150p797 Ns150p135 Ns150p797 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p799 := Ns150p738 Bool.true 84232535 48465 Bool.true 24035460 3537118876014220 1 Bool.false 62850452 Bool.false Bool.true 62011544 53992 BSN.abs_quadSignPos qz407 (BSN.sfrac_eq_quadSignPos_mul Bool.false 62850452 67108864) qz104 rfl (Ns150p796 rfl) (Ns150p773 rfl) RS151to168.d42 RS151to168.d44 RS151to168.d17 (Ns150p798 rfl rfl) rfl 

noncomputable def Ns150p800 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz101) qz101 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz101) qz101 8) 62011544 67108864 53992 67108864 62011544 67108864 53992 67108864 8323048545452032 7751443 4194304 6749 4194304 (Ns150p799 rfl rfl rfl rfl) 

noncomputable def Ns150p801 := @Enclosure.Real.IsNear.mulLit_ff qz680 (Zeta.RiemannSiegel.correction qz103) 1476101 4194304 1 4194304 13381188431181 17592186044416 46202421664029 1077521395220480000 19751985624454705281 73786976294838206464 

noncomputable abbrev qz682 := (@HPow.hPow Real Real Real qz6 qz102 qz8)

noncomputable def Ns150p802 := @Enclosure.Real.IsNear.mulLit_ff qz48 qz682 1 1 0 1 1476101 4194304 1 4194304 1476101 4194304 1 4194304 

noncomputable def Ns150p803 := @Enclosure.Real.IsNear.sqrt_image qz102 109369155791 1677721600 81919 1677721600 33864699 33864725 4194304 (@Enclosure.Real.IsNear.of_eq qz102 (@HMul.hMul Real Real Real qz4 qz101 qz2) Bool.false 109369155791 1677721600 81919 1677721600 (BSN.t_div_two_pi_mk qz101 409595 1000 qz104) (@Enclosure.Real.IsNear.mulLit_ff qz101 qz2 409595 1000 0 1 1335089 8388608 1 8388608 109369155791 1677721600 81919 1677721600 (Enclosure.Real.IsNear.const Bool.false 409595 1000) RS151to168.d36 rfl)) 

noncomputable abbrev qz869 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 409595 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz683 := qz869

noncomputable abbrev qz458 := qz683

noncomputable abbrev qz107 := qz458

noncomputable def Ns150p804 := @Enclosure.Real.IsNear.sqrt_image qz107 4233089 524288 13 4194304 11918004 11918010 4194304 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 67729424 8388608 26 8388608 4233089 524288 13 4194304 (Ns150p803 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns150p805 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz107) 11918007 4194304 3 4194304 1476100 1476102 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz107) Bool.false 23836014 8388608 6 8388608 11918007 4194304 3 4194304 (Ns150p804 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns150p806 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 2952202 8388608 2 8388608 1476101 4194304 1 4194304 (Ns150p805 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz108 := (@HMul.hMul Real Real Real qz340 qz338 qz452)

noncomputable abbrev qz684 := (@HMul.hMul Real Real Real qz839 qz868 qz868)

noncomputable abbrev qz459 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz684 qz679) qz638)

noncomputable abbrev qz109 := (Real.cos (@HMul.hMul Real Real Real qz340 qz338 qz459))

noncomputable def Ns150p807 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz103) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz108)) qz109) Bool.false 13381188431181 

noncomputable def Ns150p808 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz108)) qz109 9384203 8388608 211 

noncomputable def Ns150p809 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz108)) Bool.false 9384203 8388608 211 8388608 9384203 8388608 211 

noncomputable def Ns150p810 := @Enclosure.Real.IsNear.recentre' (Real.cos qz108) Bool.false 3749319 4194304 82457152 4110417920000 3749319 4194304 1288393 64225280000 

noncomputable def Ns150p811 := @Enclosure.Real.IsNear.cos_image qz108 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3899093) qz368) Bool.false 3899093 8388608 41 2097152 Bool.false 3749319 4194304 1 

noncomputable def Ns150p812 := nat_lit 350818980320237875822402331 

noncomputable def Ns150p813 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz103 884279719003555 140737488355328 1 500000000000000 38785 524288 13 4194304 34296788901552880675 73786976294838206464 Ns150p812 

noncomputable def Ns150p814 := @Enclosure.Real.IsNear.subLit_ff_p qz107 qz46 4233089 524288 13 4194304 8 1 0 1 38785 38785 524288 13 

noncomputable def Ns150p815 := @Ns150p814 4194304 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 67729424 8388608 26 8388608 4233089 524288 13 4194304 (Ns150p803 rfl rfl rfl rfl rfl rfl) rfl) qz410 

noncomputable def Ns150p816 := @Enclosure.Real.IsNear.recentre' qz108 Bool.false 34296788901552880675 73786976294838206464 Ns150p812 Ns150p151 3899093 8388608 41 2097152 (@Ns150p813 Ns150p151 RS151to168.d35 (Ns150p815 rfl rfl) rfl) 

noncomputable def Ns150p817 := nat_lit 231128965731308591520577201 

noncomputable def Ns150p818 := BSN.cos_dyadic_bound_f 3899093 8388608 2 1 4194304 1960000 Ns150p817 Ns150p175 Ns150p817 Ns150p817 Ns150p176 Ns150p817 3749319 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 3899093) (BSN.cosEvenQ 8388608) 0 1 Ns150p817 Ns150p175 Ns150p817 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 3899093) (BSN.cosOddQ 8388608) 0 1 Ns150p817 Ns150p176 Ns150p817 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p819 := @Enclosure.Real.IsNear.inv_image (Real.cos qz108) 3749319 4194304 1288393 64225280000 4691996 4692207 4194304 (Ns150p810 (@Ns150p811 1960000 (Ns150p816 rfl) (Enclosure.sfrac_false_div 3899093 8388608) (Ns150p818 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns150p820 := @Enclosure.Real.IsNear.recentre' qz109 Bool.false 2851854 4194304 

noncomputable abbrev qz110 := (@HMul.hMul Real Real Real qz340 qz338 qz459)

noncomputable def Ns150p821 := @Enclosure.Real.IsNear.cos_image qz110 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 3452425)) qz359) Bool.true 3452425 4194304 

noncomputable def Ns150p822 := nat_lit 31843003796615981957303645 

noncomputable def Ns150p823 := nat_lit 38685626227668133590597632 

noncomputable def Ns150p824 := nat_lit 1689150239514329727342014861392399 

noncomputable def Ns150p825 := @Enclosure.Real.IsNear.recentre' qz110 Bool.true Ns150p822 Ns150p823 Ns150p824 

noncomputable abbrev qz111 := qz459

noncomputable def Ns150p826 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz111 884279719003555 140737488355328 1 500000000000000 36010103039 

noncomputable abbrev qz460 := (@HSub.hSub Real Real Real qz634 qz684 qz679)

noncomputable abbrev qz112 := qz460

noncomputable def Ns150p827 := @Enclosure.Real.IsNear.subLit_tf qz112 qz25 18830233855 274877906944 62593401 17592186044416 1 16 

noncomputable abbrev qz461 := qz684

noncomputable abbrev qz113 := qz461

noncomputable def Ns150p828 := @Enclosure.Real.IsNear.subLit_ff_n qz113 qz103 1504276225 274877906944 8067449 17592186044416 38785 524288 13 4194304 

noncomputable def Ns150p829 := @Enclosure.Real.IsNear.mulLit_ff qz103 qz103 38785 524288 13 4194304 38785 524288 13 4194304 1504276225 274877906944 

noncomputable def Ns150p830 := nat_lit 73886409539022619144098498839945361539770524729337890625 

noncomputable def Ns150p831 := nat_lit 20183385832248011241857547071536553822168121337890625 

noncomputable def Ns150p832 := nat_lit 221618861845403361409811781425693011511667237945337890625 

noncomputable def Ns150p833 := BSN.cos_dyadic_bound_f 3452425 4194304 3 2 4194304 1960000 Ns150p830 Ns150p626 Ns150p831 Ns150p832 Ns150p629 Ns150p831 2851854 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3452425) (BSN.cosEvenQ 4194304) 0 2 Ns150p830 Ns150p626 Ns150p831 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3452425) (BSN.cosOddQ 4194304) 0 2 Ns150p832 Ns150p629 Ns150p831 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p834 := @Ns150p820 378828608 16441671680000 1425927 2097152 5919197 256901120000 (@Ns150p821 189 8388608 Bool.false 2851854 4194304 1 1960000 (@Ns150p825 Ns150p169 3452425 4194304 189 8388608 (@Ns150p826 274877906944 62593401 17592186044416 Ns150p822 Ns150p823 Ns150p824 Ns150p169 RS151to168.d35 (@Ns150p827 0 1 576161648624 36010103039 274877906944 62593401 17592186044416 (@Ns150p828 9872465647370240 18830233855 274877906944 62593401 17592186044416 (@Ns150p829 8067449 17592186044416 (Ns150p815 rfl rfl) (Ns150p815 rfl rfl) rfl) (Ns150p815 rfl rfl) rfl rfl) qz373 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 3452425 4194304) (BSN.cos_neg_of_bound 3452425 4194304 Bool.false 2851854 4194304 1 1960000 (Ns150p833 rfl rfl)) rfl rfl) 

noncomputable def Ns150p835 := @Ns150p801 8627385601815796401 564931537257355018240000 (Ns150p802 qz61 (@Enclosure.Real.IsNear.of_eq qz682 (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 1476101 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz102 (BSN.t_div_two_pi_nonneg qz101 409595 1000 qz104)) Ns150p806) rfl) (@Ns150p807 17592186044416 46202421664029 1077521395220480000 (BSN.correction_mk qz103 (BSN.cos_two_pi_p_ne_zero_mk qz101 409595 1000 8 qz104 rfl rfl (@BSN.floor_sqrt_eq_dec qz101 409595 1000 8 qz104 rfl rfl rfl))) (@Ns150p808 8388608 1425927 2097152 5919197 256901120000 13381188431181 17592186044416 46202421664029 1077521395220480000 (@Ns150p809 8388608 (Ns150p819 rfl rfl rfl rfl rfl) rfl) (Ns150p834 rfl) rfl)) 

noncomputable def Ns150p836 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz101) (hardyZApproximantRS₀ qz101) Bool.true 156116812993140797569 73786976294838206464 917651372644693236401 564931537257355018240000 (@Eq.refl Real (hardyZApproximantRS₀ qz101)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz101) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz101) qz101 8) (@HMul.hMul Real Real Real qz4 qz680 (Zeta.RiemannSiegel.correction qz103))) Bool.true 156116812993140797569 73786976294838206464 917651372644693236401 564931537257355018240000 (BSN.hardyZApproximantRS₀_eq qz101 8 (@BSN.floor_sqrt_eq_dec qz101 409595 1000 8 qz104 rfl rfl rfl)) (@Ns150p737 156116812993140797569 73786976294838206464 917651372644693236401 564931537257355018240000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz101) qz101 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz101) qz101 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz101) qz101 8)) Bool.true 7751443 4194304 6749 4194304 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz101) qz101 8) (Ns150p800 (Ns150p799 rfl rfl rfl rfl) rfl rfl)) (Ns150p835 rfl) rfl rfl)) 

theorem RS151to168.d49 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz101) Bool.true 156116812993140797569 73786976294838206464 917651372644693236401 564931537257355018240000 := Ns150p836 

noncomputable def Ns150p837 := nat_lit 1989871539216032110594752512 

noncomputable abbrev qz870 := (Enclosure.sfrac Bool.false 411099 1000)

noncomputable abbrev qz685 := qz870

noncomputable abbrev qz462 := qz685

noncomputable abbrev qz114 := qz462

noncomputable abbrev qz871 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 411099 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz686 := qz871

noncomputable abbrev qz463 := qz686

noncomputable abbrev qz115 := qz463

noncomputable abbrev qz872 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 411099 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz687 := qz872

noncomputable abbrev qz464 := qz687

noncomputable abbrev qz116 := qz464

noncomputable abbrev qz688 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz115 qz8))

noncomputable def Ns150p838 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 8) (@HMul.hMul Real Real Real qz4 qz688 (Zeta.RiemannSiegel.correction qz116)) 31284339 16777216 54193 33554432 18984391747513430749 73786976294838206464 290157801844316809 18077809192235360583680 Ns150p837 

noncomputable def Ns150p839 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.cos BSN.quadSignPos 7 8 411099 1000 128 67108864 33554432 1125899906842624 Bool.false 43852385933 1272 139548959 35 23726568 8 

noncomputable def Ns150p840 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 411099 1000 52 93 67108864 33554432 1125899906842624 Bool.false 43852385933 1272 

noncomputable def Ns150p841 := Ns150p840 120242927 35 27397080 8 130587807 35 25364760 8 Bool.false 47611720 36314 Bool.true 97814546 Bool.true 28595729 3537118876014220 1 Bool.false 7583577 Bool.false Bool.false 27738199 Bool.true Bool.false 40223651 

noncomputable def Ns150p842 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 411099 1000 53 5 67108864 33554432 1125899906842624 Bool.false 43852385933 1272 

noncomputable def Ns150p843 := Ns150p842 93032624 35 33554424 8 108007536 35 30011992 8 Bool.false 67175730 21460 Bool.false 19806314 Bool.true 22332323 3537118876014220 1 Bool.false 19520022 Bool.true Bool.false 21922415 Bool.true Bool.false 47611720 

noncomputable def Ns150p844 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 411099 1000 234 128 67108864 33554432 1125899906842624 Bool.false 43852385933 1272 

noncomputable def Ns150p845 := Ns150p844 46516304 35 47453136 16 73726608 35 38745320 8 Bool.false 67108856 1315 Bool.false 62620321 Bool.false 50413406 3537118876014220 1 Bool.false 39952164 Bool.true Bool.false 49047042 Bool.false Bool.false 67175730 

noncomputable def Ns150p846 := nat_lit 56821612700471978705311885299355553122282164599151614507 

noncomputable def Ns150p847 := nat_lit 86956132437634343714475371023898458632449985347584000 

noncomputable def Ns150p848 := nat_lit 5636051679209478047377274639520000 

noncomputable def Ns150p849 := nat_lit 13901860852504716586791004204128194880 

noncomputable abbrev qz465 := (@Eq.refl Real qz685)

noncomputable abbrev qz117 := qz465

noncomputable def Ns150p850 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz114 411099 1000 676010551204 16000000 822198 4000 2000 Ns150p848 Ns150p849 qz117 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns150p851 := nat_lit 163646244577359298671298229662143992992172634045556649780160 

noncomputable abbrev qz466 := (Enclosure.sfrac Bool.false 411099 2000)

noncomputable abbrev qz689 := (Real.log (Enclosure.sfrac Bool.false 676010551204 16000000))

noncomputable abbrev qz118 := (@HSub.hSub Real Real Real qz344 (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 411099 4000) qz689) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 822198)))))) qz466)

noncomputable abbrev qz467 := (@HSub.hSub Real Real Real qz11 qz118 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 411099 2000) (Real.log Real.pi)))

noncomputable def Ns150p852 := @Enclosure.Real.IsNear.addLit_ft_p qz467 (Enclosure.sfrac Bool.true Ns150p848 Ns150p849) 11771542518205819200707 18014398509481984000 190004164797903843 10035200000000000000000 Ns150p848 Ns150p849 0 1 Ns150p851 

noncomputable def Ns150p853 := nat_lit 789974845924491844748834766848000 

noncomputable abbrev qz468 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 411099 2000) (Real.log Real.pi))

noncomputable def Ns150p854 := @Enclosure.Real.IsNear.subLit_ff_p qz118 qz468 16010306257734677636291 18014398509481984000 261936935436453 39200000000000000000 15790625436339 67108864000 411099 33554432000 Ns150p853 11771542518205819200707 18014398509481984000 

noncomputable def Ns150p855 := nat_lit 32020612515469355272582000 

noncomputable abbrev qz119 := (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 411099 4000) qz689) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 822198))))))

noncomputable def Ns150p856 := @Enclosure.Real.IsNear.subLit_ff_p qz119 qz466 19713156864159444706499 18014398509481984000 261936935436453 39200000000000000000 411099 2000 0 1 Ns150p855 16010306257734677636291 18014398509481984000 261936935436453 39200000000000000000 

noncomputable def Ns150p857 := nat_lit 44390082953862305307129819250926026752 

noncomputable def Ns150p858 := nat_lit 12876722536430008381997056 

noncomputable def Ns150p859 := nat_lit 4071421480853946714908176530574529411169596456331951827468187240744232947655188366422494948159979520 

noncomputable def Ns150p860 := nat_lit 21894640761312243420864043444613138087670525014075861230429032912512901527384447092228296955920384 

noncomputable def Ns150p861 := nat_lit 29484270902303830140069555916084658966002362948160758932659773894729112293222297459235553280 

noncomputable def Ns150p862 := BSN.log_dyadic_bound 151722551204 1200298551204 5 4 Ns150p859 33554432 15680000 Ns150p860 Ns150p861 8528447 1352021102408 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 151722551204) (BSN.artanhQ 1200298551204) 0 4 Ns150p860 Ns150p859 Ns150p861 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns150p863 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 411099 4000) qz689 411099 4000 0 1 47969529540948601 4503599627370496 625000147 9800000000000000 19720225624754428922499 18014398509481984000 256936935431553 39200000000000000000 (Enclosure.Real.IsNear.const Bool.false 411099 4000) (BSN.isNear_log_sfrac 676010551204 16000000 47969529540948601 4503599627370496 625000147 9800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 676010551204) qz352)) Bool.false Ns150p858 Ns150p86 1000000235200000 15680000000000000000000 47969529540948601 4503599627370496 625000147 9800000000000000 (BSN.log_rat_reduce_isNear 676010551204 16000000 15 1352021102408 1048576000000 8528447 33554432 24973259072661432 36028797018963968 15680000 1000000000000000 rfl rfl rfl rfl (Ns150p862 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns150p864 := BSN.arctan_dyadic_bound_f 1000 822198 1 0 4194304 1960000 0 1 1 0 1 1 5101 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 822198) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 822198) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz469 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 822198)))

noncomputable def Ns150p865 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz469 884279719003555 562949953421312 1 2000000000000000 5101 4194304 1 1960000 3706066354823084638208 883595074373027 562949953421312 50000000049 98000000000000000 qz16 (Ns150p864 rfl) rfl rfl 

noncomputable def Ns150p866 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 411099 4000) qz689) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz469)) 19720225624754428922499 18014398509481984000 256936935431553 39200000000000000000 883595074373027 2251799813685248 50000000049 392000000000000000 Ns150p857 19713156864159444706499 18014398509481984000 261936935436453 39200000000000000000 (Ns150p863 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz469) 1 4 0 1 883595074373027 562949953421312 50000000049 98000000000000000 883595074373027 2251799813685248 50000000049 392000000000000000 qz355 Ns150p865 rfl) 

noncomputable def Ns150p867 := @Ns150p852 Ns150p846 Ns150p847 190004164797903843 10035200000000000000000 (@Ns150p854 190004164797903843 10035200000000000000000 (Ns150p856 (Ns150p866 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 411099 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz466 (Real.log Real.pi) 411099 2000 0 1 38410761 33554432 1 16777216 15790625436339 67108864000 411099 33554432000 (Enclosure.Real.IsNear.const Bool.false 411099 2000) RS151to168.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns150p848 Ns150p849) 

noncomputable def Ns150p868 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz114) Bool.false Ns150p846 Ns150p847 190004164797903843 10035200000000000000000 5481548241 8388608 5 262144 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz114) (@HAdd.hAdd Real Real Real qz356 qz467 (Enclosure.sfrac Bool.true Ns150p848 Ns150p849)) Bool.false Ns150p846 Ns150p847 190004164797903843 10035200000000000000000 Ns150p850 (Ns150p867 rfl rfl)) 

noncomputable def Ns150p869 := nat_lit 1899217419051704938135552 

noncomputable def Ns150p870 := nat_lit 140060167734292604498809360997941092494666278826354099289907200773296670978082566734080 

noncomputable def Ns150p871 := nat_lit 281552296692519046974337675278731551666910780406959075336287084739240131954832998656 

noncomputable def Ns150p872 := nat_lit 366368402252311790468447017806061105449998588995982802494450584840484892348003659448576 

noncomputable def Ns150p873 := BSN.sin_dyadic_bound_f 26989502814 17179869184 3 2 8388608 3923829 Ns150p870 Ns150p98 Ns150p871 Ns150p872 Ns150p101 Ns150p871 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26989502814) qz357 0 2 Ns150p870 Ns150p98 Ns150p871 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26989502814) qz358 0 2 Ns150p872 Ns150p101 Ns150p871 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p874 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz114) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5481548241) qz368) Bool.false 5481548241 8388608 5 262144 Bool.false 8388607 8388608 1 1960000 (Ns150p868 rfl) (Enclosure.sfrac_false_div 5481548241 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5481548241) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns150p869) qz369) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 103 1000000000000000 3920000 1960000 (BSN.sin_reduce_arg_pos_rat_q3 5481548241 8388608 226375608064910080 72057594037927936 103 Ns150p869 Ns150p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns150p869 Ns150p86 26989502814 17179869184 3923829 3920000 (Ns150p873 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns150p875 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz114) Bool.false Ns150p846 Ns150p847 190004164797903843 10035200000000000000000 43852385933 67108864 1272 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz114) (@HAdd.hAdd Real Real Real qz356 qz467 (Enclosure.sfrac Bool.true Ns150p848 Ns150p849)) Bool.false Ns150p846 Ns150p847 190004164797903843 10035200000000000000000 Ns150p850 (Ns150p867 rfl rfl)) 

noncomputable def Ns150p876 := Ns150p845 21460 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 234 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 39952164 67108864) BSN.abs_quadSignPos qz407 (BSN.sfrac_eq_quadSignPos_mul Bool.false 49047042 67108864) qz117 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 1) Bool.false 8388607 8388608 157221 8028160000 67108856 67108864 1315 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz114)) Bool.false 8388607 8388608 157221 8028160000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz114) qz114) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz114)) Bool.false 8388607 8388608 10062144 513802240000 8388607 8388608 157221 8028160000 (Ns150p874 rfl rfl) rfl)) rfl) (Ns150p875 rfl) RS151to168.d7 

noncomputable def Ns150p877 := nat_lit 524186614754885766203927326213251903969783577851484668254734583041 

noncomputable def Ns150p878 := nat_lit 236440743476928873505840155029893984626039494813385925807637761 

noncomputable def Ns150p879 := nat_lit 1572086962777703440864770298329695923940098654564827232912588473601 

noncomputable def Ns150p880 := BSN.cos_dyadic_bound_f 62620321 67108864 3 2 67108864 33554432 Ns150p877 Ns150p117 Ns150p878 Ns150p879 Ns150p120 Ns150p878 39952164 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 62620321) qz362 0 2 Ns150p877 Ns150p117 Ns150p878 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 62620321) (BSN.cosOddQ 67108864) 0 2 Ns150p879 Ns150p120 Ns150p878 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p881 := nat_lit 220138148444341661807308650801693663767071400857183723180831703296 

noncomputable def Ns150p882 := nat_lit 41722307518096751448244160283607973097529967044265824028098816 

noncomputable def Ns150p883 := nat_lit 660331000717988791919029464084513775355019142637462637894438912256 

noncomputable def Ns150p884 := BSN.cos_dyadic_bound_f 50413406 67108864 3 2 67108864 33554432 Ns150p881 Ns150p117 Ns150p882 Ns150p883 Ns150p120 Ns150p882 49047042 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 50413406) qz362 0 2 Ns150p881 Ns150p117 Ns150p882 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 50413406) (BSN.cosOddQ 67108864) 0 2 Ns150p883 Ns150p120 Ns150p882 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p885 := nat_lit 153891502368091405207281427216 

noncomputable def Ns150p886 := BSN.sin_dyadic_bound_f 19806314 67108864 2 1 67108864 33554432 Ns150p885 Ns150p107 Ns150p885 Ns150p885 Ns150p108 Ns150p885 19520022 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 19806314) qz361 0 1 Ns150p885 Ns150p107 Ns150p885 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 19806314) (BSN.sinOddQ 67108864) 0 1 Ns150p885 Ns150p108 Ns150p885 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p887 := nat_lit 248734256750890679215855116241 

noncomputable def Ns150p888 := BSN.sin_dyadic_bound_f 22332323 67108864 2 1 67108864 33554432 Ns150p887 Ns150p107 Ns150p887 Ns150p887 Ns150p108 Ns150p887 21922415 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 22332323) qz361 0 1 Ns150p887 Ns150p107 Ns150p887 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 22332323) (BSN.sinOddQ 67108864) 0 1 Ns150p887 Ns150p108 Ns150p887 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p889 := Ns150p843 36314 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 53 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 19520022 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 5 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 21922415 67108864) qz117 rfl rfl (Ns150p876 RS151to168.d9 RS151to168.d11 RS151to168.d13 RS151to168.d17 (Ns150p880 rfl rfl) (Ns150p884 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns150p875 rfl) RS151to168.d19 RS151to168.d21 RS151to168.d23 RS151to168.d25 RS151to168.d17 (Ns150p886 rfl rfl) (Ns150p888 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns150p890 := nat_lit 753605742662204477800412571852580431707618807559823071468402833882173927893719024307926073948291076096 

noncomputable def Ns150p891 := nat_lit 767081170389143993253411183566905621624753243862738642619643920474686824914861049782274639138816 

noncomputable def Ns150p892 := nat_lit 4563704707145667150865741450320031855739723875836206966501281404956076229577273974496245713327044300800 

noncomputable def Ns150p893 := BSN.cos_dyadic_bound_f 97814546 67108864 4 3 67108864 33554432 Ns150p890 Ns150p128 Ns150p891 Ns150p892 Ns150p131 Ns150p891 7583577 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 97814546) qz362 0 3 Ns150p890 Ns150p128 Ns150p891 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 97814546) (BSN.cosOddQ 67108864) 0 3 Ns150p892 Ns150p131 Ns150p891 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p894 := nat_lit 668658993896598003058111356481 

noncomputable def Ns150p895 := BSN.sin_dyadic_bound_f 28595729 67108864 2 1 67108864 33554432 Ns150p894 Ns150p107 Ns150p894 Ns150p894 Ns150p108 Ns150p894 27738199 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 28595729) qz361 0 1 Ns150p894 Ns150p107 Ns150p894 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 28595729) (BSN.sinOddQ 67108864) 0 1 Ns150p894 Ns150p108 Ns150p894 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p896 := Ns150p841 48646 BSN.abs_quadSignPos (BSN.cos_quad_nat0 52 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 7583577 67108864) BSN.abs_quadSignNeg qz650 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 27738199 67108864) qz117 rfl rfl (Ns150p889 rfl rfl) (Ns150p875 rfl) RS151to168.d27 RS151to168.d29 RS151to168.d31 RS151to168.d33 RS151to168.d17 (Ns150p893 rfl rfl) (Ns150p895 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns150p897 := nat_lit 280516050937057435234430458896 

noncomputable def Ns150p898 := BSN.cos_dyadic_bound_f 23013858 67108864 2 1 67108864 33554432 Ns150p897 Ns150p134 Ns150p897 Ns150p897 Ns150p135 Ns150p897 63201277 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 23013858) qz362 0 1 Ns150p897 Ns150p134 Ns150p897 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 23013858) (BSN.cosOddQ 67108864) 0 1 Ns150p897 Ns150p135 Ns150p897 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p899 := Ns150p839 Bool.false 40223651 48646 Bool.true 23013858 3537118876014220 1 Bool.false 63201277 Bool.false Bool.false 62568678 54193 BSN.abs_quadSignPos qz407 (BSN.sfrac_eq_quadSignPos_mul Bool.false 63201277 67108864) qz117 rfl (Ns150p896 rfl) (Ns150p875 rfl) RS151to168.d42 RS151to168.d44 RS151to168.d17 (Ns150p898 rfl rfl) rfl 

noncomputable def Ns150p900 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 8) 62568678 67108864 54193 67108864 62568678 67108864 54193 67108864 8397825805123584 31284339 16777216 54193 33554432 (Ns150p899 rfl rfl rfl rfl) 

noncomputable def Ns150p901 := @Enclosure.Real.IsNear.mulLit_ff qz688 (Zeta.RiemannSiegel.correction qz116) 2949499 8388608 1 8388608 6436480143751 8796093022208 24460151229793 538760697610240000 18984391747513430749 73786976294838206464 

noncomputable abbrev qz690 := (@HPow.hPow Real Real Real qz6 qz115 qz8)

noncomputable def Ns150p902 := @Enclosure.Real.IsNear.mulLit_ff qz48 qz690 1 1 0 1 2949499 8388608 1 8388608 2949499 8388608 1 8388608 

noncomputable def Ns150p903 := @Enclosure.Real.IsNear.sqrt_image qz115 548853752811 8388608000 411099 8388608000 33926816 33926842 4194304 (@Enclosure.Real.IsNear.of_eq qz115 (@HMul.hMul Real Real Real qz4 qz114 qz2) Bool.false 548853752811 8388608000 411099 8388608000 (BSN.t_div_two_pi_mk qz114 411099 1000 qz117) (@Enclosure.Real.IsNear.mulLit_ff qz114 qz2 411099 1000 0 1 1335089 8388608 1 8388608 548853752811 8388608000 411099 8388608000 (Enclosure.Real.IsNear.const Bool.false 411099 1000) RS151to168.d36 rfl)) 

noncomputable abbrev qz873 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 411099 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz691 := qz873

noncomputable abbrev qz470 := qz691

noncomputable abbrev qz120 := qz470

noncomputable def Ns150p904 := @Enclosure.Real.IsNear.sqrt_image qz120 33926829 4194304 13 4194304 11928930 11928935 4194304 (@Enclosure.Real.IsNear.recentre' qz120 Bool.false 67853658 8388608 26 8388608 33926829 4194304 13 4194304 (Ns150p903 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns150p905 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz120) 23857865 8388608 5 8388608 1474749 1474750 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz120) Bool.false 23857865 8388608 5 8388608 23857865 8388608 5 8388608 (Ns150p904 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns150p906 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz120)) Bool.false 2949499 8388608 1 8388608 2949499 8388608 1 8388608 (Ns150p905 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz121 := (@HMul.hMul Real Real Real qz340 qz338 qz464)

noncomputable abbrev qz692 := (@HMul.hMul Real Real Real qz839 qz872 qz872)

noncomputable abbrev qz471 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz692 qz687) qz638)

noncomputable abbrev qz122 := (Real.cos (@HMul.hMul Real Real Real qz340 qz338 qz471))

noncomputable def Ns150p907 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz116) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz121)) qz122) Bool.false 6436480143751 

noncomputable def Ns150p908 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz121)) qz122 9887689 8388608 237 

noncomputable def Ns150p909 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz121)) Bool.false 9887689 8388608 237 8388608 9887689 8388608 237 

noncomputable def Ns150p910 := @Enclosure.Real.IsNear.recentre' (Real.cos qz121) Bool.false 3558402 4194304 331788608 16441671680000 1779201 2097152 5184197 256901120000 

noncomputable def Ns150p911 := @Enclosure.Real.IsNear.cos_image qz121 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2339839) qz359) Bool.false 2339839 4194304 165 8388608 Bool.false 3558402 4194304 1 

noncomputable def Ns150p912 := nat_lit 70163796064154291357890719 

noncomputable def Ns150p913 := nat_lit 3602879701896396800000000000000 

noncomputable def Ns150p914 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz116 884279719003555 140737488355328 1 500000000000000 372397 4194304 13 4194304 329303114517766871335 590295810358705651712 Ns150p912 

noncomputable def Ns150p915 := @Enclosure.Real.IsNear.subLit_ff_p qz120 qz46 33926829 4194304 13 4194304 8 1 0 1 372397 372397 4194304 13 

noncomputable def Ns150p916 := @Ns150p915 4194304 (@Enclosure.Real.IsNear.recentre' qz120 Bool.false 67853658 8388608 26 8388608 33926829 4194304 13 4194304 (Ns150p903 rfl rfl rfl rfl rfl rfl) rfl) qz410 

noncomputable def Ns150p917 := @Enclosure.Real.IsNear.recentre' qz121 Bool.false 329303114517766871335 590295810358705651712 Ns150p912 Ns150p913 2339839 4194304 165 8388608 (@Ns150p914 Ns150p913 RS151to168.d35 (Ns150p916 rfl rfl) rfl) 

noncomputable def Ns150p918 := nat_lit 15585395875451528353682637960660930487650131679706767361 

noncomputable def Ns150p919 := nat_lit 898437360961572277308054640894004747014683001774081 

noncomputable def Ns150p920 := nat_lit 46754390751632661916493297772701003453456365673116753921 

noncomputable def Ns150p921 := BSN.cos_dyadic_bound_f 2339839 4194304 3 2 4194304 1960000 Ns150p918 Ns150p626 Ns150p919 Ns150p920 Ns150p629 Ns150p919 3558402 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2339839) (BSN.cosEvenQ 4194304) 0 2 Ns150p918 Ns150p626 Ns150p919 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2339839) (BSN.cosOddQ 4194304) 0 2 Ns150p920 Ns150p629 Ns150p919 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p922 := @Enclosure.Real.IsNear.inv_image (Real.cos qz121) 1779201 2097152 5184197 256901120000 4943726 4943963 4194304 (Ns150p910 (@Ns150p911 1960000 (Ns150p917 rfl) (Enclosure.sfrac_false_div 2339839 4194304) (Ns150p921 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns150p923 := @Enclosure.Real.IsNear.recentre' qz122 Bool.false 2603836 4194304 

noncomputable abbrev qz123 := (@HMul.hMul Real Real Real qz340 qz338 qz471)

noncomputable def Ns150p924 := @Enclosure.Real.IsNear.cos_image qz123 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7558385)) qz368) Bool.true 7558385 8388608 

noncomputable def Ns150p925 := nat_lit 2230841711748157468704079525 

noncomputable def Ns150p926 := nat_lit 1732733884716976777932605189240541 

noncomputable def Ns150p927 := @Enclosure.Real.IsNear.recentre' qz123 Bool.true Ns150p925 Ns150p268 Ns150p926 

noncomputable abbrev qz124 := qz471

noncomputable def Ns150p928 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz124 884279719003555 140737488355328 1 500000000000000 2522778328855 

noncomputable abbrev qz472 := (@HSub.hSub Real Real Real qz634 qz692 qz687)

noncomputable abbrev qz125 := qz472

noncomputable def Ns150p929 := @Enclosure.Real.IsNear.subLit_tf qz125 qz25 1423266701079 17592186044416 64208443 17592186044416 1 16 

noncomputable abbrev qz473 := qz692

noncomputable abbrev qz126 := qz473

noncomputable def Ns150p930 := @Enclosure.Real.IsNear.subLit_ff_n qz126 qz116 138679525609 17592186044416 9682491 17592186044416 372397 4194304 13 4194304 

noncomputable def Ns150p931 := @Enclosure.Real.IsNear.mulLit_ff qz116 qz116 372397 4194304 13 4194304 372397 4194304 13 4194304 138679525609 17592186044416 

noncomputable def Ns150p932 := nat_lit 27161595253199340971041224624221126927794761462173295690625 

noncomputable def Ns150p933 := nat_lit 988643523323402220304136834155207460536120982503085435781120 

noncomputable def Ns150p934 := nat_lit 10652022564572474281467157329217497526549471494562890625 

noncomputable def Ns150p935 := nat_lit 81463481714468877964560739558004945788331185443530761290625 

noncomputable def Ns150p936 := nat_lit 44488958549553099913686157536984335724125444212638844610150400 

noncomputable def Ns150p937 := BSN.cos_dyadic_bound_f 7558385 8388608 3 2 4194304 1960000 Ns150p932 Ns150p933 Ns150p934 Ns150p935 Ns150p936 Ns150p934 2603836 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 7558385) (BSN.cosEvenQ 8388608) 0 2 Ns150p932 Ns150p933 Ns150p934 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 7558385) (BSN.cosOddQ 8388608) 0 2 Ns150p935 Ns150p936 Ns150p934 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p938 := @Ns150p923 194314304 8220835840000 650959 1048576 3036161 128450560000 (@Ns150p924 97 4194304 Bool.false 2603836 4194304 1 1960000 (@Ns150p927 Ns150p169 7558385 8388608 97 4194304 (@Ns150p928 17592186044416 64208443 17592186044416 Ns150p925 Ns150p268 Ns150p926 Ns150p169 RS151to168.d35 (@Ns150p929 0 1 40364453261680 2522778328855 17592186044416 64208443 17592186044416 (@Ns150p930 5969613217402454016 1423266701079 17592186044416 64208443 17592186044416 (@Ns150p931 9682491 17592186044416 (Ns150p916 rfl rfl) (Ns150p916 rfl rfl) rfl) (Ns150p916 rfl rfl) rfl rfl) qz373 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7558385 8388608) (BSN.cos_neg_of_bound 7558385 8388608 Bool.false 2603836 4194304 1 1960000 (Ns150p937 rfl rfl)) rfl rfl) 

noncomputable def Ns150p939 := @Ns150p901 290157801844316809 18077809192235360583680 (Ns150p902 qz61 (@Enclosure.Real.IsNear.of_eq qz690 (@Inv.inv Real Real.instInv (Real.sqrt qz120)) Bool.false 2949499 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz115 (BSN.t_div_two_pi_nonneg qz114 411099 1000 qz117)) Ns150p906) rfl) (@Ns150p907 8796093022208 24460151229793 538760697610240000 (BSN.correction_mk qz116 (BSN.cos_two_pi_p_ne_zero_mk qz114 411099 1000 8 qz117 rfl rfl (@BSN.floor_sqrt_eq_dec qz114 411099 1000 8 qz117 rfl rfl rfl))) (@Ns150p908 8388608 650959 1048576 3036161 128450560000 6436480143751 8796093022208 24460151229793 538760697610240000 (@Ns150p909 8388608 (Ns150p922 rfl rfl rfl rfl rfl) rfl) (Ns150p938 rfl) rfl)) 

noncomputable def Ns150p940 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz114) (hardyZApproximantRS₀ qz114) Bool.false 118605586243631369507 73786976294838206464 29487216287436053129 18077809192235360583680 (@Eq.refl Real (hardyZApproximantRS₀ qz114)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz114) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 8) (@HMul.hMul Real Real Real qz4 qz688 (Zeta.RiemannSiegel.correction qz116))) Bool.false 118605586243631369507 73786976294838206464 29487216287436053129 18077809192235360583680 (BSN.hardyZApproximantRS₀_eq qz114 8 (@BSN.floor_sqrt_eq_dec qz114 411099 1000 8 qz117 rfl rfl rfl)) (@Ns150p838 118605586243631369507 73786976294838206464 29487216287436053129 18077809192235360583680 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 8)) Bool.false 31284339 16777216 54193 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz114) qz114 8) (Ns150p900 (Ns150p899 rfl rfl rfl rfl) rfl rfl)) (Ns150p939 rfl) rfl rfl)) 

theorem RS151to168.d50 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz114) Bool.false 118605586243631369507 73786976294838206464 29487216287436053129 18077809192235360583680 := Ns150p940 

noncomputable def Ns150p941 := nat_lit 770822897937981911418798080 

noncomputable abbrev qz874 := (Enclosure.sfrac Bool.false 412601 1000)

noncomputable abbrev qz693 := qz874

noncomputable abbrev qz474 := qz693

noncomputable abbrev qz127 := qz474

noncomputable abbrev qz875 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 412601 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz694 := qz875

noncomputable abbrev qz475 := qz694

noncomputable abbrev qz128 := qz475

noncomputable abbrev qz876 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 412601 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz695 := qz876

noncomputable abbrev qz476 := qz695

noncomputable abbrev qz129 := qz476

noncomputable abbrev qz696 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz128 qz8))

noncomputable def Ns150p942 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz127) qz127 8) (@HMul.hMul Real Real Real qz4 qz696 (Zeta.RiemannSiegel.correction qz129)) 16742575 16777216 3399 2097152 9127313233507068105 36893488147419103232 5700682872976943863 322818021289917153280000 Ns150p941 

noncomputable def Ns150p943 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz127) qz127 Real.cos BSN.quadSignPos 7 8 412601 1000 128 67108864 33554432 1125899906842624 Bool.false 44063192875 1276 139548959 35 23726568 8 

noncomputable def Ns150p944 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz127) qz127 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 412601 1000 52 93 67108864 33554432 1125899906842624 Bool.false 44063192875 1276 

noncomputable def Ns150p945 := Ns150p944 120242927 35 27397080 8 130587807 35 25364760 8 Bool.true 65371102 36440 Bool.true 67612480 Bool.true 13931673 3537118876014220 1 Bool.false 35834278 Bool.false Bool.false 13831819 Bool.true Bool.true 55969754 

noncomputable def Ns150p946 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz127) qz127 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 412601 1000 53 4 67108864 33554432 1125899906842624 Bool.false 44063192875 1276 

noncomputable def Ns150p947 := Ns150p946 93032624 35 33554424 8 108007536 35 30011992 8 Bool.true 44041914 21532 Bool.false 90878255 Bool.true 79167057 3537118876014220 1 Bool.false 65540714 Bool.true Bool.false 25583219 Bool.false Bool.true 65371102 

noncomputable def Ns150p948 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz127) qz127 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 412601 1000 235 129 67108864 33554432 1125899906842624 Bool.false 44063192875 1276 

noncomputable def Ns150p949 := Ns150p948 46516304 35 47453136 16 73726608 35 38745320 8 Bool.true 67108856 1315 Bool.false 98145417 Bool.false 45068626 3537118876014220 1 Bool.false 66715578 Bool.false Bool.false 41756452 Bool.true Bool.true 44041914 

noncomputable def Ns150p950 := nat_lit 525220806369886031570993479155037548544200249896515726073 

noncomputable def Ns150p951 := nat_lit 799918693228901404591007970654160067594987772051456000 

noncomputable def Ns150p952 := nat_lit 5739766618320073103003342240480000 

noncomputable def Ns150p953 := nat_lit 14209410416812698311712778765321730880 

noncomputable abbrev qz697 := (@Eq.refl Real qz874)

noncomputable abbrev qz477 := qz697

noncomputable abbrev qz130 := qz477

noncomputable def Ns150p954 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz127 412601 1000 680959340804 16000000 825202 4000 2000 Ns150p952 Ns150p953 qz130 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns150p955 := nat_lit 168070658038363530102717913329612015534144079966885032343360 

noncomputable abbrev qz478 := (Enclosure.sfrac Bool.false 412601 2000)

noncomputable abbrev qz698 := (Real.log (Enclosure.sfrac Bool.false 680959340804 16000000))

noncomputable abbrev qz131 := (@HSub.hSub Real Real Real qz344 (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 412601 4000) qz698) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 825202)))))) qz478)

noncomputable abbrev qz479 := (@HSub.hSub Real Real Real qz11 qz131 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 412601 2000) (Real.log Real.pi)))

noncomputable def Ns150p956 := @Enclosure.Real.IsNear.addLit_ft_p qz479 (Enclosure.sfrac Bool.true Ns150p952 Ns150p953) 11828130549170706859697 18014398509481984000 190693691397395857 10035200000000000000000 Ns150p952 Ns150p953 0 1 Ns150p955 

noncomputable def Ns150p957 := nat_lit 793772404398542279431273054208000 

noncomputable abbrev qz480 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 412601 2000) (Real.log Real.pi))

noncomputable def Ns150p958 := @Enclosure.Real.IsNear.subLit_ff_p qz131 qz480 16082381125536367003313 18014398509481984000 262875685657247 39200000000000000000 15848318399361 67108864000 412601 33554432000 Ns150p957 11828130549170706859697 18014398509481984000 

noncomputable def Ns150p959 := nat_lit 6432952450214546801325200 

noncomputable abbrev qz132 := (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 412601 4000) qz698) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 825202))))))

noncomputable def Ns150p960 := @Enclosure.Real.IsNear.subLit_ff_p qz132 qz478 3959752109048351008701 3602879701896396800 262875685657247 39200000000000000000 412601 2000 0 1 Ns150p959 16082381125536367003313 18014398509481984000 262875685657247 39200000000000000000 

noncomputable def Ns150p961 := nat_lit 8916569061394844622572437604923342848 

noncomputable def Ns150p962 := nat_lit 12885540332298820680417280 

noncomputable def Ns150p963 := nat_lit 4207666052629205123082459112758778485011703474857590611019762895399507610688704047349827666768363520 

noncomputable def Ns150p964 := nat_lit 23943136008964501757156008693167935683631086097682114463531624511433523222364688726497190946013184 

noncomputable def Ns150p965 := nat_lit 38115865026127248436537275533446614030369311033481753682894776144637751570943154531080929280 

noncomputable def Ns150p966 := BSN.log_dyadic_bound 156671340804 1205247340804 5 4 Ns150p963 33554432 15680000 Ns150p964 Ns150p965 8773190 1361918681608 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 156671340804) (BSN.artanhQ 1205247340804) 0 4 Ns150p964 Ns150p963 Ns150p965 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns150p967 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 412601 4000) qz698 412601 4000 0 1 48002378390352505 4503599627370496 625000147 9800000000000000 3961165865247566783101 3602879701896396800 36839383664621 5600000000000000000 (Enclosure.Real.IsNear.const Bool.false 412601 4000) (BSN.isNear_log_sfrac 680959340804 16000000 48002378390352505 4503599627370496 625000147 9800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 680959340804) qz352)) Bool.false Ns150p962 Ns150p86 1000000235200000 15680000000000000000000 48002378390352505 4503599627370496 625000147 9800000000000000 (BSN.log_rat_reduce_isNear 680959340804 16000000 15 1361918681608 1048576000000 8773190 33554432 24973259072661432 36028797018963968 15680000 1000000000000000 rfl rfl rfl rfl (Ns150p966 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns150p968 := BSN.arctan_dyadic_bound_f 1000 825202 1 0 4194304 1960000 0 1 1 0 1 1 5082 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 825202) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 825202) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz481 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 825202)))

noncomputable def Ns150p969 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz481 884279719003555 562949953421312 1 2000000000000000 5082 4194304 1 1960000 3706077050872199643136 883597624509859 562949953421312 50000000049 98000000000000000 qz16 (Ns150p968 rfl) rfl rfl 

noncomputable def Ns150p970 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 412601 4000) qz698) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz481)) 3961165865247566783101 3602879701896396800 36839383664621 5600000000000000000 883597624509859 2251799813685248 50000000049 392000000000000000 Ns150p961 3959752109048351008701 3602879701896396800 262875685657247 39200000000000000000 (Ns150p967 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz481) 1 4 0 1 883597624509859 562949953421312 50000000049 98000000000000000 883597624509859 2251799813685248 50000000049 392000000000000000 qz355 Ns150p969 rfl) 

noncomputable def Ns150p971 := @Ns150p956 Ns150p950 Ns150p951 190693691397395857 10035200000000000000000 (@Ns150p958 190693691397395857 10035200000000000000000 (Ns150p960 (Ns150p970 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 412601 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz478 (Real.log Real.pi) 412601 2000 0 1 38410761 33554432 1 16777216 15848318399361 67108864000 412601 33554432000 (Enclosure.Real.IsNear.const Bool.false 412601 2000) RS151to168.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns150p952 Ns150p953) 

noncomputable def Ns150p972 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz127) Bool.false Ns150p950 Ns150p951 190693691397395857 10035200000000000000000 5507899109 8388608 5 262144 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz127) (@HAdd.hAdd Real Real Real qz356 qz479 (Enclosure.sfrac Bool.true Ns150p952 Ns150p953)) Bool.false Ns150p950 Ns150p951 190693691397395857 10035200000000000000000 Ns150p954 (Ns150p971 rfl rfl)) 

noncomputable def Ns150p973 := nat_lit 1898825243197418575495168 

noncomputable def Ns150p974 := nat_lit 139944285274381184504543260897523484259510884049000308497991178802278798443907031040000 

noncomputable def Ns150p975 := nat_lit 281087523189421207768482594262230982152377364424391645054357117771079716889600000000 

noncomputable def Ns150p976 := nat_lit 366065653062024991746940521007565513375234180585932745307507937720053200192411443200000 

noncomputable def Ns150p977 := BSN.sin_dyadic_bound_f 26983929660 17179869184 3 2 8388608 3923829 Ns150p974 Ns150p98 Ns150p975 Ns150p976 Ns150p101 Ns150p975 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26983929660) qz357 0 2 Ns150p974 Ns150p98 Ns150p975 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26983929660) qz358 0 2 Ns150p976 Ns150p101 Ns150p975 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p978 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz127) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5507899109) qz368) Bool.false 5507899109 8388608 5 262144 Bool.true 8388607 8388608 1 1960000 (Ns150p972 rfl) (Enclosure.sfrac_false_div 5507899109 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5507899109) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns150p973) qz369) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 104 1000000000000000 3920000 1960000 (BSN.sin_reduce_arg_pos_rat_q1 5507899109 8388608 226375608064910080 72057594037927936 104 Ns150p973 Ns150p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns150p973 Ns150p86 26983929660 17179869184 3923829 3920000 (Ns150p977 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns150p979 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz127) Bool.false Ns150p950 Ns150p951 190693691397395857 10035200000000000000000 44063192875 67108864 1276 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz127) (@HAdd.hAdd Real Real Real qz356 qz479 (Enclosure.sfrac Bool.true Ns150p952 Ns150p953)) Bool.false Ns150p950 Ns150p951 190693691397395857 10035200000000000000000 Ns150p954 (Ns150p971 rfl rfl)) 

noncomputable def Ns150p980 := Ns150p949 21532 BSN.abs_quadSignPos (BSN.cos_quad_nat3 235 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66715578 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 129 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 41756452 67108864) qz130 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 1) Bool.true 8388607 8388608 157221 8028160000 67108856 67108864 1315 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz127)) Bool.true 8388607 8388608 157221 8028160000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz127) qz127) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz127)) Bool.true 8388607 8388608 10062144 513802240000 8388607 8388608 157221 8028160000 (Ns150p978 rfl rfl) rfl)) rfl) (Ns150p979 rfl) RS151to168.d7 

noncomputable def Ns150p981 := nat_lit 1983695196847483673876696247982704812666170690318427269289074568962725430185214669344433325975758388961 

noncomputable def Ns150p982 := nat_lit 798804117935762392979042538245979176601493479648174150324113710302131287888884030538176698728161 

noncomputable def Ns150p983 := nat_lit 9909211247861011756999297005096840367197889008150460149231322289056193179507286066615333124220568157921 

noncomputable def Ns150p984 := BSN.sin_dyadic_bound_f 98145417 67108864 4 3 67108864 33554432 Ns150p981 Ns150p111 Ns150p982 Ns150p983 Ns150p114 Ns150p982 66715578 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 98145417) qz361 0 3 Ns150p981 Ns150p111 Ns150p982 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 98145417) (BSN.sinOddQ 67108864) 0 3 Ns150p983 Ns150p114 Ns150p982 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p985 := nat_lit 253062515201745163652658136747565235789676542831045399779240853760 

noncomputable def Ns150p986 := nat_lit 17021371246730507653681301390135606284430781284200267846533376 

noncomputable def Ns150p987 := nat_lit 662755219498742626839808207469943969419930438530658770416736420096 

noncomputable def Ns150p988 := BSN.sin_dyadic_bound_f 45068626 67108864 3 2 67108864 33554432 Ns150p985 Ns150p359 Ns150p986 Ns150p987 Ns150p362 Ns150p986 41756452 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 45068626) qz361 0 2 Ns150p985 Ns150p359 Ns150p986 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 45068626) (BSN.sinOddQ 67108864) 0 2 Ns150p987 Ns150p362 Ns150p986 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p989 := nat_lit 1457675602789777226383028304320911934608710985404201028764804171578168014694557824416134093075522290625 

noncomputable def Ns150p990 := nat_lit 317336298741938229458947852662091503346616381425035448565329397949133994810084392637402587890625 

noncomputable def Ns150p991 := nat_lit 7283371758233370747805000329904611133680492356390605703565478709368257383737537412247403064823259890625 

noncomputable def Ns150p992 := BSN.sin_dyadic_bound_f 90878255 67108864 4 3 67108864 33554432 Ns150p989 Ns150p111 Ns150p990 Ns150p991 Ns150p114 Ns150p990 65540714 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 90878255) qz361 0 3 Ns150p989 Ns150p111 Ns150p990 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 90878255) (BSN.sinOddQ 67108864) 0 3 Ns150p991 Ns150p114 Ns150p990 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p993 := nat_lit 322881576425931558056617566985626632754860499833674785431241376472834002516998754276702551177033260481 

noncomputable def Ns150p994 := nat_lit 60608565681976875104003078547879079510070763398900329608108504111538462643784253648613820440001 

noncomputable def Ns150p995 := nat_lit 1957310925672008553369566857256585296986811704828662137799209423804935891676656226671003464786495774145 

noncomputable def Ns150p996 := BSN.cos_dyadic_bound_f 79167057 67108864 4 3 67108864 33554432 Ns150p993 Ns150p128 Ns150p994 Ns150p995 Ns150p131 Ns150p994 25583219 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 79167057) qz362 0 3 Ns150p993 Ns150p128 Ns150p994 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 79167057) (BSN.cosOddQ 67108864) 0 3 Ns150p995 Ns150p131 Ns150p994 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p997 := Ns150p947 36440 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 53 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 65540714 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 4 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 25583219 67108864) qz130 rfl rfl (Ns150p980 RS151to168.d9 RS151to168.d11 RS151to168.d13 RS151to168.d17 (Ns150p984 rfl rfl) (Ns150p988 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns150p979 rfl) RS151to168.d19 RS151to168.d21 RS151to168.d23 RS151to168.d25 RS151to168.d17 (Ns150p992 rfl rfl) (Ns150p996 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns150p998 := nat_lit 712529040172539479482539790308074767459787588978458588138700800000 

noncomputable def Ns150p999 := nat_lit 436731912902172299653294029845875626803053606737648025600000000 

noncomputable def Ns150p1000 := nat_lit 2136713656691814093848312782864532551125756659721900468364902400000 

noncomputable def Ns150p1001 := BSN.cos_dyadic_bound_f 67612480 67108864 3 2 67108864 33554432 Ns150p998 Ns150p117 Ns150p999 Ns150p1000 Ns150p120 Ns150p999 35834278 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 67612480) qz362 0 2 Ns150p998 Ns150p117 Ns150p999 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 67612480) (BSN.cosOddQ 67108864) 0 2 Ns150p1000 Ns150p120 Ns150p999 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1002 := nat_lit 37671515255176554236454787041 

noncomputable def Ns150p1003 := BSN.sin_dyadic_bound_f 13931673 67108864 2 1 67108864 33554432 Ns150p1002 Ns150p107 Ns150p1002 Ns150p1002 Ns150p108 Ns150p1002 13831819 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 13931673) qz361 0 1 Ns150p1002 Ns150p107 Ns150p1002 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 13931673) (BSN.sinOddQ 67108864) 0 1 Ns150p1002 Ns150p108 Ns150p1002 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1004 := Ns150p945 48817 BSN.abs_quadSignPos (BSN.cos_quad_nat0 52 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 35834278 67108864) BSN.abs_quadSignNeg qz650 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 13831819 67108864) qz130 rfl rfl (Ns150p997 rfl rfl) (Ns150p979 rfl) RS151to168.d27 RS151to168.d29 RS151to168.d31 RS151to168.d33 RS151to168.d17 (Ns150p1001 rfl rfl) (Ns150p1003 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns150p1005 := nat_lit 226245012073615984507096412416 

noncomputable def Ns150p1006 := BSN.cos_dyadic_bound_f 21809452 67108864 2 1 67108864 33554432 Ns150p1005 Ns150p134 Ns150p1005 Ns150p1005 Ns150p135 Ns150p1005 63596060 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 21809452) qz362 0 1 Ns150p1005 Ns150p134 Ns150p1005 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 21809452) (BSN.cosOddQ 67108864) 0 1 Ns150p1005 Ns150p135 Ns150p1005 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1007 := Ns150p943 Bool.true 55969754 48817 Bool.true 21809452 3537118876014220 1 Bool.false 63596060 Bool.false Bool.true 33485150 54384 BSN.abs_quadSignPos qz407 (BSN.sfrac_eq_quadSignPos_mul Bool.false 63596060 67108864) qz130 rfl (Ns150p1004 rfl) (Ns150p979 rfl) RS151to168.d42 RS151to168.d44 RS151to168.d17 (Ns150p1006 rfl rfl) rfl 

noncomputable def Ns150p1008 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 8) 33485150 67108864 54384 67108864 33485150 67108864 54384 67108864 4494300754739200 16742575 16777216 3399 2097152 (Ns150p1007 rfl rfl rfl rfl) 

noncomputable def Ns150p1009 := @Enclosure.Real.IsNear.mulLit_ff qz696 (Zeta.RiemannSiegel.correction qz129) 1473405 4194304 1 4194304 6194707655741 8796093022208 7664525841471 153931627888640000 9127313233507068105 36893488147419103232 

noncomputable abbrev qz699 := (@HPow.hPow Real Real Real qz6 qz128 qz8)

noncomputable def Ns150p1010 := @Enclosure.Real.IsNear.mulLit_ff qz48 qz699 1 1 0 1 1473405 4194304 1 4194304 1473405 4194304 1 4194304 

noncomputable def Ns150p1011 := @Enclosure.Real.IsNear.sqrt_image qz128 550859056489 8388608000 412601 8388608000 33988737 33988764 4194304 (@Enclosure.Real.IsNear.of_eq qz128 (@HMul.hMul Real Real Real qz4 qz127 qz2) Bool.false 550859056489 8388608000 412601 8388608000 (BSN.t_div_two_pi_mk qz127 412601 1000 qz130) (@Enclosure.Real.IsNear.mulLit_ff qz127 qz2 412601 1000 0 1 1335089 8388608 1 8388608 550859056489 8388608000 412601 8388608000 (Enclosure.Real.IsNear.const Bool.false 412601 1000) RS151to168.d36 rfl)) 

noncomputable abbrev qz877 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 412601 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz700 := qz877

noncomputable abbrev qz482 := qz700

noncomputable abbrev qz133 := qz482

noncomputable def Ns150p1012 := @Enclosure.Real.IsNear.sqrt_image qz133 67977501 8388608 27 8388608 11939811 11939817 4194304 (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 67977501 8388608 27 8388608 67977501 8388608 27 8388608 (Ns150p1011 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns150p1013 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz133) 5969907 2097152 3 4194304 1473404 1473406 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz133) Bool.false 23879628 8388608 6 8388608 5969907 2097152 3 4194304 (Ns150p1012 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns150p1014 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz133)) Bool.false 2946810 8388608 2 8388608 1473405 4194304 1 4194304 (Ns150p1013 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz134 := (@HMul.hMul Real Real Real qz340 qz338 qz476)

noncomputable abbrev qz701 := (@HMul.hMul Real Real Real qz839 qz876 qz876)

noncomputable abbrev qz483 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz701 qz695) qz638)

noncomputable abbrev qz135 := (Real.cos (@HMul.hMul Real Real Real qz340 qz338 qz483))

noncomputable def Ns150p1015 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz129) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz134)) qz135) Bool.false 6194707655741 

noncomputable def Ns150p1016 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz134)) qz135 5271163 4194304 69 

noncomputable def Ns150p1017 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz134)) Bool.false 10542326 8388608 276 8388608 5271163 4194304 69 

noncomputable def Ns150p1018 := @Enclosure.Real.IsNear.recentre' (Real.cos qz134) Bool.false 3337439 4194304 170794304 8220835840000 3337439 4194304 2668661 128450560000 

noncomputable def Ns150p1019 := @Enclosure.Real.IsNear.cos_image qz134 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5457807) qz368) Bool.false 5457807 8388608 85 4194304 Bool.false 3337439 4194304 1 

noncomputable def Ns150p1020 := nat_lit 728624036051650762303753213 

noncomputable def Ns150p1021 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz129 884279719003555 140737488355328 1 500000000000000 868637 8388608 27 8388608 768118082276091004535 1180591620717411303424 Ns150p1020 

noncomputable def Ns150p1022 := @Enclosure.Real.IsNear.subLit_ff_p qz133 qz46 67977501 8388608 27 8388608 8 1 0 1 868637 868637 8388608 27 

noncomputable def Ns150p1023 := @Ns150p1022 8388608 (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 67977501 8388608 27 8388608 67977501 8388608 27 8388608 (Ns150p1011 rfl rfl rfl rfl rfl rfl) rfl) qz410 

noncomputable def Ns150p1024 := @Enclosure.Real.IsNear.recentre' qz134 Bool.false 768118082276091004535 1180591620717411303424 Ns150p1020 Ns150p606 5457807 8388608 85 4194304 (@Ns150p1021 Ns150p606 RS151to168.d35 (Ns150p1023 rfl rfl) rfl) 

noncomputable def Ns150p1025 := nat_lit 7382235550483056236489135750455656809778263627985170833281 

noncomputable def Ns150p1026 := nat_lit 787309319018467979153468836159469191788361814718128001 

noncomputable def Ns150p1027 := nat_lit 22145132032811131773509100313694651490951214160326076243841 

noncomputable def Ns150p1028 := BSN.cos_dyadic_bound_f 5457807 8388608 3 2 4194304 1960000 Ns150p1025 Ns150p933 Ns150p1026 Ns150p1027 Ns150p936 Ns150p1026 3337439 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 5457807) (BSN.cosEvenQ 8388608) 0 2 Ns150p1025 Ns150p933 Ns150p1026 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 5457807) (BSN.cosOddQ 8388608) 0 2 Ns150p1027 Ns150p936 Ns150p1026 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1029 := @Enclosure.Real.IsNear.inv_image (Real.cos qz134) 3337439 4194304 2668661 128450560000 5271025 5271301 4194304 (Ns150p1018 (@Ns150p1019 1960000 (Ns150p1024 rfl) (Enclosure.sfrac_false_div 5457807 8388608) (Ns150p1028 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns150p1030 := @Enclosure.Real.IsNear.recentre' qz135 Bool.false 2350414 4194304 

noncomputable abbrev qz136 := (@HMul.hMul Real Real Real qz340 qz338 qz483)

noncomputable def Ns150p1031 := @Enclosure.Real.IsNear.cos_image qz136 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 2046713)) qz386) Bool.true 2046713 2097152 

noncomputable def Ns150p1032 := nat_lit 9665329036295428902587043205 

noncomputable def Ns150p1033 := nat_lit 7377980684290069553099581417829633 

noncomputable def Ns150p1034 := @Enclosure.Real.IsNear.recentre' qz136 Bool.true Ns150p1032 Ns150p617 Ns150p1033 

noncomputable abbrev qz137 := qz483

noncomputable def Ns150p1035 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz137 884279719003555 140737488355328 1 500000000000000 10930171560631 

noncomputable abbrev qz484 := (@HSub.hSub Real Real Real qz634 qz701 qz695)

noncomputable abbrev qz138 := qz484

noncomputable def Ns150p1036 := @Enclosure.Real.IsNear.subLit_tf qz138 qz25 6532125049527 70368744177664 273399543 70368744177664 1 16 

noncomputable abbrev qz485 := qz701

noncomputable abbrev qz139 := qz485

noncomputable def Ns150p1037 := @Enclosure.Real.IsNear.subLit_ff_n qz139 qz129 754530237769 70368744177664 46907127 70368744177664 868637 8388608 27 8388608 

noncomputable def Ns150p1038 := @Enclosure.Real.IsNear.mulLit_ff qz129 qz129 868637 8388608 27 8388608 868637 8388608 27 8388608 754530237769 70368744177664 

noncomputable def Ns150p1039 := nat_lit 570546661154838143629156829641114250353662751683153601 

noncomputable def Ns150p1040 := nat_lit 307932540110722302261857579352293660510347677961921 

noncomputable def Ns150p1041 := nat_lit 1711024118384292986282946773764638163739967559693536961 

noncomputable def Ns150p1042 := BSN.cos_dyadic_bound_f 2046713 2097152 3 2 4194304 1960000 Ns150p1039 Ns150p517 Ns150p1040 Ns150p1041 Ns150p520 Ns150p1040 2350414 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2046713) (BSN.cosEvenQ 2097152) 0 2 Ns150p1039 Ns150p517 Ns150p1040 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2046713) (BSN.cosOddQ 2097152) 0 2 Ns150p1041 Ns150p520 Ns150p1040 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1043 := @Ns150p1030 410188608 16441671680000 1175207 2097152 6409197 256901120000 (@Ns150p1031 205 8388608 Bool.false 2350414 4194304 1 1960000 (@Ns150p1034 Ns150p620 2046713 2097152 205 8388608 (@Ns150p1035 70368744177664 273399543 70368744177664 Ns150p1032 Ns150p617 Ns150p1033 Ns150p620 RS151to168.d35 (@Ns150p1036 0 1 174882744970096 10930171560631 70368744177664 273399543 70368744177664 (@Ns150p1037 54795436447462588416 6532125049527 70368744177664 273399543 70368744177664 (@Ns150p1038 46907127 70368744177664 (Ns150p1023 rfl rfl) (Ns150p1023 rfl rfl) rfl) (Ns150p1023 rfl rfl) rfl rfl) qz373 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 2046713 2097152) (BSN.cos_neg_of_bound 2046713 2097152 Bool.false 2350414 4194304 1 1960000 (Ns150p1042 rfl rfl)) rfl rfl) 

noncomputable def Ns150p1044 := @Ns150p1009 5700682872976943863 322818021289917153280000 (Ns150p1010 qz61 (@Enclosure.Real.IsNear.of_eq qz699 (@Inv.inv Real Real.instInv (Real.sqrt qz133)) Bool.false 1473405 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz128 (BSN.t_div_two_pi_nonneg qz127 412601 1000 qz130)) Ns150p1014) rfl) (@Ns150p1015 8796093022208 7664525841471 153931627888640000 (BSN.correction_mk qz129 (BSN.cos_two_pi_p_ne_zero_mk qz127 412601 1000 8 qz130 rfl rfl (@BSN.floor_sqrt_eq_dec qz127 412601 1000 8 qz130 rfl rfl rfl))) (@Ns150p1016 2097152 1175207 2097152 6409197 256901120000 6194707655741 8796093022208 7664525841471 153931627888640000 (@Ns150p1017 2097152 (Ns150p1029 rfl rfl rfl rfl rfl) rfl) (Ns150p1043 rfl) rfl)) 

noncomputable def Ns150p1045 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz127) (hardyZApproximantRS₀ qz127) Bool.true 45944625016330594505 36893488147419103232 528914286066464303863 322818021289917153280000 (@Eq.refl Real (hardyZApproximantRS₀ qz127)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz127) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz127) qz127 8) (@HMul.hMul Real Real Real qz4 qz696 (Zeta.RiemannSiegel.correction qz129))) Bool.true 45944625016330594505 36893488147419103232 528914286066464303863 322818021289917153280000 (BSN.hardyZApproximantRS₀_eq qz127 8 (@BSN.floor_sqrt_eq_dec qz127 412601 1000 8 qz130 rfl rfl rfl)) (@Ns150p942 45944625016330594505 36893488147419103232 528914286066464303863 322818021289917153280000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz127) qz127 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 8)) Bool.true 16742575 16777216 3399 2097152 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz127) qz127 8) (Ns150p1008 (Ns150p1007 rfl rfl rfl rfl) rfl rfl)) (Ns150p1044 rfl) rfl rfl)) 

theorem RS151to168.d51 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz127) Bool.true 45944625016330594505 36893488147419103232 528914286066464303863 322818021289917153280000 := Ns150p1045 

noncomputable def Ns150p1046 := nat_lit 1291272085159668613120000 

noncomputable def Ns150p1047 := nat_lit 3112920226059916022260957184 

noncomputable abbrev qz878 := (Enclosure.sfrac Bool.false 414477 1000)

noncomputable abbrev qz702 := qz878

noncomputable abbrev qz486 := qz702

noncomputable abbrev qz140 := qz486

noncomputable abbrev qz879 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 414477 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz703 := qz879

noncomputable abbrev qz487 := qz703

noncomputable abbrev qz141 := qz487

noncomputable abbrev qz880 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 414477 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz704 := qz880

noncomputable abbrev qz488 := qz704

noncomputable abbrev qz142 := qz488

noncomputable abbrev qz705 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz141 qz8))

noncomputable def Ns150p1048 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz140) qz140 8) (@HMul.hMul Real Real Real qz4 qz705 (Zeta.RiemannSiegel.correction qz142)) 12524501 8388608 27317 16777216 69577694834088519159 295147905179352825856 25180522002943195087 Ns150p1046 Ns150p1047 

noncomputable def Ns150p1049 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz140) qz140 Real.cos BSN.quadSignPos 7 8 414477 1000 128 67108864 33554432 1125899906842624 Bool.false 44326748626 1282 139548959 35 23726568 8 

noncomputable def Ns150p1050 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz140) qz140 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 414477 1000 52 92 67108864 33554432 1125899906842624 Bool.false 44326748626 1282 

noncomputable def Ns150p1051 := Ns150p1050 120242927 35 27397080 8 130587807 35 25364760 8 Bool.false 900066 36608 Bool.true 29632460 Bool.true 100773005 3537118876014220 1 Bool.false 60672246 Bool.false Bool.false 4637652 Bool.false Bool.false 27422274 

noncomputable def Ns150p1052 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz140) qz140 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 414477 1000 54 4 67108864 33554432 1125899906842624 Bool.false 44326748626 1282 

noncomputable def Ns150p1053 := Ns150p1052 93032624 35 33554424 8 108007536 35 30011992 8 Bool.true 13090435 21632 Bool.false 74490446 Bool.true 18233444 3537118876014220 1 Bool.false 29841080 Bool.true Bool.false 64647055 Bool.false Bool.false 900066 

noncomputable def Ns150p1054 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz140) qz140 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 414477 1000 237 130 67108864 33554432 1125899906842624 Bool.false 44326748626 1282 

noncomputable def Ns150p1055 := Ns150p1054 46516304 35 47453136 16 73726608 35 38745320 8 Bool.false 47445016 1323 Bool.false 63607868 Bool.false 64898903 3537118876014220 1 Bool.false 54502596 Bool.true Bool.false 38098697 Bool.true Bool.true 13090435 

noncomputable def Ns150p1056 := nat_lit 12065359377708896626339938761696340339771044862260056393 

noncomputable def Ns150p1057 := nat_lit 18266455056418652042709047134514301911139735515955200 

noncomputable def Ns150p1058 := nat_lit 5871445279539364644483569355360000 

noncomputable def Ns150p1059 := nat_lit 14601484066979952237408950584785280320 

noncomputable abbrev qz706 := (@Eq.refl Real qz878)

noncomputable abbrev qz489 := qz706

noncomputable abbrev qz143 := qz489

noncomputable def Ns150p1060 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz140 414477 1000 687165734116 16000000 828954 4000 2000 Ns150p1058 Ns150p1059 qz143 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns150p1061 := nat_lit 34748235007801622283859023633685460178540609203308962411840 

noncomputable abbrev qz490 := (Enclosure.sfrac Bool.false 414477 2000)

noncomputable abbrev qz707 := (Real.log (Enclosure.sfrac Bool.false 687165734116 16000000))

noncomputable abbrev qz144 := (@HSub.hSub Real Real Real qz344 (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 414477 4000) qz707) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 828954)))))) qz490)

noncomputable abbrev qz491 := (@HSub.hSub Real Real Real qz11 qz144 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 414477 2000) (Real.log Real.pi)))

noncomputable def Ns150p1062 := @Enclosure.Real.IsNear.addLit_ft_p qz491 (Enclosure.sfrac Bool.true Ns150p1058 Ns150p1059) 2379775644894408109537 3602879701896396800 191554911038305989 10035200000000000000000 Ns150p1058 Ns150p1059 0 1 Ns150p1061 

noncomputable def Ns150p1063 := nat_lit 798520200518655640917078179840000 

noncomputable abbrev qz492 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 414477 2000) (Real.log Real.pi))

noncomputable def Ns150p1064 := @Enclosure.Real.IsNear.subLit_ff_p qz144 qz492 16172471880668486313317 18014398509481984000 264048185933019 39200000000000000000 15920376986997 67108864000 414477 33554432000 Ns150p1063 2379775644894408109537 3602879701896396800 

noncomputable def Ns150p1065 := nat_lit 32344943761336972626634000 

noncomputable abbrev qz145 := (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 414477 4000) qz707) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 828954))))))

noncomputable def Ns150p1066 := @Enclosure.Real.IsNear.subLit_ff_p qz145 qz490 19905748806175768454501 18014398509481984000 264048185933019 39200000000000000000 414477 2000 0 1 Ns150p1065 16172471880668486313317 18014398509481984000 264048185933019 39200000000000000000 

noncomputable def Ns150p1067 := nat_lit 44823761453011943208910983790222901248 

noncomputable def Ns150p1068 := nat_lit 12896508795148085994979328 

noncomputable def Ns150p1069 := nat_lit 4384160772201138782483843139399449116707341154427289314101560964789080470273745251471900579472670720 

noncomputable def Ns150p1070 := nat_lit 26706741355617133351368373589079523100827891912937590826356618824234377522333336468264227372007424 

noncomputable def Ns150p1071 := nat_lit 52009544583720665433110875166048890580313691044951192409408116879206096001308943163123630080 

noncomputable def Ns150p1072 := BSN.log_dyadic_bound 162877734116 1211453734116 5 4 Ns150p1069 33554432 15680000 Ns150p1070 Ns150p1071 9077626 1374331468232 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 162877734116) (BSN.artanhQ 1211453734116) 0 4 Ns150p1070 Ns150p1069 Ns150p1071 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns150p1073 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 414477 4000) qz707 414477 4000 0 1 48043239098593913 4503599627370496 625000147 9800000000000000 19912817611867909278501 18014398509481984000 37006883704017 5600000000000000000 (Enclosure.Real.IsNear.const Bool.false 414477 4000) (BSN.isNear_log_sfrac 687165734116 16000000 48043239098593913 4503599627370496 625000147 9800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 687165734116) qz352)) Bool.false Ns150p1068 Ns150p86 1000000235200000 15680000000000000000000 48043239098593913 4503599627370496 625000147 9800000000000000 (BSN.log_rat_reduce_isNear 687165734116 16000000 15 1374331468232 1048576000000 9077626 33554432 24973259072661432 36028797018963968 15680000 1000000000000000 rfl rfl rfl rfl (Ns150p1072 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns150p1074 := BSN.arctan_dyadic_bound_f 1000 828954 1 0 4194304 1960000 0 1 1 0 1 1 5059 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 828954) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 828954) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz493 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 828954)))

noncomputable def Ns150p1075 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz493 884279719003555 562949953421312 1 2000000000000000 5059 4194304 1 1960000 3706089998721128333312 883600711517603 562949953421312 50000000049 98000000000000000 qz16 (Ns150p1074 rfl) rfl rfl 

noncomputable def Ns150p1076 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 414477 4000) qz707) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz493)) 19912817611867909278501 18014398509481984000 37006883704017 5600000000000000000 883600711517603 2251799813685248 50000000049 392000000000000000 Ns150p1067 19905748806175768454501 18014398509481984000 264048185933019 39200000000000000000 (Ns150p1073 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz493) 1 4 0 1 883600711517603 562949953421312 50000000049 98000000000000000 883600711517603 2251799813685248 50000000049 392000000000000000 qz355 Ns150p1075 rfl) 

noncomputable def Ns150p1077 := @Ns150p1062 Ns150p1056 Ns150p1057 191554911038305989 10035200000000000000000 (@Ns150p1064 191554911038305989 10035200000000000000000 (Ns150p1066 (Ns150p1076 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 414477 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz490 (Real.log Real.pi) 414477 2000 0 1 38410761 33554432 1 16777216 15920376986997 67108864000 414477 33554432000 (Enclosure.Real.IsNear.const Bool.false 414477 2000) RS151to168.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns150p1058 Ns150p1059) 

noncomputable def Ns150p1078 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz140) Bool.false Ns150p1056 Ns150p1057 191554911038305989 10035200000000000000000 2770421789 4194304 161 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz140) (@HAdd.hAdd Real Real Real qz356 qz491 (Enclosure.sfrac Bool.true Ns150p1058 Ns150p1059)) Bool.false Ns150p1056 Ns150p1057 191554911038305989 10035200000000000000000 Ns150p1060 (Ns150p1077 rfl rfl)) 

noncomputable def Ns150p1079 := nat_lit 4856286632964531911447489514212710447668804489761548856770650886008193866406662690625 

noncomputable def Ns150p1080 := nat_lit 305970350525552328669815250324704227796179077150711974597160454533877424919820338462720 

noncomputable def Ns150p1081 := nat_lit 1100612305114651614768359829516348764917823560909185683831857347441578298937890625 

noncomputable def Ns150p1082 := nat_lit 14566658674283366431112931822979098645476577822162828198944288943329698442622112290625 

noncomputable def Ns150p1083 := nat_lit 13768665773649854790141686264611690250828058471782038856872220454024484121391915230822400 

noncomputable def Ns150p1084 := BSN.cos_dyadic_bound_f 13495975945 17179869184 3 2 8388608 3923829 Ns150p1079 Ns150p1080 Ns150p1081 Ns150p1082 Ns150p1083 Ns150p1081 5930627 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 13495975945) (BSN.cosEvenQ 17179869184) 0 2 Ns150p1079 Ns150p1080 Ns150p1081 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 13495975945) (BSN.cosOddQ 17179869184) 0 2 Ns150p1082 Ns150p1083 Ns150p1081 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1085 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz140) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2770421789) qz359) Bool.false 2770421789 4194304 161 8388608 Bool.false 5930627 8388608 1 1960000 (Ns150p1078 rfl) (Enclosure.sfrac_false_div 2770421789 4194304) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2770421789) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474847439368557174980608) qz360) 226375608064910080 72057594037927936 Bool.false 5930627 8388608 105 1000000000000000 3920000 1960000 (BSN.sin_reduce_arg_pos_rat_q0 2770421789 4194304 226375608064910080 72057594037927936 105 474847439368557174980608 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 5930627 8388608 474847439368557174980608 604462909807314587353088 13495975945 17179869184 3923829 3920000 (Ns150p1084 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns150p1086 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz140) Bool.false Ns150p1056 Ns150p1057 191554911038305989 10035200000000000000000 44326748626 67108864 1282 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz140) (@HAdd.hAdd Real Real Real qz356 qz491 (Enclosure.sfrac Bool.true Ns150p1058 Ns150p1059)) Bool.false Ns150p1056 Ns150p1057 191554911038305989 10035200000000000000000 Ns150p1060 (Ns150p1077 rfl rfl)) 

noncomputable def Ns150p1087 := Ns150p1055 21632 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 237 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 54502596 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 130 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 38098697 67108864) qz143 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz140) qz140 1) Bool.false 5930627 8388608 5061697 256901120000 47445016 67108864 1323 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz140) qz140 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz140)) Bool.false 5930627 8388608 5061697 256901120000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz140) qz140) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz140)) Bool.false 5930627 8388608 323948608 16441671680000 5930627 8388608 5061697 256901120000 (Ns150p1085 rfl rfl) rfl)) rfl) (Ns150p1086 rfl) RS151to168.d7 

noncomputable def Ns150p1088 := nat_lit 1004293353840382891399106098635349952165789876693725653924392796160 

noncomputable def Ns150p1089 := nat_lit 267970331536921822349324420874822705105066309427421156883890176 

noncomputable def Ns150p1090 := nat_lit 2629858260473752556428140875934976352244993855411160887928931024896 

noncomputable def Ns150p1091 := BSN.sin_dyadic_bound_f 63607868 67108864 3 2 67108864 33554432 Ns150p1088 Ns150p359 Ns150p1089 Ns150p1090 Ns150p362 Ns150p1089 54502596 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 63607868) qz361 0 2 Ns150p1088 Ns150p359 Ns150p1089 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 63607868) (BSN.sinOddQ 67108864) 0 2 Ns150p1090 Ns150p362 Ns150p1089 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1092 := nat_lit 604789576831006308967027112912478029547687900149504896010220594241 

noncomputable def Ns150p1093 := nat_lit 314701524762312444300145117311754731202057005663710965561680961 

noncomputable def Ns150p1094 := nat_lit 1813739327443494302012481048502810579180659586437187266099538420801 

noncomputable def Ns150p1095 := BSN.cos_dyadic_bound_f 64898903 67108864 3 2 67108864 33554432 Ns150p1092 Ns150p117 Ns150p1093 Ns150p1094 Ns150p120 Ns150p1093 38098697 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 64898903) qz362 0 2 Ns150p1092 Ns150p117 Ns150p1093 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 64898903) (BSN.cosOddQ 67108864) 0 2 Ns150p1094 Ns150p120 Ns150p1093 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1096 := nat_lit 1050082395881694583619348742889273418472874086327258508279785308416 

noncomputable def Ns150p1097 := nat_lit 947991834176817271625980188881553718716168457231223960448123136 

noncomputable def Ns150p1098 := nat_lit 3148351203976730116314794268290057147981189922067313076918459678976 

noncomputable def Ns150p1099 := BSN.cos_dyadic_bound_f 74490446 67108864 3 2 67108864 33554432 Ns150p1096 Ns150p117 Ns150p1097 Ns150p1098 Ns150p120 Ns150p1097 29841080 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 74490446) qz362 0 2 Ns150p1096 Ns150p117 Ns150p1097 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 74490446) (BSN.cosOddQ 67108864) 0 2 Ns150p1098 Ns150p120 Ns150p1097 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1100 := nat_lit 110528640991157441676788490496 

noncomputable def Ns150p1101 := BSN.cos_dyadic_bound_f 18233444 67108864 2 1 67108864 33554432 Ns150p1100 Ns150p134 Ns150p1100 Ns150p1100 Ns150p135 Ns150p1100 64647055 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 18233444) qz362 0 1 Ns150p1100 Ns150p134 Ns150p1100 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 18233444) (BSN.cosOddQ 67108864) 0 1 Ns150p1100 Ns150p135 Ns150p1100 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1102 := Ns150p1053 36608 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 54 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 29841080 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 4 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 64647055 67108864) qz143 rfl rfl (Ns150p1087 RS151to168.d9 RS151to168.d11 RS151to168.d13 RS151to168.d17 (Ns150p1091 rfl rfl) (Ns150p1095 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns150p1086 rfl) RS151to168.d19 RS151to168.d21 RS151to168.d23 RS151to168.d25 RS151to168.d17 (Ns150p1099 rfl rfl) (Ns150p1101 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns150p1103 := nat_lit 26272989068144906536515802839383291230410797496824671121612800000 

noncomputable def Ns150p1104 := nat_lit 594486031633823117020872722459353284227747141296153600000000 

noncomputable def Ns150p1105 := nat_lit 78817778232371451963313366772704954984663936996191421057638400000 

noncomputable def Ns150p1106 := BSN.cos_dyadic_bound_f 29632460 67108864 3 2 67108864 33554432 Ns150p1103 Ns150p117 Ns150p1104 Ns150p1105 Ns150p120 Ns150p1104 60672246 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 29632460) qz362 0 2 Ns150p1103 Ns150p117 Ns150p1104 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 29632460) (BSN.cosOddQ 67108864) 0 2 Ns150p1105 Ns150p120 Ns150p1104 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1107 := nat_lit 849287334561848847677032123643173026107093651941925717622030196479128850262036806290847638640125640625 

noncomputable def Ns150p1108 := nat_lit 1096807749627745822750531336174944734917856122162132886900819128244948126549796786722461181640625 

noncomputable def Ns150p1109 := nat_lit 5141973101515372384754984356869766692785290612655085920168364803490943403755256339183702744493975240625 

noncomputable def Ns150p1110 := BSN.cos_dyadic_bound_f 100773005 67108864 4 3 67108864 33554432 Ns150p1107 Ns150p128 Ns150p1108 Ns150p1109 Ns150p131 Ns150p1108 4637652 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 100773005) qz362 0 3 Ns150p1107 Ns150p128 Ns150p1108 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 100773005) (BSN.cosOddQ 67108864) 0 3 Ns150p1109 Ns150p131 Ns150p1108 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz708 := (BSN.cos_quad_nat0 92 rfl)

noncomputable def Ns150p1111 := Ns150p1051 49041 BSN.abs_quadSignPos (BSN.cos_quad_nat0 52 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 60672246 67108864) BSN.abs_quadSignPos qz708 (BSN.sfrac_eq_quadSignPos_mul Bool.false 4637652 67108864) qz143 rfl rfl (Ns150p1102 rfl rfl) (Ns150p1086 rfl) RS151to168.d27 RS151to168.d29 RS151to168.d31 RS151to168.d33 RS151to168.d17 (Ns150p1106 rfl rfl) (Ns150p1110 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns150p1112 := nat_lit 161526970554409146721277788416 

noncomputable def Ns150p1113 := BSN.cos_dyadic_bound_f 20047548 67108864 2 1 67108864 33554432 Ns150p1112 Ns150p134 Ns150p1112 Ns150p1112 Ns150p135 Ns150p1112 64136646 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 20047548) qz362 0 1 Ns150p1112 Ns150p134 Ns150p1112 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 20047548) (BSN.cosOddQ 67108864) 0 1 Ns150p1112 Ns150p135 Ns150p1112 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1114 := Ns150p1049 Bool.false 27422274 49041 Bool.true 20047548 3537118876014220 1 Bool.false 64136646 Bool.false Bool.false 50098004 54634 BSN.abs_quadSignPos qz407 (BSN.sfrac_eq_quadSignPos_mul Bool.false 64136646 67108864) qz143 rfl (Ns150p1111 rfl) (Ns150p1086 rfl) RS151to168.d42 RS151to168.d44 RS151to168.d17 (Ns150p1113 rfl rfl) rfl 

noncomputable def Ns150p1115 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz140) qz140 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz140) qz140 8) 50098004 67108864 54634 67108864 50098004 67108864 54634 67108864 6724040274214912 12524501 8388608 27317 16777216 (Ns150p1114 rfl rfl rfl rfl) 

noncomputable def Ns150p1116 := @Enclosure.Real.IsNear.mulLit_ff qz705 (Zeta.RiemannSiegel.correction qz142) 2943471 8388608 1 8388608 23637975313529 35184372088832 59636966489447 1077521395220480000 69577694834088519159 295147905179352825856 

noncomputable abbrev qz709 := (@HPow.hPow Real Real Real qz6 qz141 qz8)

noncomputable def Ns150p1117 := @Enclosure.Real.IsNear.mulLit_ff qz48 qz709 1 1 0 1 2943471 8388608 1 8388608 2943471 8388608 1 8388608 

noncomputable def Ns150p1118 := @Enclosure.Real.IsNear.sqrt_image qz141 553363683453 8388608000 414477 8388608000 34065919 34065946 4194304 (@Enclosure.Real.IsNear.of_eq qz141 (@HMul.hMul Real Real Real qz4 qz140 qz2) Bool.false 553363683453 8388608000 414477 8388608000 (BSN.t_div_two_pi_mk qz140 414477 1000 qz143) (@Enclosure.Real.IsNear.mulLit_ff qz140 qz2 414477 1000 0 1 1335089 8388608 1 8388608 553363683453 8388608000 414477 8388608000 (Enclosure.Real.IsNear.const Bool.false 414477 1000) RS151to168.d36 rfl)) 

noncomputable abbrev qz881 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 414477 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz710 := qz881

noncomputable abbrev qz494 := qz710

noncomputable abbrev qz146 := qz494

noncomputable def Ns150p1119 := @Enclosure.Real.IsNear.sqrt_image qz146 68131865 8388608 27 8388608 11953360 11953365 4194304 (@Enclosure.Real.IsNear.recentre' qz146 Bool.false 68131865 8388608 27 8388608 68131865 8388608 27 8388608 (Ns150p1118 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns150p1120 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz146) 23906725 8388608 5 8388608 1471735 1471736 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz146) Bool.false 23906725 8388608 5 8388608 23906725 8388608 5 8388608 (Ns150p1119 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns150p1121 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz146)) Bool.false 2943471 8388608 1 8388608 2943471 8388608 1 8388608 (Ns150p1120 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz147 := (@HMul.hMul Real Real Real qz340 qz338 qz488)

noncomputable abbrev qz711 := (@HMul.hMul Real Real Real qz839 qz880 qz880)

noncomputable abbrev qz495 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz711 qz704) qz638)

noncomputable abbrev qz148 := (Real.cos (@HMul.hMul Real Real Real qz340 qz338 qz495))

noncomputable def Ns150p1122 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz142) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz147)) qz148) Bool.false 23637975313529 

noncomputable def Ns150p1123 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz147)) qz148 11642413 8388608 339 

noncomputable def Ns150p1124 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz147)) Bool.false 11642413 8388608 339 8388608 11642413 8388608 339 

noncomputable def Ns150p1125 := @Enclosure.Real.IsNear.recentre' (Real.cos qz147) Bool.false 3022086 4194304 343548608 16441671680000 1511043 2097152 5367947 256901120000 

noncomputable abbrev qz712 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable def Ns150p1126 := @Enclosure.Real.IsNear.cos_image qz147 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 803463) qz712) Bool.false 803463 1048576 171 8388608 Bool.false 3022086 4194304 1 

noncomputable def Ns150p1127 := nat_lit 728624036052976738967112701 

noncomputable def Ns150p1128 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz142 884279719003555 140737488355328 1 500000000000000 1023001 8388608 27 8388608 904619036820355768555 1180591620717411303424 Ns150p1127 

noncomputable def Ns150p1129 := @Enclosure.Real.IsNear.subLit_ff_p qz146 qz46 68131865 8388608 27 8388608 8 1 0 1 1023001 1023001 8388608 27 

noncomputable def Ns150p1130 := @Ns150p1129 8388608 (@Enclosure.Real.IsNear.recentre' qz146 Bool.false 68131865 8388608 27 8388608 68131865 8388608 27 8388608 (Ns150p1118 rfl rfl rfl rfl rfl rfl) rfl) qz410 

noncomputable def Ns150p1131 := @Enclosure.Real.IsNear.recentre' qz147 Bool.false 904619036820355768555 1180591620717411303424 Ns150p1127 Ns150p606 803463 1048576 171 8388608 (@Ns150p1128 Ns150p606 RS151to168.d35 (Ns150p1130 rfl rfl) rfl) 

noncomputable def Ns150p1132 := nat_lit 846567450409684166052151222810654008113790031774401 

noncomputable def Ns150p1133 := nat_lit 58927746017182005661972572455120531352527200132792320 

noncomputable def Ns150p1134 := nat_lit 173670900481847520980712483178927294593755529921 

noncomputable def Ns150p1135 := nat_lit 2539355009428088803114492243465604169752182584263361 

noncomputable def Ns150p1136 := nat_lit 2651748570773190254788765760480423910863724005975654400 

noncomputable def Ns150p1137 := BSN.cos_dyadic_bound_f 803463 1048576 3 2 4194304 1960000 Ns150p1132 Ns150p1133 Ns150p1134 Ns150p1135 Ns150p1136 Ns150p1134 3022086 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 803463) (BSN.cosEvenQ 1048576) 0 2 Ns150p1132 Ns150p1133 Ns150p1134 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 803463) (BSN.cosOddQ 1048576) 0 2 Ns150p1135 Ns150p1136 Ns150p1134 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1138 := @Enclosure.Real.IsNear.inv_image (Real.cos qz147) 1511043 2097152 5367947 256901120000 5821037 5821376 4194304 (Ns150p1125 (@Ns150p1126 1960000 (Ns150p1131 rfl) (Enclosure.sfrac_false_div 803463 1048576) (Ns150p1137 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns150p1139 := @Enclosure.Real.IsNear.recentre' qz148 Bool.false 2030333 4194304 

noncomputable abbrev qz149 := (@HMul.hMul Real Real Real qz340 qz338 qz495)

noncomputable def Ns150p1140 := @Enclosure.Real.IsNear.cos_image qz149 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8938037)) qz368) Bool.true 8938037 8388608 

noncomputable def Ns150p1141 := nat_lit 10552171642940880746482062605 

noncomputable def Ns150p1142 := nat_lit 1520585465139706967092956008273669 

noncomputable def Ns150p1143 := @Enclosure.Real.IsNear.recentre' qz149 Bool.true Ns150p1141 Ns150p617 Ns150p1142 

noncomputable def Ns150p1144 := nat_lit 60446290980731458735308800000000000000 

noncomputable abbrev qz150 := qz495

noncomputable def Ns150p1145 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz150 884279719003555 140737488355328 1 500000000000000 11933069837711 

noncomputable abbrev qz496 := (@HSub.hSub Real Real Real qz634 qz711 qz704)

noncomputable abbrev qz151 := qz496

noncomputable def Ns150p1146 := @Enclosure.Real.IsNear.subLit_tf qz151 qz25 7535023326607 70368744177664 281735199 70368744177664 1 16 

noncomputable abbrev qz497 := qz711

noncomputable abbrev qz152 := qz497

noncomputable def Ns150p1147 := @Enclosure.Real.IsNear.subLit_ff_n qz152 qz142 1046531046001 70368744177664 55242783 70368744177664 1023001 8388608 27 8388608 

noncomputable def Ns150p1148 := @Enclosure.Real.IsNear.mulLit_ff qz142 qz142 1023001 8388608 27 8388608 1023001 8388608 27 8388608 1046531046001 70368744177664 

noncomputable def Ns150p1149 := nat_lit 53133757770244375024312010414778361177948686778183916316001 

noncomputable def Ns150p1150 := nat_lit 40732135995261531906514647378747558200739578700485485921 

noncomputable def Ns150p1151 := nat_lit 159319809038742602009123001949577588417444581177150777976161 

noncomputable def Ns150p1152 := BSN.cos_dyadic_bound_f 8938037 8388608 3 2 4194304 1960000 Ns150p1149 Ns150p933 Ns150p1150 Ns150p1151 Ns150p936 Ns150p1150 2030333 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 8938037) (BSN.cosEvenQ 8388608) 0 2 Ns150p1149 Ns150p933 Ns150p1150 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 8938037) (BSN.cosOddQ 8388608) 0 2 Ns150p1151 Ns150p936 Ns150p1150 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1153 := @Ns150p1139 105977152 4110417920000 2030333 4194304 1655893 64225280000 (@Ns150p1140 53 2097152 Bool.false 2030333 4194304 1 1960000 (@Ns150p1143 Ns150p1144 8938037 8388608 53 2097152 (@Ns150p1145 70368744177664 281735199 70368744177664 Ns150p1141 Ns150p617 Ns150p1142 Ns150p1144 RS151to168.d35 (@Ns150p1146 0 1 190929117403376 11933069837711 70368744177664 281735199 70368744177664 (@Ns150p1147 63208356957762093056 7535023326607 70368744177664 281735199 70368744177664 (@Ns150p1148 55242783 70368744177664 (Ns150p1130 rfl rfl) (Ns150p1130 rfl rfl) rfl) (Ns150p1130 rfl rfl) rfl rfl) qz373 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 8938037 8388608) (BSN.cos_neg_of_bound 8938037 8388608 Bool.false 2030333 4194304 1 1960000 (Ns150p1152 rfl rfl)) rfl rfl) 

noncomputable def Ns150p1154 := @Ns150p1116 25180522002943195087 Ns150p1046 (Ns150p1117 qz61 (@Enclosure.Real.IsNear.of_eq qz709 (@Inv.inv Real Real.instInv (Real.sqrt qz146)) Bool.false 2943471 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz141 (BSN.t_div_two_pi_nonneg qz140 414477 1000 qz143)) Ns150p1121) rfl) (@Ns150p1122 35184372088832 59636966489447 1077521395220480000 (BSN.correction_mk qz142 (BSN.cos_two_pi_p_ne_zero_mk qz140 414477 1000 8 qz143 rfl rfl (@BSN.floor_sqrt_eq_dec qz140 414477 1000 8 qz143 rfl rfl rfl))) (@Ns150p1123 8388608 2030333 4194304 1655893 64225280000 23637975313529 35184372088832 59636966489447 1077521395220480000 (@Ns150p1124 8388608 (Ns150p1138 rfl rfl rfl rfl rfl) rfl) (Ns150p1153 rfl) rfl)) 

noncomputable def Ns150p1155 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz140) (hardyZApproximantRS₀ qz140) Bool.false 371089008576859953673 295147905179352825856 2127655661519932635087 Ns150p1046 (@Eq.refl Real (hardyZApproximantRS₀ qz140)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz140) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz140) qz140 8) (@HMul.hMul Real Real Real qz4 qz705 (Zeta.RiemannSiegel.correction qz142))) Bool.false 371089008576859953673 295147905179352825856 2127655661519932635087 Ns150p1046 (BSN.hardyZApproximantRS₀_eq qz140 8 (@BSN.floor_sqrt_eq_dec qz140 414477 1000 8 qz143 rfl rfl rfl)) (@Ns150p1048 371089008576859953673 295147905179352825856 2127655661519932635087 Ns150p1046 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz140) qz140 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz140) qz140 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz140) qz140 8)) Bool.false 12524501 8388608 27317 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz140) qz140 8) (Ns150p1115 (Ns150p1114 rfl rfl rfl rfl) rfl rfl)) (Ns150p1154 rfl) rfl rfl)) 

theorem RS151to168.d52 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz140) Bool.false 371089008576859953673 295147905179352825856 2127655661519932635087 Ns150p1046 := Ns150p1155 

noncomputable def Ns150p1156 := nat_lit 60098339716184789108129792 

noncomputable abbrev qz882 := (Enclosure.sfrac Bool.false 415227 1000)

noncomputable abbrev qz713 := qz882

noncomputable abbrev qz498 := qz713

noncomputable abbrev qz153 := qz498

noncomputable abbrev qz883 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 415227 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz714 := qz883

noncomputable abbrev qz499 := qz714

noncomputable abbrev qz154 := qz499

noncomputable abbrev qz884 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 415227 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz715 := qz884

noncomputable abbrev qz500 := qz715

noncomputable abbrev qz155 := qz500

noncomputable abbrev qz716 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz154 qz8))

noncomputable def Ns150p1157 := @Enclosure.Real.IsNear.subLit_ff_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz153) qz153 8) (@HMul.hMul Real Real Real qz4 qz716 (Zeta.RiemannSiegel.correction qz155)) 622483 16777216 54729 33554432 4266567486966832395 18446744073709551616 12765187563083296977 645636042579834306560000 Ns150p1156 

noncomputable def Ns150p1158 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz153) qz153 Real.cos BSN.quadSignPos 7 8 415227 1000 128 67108864 33554432 1125899906842624 Bool.false 44432194504 1284 139548959 35 23726568 8 

noncomputable def Ns150p1159 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz153) qz153 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 415227 1000 52 92 67108864 33554432 1125899906842624 Bool.false 44432194504 1284 

noncomputable def Ns150p1160 := Ns150p1159 120242927 35 27397080 8 130587807 35 25364760 8 Bool.true 52848163 36671 Bool.true 14368777 Bool.true 93267983 3537118876014220 1 Bool.false 65576471 Bool.false Bool.false 12080164 Bool.false Bool.true 21510809 

noncomputable def Ns150p1161 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz153) qz153 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 415227 1000 55 3 67108864 33554432 1125899906842624 Bool.false 44432194504 1284 

noncomputable def Ns150p1162 := Ns150p1161 93032624 35 33554424 8 108007536 35 30011992 8 Bool.true 85103653 21669 Bool.false 4747499 Bool.true 99207575 3537118876014220 1 Bool.false 4743540 Bool.false Bool.false 66822041 Bool.false Bool.true 52848163 

noncomputable def Ns150p1163 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz153) qz153 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 415227 1000 238 131 67108864 33554432 1125899906842624 Bool.false 44432194504 1284 

noncomputable def Ns150p1164 := Ns150p1163 46516304 35 47453136 16 73726608 35 38745320 8 Bool.true 47483528 1323 Bool.false 28752161 Bool.false 9635468 3537118876014220 1 Bool.false 61043210 Bool.true Bool.false 9602396 Bool.false Bool.true 85103653 

noncomputable def Ns150p1165 := nat_lit 61129809870897397317012980706938913186188725013446513931 

noncomputable def Ns150p1166 := nat_lit 92328370064064248440873454793741370450348947275776000 

noncomputable def Ns150p1167 := nat_lit 5924759974213023846477583155360000 

noncomputable def Ns150p1168 := nat_lit 14760731847058008198698450519680000320 

noncomputable abbrev qz885 := (@Eq.refl Real (Enclosure.sfrac Bool.false 415227 1000))

noncomputable abbrev qz717 := qz885

noncomputable abbrev qz501 := qz717

noncomputable abbrev qz156 := qz501

noncomputable def Ns150p1169 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz153 415227 1000 689654846116 16000000 830454 4000 2000 Ns150p1167 Ns150p1168 qz156 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns150p1170 := nat_lit 176053852428184504272997384435984069976223528038725960121280 

noncomputable abbrev qz502 := (Enclosure.sfrac Bool.false 415227 2000)

noncomputable abbrev qz718 := (Real.log (Enclosure.sfrac Bool.false 689654846116 16000000))

noncomputable abbrev qz157 := (@HSub.hSub Real Real Real qz344 (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 415227 4000) qz718) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 830454)))))) qz502)

noncomputable abbrev qz503 := (@HSub.hSub Real Real Real qz11 qz157 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 415227 2000) (Real.log Real.pi)))

noncomputable def Ns150p1171 := @Enclosure.Real.IsNear.addLit_ft_p qz503 (Enclosure.sfrac Bool.true Ns150p1167 Ns150p1168) 11927183623640004625379 18014398509481984000 27414173609392677 1433600000000000000000 Ns150p1167 Ns150p1168 0 1 Ns150p1170 

noncomputable def Ns150p1172 := nat_lit 800419743701884255363930259456000 

noncomputable abbrev qz504 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 415227 2000) (Real.log Real.pi))

noncomputable def Ns150p1173 := @Enclosure.Real.IsNear.subLit_ff_p qz157 qz504 16208510387444706903011 18014398509481984000 37788133720467 5600000000000000000 15949185057747 67108864000 415227 33554432000 Ns150p1172 11927183623640004625379 18014398509481984000 

noncomputable def Ns150p1174 := nat_lit 6483404154977882761204400 

noncomputable abbrev qz158 := (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 415227 4000) qz718) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 830454))))))

noncomputable def Ns150p1175 := @Enclosure.Real.IsNear.subLit_ff_p qz158 qz502 3989708542478608957639 3602879701896396800 37788133720467 5600000000000000000 415227 2000 0 1 Ns150p1174 16208510387444706903011 18014398509481984000 37788133720467 5600000000000000000 

noncomputable def Ns150p1176 := nat_lit 8984024952611774006628006952511209472 

noncomputable def Ns150p1177 := nat_lit 12900879952917614779432960 

noncomputable def Ns150p1178 := nat_lit 4456744420327192304261091473572760341524758216517681103580469586348592546691061068801201124680990720 

noncomputable def Ns150p1179 := nat_lit 27878531756940029627640777102096128868401114774571860475424331090029729980566685570947040869351424 

noncomputable def Ns150p1180 := nat_lit 58718756226501333168360627450320375392500116581618295357370692662538832420082764041480110080 

noncomputable def Ns150p1181 := BSN.log_dyadic_bound 165366846116 1213942846116 5 4 Ns150p1178 33554432 15680000 Ns150p1179 Ns150p1180 9198950 1379309692232 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 165366846116) (BSN.artanhQ 1213942846116) 0 4 Ns150p1179 Ns150p1178 Ns150p1180 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns150p1182 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 415227 4000) qz718 415227 4000 0 1 48059522930225785 4503599627370496 625000147 9800000000000000 3991122305549772405639 3602879701896396800 259516936038369 39200000000000000000 (Enclosure.Real.IsNear.const Bool.false 415227 4000) (BSN.isNear_log_sfrac 689654846116 16000000 48059522930225785 4503599627370496 625000147 9800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 689654846116) qz352)) Bool.false Ns150p1177 Ns150p86 1000000235200000 15680000000000000000000 48059522930225785 4503599627370496 625000147 9800000000000000 (BSN.log_rat_reduce_isNear 689654846116 16000000 15 1379309692232 1048576000000 9198950 33554432 24973259072661432 36028797018963968 15680000 1000000000000000 rfl rfl rfl rfl (Ns150p1181 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns150p1183 := BSN.arctan_dyadic_bound_f 1000 830454 1 0 4194304 1960000 0 1 1 0 1 1 5050 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 830454) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 830454) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz505 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 830454)))

noncomputable def Ns150p1184 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz505 884279719003555 562949953421312 1 2000000000000000 5050 4194304 1 1960000 3706095065270709125120 883601919477155 562949953421312 50000000049 98000000000000000 qz16 (Ns150p1183 rfl) rfl rfl 

noncomputable def Ns150p1185 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 415227 4000) qz718) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz505)) 3991122305549772405639 3602879701896396800 259516936038369 39200000000000000000 883601919477155 2251799813685248 50000000049 392000000000000000 Ns150p1176 3989708542478608957639 3602879701896396800 37788133720467 5600000000000000000 (Ns150p1182 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz505) 1 4 0 1 883601919477155 562949953421312 50000000049 98000000000000000 883601919477155 2251799813685248 50000000049 392000000000000000 qz355 Ns150p1184 rfl) 

noncomputable def Ns150p1186 := @Ns150p1171 Ns150p1165 Ns150p1166 27414173609392677 1433600000000000000000 (@Ns150p1173 27414173609392677 1433600000000000000000 (Ns150p1175 (Ns150p1185 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 415227 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz502 (Real.log Real.pi) 415227 2000 0 1 38410761 33554432 1 16777216 15949185057747 67108864000 415227 33554432000 (Enclosure.Real.IsNear.const Bool.false 415227 2000) RS151to168.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns150p1167 Ns150p1168) 

noncomputable def Ns150p1187 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz153) Bool.false Ns150p1165 Ns150p1166 27414173609392677 1433600000000000000000 5554024313 8388608 161 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz153) (@HAdd.hAdd Real Real Real qz356 qz503 (Enclosure.sfrac Bool.true Ns150p1167 Ns150p1168)) Bool.false Ns150p1165 Ns150p1166 27414173609392677 1433600000000000000000 Ns150p1169 (Ns150p1186 rfl rfl)) 

noncomputable def Ns150p1188 := nat_lit 8761362098034481054346114400783529938000433901175610106495757496035183320378009190400 

noncomputable def Ns150p1189 := nat_lit 1105888194489025016605896290277608805096791115110023045836567865210916592676765696 

noncomputable def Ns150p1190 := nat_lit 22944634056823039578022461503296414661459551126987848336843248522596091021744737878016 

noncomputable def Ns150p1191 := BSN.sin_dyadic_bound_f 13504045816 17179869184 3 2 8388608 3923829 Ns150p1188 Ns150p98 Ns150p1189 Ns150p1190 Ns150p101 Ns150p1189 5935441 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 13504045816) qz357 0 2 Ns150p1188 Ns150p98 Ns150p1189 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 13504045816) qz358 0 2 Ns150p1190 Ns150p101 Ns150p1189 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1192 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz153) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5554024313) qz368) Bool.false 5554024313 8388608 161 8388608 Bool.true 5935441 8388608 1 1960000 (Ns150p1187 rfl) (Enclosure.sfrac_false_div 5554024313 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5554024313) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 950262745421961280618496) qz369) 226375608064910080 72057594037927936 Bool.false 5935441 8388608 105 1000000000000000 3920000 1960000 (BSN.sin_reduce_arg_pos_rat_q1 5554024313 8388608 226375608064910080 72057594037927936 105 950262745421961280618496 Ns150p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 5935441 8388608 950262745421961280618496 Ns150p86 13504045816 17179869184 3923829 3920000 (Ns150p1191 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns150p1193 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz153) Bool.false Ns150p1165 Ns150p1166 27414173609392677 1433600000000000000000 44432194504 67108864 1284 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz153) (@HAdd.hAdd Real Real Real qz356 qz503 (Enclosure.sfrac Bool.true Ns150p1167 Ns150p1168)) Bool.false Ns150p1165 Ns150p1166 27414173609392677 1433600000000000000000 Ns150p1169 (Ns150p1186 rfl rfl)) 

noncomputable def Ns150p1194 := Ns150p1164 21669 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 238 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 61043210 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 131 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 9602396 67108864) qz156 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz153) qz153 1) Bool.true 5935441 8388608 5061697 256901120000 47483528 67108864 1323 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz153) qz153 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz153)) Bool.true 5935441 8388608 5061697 256901120000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz153) qz153) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz153)) Bool.true 5935441 8388608 323948608 16441671680000 5935441 8388608 5061697 256901120000 (Ns150p1192 rfl rfl) rfl)) rfl) (Ns150p1193 rfl) RS151to168.d7 

noncomputable def Ns150p1195 := nat_lit 23287319817997961759904205288987349085528407552185818051747068161 

noncomputable def Ns150p1196 := nat_lit 467050598675642992629057845278023239104782382689735300430081 

noncomputable def Ns150p1197 := nat_lit 69861025352796533993727357751271491210107013091792074684640344321 

noncomputable def Ns150p1198 := BSN.cos_dyadic_bound_f 28752161 67108864 3 2 67108864 33554432 Ns150p1195 Ns150p117 Ns150p1196 Ns150p1197 Ns150p120 Ns150p1196 61043210 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 28752161) qz362 0 2 Ns150p1195 Ns150p117 Ns150p1196 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 28752161) (BSN.cosOddQ 67108864) 0 2 Ns150p1197 Ns150p120 Ns150p1196 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1199 := nat_lit 8619682192786823156932792576 

noncomputable def Ns150p1200 := BSN.sin_dyadic_bound_f 9635468 67108864 2 1 67108864 33554432 Ns150p1199 Ns150p107 Ns150p1199 Ns150p1199 Ns150p108 Ns150p1199 9602396 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 9635468) qz361 0 1 Ns150p1199 Ns150p107 Ns150p1199 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 9635468) (BSN.sinOddQ 67108864) 0 1 Ns150p1199 Ns150p108 Ns150p1199 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1201 := nat_lit 507995105286068107518510001 

noncomputable def Ns150p1202 := BSN.sin_dyadic_bound_f 4747499 67108864 2 1 67108864 33554432 Ns150p1201 Ns150p107 Ns150p1201 Ns150p1201 Ns150p108 Ns150p1201 4743540 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 4747499) qz361 0 1 Ns150p1201 Ns150p107 Ns150p1201 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 4747499) (BSN.sinOddQ 67108864) 0 1 Ns150p1201 Ns150p108 Ns150p1201 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1203 := nat_lit 2071109479106313232487839739718912153348165957569356579747816920106772482159860664208988728133150390625 

noncomputable def Ns150p1204 := nat_lit 908945843482889646231427461184720204681339055968020513066909433395786336903133451938629150390625 

noncomputable def Ns150p1205 := nat_lit 10345449331242939661108908168703811520199472133720950071525601933017464171928259428344735886149150390625 

noncomputable def Ns150p1206 := BSN.sin_dyadic_bound_f 99207575 67108864 4 3 67108864 33554432 Ns150p1203 Ns150p111 Ns150p1204 Ns150p1205 Ns150p114 Ns150p1204 66822041 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 99207575) qz361 0 3 Ns150p1203 Ns150p111 Ns150p1204 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 99207575) (BSN.sinOddQ 67108864) 0 3 Ns150p1205 Ns150p114 Ns150p1204 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1207 := Ns150p1162 36671 BSN.abs_quadSignPos (BSN.cos_quad_nat3 55 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 4743540 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 3 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66822041 67108864) qz156 rfl rfl (Ns150p1194 RS151to168.d9 RS151to168.d11 RS151to168.d13 RS151to168.d17 (Ns150p1198 rfl rfl) (Ns150p1200 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns150p1193 rfl) RS151to168.d19 RS151to168.d21 RS151to168.d23 RS151to168.d25 RS151to168.d17 (Ns150p1202 rfl rfl) (Ns150p1206 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns150p1208 := nat_lit 42626455235349189860734081441 

noncomputable def Ns150p1209 := BSN.cos_dyadic_bound_f 14368777 67108864 2 1 67108864 33554432 Ns150p1208 Ns150p134 Ns150p1208 Ns150p1208 Ns150p135 Ns150p1208 65576471 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 14368777) qz362 0 1 Ns150p1208 Ns150p134 Ns150p1208 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 14368777) (BSN.cosOddQ 67108864) 0 1 Ns150p1208 Ns150p135 Ns150p1208 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1210 := nat_lit 622671310910010910577574017374600075104494700342154202963452357179934426601086202755331519593688965441 

noncomputable def Ns150p1211 := nat_lit 433302324129757872594599571769611246261485666168067694605677163294926788609548311481562877501761 

noncomputable def Ns150p1212 := nat_lit 3771956816545874673965071534894251455232343326913174573708335404605612885740469066083369133418667680065 

noncomputable def Ns150p1213 := BSN.cos_dyadic_bound_f 93267983 67108864 4 3 67108864 33554432 Ns150p1210 Ns150p128 Ns150p1211 Ns150p1212 Ns150p131 Ns150p1211 12080164 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 93267983) qz362 0 3 Ns150p1210 Ns150p128 Ns150p1211 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 93267983) (BSN.cosOddQ 67108864) 0 3 Ns150p1212 Ns150p131 Ns150p1211 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1214 := Ns150p1160 49126 BSN.abs_quadSignPos (BSN.cos_quad_nat0 52 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 65576471 67108864) BSN.abs_quadSignPos qz708 (BSN.sfrac_eq_quadSignPos_mul Bool.false 12080164 67108864) qz156 rfl rfl (Ns150p1207 rfl rfl) (Ns150p1193 rfl) RS151to168.d27 RS151to168.d29 RS151to168.d31 RS151to168.d33 RS151to168.d17 (Ns150p1209 rfl rfl) (Ns150p1213 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns150p1215 := nat_lit 137699026279085517020122410000 

noncomputable def Ns150p1216 := BSN.cos_dyadic_bound_f 19263390 67108864 2 1 67108864 33554432 Ns150p1215 Ns150p134 Ns150p1215 Ns150p1215 Ns150p135 Ns150p1215 64363047 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 19263390) qz362 0 1 Ns150p1215 Ns150p134 Ns150p1215 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 19263390) (BSN.cosOddQ 67108864) 0 1 Ns150p1215 Ns150p135 Ns150p1215 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1217 := Ns150p1158 Bool.true 21510809 49126 Bool.true 19263390 3537118876014220 1 Bool.false 64363047 Bool.false Bool.false 1244966 54729 BSN.abs_quadSignPos qz407 (BSN.sfrac_eq_quadSignPos_mul Bool.false 64363047 67108864) qz156 rfl (Ns150p1214 rfl) (Ns150p1193 rfl) RS151to168.d42 RS151to168.d44 RS151to168.d17 (Ns150p1216 rfl rfl) rfl 

noncomputable def Ns150p1218 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz153) qz153 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz153) qz153 8) 1244966 67108864 54729 67108864 1244966 67108864 54729 67108864 167096507957248 622483 16777216 54729 33554432 (Ns150p1217 rfl rfl rfl rfl) 

noncomputable def Ns150p1219 := @Enclosure.Real.IsNear.mulLit_ff qz716 (Zeta.RiemannSiegel.correction qz155) 735535 2097152 1 4194304 5800631495397 8796093022208 60259318267709 1077521395220480000 4266567486966832395 18446744073709551616 

noncomputable abbrev qz719 := (@HPow.hPow Real Real Real qz6 qz154 qz8)

noncomputable def Ns150p1220 := @Enclosure.Real.IsNear.mulLit_ff qz48 qz719 1 1 0 1 735535 2097152 1 4194304 735535 2097152 1 4194304 

noncomputable def Ns150p1221 := @Enclosure.Real.IsNear.sqrt_image qz154 554365000203 8388608000 415227 8388608000 34096727 34096753 4194304 (@Enclosure.Real.IsNear.of_eq qz154 (@HMul.hMul Real Real Real qz4 qz153 qz2) Bool.false 554365000203 8388608000 415227 8388608000 (BSN.t_div_two_pi_mk qz153 415227 1000 qz156) (@Enclosure.Real.IsNear.mulLit_ff qz153 qz2 415227 1000 0 1 1335089 8388608 1 8388608 554365000203 8388608000 415227 8388608000 (Enclosure.Real.IsNear.const Bool.false 415227 1000) RS151to168.d36 rfl)) 

noncomputable abbrev qz886 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 415227 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz720 := qz886

noncomputable abbrev qz506 := qz720

noncomputable abbrev qz159 := qz506

noncomputable def Ns150p1222 := @Enclosure.Real.IsNear.sqrt_image qz159 8524185 1048576 13 4194304 11958764 11958769 4194304 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 68193480 8388608 26 8388608 8524185 1048576 13 4194304 (Ns150p1221 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns150p1223 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz159) 23917533 8388608 5 8388608 1471069 1471071 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz159) Bool.false 23917533 8388608 5 8388608 23917533 8388608 5 8388608 (Ns150p1222 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns150p1224 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz159)) Bool.false 2942140 8388608 2 8388608 735535 2097152 1 4194304 (Ns150p1223 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz340 qz338 qz500)

noncomputable abbrev qz721 := (@HMul.hMul Real Real Real qz839 qz884 qz884)

noncomputable abbrev qz507 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz721 qz715) qz638)

noncomputable abbrev qz161 := (Real.cos (@HMul.hMul Real Real Real qz340 qz338 qz507))

noncomputable def Ns150p1225 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz155) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz160)) qz161) Bool.false 5800631495397 

noncomputable def Ns150p1226 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz160)) qz161 12196937 8388608 357 

noncomputable def Ns150p1227 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz160)) Bool.false 12196937 8388608 357 8388608 12196937 8388608 357 

noncomputable def Ns150p1228 := @Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.false 2884689 4194304 82457152 4110417920000 2884689 4194304 1288393 64225280000 

noncomputable def Ns150p1229 := @Enclosure.Real.IsNear.cos_image qz160 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6814843) qz368) Bool.false 6814843 8388608 41 2097152 Bool.false 2884689 4194304 1 

noncomputable def Ns150p1230 := nat_lit 350818980322230981165914907 

noncomputable def Ns150p1231 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz155 884279719003555 140737488355328 1 500000000000000 135577 1048576 13 4194304 119887991463344976235 147573952589676412928 Ns150p1230 

noncomputable def Ns150p1232 := @Enclosure.Real.IsNear.subLit_ff_p qz159 qz46 8524185 1048576 13 4194304 8 1 0 1 135577 135577 1048576 13 

noncomputable def Ns150p1233 := @Ns150p1232 4194304 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 68193480 8388608 26 8388608 8524185 1048576 13 4194304 (Ns150p1221 rfl rfl rfl rfl rfl rfl) rfl) qz410 

noncomputable def Ns150p1234 := @Enclosure.Real.IsNear.recentre' qz160 Bool.false 119887991463344976235 147573952589676412928 Ns150p1230 Ns150p151 6814843 8388608 41 2097152 (@Ns150p1231 Ns150p151 RS151to168.d35 (Ns150p1233 rfl rfl) rfl) 

noncomputable def Ns150p1235 := nat_lit 17947538286597019542317584267907275595897992122345561907681 

noncomputable def Ns150p1236 := nat_lit 4652076419518554748466843382485920816494674947155026401 

noncomputable def Ns150p1237 := nat_lit 53833310706952021517455819116956854946060987017142375670241 

noncomputable def Ns150p1238 := BSN.cos_dyadic_bound_f 6814843 8388608 3 2 4194304 1960000 Ns150p1235 Ns150p933 Ns150p1236 Ns150p1237 Ns150p936 Ns150p1236 2884689 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 6814843) (BSN.cosEvenQ 8388608) 0 2 Ns150p1235 Ns150p933 Ns150p1236 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 6814843) (BSN.cosOddQ 8388608) 0 2 Ns150p1237 Ns150p936 Ns150p1236 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1239 := @Enclosure.Real.IsNear.inv_image (Real.cos qz160) 2884689 4194304 1288393 64225280000 6098290 6098647 4194304 (Ns150p1228 (@Ns150p1229 1960000 (Ns150p1234 rfl) (Enclosure.sfrac_false_div 6814843 8388608) (Ns150p1238 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns150p1240 := @Enclosure.Real.IsNear.recentre' qz161 Bool.false 1902324 4194304 

noncomputable abbrev qz162 := (@HMul.hMul Real Real Real qz340 qz338 qz507)

noncomputable def Ns150p1241 := @Enclosure.Real.IsNear.cos_image qz162 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 9227907)) qz368) Bool.true 9227907 8388608 

noncomputable def Ns150p1242 := nat_lit 170224855896223914881375245 

noncomputable def Ns150p1243 := nat_lit 154742504910672534362390528 

noncomputable def Ns150p1244 := nat_lit 1851949892251241585608786904764791 

noncomputable def Ns150p1245 := @Enclosure.Real.IsNear.recentre' qz162 Bool.true Ns150p1242 Ns150p1243 Ns150p1244 

noncomputable abbrev qz163 := qz507

noncomputable def Ns150p1246 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz163 884279719003555 140737488355328 1 500000000000000 192501142159 

noncomputable abbrev qz508 := (@HSub.hSub Real Real Real qz634 qz721 qz715)

noncomputable abbrev qz164 := qz508

noncomputable def Ns150p1247 := @Enclosure.Real.IsNear.subLit_tf qz164 qz25 123781665423 1099511627776 68626129 17592186044416 1 16 

noncomputable abbrev qz509 := qz721

noncomputable abbrev qz165 := qz509

noncomputable def Ns150p1248 := @Enclosure.Real.IsNear.subLit_ff_n qz165 qz155 18381122929 1099511627776 14100177 17592186044416 135577 1048576 13 4194304 

noncomputable def Ns150p1249 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz155 135577 1048576 13 4194304 135577 1048576 13 4194304 18381122929 1099511627776 

noncomputable def Ns150p1250 := nat_lit 60375412125144510356292540000211580699265731730029838603681 

noncomputable def Ns150p1251 := nat_lit 52580616274469640584692808040098809922290615275619882401 

noncomputable def Ns150p1252 := nat_lit 181021075142884591787708234384554544477952613959538276046241 

noncomputable def Ns150p1253 := BSN.cos_dyadic_bound_f 9227907 8388608 3 2 4194304 1960000 Ns150p1250 Ns150p933 Ns150p1251 Ns150p1252 Ns150p936 Ns150p1251 1902324 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 9227907) (BSN.cosEvenQ 8388608) 0 2 Ns150p1250 Ns150p933 Ns150p1251 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 9227907) (BSN.cosOddQ 8388608) 0 2 Ns150p1252 Ns150p936 Ns150p1251 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1254 := @Ns150p1240 414108608 16441671680000 475581 1048576 6470447 256901120000 (@Ns150p1241 207 8388608 Bool.false 1902324 4194304 1 1960000 (@Ns150p1245 Ns150p169 9227907 8388608 207 8388608 (@Ns150p1246 1099511627776 68626129 17592186044416 Ns150p1242 Ns150p1243 Ns150p1244 Ns150p169 RS151to168.d35 (@Ns150p1247 0 1 3080018274544 192501142159 1099511627776 68626129 17592186044416 (@Ns150p1248 129794483602587648 123781665423 1099511627776 68626129 17592186044416 (@Ns150p1249 14100177 17592186044416 (Ns150p1233 rfl rfl) (Ns150p1233 rfl rfl) rfl) (Ns150p1233 rfl rfl) rfl rfl) qz373 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 9227907 8388608) (BSN.cos_neg_of_bound 9227907 8388608 Bool.false 1902324 4194304 1 1960000 (Ns150p1253 rfl rfl)) rfl rfl) 

noncomputable def Ns150p1255 := @Ns150p1219 12765187563083296977 645636042579834306560000 (Ns150p1220 qz61 (@Enclosure.Real.IsNear.of_eq qz719 (@Inv.inv Real Real.instInv (Real.sqrt qz159)) Bool.false 735535 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz154 (BSN.t_div_two_pi_nonneg qz153 415227 1000 qz156)) Ns150p1224) rfl) (@Ns150p1225 8796093022208 60259318267709 1077521395220480000 (BSN.correction_mk qz155 (BSN.cos_two_pi_p_ne_zero_mk qz153 415227 1000 8 qz156 rfl rfl (@BSN.floor_sqrt_eq_dec qz153 415227 1000 8 qz156 rfl rfl rfl))) (@Ns150p1226 8388608 475581 1048576 6470447 256901120000 5800631495397 8796093022208 60259318267709 1077521395220480000 (@Ns150p1227 8388608 (Ns150p1239 rfl rfl rfl rfl rfl) rfl) (Ns150p1254 rfl) rfl)) 

noncomputable def Ns150p1256 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz153) (hardyZApproximantRS₀ qz153) Bool.true 3582140190373944587 18446744073709551616 1065830695402755616977 645636042579834306560000 (@Eq.refl Real (hardyZApproximantRS₀ qz153)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz153) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz153) qz153 8) (@HMul.hMul Real Real Real qz4 qz716 (Zeta.RiemannSiegel.correction qz155))) Bool.true 3582140190373944587 18446744073709551616 1065830695402755616977 645636042579834306560000 (BSN.hardyZApproximantRS₀_eq qz153 8 (@BSN.floor_sqrt_eq_dec qz153 415227 1000 8 qz156 rfl rfl rfl)) (@Ns150p1157 3582140190373944587 18446744073709551616 1065830695402755616977 645636042579834306560000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz153) qz153 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz153) qz153 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz153) qz153 8)) Bool.false 622483 16777216 54729 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz153) qz153 8) (Ns150p1218 (Ns150p1217 rfl rfl rfl rfl) rfl rfl)) (Ns150p1255 rfl) rfl rfl)) 

theorem RS151to168.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz153) Bool.true 3582140190373944587 18446744073709551616 1065830695402755616977 645636042579834306560000 := Ns150p1256 

noncomputable def Ns150p1257 := nat_lit 11647938341566983648185417728 

noncomputable abbrev qz887 := (Enclosure.sfrac Bool.false 416351 1000)

noncomputable abbrev qz722 := qz887

noncomputable abbrev qz510 := qz722

noncomputable abbrev qz166 := qz510

noncomputable abbrev qz888 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 416351 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz723 := qz888

noncomputable abbrev qz511 := qz723

noncomputable abbrev qz167 := qz511

noncomputable abbrev qz889 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 416351 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz724 := qz889

noncomputable abbrev qz512 := qz724

noncomputable abbrev qz168 := qz512

noncomputable abbrev qz725 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz167 qz8))

noncomputable def Ns150p1258 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz166) qz166 8) (@HMul.hMul Real Real Real qz4 qz725 (Zeta.RiemannSiegel.correction qz168)) 82701881 16777216 27441 16777216 33182211172823720115 147573952589676412928 13770442690870518847 645636042579834306560000 Ns150p1257 

noncomputable def Ns150p1259 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz166) qz166 Real.cos BSN.quadSignPos 7 8 416351 1000 128 67108864 33554432 1125899906842624 Bool.false 44590307900 1288 139548959 35 23726568 8 

noncomputable def Ns150p1260 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz166) qz166 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 416351 1000 51 92 67108864 33554432 1125899906842624 Bool.false 44590307900 1288 

noncomputable def Ns150p1261 := Ns150p1260 120242927 35 27397080 8 130587807 35 25364760 8 Bool.false 106658668 36775 Bool.true 96822788 Bool.true 81935282 3537118876014220 1 Bool.false 66559649 Bool.false Bool.false 23003002 Bool.false Bool.false 142525847 

noncomputable def Ns150p1262 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz166) qz166 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 416351 1000 55 3 67108864 33554432 1125899906842624 Bool.false 44590307900 1288 

noncomputable def Ns150p1263 := Ns150p1262 93032624 35 33554424 8 108007536 35 30011992 8 Bool.false 56961403 21732 Bool.false 58292226 Bool.true 62494649 3537118876014220 1 Bool.false 51233560 Bool.false Bool.false 53845624 Bool.false Bool.false 106658668 

noncomputable def Ns150p1264 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz166) qz166 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 416351 1000 239 131 67108864 33554432 1125899906842624 Bool.false 44590307900 1288 

noncomputable def Ns150p1265 := Ns150p1264 46516304 35 47453136 16 73726608 35 38745320 8 Bool.false 34856 1331 Bool.false 29166874 Bool.false 84880156 3537118876014220 1 Bool.false 28257262 Bool.false Bool.false 63991735 Bool.false Bool.false 56961403 

noncomputable def Ns150p1266 := nat_lit 561154449398726004368159621237695711510769673682194749423 

noncomputable def Ns150p1267 := nat_lit 844543117115740103363265608644254426974048753811456000 

noncomputable def Ns150p1268 := nat_lit 6005385410305779129634451240480000 

noncomputable def Ns150p1269 := nat_lit 15002099422569516622219254185286530880 

noncomputable abbrev qz890 := (@Eq.refl Real (Enclosure.sfrac Bool.false 416351 1000))

noncomputable abbrev qz726 := qz890

noncomputable abbrev qz513 := qz726

noncomputable abbrev qz169 := qz513

noncomputable def Ns150p1270 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz166 416351 1000 693393620804 16000000 832702 4000 2000 Ns150p1268 Ns150p1269 qz169 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns150p1271 := nat_lit 179569423807592321397811078796062627683446295578302319815360 

noncomputable abbrev qz514 := (Enclosure.sfrac Bool.false 416351 2000)

noncomputable abbrev qz727 := (Real.log (Enclosure.sfrac Bool.false 693393620804 16000000))

noncomputable abbrev qz170 := (@HSub.hSub Real Real Real qz344 (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 416351 4000) qz727) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 832702)))))) qz514)

noncomputable abbrev qz515 := (@HSub.hSub Real Real Real qz11 qz170 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 416351 2000) (Real.log Real.pi)))

noncomputable def Ns150p1272 := @Enclosure.Real.IsNear.addLit_ft_p qz515 (Enclosure.sfrac Bool.true Ns150p1268 Ns150p1269) 11969626845749976407847 18014398509481984000 192415212534609607 10035200000000000000000 Ns150p1268 Ns150p1269 0 1 Ns150p1271 

noncomputable def Ns150p1273 := nat_lit 803268060122184144757412855808000 

noncomputable abbrev qz516 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 416351 2000) (Real.log Real.pi))

noncomputable def Ns150p1274 := @Enclosure.Real.IsNear.subLit_ff_p qz170 qz516 16262542960156919111463 18014398509481984000 265219436208497 39200000000000000000 15992358753111 67108864000 416351 33554432000 Ns150p1273 11969626845749976407847 18014398509481984000 

noncomputable def Ns150p1275 := nat_lit 6505017184062767644585200 

noncomputable abbrev qz171 := (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 416351 4000) qz727) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 832702))))))

noncomputable def Ns150p1276 := @Enclosure.Real.IsNear.subLit_ff_p qz171 qz514 4002539875413517174331 3602879701896396800 265219436208497 39200000000000000000 416351 2000 0 1 Ns150p1275 16262542960156919111463 18014398509481984000 265219436208497 39200000000000000000 

noncomputable def Ns150p1277 := nat_lit 9012918545723933715378196016778969088 

noncomputable def Ns150p1278 := nat_lit 12907416117128810127687680 

noncomputable def Ns150p1279 := nat_lit 4567744640121160588456419287499749550038500822139669583793090024457049681651175589836403619459563520 

noncomputable def Ns150p1280 := nat_lit 29709497636580940772213313017827943357152853132436923955563772071227941159951156096243927033053184 

noncomputable def Ns150p1281 := nat_lit 70218838890762968434748265693459405376645949263910737172516862722321075537652817459157729280 

noncomputable def Ns150p1282 := BSN.log_dyadic_bound 169105620804 1217681620804 5 4 Ns150p1279 33554432 15680000 Ns150p1280 Ns150p1281 9380365 1386787241608 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 169105620804) (BSN.artanhQ 1217681620804) 0 4 Ns150p1280 Ns150p1279 Ns150p1281 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns150p1283 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 416351 4000) qz727 416351 4000 0 1 48083872039350905 4503599627370496 625000147 9800000000000000 4003953641491157729531 3602879701896396800 260219436203597 39200000000000000000 (Enclosure.Real.IsNear.const Bool.false 416351 4000) (BSN.isNear_log_sfrac 693393620804 16000000 48083872039350905 4503599627370496 625000147 9800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 693393620804) qz352)) Bool.false Ns150p1278 Ns150p86 1000000235200000 15680000000000000000000 48083872039350905 4503599627370496 625000147 9800000000000000 (BSN.log_rat_reduce_isNear 693393620804 16000000 15 1386787241608 1048576000000 9380365 33554432 24973259072661432 36028797018963968 15680000 1000000000000000 rfl rfl rfl rfl (Ns150p1282 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns150p1284 := BSN.arctan_dyadic_bound_f 1000 832702 1 0 4194304 1960000 0 1 1 0 1 1 5036 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 832702) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 832702) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz517 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 832702)))

noncomputable def Ns150p1285 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz517 884279719003555 562949953421312 1 2000000000000000 5036 4194304 1 1960000 3706102946570057023488 883603798525347 562949953421312 50000000049 98000000000000000 qz16 (Ns150p1284 rfl) rfl rfl 

noncomputable def Ns150p1286 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 416351 4000) qz727) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz517)) 4003953641491157729531 3602879701896396800 260219436203597 39200000000000000000 883603798525347 2251799813685248 50000000049 392000000000000000 Ns150p1277 4002539875413517174331 3602879701896396800 265219436208497 39200000000000000000 (Ns150p1283 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz517) 1 4 0 1 883603798525347 562949953421312 50000000049 98000000000000000 883603798525347 2251799813685248 50000000049 392000000000000000 qz355 Ns150p1285 rfl) 

noncomputable def Ns150p1287 := @Ns150p1272 Ns150p1266 Ns150p1267 192415212534609607 10035200000000000000000 (@Ns150p1274 192415212534609607 10035200000000000000000 (Ns150p1276 (Ns150p1286 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 416351 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz514 (Real.log Real.pi) 416351 2000 0 1 38410761 33554432 1 16777216 15992358753111 67108864000 416351 33554432000 (Enclosure.Real.IsNear.const Bool.false 416351 2000) RS151to168.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns150p1268 Ns150p1269) 

noncomputable def Ns150p1288 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz166) Bool.false Ns150p1266 Ns150p1267 192415212534609607 10035200000000000000000 5573788487 8388608 81 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz166) (@HAdd.hAdd Real Real Real qz356 qz515 (Enclosure.sfrac Bool.true Ns150p1268 Ns150p1269)) Bool.false Ns150p1266 Ns150p1267 192415212534609607 10035200000000000000000 Ns150p1270 (Ns150p1287 rfl rfl)) 

noncomputable def Ns150p1289 := BSN.sin_dyadic_bound_f 8923350 17179869184 1 0 8388608 3923829 0 1 1 0 1 1 4357 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 8923350) qz357 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 8923350) qz358 0 0 rfl) rfl rfl 

noncomputable def Ns150p1290 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz166) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5573788487) qz368) Bool.false 5573788487 8388608 81 4194304 Bool.false 4357 8388608 1 1960000 (Ns150p1288 rfl) (Enclosure.sfrac_false_div 5573788487 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5573788487) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 627924959563501010944) qz369) 226375608064910080 72057594037927936 Bool.false 4357 8388608 105 1000000000000000 3920000 1960000 (BSN.sin_reduce_arg_pos_rat_q3 5573788487 8388608 226375608064910080 72057594037927936 105 627924959563501010944 Ns150p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 4357 8388608 627924959563501010944 Ns150p86 8923350 17179869184 3923829 3920000 (Ns150p1289 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns150p1291 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz166) Bool.false Ns150p1266 Ns150p1267 192415212534609607 10035200000000000000000 44590307900 67108864 1288 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz166) (@HAdd.hAdd Real Real Real qz356 qz515 (Enclosure.sfrac Bool.true Ns150p1268 Ns150p1269)) Bool.false Ns150p1266 Ns150p1267 192415212534609607 10035200000000000000000 Ns150p1270 (Ns150p1287 rfl rfl)) 

noncomputable def Ns150p1292 := Ns150p1265 21732 BSN.abs_quadSignPos (BSN.cos_quad_nat3 239 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 28257262 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 131 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 63991735 67108864) qz169 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz166) qz166 1) Bool.false 4357 8388608 2546161 128450560000 34856 67108864 1331 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz166) qz166 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz166)) Bool.false 4357 8388608 2546161 128450560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz166) qz166) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz166)) Bool.false 4357 8388608 162954304 8220835840000 4357 8388608 2546161 128450560000 (Ns150p1290 rfl rfl) rfl)) rfl) (Ns150p1291 rfl) RS151to168.d7 

noncomputable def Ns150p1293 := nat_lit 723701615381451456478968879376 

noncomputable def Ns150p1294 := BSN.sin_dyadic_bound_f 29166874 67108864 2 1 67108864 33554432 Ns150p1293 Ns150p107 Ns150p1293 Ns150p1293 Ns150p108 Ns150p1293 28257262 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 29166874) qz361 0 1 Ns150p1293 Ns150p107 Ns150p1293 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 29166874) (BSN.sinOddQ 67108864) 0 1 Ns150p1293 Ns150p108 Ns150p1293 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1295 := nat_lit 3186349418888775663623362082553982561160266559740009641888756858880 

noncomputable def Ns150p1296 := nat_lit 2694321102565065317024810968906948170037680057343871306988322816 

noncomputable def Ns150p1297 := nat_lit 8340838624828354727547908141310771648858732364940516127592572583936 

noncomputable def Ns150p1298 := BSN.sin_dyadic_bound_f 84880156 67108864 3 2 67108864 33554432 Ns150p1295 Ns150p359 Ns150p1296 Ns150p1297 Ns150p362 Ns150p1296 63991735 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 84880156) qz361 0 2 Ns150p1295 Ns150p359 Ns150p1296 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 84880156) (BSN.sinOddQ 67108864) 0 2 Ns150p1297 Ns150p362 Ns150p1296 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1299 := nat_lit 708313705582317395576559535494974698137949759123098241444194812160 

noncomputable def Ns150p1300 := nat_lit 133316873443531232909779372353422936302041704406004800338002176 

noncomputable def Ns150p1301 := nat_lit 1854891477777636985466278188264932953226331777800980910296153456896 

noncomputable def Ns150p1302 := BSN.sin_dyadic_bound_f 58292226 67108864 3 2 67108864 33554432 Ns150p1299 Ns150p359 Ns150p1300 Ns150p1301 Ns150p362 Ns150p1300 51233560 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 58292226) qz361 0 2 Ns150p1299 Ns150p359 Ns150p1300 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 58292226) (BSN.sinOddQ 67108864) 0 2 Ns150p1301 Ns150p362 Ns150p1300 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1303 := nat_lit 935794875954685831304957933199384373864243362236463357390076142785 

noncomputable def Ns150p1304 := nat_lit 232671219205400998784710956836726187285362789437283048539972801 

noncomputable def Ns150p1305 := nat_lit 2450514636002606527991143150163509136769794408960219858704944227521 

noncomputable def Ns150p1306 := BSN.sin_dyadic_bound_f 62494649 67108864 3 2 67108864 33554432 Ns150p1303 Ns150p359 Ns150p1304 Ns150p1305 Ns150p362 Ns150p1304 53845624 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 62494649) qz361 0 2 Ns150p1303 Ns150p359 Ns150p1304 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 62494649) (BSN.sinOddQ 67108864) 0 2 Ns150p1305 Ns150p362 Ns150p1304 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1307 := Ns150p1263 36775 BSN.abs_quadSignPos (BSN.cos_quad_nat3 55 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 51233560 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 3 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 53845624 67108864) qz169 rfl rfl (Ns150p1292 RS151to168.d9 RS151to168.d11 RS151to168.d13 RS151to168.d17 (Ns150p1294 rfl rfl) (Ns150p1298 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns150p1291 rfl) RS151to168.d19 RS151to168.d21 RS151to168.d23 RS151to168.d25 RS151to168.d17 (Ns150p1302 rfl rfl) (Ns150p1306 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns150p1308 := nat_lit 1878756544424191646103916372440823648419163472774952191592218093594675828770625416136571473068772294656 

noncomputable def Ns150p1309 := nat_lit 678783078656119202060472930974548859217812550223597011992425843692411753083145564749128013971456 

noncomputable def Ns150p1310 := nat_lit 9385471103089005566016910964348656998104608707022976323212489638710674686633831393482042481054649942016 

noncomputable def Ns150p1311 := BSN.sin_dyadic_bound_f 96822788 67108864 4 3 67108864 33554432 Ns150p1308 Ns150p111 Ns150p1309 Ns150p1310 Ns150p114 Ns150p1309 66559649 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 96822788) qz361 0 3 Ns150p1308 Ns150p111 Ns150p1309 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 96822788) (BSN.sinOddQ 67108864) 0 3 Ns150p1310 Ns150p114 Ns150p1309 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1312 := nat_lit 370529501557391191471645025650804236650584473145911495217475861894929938610122652045012890403734163456 

noncomputable def Ns150p1313 := nat_lit 91548542255737657515679488197114567477430645435059103221059055158133991534184509424977859710976 

noncomputable def Ns150p1314 := nat_lit 2245898980453803931939156882664383874977991649165795731642572404257578910268808256966448253013552926720 

noncomputable def Ns150p1315 := BSN.cos_dyadic_bound_f 81935282 67108864 4 3 67108864 33554432 Ns150p1312 Ns150p128 Ns150p1313 Ns150p1314 Ns150p131 Ns150p1313 23003002 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 81935282) qz362 0 3 Ns150p1312 Ns150p128 Ns150p1313 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 81935282) (BSN.cosOddQ 67108864) 0 3 Ns150p1314 Ns150p131 Ns150p1313 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1316 := Ns150p1261 49264 BSN.abs_quadSignPos (BSN.cos_quad_nat3 51 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66559649 67108864) BSN.abs_quadSignPos qz708 (BSN.sfrac_eq_quadSignPos_mul Bool.false 23003002 67108864) qz169 rfl rfl (Ns150p1307 rfl rfl) (Ns150p1291 rfl) RS151to168.d27 RS151to168.d29 RS151to168.d31 RS151to168.d33 RS151to168.d17 (Ns150p1311 rfl rfl) (Ns150p1315 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns150p1317 := nat_lit 105046561651046857866598219776 

noncomputable def Ns150p1318 := BSN.cos_dyadic_bound_f 18003024 67108864 2 1 67108864 33554432 Ns150p1317 Ns150p134 Ns150p1317 Ns150p1317 Ns150p135 Ns150p1317 64708512 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 18003024) qz362 0 1 Ns150p1317 Ns150p134 Ns150p1317 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 18003024) (BSN.cosOddQ 67108864) 0 1 Ns150p1317 Ns150p135 Ns150p1317 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1319 := Ns150p1259 Bool.false 142525847 49264 Bool.true 18003024 3537118876014220 1 Bool.false 64708512 Bool.false Bool.false 165403762 54882 BSN.abs_quadSignPos qz407 (BSN.sfrac_eq_quadSignPos_mul Bool.false 64708512 67108864) qz169 rfl (Ns150p1316 rfl) (Ns150p1291 rfl) RS151to168.d42 RS151to168.d44 RS151to168.d17 (Ns150p1318 rfl rfl) rfl 

noncomputable def Ns150p1320 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz166) qz166 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz166) qz166 8) 165403762 67108864 54882 67108864 165403762 67108864 54882 67108864 22200117138292736 82701881 16777216 27441 16777216 (Ns150p1319 rfl rfl rfl rfl) 

noncomputable def Ns150p1321 := @Enclosure.Real.IsNear.mulLit_ff qz725 (Zeta.RiemannSiegel.correction qz168) 2940153 8388608 1 8388608 11285879058955 17592186044416 32667495916851 538760697610240000 33182211172823720115 147573952589676412928 

noncomputable abbrev qz728 := (@HPow.hPow Real Real Real qz6 qz167 qz8)

noncomputable def Ns150p1322 := @Enclosure.Real.IsNear.mulLit_ff qz48 qz728 1 1 0 1 2940153 8388608 1 8388608 2940153 8388608 1 8388608 

noncomputable def Ns150p1323 := @Enclosure.Real.IsNear.sqrt_image qz167 555865640239 8388608000 416351 8388608000 34142845 34142871 4194304 (@Enclosure.Real.IsNear.of_eq qz167 (@HMul.hMul Real Real Real qz4 qz166 qz2) Bool.false 555865640239 8388608000 416351 8388608000 (BSN.t_div_two_pi_mk qz166 416351 1000 qz169) (@Enclosure.Real.IsNear.mulLit_ff qz166 qz2 416351 1000 0 1 1335089 8388608 1 8388608 555865640239 8388608000 416351 8388608000 (Enclosure.Real.IsNear.const Bool.false 416351 1000) RS151to168.d36 rfl)) 

noncomputable abbrev qz891 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 416351 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz729 := qz891

noncomputable abbrev qz518 := qz729

noncomputable abbrev qz172 := qz518

noncomputable def Ns150p1324 := @Enclosure.Real.IsNear.sqrt_image qz172 17071429 2097152 13 4194304 11966848 11966854 4194304 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 68285716 8388608 26 8388608 17071429 2097152 13 4194304 (Ns150p1323 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns150p1325 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz172) 11966851 4194304 3 4194304 1470076 1470077 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz172) Bool.false 23933702 8388608 6 8388608 11966851 4194304 3 4194304 (Ns150p1324 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns150p1326 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz172)) Bool.false 2940153 8388608 1 8388608 2940153 8388608 1 8388608 (Ns150p1325 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz340 qz338 qz512)

noncomputable abbrev qz730 := (@HMul.hMul Real Real Real qz839 qz889 qz889)

noncomputable abbrev qz519 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz730 qz724) qz638)

noncomputable abbrev qz174 := (Real.cos (@HMul.hMul Real Real Real qz340 qz338 qz519))

noncomputable def Ns150p1327 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz168) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz173)) qz174) Bool.false 11285879058955 

noncomputable def Ns150p1328 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz173)) qz174 13189415 8388608 417 

noncomputable def Ns150p1329 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz173)) Bool.false 13189415 8388608 417 8388608 13189415 8388608 417 

noncomputable def Ns150p1330 := @Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.false 2667622 4194304 82457152 4110417920000 1333811 2097152 1288393 64225280000 

noncomputable def Ns150p1331 := @Enclosure.Real.IsNear.cos_image qz173 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7394379) qz368) Bool.false 7394379 8388608 41 2097152 Bool.false 2667622 4194304 1 

noncomputable def Ns150p1332 := nat_lit 350818980322627131769428763 

noncomputable def Ns150p1333 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz168 884279719003555 140737488355328 1 500000000000000 294213 2097152 13 4194304 260166588967192927215 295147905179352825856 Ns150p1332 

noncomputable def Ns150p1334 := @Enclosure.Real.IsNear.subLit_ff_p qz172 qz46 17071429 2097152 13 4194304 8 1 0 1 294213 294213 2097152 13 

noncomputable def Ns150p1335 := @Ns150p1334 4194304 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 68285716 8388608 26 8388608 17071429 2097152 13 4194304 (Ns150p1323 rfl rfl rfl rfl rfl rfl) rfl) qz410 

noncomputable def Ns150p1336 := @Enclosure.Real.IsNear.recentre' qz173 Bool.false 260166588967192927215 295147905179352825856 Ns150p1332 Ns150p151 7394379 8388608 41 2097152 (@Ns150p1333 Ns150p151 RS151to168.d35 (Ns150p1335 rfl rfl) rfl) 

noncomputable def Ns150p1337 := nat_lit 24878933103372665276979783832304043643112678696564159807841 

noncomputable def Ns150p1338 := nat_lit 8937450574283819511838877099081849043630446831145976161 

noncomputable def Ns150p1339 := nat_lit 74618924408969428191915673742713967231250775196030187471201 

noncomputable def Ns150p1340 := BSN.cos_dyadic_bound_f 7394379 8388608 3 2 4194304 1960000 Ns150p1337 Ns150p933 Ns150p1338 Ns150p1339 Ns150p936 Ns150p1338 2667622 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 7394379) (BSN.cosEvenQ 8388608) 0 2 Ns150p1337 Ns150p933 Ns150p1338 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 7394379) (BSN.cosOddQ 8388608) 0 2 Ns150p1339 Ns150p936 Ns150p1338 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1341 := @Enclosure.Real.IsNear.inv_image (Real.cos qz173) 1333811 2097152 1288393 64225280000 6594499 6594916 4194304 (Ns150p1330 (@Ns150p1331 1960000 (Ns150p1336 rfl) (Enclosure.sfrac_false_div 7394379 8388608) (Ns150p1340 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns150p1342 := @Enclosure.Real.IsNear.recentre' qz174 Bool.false 1711354 4194304 

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz340 qz338 qz519)

noncomputable def Ns150p1343 := @Enclosure.Real.IsNear.cos_image qz175 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 9651207)) qz368) Bool.true 9651207 8388608 

noncomputable def Ns150p1344 := nat_lit 712133448058647508695270805 

noncomputable def Ns150p1345 := nat_lit 1884308031721026846209032391513467 

noncomputable def Ns150p1346 := @Enclosure.Real.IsNear.recentre' qz175 Bool.true Ns150p1344 Ns150p166 Ns150p1345 

noncomputable abbrev qz176 := qz519

noncomputable def Ns150p1347 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz176 884279719003555 140737488355328 1 500000000000000 805325998951 

noncomputable abbrev qz520 := (@HSub.hSub Real Real Real qz634 qz730 qz724)

noncomputable abbrev qz177 := qz520

noncomputable def Ns150p1348 := @Enclosure.Real.IsNear.subLit_tf qz177 qz25 530448092007 4398046511104 69825197 17592186044416 1 16 

noncomputable abbrev qz521 := qz730

noncomputable abbrev qz178 := qz521

noncomputable def Ns150p1349 := @Enclosure.Real.IsNear.subLit_ff_n qz178 qz168 86561289369 4398046511104 15299245 17592186044416 294213 2097152 13 4194304 

noncomputable def Ns150p1350 := @Enclosure.Real.IsNear.mulLit_ff qz168 qz168 294213 2097152 13 4194304 294213 2097152 13 4194304 86561289369 4398046511104 

noncomputable def Ns150p1351 := nat_lit 72251706679878245930561388082266829246085104715883424306881 

noncomputable def Ns150p1352 := nat_lit 75275395169511116850772170792241305060672268410335057601 

noncomputable def Ns150p1353 := nat_lit 216604569249295715557982619905216005128133969610829602805441 

noncomputable def Ns150p1354 := BSN.cos_dyadic_bound_f 9651207 8388608 3 2 4194304 1960000 Ns150p1351 Ns150p933 Ns150p1352 Ns150p1353 Ns150p936 Ns150p1352 1711354 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 9651207) (BSN.cosEvenQ 8388608) 0 2 Ns150p1351 Ns150p933 Ns150p1352 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 9651207) (BSN.cosOddQ 8388608) 0 2 Ns150p1353 Ns150p936 Ns150p1352 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1355 := @Ns150p1342 421948608 16441671680000 855677 2097152 6592947 256901120000 (@Ns150p1343 211 8388608 Bool.false 1711354 4194304 1 1960000 (@Ns150p1346 Ns150p169 9651207 8388608 211 8388608 (@Ns150p1347 4398046511104 69825197 17592186044416 Ns150p1344 Ns150p166 Ns150p1345 Ns150p169 RS151to168.d35 (@Ns150p1348 0 1 12885215983216 805325998951 4398046511104 69825197 17592186044416 (@Ns150p1349 1112430277048664064 530448092007 4398046511104 69825197 17592186044416 (@Ns150p1350 15299245 17592186044416 (Ns150p1335 rfl rfl) (Ns150p1335 rfl rfl) rfl) (Ns150p1335 rfl rfl) rfl rfl) qz373 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 9651207 8388608) (BSN.cos_neg_of_bound 9651207 8388608 Bool.false 1711354 4194304 1 1960000 (Ns150p1354 rfl rfl)) rfl rfl) 

noncomputable def Ns150p1356 := @Ns150p1321 13770442690870518847 645636042579834306560000 (Ns150p1322 qz61 (@Enclosure.Real.IsNear.of_eq qz728 (@Inv.inv Real Real.instInv (Real.sqrt qz172)) Bool.false 2940153 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz167 (BSN.t_div_two_pi_nonneg qz166 416351 1000 qz169)) Ns150p1326) rfl) (@Ns150p1327 17592186044416 32667495916851 538760697610240000 (BSN.correction_mk qz168 (BSN.cos_two_pi_p_ne_zero_mk qz166 416351 1000 8 qz169 rfl rfl (@BSN.floor_sqrt_eq_dec qz166 416351 1000 8 qz169 rfl rfl rfl))) (@Ns150p1328 8388608 855677 2097152 6592947 256901120000 11285879058955 17592186044416 32667495916851 538760697610240000 (@Ns150p1329 8388608 (Ns150p1341 rfl rfl rfl rfl rfl) rfl) (Ns150p1355 rfl) rfl)) 

noncomputable def Ns150p1357 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz166) (hardyZApproximantRS₀ qz166) Bool.false 694271227214752653133 147573952589676412928 1069779892913913078847 645636042579834306560000 (@Eq.refl Real (hardyZApproximantRS₀ qz166)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz166) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz166) qz166 8) (@HMul.hMul Real Real Real qz4 qz725 (Zeta.RiemannSiegel.correction qz168))) Bool.false 694271227214752653133 147573952589676412928 1069779892913913078847 645636042579834306560000 (BSN.hardyZApproximantRS₀_eq qz166 8 (@BSN.floor_sqrt_eq_dec qz166 416351 1000 8 qz169 rfl rfl rfl)) (@Ns150p1258 694271227214752653133 147573952589676412928 1069779892913913078847 645636042579834306560000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz166) qz166 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz166) qz166 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz166) qz166 8)) Bool.false 82701881 16777216 27441 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz166) qz166 8) (Ns150p1320 (Ns150p1319 rfl rfl rfl rfl) rfl rfl)) (Ns150p1356 rfl) rfl rfl)) 

theorem RS151to168.d54 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz166) Bool.false 694271227214752653133 147573952589676412928 1069779892913913078847 645636042579834306560000 := Ns150p1357 

noncomputable def Ns150p1358 := nat_lit 4519452298058840145920000 

noncomputable def Ns150p1359 := nat_lit 1281653872049534173072850944 

noncomputable abbrev qz892 := (Enclosure.sfrac Bool.false 418597 1000)

noncomputable abbrev qz731 := qz892

noncomputable abbrev qz522 := qz731

noncomputable abbrev qz179 := qz522

noncomputable abbrev qz893 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 418597 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz732 := qz893

noncomputable abbrev qz523 := qz732

noncomputable abbrev qz180 := qz523

noncomputable abbrev qz894 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 418597 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz733 := qz894

noncomputable abbrev qz524 := qz733

noncomputable abbrev qz181 := qz524

noncomputable abbrev qz734 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz180 qz8))

noncomputable def Ns150p1360 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz179) qz179 8) (@HMul.hMul Real Real Real qz4 qz734 (Zeta.RiemannSiegel.correction qz181)) 27599693 33554432 13793 8388608 7850078507710343049 36893488147419103232 121228296441979323831 Ns150p1358 Ns150p1359 

noncomputable def Ns150p1361 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz179) qz179 Real.cos BSN.quadSignPos 7 8 418597 1000 128 67108864 33554432 1125899906842624 Bool.false 44906558144 1295 139548959 35 23726568 8 

noncomputable def Ns150p1362 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz179) qz179 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 418597 1000 51 92 67108864 33554432 1125899906842624 Bool.false 44906558144 1295 

noncomputable def Ns150p1363 := Ns150p1362 120242927 35 27397080 8 130587807 35 25364760 8 Bool.true 85669866 36967 Bool.true 50638159 Bool.true 58985252 3537118876014220 1 Bool.false 45967795 Bool.false Bool.false 42812840 Bool.false Bool.true 50721864 

noncomputable def Ns150p1364 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz179) qz179 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 418597 1000 56 2 67108864 33554432 1125899906842624 Bool.false 44906558144 1295 

noncomputable def Ns150p1365 := Ns150p1364 93032624 35 33554424 8 108007536 35 30011992 8 Bool.true 101641491 21842 Bool.false 60176839 Bool.true 94243688 3537118876014220 1 Bool.false 41888535 Bool.false Bool.false 11119155 Bool.true Bool.true 85669866 

noncomputable def Ns150p1366 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz179) qz179 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 418597 1000 241 133 67108864 33554432 1125899906842624 Bool.false 44906558144 1295 

noncomputable def Ns150p1367 := Ns150p1366 46516304 35 47453136 16 73726608 35 38745320 8 Bool.true 67108848 1331 Bool.false 30112785 Bool.false 24711725 3537118876014220 1 Bool.false 29112396 Bool.true Bool.false 24157031 Bool.true Bool.true 101641491 

noncomputable def Ns150p1368 := nat_lit 583674454250559890542434963479006563040402105940682780669 

noncomputable def Ns150p1369 := nat_lit 872249648806526189552942690129172223302705793204224000 

noncomputable def Ns150p1370 := nat_lit 6169122081943388339556751723360000 

noncomputable def Ns150p1371 := nat_lit 15494266293219393118948493717275955520 

noncomputable abbrev qz525 := (@Eq.refl Real qz731)

noncomputable abbrev qz182 := qz525

noncomputable def Ns150p1372 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz179 418597 1000 700894793636 16000000 837194 4000 2000 Ns150p1370 Ns150p1371 qz182 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns150p1373 := nat_lit 186775825360179164973579188313282100172928673901018489814080 

noncomputable abbrev qz526 := (Enclosure.sfrac Bool.false 418597 2000)

noncomputable abbrev qz735 := (Real.log (Enclosure.sfrac Bool.false 700894793636 16000000))

noncomputable abbrev qz183 := (@HSub.hSub Real Real Real qz344 (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 418597 4000) qz735) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 837194)))))) qz526)

noncomputable abbrev qz527 := (@HSub.hSub Real Real Real qz11 qz183 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 418597 2000) (Real.log Real.pi)))

noncomputable def Ns150p1374 := @Enclosure.Real.IsNear.addLit_ft_p qz527 (Enclosure.sfrac Bool.true Ns150p1370 Ns150p1371) 12054519585412041175229 18014398509481984000 193446288927724829 10035200000000000000000 Ns150p1370 Ns150p1371 0 1 Ns150p1373 

noncomputable def Ns150p1375 := nat_lit 808965115442753055190843129856000 

noncomputable abbrev qz528 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 418597 2000) (Real.log Real.pi))

noncomputable def Ns150p1376 := @Enclosure.Real.IsNear.subLit_ff_p qz183 qz528 16370593779403176046781 18014398509481984000 266623186538659 39200000000000000000 16078629322317 67108864000 418597 33554432000 Ns150p1375 12054519585412041175229 18014398509481984000 

noncomputable def Ns150p1377 := nat_lit 6548237511761270418712400 

noncomputable abbrev qz184 := (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 418597 4000) qz735) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 837194))))))

noncomputable def Ns150p1378 := @Enclosure.Real.IsNear.subLit_ff_p qz184 qz526 4028196073167998215001 3602879701896396800 266623186538659 39200000000000000000 418597 2000 0 1 Ns150p1377 16370593779403176046781 18014398509481984000 266623186538659 39200000000000000000 

noncomputable def Ns150p1379 := nat_lit 9070691167047346000869810035646005248 

noncomputable def Ns150p1380 := nat_lit 12920424134148521973514240 

noncomputable def Ns150p1381 := nat_lit 4797764430548910124232872249120919685578109638598429173213995657333162659871513876142321547827281920 

noncomputable def Ns150p1382 := nat_lit 33650556386252054991864603338387880736729067802683122583397323260263415219183818257140331290558464 

noncomputable def Ns150p1383 := nat_lit 99368456889405111594597072228070974269692369122688039632032895749223422885106179373118586880 

noncomputable def Ns150p1384 := BSN.log_dyadic_bound 176606793636 1225182793636 5 4 Ns150p1381 33554432 15680000 Ns150p1382 Ns150p1383 9741410 1401789587272 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 176606793636) (BSN.artanhQ 1225182793636) 0 4 Ns150p1382 Ns150p1381 Ns150p1383 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns150p1385 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 418597 4000) qz735 418597 4000 0 1 48132330678956665 4503599627370496 625000147 9800000000000000 4029609845043844619801 3602879701896396800 261623186533759 39200000000000000000 (Enclosure.Real.IsNear.const Bool.false 418597 4000) (BSN.isNear_log_sfrac 700894793636 16000000 48132330678956665 4503599627370496 625000147 9800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 700894793636) qz352)) Bool.false Ns150p1380 Ns150p86 1000000235200000 15680000000000000000000 48132330678956665 4503599627370496 625000147 9800000000000000 (BSN.log_rat_reduce_isNear 700894793636 16000000 15 1401789587272 1048576000000 9741410 33554432 24973259072661432 36028797018963968 15680000 1000000000000000 rfl rfl rfl rfl (Ns150p1384 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns150p1386 := BSN.arctan_dyadic_bound_f 1000 837194 1 0 4194304 1960000 0 1 1 0 1 1 5009 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 837194) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 837194) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz529 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 837194)))

noncomputable def Ns150p1387 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz529 884279719003555 562949953421312 1 2000000000000000 5009 4194304 1 1960000 3706118146218799398912 883607422404003 562949953421312 50000000049 98000000000000000 qz16 (Ns150p1386 rfl) rfl rfl 

noncomputable def Ns150p1388 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 418597 4000) qz735) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz529)) 4029609845043844619801 3602879701896396800 261623186533759 39200000000000000000 883607422404003 2251799813685248 50000000049 392000000000000000 Ns150p1379 4028196073167998215001 3602879701896396800 266623186538659 39200000000000000000 (Ns150p1385 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz529) 1 4 0 1 883607422404003 562949953421312 50000000049 98000000000000000 883607422404003 2251799813685248 50000000049 392000000000000000 qz355 Ns150p1387 rfl) 

noncomputable def Ns150p1389 := @Ns150p1374 Ns150p1368 Ns150p1369 193446288927724829 10035200000000000000000 (@Ns150p1376 193446288927724829 10035200000000000000000 (Ns150p1378 (Ns150p1388 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 418597 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz526 (Real.log Real.pi) 418597 2000 0 1 38410761 33554432 1 16777216 16078629322317 67108864000 418597 33554432000 (Enclosure.Real.IsNear.const Bool.false 418597 2000) RS151to168.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns150p1370 Ns150p1371) 

noncomputable def Ns150p1390 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz179) Bool.false Ns150p1368 Ns150p1369 193446288927724829 10035200000000000000000 701664971 1048576 81 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz179) (@HAdd.hAdd Real Real Real qz356 qz527 (Enclosure.sfrac Bool.true Ns150p1370 Ns150p1371)) Bool.false Ns150p1368 Ns150p1369 193446288927724829 10035200000000000000000 Ns150p1372 (Ns150p1389 rfl rfl)) 

noncomputable def Ns150p1391 := BSN.cos_dyadic_bound_f 10760611 17179869184 1 0 8388608 3923829 0 1 1 0 1 1 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 10760611) (BSN.cosEvenQ 17179869184) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 10760611) (BSN.cosOddQ 17179869184) 0 0 rfl) rfl rfl 

noncomputable def Ns150p1392 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz179) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 701664971) qz712) Bool.false 701664971 1048576 81 4194304 Bool.true 8388606 8388608 1 1960000 (Ns150p1390 rfl) (Enclosure.sfrac_false_div 701664971 1048576) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 701664971) qz712) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 94651337445455429632) (@Nat.cast Real Real.instNatCast 151115727451828646838272)) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 106 1000000000000000 3920000 1960000 (BSN.sin_reduce_arg_pos_rat_q2 701664971 1048576 226375608064910080 72057594037927936 106 94651337445455429632 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 8388606 8388608 94651337445455429632 151115727451828646838272 10760611 17179869184 3923829 3920000 (Ns150p1391 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns150p1393 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz179) Bool.false Ns150p1368 Ns150p1369 193446288927724829 10035200000000000000000 44906558144 67108864 1295 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz179) (@HAdd.hAdd Real Real Real qz356 qz527 (Enclosure.sfrac Bool.true Ns150p1370 Ns150p1371)) Bool.false Ns150p1368 Ns150p1369 193446288927724829 10035200000000000000000 Ns150p1372 (Ns150p1389 rfl rfl)) 

noncomputable def Ns150p1394 := Ns150p1367 21842 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 29112396 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 133 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 24157031 67108864) qz182 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz179) qz179 1) Bool.true 4194303 4194304 2546161 128450560000 67108848 67108864 1331 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz179) qz179 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz179)) Bool.true 4194303 4194304 2546161 128450560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz179) qz179) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz179)) Bool.true 8388606 8388608 162954304 8220835840000 4194303 4194304 2546161 128450560000 (Ns150p1392 rfl rfl) rfl)) rfl) (Ns150p1393 rfl) RS151to168.d7 

noncomputable def Ns150p1395 := nat_lit 822249642786623646967141250625 

noncomputable def Ns150p1396 := BSN.sin_dyadic_bound_f 30112785 67108864 2 1 67108864 33554432 Ns150p1395 Ns150p107 Ns150p1395 Ns150p1395 Ns150p108 Ns150p1395 29112396 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 30112785) qz361 0 1 Ns150p1395 Ns150p107 Ns150p1395 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 30112785) (BSN.sinOddQ 67108864) 0 1 Ns150p1395 Ns150p108 Ns150p1395 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1397 := nat_lit 372917058052999125316219140625 

noncomputable def Ns150p1398 := BSN.sin_dyadic_bound_f 24711725 67108864 2 1 67108864 33554432 Ns150p1397 Ns150p107 Ns150p1397 Ns150p1397 Ns150p108 Ns150p1397 24157031 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 24711725) qz361 0 1 Ns150p1397 Ns150p107 Ns150p1397 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 24711725) (BSN.sinOddQ 67108864) 0 1 Ns150p1397 Ns150p108 Ns150p1397 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1399 := nat_lit 447006069839310363416860989758165452514516527509124975157100116161 

noncomputable def Ns150p1400 := nat_lit 171962982667568003139807679374124224051915333138228833121958081 

noncomputable def Ns150p1401 := nat_lit 1340674283552595954244303353915748109095445751861098467805056432321 

noncomputable def Ns150p1402 := BSN.cos_dyadic_bound_f 60176839 67108864 3 2 67108864 33554432 Ns150p1399 Ns150p117 Ns150p1400 Ns150p1401 Ns150p120 Ns150p1400 41888535 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 60176839) qz362 0 2 Ns150p1399 Ns150p117 Ns150p1400 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 60176839) (BSN.cosOddQ 67108864) 0 2 Ns150p1401 Ns150p120 Ns150p1400 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1403 := nat_lit 649200039615167393848893846432478507284953836033385482434614318346955938721000707780840661792520667136 

noncomputable def Ns150p1404 := nat_lit 490938706644077645834338587203893773241067740393946260887076817359307709901488953390232613421056 

noncomputable def Ns150p1405 := nat_lit 3932413000905225461728543546898641989422822295933284773249214567421133764852843338401871535693868564480 

noncomputable def Ns150p1406 := BSN.cos_dyadic_bound_f 94243688 67108864 4 3 67108864 33554432 Ns150p1403 Ns150p128 Ns150p1404 Ns150p1405 Ns150p131 Ns150p1404 11119155 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 94243688) qz362 0 3 Ns150p1403 Ns150p128 Ns150p1404 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 94243688) (BSN.cosOddQ 67108864) 0 3 Ns150p1405 Ns150p131 Ns150p1404 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1407 := Ns150p1365 36967 BSN.abs_quadSignPos (BSN.cos_quad_nat0 56 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 41888535 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 2 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 11119155 67108864) qz182 rfl rfl (Ns150p1394 RS151to168.d9 RS151to168.d11 RS151to168.d13 RS151to168.d17 (Ns150p1396 rfl rfl) (Ns150p1398 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns150p1393 rfl) RS151to168.d19 RS151to168.d21 RS151to168.d23 RS151to168.d25 RS151to168.d17 (Ns150p1402 rfl rfl) (Ns150p1406 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns150p1408 := nat_lit 403329068906516456130657762949706627927292001952962860189090140545 

noncomputable def Ns150p1409 := nat_lit 43233785622727919850273804741099069743203910655823958141915521 

noncomputable def Ns150p1410 := nat_lit 1056268040054630111329107983470127007982371008307174252182053933441 

noncomputable def Ns150p1411 := BSN.sin_dyadic_bound_f 50638159 67108864 3 2 67108864 33554432 Ns150p1408 Ns150p359 Ns150p1409 Ns150p1410 Ns150p362 Ns150p1409 45967795 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 50638159) qz361 0 2 Ns150p1408 Ns150p359 Ns150p1409 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 50638159) (BSN.sinOddQ 67108864) 0 2 Ns150p1410 Ns150p362 Ns150p1409 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1412 := nat_lit 412626244353748157392987434297027543690379348717990535268453646336 

noncomputable def Ns150p1413 := nat_lit 146537073302740146155142973719895024559828077392014049772896256 

noncomputable def Ns150p1414 := nat_lit 1237585658914638991886652016943642841022018389999187577705815146496 

noncomputable def Ns150p1415 := BSN.cos_dyadic_bound_f 58985252 67108864 3 2 67108864 33554432 Ns150p1412 Ns150p117 Ns150p1413 Ns150p1414 Ns150p120 Ns150p1413 42812840 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 58985252) qz362 0 2 Ns150p1412 Ns150p117 Ns150p1413 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 58985252) (BSN.cosOddQ 67108864) 0 2 Ns150p1414 Ns150p120 Ns150p1413 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1416 := Ns150p1363 49524 BSN.abs_quadSignPos (BSN.cos_quad_nat3 51 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 45967795 67108864) BSN.abs_quadSignPos qz708 (BSN.sfrac_eq_quadSignPos_mul Bool.false 42812840 67108864) qz182 rfl rfl (Ns150p1407 rfl rfl) (Ns150p1393 rfl) RS151to168.d27 RS151to168.d29 RS151to168.d31 RS151to168.d33 RS151to168.d17 (Ns150p1411 rfl rfl) (Ns150p1415 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns150p1417 := nat_lit 53095481163115346870382126096 

noncomputable def Ns150p1418 := BSN.cos_dyadic_bound_f 15179742 67108864 2 1 67108864 33554432 Ns150p1417 Ns150p134 Ns150p1417 Ns150p1417 Ns150p135 Ns150p1417 65399374 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 15179742) qz362 0 1 Ns150p1417 Ns150p134 Ns150p1417 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 15179742) (BSN.cosOddQ 67108864) 0 1 Ns150p1417 Ns150p135 Ns150p1417 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1419 := Ns150p1361 Bool.true 50721864 49524 Bool.true 15179742 3537118876014220 1 Bool.false 65399374 Bool.false Bool.true 27599693 55172 BSN.abs_quadSignPos qz407 (BSN.sfrac_eq_quadSignPos_mul Bool.false 65399374 67108864) qz182 rfl (Ns150p1416 rfl) (Ns150p1393 rfl) RS151to168.d42 RS151to168.d44 RS151to168.d17 (Ns150p1418 rfl rfl) rfl 

noncomputable def Ns150p1420 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz179) qz179 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz179) qz179 8) 27599693 67108864 55172 67108864 27599693 67108864 55172 67108864 3704368087957504 27599693 33554432 13793 8388608 (Ns150p1419 rfl rfl rfl rfl) 

noncomputable def Ns150p1421 := @Enclosure.Real.IsNear.mulLit_ff qz734 (Zeta.RiemannSiegel.correction qz181) 2936201 8388608 1 8388608 2673549429249 4398046511104 82351818190231 1077521395220480000 7850078507710343049 36893488147419103232 

noncomputable abbrev qz736 := (@HPow.hPow Real Real Real qz6 qz180 qz8)

noncomputable def Ns150p1422 := @Enclosure.Real.IsNear.mulLit_ff qz48 qz736 1 1 0 1 2936201 8388608 1 8388608 2936201 8388608 1 8388608 

noncomputable def Ns150p1423 := @Enclosure.Real.IsNear.sqrt_image qz180 558864250133 8388608000 418597 8388608000 34234812 34234839 4194304 (@Enclosure.Real.IsNear.of_eq qz180 (@HMul.hMul Real Real Real qz4 qz179 qz2) Bool.false 558864250133 8388608000 418597 8388608000 (BSN.t_div_two_pi_mk qz179 418597 1000 qz182) (@Enclosure.Real.IsNear.mulLit_ff qz179 qz2 418597 1000 0 1 1335089 8388608 1 8388608 558864250133 8388608000 418597 8388608000 (Enclosure.Real.IsNear.const Bool.false 418597 1000) RS151to168.d36 rfl)) 

noncomputable abbrev qz895 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 418597 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz737 := qz895

noncomputable abbrev qz530 := qz737

noncomputable abbrev qz185 := qz530

noncomputable def Ns150p1424 := @Enclosure.Real.IsNear.sqrt_image qz185 68469651 8388608 27 8388608 11982954 11982960 4194304 (@Enclosure.Real.IsNear.recentre' qz185 Bool.false 68469651 8388608 27 8388608 68469651 8388608 27 8388608 (Ns150p1423 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns150p1425 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz185) 11982957 4194304 3 4194304 1468100 1468101 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz185) Bool.false 23965914 8388608 6 8388608 11982957 4194304 3 4194304 (Ns150p1424 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns150p1426 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz185)) Bool.false 2936201 8388608 1 8388608 2936201 8388608 1 8388608 (Ns150p1425 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz186 := (@HMul.hMul Real Real Real qz340 qz338 qz524)

noncomputable abbrev qz738 := (@HMul.hMul Real Real Real qz839 qz894 qz894)

noncomputable abbrev qz531 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz738 qz733) qz638)

noncomputable abbrev qz187 := (Real.cos (@HMul.hMul Real Real Real qz340 qz338 qz531))

noncomputable def Ns150p1427 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz181) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz186)) qz187) Bool.false 2673549429249 

noncomputable def Ns150p1428 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz186)) qz187 16008607 8388608 639 

noncomputable def Ns150p1429 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz186)) Bool.false 16008607 8388608 639 8388608 16008607 8388608 639 

noncomputable def Ns150p1430 := @Enclosure.Real.IsNear.recentre' (Real.cos qz186) Bool.false 2197841 4194304 343548608 16441671680000 2197841 4194304 5367947 256901120000 

noncomputable def Ns150p1431 := @Enclosure.Real.IsNear.cos_image qz186 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2137519) qz386) Bool.false 2137519 2097152 171 8388608 Bool.false 2197841 4194304 1 

noncomputable def Ns150p1432 := nat_lit 728624036055878298613206013 

noncomputable def Ns150p1433 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz181 884279719003555 140737488355328 1 500000000000000 1360787 8388608 27 8388608 1203316345983690597785 1180591620717411303424 Ns150p1432 

noncomputable def Ns150p1434 := @Enclosure.Real.IsNear.subLit_ff_p qz185 qz46 68469651 8388608 27 8388608 8 1 0 1 1360787 1360787 8388608 27 

noncomputable def Ns150p1435 := @Ns150p1434 8388608 (@Enclosure.Real.IsNear.recentre' qz185 Bool.false 68469651 8388608 27 8388608 68469651 8388608 27 8388608 (Ns150p1423 rfl rfl rfl rfl rfl rfl) rfl) qz410 

noncomputable def Ns150p1436 := @Enclosure.Real.IsNear.recentre' qz186 Bool.false 1203316345983690597785 1180591620717411303424 Ns150p1432 Ns150p606 2137519 2097152 171 8388608 (@Ns150p1433 Ns150p606 RS151to168.d35 (Ns150p1435 rfl rfl) rfl) 

noncomputable def Ns150p1437 := nat_lit 678809258762201711529772015018330823141948409871355521 

noncomputable def Ns150p1438 := nat_lit 435792618880764241152586522127558527906628095463041 

noncomputable def Ns150p1439 := nat_lit 2035556191048843606107010872010737352370031973423140481 

noncomputable def Ns150p1440 := BSN.cos_dyadic_bound_f 2137519 2097152 3 2 4194304 1960000 Ns150p1437 Ns150p517 Ns150p1438 Ns150p1439 Ns150p520 Ns150p1438 2197841 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2137519) (BSN.cosEvenQ 2097152) 0 2 Ns150p1437 Ns150p517 Ns150p1438 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2137519) (BSN.cosOddQ 2097152) 0 2 Ns150p1439 Ns150p520 Ns150p1438 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1441 := @Enclosure.Real.IsNear.inv_image (Real.cos qz186) 2197841 4194304 5367947 256901120000 8003984 8004623 4194304 (Ns150p1430 (@Ns150p1431 1960000 (Ns150p1436 rfl) (Enclosure.sfrac_false_div 2137519 2097152) (Ns150p1440 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns150p1442 := @Enclosure.Real.IsNear.recentre' qz187 Bool.false 1336056 4194304 

noncomputable abbrev qz188 := (@HMul.hMul Real Real Real qz340 qz338 qz531)

noncomputable def Ns150p1443 := @Enclosure.Real.IsNear.cos_image qz188 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 10457295)) qz368) Bool.true 10457295 8388608 

noncomputable def Ns150p1444 := nat_lit 12345795218951056995738951205 

noncomputable def Ns150p1445 := nat_lit 8095165322994403183517298136233533 

noncomputable def Ns150p1446 := @Enclosure.Real.IsNear.recentre' qz188 Bool.true Ns150p1444 Ns150p617 Ns150p1445 

noncomputable abbrev qz189 := qz531

noncomputable def Ns150p1447 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz189 884279719003555 140737488355328 1 500000000000000 13961413966231 

noncomputable abbrev qz532 := (@HSub.hSub Real Real Real qz634 qz738 qz733)

noncomputable abbrev qz190 := qz532

noncomputable def Ns150p1448 := @Enclosure.Real.IsNear.subLit_tf qz190 qz25 9563367455127 70368744177664 299975643 70368744177664 1 16 

noncomputable abbrev qz533 := qz738

noncomputable abbrev qz191 := qz533

noncomputable def Ns150p1449 := @Enclosure.Real.IsNear.subLit_ff_n qz191 qz181 1851741259369 70368744177664 73483227 70368744177664 1360787 8388608 27 8388608 

noncomputable def Ns150p1450 := @Enclosure.Real.IsNear.mulLit_ff qz181 qz181 1360787 8388608 27 8388608 1360787 8388608 27 8388608 1851741259369 70368744177664 

noncomputable def Ns150p1451 := nat_lit 99625421619021116334923404457573425207720813849099511690625 

noncomputable def Ns150p1452 := nat_lit 143006203426982198239897086051125370317537613803562890625 

noncomputable def Ns150p1453 := nat_lit 298590252450209384608290419200618024882527366319691409290625 

noncomputable def Ns150p1454 := BSN.cos_dyadic_bound_f 10457295 8388608 3 2 4194304 1960000 Ns150p1451 Ns150p933 Ns150p1452 Ns150p1453 Ns150p936 Ns150p1452 1336056 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 10457295) (BSN.cosEvenQ 8388608) 0 2 Ns150p1451 Ns150p933 Ns150p1452 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 10457295) (BSN.cosOddQ 8388608) 0 2 Ns150p1453 Ns150p936 Ns150p1452 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1455 := @Ns150p1442 449388608 16441671680000 167007 524288 7021697 256901120000 (@Ns150p1443 225 8388608 Bool.false 1336056 4194304 1 1960000 (@Ns150p1446 Ns150p620 10457295 8388608 225 8388608 (@Ns150p1447 70368744177664 299975643 70368744177664 Ns150p1444 Ns150p617 Ns150p1445 Ns150p620 RS151to168.d35 (@Ns150p1448 0 1 223382623459696 13961413966231 70368744177664 299975643 70368744177664 (@Ns150p1449 80223340741017993216 9563367455127 70368744177664 299975643 70368744177664 (@Ns150p1450 73483227 70368744177664 (Ns150p1435 rfl rfl) (Ns150p1435 rfl rfl) rfl) (Ns150p1435 rfl rfl) rfl rfl) qz373 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 10457295 8388608) (BSN.cos_neg_of_bound 10457295 8388608 Bool.false 1336056 4194304 1 1960000 (Ns150p1454 rfl rfl)) rfl rfl) 

noncomputable def Ns150p1456 := @Ns150p1421 121228296441979323831 Ns150p1358 (Ns150p1422 qz61 (@Enclosure.Real.IsNear.of_eq qz736 (@Inv.inv Real Real.instInv (Real.sqrt qz185)) Bool.false 2936201 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz180 (BSN.t_div_two_pi_nonneg qz179 418597 1000 qz182)) Ns150p1426) rfl) (@Ns150p1427 4398046511104 82351818190231 1077521395220480000 (BSN.correction_mk qz181 (BSN.cos_two_pi_p_ne_zero_mk qz179 418597 1000 8 qz182 rfl rfl (@BSN.floor_sqrt_eq_dec qz179 418597 1000 8 qz182 rfl rfl rfl))) (@Ns150p1428 8388608 167007 524288 7021697 256901120000 2673549429249 4398046511104 82351818190231 1077521395220480000 (@Ns150p1429 8388608 (Ns150p1441 rfl rfl rfl rfl rfl) rfl) (Ns150p1455 rfl) rfl)) 

noncomputable def Ns150p1457 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz179) (hardyZApproximantRS₀ qz179) Bool.true 38196261884258215817 36893488147419103232 7552354598580019643831 Ns150p1358 (@Eq.refl Real (hardyZApproximantRS₀ qz179)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz179) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz179) qz179 8) (@HMul.hMul Real Real Real qz4 qz734 (Zeta.RiemannSiegel.correction qz181))) Bool.true 38196261884258215817 36893488147419103232 7552354598580019643831 Ns150p1358 (BSN.hardyZApproximantRS₀_eq qz179 8 (@BSN.floor_sqrt_eq_dec qz179 418597 1000 8 qz182 rfl rfl rfl)) (@Ns150p1360 38196261884258215817 36893488147419103232 7552354598580019643831 Ns150p1358 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz179) qz179 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz179) qz179 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz179) qz179 8)) Bool.true 27599693 33554432 13793 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz179) qz179 8) (Ns150p1420 (Ns150p1419 rfl rfl rfl rfl) rfl rfl)) (Ns150p1456 rfl) rfl rfl)) 

theorem RS151to168.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz179) Bool.true 38196261884258215817 36893488147419103232 7552354598580019643831 Ns150p1358 := Ns150p1457 

noncomputable def Ns150p1458 := nat_lit 436124594025682267501756416 

noncomputable abbrev qz896 := (Enclosure.sfrac Bool.false 420092 1000)

noncomputable abbrev qz739 := qz896

noncomputable abbrev qz534 := qz739

noncomputable abbrev qz192 := qz534

noncomputable abbrev qz897 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 420092 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz740 := qz897

noncomputable abbrev qz535 := qz740

noncomputable abbrev qz193 := qz535

noncomputable abbrev qz898 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 420092 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz741 := qz898

noncomputable abbrev qz536 := qz741

noncomputable abbrev qz194 := qz536

noncomputable abbrev qz742 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz193 qz8))

noncomputable def Ns150p1459 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz192) qz192 8) (@HMul.hMul Real Real Real qz4 qz742 (Zeta.RiemannSiegel.correction qz194)) 9355143 16777216 27685 16777216 15149302527316767921 73786976294838206464 1980020452751014477 64563604257983430656000 Ns150p1458 

noncomputable def Ns150p1460 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz192) qz192 Real.cos BSN.quadSignPos 7 8 420092 1000 128 67108864 33554432 1125899906842624 Bool.false 45117287115 1299 139548959 35 23726568 8 

noncomputable def Ns150p1461 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz192) qz192 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 420092 1000 51 92 67108864 33554432 1125899906842624 Bool.false 45117287115 1299 

noncomputable def Ns150p1462 := Ns150p1461 120242927 35 27397080 8 130587807 35 25364760 8 Bool.true 32707430 37101 Bool.true 19672363 Bool.true 43485053 3537118876014220 1 Bool.false 19391824 Bool.false Bool.false 53506299 Bool.false Bool.true 4567276 

noncomputable def Ns150p1463 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz192) qz192 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 420092 1000 57 2 67108864 33554432 1125899906842624 Bool.false 45117287115 1299 

noncomputable def Ns150p1464 := Ns150p1463 93032624 35 33554424 8 108007536 35 30011992 8 Bool.false 3675923 21923 Bool.false 26407680 Bool.true 44985984 3537118876014220 1 Bool.false 25731415 Bool.true Bool.false 52587067 Bool.true Bool.true 32707430 

noncomputable def Ns150p1465 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz192) qz192 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 420092 1000 242 134 67108864 33554432 1125899906842624 Bool.false 45117287115 1299 

noncomputable def Ns150p1466 := Ns150p1465 46516304 35 47453136 16 73726608 35 38745320 8 Bool.false 67108832 1339 Bool.false 65885524 Bool.false 19805060 3537118876014220 1 Bool.false 37282397 Bool.true Bool.false 64207594 Bool.true Bool.false 3675923 

noncomputable def Ns150p1467 := nat_lit 4570710893209209875127677012329025698169522982256531 

noncomputable def Ns150p1468 := nat_lit 6798618341779797418627811635091512404907917312000 

noncomputable def Ns150p1469 := nat_lit 6280075308963742750215111311360000 

noncomputable def Ns150p1470 := nat_lit 15829266844735940496036344289527070720 

noncomputable abbrev qz537 := (@Eq.refl Real qz739)

noncomputable abbrev qz195 := qz537

noncomputable def Ns150p1471 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz192 420092 1000 705910153856 16000000 840184 4000 2000 Ns150p1469 Ns150p1470 qz195 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns150p1472 := nat_lit 47927377455577404540218790508799204504838057306426242498560 

noncomputable abbrev qz538 := (Enclosure.sfrac Bool.false 420092 2000)

noncomputable abbrev qz743 := (Real.log (Enclosure.sfrac Bool.false 705910153856 16000000))

noncomputable abbrev qz196 := (@HSub.hSub Real Real Real qz344 (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 420092 4000) qz743) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 840184)))))) qz538)

noncomputable abbrev qz539 := (@HSub.hSub Real Real Real qz11 qz196 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 420092 2000) (Real.log Real.pi)))

noncomputable def Ns150p1473 := @Enclosure.Real.IsNear.addLit_ft_p qz539 (Enclosure.sfrac Bool.true Ns150p1469 Ns150p1470) 3027771671842186177623 4503599627370496000 6933307215039073 358400000000000000000 Ns150p1469 Ns150p1470 0 1 Ns150p1472 

noncomputable def Ns150p1474 := nat_lit 50797579337177475414195437568000 

noncomputable abbrev qz540 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 420092 2000) (Real.log Real.pi))

noncomputable def Ns150p1475 := @Enclosure.Real.IsNear.subLit_ff_p qz196 qz540 4110643885631417723991 4503599627370496000 4777813602829 700000000000000000 4034013352503 16777216000 105023 8388608000 Ns150p1474 3027771671842186177623 4503599627370496000 

noncomputable def Ns150p1476 := nat_lit 8221287771262835447982000 

noncomputable abbrev qz197 := (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 420092 4000) qz743) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 840184))))))

noncomputable def Ns150p1477 := @Enclosure.Real.IsNear.subLit_ff_p qz197 qz538 5056606972962080926807 4503599627370496000 4777813602829 700000000000000000 420092 2000 0 1 Ns150p1476 4110643885631417723991 4503599627370496000 4777813602829 700000000000000000 

noncomputable def Ns150p1478 := nat_lit 11386466639595539702083189318023643136 

noncomputable def Ns150p1479 := nat_lit 12929043951777715064930304 

noncomputable def Ns150p1480 := nat_lit 4957153601531660134966602170849419244336773858702839871232198408464304826484538998303262034226053120 

noncomputable def Ns150p1481 := nat_lit 36494736263242644387190553490865852006990792165892889851674042014633151905230557889072762405781504 

noncomputable def Ns150p1482 := nat_lit 124319676799739140196784309524594274320502145407413700422643855086840580368949968610451783680 

noncomputable def Ns150p1483 := BSN.log_dyadic_bound 181622153856 1230198153856 5 4 Ns150p1480 33554432 15680000 Ns150p1481 Ns150p1482 9980658 1411820307712 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 181622153856) (BSN.artanhQ 1230198153856) 0 4 Ns150p1481 Ns150p1480 Ns150p1482 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns150p1484 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 420092 4000) qz743 420092 4000 0 1 48164442001945209 4503599627370496 625000147 9800000000000000 5058374192370291684807 4503599627370496000 65639390438381 9800000000000000000 (Enclosure.Real.IsNear.const Bool.false 420092 4000) (BSN.isNear_log_sfrac 705910153856 16000000 48164442001945209 4503599627370496 625000147 9800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 705910153856) qz352)) Bool.false Ns150p1479 Ns150p86 1000000235200000 15680000000000000000000 48164442001945209 4503599627370496 625000147 9800000000000000 (BSN.log_rat_reduce_isNear 705910153856 16000000 15 1411820307712 1048576000000 9980658 33554432 24973259072661432 36028797018963968 15680000 1000000000000000 rfl rfl rfl rfl (Ns150p1483 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns150p1485 := BSN.arctan_dyadic_bound_f 1000 840184 1 0 4194304 1960000 0 1 1 0 1 1 4992 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 840184) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 840184) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz541 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 840184)))

noncomputable def Ns150p1486 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz541 884279719003555 562949953421312 1 2000000000000000 4992 4194304 1 1960000 3706127716368007561216 883609704105379 562949953421312 50000000049 98000000000000000 qz16 (Ns150p1485 rfl) rfl rfl 

noncomputable def Ns150p1487 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 420092 4000) qz743) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz541)) 5058374192370291684807 4503599627370496000 65639390438381 9800000000000000000 883609704105379 2251799813685248 50000000049 392000000000000000 Ns150p1478 5056606972962080926807 4503599627370496000 4777813602829 700000000000000000 (Ns150p1484 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz541) 1 4 0 1 883609704105379 562949953421312 50000000049 98000000000000000 883609704105379 2251799813685248 50000000049 392000000000000000 qz355 Ns150p1486 rfl) 

noncomputable def Ns150p1488 := @Ns150p1473 Ns150p1467 Ns150p1468 6933307215039073 358400000000000000000 (@Ns150p1475 6933307215039073 358400000000000000000 (Ns150p1477 (Ns150p1487 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 420092 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz538 (Real.log Real.pi) 420092 2000 0 1 38410761 33554432 1 16777216 4034013352503 16777216000 105023 8388608000 (Enclosure.Real.IsNear.const Bool.false 420092 2000) RS151to168.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns150p1469 Ns150p1470) 

noncomputable def Ns150p1489 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz192) Bool.false Ns150p1467 Ns150p1468 6933307215039073 358400000000000000000 5639660889 8388608 163 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz192) (@HAdd.hAdd Real Real Real qz356 qz539 (Enclosure.sfrac Bool.true Ns150p1469 Ns150p1470)) Bool.false Ns150p1467 Ns150p1468 6933307215039073 358400000000000000000 Ns150p1471 (Ns150p1488 rfl rfl)) 

noncomputable def Ns150p1490 := nat_lit 1897936580925271129980928 

noncomputable def Ns150p1491 := nat_lit 139681965031207423693885846953367804122660130889516148189299992911626710450519892640000 

noncomputable def Ns150p1492 := nat_lit 280036839510720459803193015089485813889137246963668615837628728982416132080100000000 

noncomputable def Ns150p1493 := nat_lit 365380324960621133691924429520104129003527453929839210355858106350193663156565271200000 

noncomputable def Ns150p1494 := BSN.sin_dyadic_bound_f 26971301010 17179869184 3 2 8388608 3923829 Ns150p1491 Ns150p98 Ns150p1492 Ns150p1493 Ns150p101 Ns150p1492 8388604 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26971301010) qz357 0 2 Ns150p1491 Ns150p98 Ns150p1492 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26971301010) qz358 0 2 Ns150p1493 Ns150p101 Ns150p1492 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1495 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz192) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5639660889) qz368) Bool.false 5639660889 8388608 163 8388608 Bool.false 8388604 8388608 1 1960000 (Ns150p1489 rfl) (Enclosure.sfrac_false_div 5639660889 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5639660889) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns150p1490) qz369) 226375608064910080 72057594037927936 Bool.false 8388604 8388608 106 1000000000000000 3920000 1960000 (BSN.sin_reduce_arg_pos_rat_q3 5639660889 8388608 226375608064910080 72057594037927936 106 Ns150p1490 Ns150p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388604 8388608 Ns150p1490 Ns150p86 26971301010 17179869184 3923829 3920000 (Ns150p1494 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns150p1496 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz192) Bool.false Ns150p1467 Ns150p1468 6933307215039073 358400000000000000000 45117287115 67108864 1299 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz192) (@HAdd.hAdd Real Real Real qz356 qz539 (Enclosure.sfrac Bool.true Ns150p1469 Ns150p1470)) Bool.false Ns150p1467 Ns150p1468 6933307215039073 358400000000000000000 Ns150p1471 (Ns150p1488 rfl rfl)) 

noncomputable def Ns150p1497 := Ns150p1466 21923 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 242 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 37282397 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 134 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 64207594 67108864) qz195 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz192) qz192 1) Bool.false 2097151 2097152 5122947 256901120000 67108832 67108864 1339 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz192) qz192 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz192)) Bool.false 2097151 2097152 5122947 256901120000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz192) qz192) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz192)) Bool.false 8388604 8388608 327868608 16441671680000 2097151 2097152 5122947 256901120000 (Ns150p1495 rfl rfl) rfl)) rfl) (Ns150p1496 rfl) RS151to168.d7 

noncomputable def Ns150p1498 := nat_lit 642434639757966369328200488860928544091941868910180765462188589056 

noncomputable def Ns150p1499 := nat_lit 355074949950050052526039392798977680687181003296000621034930176 

noncomputable def Ns150p1500 := nat_lit 1926593769373999007879549387797187676914451244723950295144495906816 

noncomputable def Ns150p1501 := BSN.cos_dyadic_bound_f 65885524 67108864 3 2 67108864 33554432 Ns150p1498 Ns150p117 Ns150p1499 Ns150p1500 Ns150p120 Ns150p1499 37282397 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 65885524) qz362 0 2 Ns150p1498 Ns150p117 Ns150p1499 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 65885524) (BSN.cosOddQ 67108864) 0 2 Ns150p1500 Ns150p120 Ns150p1499 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1502 := nat_lit 153852532650153413451532960000 

noncomputable def Ns150p1503 := BSN.cos_dyadic_bound_f 19805060 67108864 2 1 67108864 33554432 Ns150p1502 Ns150p134 Ns150p1502 Ns150p1502 Ns150p135 Ns150p1502 64207594 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 19805060) qz362 0 1 Ns150p1502 Ns150p134 Ns150p1502 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 19805060) (BSN.cosOddQ 67108864) 0 1 Ns150p1502 Ns150p135 Ns150p1502 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1504 := nat_lit 486318728433759701182709760000 

noncomputable def Ns150p1505 := BSN.sin_dyadic_bound_f 26407680 67108864 2 1 67108864 33554432 Ns150p1504 Ns150p107 Ns150p1504 Ns150p1504 Ns150p108 Ns150p1504 25731415 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 26407680) qz361 0 1 Ns150p1504 Ns150p107 Ns150p1504 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 26407680) (BSN.sinOddQ 67108864) 0 1 Ns150p1504 Ns150p108 Ns150p1504 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1506 := nat_lit 139569307834839865513074608876450657145348962254482626406279806976 

noncomputable def Ns150p1507 := nat_lit 16773272229031122978327694489649475689219593789428650314039296 

noncomputable def Ns150p1508 := nat_lit 418674376960061534293267171240372672484668447575869021918211342336 

noncomputable def Ns150p1509 := BSN.cos_dyadic_bound_f 44985984 67108864 3 2 67108864 33554432 Ns150p1506 Ns150p117 Ns150p1507 Ns150p1508 Ns150p120 Ns150p1507 52587067 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 44985984) qz362 0 2 Ns150p1506 Ns150p117 Ns150p1507 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 44985984) (BSN.cosOddQ 67108864) 0 2 Ns150p1508 Ns150p120 Ns150p1507 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1510 := Ns150p1464 37101 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 57 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 25731415 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 2 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 52587067 67108864) qz195 rfl rfl (Ns150p1497 RS151to168.d9 RS151to168.d11 RS151to168.d13 RS151to168.d17 (Ns150p1501 rfl rfl) (Ns150p1503 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns150p1496 rfl) RS151to168.d19 RS151to168.d21 RS151to168.d23 RS151to168.d25 RS151to168.d17 (Ns150p1505 rfl rfl) (Ns150p1509 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns150p1511 := nat_lit 149770444290399176065922205361 

noncomputable def Ns150p1512 := BSN.sin_dyadic_bound_f 19672363 67108864 2 1 67108864 33554432 Ns150p1511 Ns150p107 Ns150p1511 Ns150p1511 Ns150p108 Ns150p1511 19391824 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 19672363) qz361 0 1 Ns150p1511 Ns150p107 Ns150p1511 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 19672363) (BSN.sinOddQ 67108864) 0 1 Ns150p1511 Ns150p108 Ns150p1511 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1513 := nat_lit 121852492504901471219437883404300650036188501002125123317187380641 

noncomputable def Ns150p1514 := nat_lit 12785568103163558599516871357861418045958550261675038885971361 

noncomputable def Ns150p1515 := nat_lit 365531906378498086541114616470186227272473585905852019873790199201 

noncomputable def Ns150p1516 := BSN.cos_dyadic_bound_f 43485053 67108864 3 2 67108864 33554432 Ns150p1513 Ns150p117 Ns150p1514 Ns150p1515 Ns150p120 Ns150p1514 53506299 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 43485053) qz362 0 2 Ns150p1513 Ns150p117 Ns150p1514 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 43485053) (BSN.cosOddQ 67108864) 0 2 Ns150p1515 Ns150p120 Ns150p1514 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1517 := Ns150p1462 49702 BSN.abs_quadSignPos (BSN.cos_quad_nat3 51 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 19391824 67108864) BSN.abs_quadSignPos qz708 (BSN.sfrac_eq_quadSignPos_mul Bool.false 53506299 67108864) qz195 rfl rfl (Ns150p1510 rfl rfl) (Ns150p1496 rfl) RS151to168.d27 RS151to168.d29 RS151to168.d31 RS151to168.d33 RS151to168.d17 (Ns150p1512 rfl rfl) (Ns150p1516 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns150p1518 := nat_lit 29238917511286279207208943616 

noncomputable def Ns150p1519 := BSN.cos_dyadic_bound_f 13076464 67108864 2 1 67108864 33554432 Ns150p1518 Ns150p134 Ns150p1518 Ns150p1518 Ns150p135 Ns150p1518 65838885 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 13076464) qz362 0 1 Ns150p1518 Ns150p134 Ns150p1518 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 13076464) (BSN.cosOddQ 67108864) 0 1 Ns150p1518 Ns150p135 Ns150p1518 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1520 := Ns150p1460 Bool.true 4567276 49702 Bool.true 13076464 3537118876014220 1 Bool.false 65838885 Bool.false Bool.false 18710286 55370 BSN.abs_quadSignPos qz407 (BSN.sfrac_eq_quadSignPos_mul Bool.false 65838885 67108864) qz195 rfl (Ns150p1517 rfl) (Ns150p1496 rfl) RS151to168.d42 RS151to168.d44 RS151to168.d17 (Ns150p1519 rfl rfl) rfl 

noncomputable def Ns150p1521 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz192) qz192 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz192) qz192 8) 18710286 67108864 55370 67108864 18710286 67108864 55370 67108864 2511252077150208 9355143 16777216 27685 16777216 (Ns150p1520 rfl rfl rfl rfl) 

noncomputable def Ns150p1522 := @Enclosure.Real.IsNear.mulLit_ff qz742 (Zeta.RiemannSiegel.correction qz194) 1466793 4194304 1 4194304 10328180273097 17592186044416 9406149101431 107752139522048000 15149302527316767921 73786976294838206464 

noncomputable abbrev qz744 := (@HPow.hPow Real Real Real qz6 qz193 qz8)

noncomputable def Ns150p1523 := @Enclosure.Real.IsNear.mulLit_ff qz48 qz744 1 1 0 1 1466793 4194304 1 4194304 1466793 4194304 1 4194304 

noncomputable def Ns150p1524 := @Enclosure.Real.IsNear.sqrt_image qz193 140215052047 2097152000 105023 2097152000 34295892 34295918 4194304 (@Enclosure.Real.IsNear.of_eq qz193 (@HMul.hMul Real Real Real qz4 qz192 qz2) Bool.false 140215052047 2097152000 105023 2097152000 (BSN.t_div_two_pi_mk qz192 420092 1000 qz195) (@Enclosure.Real.IsNear.mulLit_ff qz192 qz2 420092 1000 0 1 1335089 8388608 1 8388608 140215052047 2097152000 105023 2097152000 (Enclosure.Real.IsNear.const Bool.false 420092 1000) RS151to168.d36 rfl)) 

noncomputable abbrev qz899 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 420092 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz745 := qz899

noncomputable abbrev qz542 := qz745

noncomputable abbrev qz198 := qz542

noncomputable def Ns150p1525 := @Enclosure.Real.IsNear.sqrt_image qz198 34295905 4194304 13 4194304 11993639 11993645 4194304 (@Enclosure.Real.IsNear.recentre' qz198 Bool.false 68591810 8388608 26 8388608 34295905 4194304 13 4194304 (Ns150p1524 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns150p1526 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz198) 5996821 2097152 3 4194304 1466792 1466794 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz198) Bool.false 23987284 8388608 6 8388608 5996821 2097152 3 4194304 (Ns150p1525 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns150p1527 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz198)) Bool.false 2933586 8388608 2 8388608 1466793 4194304 1 4194304 (Ns150p1526 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz199 := (@HMul.hMul Real Real Real qz340 qz338 qz536)

noncomputable abbrev qz746 := (@HMul.hMul Real Real Real qz839 qz898 qz898)

noncomputable abbrev qz543 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz746 qz741) qz638)

noncomputable abbrev qz200 := (Real.cos (@HMul.hMul Real Real Real qz340 qz338 qz543))

noncomputable def Ns150p1528 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz194) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz199)) qz200) Bool.false 10328180273097 

noncomputable def Ns150p1529 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz199)) qz200 9446803 4194304 427 

noncomputable def Ns150p1530 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz199)) Bool.false 18893606 8388608 854 8388608 9446803 4194304 427 

noncomputable def Ns150p1531 := @Enclosure.Real.IsNear.recentre' (Real.cos qz199) Bool.false 1862237 4194304 82457152 4110417920000 1862237 4194304 1288393 64225280000 

noncomputable def Ns150p1532 := @Enclosure.Real.IsNear.cos_image qz199 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1164703) qz712) Bool.false 1164703 1048576 41 2097152 Bool.false 1862237 4194304 1 

noncomputable def Ns150p1533 := nat_lit 350818980323941795488930587 

noncomputable def Ns150p1534 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz194 884279719003555 140737488355328 1 500000000000000 741473 4194304 13 4194304 655669536088722936515 590295810358705651712 Ns150p1533 

noncomputable def Ns150p1535 := @Enclosure.Real.IsNear.subLit_ff_p qz198 qz46 34295905 4194304 13 4194304 8 1 0 1 741473 741473 4194304 13 

noncomputable def Ns150p1536 := @Ns150p1535 4194304 (@Enclosure.Real.IsNear.recentre' qz198 Bool.false 68591810 8388608 26 8388608 34295905 4194304 13 4194304 (Ns150p1524 rfl rfl rfl rfl rfl rfl) rfl) qz410 

noncomputable def Ns150p1537 := @Enclosure.Real.IsNear.recentre' qz199 Bool.false 655669536088722936515 590295810358705651712 Ns150p1533 Ns150p151 1164703 1048576 41 2097152 (@Ns150p1534 Ns150p151 RS151to168.d35 (Ns150p1536 rfl rfl) rfl) 

noncomputable def Ns150p1538 := nat_lit 3740787388826977208278285109993166644787618617475841 

noncomputable def Ns150p1539 := nat_lit 3386269764693868698163710000569276175806910677761 

noncomputable def Ns150p1540 := nat_lit 11215589626951543887438527909978361382011242031072001 

noncomputable def Ns150p1541 := BSN.cos_dyadic_bound_f 1164703 1048576 3 2 4194304 1960000 Ns150p1538 Ns150p1133 Ns150p1539 Ns150p1540 Ns150p1136 Ns150p1539 1862237 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1164703) (BSN.cosEvenQ 1048576) 0 2 Ns150p1538 Ns150p1133 Ns150p1539 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1164703) (BSN.cosOddQ 1048576) 0 2 Ns150p1540 Ns150p1136 Ns150p1539 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1542 := @Enclosure.Real.IsNear.inv_image (Real.cos qz199) 1862237 4194304 1288393 64225280000 9446376 9447230 4194304 (Ns150p1531 (@Ns150p1532 1960000 (Ns150p1537 rfl) (Enclosure.sfrac_false_div 1164703 1048576) (Ns150p1541 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns150p1543 := @Enclosure.Real.IsNear.recentre' qz200 Bool.false 1093299 4194304 

noncomputable abbrev qz201 := (@HMul.hMul Real Real Real qz340 qz338 qz543)

noncomputable def Ns150p1544 := @Enclosure.Real.IsNear.cos_image qz201 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 2741161)) qz386) Bool.true 2741161 2097152 

noncomputable def Ns150p1545 := nat_lit 3236191933213663944390767645 

noncomputable def Ns150p1546 := nat_lit 1991691616686119640184700380891861 

noncomputable def Ns150p1547 := @Enclosure.Real.IsNear.recentre' qz201 Bool.true Ns150p1545 Ns150p268 Ns150p1546 

noncomputable abbrev qz202 := qz543

noncomputable def Ns150p1548 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz202 884279719003555 140737488355328 1 500000000000000 3659692587839 

noncomputable abbrev qz544 := (@HSub.hSub Real Real Real qz634 qz746 qz741)

noncomputable abbrev qz203 := qz544

noncomputable def Ns150p1549 := @Enclosure.Real.IsNear.subLit_tf qz203 qz25 2560180960063 17592186044416 73804419 17592186044416 1 16 

noncomputable abbrev qz545 := qz746

noncomputable abbrev qz204 := qz545

noncomputable def Ns150p1550 := @Enclosure.Real.IsNear.subLit_ff_n qz204 qz194 549782209729 17592186044416 19278467 17592186044416 741473 4194304 13 4194304 

noncomputable def Ns150p1551 := @Enclosure.Real.IsNear.mulLit_ff qz194 qz194 741473 4194304 13 4194304 741473 4194304 13 4194304 549782209729 17592186044416 

noncomputable def Ns150p1552 := nat_lit 1837896282718662295425362582730279002007558454053764161 

noncomputable def Ns150p1553 := nat_lit 3187692010565109499625937172783083441831106560982081 

noncomputable def Ns150p1554 := nat_lit 5507313464134856667276835873845270839139013149039328321 

noncomputable def Ns150p1555 := BSN.cos_dyadic_bound_f 2741161 2097152 3 2 4194304 1960000 Ns150p1552 Ns150p517 Ns150p1553 Ns150p1554 Ns150p520 Ns150p1553 1093299 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2741161) (BSN.cosEvenQ 2097152) 0 2 Ns150p1552 Ns150p517 Ns150p1553 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2741161) (BSN.cosOddQ 2097152) 0 2 Ns150p1554 Ns150p520 Ns150p1553 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1556 := @Ns150p1543 221754304 8220835840000 1093299 4194304 3464911 128450560000 (@Ns150p1544 111 4194304 Bool.false 1093299 4194304 1 1960000 (@Ns150p1547 Ns150p169 2741161 2097152 111 4194304 (@Ns150p1548 17592186044416 73804419 17592186044416 Ns150p1545 Ns150p268 Ns150p1546 Ns150p169 RS151to168.d35 (@Ns150p1549 0 1 58555081405424 3659692587839 17592186044416 73804419 17592186044416 (@Ns150p1550 10738177241516081152 2560180960063 17592186044416 73804419 17592186044416 (@Ns150p1551 19278467 17592186044416 (Ns150p1536 rfl rfl) (Ns150p1536 rfl rfl) rfl) (Ns150p1536 rfl rfl) rfl rfl) qz373 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 2741161 2097152) (BSN.cos_neg_of_bound 2741161 2097152 Bool.false 1093299 4194304 1 1960000 (Ns150p1555 rfl rfl)) rfl rfl) 

noncomputable def Ns150p1557 := @Ns150p1522 1980020452751014477 64563604257983430656000 (Ns150p1523 qz61 (@Enclosure.Real.IsNear.of_eq qz744 (@Inv.inv Real Real.instInv (Real.sqrt qz198)) Bool.false 1466793 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz193 (BSN.t_div_two_pi_nonneg qz192 420092 1000 qz195)) Ns150p1527) rfl) (@Ns150p1528 17592186044416 9406149101431 107752139522048000 (BSN.correction_mk qz194 (BSN.cos_two_pi_p_ne_zero_mk qz192 420092 1000 8 qz195 rfl rfl (@BSN.floor_sqrt_eq_dec qz192 420092 1000 8 qz195 rfl rfl rfl))) (@Ns150p1529 4194304 1093299 4194304 3464911 128450560000 10328180273097 17592186044416 9406149101431 107752139522048000 (@Ns150p1530 4194304 (Ns150p1542 rfl rfl rfl rfl rfl) rfl) (Ns150p1556 rfl) rfl)) 

noncomputable def Ns150p1558 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz192) (hardyZApproximantRS₀ qz192) Bool.false 25995051504712239951 73786976294838206464 108519948405175974477 64563604257983430656000 (@Eq.refl Real (hardyZApproximantRS₀ qz192)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz192) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz192) qz192 8) (@HMul.hMul Real Real Real qz4 qz742 (Zeta.RiemannSiegel.correction qz194))) Bool.false 25995051504712239951 73786976294838206464 108519948405175974477 64563604257983430656000 (BSN.hardyZApproximantRS₀_eq qz192 8 (@BSN.floor_sqrt_eq_dec qz192 420092 1000 8 qz195 rfl rfl rfl)) (@Ns150p1459 25995051504712239951 73786976294838206464 108519948405175974477 64563604257983430656000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz192) qz192 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz192) qz192 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz192) qz192 8)) Bool.false 9355143 16777216 27685 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz192) qz192 8) (Ns150p1521 (Ns150p1520 rfl rfl rfl rfl) rfl rfl)) (Ns150p1557 rfl) rfl rfl)) 

theorem RS151to168.d56 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz192) Bool.false 25995051504712239951 73786976294838206464 108519948405175974477 64563604257983430656000 := Ns150p1558 

noncomputable def Ns150p1559 := nat_lit 5766496370432148128598589440 

noncomputable abbrev qz900 := (Enclosure.sfrac Bool.false 421587 1000)

noncomputable abbrev qz747 := qz900

noncomputable abbrev qz546 := qz747

noncomputable abbrev qz205 := qz546

noncomputable abbrev qz901 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 421587 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz748 := qz901

noncomputable abbrev qz547 := qz748

noncomputable abbrev qz206 := qz547

noncomputable abbrev qz902 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 421587 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz749 := qz902

noncomputable abbrev qz548 := qz749

noncomputable abbrev qz207 := qz548

noncomputable abbrev qz750 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz206 qz8))

noncomputable def Ns150p1560 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz205) qz205 8) (@HMul.hMul Real Real Real qz4 qz750 (Zeta.RiemannSiegel.correction qz207)) 32421837 33554432 27785 16777216 29262236777661191997 147573952589676412928 85658593138666076289 Ns150p422 Ns150p1559 

noncomputable def Ns150p1561 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz205) qz205 Real.cos BSN.quadSignPos 7 8 421587 1000 128 67108864 33554432 1125899906842624 Bool.false 45328194794 1304 139548959 35 23726568 8 

noncomputable def Ns150p1562 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz205) qz205 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 421587 1000 50 92 67108864 33554432 1125899906842624 Bool.false 45328194794 1304 

noncomputable def Ns150p1563 := Ns150p1562 120242927 35 27397080 8 130587807 35 25364760 8 Bool.true 74399836 37236 Bool.true 93942217 Bool.true 27806145 3537118876014220 1 Bool.false 11416346 Bool.true Bool.false 61430157 Bool.false Bool.true 55842129 

noncomputable def Ns150p1564 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz205) qz205 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 421587 1000 57 1 67108864 33554432 1125899906842624 Bool.false 45328194794 1304 

noncomputable def Ns150p1565 := Ns150p1564 93032624 35 33554424 8 108007536 35 30011992 8 Bool.true 11091403 22004 Bool.false 98231586 Bool.true 100963928 3537118876014220 1 Bool.false 66724838 Bool.true Bool.false 66961349 Bool.true Bool.true 74399836 

noncomputable def Ns150p1566 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz205) qz205 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 421587 1000 243 135 67108864 33554432 1125899906842624 Bool.false 45328194794 1304 

noncomputable def Ns150p1567 := Ns150p1566 46516304 35 47453136 16 73726608 35 38745320 8 Bool.true 67108856 1347 Bool.false 101836972 Bool.false 15077103 3537118876014220 1 Bool.false 67013536 Bool.false Bool.false 14950586 Bool.false Bool.true 11091403 

noncomputable def Ns150p1568 := nat_lit 68317725366422619711049655712262330616438224279606897459 

noncomputable def Ns150p1569 := nat_lit 101145103201536666055724632207828157823565070073856000 

noncomputable def Ns150p1570 := nat_lit 6392619242534527916987960019360000 

noncomputable def Ns150p1571 := nat_lit 16170281625950444395228119451787545920 

noncomputable abbrev qz549 := (@Eq.refl Real qz747)

noncomputable abbrev qz208 := qz549

noncomputable def Ns150p1572 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz205 421587 1000 710943394276 16000000 843174 4000 2000 Ns150p1570 Ns150p1571 qz208 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns150p1573 := nat_lit 196755049055297144767823008451315512175342085925267864681920 

noncomputable abbrev qz550 := (Enclosure.sfrac Bool.false 421587 2000)

noncomputable abbrev qz751 := (Real.log (Enclosure.sfrac Bool.false 710943394276 16000000))

noncomputable abbrev qz209 := (@HSub.hSub Real Real Real qz344 (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 421587 4000) qz751) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 843174)))))) qz550)

noncomputable abbrev qz551 := (@HSub.hSub Real Real Real qz11 qz209 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 421587 2000) (Real.log Real.pi)))

noncomputable def Ns150p1574 := @Enclosure.Real.IsNear.addLit_ft_p qz551 (Enclosure.sfrac Bool.true Ns150p1570 Ns150p1571) 12167701760909991277051 18014398509481984000 194818915114463259 10035200000000000000000 Ns150p1570 Ns150p1571 0 1 Ns150p1573 

noncomputable def Ns150p1575 := nat_lit 816560642665469120852801880064000 

noncomputable abbrev qz552 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 421587 2000) (Real.log Real.pi))

noncomputable def Ns150p1576 := @Enclosure.Real.IsNear.subLit_ff_p qz209 qz552 16514605277232708776443 18014398509481984000 268491936978189 39200000000000000000 16193477497707 67108864000 421587 33554432000 Ns150p1575 12167701760909991277051 18014398509481984000 

noncomputable def Ns150p1577 := nat_lit 33029210554465417552886000 

noncomputable abbrev qz210 := (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 421587 4000) qz751) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 843174))))))

noncomputable def Ns150p1578 := @Enclosure.Real.IsNear.subLit_ff_p qz210 qz550 20311923389441199370747 18014398509481984000 268491936978189 39200000000000000000 421587 2000 0 1 Ns150p1577 16514605277232708776443 18014398509481984000 268491936978189 39200000000000000000 

noncomputable def Ns150p1579 := nat_lit 45738385303932723796311615256716640256 

noncomputable def Ns150p1580 := nat_lit 12937633180958239055937536 

noncomputable def Ns150p1581 := nat_lit 5121750007737022728575329316670487510843927923299332672372097363003670358282690658241911508549304320 

noncomputable def Ns150p1582 := nat_lit 39526525953389365985162510365987199778021454610990529681628305020291280248738177940578704877420544 

noncomputable def Ns150p1583 := nat_lit 154708317225066810068027192783913769693393102071109065907235156937861036816733915962887700480 

noncomputable def Ns150p1584 := BSN.log_dyadic_bound 186655394276 1235231394276 5 4 Ns150p1581 33554432 15680000 Ns150p1582 Ns150p1583 10219057 1421886788552 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 186655394276) (BSN.artanhQ 1235231394276) 0 4 Ns150p1582 Ns150p1581 Ns150p1583 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns150p1585 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 421587 4000) qz751 421587 4000 0 1 48196439374082681 4503599627370496 625000147 9800000000000000 20318992286401395234747 18014398509481984000 263491936973289 39200000000000000000 (Enclosure.Real.IsNear.const Bool.false 421587 4000) (BSN.isNear_log_sfrac 710943394276 16000000 48196439374082681 4503599627370496 625000147 9800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 710943394276) qz352)) Bool.false Ns150p1580 Ns150p86 1000000235200000 15680000000000000000000 48196439374082681 4503599627370496 625000147 9800000000000000 (BSN.log_rat_reduce_isNear 710943394276 16000000 15 1421886788552 1048576000000 10219057 33554432 24973259072661432 36028797018963968 15680000 1000000000000000 rfl rfl rfl rfl (Ns150p1584 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns150p1586 := BSN.arctan_dyadic_bound_f 1000 843174 1 0 4194304 1960000 0 1 1 0 1 1 4974 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 843174) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 843174) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz553 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 843174)))

noncomputable def Ns150p1587 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz553 884279719003555 562949953421312 1 2000000000000000 4974 4194304 1 1960000 3706137849467169144832 883612120024483 562949953421312 50000000049 98000000000000000 qz16 (Ns150p1586 rfl) rfl rfl 

noncomputable def Ns150p1588 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 421587 4000) qz751) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz553)) 20318992286401395234747 18014398509481984000 263491936973289 39200000000000000000 883612120024483 2251799813685248 50000000049 392000000000000000 Ns150p1579 20311923389441199370747 18014398509481984000 268491936978189 39200000000000000000 (Ns150p1585 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz553) 1 4 0 1 883612120024483 562949953421312 50000000049 98000000000000000 883612120024483 2251799813685248 50000000049 392000000000000000 qz355 Ns150p1587 rfl) 

noncomputable def Ns150p1589 := @Ns150p1574 Ns150p1568 Ns150p1569 194818915114463259 10035200000000000000000 (@Ns150p1576 194818915114463259 10035200000000000000000 (Ns150p1578 (Ns150p1588 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 421587 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz550 (Real.log Real.pi) 421587 2000 0 1 38410761 33554432 1 16777216 16193477497707 67108864000 421587 33554432000 (Enclosure.Real.IsNear.const Bool.false 421587 2000) RS151to168.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns150p1570 Ns150p1571) 

noncomputable def Ns150p1590 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz205) Bool.false Ns150p1568 Ns150p1569 194818915114463259 10035200000000000000000 5666024349 8388608 41 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz205) (@HAdd.hAdd Real Real Real qz356 qz551 (Enclosure.sfrac Bool.true Ns150p1570 Ns150p1571)) Bool.false Ns150p1568 Ns150p1569 194818915114463259 10035200000000000000000 Ns150p1572 (Ns150p1589 rfl rfl)) 

noncomputable def Ns150p1591 := BSN.cos_dyadic_bound_f 5440863 17179869184 1 0 8388608 3923829 0 1 1 0 1 1 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 5440863) (BSN.cosEvenQ 17179869184) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 5440863) (BSN.cosOddQ 17179869184) 0 0 rfl) rfl rfl 

noncomputable def Ns150p1592 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz205) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5666024349) qz368) Bool.false 5666024349 8388608 41 2097152 Bool.true 8388607 8388608 1 1960000 (Ns150p1590 rfl) (Enclosure.sfrac_false_div 5666024349 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5666024349) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 382866701066728112128) qz369) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 107 1000000000000000 3920000 1960000 (BSN.sin_reduce_arg_pos_rat_q2 5666024349 8388608 226375608064910080 72057594037927936 107 382866701066728112128 Ns150p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 8388607 8388608 382866701066728112128 Ns150p86 5440863 17179869184 3923829 3920000 (Ns150p1591 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns150p1593 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz205) Bool.false Ns150p1568 Ns150p1569 194818915114463259 10035200000000000000000 45328194794 67108864 1304 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz205) (@HAdd.hAdd Real Real Real qz356 qz551 (Enclosure.sfrac Bool.true Ns150p1570 Ns150p1571)) Bool.false Ns150p1568 Ns150p1569 194818915114463259 10035200000000000000000 Ns150p1572 (Ns150p1589 rfl rfl)) 

noncomputable def Ns150p1594 := Ns150p1567 22004 BSN.abs_quadSignPos (BSN.cos_quad_nat3 243 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 67013536 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 135 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 14950586 67108864) qz208 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz205) qz205 1) Bool.true 8388607 8388608 1288393 64225280000 67108856 67108864 1347 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz205) qz205 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz205)) Bool.true 8388607 8388608 1288393 64225280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz205) qz205) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz205)) Bool.true 8388607 8388608 82457152 4110417920000 8388607 8388608 1288393 64225280000 (Ns150p1592 rfl rfl) rfl)) rfl) (Ns150p1593 rfl) RS151to168.d7 

noncomputable def Ns150p1595 := nat_lit 2299964899803736572037383810631439000487632747754022778392419022618869134392990154267476708883553058816 

noncomputable def Ns150p1596 := nat_lit 1244129910909143072559499591073990874449885322563663642162460769142475000097369270901357638844416 

noncomputable def Ns150p1597 := nat_lit 11487375325278689073281570070336533548196190121769741147779762438718803557505647787915878407491211493376 

noncomputable def Ns150p1598 := BSN.sin_dyadic_bound_f 101836972 67108864 4 3 67108864 33554432 Ns150p1595 Ns150p111 Ns150p1596 Ns150p1597 Ns150p114 Ns150p1596 67013536 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 101836972) qz361 0 3 Ns150p1595 Ns150p111 Ns150p1596 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 101836972) (BSN.sinOddQ 67108864) 0 3 Ns150p1597 Ns150p114 Ns150p1596 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1599 := nat_lit 51673943615414426640858466881 

noncomputable def Ns150p1600 := BSN.sin_dyadic_bound_f 15077103 67108864 2 1 67108864 33554432 Ns150p1599 Ns150p107 Ns150p1599 Ns150p1599 Ns150p108 Ns150p1599 14950586 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 15077103) qz361 0 1 Ns150p1599 Ns150p107 Ns150p1599 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 15077103) (BSN.sinOddQ 67108864) 0 1 Ns150p1599 Ns150p108 Ns150p1599 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1601 := nat_lit 1990681477546438814429037477152102730385029029973147727166008139874976678849011765942050725049001578496 

noncomputable def Ns150p1602 := nat_lit 807260815226629728682570674760441558641790355412005785172640809158556419966704842821054359146496 

noncomputable def Ns150p1603 := nat_lit 9944077366237118586614426701077601693392775181610956555879114772498528560096837639182323643226551750656 

noncomputable def Ns150p1604 := BSN.sin_dyadic_bound_f 98231586 67108864 4 3 67108864 33554432 Ns150p1601 Ns150p111 Ns150p1602 Ns150p1603 Ns150p114 Ns150p1602 66724838 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 98231586) qz361 0 3 Ns150p1601 Ns150p111 Ns150p1602 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 98231586) (BSN.sinOddQ 67108864) 0 3 Ns150p1603 Ns150p114 Ns150p1602 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1605 := nat_lit 2221971575218183384535103385552709963546559421826131016256431733313919357071016819321712578523264188416 

noncomputable def Ns150p1606 := nat_lit 1122005178543093514633880775823268637970320086251280555553127006112824081833067759265345506902016 

noncomputable def Ns150p1607 := nat_lit 11098237485195995800831017474459309585313289663743439853422699927079203077870038255660769521482623614976 

noncomputable def Ns150p1608 := BSN.sin_dyadic_bound_f 100963928 67108864 4 3 67108864 33554432 Ns150p1605 Ns150p111 Ns150p1606 Ns150p1607 Ns150p114 Ns150p1606 66961349 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 100963928) qz361 0 3 Ns150p1605 Ns150p111 Ns150p1606 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 100963928) (BSN.sinOddQ 67108864) 0 3 Ns150p1607 Ns150p114 Ns150p1606 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1609 := Ns150p1565 37236 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 57 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66724838 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 1 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66961349 67108864) qz208 rfl rfl (Ns150p1594 RS151to168.d9 RS151to168.d11 RS151to168.d13 RS151to168.d17 (Ns150p1598 rfl rfl) (Ns150p1600 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns150p1593 rfl) RS151to168.d19 RS151to168.d21 RS151to168.d23 RS151to168.d25 RS151to168.d17 (Ns150p1604 rfl rfl) (Ns150p1608 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns150p1610 := nat_lit 640914185928848300777440617334762514909180258088842985131592035802579150957141255514177301541522908641 

noncomputable def Ns150p1611 := nat_lit 472421508242831919523474316680948357183274073901803014505490924994196382979007077781750459540961 

noncomputable def Ns150p1612 := nat_lit 3882299057441943149859307564503797280231920500657100617531799578729402005793828260438627458584932394465 

noncomputable def Ns150p1613 := BSN.cos_dyadic_bound_f 93942217 67108864 4 3 67108864 33554432 Ns150p1610 Ns150p128 Ns150p1611 Ns150p1612 Ns150p131 Ns150p1611 11416346 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 93942217) qz362 0 3 Ns150p1610 Ns150p128 Ns150p1611 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 93942217) (BSN.cosOddQ 67108864) 0 3 Ns150p1612 Ns150p131 Ns150p1611 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1614 := nat_lit 20370401200130374020994113540888141413265653819849495624393690625 

noncomputable def Ns150p1615 := nat_lit 357376725373518243730752552080731454411055580269538812890625 

noncomputable def Ns150p1616 := nat_lit 61110488846940375026494879117560262776888139348387947795555290625 

noncomputable def Ns150p1617 := BSN.cos_dyadic_bound_f 27806145 67108864 3 2 67108864 33554432 Ns150p1614 Ns150p117 Ns150p1615 Ns150p1616 Ns150p120 Ns150p1615 61430157 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 27806145) qz362 0 2 Ns150p1614 Ns150p117 Ns150p1615 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 27806145) (BSN.cosOddQ 67108864) 0 2 Ns150p1616 Ns150p120 Ns150p1615 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1618 := Ns150p1563 49882 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 50 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 11416346 67108864) BSN.abs_quadSignPos qz708 (BSN.sfrac_eq_quadSignPos_mul Bool.false 61430157 67108864) qz208 rfl rfl (Ns150p1609 rfl rfl) (Ns150p1593 rfl) RS151to168.d27 RS151to168.d29 RS151to168.d31 RS151to168.d33 RS151to168.d17 (Ns150p1613 rfl rfl) (Ns150p1617 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns150p1619 := nat_lit 13577091445054555413370236481 

noncomputable def Ns150p1620 := BSN.cos_dyadic_bound_f 10794479 67108864 2 1 67108864 33554432 Ns150p1619 Ns150p134 Ns150p1619 Ns150p1619 Ns150p135 Ns150p1619 66242586 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 10794479) qz362 0 1 Ns150p1619 Ns150p134 Ns150p1619 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 10794479) (BSN.cosOddQ 67108864) 0 1 Ns150p1619 Ns150p135 Ns150p1619 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1621 := Ns150p1561 Bool.true 55842129 49882 Bool.true 10794479 3537118876014220 1 Bool.false 66242586 Bool.false Bool.true 32421837 55570 BSN.abs_quadSignPos qz407 (BSN.sfrac_eq_quadSignPos_mul Bool.false 66242586 67108864) qz208 rfl (Ns150p1618 rfl) (Ns150p1593 rfl) RS151to168.d42 RS151to168.d44 RS151to168.d17 (Ns150p1620 rfl rfl) rfl 

noncomputable def Ns150p1622 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz205) qz205 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz205) qz205 8) 32421837 67108864 55570 67108864 32421837 67108864 55570 67108864 4351585299726336 32421837 33554432 27785 16777216 (Ns150p1621 rfl rfl rfl rfl) 

noncomputable def Ns150p1623 := @Enclosure.Real.IsNear.mulLit_ff qz750 (Zeta.RiemannSiegel.correction qz207) 2930981 8388608 1 8388608 9983768839737 17592186044416 116692244003283 1077521395220480000 29262236777661191997 147573952589676412928 

noncomputable abbrev qz752 := (@HPow.hPow Real Real Real qz6 qz206 qz8)

noncomputable def Ns150p1624 := @Enclosure.Real.IsNear.mulLit_ff qz48 qz752 1 1 0 1 2930981 8388608 1 8388608 2930981 8388608 1 8388608 

noncomputable def Ns150p1625 := @Enclosure.Real.IsNear.sqrt_image qz206 562856166243 8388608000 421587 8388608000 34356863 34356889 4194304 (@Enclosure.Real.IsNear.of_eq qz206 (@HMul.hMul Real Real Real qz4 qz205 qz2) Bool.false 562856166243 8388608000 421587 8388608000 (BSN.t_div_two_pi_mk qz205 421587 1000 qz208) (@Enclosure.Real.IsNear.mulLit_ff qz205 qz2 421587 1000 0 1 1335089 8388608 1 8388608 562856166243 8388608000 421587 8388608000 (Enclosure.Real.IsNear.const Bool.false 421587 1000) RS151to168.d36 rfl)) 

noncomputable abbrev qz903 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 421587 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz753 := qz903

noncomputable abbrev qz554 := qz753

noncomputable abbrev qz211 := qz554

noncomputable def Ns150p1626 := @Enclosure.Real.IsNear.sqrt_image qz211 8589219 1048576 13 4194304 12004296 12004301 4194304 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 68713752 8388608 26 8388608 8589219 1048576 13 4194304 (Ns150p1625 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns150p1627 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz211) 24008597 8388608 5 8388608 1465490 1465491 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz211) Bool.false 24008597 8388608 5 8388608 24008597 8388608 5 8388608 (Ns150p1626 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns150p1628 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz211)) Bool.false 2930981 8388608 1 8388608 2930981 8388608 1 8388608 (Ns150p1627 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz340 qz338 qz548)

noncomputable abbrev qz754 := (@HMul.hMul Real Real Real qz839 qz902 qz902)

noncomputable abbrev qz555 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz754 qz749) qz638)

noncomputable abbrev qz213 := (Real.cos (@HMul.hMul Real Real Real qz340 qz338 qz555))

noncomputable def Ns150p1629 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz207) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz212)) qz213) Bool.false 9983768839737 

noncomputable def Ns150p1630 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz212)) qz213 11637437 4194304 163 

noncomputable def Ns150p1631 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz212)) Bool.false 23274874 8388608 1304 8388608 11637437 4194304 163 

noncomputable def Ns150p1632 := @Enclosure.Real.IsNear.recentre' (Real.cos qz212) Bool.false 1511689 4194304 331788608 16441671680000 1511689 4194304 5184197 256901120000 

noncomputable def Ns150p1633 := @Enclosure.Real.IsNear.cos_image qz212 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 315119) (@Nat.cast Real Real.instNatCast 262144)) Bool.false 315119 262144 165 8388608 Bool.false 1511689 4194304 1 

noncomputable def Ns150p1634 := nat_lit 350818980324465532390939419 

noncomputable def Ns150p1635 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz207 884279719003555 140737488355328 1 500000000000000 200611 1048576 13 4194304 177396238709022172105 147573952589676412928 Ns150p1634 

noncomputable def Ns150p1636 := @Enclosure.Real.IsNear.subLit_ff_p qz211 qz46 8589219 1048576 13 4194304 8 1 0 1 200611 200611 1048576 13 

noncomputable def Ns150p1637 := @Ns150p1636 4194304 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 68713752 8388608 26 8388608 8589219 1048576 13 4194304 (Ns150p1625 rfl rfl rfl rfl rfl rfl) rfl) qz410 

noncomputable def Ns150p1638 := @Enclosure.Real.IsNear.recentre' qz212 Bool.false 177396238709022172105 147573952589676412928 Ns150p1634 Ns150p151 315119 262144 165 8388608 (@Ns150p1635 Ns150p151 RS151to168.d35 (Ns150p1637 rfl rfl) rfl) 

noncomputable def Ns150p1639 := nat_lit 78326148012477879769210712662637496806786901121 

noncomputable def Ns150p1640 := nat_lit 899166046404754725066720160753181935921130373120 

noncomputable def Ns150p1641 := nat_lit 97229201005299241545157377046747337437914241 

noncomputable def Ns150p1642 := nat_lit 234783985635423040824541823233818995745484874881 

noncomputable def Ns150p1643 := nat_lit 40462472088213962628002407233893187116450866790400 

noncomputable def Ns150p1644 := BSN.cos_dyadic_bound_f 315119 262144 3 2 4194304 1960000 Ns150p1639 Ns150p1640 Ns150p1641 Ns150p1642 Ns150p1643 Ns150p1641 1511689 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 315119) (BSN.cosEvenQ 262144) 0 2 Ns150p1639 Ns150p1640 Ns150p1641 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 315119) (BSN.cosOddQ 262144) 0 2 Ns150p1642 Ns150p1643 Ns150p1641 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1645 := @Enclosure.Real.IsNear.inv_image (Real.cos qz212) 1511689 4194304 5184197 256901120000 11636785 11638089 4194304 (Ns150p1632 (@Ns150p1633 1960000 (Ns150p1638 rfl) (Enclosure.sfrac_false_div 315119 262144) (Ns150p1644 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns150p1646 := @Enclosure.Real.IsNear.recentre' qz213 Bool.false 857901 4194304 

noncomputable abbrev qz214 := (@HMul.hMul Real Real Real qz340 qz338 qz555)

noncomputable def Ns150p1647 := @Enclosure.Real.IsNear.cos_image qz214 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 11448797)) qz368) Bool.true 11448797 8388608 

noncomputable def Ns150p1648 := nat_lit 211193041135077401092812805 

noncomputable def Ns150p1649 := nat_lit 2034471184785393182542829647370727 

noncomputable def Ns150p1650 := @Enclosure.Real.IsNear.recentre' qz214 Bool.true Ns150p1648 Ns150p1243 Ns150p1649 

noncomputable abbrev qz215 := qz555

noncomputable def Ns150p1651 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz215 884279719003555 140737488355328 1 500000000000000 238830583351 

noncomputable abbrev qz556 := (@HSub.hSub Real Real Real qz634 qz754 qz749)

noncomputable abbrev qz216 := qz556

noncomputable def Ns150p1652 := @Enclosure.Real.IsNear.subLit_tf qz216 qz25 170111106615 1099511627776 75389665 17592186044416 1 16 

noncomputable abbrev qz557 := qz754

noncomputable abbrev qz217 := qz557

noncomputable def Ns150p1653 := @Enclosure.Real.IsNear.subLit_ff_n qz217 qz207 40244773321 1099511627776 20863713 17592186044416 200611 1048576 13 4194304 

noncomputable def Ns150p1654 := @Enclosure.Real.IsNear.mulLit_ff qz207 qz207 200611 1048576 13 4194304 200611 1048576 13 4194304 40244773321 1099511627776 

noncomputable def Ns150p1655 := nat_lit 143220207928209406492010762967483010499035093816322023777441 

noncomputable def Ns150p1656 := nat_lit 295174502060545076900261939457621944614592229691949081761 

noncomputable def Ns150p1657 := nat_lit 429070274780507129322231765023533787607876096989582173168801 

noncomputable def Ns150p1658 := BSN.cos_dyadic_bound_f 11448797 8388608 3 2 4194304 1960000 Ns150p1655 Ns150p933 Ns150p1656 Ns150p1657 Ns150p936 Ns150p1656 857901 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 11448797) (BSN.cosEvenQ 8388608) 0 2 Ns150p1655 Ns150p933 Ns150p1656 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 11448797) (BSN.cosOddQ 8388608) 0 2 Ns150p1657 Ns150p936 Ns150p1656 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1659 := @Ns150p1646 453308608 16441671680000 857901 4194304 7082947 256901120000 (@Ns150p1647 227 8388608 Bool.false 857901 4194304 1 1960000 (@Ns150p1650 Ns150p169 11448797 8388608 227 8388608 (@Ns150p1651 1099511627776 75389665 17592186044416 Ns150p1648 Ns150p1243 Ns150p1649 Ns150p169 RS151to168.d35 (@Ns150p1652 0 1 3821289333616 238830583351 1099511627776 75389665 17592186044416 (@Ns150p1653 178374423729930240 170111106615 1099511627776 75389665 17592186044416 (@Ns150p1654 20863713 17592186044416 (Ns150p1637 rfl rfl) (Ns150p1637 rfl rfl) rfl) (Ns150p1637 rfl rfl) rfl rfl) qz373 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 11448797 8388608) (BSN.cos_neg_of_bound 11448797 8388608 Bool.false 857901 4194304 1 1960000 (Ns150p1658 rfl rfl)) rfl rfl) 

noncomputable def Ns150p1660 := @Ns150p1623 85658593138666076289 Ns150p422 (Ns150p1624 qz61 (@Enclosure.Real.IsNear.of_eq qz752 (@Inv.inv Real Real.instInv (Real.sqrt qz211)) Bool.false 2930981 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz206 (BSN.t_div_two_pi_nonneg qz205 421587 1000 qz208)) Ns150p1628) rfl) (@Ns150p1629 17592186044416 116692244003283 1077521395220480000 (BSN.correction_mk qz207 (BSN.cos_two_pi_p_ne_zero_mk qz205 421587 1000 8 qz208 rfl rfl (@BSN.floor_sqrt_eq_dec qz205 421587 1000 8 qz208 rfl rfl rfl))) (@Ns150p1630 1048576 857901 4194304 7082947 256901120000 9983768839737 17592186044416 116692244003283 1077521395220480000 (@Ns150p1631 1048576 (Ns150p1645 rfl rfl rfl rfl rfl) rfl) (Ns150p1659 rfl) rfl)) 

noncomputable def Ns150p1661 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz205) (hardyZApproximantRS₀ qz205) Bool.true 171854983879093770045 147573952589676412928 3828025088913795676289 Ns150p422 (@Eq.refl Real (hardyZApproximantRS₀ qz205)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz205) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz205) qz205 8) (@HMul.hMul Real Real Real qz4 qz750 (Zeta.RiemannSiegel.correction qz207))) Bool.true 171854983879093770045 147573952589676412928 3828025088913795676289 Ns150p422 (BSN.hardyZApproximantRS₀_eq qz205 8 (@BSN.floor_sqrt_eq_dec qz205 421587 1000 8 qz208 rfl rfl rfl)) (@Ns150p1560 171854983879093770045 147573952589676412928 3828025088913795676289 Ns150p422 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz205) qz205 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz205) qz205 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz205) qz205 8)) Bool.true 32421837 33554432 27785 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz205) qz205 8) (Ns150p1622 (Ns150p1621 rfl rfl rfl rfl) rfl rfl)) (Ns150p1660 rfl) rfl rfl)) 

theorem RS151to168.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz205) Bool.true 171854983879093770045 147573952589676412928 3828025088913795676289 Ns150p422 := Ns150p1661 

noncomputable def Ns150p1662 := nat_lit 2554092576388992783714615296 

noncomputable abbrev qz904 := (Enclosure.sfrac Bool.false 423080 1000)

noncomputable abbrev qz755 := qz904

noncomputable abbrev qz558 := qz755

noncomputable abbrev qz218 := qz558

noncomputable abbrev qz905 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 423080 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz756 := qz905

noncomputable abbrev qz559 := qz756

noncomputable abbrev qz219 := qz559

noncomputable abbrev qz906 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 423080 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz757 := qz906

noncomputable abbrev qz560 := qz757

noncomputable abbrev qz220 := qz560

noncomputable abbrev qz758 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz219 qz8))

noncomputable def Ns150p1663 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz218) qz218 8) (@HMul.hMul Real Real Real qz4 qz758 (Zeta.RiemannSiegel.correction qz220)) 75661339 33554432 55759 33554432 7072631634037672311 36893488147419103232 16733172934218330241 322818021289917153280000 Ns150p1662 

noncomputable def Ns150p1664 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz218) qz218 Real.cos BSN.quadSignPos 7 8 423080 1000 128 67108864 33554432 1125899906842624 Bool.false 45538997881 1308 139548959 35 23726568 8 

noncomputable def Ns150p1665 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz218) qz218 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 423080 1000 50 92 67108864 33554432 1125899906842624 Bool.false 45538997881 1308 

noncomputable def Ns150p1666 := Ns150p1665 120242927 35 27397080 8 130587807 35 25364760 8 Bool.false 43452160 37361 Bool.true 62661820 Bool.true 11970654 3537118876014220 1 Bool.false 39918813 Bool.true Bool.false 66044049 Bool.false Bool.false 52117670 

noncomputable def Ns150p1667 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz218) qz218 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 423080 1000 58 1 67108864 33554432 1125899906842624 Bool.false 45538997881 1308 

noncomputable def Ns150p1668 := Ns150p1667 93032624 35 33554424 8 108007536 35 30011992 8 Bool.false 83383507 22076 Bool.false 64722609 Bool.true 51416092 3537118876014220 1 Bool.false 38243695 Bool.true Bool.false 46531471 Bool.true Bool.false 43452160 

noncomputable def Ns150p1669 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz218) qz218 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 423080 1000 245 136 67108864 33554432 1125899906842624 Bool.false 45538997881 1308 

noncomputable def Ns150p1670 := Ns150p1669 46516304 35 47453136 16 73726608 35 38745320 8 Bool.false 67108856 1347 Bool.false 32362503 Bool.false 10392007 3537118876014220 1 Bool.false 31122667 Bool.true Bool.false 66305853 Bool.false Bool.false 83383507 

noncomputable def Ns150p1671 := nat_lit 246469217304002327623994071040317493004478085861 

noncomputable def Ns150p1672 := nat_lit 363211092773610580096831138892412159944294400 

noncomputable def Ns150p1673 := nat_lit 6506617132947397256612864000000000 

noncomputable def Ns150p1674 := nat_lit 16516928225137716258215329566720000000 

noncomputable abbrev qz759 := (@Eq.refl Real qz904)

noncomputable abbrev qz561 := qz759

noncomputable abbrev qz221 := qz561

noncomputable def Ns150p1675 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz218 423080 1000 715987745600 16000000 846160 4000 2000 Ns150p1673 Ns150p1674 qz221 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns150p1676 := nat_lit 5047689570385967669739398574905702256731711198433280000000 

noncomputable abbrev qz562 := (Enclosure.sfrac Bool.false 423080 2000)

noncomputable abbrev qz760 := (Real.log (Enclosure.sfrac Bool.false 715987745600 16000000))

noncomputable abbrev qz222 := (@HSub.hSub Real Real Real qz344 (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 423080 4000) qz760) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 846160)))))) qz562)

noncomputable abbrev qz563 := (@HSub.hSub Real Real Real qz11 qz222 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 423080 2000) (Real.log Real.pi)))

noncomputable def Ns150p1677 := @Enclosure.Real.IsNear.addLit_ft_p qz563 (Enclosure.sfrac Bool.true Ns150p1673 Ns150p1674) 305607218963605451249 450359962737049600 4887607751580649 250880000000000000000 Ns150p1673 Ns150p1674 0 1 Ns150p1676 

noncomputable def Ns150p1678 := nat_lit 512723832371170479438194278400 

noncomputable abbrev qz564 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 423080 2000) (Real.log Real.pi))

noncomputable def Ns150p1679 := @Enclosure.Real.IsNear.subLit_ff_p qz222 qz564 414664657860310954481 450359962737049600 13471253109883 1960000000000000000 406270619097 1677721600 10577 838860800 Ns150p1678 305607218963605451249 450359962737049600 

noncomputable abbrev qz223 := (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 423080 4000) qz760) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 846160))))))

noncomputable def Ns150p1680 := @Enclosure.Real.IsNear.subLit_ff_p qz223 qz562 101986760875541285373 90071992547409920 13471253109883 1960000000000000000 423080 2000 0 1 165865863144124381792400 414664657860310954481 450359962737049600 13471253109883 1960000000000000000 

noncomputable def Ns150p1681 := nat_lit 229653769137905806593143949968277504 

noncomputable def Ns150p1682 := nat_lit 12946180580705424029777920 

noncomputable def Ns150p1683 := nat_lit 5291487998851349087617706699178799826558002652901992504697879784835400118568170291200000000000000000 

noncomputable def Ns150p1684 := nat_lit 42751428906310978549134844946849844220134538591195399141810625891101338279912407040000000000000000 

noncomputable def Ns150p1685 := nat_lit 191496830981065501696629173432764876497695507707385614071755337254218550476800000000000000000 

noncomputable def Ns150p1686 := BSN.log_dyadic_bound 191699745600 1240275745600 5 4 Ns150p1683 33554432 15680000 Ns150p1684 Ns150p1685 10456295 1431975491200 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 191699745600) (BSN.artanhQ 1240275745600) 0 4 Ns150p1684 Ns150p1683 Ns150p1685 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns150p1687 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 423080 4000) qz760 423080 4000 0 1 48228280919437945 4503599627370496 625000147 9800000000000000 102022105456979028853 90071992547409920 944375222117 140000000000000000 (Enclosure.Real.IsNear.const Bool.false 423080 4000) (BSN.isNear_log_sfrac 715987745600 16000000 48228280919437945 4503599627370496 625000147 9800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 715987745600) qz352)) Bool.false Ns150p1682 Ns150p86 1000000235200000 15680000000000000000000 48228280919437945 4503599627370496 625000147 9800000000000000 (BSN.log_rat_reduce_isNear 715987745600 16000000 15 1431975491200 1048576000000 10456295 33554432 24973259072661432 36028797018963968 15680000 1000000000000000 rfl rfl rfl rfl (Ns150p1686 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns150p1688 := BSN.arctan_dyadic_bound_f 1000 846160 1 0 4194304 1960000 0 1 1 0 1 1 4956 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 846160) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 846160) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz565 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 846160)))

noncomputable def Ns150p1689 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz565 884279719003555 562949953421312 1 2000000000000000 4956 4194304 1 1960000 3706147982566330728448 883614535943587 562949953421312 50000000049 98000000000000000 qz16 (Ns150p1688 rfl) rfl rfl 

noncomputable def Ns150p1690 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 423080 4000) qz760) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz565)) 102022105456979028853 90071992547409920 944375222117 140000000000000000 883614535943587 2251799813685248 50000000049 392000000000000000 Ns150p1681 101986760875541285373 90071992547409920 13471253109883 1960000000000000000 (Ns150p1687 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz565) 1 4 0 1 883614535943587 562949953421312 50000000049 98000000000000000 883614535943587 2251799813685248 50000000049 392000000000000000 qz355 Ns150p1689 rfl) 

noncomputable def Ns150p1691 := @Ns150p1677 Ns150p1671 Ns150p1672 4887607751580649 250880000000000000000 (@Ns150p1679 4887607751580649 250880000000000000000 (Ns150p1680 (Ns150p1690 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 423080 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz562 (Real.log Real.pi) 423080 2000 0 1 38410761 33554432 1 16777216 406270619097 1677721600 10577 838860800 (Enclosure.Real.IsNear.const Bool.false 423080 2000) RS151to168.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns150p1673 Ns150p1674) 

noncomputable def Ns150p1692 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz218) Bool.false Ns150p1671 Ns150p1672 4887607751580649 250880000000000000000 5692374735 8388608 41 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz218) (@HAdd.hAdd Real Real Real qz356 qz563 (Enclosure.sfrac Bool.true Ns150p1673 Ns150p1674)) Bool.false Ns150p1671 Ns150p1672 4887607751580649 250880000000000000000 Ns150p1675 (Ns150p1691 rfl rfl)) 

noncomputable def Ns150p1693 := nat_lit 1898897464144297019310080 

noncomputable def Ns150p1694 := nat_lit 139965620141714780461326998793557237958386401407932299913508735677832610946018275344640 

noncomputable def Ns150p1695 := nat_lit 281173062907056160780694199047598209111888213129693709468780737845708085354903224576 

noncomputable def Ns150p1696 := nat_lit 366121391602641572186021015756096654695307041818565090910525805580668548910901830205696 

noncomputable def Ns150p1697 := BSN.sin_dyadic_bound_f 26984955982 17179869184 3 2 8388608 3923829 Ns150p1694 Ns150p98 Ns150p1695 Ns150p1696 Ns150p101 Ns150p1695 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26984955982) qz357 0 2 Ns150p1694 Ns150p98 Ns150p1695 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26984955982) qz358 0 2 Ns150p1696 Ns150p101 Ns150p1695 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1698 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz218) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5692374735) qz368) Bool.false 5692374735 8388608 41 2097152 Bool.false 8388607 8388608 1 1960000 (Ns150p1692 rfl) (Enclosure.sfrac_false_div 5692374735 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5692374735) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns150p1693) qz369) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 107 1000000000000000 3920000 1960000 (BSN.sin_reduce_arg_pos_rat_q3 5692374735 8388608 226375608064910080 72057594037927936 107 Ns150p1693 Ns150p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns150p1693 Ns150p86 26984955982 17179869184 3923829 3920000 (Ns150p1697 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns150p1699 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz218) Bool.false Ns150p1671 Ns150p1672 4887607751580649 250880000000000000000 45538997881 67108864 1308 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz218) (@HAdd.hAdd Real Real Real qz356 qz563 (Enclosure.sfrac Bool.true Ns150p1673 Ns150p1674)) Bool.false Ns150p1671 Ns150p1672 4887607751580649 250880000000000000000 Ns150p1675 (Ns150p1691 rfl rfl)) 

noncomputable def Ns150p1700 := Ns150p1670 22076 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 245 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 31122667 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 136 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66305853 67108864) qz221 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz218) qz218 1) Bool.false 8388607 8388608 1288393 64225280000 67108856 67108864 1347 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz218) qz218 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz218)) Bool.false 8388607 8388608 1288393 64225280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz218) qz218) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz218)) Bool.false 8388607 8388608 82457152 4110417920000 8388607 8388608 1288393 64225280000 (Ns150p1698 rfl rfl) rfl)) rfl) (Ns150p1699 rfl) RS151to168.d7 

noncomputable def Ns150p1701 := nat_lit 1096903481248810712149432650081 

noncomputable def Ns150p1702 := BSN.sin_dyadic_bound_f 32362503 67108864 2 1 67108864 33554432 Ns150p1701 Ns150p107 Ns150p1701 Ns150p1701 Ns150p108 Ns150p1701 31122667 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 32362503) qz361 0 1 Ns150p1701 Ns150p107 Ns150p1701 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 32362503) (BSN.sinOddQ 67108864) 0 1 Ns150p1701 Ns150p108 Ns150p1701 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1703 := nat_lit 11662662887741022215473826401 

noncomputable def Ns150p1704 := BSN.cos_dyadic_bound_f 10392007 67108864 2 1 67108864 33554432 Ns150p1703 Ns150p134 Ns150p1703 Ns150p1703 Ns150p135 Ns150p1703 66305853 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 10392007) qz362 0 1 Ns150p1703 Ns150p134 Ns150p1703 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 10392007) (BSN.cosOddQ 67108864) 0 1 Ns150p1703 Ns150p135 Ns150p1703 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1705 := nat_lit 598241437006709728254025759902434786684322792152952340784908169601 

noncomputable def Ns150p1706 := nat_lit 307927250833886261505138078466621713485986954039189516166721921 

noncomputable def Ns150p1707 := nat_lit 1794108456518461412239067003550371116625996402550778643322391064961 

noncomputable def Ns150p1708 := BSN.cos_dyadic_bound_f 64722609 67108864 3 2 67108864 33554432 Ns150p1705 Ns150p117 Ns150p1706 Ns150p1707 Ns150p120 Ns150p1706 38243695 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 64722609) qz362 0 2 Ns150p1705 Ns150p117 Ns150p1706 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 64722609) (BSN.cosOddQ 67108864) 0 2 Ns150p1707 Ns150p120 Ns150p1706 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1709 := nat_lit 428693673786338936741289544112002893497021437150785973273434849280 

noncomputable def Ns150p1710 := nat_lit 48841895711488017404789417554173844669571848932330628007919616 

noncomputable def Ns150p1711 := nat_lit 1122690068275926234675198194569681772934162552401406156604126068736 

noncomputable def Ns150p1712 := BSN.sin_dyadic_bound_f 51416092 67108864 3 2 67108864 33554432 Ns150p1709 Ns150p359 Ns150p1710 Ns150p1711 Ns150p362 Ns150p1710 46531471 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 51416092) qz361 0 2 Ns150p1709 Ns150p359 Ns150p1710 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 51416092) (BSN.sinOddQ 67108864) 0 2 Ns150p1711 Ns150p362 Ns150p1710 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1713 := Ns150p1668 37361 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 58 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 38243695 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 1 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 46531471 67108864) qz221 rfl rfl (Ns150p1700 RS151to168.d9 RS151to168.d11 RS151to168.d13 RS151to168.d17 (Ns150p1702 rfl rfl) (Ns150p1704 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns150p1699 rfl) RS151to168.d19 RS151to168.d21 RS151to168.d23 RS151to168.d25 RS151to168.d17 (Ns150p1708 rfl rfl) (Ns150p1712 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns150p1714 := nat_lit 525578156763201727158153299232401466489256613971270788952268800000 

noncomputable def Ns150p1715 := nat_lit 237697184619043534376002381728358555573184240894349337600000000 

noncomputable def Ns150p1716 := nat_lit 1576259075920367094405707892933747682356623473432023668181606400000 

noncomputable def Ns150p1717 := BSN.cos_dyadic_bound_f 62661820 67108864 3 2 67108864 33554432 Ns150p1714 Ns150p117 Ns150p1715 Ns150p1716 Ns150p120 Ns150p1715 39918813 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 62661820) qz362 0 2 Ns150p1714 Ns150p117 Ns150p1715 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 62661820) (BSN.cosOddQ 67108864) 0 2 Ns150p1716 Ns150p120 Ns150p1715 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1718 := nat_lit 20533903301852362022861296656 

noncomputable def Ns150p1719 := BSN.cos_dyadic_bound_f 11970654 67108864 2 1 67108864 33554432 Ns150p1718 Ns150p134 Ns150p1718 Ns150p1718 Ns150p135 Ns150p1718 66044049 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 11970654) qz362 0 1 Ns150p1718 Ns150p134 Ns150p1718 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 11970654) (BSN.cosOddQ 67108864) 0 1 Ns150p1718 Ns150p135 Ns150p1718 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1720 := Ns150p1666 50051 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 50 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 39918813 67108864) BSN.abs_quadSignPos qz708 (BSN.sfrac_eq_quadSignPos_mul Bool.false 66044049 67108864) qz221 rfl rfl (Ns150p1713 rfl rfl) (Ns150p1699 rfl) RS151to168.d27 RS151to168.d29 RS151to168.d31 RS151to168.d33 RS151to168.d17 (Ns150p1717 rfl rfl) (Ns150p1719 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns150p1721 := nat_lit 4833314586385020505183764736 

noncomputable def Ns150p1722 := BSN.cos_dyadic_bound_f 8337988 67108864 2 1 67108864 33554432 Ns150p1721 Ns150p134 Ns150p1721 Ns150p1721 Ns150p135 Ns150p1721 66591550 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 8337988) qz362 0 1 Ns150p1721 Ns150p134 Ns150p1721 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 8337988) (BSN.cosOddQ 67108864) 0 1 Ns150p1721 Ns150p135 Ns150p1721 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1723 := Ns150p1664 Bool.false 52117670 50051 Bool.true 8337988 3537118876014220 1 Bool.false 66591550 Bool.false Bool.false 75661339 55759 BSN.abs_quadSignPos qz407 (BSN.sfrac_eq_quadSignPos_mul Bool.false 66591550 67108864) qz221 rfl (Ns150p1720 rfl) (Ns150p1699 rfl) RS151to168.d42 RS151to168.d44 RS151to168.d17 (Ns150p1722 rfl rfl) rfl 

noncomputable def Ns150p1724 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz218) qz218 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz218) qz218 8) 75661339 67108864 55759 67108864 75661339 67108864 55759 67108864 10155093018017792 75661339 33554432 55759 33554432 (Ns150p1723 rfl rfl rfl rfl) 

noncomputable def Ns150p1725 := @Enclosure.Real.IsNear.mulLit_ff qz758 (Zeta.RiemannSiegel.correction qz220) 366049 1048576 1 4194304 19321543383639 35184372088832 159591024167467 1077521395220480000 7072631634037672311 36893488147419103232 

noncomputable abbrev qz761 := (@HPow.hPow Real Real Real qz6 qz219 qz8)

noncomputable def Ns150p1726 := @Enclosure.Real.IsNear.mulLit_ff qz48 qz761 1 1 0 1 366049 1048576 1 4194304 366049 1048576 1 4194304 

noncomputable def Ns150p1727 := @Enclosure.Real.IsNear.sqrt_image qz219 14121236353 209715200 10577 209715200 34417644 34417671 4194304 (@Enclosure.Real.IsNear.of_eq qz219 (@HMul.hMul Real Real Real qz4 qz218 qz2) Bool.false 14121236353 209715200 10577 209715200 (BSN.t_div_two_pi_mk qz218 423080 1000 qz221) (@Enclosure.Real.IsNear.mulLit_ff qz218 qz2 423080 1000 0 1 1335089 8388608 1 8388608 14121236353 209715200 10577 209715200 (Enclosure.Real.IsNear.const Bool.false 423080 1000) RS151to168.d36 rfl)) 

noncomputable abbrev qz907 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 423080 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz762 := qz907

noncomputable abbrev qz566 := qz762

noncomputable abbrev qz224 := qz566

noncomputable def Ns150p1728 := @Enclosure.Real.IsNear.sqrt_image qz224 68835315 8388608 27 8388608 12014909 12014915 4194304 (@Enclosure.Real.IsNear.recentre' qz224 Bool.false 68835315 8388608 27 8388608 68835315 8388608 27 8388608 (Ns150p1727 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns150p1729 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz224) 187733 65536 3 4194304 1464195 1464197 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz224) Bool.false 24029824 8388608 6 8388608 187733 65536 3 4194304 (Ns150p1728 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns150p1730 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz224)) Bool.false 2928392 8388608 2 8388608 366049 1048576 1 4194304 (Ns150p1729 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz225 := (@HMul.hMul Real Real Real qz340 qz338 qz560)

noncomputable abbrev qz763 := (@HMul.hMul Real Real Real qz839 qz906 qz906)

noncomputable abbrev qz567 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz763 qz757) qz638)

noncomputable abbrev qz226 := (Real.cos (@HMul.hMul Real Real Real qz340 qz338 qz567))

noncomputable def Ns150p1731 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz220) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz225)) qz226) Bool.false 19321543383639 

noncomputable def Ns150p1732 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz225)) qz226 30603489 8388608 2333 

noncomputable def Ns150p1733 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz225)) Bool.false 30603489 8388608 2333 8388608 30603489 8388608 2333 

noncomputable def Ns150p1734 := @Enclosure.Real.IsNear.recentre' (Real.cos qz225) Bool.false 1149685 4194304 343548608 16441671680000 1149685 4194304 5367947 256901120000 

noncomputable def Ns150p1735 := @Enclosure.Real.IsNear.cos_image qz225 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10847611) qz368) Bool.false 10847611 8388608 171 8388608 Bool.false 1149685 4194304 1 

noncomputable def Ns150p1736 := nat_lit 728624036059019328455855101 

noncomputable def Ns150p1737 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz220 884279719003555 140737488355328 1 500000000000000 1726451 8388608 27 8388608 1526665605153406533305 1180591620717411303424 Ns150p1736 

noncomputable def Ns150p1738 := @Enclosure.Real.IsNear.subLit_ff_p qz224 qz46 68835315 8388608 27 8388608 8 1 0 1 1726451 1726451 8388608 27 

noncomputable def Ns150p1739 := @Ns150p1738 8388608 (@Enclosure.Real.IsNear.recentre' qz224 Bool.false 68835315 8388608 27 8388608 68835315 8388608 27 8388608 (Ns150p1727 rfl rfl rfl rfl rfl rfl) rfl) qz410 

noncomputable def Ns150p1740 := @Enclosure.Real.IsNear.recentre' qz225 Bool.false 1526665605153406533305 1180591620717411303424 Ns150p1736 Ns150p606 10847611 8388608 171 8388608 (@Ns150p1737 Ns150p606 RS151to168.d35 (Ns150p1739 rfl rfl) rfl) 

noncomputable def Ns150p1741 := nat_lit 115379206871476856670878831753999464253192888085183779912161 

noncomputable def Ns150p1742 := nat_lit 191722384825402378285048650678923238446092014081877555681 

noncomputable def Ns150p1743 := nat_lit 345754175844779765256066397960640546282686480227387584625121 

noncomputable def Ns150p1744 := BSN.cos_dyadic_bound_f 10847611 8388608 3 2 4194304 1960000 Ns150p1741 Ns150p933 Ns150p1742 Ns150p1743 Ns150p936 Ns150p1742 1149685 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 10847611) (BSN.cosEvenQ 8388608) 0 2 Ns150p1741 Ns150p933 Ns150p1742 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 10847611) (BSN.cosOddQ 8388608) 0 2 Ns150p1743 Ns150p936 Ns150p1742 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1745 := @Enclosure.Real.IsNear.inv_image (Real.cos qz225) 1149685 4194304 5367947 256901120000 15300578 15302911 4194304 (Ns150p1734 (@Ns150p1735 1960000 (Ns150p1740 rfl) (Enclosure.sfrac_false_div 10847611 8388608) (Ns150p1744 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns150p1746 := @Enclosure.Real.IsNear.recentre' qz226 Bool.false 631351 4194304 

noncomputable abbrev qz227 := (@HMul.hMul Real Real Real qz340 qz338 qz567)

noncomputable def Ns150p1747 := @Enclosure.Real.IsNear.cos_image qz227 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 5954637)) qz359) Bool.true 5954637 4194304 

noncomputable def Ns150p1748 := nat_lit 14059989281035613964826613605 

noncomputable def Ns150p1749 := nat_lit 1725605696408635952821888721986969 

noncomputable def Ns150p1750 := @Enclosure.Real.IsNear.recentre' qz227 Bool.true Ns150p1748 Ns150p617 Ns150p1749 

noncomputable abbrev qz228 := qz567

noncomputable def Ns150p1751 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz228 884279719003555 140737488355328 1 500000000000000 15899934125911 

noncomputable abbrev qz568 := (@HSub.hSub Real Real Real qz634 qz763 qz757)

noncomputable abbrev qz229 := qz568

noncomputable def Ns150p1752 := @Enclosure.Real.IsNear.subLit_tf qz229 qz25 11501887614807 70368744177664 319721499 70368744177664 1 16 

noncomputable abbrev qz569 := qz763

noncomputable abbrev qz230 := qz569

noncomputable def Ns150p1753 := @Enclosure.Real.IsNear.subLit_ff_n qz230 qz220 2980633055401 70368744177664 93229083 70368744177664 1726451 8388608 27 8388608 

noncomputable def Ns150p1754 := @Enclosure.Real.IsNear.mulLit_ff qz220 qz220 1726451 8388608 27 8388608 1726451 8388608 27 8388608 2980633055401 70368744177664 

noncomputable def Ns150p1755 := nat_lit 2409214004848115388935889961529682630853799292265075015813427248743546893169408330154161 

noncomputable def Ns150p1756 := nat_lit 14198936579076412752333613960380805571166435299025227571149477343212749250185412581785600 

noncomputable def Ns150p1757 := nat_lit 1987300307528698192404736385076667613637457400054588092851780606985094426742472881 

noncomputable def Ns150p1758 := nat_lit 14592383388865292932577104588606271215679192257234601370695817403639189750899185539596465 

noncomputable def Ns150p1759 := nat_lit 1292103228695953560462358870394653306976145612211295708974602438232360181766872544942489600 

noncomputable def Ns150p1760 := BSN.cos_dyadic_bound_f 5954637 4194304 4 3 4194304 1960000 Ns150p1755 Ns150p1756 Ns150p1757 Ns150p1758 Ns150p1759 Ns150p1757 631351 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 5954637) (BSN.cosEvenQ 4194304) 0 3 Ns150p1755 Ns150p1756 Ns150p1757 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 5954637) (BSN.cosOddQ 4194304) 0 3 Ns150p1758 Ns150p1759 Ns150p1757 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1761 := @Ns150p1746 29924288 1027604480000 631351 4194304 467567 16056320000 (@Ns150p1747 15 524288 Bool.false 631351 4194304 1 1960000 (@Ns150p1750 Ns150p1144 5954637 4194304 15 524288 (@Ns150p1751 70368744177664 319721499 70368744177664 Ns150p1748 Ns150p617 Ns150p1749 Ns150p1144 RS151to168.d35 (@Ns150p1752 0 1 254398946014576 15899934125911 70368744177664 319721499 70368744177664 (@Ns150p1753 96484826460670918656 11501887614807 70368744177664 319721499 70368744177664 (@Ns150p1754 93229083 70368744177664 (Ns150p1739 rfl rfl) (Ns150p1739 rfl rfl) rfl) (Ns150p1739 rfl rfl) rfl rfl) qz373 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 5954637 4194304) (BSN.cos_neg_of_bound 5954637 4194304 Bool.false 631351 4194304 1 1960000 (Ns150p1760 rfl rfl)) rfl rfl) 

noncomputable def Ns150p1762 := @Ns150p1725 16733172934218330241 322818021289917153280000 (Ns150p1726 qz61 (@Enclosure.Real.IsNear.of_eq qz761 (@Inv.inv Real Real.instInv (Real.sqrt qz224)) Bool.false 366049 1048576 1 4194304 (BSN.rpow_neg_quarter_mk qz219 (BSN.t_div_two_pi_nonneg qz218 423080 1000 qz221)) Ns150p1730) rfl) (@Ns150p1731 35184372088832 159591024167467 1077521395220480000 (BSN.correction_mk qz220 (BSN.cos_two_pi_p_ne_zero_mk qz218 423080 1000 8 qz221 rfl rfl (@BSN.floor_sqrt_eq_dec qz218 423080 1000 8 qz221 rfl rfl rfl))) (@Ns150p1732 8388608 631351 4194304 467567 16056320000 19321543383639 35184372088832 159591024167467 1077521395220480000 (@Ns150p1733 8388608 (Ns150p1745 rfl rfl rfl rfl rfl) rfl) (Ns150p1761 rfl) rfl)) 

noncomputable def Ns150p1763 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz218) (hardyZApproximantRS₀ qz218) Bool.false 76117890369564079753 36893488147419103232 553175275399385690241 322818021289917153280000 (@Eq.refl Real (hardyZApproximantRS₀ qz218)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz218) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz218) qz218 8) (@HMul.hMul Real Real Real qz4 qz758 (Zeta.RiemannSiegel.correction qz220))) Bool.false 76117890369564079753 36893488147419103232 553175275399385690241 322818021289917153280000 (BSN.hardyZApproximantRS₀_eq qz218 8 (@BSN.floor_sqrt_eq_dec qz218 423080 1000 8 qz221 rfl rfl rfl)) (@Ns150p1663 76117890369564079753 36893488147419103232 553175275399385690241 322818021289917153280000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz218) qz218 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz218) qz218 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz218) qz218 8)) Bool.false 75661339 33554432 55759 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz218) qz218 8) (Ns150p1724 (Ns150p1723 rfl rfl rfl rfl) rfl rfl)) (Ns150p1762 rfl) rfl rfl)) 

theorem RS151to168.d58 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz218) Bool.false 76117890369564079753 36893488147419103232 553175275399385690241 322818021289917153280000 := Ns150p1763 

noncomputable def Ns150p1764 := nat_lit 1157572005535386911436177408 

noncomputable abbrev qz908 := (Enclosure.sfrac Bool.false 424572 1000)

noncomputable abbrev qz764 := qz908

noncomputable abbrev qz570 := qz764

noncomputable abbrev qz231 := qz570

noncomputable abbrev qz909 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 424572 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz765 := qz909

noncomputable abbrev qz571 := qz765

noncomputable abbrev qz232 := qz571

noncomputable abbrev qz910 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 424572 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz766 := qz910

noncomputable abbrev qz572 := qz766

noncomputable abbrev qz233 := qz572

noncomputable abbrev qz767 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz232 qz8))

noncomputable def Ns150p1765 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz231) qz231 8) (@HMul.hMul Real Real Real qz4 qz767 (Zeta.RiemannSiegel.correction qz233)) 28263225 16777216 27981 16777216 6845179139974571913 36893488147419103232 9918011517977935537 129127208515966861312000 Ns150p1764 

noncomputable def Ns150p1766 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz231) qz231 Real.cos BSN.quadSignPos 7 8 424572 1000 128 67108864 33554432 1125899906842624 Bool.false 45749836337 1313 139548959 35 23726568 8 

noncomputable def Ns150p1767 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz231) qz231 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 424572 1000 50 91 67108864 33554432 1125899906842624 Bool.false 45749836337 1313 

noncomputable def Ns150p1768 := Ns150p1767 120242927 35 27397080 8 130587807 35 25364760 8 Bool.true 81001903 37498 Bool.true 31225811 Bool.true 101383563 3537118876014220 1 Bool.false 59974293 Bool.true Bool.false 66987848 Bool.false Bool.true 80167287 

noncomputable def Ns150p1769 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz231) qz231 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 424572 1000 59 1 67108864 33554432 1125899906842624 Bool.false 45749836337 1313 

noncomputable def Ns150p1770 := Ns150p1769 93032624 35 33554424 8 108007536 35 30011992 8 Bool.true 95338099 22158 Bool.false 31342033 Bool.true 1724880 3537118876014220 1 Bool.false 30215009 Bool.false Bool.false 1724690 Bool.true Bool.true 81001903 

noncomputable def Ns150p1771 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz231) qz231 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 424572 1000 246 137 67108864 33554432 1125899906842624 Bool.false 45749836337 1313 

noncomputable def Ns150p1772 := Ns150p1771 46516304 35 47453136 16 73726608 35 38745320 8 Bool.true 67108856 1355 Bool.false 68384276 Bool.false 5816007 3537118876014220 1 Bool.false 35179368 Bool.true Bool.false 5808729 Bool.true Bool.true 95338099 

noncomputable def Ns150p1773 := nat_lit 548819332880841327553233635299556558580505729342651 

noncomputable def Ns150p1774 := nat_lit 805044234454336718141674253936034018794405888000 

noncomputable def Ns150p1775 := nat_lit 6622157583342330615554245263360000 

noncomputable def Ns150p1776 := nat_lit 16869507055005595235328814679347691520 

noncomputable abbrev qz768 := (@Eq.refl Real qz908)

noncomputable abbrev qz573 := qz768

noncomputable abbrev qz234 := qz573

noncomputable def Ns150p1777 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz231 424572 1000 721046532736 16000000 849144 4000 2000 Ns150p1775 Ns150p1776 qz234 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns150p1778 := nat_lit 51793090271537496829241356113108103617310113808607965347840 

noncomputable abbrev qz574 := (Enclosure.sfrac Bool.false 424572 2000)

noncomputable abbrev qz769 := (Real.log (Enclosure.sfrac Bool.false 721046532736 16000000))

noncomputable abbrev qz235 := (@HSub.hSub Real Real Real qz344 (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 424572 4000) qz769) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 849144)))))) qz574)

noncomputable abbrev qz575 := (@HSub.hSub Real Real Real qz11 qz235 (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 424572 2000) (Real.log Real.pi)))

noncomputable def Ns150p1779 := @Enclosure.Real.IsNear.addLit_ft_p qz575 (Enclosure.sfrac Bool.true Ns150p1775 Ns150p1776) 3070221312703718653367 4503599627370496000 1000965540508599 51200000000000000000 Ns150p1775 Ns150p1776 0 1 Ns150p1778 

noncomputable def Ns150p1780 := nat_lit 10301953226206766370153457254400 

noncomputable abbrev qz576 := (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 424572 2000) (Real.log Real.pi))

noncomputable def Ns150p1781 := @Enclosure.Real.IsNear.subLit_ff_p qz235 qz576 832928326770922651531 900719925474099200 689687659227 100000000000000000 4077033404823 16777216000 106143 8388608000 Ns150p1780 3070221312703718653367 4503599627370496000 

noncomputable def Ns150p1782 := nat_lit 8329283267709226515310000 

noncomputable abbrev qz236 := (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 424572 4000) qz769) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 849144))))))

noncomputable def Ns150p1783 := @Enclosure.Real.IsNear.subLit_ff_p qz236 qz574 5120692784350586371511 4503599627370496000 689687659227 100000000000000000 424572 2000 0 1 Ns150p1782 832928326770922651531 900719925474099200 689687659227 100000000000000000 

noncomputable def Ns150p1784 := nat_lit 11530775057740044206899488937348169728 

noncomputable def Ns150p1785 := nat_lit 12954692167828372153434112 

noncomputable def Ns150p1786 := nat_lit 5466634746214935740905901616600107264453209580605413169983869431590695777126359663471134123145297920 

noncomputable def Ns150p1787 := nat_lit 46181377702277056137720461944570173334156424366938283173050139108798881772723669267745789039345664 

noncomputable def Ns150p1788 := nat_lit 235861959012731430678934540369659679965476066119927724938005843288410840374735145549042810880 

noncomputable def Ns150p1789 := BSN.log_dyadic_bound 196758532736 1245334532736 5 4 Ns150p1786 33554432 15680000 Ns150p1787 Ns150p1788 10692539 1442093065472 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 196758532736) (BSN.artanhQ 1245334532736) 0 4 Ns150p1787 Ns150p1786 Ns150p1788 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns150p1790 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 424572 4000) qz769 424572 4000 0 1 48259989052371577 4503599627370496 625000147 9800000000000000 5122460017985876297511 4503599627370496000 66339390603021 9800000000000000000 (Enclosure.Real.IsNear.const Bool.false 424572 4000) (BSN.isNear_log_sfrac 721046532736 16000000 48259989052371577 4503599627370496 625000147 9800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 721046532736) qz352)) Bool.false Ns150p1785 Ns150p86 1000000235200000 15680000000000000000000 48259989052371577 4503599627370496 625000147 9800000000000000 (BSN.log_rat_reduce_isNear 721046532736 16000000 15 1442093065472 1048576000000 10692539 33554432 24973259072661432 36028797018963968 15680000 1000000000000000 rfl rfl rfl rfl (Ns150p1789 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns150p1791 := BSN.arctan_dyadic_bound_f 1000 849144 1 0 4194304 1960000 0 1 1 0 1 1 4939 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 849144) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 849144) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz577 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 849144)))

noncomputable def Ns150p1792 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz577 884279719003555 562949953421312 1 2000000000000000 4939 4194304 1 1960000 3706157552715538890752 883616817644963 562949953421312 50000000049 98000000000000000 qz16 (Ns150p1791 rfl) rfl rfl 

noncomputable def Ns150p1793 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 424572 4000) qz769) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz577)) 5122460017985876297511 4503599627370496000 66339390603021 9800000000000000000 883616817644963 2251799813685248 50000000049 392000000000000000 Ns150p1784 5120692784350586371511 4503599627370496000 689687659227 100000000000000000 (Ns150p1790 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz577) 1 4 0 1 883616817644963 562949953421312 50000000049 98000000000000000 883616817644963 2251799813685248 50000000049 392000000000000000 qz355 Ns150p1792 rfl) 

noncomputable def Ns150p1794 := @Ns150p1779 Ns150p1773 Ns150p1774 1000965540508599 51200000000000000000 (@Ns150p1781 1000965540508599 51200000000000000000 (Ns150p1783 (Ns150p1793 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 424572 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz574 (Real.log Real.pi) 424572 2000 0 1 38410761 33554432 1 16777216 4077033404823 16777216000 106143 8388608000 (Enclosure.Real.IsNear.const Bool.false 424572 2000) RS151to168.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns150p1775 Ns150p1776) 

noncomputable def Ns150p1795 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz231) Bool.false Ns150p1773 Ns150p1774 1000965540508599 51200000000000000000 2859364771 4194304 165 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz231) (@HAdd.hAdd Real Real Real qz356 qz575 (Enclosure.sfrac Bool.true Ns150p1775 Ns150p1776)) Bool.false Ns150p1773 Ns150p1774 1000965540508599 51200000000000000000 Ns150p1777 (Ns150p1794 rfl rfl)) 

noncomputable def Ns150p1796 := nat_lit 140017473124008378181831661929719811064585194893136571517824263248265040260139932180065 

noncomputable def Ns150p1797 := nat_lit 281381015558993744376934419938423731941961636353712024505367380547626604375436680801 

noncomputable def Ns150p1798 := nat_lit 366256860347212143461520268374127771507912334451737391649864380367426567131377686797921 

noncomputable def Ns150p1799 := BSN.sin_dyadic_bound_f 26987449899 17179869184 3 2 8388608 3923829 Ns150p1796 Ns150p98 Ns150p1797 Ns150p1798 Ns150p101 Ns150p1797 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26987449899) qz357 0 2 Ns150p1796 Ns150p98 Ns150p1797 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26987449899) qz358 0 2 Ns150p1798 Ns150p101 Ns150p1797 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1800 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz231) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2859364771) qz359) Bool.false 2859364771 4194304 165 8388608 Bool.true 8388607 8388608 1 1960000 (Ns150p1795 rfl) (Enclosure.sfrac_false_div 2859364771 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2859364771) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949536479007920726474752) qz360) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 108 1000000000000000 3920000 1960000 (BSN.sin_reduce_arg_pos_rat_q1 2859364771 4194304 226375608064910080 72057594037927936 108 949536479007920726474752 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 949536479007920726474752 604462909807314587353088 26987449899 17179869184 3923829 3920000 (Ns150p1799 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns150p1801 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz231) Bool.false Ns150p1773 Ns150p1774 1000965540508599 51200000000000000000 45749836337 67108864 1313 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz231) (@HAdd.hAdd Real Real Real qz356 qz575 (Enclosure.sfrac Bool.true Ns150p1775 Ns150p1776)) Bool.false Ns150p1773 Ns150p1774 1000965540508599 51200000000000000000 Ns150p1777 (Ns150p1794 rfl rfl)) 

noncomputable def Ns150p1802 := Ns150p1772 22158 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 246 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 35179368 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 137 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 5808729 67108864) qz234 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 1) Bool.true 8388607 8388608 5184197 256901120000 67108856 67108864 1355 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz231)) Bool.true 8388607 8388608 5184197 256901120000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz231) qz231) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz231)) Bool.true 8388607 8388608 331788608 16441671680000 8388607 8388608 5184197 256901120000 (Ns150p1800 rfl rfl) rfl)) rfl) (Ns150p1801 rfl) RS151to168.d7 

noncomputable def Ns150p1803 := nat_lit 745645639613674373215732054283359520754706184139898372104042643456 

noncomputable def Ns150p1804 := nat_lit 478244546562790180120565461418222152563394822360947410904088576 

noncomputable def Ns150p1805 := nat_lit 2235980429747897539286955031927242117958991762774973221490319753216 

noncomputable def Ns150p1806 := BSN.cos_dyadic_bound_f 68384276 67108864 3 2 67108864 33554432 Ns150p1803 Ns150p117 Ns150p1804 Ns150p1805 Ns150p120 Ns150p1804 35179368 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 68384276) qz362 0 2 Ns150p1803 Ns150p117 Ns150p1804 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 68384276) (BSN.cosOddQ 67108864) 0 2 Ns150p1805 Ns150p120 Ns150p1804 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1807 := nat_lit 1144194042615678697643554401 

noncomputable def Ns150p1808 := BSN.sin_dyadic_bound_f 5816007 67108864 2 1 67108864 33554432 Ns150p1807 Ns150p107 Ns150p1807 Ns150p1807 Ns150p108 Ns150p1807 5808729 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 5816007) qz361 0 1 Ns150p1807 Ns150p107 Ns150p1807 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 5816007) (BSN.sinOddQ 67108864) 0 1 Ns150p1807 Ns150p108 Ns150p1807 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1809 := nat_lit 964958540323590072500127001921 

noncomputable def Ns150p1810 := BSN.sin_dyadic_bound_f 31342033 67108864 2 1 67108864 33554432 Ns150p1809 Ns150p107 Ns150p1809 Ns150p1809 Ns150p108 Ns150p1809 30215009 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 31342033) qz361 0 1 Ns150p1809 Ns150p107 Ns150p1809 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 31342033) (BSN.sinOddQ 67108864) 0 1 Ns150p1809 Ns150p108 Ns150p1809 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1811 := BSN.sin_dyadic_bound_f 1724880 67108864 1 0 67108864 33554432 0 1 1 0 1 1 1724690 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 1724880) qz361 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 1724880) (BSN.sinOddQ 67108864) 0 0 rfl) rfl rfl 

noncomputable def Ns150p1812 := Ns150p1770 37498 BSN.abs_quadSignPos (BSN.cos_quad_nat3 59 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 30215009 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 1 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 1724690 67108864) qz234 rfl rfl (Ns150p1802 RS151to168.d9 RS151to168.d11 RS151to168.d13 RS151to168.d17 (Ns150p1806 rfl rfl) (Ns150p1808 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns150p1801 rfl) RS151to168.d19 RS151to168.d21 RS151to168.d23 RS151to168.d25 RS151to168.d17 (Ns150p1810 rfl rfl) (Ns150p1811 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns150p1813 := nat_lit 32396333042419511914591754952465695500485913422273828473392899361 

noncomputable def Ns150p1814 := nat_lit 903877995608589336537893131847092583246060716806134073173281 

noncomputable def Ns150p1815 := nat_lit 97187191371267318565102189071133392316291248145387873152032351521 

noncomputable def Ns150p1816 := BSN.cos_dyadic_bound_f 31225811 67108864 3 2 67108864 33554432 Ns150p1813 Ns150p117 Ns150p1814 Ns150p1815 Ns150p120 Ns150p1814 59974293 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 31225811) qz362 0 2 Ns150p1813 Ns150p117 Ns150p1814 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 31225811) (BSN.cosOddQ 67108864) 0 2 Ns150p1815 Ns150p120 Ns150p1814 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1817 := nat_lit 2259207078042021017851539679570101759553698272181164387518375745584905349997494225264989257334211828881 

noncomputable def Ns150p1818 := nat_lit 1179262799729649251663363469323038905729024744436979690187416621047350609326530029023463215553681 

noncomputable def Ns150p1819 := nat_lit 11284022872664504252617791200774838935377844538934528122774645370285915531980603040521827900443133828241 

noncomputable def Ns150p1820 := BSN.sin_dyadic_bound_f 101383563 67108864 4 3 67108864 33554432 Ns150p1817 Ns150p111 Ns150p1818 Ns150p1819 Ns150p114 Ns150p1818 66987848 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 101383563) qz361 0 3 Ns150p1817 Ns150p111 Ns150p1818 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 101383563) (BSN.sinOddQ 67108864) 0 3 Ns150p1819 Ns150p114 Ns150p1818 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1821 := Ns150p1768 50233 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 50 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 59974293 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 91 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66987848 67108864) qz234 rfl rfl (Ns150p1812 rfl rfl) (Ns150p1801 rfl) RS151to168.d27 RS151to168.d29 RS151to168.d31 RS151to168.d33 RS151to168.d17 (Ns150p1816 rfl rfl) (Ns150p1820 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns150p1822 := nat_lit 1060482083117412068840664081 

noncomputable def Ns150p1823 := BSN.cos_dyadic_bound_f 5706579 67108864 2 1 67108864 33554432 Ns150p1822 Ns150p134 Ns150p1822 Ns150p1822 Ns150p135 Ns150p1822 66866381 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 5706579) qz362 0 1 Ns150p1822 Ns150p134 Ns150p1822 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 5706579) (BSN.cosOddQ 67108864) 0 1 Ns150p1822 Ns150p135 Ns150p1822 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1824 := Ns150p1766 Bool.true 80167287 50233 Bool.true 5706579 3537118876014220 1 Bool.false 66866381 Bool.false Bool.true 56526450 55962 BSN.abs_quadSignPos qz407 (BSN.sfrac_eq_quadSignPos_mul Bool.false 66866381 67108864) qz234 rfl (Ns150p1821 rfl) (Ns150p1801 rfl) RS151to168.d42 RS151to168.d44 RS151to168.d17 (Ns150p1823 rfl rfl) rfl 

noncomputable def Ns150p1825 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 8) 56526450 67108864 55962 67108864 56526450 67108864 55962 67108864 7586851690905600 28263225 16777216 27981 16777216 (Ns150p1824 rfl rfl rfl rfl) 

noncomputable def Ns150p1826 := @Enclosure.Real.IsNear.mulLit_ff qz767 (Zeta.RiemannSiegel.correction qz233) 365727 1048576 1 4194304 18716636015319 35184372088832 11844797118319 53876069761024000 6845179139974571913 36893488147419103232 

noncomputable abbrev qz770 := (@HPow.hPow Real Real Real qz6 qz232 qz8)

noncomputable def Ns150p1827 := @Enclosure.Real.IsNear.mulLit_ff qz48 qz770 1 1 0 1 365727 1048576 1 4194304 365727 1048576 1 4194304 

noncomputable def Ns150p1828 := @Enclosure.Real.IsNear.sqrt_image qz232 141710351727 2097152000 106143 2097152000 34478278 34478305 4194304 (@Enclosure.Real.IsNear.of_eq qz232 (@HMul.hMul Real Real Real qz4 qz231 qz2) Bool.false 141710351727 2097152000 106143 2097152000 (BSN.t_div_two_pi_mk qz231 424572 1000 qz234) (@Enclosure.Real.IsNear.mulLit_ff qz231 qz2 424572 1000 0 1 1335089 8388608 1 8388608 141710351727 2097152000 106143 2097152000 (Enclosure.Real.IsNear.const Bool.false 424572 1000) RS151to168.d36 rfl)) 

noncomputable abbrev qz911 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 424572 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz771 := qz911

noncomputable abbrev qz578 := qz771

noncomputable abbrev qz237 := qz578

noncomputable def Ns150p1829 := @Enclosure.Real.IsNear.sqrt_image qz237 68956583 8388608 27 8388608 12025488 12025494 4194304 (@Enclosure.Real.IsNear.recentre' qz237 Bool.false 68956583 8388608 27 8388608 68956583 8388608 27 8388608 (Ns150p1828 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns150p1830 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz237) 12025491 4194304 3 4194304 1462907 1462909 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz237) Bool.false 24050982 8388608 6 8388608 12025491 4194304 3 4194304 (Ns150p1829 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns150p1831 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz237)) Bool.false 2925816 8388608 2 8388608 365727 1048576 1 4194304 (Ns150p1830 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz238 := (@HMul.hMul Real Real Real qz340 qz338 qz572)

noncomputable abbrev qz772 := (@HMul.hMul Real Real Real qz839 qz910 qz910)

noncomputable abbrev qz579 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz772 qz766) qz638)

noncomputable abbrev qz239 := (Real.cos (@HMul.hMul Real Real Real qz340 qz338 qz579))

noncomputable def Ns150p1832 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz233) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz238)) qz239) Bool.false 18716636015319 

noncomputable def Ns150p1833 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz238)) qz239 45162249 8388608 5081 

noncomputable def Ns150p1834 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz238)) Bool.false 45162249 8388608 5081 8388608 45162249 8388608 5081 

noncomputable def Ns150p1835 := @Enclosure.Real.IsNear.recentre' (Real.cos qz238) Bool.false 779066 4194304 343548608 16441671680000 389533 2097152 5367947 256901120000 

noncomputable def Ns150p1836 := @Enclosure.Real.IsNear.cos_image qz238 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1451195) qz712) Bool.false 1451195 1048576 171 8388608 Bool.false 779066 4194304 1 

noncomputable def Ns150p1837 := nat_lit 728624036060061012643957757 

noncomputable def Ns150p1838 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz233 884279719003555 140737488355328 1 500000000000000 1847719 8388608 27 8388608 1633900438117529641045 1180591620717411303424 Ns150p1837 

noncomputable def Ns150p1839 := @Enclosure.Real.IsNear.subLit_ff_p qz237 qz46 68956583 8388608 27 8388608 8 1 0 1 1847719 1847719 8388608 27 

noncomputable def Ns150p1840 := @Ns150p1839 8388608 (@Enclosure.Real.IsNear.recentre' qz237 Bool.false 68956583 8388608 27 8388608 68956583 8388608 27 8388608 (Ns150p1828 rfl rfl rfl rfl rfl rfl) rfl) qz410 

noncomputable def Ns150p1841 := @Enclosure.Real.IsNear.recentre' qz238 Bool.false 1633900438117529641045 1180591620717411303424 Ns150p1837 Ns150p606 1451195 1048576 171 8388608 (@Ns150p1838 Ns150p606 RS151to168.d35 (Ns150p1840 rfl rfl) rfl) 

noncomputable def Ns150p1842 := nat_lit 9027330980723234412286305991092888160021075157190625 

noncomputable def Ns150p1843 := nat_lit 19670082755515206798137563136609044143573000390625 

noncomputable def Ns150p1844 := nat_lit 27042652776658672823262642847005446391776079470790625 

noncomputable def Ns150p1845 := BSN.cos_dyadic_bound_f 1451195 1048576 3 2 4194304 1960000 Ns150p1842 Ns150p1133 Ns150p1843 Ns150p1844 Ns150p1136 Ns150p1843 779066 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1451195) (BSN.cosEvenQ 1048576) 0 2 Ns150p1842 Ns150p1133 Ns150p1843 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1451195) (BSN.cosOddQ 1048576) 0 2 Ns150p1844 Ns150p1136 Ns150p1843 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1846 := @Enclosure.Real.IsNear.inv_image (Real.cos qz238) 389533 2097152 5367947 256901120000 22578584 22583665 4194304 (Ns150p1835 (@Ns150p1836 1960000 (Ns150p1841 rfl) (Enclosure.sfrac_false_div 1451195 1048576) (Ns150p1845 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns150p1847 := @Enclosure.Real.IsNear.recentre' qz239 Bool.false 414431 4194304 

noncomputable abbrev qz240 := (@HMul.hMul Real Real Real qz340 qz338 qz579)

noncomputable def Ns150p1848 := @Enclosure.Real.IsNear.cos_image qz240 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 771661)) (@Nat.cast Real Real.instNatCast 524288)) Bool.true 771661 524288 

noncomputable def Ns150p1849 := nat_lit 14576264735781740891408163725 

noncomputable def Ns150p1850 := nat_lit 8804746041254208366478545420550597 

noncomputable def Ns150p1851 := @Enclosure.Real.IsNear.recentre' qz240 Bool.true Ns150p1849 Ns150p617 Ns150p1850 

noncomputable abbrev qz241 := qz579

noncomputable def Ns150p1852 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz241 884279719003555 140737488355328 1 500000000000000 16483771393295 

noncomputable abbrev qz580 := (@HSub.hSub Real Real Real qz634 qz772 qz766)

noncomputable abbrev qz242 := qz580

noncomputable def Ns150p1853 := @Enclosure.Real.IsNear.subLit_tf qz242 qz25 12085724882191 70368744177664 326269971 70368744177664 1 16 

noncomputable abbrev qz581 := qz772

noncomputable abbrev qz243 := qz581

noncomputable def Ns150p1854 := @Enclosure.Real.IsNear.subLit_ff_n qz243 qz233 3414065502961 70368744177664 99777555 70368744177664 1847719 8388608 27 8388608 

noncomputable def Ns150p1855 := @Enclosure.Real.IsNear.mulLit_ff qz233 qz233 1847719 8388608 27 8388608 1847719 8388608 27 8388608 3414065502961 70368744177664 

noncomputable def Ns150p1856 := nat_lit 40513817697780640490858707499091912178578800504865054789316461744888332622001 

noncomputable def Ns150p1857 := nat_lit 206621721431677182442706747102504677185300319965248164533833585202413803929600 

noncomputable def Ns150p1858 := nat_lit 44577798524180022085815401693877304726962147582790957221332857525049521 

noncomputable def Ns150p1859 := nat_lit 245327178636565842362588458725828367188438617443938309744569631877688746252465 

noncomputable def Ns150p1860 := nat_lit 18802576650282623602286313986327925623862329116837582972578856253419656157593600 

noncomputable def Ns150p1861 := BSN.cos_dyadic_bound_f 771661 524288 4 3 4194304 1960000 Ns150p1856 Ns150p1857 Ns150p1858 Ns150p1859 Ns150p1860 Ns150p1858 414431 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 771661) (BSN.cosEvenQ 524288) 0 3 Ns150p1856 Ns150p1857 Ns150p1858 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 771661) (BSN.cosOddQ 524288) 0 3 Ns150p1859 Ns150p1860 Ns150p1858 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1862 := @Ns150p1847 488588608 16441671680000 414431 4194304 7634197 256901120000 (@Ns150p1848 245 8388608 Bool.false 414431 4194304 1 1960000 (@Ns150p1851 Ns150p620 771661 524288 245 8388608 (@Ns150p1852 70368744177664 326269971 70368744177664 Ns150p1849 Ns150p617 Ns150p1850 Ns150p620 RS151to168.d35 (@Ns150p1853 0 1 263740342292720 16483771393295 70368744177664 326269971 70368744177664 (@Ns150p1854 101382408432546480128 12085724882191 70368744177664 326269971 70368744177664 (@Ns150p1855 99777555 70368744177664 (Ns150p1840 rfl rfl) (Ns150p1840 rfl rfl) rfl) (Ns150p1840 rfl rfl) rfl rfl) qz373 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 771661 524288) (BSN.cos_neg_of_bound 771661 524288 Bool.false 414431 4194304 1 1960000 (Ns150p1861 rfl rfl)) rfl rfl) 

noncomputable def Ns150p1863 := @Ns150p1826 9918011517977935537 129127208515966861312000 (Ns150p1827 qz61 (@Enclosure.Real.IsNear.of_eq qz770 (@Inv.inv Real Real.instInv (Real.sqrt qz237)) Bool.false 365727 1048576 1 4194304 (BSN.rpow_neg_quarter_mk qz232 (BSN.t_div_two_pi_nonneg qz231 424572 1000 qz234)) Ns150p1831) rfl) (@Ns150p1832 35184372088832 11844797118319 53876069761024000 (BSN.correction_mk qz233 (BSN.cos_two_pi_p_ne_zero_mk qz231 424572 1000 8 qz234 rfl rfl (@BSN.floor_sqrt_eq_dec qz231 424572 1000 8 qz234 rfl rfl rfl))) (@Ns150p1833 8388608 414431 4194304 7634197 256901120000 18716636015319 35184372088832 11844797118319 53876069761024000 (@Ns150p1834 8388608 (Ns150p1846 rfl rfl rfl rfl rfl) rfl) (Ns150p1862 rfl) rfl)) 

noncomputable def Ns150p1864 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz231) (hardyZApproximantRS₀ qz231) Bool.true 68996668191873247113 36893488147419103232 225276055515579727537 129127208515966861312000 (@Eq.refl Real (hardyZApproximantRS₀ qz231)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz231) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz231) qz231 8) (@HMul.hMul Real Real Real qz4 qz767 (Zeta.RiemannSiegel.correction qz233))) Bool.true 68996668191873247113 36893488147419103232 225276055515579727537 129127208515966861312000 (BSN.hardyZApproximantRS₀_eq qz231 8 (@BSN.floor_sqrt_eq_dec qz231 424572 1000 8 qz234 rfl rfl rfl)) (@Ns150p1765 68996668191873247113 36893488147419103232 225276055515579727537 129127208515966861312000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz231) qz231 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 8)) Bool.true 28263225 16777216 27981 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz231) qz231 8) (Ns150p1825 (Ns150p1824 rfl rfl rfl rfl) rfl rfl)) (Ns150p1863 rfl) rfl rfl)) 

theorem RS151to168.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz231) Bool.true 68996668191873247113 36893488147419103232 225276055515579727537 129127208515966861312000 := Ns150p1864 

noncomputable def Ns150p1865 := nat_lit 10346001781498450267930624 

noncomputable abbrev qz912 := (Enclosure.sfrac Bool.false 426063 1000)

noncomputable abbrev qz773 := qz912

noncomputable abbrev qz582 := qz773

noncomputable abbrev qz244 := qz582

noncomputable abbrev qz913 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 426063 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz774 := qz913

noncomputable abbrev qz583 := qz774

noncomputable abbrev qz245 := qz583

noncomputable abbrev qz914 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 426063 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz775 := qz914

noncomputable abbrev qz584 := qz775

noncomputable abbrev qz246 := qz584

noncomputable abbrev qz776 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz245 qz8))

noncomputable def Ns150p1866 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz244) qz244 8) (@HMul.hMul Real Real Real qz4 qz776 (Zeta.RiemannSiegel.correction qz246)) 292211 65536 28079 16777216 6632710015060933023 36893488147419103232 676287029122612115829 Ns150p1358 Ns150p1865 

noncomputable def Ns150p1867 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz244) qz244 Real.cos BSN.quadSignPos 7 8 426063 1000 128 67108864 33554432 1125899906842624 Bool.false 45960709285 1317 139548959 35 23726568 8 

noncomputable def Ns150p1868 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz244) qz244 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 426063 1000 49 91 67108864 33554432 1125899906842624 Bool.false 45960709285 1317 

noncomputable def Ns150p1869 := Ns150p1868 120242927 35 27397080 8 130587807 35 25364760 8 Bool.false 129079660 37631 Bool.true 105049425 Bool.true 85217035 3537118876014220 1 Bool.false 67107871 Bool.true Bool.false 64092407 Bool.false Bool.false 125907632 

noncomputable def Ns150p1870 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz244) qz244 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 426063 1000 59 0 67108864 33554432 1125899906842624 Bool.false 45960709285 1317 

noncomputable def Ns150p1871 := Ns150p1870 93032624 35 33554424 8 108007536 35 30011992 8 Bool.false 75819944 22238 Bool.false 103503338 Bool.true 57305525 3537118876014220 1 Bool.false 67081656 Bool.false Bool.false 44092799 Bool.false Bool.false 129079660 

noncomputable def Ns150p1872 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz244) qz244 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 426063 1000 247 138 67108864 33554432 1125899906842624 Bool.false 45960709285 1317 

noncomputable def Ns150p1873 := Ns150p1872 46516304 35 47453136 16 73726608 35 38745320 8 Bool.false 67108840 1363 Bool.false 104487058 Bool.false 1348225 3537118876014220 1 Bool.false 67102457 Bool.false Bool.false 67095321 Bool.true Bool.false 75819944 

noncomputable def Ns150p1874 := nat_lit 73802542102736635136932479862705522542633277696651682631 

noncomputable def Ns150p1875 := nat_lit 107761712947272525095614062247361315187300191174656000 

noncomputable def Ns150p1876 := nat_lit 6739254504384614780631583940640000 

noncomputable def Ns150p1877 := nat_lit 17228093023743666482881425853901401920 

noncomputable abbrev qz915 := (@Eq.refl Real (Enclosure.sfrac Bool.false 426063 1000))

noncomputable abbrev qz777 := qz915

noncomputable abbrev qz585 := qz777

noncomputable abbrev qz247 := qz585

noncomputable def Ns150p1878 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz244 426063 1000 726119719876 16000000 852126 4000 2000 Ns150p1876 Ns150p1877 qz247 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns150p1879 := nat_lit 212551321255881509194365542004591904922783839766356845977280 

noncomputable abbrev qz778 := (Real.log (Enclosure.sfrac Bool.false 726119719876 16000000))

noncomputable abbrev qz248 := (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 426063 4000) qz778) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 852126))))))

noncomputable abbrev qz779 := (Enclosure.sfrac Bool.false 426063 2000)

noncomputable abbrev qz586 := (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 qz248 qz779) (@HMul.hMul Real Real Real qz4 qz779 (Real.log Real.pi)))

noncomputable def Ns150p1880 := @Enclosure.Real.IsNear.addLit_ft_p qz586 (Enclosure.sfrac Bool.true Ns150p1876 Ns150p1877) 12337491001851483876759 18014398509481984000 28124817534834513 1433600000000000000000 Ns150p1876 Ns150p1877 0 1 Ns150p1879 

noncomputable def Ns150p1881 := nat_lit 827955005744474979683612491776000 

noncomputable abbrev qz587 := (@HSub.hSub Real Real Real qz11 qz248 qz779)

noncomputable abbrev qz588 := (@HMul.hMul Real Real Real qz4 qz779 (Real.log Real.pi))

noncomputable def Ns150p1882 := @Enclosure.Real.IsNear.subLit_ff_p qz587 qz588 16730545704380276239767 18014398509481984000 38755633948023 5600000000000000000 16365404063943 67108864000 426063 33554432000 Ns150p1881 12337491001851483876759 18014398509481984000 

noncomputable def Ns150p1883 := nat_lit 33461091408760552479534000 

noncomputable abbrev qz589 := qz779

noncomputable def Ns150p1884 := @Enclosure.Real.IsNear.subLit_ff_p qz248 qz589 20568180040452987514263 18014398509481984000 38755633948023 5600000000000000000 426063 2000 0 1 Ns150p1883 16730545704380276239767 18014398509481984000 38755633948023 5600000000000000000 

noncomputable def Ns150p1885 := nat_lit 46315423982936673956269087020992692224 

noncomputable def Ns150p1886 := nat_lit 12963168230557459578617856 

noncomputable def Ns150p1887 := nat_lit 5647353570137242635571149722672123845223829680096764393017292843569996982910909852822356071661240320 

noncomputable def Ns150p1888 := nat_lit 49826770670295355252367617299157928090056934691550052248449809971579811398067361494192547175071744 

noncomputable def Ns150p1889 := nat_lit 289137663371668183009717233310834481644269632731147330201208863670130818710252117408566804480 

noncomputable def Ns150p1890 := BSN.log_dyadic_bound 201831719876 1250407719876 5 4 Ns150p1887 33554432 15680000 Ns150p1888 Ns150p1889 10927797 1452239439752 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 201831719876) (BSN.artanhQ 1250407719876) 0 4 Ns150p1888 Ns150p1887 Ns150p1889 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns150p1891 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 426063 4000) qz778 426063 4000 0 1 48291564846625401 4503599627370496 625000147 9800000000000000 20575248993247758226263 18014398509481984000 266289437631261 39200000000000000000 (Enclosure.Real.IsNear.const Bool.false 426063 4000) (BSN.isNear_log_sfrac 726119719876 16000000 48291564846625401 4503599627370496 625000147 9800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 726119719876) qz352)) Bool.false Ns150p1886 Ns150p86 1000000235200000 15680000000000000000000 48291564846625401 4503599627370496 625000147 9800000000000000 (BSN.log_rat_reduce_isNear 726119719876 16000000 15 1452239439752 1048576000000 10927797 33554432 24973259072661432 36028797018963968 15680000 1000000000000000 rfl rfl rfl rfl (Ns150p1890 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns150p1892 := BSN.arctan_dyadic_bound_f 1000 852126 1 0 4194304 1960000 0 1 1 0 1 1 4922 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 852126) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 852126) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz590 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 852126)))

noncomputable def Ns150p1893 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz590 884279719003555 562949953421312 1 2000000000000000 4922 4194304 1 1960000 3706167122864747053056 883619099346339 562949953421312 50000000049 98000000000000000 qz16 (Ns150p1892 rfl) rfl rfl 

noncomputable def Ns150p1894 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 426063 4000) qz778) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz590)) 20575248993247758226263 18014398509481984000 266289437631261 39200000000000000000 883619099346339 2251799813685248 50000000049 392000000000000000 Ns150p1885 20568180040452987514263 18014398509481984000 38755633948023 5600000000000000000 (Ns150p1891 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz590) 1 4 0 1 883619099346339 562949953421312 50000000049 98000000000000000 883619099346339 2251799813685248 50000000049 392000000000000000 qz355 Ns150p1893 rfl) 

noncomputable def Ns150p1895 := @Ns150p1880 Ns150p1874 Ns150p1875 28124817534834513 1433600000000000000000 (@Ns150p1882 28124817534834513 1433600000000000000000 (Ns150p1884 (Ns150p1894 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 426063 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz589 (Real.log Real.pi) 426063 2000 0 1 38410761 33554432 1 16777216 16365404063943 67108864000 426063 33554432000 (Enclosure.Real.IsNear.const Bool.false 426063 2000) RS151to168.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns150p1876 Ns150p1877) 

noncomputable def Ns150p1896 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz244) Bool.false Ns150p1874 Ns150p1875 28124817534834513 1433600000000000000000 1436272165 2097152 83 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz244) (@HAdd.hAdd Real Real Real qz356 qz586 (Enclosure.sfrac Bool.true Ns150p1876 Ns150p1877)) Bool.false Ns150p1874 Ns150p1875 28124817534834513 1433600000000000000000 Ns150p1878 (Ns150p1895 rfl rfl)) 

noncomputable def Ns150p1897 := BSN.cos_dyadic_bound_f 12697336 17179869184 1 0 8388608 3923829 0 1 1 0 1 1 8388605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 12697336) (BSN.cosEvenQ 17179869184) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 12697336) (BSN.cosOddQ 17179869184) 0 0 rfl) rfl rfl 

noncomputable def Ns150p1898 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz244) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1436272165) qz386) Bool.false 1436272165 2097152 83 4194304 Bool.false 8388605 8388608 1 1960000 (Ns150p1896 rfl) (Enclosure.sfrac_false_div 1436272165 2097152) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1436272165) qz386) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 223373911252921221120) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 8388605 8388608 109 1000000000000000 3920000 1960000 (BSN.sin_reduce_arg_pos_rat_q0 1436272165 2097152 226375608064910080 72057594037927936 109 223373911252921221120 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 8388605 8388608 223373911252921221120 302231454903657293676544 12697336 17179869184 3923829 3920000 (Ns150p1897 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns150p1899 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz244) Bool.false Ns150p1874 Ns150p1875 28124817534834513 1433600000000000000000 45960709285 67108864 1317 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz244) (@HAdd.hAdd Real Real Real qz356 qz586 (Enclosure.sfrac Bool.true Ns150p1876 Ns150p1877)) Bool.false Ns150p1874 Ns150p1875 28124817534834513 1433600000000000000000 Ns150p1878 (Ns150p1895 rfl rfl)) 

noncomputable def Ns150p1900 := Ns150p1873 22238 BSN.abs_quadSignPos (BSN.cos_quad_nat3 247 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 67102457 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 138 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 67095321 67108864) qz247 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz244) qz244 1) Bool.false 8388605 8388608 2607411 128450560000 67108840 67108864 1363 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz244) qz244 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz244)) Bool.false 8388605 8388608 2607411 128450560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz244) qz244) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz244)) Bool.false 8388605 8388608 166874304 8220835840000 8388605 8388608 2607411 128450560000 (Ns150p1898 rfl rfl) rfl)) rfl) (Ns150p1899 rfl) RS151to168.d7 

noncomputable def Ns150p1901 := nat_lit 2549362679948988135110542822492837493027926275025845588858621904182113974346140402383907270885703028736 

noncomputable def Ns150p1902 := nat_lit 1693362793125414169225994385531101613030124863702823308347667105109750218442736407748289769639936 

noncomputable def Ns150p1903 := nat_lit 12731523117428427036909562066774407146299395425338482109869430034489985785540273692463957767925553565696 

noncomputable def Ns150p1904 := BSN.sin_dyadic_bound_f 104487058 67108864 4 3 67108864 33554432 Ns150p1901 Ns150p111 Ns150p1902 Ns150p1903 Ns150p114 Ns150p1902 67102457 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 104487058) qz361 0 3 Ns150p1901 Ns150p111 Ns150p1902 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 104487058) (BSN.sinOddQ 67108864) 0 3 Ns150p1903 Ns150p114 Ns150p1902 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1905 := BSN.cos_dyadic_bound_f 1348225 67108864 1 0 67108864 33554432 0 1 1 0 1 1 67095321 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 1348225) qz362 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 1348225) (BSN.cosOddQ 67108864) 0 0 rfl) rfl rfl 

noncomputable def Ns150p1906 := nat_lit 2454526611737965330633225150346146755917290005467253562865379208596733512322664119274150617246845177856 

noncomputable def Ns150p1907 := nat_lit 1511653566561207823863120822132706335837595976940621265924051282446130054612540831068986316230656 

noncomputable def Ns150p1908 := nat_lit 12258457401549096561486631058218691599357129663414770908336761095839373411202365295907961187806317449216 

noncomputable def Ns150p1909 := BSN.sin_dyadic_bound_f 103503338 67108864 4 3 67108864 33554432 Ns150p1906 Ns150p111 Ns150p1907 Ns150p1908 Ns150p114 Ns150p1907 67081656 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 103503338) qz361 0 3 Ns150p1906 Ns150p111 Ns150p1907 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 103503338) (BSN.sinOddQ 67108864) 0 3 Ns150p1908 Ns150p114 Ns150p1907 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1910 := nat_lit 367580310725954490336754140663113210228780933822541856017150390625 

noncomputable def Ns150p1911 := nat_lit 116297924742039706533151559789758839548778373141626129150390625 

noncomputable def Ns150p1912 := nat_lit 1102508336328379391597196118869760113007245244721342315793150390625 

noncomputable def Ns150p1913 := BSN.cos_dyadic_bound_f 57305525 67108864 3 2 67108864 33554432 Ns150p1910 Ns150p117 Ns150p1911 Ns150p1912 Ns150p120 Ns150p1911 44092799 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 57305525) qz362 0 2 Ns150p1910 Ns150p117 Ns150p1911 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 57305525) (BSN.cosOddQ 67108864) 0 2 Ns150p1912 Ns150p120 Ns150p1911 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1914 := Ns150p1871 37631 BSN.abs_quadSignPos (BSN.cos_quad_nat3 59 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 67081656 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 0 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 44092799 67108864) qz247 rfl rfl (Ns150p1900 RS151to168.d9 RS151to168.d11 RS151to168.d13 RS151to168.d17 (Ns150p1904 rfl rfl) (Ns150p1905 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns150p1899 rfl) RS151to168.d19 RS151to168.d21 RS151to168.d23 RS151to168.d25 RS151to168.d17 (Ns150p1909 rfl rfl) (Ns150p1913 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns150p1915 := nat_lit 2604801489922132972856213893104089463916196544175007888876497710326155742656930224252752392021587890625 

noncomputable def Ns150p1916 := nat_lit 1806026652155639084391667220118140542402448494885679423143584433272413439331789076328277587890625 

noncomputable def Ns150p1917 := nat_lit 13008046118477166323306373223621106467345894501248115866033550327029327660694940114133056646997587890625 

noncomputable def Ns150p1918 := BSN.sin_dyadic_bound_f 105049425 67108864 4 3 67108864 33554432 Ns150p1915 Ns150p111 Ns150p1916 Ns150p1917 Ns150p114 Ns150p1916 67107871 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 105049425) qz361 0 3 Ns150p1915 Ns150p111 Ns150p1916 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 105049425) (BSN.sinOddQ 67108864) 0 3 Ns150p1917 Ns150p114 Ns150p1916 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1919 := nat_lit 3237280011741708213941953522016852134686041593551704858143248630625 

noncomputable def Ns150p1920 := nat_lit 2781066386464049262764544174205285196227690889939987583750390625 

noncomputable def Ns150p1921 := nat_lit 8474087828031151147232069009952566081479073626432657505715769590625 

noncomputable def Ns150p1922 := BSN.sin_dyadic_bound_f 85217035 67108864 3 2 67108864 33554432 Ns150p1919 Ns150p359 Ns150p1920 Ns150p1921 Ns150p362 Ns150p1920 64092407 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 85217035) qz361 0 2 Ns150p1919 Ns150p359 Ns150p1920 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 85217035) (BSN.sinOddQ 67108864) 0 2 Ns150p1921 Ns150p362 Ns150p1920 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1923 := Ns150p1869 50410 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 49 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 67107871 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 91 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 64092407 67108864) qz247 rfl rfl (Ns150p1914 rfl rfl) (Ns150p1899 rfl) RS151to168.d27 RS151to168.d29 RS151to168.d31 RS151to168.d33 RS151to168.d17 (Ns150p1918 rfl rfl) (Ns150p1922 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns150p1924 := nat_lit 70838207389147149124243456 

noncomputable def Ns150p1925 := BSN.cos_dyadic_bound_f 2901128 67108864 2 1 67108864 33554432 Ns150p1924 Ns150p134 Ns150p1924 Ns150p1924 Ns150p135 Ns150p1924 67046165 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 2901128) qz362 0 1 Ns150p1924 Ns150p134 Ns150p1924 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 2901128) (BSN.cosOddQ 67108864) 0 1 Ns150p1924 Ns150p135 Ns150p1924 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1926 := Ns150p1867 Bool.false 125907632 50410 Bool.true 2901128 3537118876014220 1 Bool.false 67046165 Bool.false Bool.false 149612032 56158 BSN.abs_quadSignPos qz407 (BSN.sfrac_eq_quadSignPos_mul Bool.false 67046165 67108864) qz247 rfl (Ns150p1923 rfl) (Ns150p1899 rfl) RS151to168.d42 RS151to168.d44 RS151to168.d17 (Ns150p1925 rfl rfl) rfl 

noncomputable def Ns150p1927 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz244) qz244 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz244) qz244 8) 149612032 67108864 56158 67108864 149612032 67108864 56158 67108864 20080587016503296 292211 65536 28079 16777216 (Ns150p1926 rfl rfl rfl rfl) 

noncomputable def Ns150p1928 := @Enclosure.Real.IsNear.mulLit_ff qz776 (Zeta.RiemannSiegel.correction qz246) 730813 2097152 1 4194304 9075796428171 17592186044416 462314350098477 1077521395220480000 6632710015060933023 36893488147419103232 

noncomputable abbrev qz780 := (@HPow.hPow Real Real Real qz6 qz245 qz8)

noncomputable def Ns150p1929 := @Enclosure.Real.IsNear.mulLit_ff qz48 qz780 1 1 0 1 730813 2097152 1 4194304 730813 2097152 1 4194304 

noncomputable def Ns150p1930 := @Enclosure.Real.IsNear.sqrt_image qz245 568832024607 8388608000 426063 8388608000 34538765 34538792 4194304 (@Enclosure.Real.IsNear.of_eq qz245 (@HMul.hMul Real Real Real qz4 qz244 qz2) Bool.false 568832024607 8388608000 426063 8388608000 (BSN.t_div_two_pi_mk qz244 426063 1000 qz247) (@Enclosure.Real.IsNear.mulLit_ff qz244 qz2 426063 1000 0 1 1335089 8388608 1 8388608 568832024607 8388608000 426063 8388608000 (Enclosure.Real.IsNear.const Bool.false 426063 1000) RS151to168.d36 rfl)) 

noncomputable abbrev qz916 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 426063 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz781 := qz916

noncomputable abbrev qz591 := qz781

noncomputable abbrev qz249 := qz591

noncomputable def Ns150p1931 := @Enclosure.Real.IsNear.sqrt_image qz249 69077557 8388608 27 8388608 12036032 12036038 4194304 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 69077557 8388608 27 8388608 69077557 8388608 27 8388608 (Ns150p1930 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns150p1932 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz249) 12036035 4194304 3 4194304 1461625 1461627 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz249) Bool.false 24072070 8388608 6 8388608 12036035 4194304 3 4194304 (Ns150p1931 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns150p1933 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 2923252 8388608 2 8388608 730813 2097152 1 4194304 (Ns150p1932 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz250 := (@HMul.hMul Real Real Real qz340 qz338 qz584)

noncomputable abbrev qz782 := (@HMul.hMul Real Real Real qz839 qz914 qz914)

noncomputable abbrev qz592 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz782 qz775) qz638)

noncomputable abbrev qz251 := (Real.cos (@HMul.hMul Real Real Real qz340 qz338 qz592))

noncomputable def Ns150p1934 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz246) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz250)) qz251) Bool.false 9075796428171 

noncomputable def Ns150p1935 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz250)) qz251 87318489 8388608 18993 

noncomputable def Ns150p1936 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz250)) Bool.false 87318489 8388608 18993 8388608 87318489 8388608 18993 

noncomputable def Ns150p1937 := @Enclosure.Real.IsNear.recentre' (Real.cos qz250) Bool.false 402943 4194304 343548608 16441671680000 402943 4194304 5367947 256901120000 

noncomputable def Ns150p1938 := @Enclosure.Real.IsNear.cos_image qz250 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6184831) qz359) Bool.false 6184831 4194304 171 8388608 Bool.false 402943 4194304 1 

noncomputable def Ns150p1939 := nat_lit 145724807212220034278258073 

noncomputable def Ns150p1940 := nat_lit 7205759403792793600000000000000 

noncomputable def Ns150p1941 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz246 884279719003555 140737488355328 1 500000000000000 1968693 8388608 27 8388608 1740875292844265703615 1180591620717411303424 Ns150p1939 

noncomputable def Ns150p1942 := @Enclosure.Real.IsNear.subLit_ff_p qz249 qz46 69077557 8388608 27 8388608 8 1 0 1 1968693 1968693 8388608 27 

noncomputable def Ns150p1943 := @Ns150p1942 8388608 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 69077557 8388608 27 8388608 69077557 8388608 27 8388608 (Ns150p1930 rfl rfl rfl rfl rfl rfl) rfl) qz410 

noncomputable def Ns150p1944 := @Enclosure.Real.IsNear.recentre' qz250 Bool.false 1740875292844265703615 1180591620717411303424 Ns150p1939 Ns150p1940 6184831 4194304 171 8388608 (@Ns150p1941 Ns150p1940 RS151to168.d35 (Ns150p1943 rfl rfl) rfl) 

noncomputable def Ns150p1945 := nat_lit 2805028567014910035685199842935289330183308152944496151121365379959719417316024579786241 

noncomputable def Ns150p1946 := nat_lit 3132809916256936113553507559638118872600179706247579633466709528376457391694415361 

noncomputable def Ns150p1947 := nat_lit 16985320031018675355821458121448906622346665895716098977541306109941197252891968740263425 

noncomputable def Ns150p1948 := BSN.cos_dyadic_bound_f 6184831 4194304 4 3 4194304 1960000 Ns150p1945 Ns150p1756 Ns150p1946 Ns150p1947 Ns150p1759 Ns150p1946 402943 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 6184831) (BSN.cosEvenQ 4194304) 0 3 Ns150p1945 Ns150p1756 Ns150p1946 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 6184831) (BSN.cosOddQ 4194304) 0 3 Ns150p1947 Ns150p1759 Ns150p1946 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1949 := @Enclosure.Real.IsNear.inv_image (Real.cos qz250) 402943 4194304 5367947 256901120000 43649748 43668741 4194304 (Ns150p1937 (@Ns150p1938 1960000 (Ns150p1944 rfl) (Enclosure.sfrac_false_div 6184831 4194304) (Ns150p1948 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns150p1950 := @Enclosure.Real.IsNear.recentre' qz251 Bool.false 207878 4194304 

noncomputable abbrev qz252 := (@HMul.hMul Real Real Real qz340 qz338 qz592)

noncomputable def Ns150p1951 := @Enclosure.Real.IsNear.cos_image qz252 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 3190217)) qz386) Bool.true 3190217 2097152 

noncomputable def Ns150p1952 := nat_lit 15065374738663904609746467445 

noncomputable def Ns150p1953 := nat_lit 8981035169531779099110719554666097 

noncomputable def Ns150p1954 := @Enclosure.Real.IsNear.recentre' qz252 Bool.true Ns150p1952 Ns150p617 Ns150p1953 

noncomputable abbrev qz253 := qz592

noncomputable def Ns150p1955 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz253 884279719003555 140737488355328 1 500000000000000 17036888232199 

noncomputable abbrev qz593 := (@HSub.hSub Real Real Real qz634 qz782 qz775)

noncomputable abbrev qz254 := qz593

noncomputable def Ns150p1956 := @Enclosure.Real.IsNear.subLit_tf qz254 qz25 12638841721095 70368744177664 332802567 70368744177664 1 16 

noncomputable abbrev qz594 := qz782

noncomputable abbrev qz255 := qz594

noncomputable def Ns150p1957 := @Enclosure.Real.IsNear.subLit_ff_n qz255 qz246 3875752128249 70368744177664 106310151 70368744177664 1968693 8388608 27 8388608 

noncomputable def Ns150p1958 := @Enclosure.Real.IsNear.mulLit_ff qz246 qz246 1968693 8388608 27 8388608 1968693 8388608 27 8388608 3875752128249 70368744177664 

noncomputable def Ns150p1959 := nat_lit 775940880986271473710913253353073653852585591931125256817023420085360912217317340641 

noncomputable def Ns150p1960 := nat_lit 3466537250751077332112698720796095110148055492926080949987665366995300109908547993600 

noncomputable def Ns150p1961 := nat_lit 1111329133738740090369839920607978887517143307206372253579402004642865856148961 

noncomputable def Ns150p1962 := nat_lit 4697397633193728462098602095606280981463906498145731190639702910816900267410077021665 

noncomputable def Ns150p1963 := nat_lit 315454889818348037222255583592444655023473049856273366448877548396572310001677867417600 

noncomputable def Ns150p1964 := BSN.cos_dyadic_bound_f 3190217 2097152 4 3 4194304 1960000 Ns150p1959 Ns150p1960 Ns150p1961 Ns150p1962 Ns150p1963 Ns150p1961 207878 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 3190217) (BSN.cosEvenQ 2097152) 0 3 Ns150p1959 Ns150p1960 Ns150p1961 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 3190217) (BSN.cosOddQ 2097152) 0 3 Ns150p1962 Ns150p1963 Ns150p1961 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p1965 := @Ns150p1950 500348608 16441671680000 103939 2097152 7817947 256901120000 (@Ns150p1951 251 8388608 Bool.false 207878 4194304 1 1960000 (@Ns150p1954 Ns150p620 3190217 2097152 251 8388608 (@Ns150p1955 70368744177664 332802567 70368744177664 Ns150p1952 Ns150p617 Ns150p1953 Ns150p620 RS151to168.d35 (@Ns150p1956 0 1 272590211715184 17036888232199 70368744177664 332802567 70368744177664 (@Ns150p1957 106022288772311285760 12638841721095 70368744177664 332802567 70368744177664 (@Ns150p1958 106310151 70368744177664 (Ns150p1943 rfl rfl) (Ns150p1943 rfl rfl) rfl) (Ns150p1943 rfl rfl) rfl rfl) qz373 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 3190217 2097152) (BSN.cos_neg_of_bound 3190217 2097152 Bool.false 207878 4194304 1 1960000 (Ns150p1964 rfl rfl)) rfl rfl) 

noncomputable def Ns150p1966 := @Ns150p1928 676287029122612115829 Ns150p1358 (Ns150p1929 qz61 (@Enclosure.Real.IsNear.of_eq qz780 (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 730813 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz245 (BSN.t_div_two_pi_nonneg qz244 426063 1000 qz247)) Ns150p1933) rfl) (@Ns150p1934 17592186044416 462314350098477 1077521395220480000 (BSN.correction_mk qz246 (BSN.cos_two_pi_p_ne_zero_mk qz244 426063 1000 8 qz247 rfl rfl (@BSN.floor_sqrt_eq_dec qz244 426063 1000 8 qz247 rfl rfl rfl))) (@Ns150p1935 8388608 103939 2097152 7817947 256901120000 9075796428171 17592186044416 462314350098477 1077521395220480000 (@Ns150p1936 8388608 (Ns150p1949 rfl rfl rfl rfl rfl) rfl) (Ns150p1965 rfl) rfl)) 

noncomputable def Ns150p1967 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz244) (hardyZApproximantRS₀ qz244) Bool.false 157867458824134067809 36893488147419103232 8240217843221576595829 Ns150p1358 (@Eq.refl Real (hardyZApproximantRS₀ qz244)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz244) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz244) qz244 8) (@HMul.hMul Real Real Real qz4 qz776 (Zeta.RiemannSiegel.correction qz246))) Bool.false 157867458824134067809 36893488147419103232 8240217843221576595829 Ns150p1358 (BSN.hardyZApproximantRS₀_eq qz244 8 (@BSN.floor_sqrt_eq_dec qz244 426063 1000 8 qz247 rfl rfl rfl)) (@Ns150p1866 157867458824134067809 36893488147419103232 8240217843221576595829 Ns150p1358 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz244) qz244 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz244) qz244 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz244) qz244 8)) Bool.false 292211 65536 28079 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz244) qz244 8) (Ns150p1927 (Ns150p1926 rfl rfl rfl rfl) rfl rfl)) (Ns150p1966 rfl) rfl rfl)) 

theorem RS151to168.d60 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz244) Bool.false 157867458824134067809 36893488147419103232 8240217843221576595829 Ns150p1358 := Ns150p1967 

noncomputable abbrev qz917 := (Enclosure.sfrac Bool.false 427552 1000)

noncomputable abbrev qz783 := qz917

noncomputable abbrev qz595 := qz783

noncomputable abbrev qz256 := qz595

noncomputable abbrev qz918 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 427552 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz784 := qz918

noncomputable abbrev qz596 := qz784

noncomputable abbrev qz257 := qz596

noncomputable abbrev qz919 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 427552 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz785 := qz919

noncomputable abbrev qz597 := qz785

noncomputable abbrev qz258 := qz597

noncomputable abbrev qz786 := (@HMul.hMul Real Real Real qz4 qz48 (@HPow.hPow Real Real Real qz6 qz257 qz8))

noncomputable def Ns150p1968 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz256) qz256 8) (@HMul.hMul Real Real Real qz4 qz786 (Zeta.RiemannSiegel.correction qz258)) 24937149 33554432 56351 33554432 1571045642183055 9007199254740992 5537359792377900829893 Ns150p422 277329414057692724461568 

noncomputable def Ns150p1969 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz256) qz256 Real.sin BSN.quadSignPos 7 8 427552 1000 127 67108864 33554432 1125899906842624 Bool.false 46171474046 1322 139548959 35 23726568 8 

noncomputable def Ns150p1970 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz256) qz256 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 427552 1000 49 91 67108864 33554432 1125899906842624 Bool.false 46171474046 1322 

noncomputable def Ns150p1971 := Ns150p1970 120242927 35 27397080 8 130587807 35 25364760 8 Bool.true 46040598 37758 Bool.true 73326382 Bool.true 68897519 3537118876014220 1 Bool.false 59582509 Bool.true Bool.false 57416405 Bool.false Bool.true 48663701 

noncomputable def Ns150p1972 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz256) qz256 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 427552 1000 60 0 67108864 33554432 1125899906842624 Bool.false 46171474046 1322 

noncomputable def Ns150p1973 := Ns150p1972 93032624 35 33554424 8 108007536 35 30011992 8 Bool.true 92626804 22311 Bool.false 70328165 Bool.true 7363985 3537118876014220 1 Bool.false 33509451 Bool.false Bool.false 66705237 Bool.false Bool.true 46040598 

noncomputable def Ns150p1974 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz256) qz256 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 427552 1000 249 138 67108864 33554432 1125899906842624 Bool.false 46171474046 1322 

noncomputable def Ns150p1975 := Ns150p1974 46516304 35 47453136 16 73726608 35 38745320 8 Bool.true 67108856 1363 Bool.false 35160328 Bool.false 102334067 3537118876014220 1 Bool.false 33573663 Bool.true Bool.false 3079208 Bool.true Bool.true 92626804 

noncomputable def Ns150p1976 := nat_lit 5198542960389703242630906486433102523929675611675419 

noncomputable def Ns150p1977 := nat_lit 7555927544657740362946556402045826114017820672000 

noncomputable def Ns150p1978 := nat_lit 6857841661489284600005345935360000 

noncomputable def Ns150p1979 := nat_lit 17592514736246644432997695175106232320 

noncomputable def Ns150p1980 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz256 427552 1000 731203850816 16000000 855104 4000 2000 Ns150p1978 Ns150p1979 (@Eq.refl Real qz256) rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns150p1981 := nat_lit 6813834229041991834181181749897596140165104417735205191680 

noncomputable abbrev qz787 := (Real.log (Enclosure.sfrac Bool.false 731203850816 16000000))

noncomputable abbrev qz259 := (@HSub.hSub Real Real Real qz344 (@HMul.hMul Real Real Real qz340 (Enclosure.sfrac Bool.false 427552 4000) qz787) (@HMul.hMul Real Real Real qz340 qz346 (@HSub.hSub Real Real Real qz344 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 855104))))))

noncomputable abbrev qz788 := (Enclosure.sfrac Bool.false 427552 2000)

noncomputable abbrev qz598 := (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 qz259 qz788) (@HMul.hMul Real Real Real qz4 qz788 (Real.log Real.pi)))

noncomputable def Ns150p1982 := @Enclosure.Real.IsNear.addLit_ft_p qz598 (Enclosure.sfrac Bool.true Ns150p1978 Ns150p1979) 387314616006816840699 562949953421312000 6173665043855977 313600000000000000000 Ns150p1978 Ns150p1979 0 1 Ns150p1981 

noncomputable def Ns150p1983 := nat_lit 32490304863517118044223569920 

noncomputable abbrev qz599 := (@HSub.hSub Real Real Real qz11 qz259 qz788)

noncomputable abbrev qz600 := (@HMul.hMul Real Real Real qz4 qz788 (Real.log Real.pi))

noncomputable def Ns150p1984 := @Enclosure.Real.IsNear.subLit_ff_p qz599 qz600 21003094013814820659 22517998136852480 68055015713761 9800000000000000000 513206177721 2097152000 13361 1048576000 Ns150p1983 387314616006816840699 562949953421312000 

noncomputable abbrev qz601 := qz788

noncomputable def Ns150p1985 := @Enclosure.Real.IsNear.subLit_ff_p qz259 qz601 645422539587964910587 562949953421312000 68055015713761 9800000000000000000 427552 2000 0 1 1050154700690741032950000 21003094013814820659 22517998136852480 68055015713761 9800000000000000000 

noncomputable def Ns150p1986 := nat_lit 1453362354392438987117942099280920576 

noncomputable def Ns150p1987 := nat_lit 12971603364573133460733952 

noncomputable def Ns150p1988 := nat_lit 5833685249720805284291059410033083490959440101669868749889464140084847805584357549083153985668382720 

noncomputable def Ns150p1989 := nat_lit 53695774364043362543832052398524985081122461476737161239103475320961311424236251084762274357837824 

noncomputable def Ns150p1990 := nat_lit 352808782949650493573162882660333824996240746459798850645598435674869795440693998583367598080 

noncomputable def Ns150p1991 := BSN.log_dyadic_bound 206915850816 1255491850816 5 4 Ns150p1988 33554432 15680000 Ns150p1989 Ns150p1990 11161919 1462407701632 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 206915850816) (BSN.artanhQ 1255491850816) 0 4 Ns150p1989 Ns150p1988 Ns150p1990 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns150p1992 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 427552 4000) qz787 427552 4000 0 1 48322988169540217 4503599627370496 625000147 9800000000000000 645643444933226839337 562949953421312000 8350626964067 1225000000000000000 (Enclosure.Real.IsNear.const Bool.false 427552 4000) (BSN.isNear_log_sfrac 731203850816 16000000 48322988169540217 4503599627370496 625000147 9800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 731203850816) qz352)) Bool.false Ns150p1987 Ns150p86 1000000235200000 15680000000000000000000 48322988169540217 4503599627370496 625000147 9800000000000000 (BSN.log_rat_reduce_isNear 731203850816 16000000 15 1462407701632 1048576000000 11161919 33554432 24973259072661432 36028797018963968 15680000 1000000000000000 rfl rfl rfl rfl (Ns150p1991 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns150p1993 := BSN.arctan_dyadic_bound_f 1000 855104 1 0 4194304 1960000 0 1 1 0 1 1 4905 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 855104) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 855104) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz602 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 855104)))

noncomputable def Ns150p1994 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz602 884279719003555 562949953421312 1 2000000000000000 4905 4194304 1 1960000 3706176693013955215360 883621381047715 562949953421312 50000000049 98000000000000000 qz16 (Ns150p1993 rfl) rfl rfl 

noncomputable def Ns150p1995 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz4 (Enclosure.sfrac Bool.false 427552 4000) qz787) (@HMul.hMul Real Real Real qz4 qz17 (@HSub.hSub Real Real Real qz11 qz14 qz602)) 645643444933226839337 562949953421312000 8350626964067 1225000000000000000 883621381047715 2251799813685248 50000000049 392000000000000000 Ns150p1986 645422539587964910587 562949953421312000 68055015713761 9800000000000000000 (Ns150p1992 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz11 qz14 qz602) 1 4 0 1 883621381047715 562949953421312 50000000049 98000000000000000 883621381047715 2251799813685248 50000000049 392000000000000000 qz355 Ns150p1994 rfl) 

noncomputable def Ns150p1996 := @Ns150p1982 Ns150p1976 Ns150p1977 6173665043855977 313600000000000000000 (@Ns150p1984 6173665043855977 313600000000000000000 (Ns150p1985 (Ns150p1995 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 427552 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz601 (Real.log Real.pi) 427552 2000 0 1 38410761 33554432 1 16777216 513206177721 2097152000 13361 1048576000 (Enclosure.Real.IsNear.const Bool.false 427552 2000) RS151to168.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns150p1978 Ns150p1979) 

noncomputable def Ns150p1997 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz256) Bool.false Ns150p1976 Ns150p1977 6173665043855977 313600000000000000000 5771434255 8388608 83 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz256) (@HAdd.hAdd Real Real Real qz356 qz598 (Enclosure.sfrac Bool.true Ns150p1978 Ns150p1979)) Bool.false Ns150p1976 Ns150p1977 6173665043855977 313600000000000000000 Ns150p1980 (Ns150p1996 rfl rfl)) 

noncomputable def Ns150p1998 := nat_lit 1898717637222170550599680 

noncomputable def Ns150p1999 := nat_lit 139912501834012009132687361831849067376206230632283522936983333827733017165767798284225 

noncomputable def Ns150p2000 := nat_lit 280960115147195562123107551448033363618537412068840291166238900815091075825478262721 

noncomputable def Ns150p2001 := nat_lit 365982616997888373961219964000117408158491067274535866268306249423695373692341078319041 

noncomputable def Ns150p2002 := BSN.sin_dyadic_bound_f 26982400487 17179869184 3 2 8388608 3923829 Ns150p1999 Ns150p98 Ns150p2000 Ns150p2001 Ns150p101 Ns150p2000 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26982400487) qz357 0 2 Ns150p1999 Ns150p98 Ns150p2000 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26982400487) qz358 0 2 Ns150p2001 Ns150p101 Ns150p2000 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p2003 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz256) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5771434255) qz368) Bool.false 5771434255 8388608 83 4194304 Bool.true 8388607 8388608 1 1960000 (Ns150p1997 rfl) (Enclosure.sfrac_false_div 5771434255 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5771434255) qz368) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns150p1998) qz369) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 109 1000000000000000 3920000 1960000 (BSN.sin_reduce_arg_pos_rat_q1 5771434255 8388608 226375608064910080 72057594037927936 109 Ns150p1998 Ns150p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns150p1998 Ns150p86 26982400487 17179869184 3923829 3920000 (Ns150p2002 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns150p2004 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz256) Bool.false Ns150p1976 Ns150p1977 6173665043855977 313600000000000000000 46171474046 67108864 1322 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz256) (@HAdd.hAdd Real Real Real qz356 qz598 (Enclosure.sfrac Bool.true Ns150p1978 Ns150p1979)) Bool.false Ns150p1976 Ns150p1977 6173665043855977 313600000000000000000 Ns150p1980 (Ns150p1996 rfl rfl)) 

noncomputable def Ns150p2005 := Ns150p1975 22311 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 249 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 33573663 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 138 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 3079208 67108864) (@Eq.refl Real qz256) rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 1) Bool.true 8388607 8388608 2607411 128450560000 67108856 67108864 1363 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz256)) Bool.true 8388607 8388608 2607411 128450560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz256) qz256) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz256)) Bool.true 8388607 8388608 166874304 8220835840000 8388607 8388608 2607411 128450560000 (Ns150p2003 rfl rfl) rfl)) rfl) (Ns150p2004 rfl) RS151to168.d7 

noncomputable def Ns150p2006 := nat_lit 93739758153205935591162784992960749128710697846314192203300208640 

noncomputable def Ns150p2007 := nat_lit 2335733784882454849803883514907854329370755161652226619867136 

noncomputable def Ns150p2008 := nat_lit 245505108737030497811859992503492111191994751231989733117925523456 

noncomputable def Ns150p2009 := BSN.sin_dyadic_bound_f 35160328 67108864 3 2 67108864 33554432 Ns150p2006 Ns150p359 Ns150p2007 Ns150p2008 Ns150p362 Ns150p2007 33573663 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 35160328) qz361 0 2 Ns150p2006 Ns150p359 Ns150p2007 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 35160328) (BSN.sinOddQ 67108864) 0 2 Ns150p2008 Ns150p362 Ns150p2007 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p2010 := nat_lit 903320611424980525955361221468346491759611251033631210244370720402855891082092379088577841208607288241 

noncomputable def Ns150p2011 := nat_lit 1318993977066249785067372222578088551284199701088389052515959303689136385473821415508445421808561 

noncomputable def Ns150p2012 := nat_lit 5468417573680993359256225679900764139528403612730239875385347876800849871208946960660195802130136607665 

noncomputable def Ns150p2013 := BSN.cos_dyadic_bound_f 102334067 67108864 4 3 67108864 33554432 Ns150p2010 Ns150p128 Ns150p2011 Ns150p2012 Ns150p131 Ns150p2011 3079208 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 102334067) qz362 0 3 Ns150p2010 Ns150p128 Ns150p2011 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 102334067) (BSN.cosOddQ 67108864) 0 3 Ns150p2012 Ns150p131 Ns150p2011 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p2014 := nat_lit 834175941648515259704285953042474831633349906530916322819113190625 

noncomputable def Ns150p2015 := nat_lit 598458841755229877179753793326202454193597470124124401500390625 

noncomputable def Ns150p2016 := nat_lit 2501330907262035319358498351540772089991662524652500719654338790625 

noncomputable def Ns150p2017 := BSN.cos_dyadic_bound_f 70328165 67108864 3 2 67108864 33554432 Ns150p2014 Ns150p117 Ns150p2015 Ns150p2016 Ns150p120 Ns150p2015 33509451 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 70328165) qz362 0 2 Ns150p2014 Ns150p117 Ns150p2015 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 70328165) (BSN.cosOddQ 67108864) 0 2 Ns150p2016 Ns150p120 Ns150p2015 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p2018 := nat_lit 2940705818176551730186050625 

noncomputable def Ns150p2019 := BSN.cos_dyadic_bound_f 7363985 67108864 2 1 67108864 33554432 Ns150p2018 Ns150p134 Ns150p2018 Ns150p2018 Ns150p135 Ns150p2018 66705237 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 7363985) qz362 0 1 Ns150p2018 Ns150p134 Ns150p2018 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 7363985) (BSN.cosOddQ 67108864) 0 1 Ns150p2018 Ns150p135 Ns150p2018 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p2020 := Ns150p1973 37758 BSN.abs_quadSignPos (BSN.cos_quad_nat0 60 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 33509451 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 0 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66705237 67108864) (@Eq.refl Real qz256) rfl rfl (Ns150p2005 RS151to168.d9 RS151to168.d11 RS151to168.d13 RS151to168.d17 (Ns150p2009 rfl rfl) (Ns150p2013 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns150p2004 rfl) RS151to168.d19 RS151to168.d21 RS151to168.d23 RS151to168.d25 RS151to168.d17 (Ns150p2017 rfl rfl) (Ns150p2019 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns150p2021 := nat_lit 1773973052845758490937329000508145959635759856103800105315570172160 

noncomputable def Ns150p2022 := nat_lit 835760912483223952398647810673509728285639801752636665405522176 

noncomputable def Ns150p2023 := nat_lit 4644766763594870827960549571542148973771670492021400768844408176896 

noncomputable def Ns150p2024 := BSN.sin_dyadic_bound_f 73326382 67108864 3 2 67108864 33554432 Ns150p2021 Ns150p359 Ns150p2022 Ns150p2023 Ns150p362 Ns150p2022 59582509 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 73326382) qz361 0 2 Ns150p2021 Ns150p359 Ns150p2022 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 73326382) (BSN.sinOddQ 67108864) 0 2 Ns150p2023 Ns150p362 Ns150p2022 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p2025 := nat_lit 1382531992013531636046345153426023013996652861561013987211706418305 

noncomputable def Ns150p2026 := nat_lit 507725137571339469011557310284655557113193312445128175260583041 

noncomputable def Ns150p2027 := nat_lit 3620095090765086401933456689994361308613050419677744520889761580161 

noncomputable def Ns150p2028 := BSN.sin_dyadic_bound_f 68897519 67108864 3 2 67108864 33554432 Ns150p2025 Ns150p359 Ns150p2026 Ns150p2027 Ns150p362 Ns150p2026 57416405 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 68897519) qz361 0 2 Ns150p2025 Ns150p359 Ns150p2026 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 68897519) (BSN.sinOddQ 67108864) 0 2 Ns150p2027 Ns150p362 Ns150p2026 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p2029 := Ns150p1971 50582 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 49 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 59582509 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 91 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 57416405 67108864) (@Eq.refl Real qz256) rfl rfl (Ns150p2020 rfl rfl) (Ns150p2004 rfl) RS151to168.d27 RS151to168.d29 RS151to168.d31 RS151to168.d33 RS151to168.d17 (Ns150p2024 rfl rfl) (Ns150p2028 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns150p2030 := nat_lit 2633711876217659267080626807892347333186531976802864656245827843563378663438134467787031226659662462976 

noncomputable def Ns150p2031 := nat_lit 1866708174636975336761677386547308372948247976726269159264839732645180049155805470369071157477376 

noncomputable def Ns150p2032 := nat_lit 13152242412869220046629942289327248639839330734105603825702365496393654775117995345956890358343832436736 

noncomputable def Ns150p2033 := BSN.sin_dyadic_bound_f 105339124 67108864 4 3 67108864 33554432 Ns150p2030 Ns150p111 Ns150p2031 Ns150p2032 Ns150p114 Ns150p2031 67108821 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 105339124) qz361 0 3 Ns150p2030 Ns150p111 Ns150p2031 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 105339124) (BSN.sinOddQ 67108864) 0 3 Ns150p2032 Ns150p114 Ns150p2031 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p2034 := Ns150p1969 Bool.true 48663701 50582 Bool.true 105339124 3537118876014220 1 Bool.false 67108821 Bool.false Bool.true 24937149 56351 BSN.abs_quadSignPos (BSN.cos_quad_nat3 127 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 67108821 67108864) (@Eq.refl Real qz256) rfl (Ns150p2029 rfl) (Ns150p2004 rfl) RS151to168.d42 RS151to168.d44 RS151to168.d17 (Ns150p2033 rfl rfl) rfl 

noncomputable def Ns150p2035 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 8) 24937149 67108864 56351 67108864 24937149 67108864 56351 67108864 3347007481577472 24937149 33554432 56351 33554432 (Ns150p2034 rfl rfl rfl rfl) 

noncomputable def Ns150p2036 := @Enclosure.Real.IsNear.mulLit_ff qz786 (Zeta.RiemannSiegel.correction qz258) 11409 32768 1 4194304 137702308895 274877906944 3791610587202181 538760697610240000 1571045642183055 9007199254740992 

noncomputable abbrev qz789 := (@HPow.hPow Real Real Real qz6 qz257 qz8)

noncomputable def Ns150p2037 := @Enclosure.Real.IsNear.mulLit_ff qz48 qz789 1 1 0 1 11409 32768 1 4194304 11409 32768 1 4194304 

noncomputable def Ns150p2038 := @Enclosure.Real.IsNear.sqrt_image qz257 17838124129 262144000 13361 262144000 34599065 34599092 4194304 (@Enclosure.Real.IsNear.of_eq qz257 (@HMul.hMul Real Real Real qz4 qz256 qz2) Bool.false 17838124129 262144000 13361 262144000 (BSN.t_div_two_pi_mk qz256 427552 1000 (@Eq.refl Real qz256)) (@Enclosure.Real.IsNear.mulLit_ff qz256 qz2 427552 1000 0 1 1335089 8388608 1 8388608 17838124129 262144000 13361 262144000 (Enclosure.Real.IsNear.const Bool.false 427552 1000) RS151to168.d36 rfl)) 

noncomputable abbrev qz920 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 427552 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz790 := qz920

noncomputable abbrev qz603 := qz790

noncomputable abbrev qz260 := qz603

noncomputable def Ns150p2039 := @Enclosure.Real.IsNear.sqrt_image qz260 69198157 8388608 27 8388608 12046534 12046540 4194304 (@Enclosure.Real.IsNear.recentre' qz260 Bool.false 69198157 8388608 27 8388608 69198157 8388608 27 8388608 (Ns150p2038 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns150p2040 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz260) 12046537 4194304 3 4194304 1460351 1460353 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz260) Bool.false 24093074 8388608 6 8388608 12046537 4194304 3 4194304 (Ns150p2039 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns150p2041 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz260)) Bool.false 2920704 8388608 2 8388608 11409 32768 1 4194304 (Ns150p2040 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz261 := (@HMul.hMul Real Real Real qz340 qz338 qz597)

noncomputable abbrev qz791 := (@HMul.hMul Real Real Real qz839 qz919 qz919)

noncomputable abbrev qz604 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz791 qz785) qz638)

noncomputable abbrev qz262 := (Real.cos (@HMul.hMul Real Real Real qz340 qz338 qz604))

noncomputable def Ns150p2042 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz258) (@HMul.hMul Real Real Real qz4 (@Inv.inv Real Real.instInv (Real.cos qz261)) qz262) Bool.false 137702308895 

noncomputable def Ns150p2043 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz261)) qz262 178140115 1048576 1257493 

noncomputable def Ns150p2044 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz261)) Bool.false 1425120920 8388608 5029972 8388608 178140115 1048576 1257493 

noncomputable def Ns150p2045 := @Enclosure.Real.IsNear.recentre' (Real.cos qz261) Bool.false 24689 4194304 170794304 8220835840000 24689 4194304 2668661 128450560000 

noncomputable def Ns150p2046 := @Enclosure.Real.IsNear.cos_image qz261 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13127415) qz368) Bool.false 13127415 8388608 85 4194304 Bool.false 24689 4194304 1 

noncomputable def Ns150p2047 := nat_lit 145724807212427223500617113 

noncomputable def Ns150p2048 := @Enclosure.Real.IsNear.mulLit_ff qz1 qz258 884279719003555 140737488355328 1 500000000000000 2089293 8388608 27 8388608 1847519426956094436615 1180591620717411303424 Ns150p2047 

noncomputable def Ns150p2049 := @Enclosure.Real.IsNear.subLit_ff_p qz260 qz46 69198157 8388608 27 8388608 8 1 0 1 2089293 2089293 8388608 27 

noncomputable def Ns150p2050 := @Ns150p2049 8388608 (@Enclosure.Real.IsNear.recentre' qz260 Bool.false 69198157 8388608 27 8388608 69198157 8388608 27 8388608 (Ns150p2038 rfl rfl rfl rfl rfl rfl) rfl) qz410 

noncomputable def Ns150p2051 := @Enclosure.Real.IsNear.recentre' qz261 Bool.false 1847519426956094436615 1180591620717411303424 Ns150p2047 Ns150p1940 13127415 8388608 85 4194304 (@Ns150p2048 Ns150p1940 RS151to168.d35 (Ns150p2050 rfl rfl) rfl) 

noncomputable def Ns150p2052 := nat_lit 14585125231043583612351006230270959599069624955490008483170606159760488629891422246364390625 

noncomputable def Ns150p2053 := nat_lit 58158844227896986633558482781719779619497718984807332131428259197799420928759449934993817600 

noncomputable def Ns150p2054 := nat_lit 26190909441880460335152279215558590549100104867440391403232480514374233503847900390625 

noncomputable def Ns150p2055 := nat_lit 88273129858188691590017840322877130183512647119350914709838310223632345841100574289781990625 

noncomputable def Ns150p2056 := nat_lit 5292454824738625783653821933136499945374292427617467223959971586999747304517109944084437401600 

noncomputable def Ns150p2057 := BSN.cos_dyadic_bound_f 13127415 8388608 4 3 4194304 1960000 Ns150p2052 Ns150p2053 Ns150p2054 Ns150p2055 Ns150p2056 Ns150p2054 24689 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 13127415) (BSN.cosEvenQ 8388608) 0 3 Ns150p2052 Ns150p2053 Ns150p2054 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 13127415) (BSN.cosOddQ 8388608) 0 3 Ns150p2055 Ns150p2056 Ns150p2054 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p2058 := @Enclosure.Real.IsNear.inv_image (Real.cos qz261) 24689 4194304 2668661 128450560000 710045474 715075446 4194304 (Ns150p2045 (@Ns150p2046 1960000 (Ns150p2051 rfl) (Enclosure.sfrac_false_div 13127415 8388608) (Ns150p2057 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns150p2059 := @Enclosure.Real.IsNear.recentre' qz262 Bool.false 12368 4194304 

noncomputable abbrev qz263 := (@HMul.hMul Real Real Real qz340 qz338 qz604)

noncomputable def Ns150p2060 := @Enclosure.Real.IsNear.cos_image qz263 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 6576029)) qz359) Bool.true 6576029 4194304 

noncomputable def Ns150p2061 := nat_lit 15527210172019540581108393445 

noncomputable def Ns150p2062 := nat_lit 9156779287030123831755516687971297 

noncomputable def Ns150p2063 := @Enclosure.Real.IsNear.recentre' qz263 Bool.true Ns150p2061 Ns150p617 Ns150p2062 

noncomputable abbrev qz264 := qz604

noncomputable def Ns150p2064 := @Enclosure.Real.IsNear.mulLit_ft qz1 qz264 884279719003555 140737488355328 1 500000000000000 17559161245399 

noncomputable abbrev qz605 := (@HSub.hSub Real Real Real qz634 qz791 qz785)

noncomputable abbrev qz265 := qz605

noncomputable def Ns150p2065 := @Enclosure.Real.IsNear.subLit_tf qz265 qz25 13161114734295 70368744177664 339314967 70368744177664 1 16 

noncomputable abbrev qz606 := qz791

noncomputable abbrev qz266 := qz606

noncomputable def Ns150p2066 := @Enclosure.Real.IsNear.subLit_ff_n qz266 qz258 4365145239849 70368744177664 112822551 70368744177664 2089293 8388608 27 8388608 

noncomputable def Ns150p2067 := @Enclosure.Real.IsNear.mulLit_ff qz258 qz258 2089293 8388608 27 8388608 2089293 8388608 27 8388608 4365145239849 70368744177664 

noncomputable def Ns150p2068 := nat_lit 3587730898058872947379366352453366527254684447559222069513655788993674428915215186865521 

noncomputable def Ns150p2069 := nat_lit 6539802561834617021067192672136817791267808410815593208747401326181722573999517041 

noncomputable def Ns150p2070 := nat_lit 21713531757107089706482768086417504186978186931317889043871148424730968363646230846319985 

noncomputable def Ns150p2071 := BSN.cos_dyadic_bound_f 6576029 4194304 4 3 4194304 1960000 Ns150p2068 Ns150p1756 Ns150p2069 Ns150p2070 Ns150p1759 Ns150p2069 12368 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 6576029) (BSN.cosEvenQ 4194304) 0 3 Ns150p2068 Ns150p1756 Ns150p2069 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 6576029) (BSN.cosOddQ 4194304) 0 3 Ns150p2070 Ns150p1759 Ns150p2069 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns150p2072 := @Ns150p2059 508188608 16441671680000 773 262144 7940447 256901120000 (@Ns150p2060 255 8388608 Bool.false 12368 4194304 1 1960000 (@Ns150p2063 Ns150p620 6576029 4194304 255 8388608 (@Ns150p2064 70368744177664 339314967 70368744177664 Ns150p2061 Ns150p617 Ns150p2062 Ns150p620 RS151to168.d35 (@Ns150p2065 0 1 280946579926384 17559161245399 70368744177664 339314967 70368744177664 (@Ns150p2066 110403432349024911360 13161114734295 70368744177664 339314967 70368744177664 (@Ns150p2067 112822551 70368744177664 (Ns150p2050 rfl rfl) (Ns150p2050 rfl rfl) rfl) (Ns150p2050 rfl rfl) rfl rfl) qz373 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 6576029 4194304) (BSN.cos_neg_of_bound 6576029 4194304 Bool.false 12368 4194304 1 1960000 (Ns150p2071 rfl rfl)) rfl rfl) 

noncomputable def Ns150p2073 := @Ns150p2036 5537359792377900829893 Ns150p422 (Ns150p2037 qz61 (@Enclosure.Real.IsNear.of_eq qz789 (@Inv.inv Real Real.instInv (Real.sqrt qz260)) Bool.false 11409 32768 1 4194304 (BSN.rpow_neg_quarter_mk qz257 (BSN.t_div_two_pi_nonneg qz256 427552 1000 (@Eq.refl Real qz256))) Ns150p2041) rfl) (@Ns150p2042 274877906944 3791610587202181 538760697610240000 (BSN.correction_mk qz258 (BSN.cos_two_pi_p_ne_zero_mk qz256 427552 1000 8 (@Eq.refl Real qz256) rfl rfl (@BSN.floor_sqrt_eq_dec qz256 427552 1000 8 (@Eq.refl Real qz256) rfl rfl rfl))) (@Ns150p2043 2097152 773 262144 7940447 256901120000 137702308895 274877906944 3791610587202181 538760697610240000 (@Ns150p2044 2097152 (Ns150p2058 rfl rfl rfl rfl rfl) rfl) (Ns150p2072 rfl) rfl)) 

noncomputable def Ns150p2074 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz256) (hardyZApproximantRS₀ qz256) Bool.true 8265060605337999 9007199254740992 9332322801257230109893 Ns150p422 (@Eq.refl Real (hardyZApproximantRS₀ qz256)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz256) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz256) qz256 8) (@HMul.hMul Real Real Real qz4 qz786 (Zeta.RiemannSiegel.correction qz258))) Bool.true 8265060605337999 9007199254740992 9332322801257230109893 Ns150p422 (BSN.hardyZApproximantRS₀_eq qz256 8 (@BSN.floor_sqrt_eq_dec qz256 427552 1000 8 (@Eq.refl Real qz256) rfl rfl rfl)) (@Ns150p1968 8265060605337999 9007199254740992 9332322801257230109893 Ns150p422 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz256) qz256 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 8)) Bool.true 24937149 33554432 56351 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz256) qz256 8) (Ns150p2035 (Ns150p2034 rfl rfl rfl rfl) rfl rfl)) (Ns150p2073 rfl) rfl rfl)) 

theorem RS151to168.d61 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz256) Bool.true 8265060605337999 9007199254740992 9332322801257230109893 Ns150p422 := Ns150p2074 

noncomputable def RS151to168.d62 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz267 := (RS151to168.d3 qz339 qz374 (@Enclosure.dec_le_dec qz339 qz374 400547 1000 402058 1000 (@Eq.refl Real qz339) qz378 rfl rfl rfl))

noncomputable abbrev qz792 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz267)

noncomputable def Ns150p2075 := @Enclosure.Real.IsNear.of_eq qz792 (hardyZApproximantRS₀ qz3) Bool.true 821651366779736627731 295147905179352825856 13015004365296580772851 Ns150p64 

noncomputable abbrev qz268 := (@Enclosure.dec_le_dec qz339 qz374 400547 1000 402058 1000 (@Eq.refl Real qz339) qz378 rfl rfl rfl)

noncomputable def Ns150p2076 := @Enclosure.Real.IsNear.neg_val qz792 821651366779736627731 295147905179352825856 13015004365296580772851 Ns150p64 (Ns150p2075 (RS151to168.d4 qz3 qz27 qz268) RS151to168.d37) rfl 

noncomputable abbrev qz793 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz267)

noncomputable def Ns150p2077 := @Enclosure.Real.IsNear.of_eq qz793 (hardyZApproximantRS₀ qz27) Bool.false 2435574451463131533 4611686018427387904 65330936813989663517 45194522980588401459200 

noncomputable def Ns150p2078 := @Enclosure.Real.IsNear.pos_val qz793 2435574451463131533 4611686018427387904 65330936813989663517 45194522980588401459200 (Ns150p2077 (RS151to168.d38 qz3 qz27 qz268) RS151to168.d39) rfl 

noncomputable def Ns150p2079 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz792 qz3 qz3 400547 1000 400547 1000 

noncomputable def Ns150p2080 := @Enclosure.norm_gt_of_isNear qz792 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 821651366779736627731 295147905179352825856 13015004365296580772851 

noncomputable def Ns150p2081 := @Ns150p2080 Ns150p64 123907773 1342177280 1213 1342177280 (Ns150p2075 (RS151to168.d4 qz3 qz27 qz268) RS151to168.d37) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2082 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz793 qz3 qz27 400547 1000 402058 1000 

noncomputable def Ns150p2083 := @Enclosure.norm_gt_of_isNear qz793 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 2435574451463131533 4611686018427387904 65330936813989663517 

noncomputable def Ns150p2084 := @Ns150p2083 45194522980588401459200 123907773 1342177280 1213 1342177280 (Ns150p2077 (RS151to168.d38 qz3 qz27 qz268) RS151to168.d39) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2085 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz267 (@BSN.thirtyTwoPi_le_dec qz3 400547 1000 qz10 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz792 qz793 (Ns150p2076 rfl rfl) (Ns150p2078 rfl rfl)) (Ns150p2079 qz10 qz10 rfl rfl rfl rfl (Ns150p2081 rfl)) (Ns150p2082 qz10 qz30 rfl rfl rfl rfl (Ns150p2084 rfl)) 

noncomputable abbrev qz269 := (RS151to168.d3 qz374 qz398 (@Enclosure.dec_le_dec qz374 qz398 402058 1000 403568 1000 qz378 qz401 rfl rfl rfl))

noncomputable abbrev qz794 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz269)

noncomputable def Ns150p2086 := @Enclosure.Real.IsNear.of_eq qz794 (hardyZApproximantRS₀ qz27) Bool.false 2435574451463131533 4611686018427387904 65330936813989663517 45194522980588401459200 

noncomputable abbrev qz270 := (@Enclosure.dec_le_dec qz374 qz398 402058 1000 403568 1000 qz378 qz401 rfl rfl rfl)

noncomputable def Ns150p2087 := @Enclosure.Real.IsNear.pos_val qz794 2435574451463131533 4611686018427387904 65330936813989663517 45194522980588401459200 (Ns150p2086 (RS151to168.d4 qz27 qz47 qz270) RS151to168.d39) rfl 

noncomputable abbrev qz795 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz269)

noncomputable def Ns150p2088 := @Enclosure.Real.IsNear.of_eq qz795 (hardyZApproximantRS₀ qz47) Bool.true 73035826513246771277 73786976294838206464 903604238316071005107 564931537257355018240000 

noncomputable def Ns150p2089 := @Enclosure.Real.IsNear.neg_val qz795 73035826513246771277 73786976294838206464 903604238316071005107 564931537257355018240000 (Ns150p2088 (RS151to168.d38 qz27 qz47 qz270) RS151to168.d45) rfl 

noncomputable def Ns150p2090 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz794 qz3 qz27 400547 1000 402058 1000 

noncomputable def Ns150p2091 := @Enclosure.norm_gt_of_isNear qz794 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 2435574451463131533 4611686018427387904 65330936813989663517 

noncomputable def Ns150p2092 := @Ns150p2091 45194522980588401459200 123907773 1342177280 1213 1342177280 (Ns150p2086 (RS151to168.d4 qz27 qz47 qz270) RS151to168.d39) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2093 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz795 qz3 qz47 400547 1000 403568 1000 

noncomputable def Ns150p2094 := @Enclosure.norm_gt_of_isNear qz795 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 73035826513246771277 73786976294838206464 903604238316071005107 

noncomputable def Ns150p2095 := @Ns150p2094 564931537257355018240000 123907773 1342177280 1213 1342177280 (Ns150p2088 (RS151to168.d38 qz27 qz47 qz270) RS151to168.d45) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2096 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz269 (@BSN.thirtyTwoPi_le_dec qz27 402058 1000 qz30 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz794 qz795 (Ns150p2087 rfl rfl) (Ns150p2089 rfl rfl)) (Ns150p2090 qz10 qz30 rfl rfl rfl rfl (Ns150p2092 rfl)) (Ns150p2093 qz10 qz51 rfl rfl rfl rfl (Ns150p2095 rfl)) 

noncomputable abbrev qz271 := (RS151to168.d3 qz398 qz413 (@Enclosure.dec_le_dec qz398 qz413 403568 1000 405077 1000 qz401 qz416 rfl rfl rfl))

noncomputable abbrev qz796 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz271)

noncomputable def Ns150p2097 := @Enclosure.Real.IsNear.of_eq qz796 (hardyZApproximantRS₀ qz47) Bool.true 73035826513246771277 73786976294838206464 903604238316071005107 564931537257355018240000 

noncomputable abbrev qz272 := (@Enclosure.dec_le_dec qz398 qz413 403568 1000 405077 1000 qz401 qz416 rfl rfl rfl)

noncomputable def Ns150p2098 := @Enclosure.Real.IsNear.neg_val qz796 73035826513246771277 73786976294838206464 903604238316071005107 564931537257355018240000 (Ns150p2097 (RS151to168.d4 qz47 qz62 qz272) RS151to168.d45) rfl 

noncomputable abbrev qz797 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz271)

noncomputable def Ns150p2099 := @Enclosure.Real.IsNear.of_eq qz797 (hardyZApproximantRS₀ qz62) Bool.false 1551737812552519521 9223372036854775808 3628123719783859987683 Ns150p422 

noncomputable def Ns150p2100 := @Enclosure.Real.IsNear.pos_val qz797 1551737812552519521 9223372036854775808 3628123719783859987683 Ns150p422 (Ns150p2099 (RS151to168.d38 qz47 qz62 qz272) RS151to168.d46) rfl 

noncomputable def Ns150p2101 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz796 qz3 qz47 400547 1000 403568 1000 

noncomputable def Ns150p2102 := @Enclosure.norm_gt_of_isNear qz796 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 73035826513246771277 73786976294838206464 903604238316071005107 

noncomputable def Ns150p2103 := @Ns150p2102 564931537257355018240000 123907773 1342177280 1213 1342177280 (Ns150p2097 (RS151to168.d4 qz47 qz62 qz272) RS151to168.d45) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2104 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz797 qz3 qz62 400547 1000 405077 1000 

noncomputable def Ns150p2105 := @Enclosure.norm_gt_of_isNear qz797 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 1551737812552519521 9223372036854775808 3628123719783859987683 

noncomputable def Ns150p2106 := @Ns150p2105 Ns150p422 123907773 1342177280 1213 1342177280 (Ns150p2099 (RS151to168.d38 qz47 qz62 qz272) RS151to168.d46) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2107 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz271 (@BSN.thirtyTwoPi_le_dec qz47 403568 1000 qz51 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz796 qz797 (Ns150p2098 rfl rfl) (Ns150p2100 rfl rfl)) (Ns150p2101 qz10 qz51 rfl rfl rfl rfl (Ns150p2103 rfl)) (Ns150p2104 qz10 qz65 rfl rfl rfl rfl (Ns150p2106 rfl)) 

noncomputable abbrev qz273 := (RS151to168.d3 qz413 qz426 (@Enclosure.dec_le_dec qz413 qz426 405077 1000 406585 1000 qz416 qz429 rfl rfl rfl))

noncomputable abbrev qz798 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz273)

noncomputable def Ns150p2108 := @Enclosure.Real.IsNear.of_eq qz798 (hardyZApproximantRS₀ qz62) Bool.false 1551737812552519521 9223372036854775808 3628123719783859987683 Ns150p422 

noncomputable abbrev qz274 := (@Enclosure.dec_le_dec qz413 qz426 405077 1000 406585 1000 qz416 qz429 rfl rfl rfl)

noncomputable def Ns150p2109 := @Enclosure.Real.IsNear.pos_val qz798 1551737812552519521 9223372036854775808 3628123719783859987683 Ns150p422 (Ns150p2108 (RS151to168.d4 qz62 qz75 qz274) RS151to168.d46) rfl 

noncomputable abbrev qz799 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz273)

noncomputable def Ns150p2110 := @Enclosure.Real.IsNear.of_eq qz799 (hardyZApproximantRS₀ qz75) Bool.true 47620126860223971949 9223372036854775808 1040775034931730893731 645636042579834306560000 

noncomputable def Ns150p2111 := @Enclosure.Real.IsNear.neg_val qz799 47620126860223971949 9223372036854775808 1040775034931730893731 645636042579834306560000 (Ns150p2110 (RS151to168.d38 qz62 qz75 qz274) RS151to168.d47) rfl 

noncomputable def Ns150p2112 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz798 qz3 qz62 400547 1000 405077 1000 

noncomputable def Ns150p2113 := @Enclosure.norm_gt_of_isNear qz798 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 1551737812552519521 9223372036854775808 3628123719783859987683 

noncomputable def Ns150p2114 := @Ns150p2113 Ns150p422 123907773 1342177280 1213 1342177280 (Ns150p2108 (RS151to168.d4 qz62 qz75 qz274) RS151to168.d46) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2115 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz799 qz3 qz75 400547 1000 406585 1000 

noncomputable def Ns150p2116 := @Enclosure.norm_gt_of_isNear qz799 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 47620126860223971949 9223372036854775808 1040775034931730893731 

noncomputable def Ns150p2117 := @Ns150p2116 645636042579834306560000 123907773 1342177280 1213 1342177280 (Ns150p2110 (RS151to168.d38 qz62 qz75 qz274) RS151to168.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2118 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz273 (@BSN.thirtyTwoPi_le_dec qz62 405077 1000 qz65 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz798 qz799 (Ns150p2109 rfl rfl) (Ns150p2111 rfl rfl)) (Ns150p2112 qz10 qz65 rfl rfl rfl rfl (Ns150p2114 rfl)) (Ns150p2115 qz10 qz78 rfl rfl rfl rfl (Ns150p2117 rfl)) 

noncomputable abbrev qz275 := (RS151to168.d3 qz426 qz438 (@Enclosure.dec_le_dec qz426 qz438 406585 1000 408091 1000 qz429 qz441 rfl rfl rfl))

noncomputable abbrev qz800 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz275)

noncomputable def Ns150p2119 := @Enclosure.Real.IsNear.of_eq qz800 (hardyZApproximantRS₀ qz75) Bool.true 47620126860223971949 9223372036854775808 1040775034931730893731 645636042579834306560000 

noncomputable abbrev qz276 := (@Enclosure.dec_le_dec qz426 qz438 406585 1000 408091 1000 qz429 qz441 rfl rfl rfl)

noncomputable def Ns150p2120 := @Enclosure.Real.IsNear.neg_val qz800 47620126860223971949 9223372036854775808 1040775034931730893731 645636042579834306560000 (Ns150p2119 (RS151to168.d4 qz75 qz88 qz276) RS151to168.d47) rfl 

noncomputable abbrev qz801 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz275)

noncomputable def Ns150p2121 := @Enclosure.Real.IsNear.of_eq qz801 (hardyZApproximantRS₀ qz88) Bool.false 598773862616084374721 295147905179352825856 2925376572038020848037 Ns150p634 

noncomputable def Ns150p2122 := @Enclosure.Real.IsNear.pos_val qz801 598773862616084374721 295147905179352825856 2925376572038020848037 Ns150p634 (Ns150p2121 (RS151to168.d38 qz75 qz88 qz276) RS151to168.d48) rfl 

noncomputable def Ns150p2123 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz800 qz3 qz75 400547 1000 406585 1000 

noncomputable def Ns150p2124 := @Enclosure.norm_gt_of_isNear qz800 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 47620126860223971949 9223372036854775808 1040775034931730893731 

noncomputable def Ns150p2125 := @Ns150p2124 645636042579834306560000 123907773 1342177280 1213 1342177280 (Ns150p2119 (RS151to168.d4 qz75 qz88 qz276) RS151to168.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2126 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz801 qz3 qz88 400547 1000 408091 1000 

noncomputable def Ns150p2127 := @Enclosure.norm_gt_of_isNear qz801 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 598773862616084374721 295147905179352825856 2925376572038020848037 

noncomputable def Ns150p2128 := @Ns150p2127 Ns150p634 123907773 1342177280 1213 1342177280 (Ns150p2121 (RS151to168.d38 qz75 qz88 qz276) RS151to168.d48) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2129 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz275 (@BSN.thirtyTwoPi_le_dec qz75 406585 1000 qz78 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz800 qz801 (Ns150p2120 rfl rfl) (Ns150p2122 rfl rfl)) (Ns150p2123 qz10 qz78 rfl rfl rfl rfl (Ns150p2125 rfl)) (Ns150p2126 qz10 qz91 rfl rfl rfl rfl (Ns150p2128 rfl)) 

noncomputable abbrev qz277 := (RS151to168.d3 qz438 qz450 (@Enclosure.dec_le_dec qz438 qz450 408091 1000 409595 1000 qz441 qz453 rfl rfl rfl))

noncomputable abbrev qz802 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz277)

noncomputable def Ns150p2130 := @Enclosure.Real.IsNear.of_eq qz802 (hardyZApproximantRS₀ qz88) Bool.false 598773862616084374721 295147905179352825856 2925376572038020848037 Ns150p634 

noncomputable abbrev qz278 := (@Enclosure.dec_le_dec qz438 qz450 408091 1000 409595 1000 qz441 qz453 rfl rfl rfl)

noncomputable def Ns150p2131 := @Enclosure.Real.IsNear.pos_val qz802 598773862616084374721 295147905179352825856 2925376572038020848037 Ns150p634 (Ns150p2130 (RS151to168.d4 qz88 qz101 qz278) RS151to168.d48) rfl 

noncomputable abbrev qz803 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz277)

noncomputable def Ns150p2132 := @Enclosure.Real.IsNear.of_eq qz803 (hardyZApproximantRS₀ qz101) Bool.true 156116812993140797569 73786976294838206464 917651372644693236401 564931537257355018240000 

noncomputable def Ns150p2133 := @Enclosure.Real.IsNear.neg_val qz803 156116812993140797569 73786976294838206464 917651372644693236401 564931537257355018240000 (Ns150p2132 (RS151to168.d38 qz88 qz101 qz278) RS151to168.d49) rfl 

noncomputable def Ns150p2134 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz802 qz3 qz88 400547 1000 408091 1000 

noncomputable def Ns150p2135 := @Enclosure.norm_gt_of_isNear qz802 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 598773862616084374721 295147905179352825856 2925376572038020848037 

noncomputable def Ns150p2136 := @Ns150p2135 Ns150p634 123907773 1342177280 1213 1342177280 (Ns150p2130 (RS151to168.d4 qz88 qz101 qz278) RS151to168.d48) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2137 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz803 qz3 qz101 400547 1000 409595 1000 

noncomputable def Ns150p2138 := @Enclosure.norm_gt_of_isNear qz803 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 156116812993140797569 73786976294838206464 917651372644693236401 

noncomputable def Ns150p2139 := @Ns150p2138 564931537257355018240000 123907773 1342177280 1213 1342177280 (Ns150p2132 (RS151to168.d38 qz88 qz101 qz278) RS151to168.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2140 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz277 (@BSN.thirtyTwoPi_le_dec qz88 408091 1000 qz91 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz802 qz803 (Ns150p2131 rfl rfl) (Ns150p2133 rfl rfl)) (Ns150p2134 qz10 qz91 rfl rfl rfl rfl (Ns150p2136 rfl)) (Ns150p2137 qz10 qz104 rfl rfl rfl rfl (Ns150p2139 rfl)) 

noncomputable abbrev qz607 := (@Enclosure.dec_le_dec qz677 qz685 409595 1000 411099 1000 (@Eq.refl Real qz677) (@Eq.refl Real qz685) rfl rfl rfl)

noncomputable abbrev qz279 := (RS151to168.d3 qz450 qz462 qz607)

noncomputable abbrev qz804 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz279)

noncomputable def Ns150p2141 := @Enclosure.Real.IsNear.of_eq qz804 (hardyZApproximantRS₀ qz101) Bool.true 156116812993140797569 73786976294838206464 917651372644693236401 564931537257355018240000 

noncomputable abbrev qz280 := qz607

noncomputable def Ns150p2142 := @Enclosure.Real.IsNear.neg_val qz804 156116812993140797569 73786976294838206464 917651372644693236401 564931537257355018240000 (Ns150p2141 (RS151to168.d4 qz101 qz114 qz280) RS151to168.d49) rfl 

noncomputable abbrev qz805 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz279)

noncomputable def Ns150p2143 := @Enclosure.Real.IsNear.of_eq qz805 (hardyZApproximantRS₀ qz114) Bool.false 118605586243631369507 73786976294838206464 29487216287436053129 18077809192235360583680 

noncomputable def Ns150p2144 := @Enclosure.Real.IsNear.pos_val qz805 118605586243631369507 73786976294838206464 29487216287436053129 18077809192235360583680 (Ns150p2143 (RS151to168.d38 qz101 qz114 qz280) RS151to168.d50) rfl 

noncomputable def Ns150p2145 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz804 qz3 qz101 400547 1000 409595 1000 

noncomputable def Ns150p2146 := @Enclosure.norm_gt_of_isNear qz804 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 156116812993140797569 73786976294838206464 917651372644693236401 

noncomputable def Ns150p2147 := @Ns150p2146 564931537257355018240000 123907773 1342177280 1213 1342177280 (Ns150p2141 (RS151to168.d4 qz101 qz114 qz280) RS151to168.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2148 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz805 qz3 qz114 400547 1000 411099 1000 

noncomputable def Ns150p2149 := @Enclosure.norm_gt_of_isNear qz805 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 118605586243631369507 73786976294838206464 29487216287436053129 

noncomputable def Ns150p2150 := @Ns150p2149 18077809192235360583680 123907773 1342177280 1213 1342177280 (Ns150p2143 (RS151to168.d38 qz101 qz114 qz280) RS151to168.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2151 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz279 (@BSN.thirtyTwoPi_le_dec qz101 409595 1000 qz104 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz804 qz805 (Ns150p2142 rfl rfl) (Ns150p2144 rfl rfl)) (Ns150p2145 qz10 qz104 rfl rfl rfl rfl (Ns150p2147 rfl)) (Ns150p2148 qz10 qz117 rfl rfl rfl rfl (Ns150p2150 rfl)) 

noncomputable abbrev qz608 := (@Enclosure.dec_le_dec qz685 qz693 411099 1000 412601 1000 (@Eq.refl Real qz685) qz697 rfl rfl rfl)

noncomputable abbrev qz281 := (RS151to168.d3 qz462 qz474 qz608)

noncomputable abbrev qz806 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz281)

noncomputable def Ns150p2152 := @Enclosure.Real.IsNear.of_eq qz806 (hardyZApproximantRS₀ qz114) Bool.false 118605586243631369507 73786976294838206464 29487216287436053129 18077809192235360583680 

noncomputable abbrev qz282 := qz608

noncomputable def Ns150p2153 := @Enclosure.Real.IsNear.pos_val qz806 118605586243631369507 73786976294838206464 29487216287436053129 18077809192235360583680 (Ns150p2152 (RS151to168.d4 qz114 qz127 qz282) RS151to168.d50) rfl 

noncomputable abbrev qz807 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz281)

noncomputable def Ns150p2154 := @Enclosure.Real.IsNear.of_eq qz807 (hardyZApproximantRS₀ qz127) Bool.true 45944625016330594505 36893488147419103232 528914286066464303863 322818021289917153280000 

noncomputable def Ns150p2155 := @Enclosure.Real.IsNear.neg_val qz807 45944625016330594505 36893488147419103232 528914286066464303863 322818021289917153280000 (Ns150p2154 (RS151to168.d38 qz114 qz127 qz282) RS151to168.d51) rfl 

noncomputable def Ns150p2156 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz806 qz3 qz114 400547 1000 411099 1000 

noncomputable def Ns150p2157 := @Enclosure.norm_gt_of_isNear qz806 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 118605586243631369507 73786976294838206464 29487216287436053129 

noncomputable def Ns150p2158 := @Ns150p2157 18077809192235360583680 123907773 1342177280 1213 1342177280 (Ns150p2152 (RS151to168.d4 qz114 qz127 qz282) RS151to168.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2159 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz807 qz3 qz127 400547 1000 412601 1000 

noncomputable def Ns150p2160 := @Enclosure.norm_gt_of_isNear qz807 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 45944625016330594505 36893488147419103232 528914286066464303863 

noncomputable def Ns150p2161 := @Ns150p2160 322818021289917153280000 123907773 1342177280 1213 1342177280 (Ns150p2154 (RS151to168.d38 qz114 qz127 qz282) RS151to168.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2162 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz281 (@BSN.thirtyTwoPi_le_dec qz114 411099 1000 qz117 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz806 qz807 (Ns150p2153 rfl rfl) (Ns150p2155 rfl rfl)) (Ns150p2156 qz10 qz117 rfl rfl rfl rfl (Ns150p2158 rfl)) (Ns150p2159 qz10 qz130 rfl rfl rfl rfl (Ns150p2161 rfl)) 

noncomputable abbrev qz609 := (@Enclosure.dec_le_dec qz693 qz702 412601 1000 414477 1000 qz697 qz706 rfl rfl rfl)

noncomputable abbrev qz283 := (RS151to168.d3 qz474 qz486 qz609)

noncomputable abbrev qz808 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz283)

noncomputable def Ns150p2163 := @Enclosure.Real.IsNear.of_eq qz808 (hardyZApproximantRS₀ qz127) Bool.true 45944625016330594505 36893488147419103232 528914286066464303863 322818021289917153280000 

noncomputable abbrev qz284 := qz609

noncomputable def Ns150p2164 := @Enclosure.Real.IsNear.neg_val qz808 45944625016330594505 36893488147419103232 528914286066464303863 322818021289917153280000 (Ns150p2163 (RS151to168.d4 qz127 qz140 qz284) RS151to168.d51) rfl 

noncomputable abbrev qz809 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz283)

noncomputable def Ns150p2165 := @Enclosure.Real.IsNear.of_eq qz809 (hardyZApproximantRS₀ qz140) Bool.false 371089008576859953673 295147905179352825856 2127655661519932635087 Ns150p1046 

noncomputable def Ns150p2166 := @Enclosure.Real.IsNear.pos_val qz809 371089008576859953673 295147905179352825856 2127655661519932635087 Ns150p1046 (Ns150p2165 (RS151to168.d38 qz127 qz140 qz284) RS151to168.d52) rfl 

noncomputable def Ns150p2167 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz808 qz3 qz127 400547 1000 412601 1000 

noncomputable def Ns150p2168 := @Enclosure.norm_gt_of_isNear qz808 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 45944625016330594505 36893488147419103232 528914286066464303863 

noncomputable def Ns150p2169 := @Ns150p2168 322818021289917153280000 123907773 1342177280 1213 1342177280 (Ns150p2163 (RS151to168.d4 qz127 qz140 qz284) RS151to168.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2170 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz809 qz3 qz140 400547 1000 414477 1000 

noncomputable def Ns150p2171 := @Enclosure.norm_gt_of_isNear qz809 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 371089008576859953673 295147905179352825856 2127655661519932635087 

noncomputable def Ns150p2172 := @Ns150p2171 Ns150p1046 123907773 1342177280 1213 1342177280 (Ns150p2165 (RS151to168.d38 qz127 qz140 qz284) RS151to168.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2173 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz283 (@BSN.thirtyTwoPi_le_dec qz127 412601 1000 qz130 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz808 qz809 (Ns150p2164 rfl rfl) (Ns150p2166 rfl rfl)) (Ns150p2167 qz10 qz130 rfl rfl rfl rfl (Ns150p2169 rfl)) (Ns150p2170 qz10 qz143 rfl rfl rfl rfl (Ns150p2172 rfl)) 

noncomputable abbrev qz810 := (@Enclosure.dec_le_dec qz878 qz882 414477 1000 415227 1000 (@Eq.refl Real qz878) qz885 rfl rfl rfl)

noncomputable abbrev qz610 := qz810

noncomputable abbrev qz285 := (RS151to168.d3 qz486 qz498 qz610)

noncomputable abbrev qz811 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz285)

noncomputable def Ns150p2174 := @Enclosure.Real.IsNear.of_eq qz811 (hardyZApproximantRS₀ qz140) Bool.false 371089008576859953673 295147905179352825856 2127655661519932635087 Ns150p1046 

noncomputable abbrev qz286 := qz610

noncomputable def Ns150p2175 := @Enclosure.Real.IsNear.pos_val qz811 371089008576859953673 295147905179352825856 2127655661519932635087 Ns150p1046 (Ns150p2174 (RS151to168.d4 qz140 qz153 qz286) RS151to168.d52) rfl 

noncomputable abbrev qz812 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz285)

noncomputable def Ns150p2176 := @Enclosure.Real.IsNear.of_eq qz812 (hardyZApproximantRS₀ qz153) Bool.true 3582140190373944587 18446744073709551616 1065830695402755616977 645636042579834306560000 

noncomputable def Ns150p2177 := @Enclosure.Real.IsNear.neg_val qz812 3582140190373944587 18446744073709551616 1065830695402755616977 645636042579834306560000 (Ns150p2176 (RS151to168.d38 qz140 qz153 qz286) RS151to168.d53) rfl 

noncomputable def Ns150p2178 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz811 qz3 qz140 400547 1000 414477 1000 

noncomputable def Ns150p2179 := @Enclosure.norm_gt_of_isNear qz811 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 371089008576859953673 295147905179352825856 2127655661519932635087 

noncomputable def Ns150p2180 := @Ns150p2179 Ns150p1046 123907773 1342177280 1213 1342177280 (Ns150p2174 (RS151to168.d4 qz140 qz153 qz286) RS151to168.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2181 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz812 qz3 qz153 400547 1000 415227 1000 

noncomputable def Ns150p2182 := @Enclosure.norm_gt_of_isNear qz812 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 3582140190373944587 18446744073709551616 1065830695402755616977 

noncomputable def Ns150p2183 := @Ns150p2182 645636042579834306560000 123907773 1342177280 1213 1342177280 (Ns150p2176 (RS151to168.d38 qz140 qz153 qz286) RS151to168.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2184 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz285 (@BSN.thirtyTwoPi_le_dec qz140 414477 1000 qz143 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz811 qz812 (Ns150p2175 rfl rfl) (Ns150p2177 rfl rfl)) (Ns150p2178 qz10 qz143 rfl rfl rfl rfl (Ns150p2180 rfl)) (Ns150p2181 qz10 qz156 rfl rfl rfl rfl (Ns150p2183 rfl)) 

noncomputable abbrev qz921 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 415227 1000) (Enclosure.sfrac Bool.false 416351 1000) 415227 1000 416351 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 415227 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 416351 1000)) rfl rfl rfl)

noncomputable abbrev qz813 := qz921

noncomputable abbrev qz611 := qz813

noncomputable abbrev qz287 := (RS151to168.d3 qz498 qz510 qz611)

noncomputable abbrev qz814 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz287)

noncomputable def Ns150p2185 := @Enclosure.Real.IsNear.of_eq qz814 (hardyZApproximantRS₀ qz153) Bool.true 3582140190373944587 18446744073709551616 1065830695402755616977 645636042579834306560000 

noncomputable abbrev qz288 := qz611

noncomputable def Ns150p2186 := @Enclosure.Real.IsNear.neg_val qz814 3582140190373944587 18446744073709551616 1065830695402755616977 645636042579834306560000 (Ns150p2185 (RS151to168.d4 qz153 qz166 qz288) RS151to168.d53) rfl 

noncomputable abbrev qz815 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz287)

noncomputable def Ns150p2187 := @Enclosure.Real.IsNear.of_eq qz815 (hardyZApproximantRS₀ qz166) Bool.false 694271227214752653133 147573952589676412928 1069779892913913078847 645636042579834306560000 

noncomputable def Ns150p2188 := @Enclosure.Real.IsNear.pos_val qz815 694271227214752653133 147573952589676412928 1069779892913913078847 645636042579834306560000 (Ns150p2187 (RS151to168.d38 qz153 qz166 qz288) RS151to168.d54) rfl 

noncomputable def Ns150p2189 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz814 qz3 qz153 400547 1000 415227 1000 

noncomputable def Ns150p2190 := @Enclosure.norm_gt_of_isNear qz814 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 3582140190373944587 18446744073709551616 1065830695402755616977 

noncomputable def Ns150p2191 := @Ns150p2190 645636042579834306560000 123907773 1342177280 1213 1342177280 (Ns150p2185 (RS151to168.d4 qz153 qz166 qz288) RS151to168.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2192 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz815 qz3 qz166 400547 1000 416351 1000 

noncomputable def Ns150p2193 := @Enclosure.norm_gt_of_isNear qz815 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 694271227214752653133 147573952589676412928 1069779892913913078847 

noncomputable def Ns150p2194 := @Ns150p2193 645636042579834306560000 123907773 1342177280 1213 1342177280 (Ns150p2187 (RS151to168.d38 qz153 qz166 qz288) RS151to168.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2195 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz287 (@BSN.thirtyTwoPi_le_dec qz153 415227 1000 qz156 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz814 qz815 (Ns150p2186 rfl rfl) (Ns150p2188 rfl rfl)) (Ns150p2189 qz10 qz156 rfl rfl rfl rfl (Ns150p2191 rfl)) (Ns150p2192 qz10 qz169 rfl rfl rfl rfl (Ns150p2194 rfl)) 

noncomputable abbrev qz289 := (RS151to168.d3 qz510 qz522 (@Enclosure.dec_le_dec qz510 qz522 416351 1000 418597 1000 qz513 qz525 rfl rfl rfl))

noncomputable abbrev qz816 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz289)

noncomputable def Ns150p2196 := @Enclosure.Real.IsNear.of_eq qz816 (hardyZApproximantRS₀ qz166) Bool.false 694271227214752653133 147573952589676412928 1069779892913913078847 645636042579834306560000 

noncomputable abbrev qz290 := (@Enclosure.dec_le_dec qz510 qz522 416351 1000 418597 1000 qz513 qz525 rfl rfl rfl)

noncomputable def Ns150p2197 := @Enclosure.Real.IsNear.pos_val qz816 694271227214752653133 147573952589676412928 1069779892913913078847 645636042579834306560000 (Ns150p2196 (RS151to168.d4 qz166 qz179 qz290) RS151to168.d54) rfl 

noncomputable abbrev qz817 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz289)

noncomputable def Ns150p2198 := @Enclosure.Real.IsNear.of_eq qz817 (hardyZApproximantRS₀ qz179) Bool.true 38196261884258215817 36893488147419103232 7552354598580019643831 Ns150p1358 

noncomputable def Ns150p2199 := @Enclosure.Real.IsNear.neg_val qz817 38196261884258215817 36893488147419103232 7552354598580019643831 Ns150p1358 (Ns150p2198 (RS151to168.d38 qz166 qz179 qz290) RS151to168.d55) rfl 

noncomputable def Ns150p2200 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz816 qz3 qz166 400547 1000 416351 1000 

noncomputable def Ns150p2201 := @Enclosure.norm_gt_of_isNear qz816 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 694271227214752653133 147573952589676412928 1069779892913913078847 

noncomputable def Ns150p2202 := @Ns150p2201 645636042579834306560000 123907773 1342177280 1213 1342177280 (Ns150p2196 (RS151to168.d4 qz166 qz179 qz290) RS151to168.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2203 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz817 qz3 qz179 400547 1000 418597 1000 

noncomputable def Ns150p2204 := @Enclosure.norm_gt_of_isNear qz817 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 38196261884258215817 36893488147419103232 7552354598580019643831 

noncomputable def Ns150p2205 := @Ns150p2204 Ns150p1358 123907773 1342177280 1213 1342177280 (Ns150p2198 (RS151to168.d38 qz166 qz179 qz290) RS151to168.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2206 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz289 (@BSN.thirtyTwoPi_le_dec qz166 416351 1000 qz169 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz816 qz817 (Ns150p2197 rfl rfl) (Ns150p2199 rfl rfl)) (Ns150p2200 qz10 qz169 rfl rfl rfl rfl (Ns150p2202 rfl)) (Ns150p2203 qz10 qz182 rfl rfl rfl rfl (Ns150p2205 rfl)) 

noncomputable abbrev qz291 := (RS151to168.d3 qz522 qz534 (@Enclosure.dec_le_dec qz522 qz534 418597 1000 420092 1000 qz525 qz537 rfl rfl rfl))

noncomputable abbrev qz818 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz291)

noncomputable def Ns150p2207 := @Enclosure.Real.IsNear.of_eq qz818 (hardyZApproximantRS₀ qz179) Bool.true 38196261884258215817 36893488147419103232 7552354598580019643831 Ns150p1358 

noncomputable abbrev qz292 := (@Enclosure.dec_le_dec qz522 qz534 418597 1000 420092 1000 qz525 qz537 rfl rfl rfl)

noncomputable def Ns150p2208 := @Enclosure.Real.IsNear.neg_val qz818 38196261884258215817 36893488147419103232 7552354598580019643831 Ns150p1358 (Ns150p2207 (RS151to168.d4 qz179 qz192 qz292) RS151to168.d55) rfl 

noncomputable abbrev qz819 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz291)

noncomputable def Ns150p2209 := @Enclosure.Real.IsNear.of_eq qz819 (hardyZApproximantRS₀ qz192) Bool.false 25995051504712239951 73786976294838206464 108519948405175974477 64563604257983430656000 

noncomputable def Ns150p2210 := @Enclosure.Real.IsNear.pos_val qz819 25995051504712239951 73786976294838206464 108519948405175974477 64563604257983430656000 (Ns150p2209 (RS151to168.d38 qz179 qz192 qz292) RS151to168.d56) rfl 

noncomputable def Ns150p2211 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz818 qz3 qz179 400547 1000 418597 1000 

noncomputable def Ns150p2212 := @Enclosure.norm_gt_of_isNear qz818 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 38196261884258215817 36893488147419103232 7552354598580019643831 

noncomputable def Ns150p2213 := @Ns150p2212 Ns150p1358 123907773 1342177280 1213 1342177280 (Ns150p2207 (RS151to168.d4 qz179 qz192 qz292) RS151to168.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2214 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz819 qz3 qz192 400547 1000 420092 1000 

noncomputable def Ns150p2215 := @Enclosure.norm_gt_of_isNear qz819 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 25995051504712239951 73786976294838206464 108519948405175974477 

noncomputable def Ns150p2216 := @Ns150p2215 64563604257983430656000 123907773 1342177280 1213 1342177280 (Ns150p2209 (RS151to168.d38 qz179 qz192 qz292) RS151to168.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2217 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz291 (@BSN.thirtyTwoPi_le_dec qz179 418597 1000 qz182 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz818 qz819 (Ns150p2208 rfl rfl) (Ns150p2210 rfl rfl)) (Ns150p2211 qz10 qz182 rfl rfl rfl rfl (Ns150p2213 rfl)) (Ns150p2214 qz10 qz195 rfl rfl rfl rfl (Ns150p2216 rfl)) 

noncomputable abbrev qz612 := (@Enclosure.dec_le_dec qz739 qz747 420092 1000 421587 1000 (@Eq.refl Real qz739) (@Eq.refl Real qz747) rfl rfl rfl)

noncomputable abbrev qz293 := (RS151to168.d3 qz534 qz546 qz612)

noncomputable abbrev qz820 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz293)

noncomputable def Ns150p2218 := @Enclosure.Real.IsNear.of_eq qz820 (hardyZApproximantRS₀ qz192) Bool.false 25995051504712239951 73786976294838206464 108519948405175974477 64563604257983430656000 

noncomputable abbrev qz294 := qz612

noncomputable def Ns150p2219 := @Enclosure.Real.IsNear.pos_val qz820 25995051504712239951 73786976294838206464 108519948405175974477 64563604257983430656000 (Ns150p2218 (RS151to168.d4 qz192 qz205 qz294) RS151to168.d56) rfl 

noncomputable abbrev qz821 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz293)

noncomputable def Ns150p2220 := @Enclosure.Real.IsNear.of_eq qz821 (hardyZApproximantRS₀ qz205) Bool.true 171854983879093770045 147573952589676412928 3828025088913795676289 Ns150p422 

noncomputable def Ns150p2221 := @Enclosure.Real.IsNear.neg_val qz821 171854983879093770045 147573952589676412928 3828025088913795676289 Ns150p422 (Ns150p2220 (RS151to168.d38 qz192 qz205 qz294) RS151to168.d57) rfl 

noncomputable def Ns150p2222 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz820 qz3 qz192 400547 1000 420092 1000 

noncomputable def Ns150p2223 := @Enclosure.norm_gt_of_isNear qz820 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 25995051504712239951 73786976294838206464 108519948405175974477 

noncomputable def Ns150p2224 := @Ns150p2223 64563604257983430656000 123907773 1342177280 1213 1342177280 (Ns150p2218 (RS151to168.d4 qz192 qz205 qz294) RS151to168.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2225 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz821 qz3 qz205 400547 1000 421587 1000 

noncomputable def Ns150p2226 := @Enclosure.norm_gt_of_isNear qz821 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 171854983879093770045 147573952589676412928 3828025088913795676289 

noncomputable def Ns150p2227 := @Ns150p2226 Ns150p422 123907773 1342177280 1213 1342177280 (Ns150p2220 (RS151to168.d38 qz192 qz205 qz294) RS151to168.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2228 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz293 (@BSN.thirtyTwoPi_le_dec qz192 420092 1000 qz195 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz820 qz821 (Ns150p2219 rfl rfl) (Ns150p2221 rfl rfl)) (Ns150p2222 qz10 qz195 rfl rfl rfl rfl (Ns150p2224 rfl)) (Ns150p2225 qz10 qz208 rfl rfl rfl rfl (Ns150p2227 rfl)) 

noncomputable abbrev qz613 := (@Enclosure.dec_le_dec qz747 qz755 421587 1000 423080 1000 (@Eq.refl Real qz747) qz759 rfl rfl rfl)

noncomputable abbrev qz295 := (RS151to168.d3 qz546 qz558 qz613)

noncomputable abbrev qz822 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz295)

noncomputable def Ns150p2229 := @Enclosure.Real.IsNear.of_eq qz822 (hardyZApproximantRS₀ qz205) Bool.true 171854983879093770045 147573952589676412928 3828025088913795676289 Ns150p422 

noncomputable abbrev qz296 := qz613

noncomputable def Ns150p2230 := @Enclosure.Real.IsNear.neg_val qz822 171854983879093770045 147573952589676412928 3828025088913795676289 Ns150p422 (Ns150p2229 (RS151to168.d4 qz205 qz218 qz296) RS151to168.d57) rfl 

noncomputable abbrev qz823 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz295)

noncomputable def Ns150p2231 := @Enclosure.Real.IsNear.of_eq qz823 (hardyZApproximantRS₀ qz218) Bool.false 76117890369564079753 36893488147419103232 553175275399385690241 322818021289917153280000 

noncomputable def Ns150p2232 := @Enclosure.Real.IsNear.pos_val qz823 76117890369564079753 36893488147419103232 553175275399385690241 322818021289917153280000 (Ns150p2231 (RS151to168.d38 qz205 qz218 qz296) RS151to168.d58) rfl 

noncomputable def Ns150p2233 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz822 qz3 qz205 400547 1000 421587 1000 

noncomputable def Ns150p2234 := @Enclosure.norm_gt_of_isNear qz822 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 171854983879093770045 147573952589676412928 3828025088913795676289 

noncomputable def Ns150p2235 := @Ns150p2234 Ns150p422 123907773 1342177280 1213 1342177280 (Ns150p2229 (RS151to168.d4 qz205 qz218 qz296) RS151to168.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2236 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz823 qz3 qz218 400547 1000 423080 1000 

noncomputable def Ns150p2237 := @Enclosure.norm_gt_of_isNear qz823 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 76117890369564079753 36893488147419103232 553175275399385690241 

noncomputable def Ns150p2238 := @Ns150p2237 322818021289917153280000 123907773 1342177280 1213 1342177280 (Ns150p2231 (RS151to168.d38 qz205 qz218 qz296) RS151to168.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2239 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz295 (@BSN.thirtyTwoPi_le_dec qz205 421587 1000 qz208 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz822 qz823 (Ns150p2230 rfl rfl) (Ns150p2232 rfl rfl)) (Ns150p2233 qz10 qz208 rfl rfl rfl rfl (Ns150p2235 rfl)) (Ns150p2236 qz10 qz221 rfl rfl rfl rfl (Ns150p2238 rfl)) 

noncomputable abbrev qz614 := (@Enclosure.dec_le_dec qz755 qz764 423080 1000 424572 1000 qz759 qz768 rfl rfl rfl)

noncomputable abbrev qz297 := (RS151to168.d3 qz558 qz570 qz614)

noncomputable abbrev qz824 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz297)

noncomputable def Ns150p2240 := @Enclosure.Real.IsNear.of_eq qz824 (hardyZApproximantRS₀ qz218) Bool.false 76117890369564079753 36893488147419103232 553175275399385690241 322818021289917153280000 

noncomputable abbrev qz298 := qz614

noncomputable def Ns150p2241 := @Enclosure.Real.IsNear.pos_val qz824 76117890369564079753 36893488147419103232 553175275399385690241 322818021289917153280000 (Ns150p2240 (RS151to168.d4 qz218 qz231 qz298) RS151to168.d58) rfl 

noncomputable abbrev qz825 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz297)

noncomputable def Ns150p2242 := @Enclosure.Real.IsNear.of_eq qz825 (hardyZApproximantRS₀ qz231) Bool.true 68996668191873247113 36893488147419103232 225276055515579727537 129127208515966861312000 

noncomputable def Ns150p2243 := @Enclosure.Real.IsNear.neg_val qz825 68996668191873247113 36893488147419103232 225276055515579727537 129127208515966861312000 (Ns150p2242 (RS151to168.d38 qz218 qz231 qz298) RS151to168.d59) rfl 

noncomputable def Ns150p2244 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz824 qz3 qz218 400547 1000 423080 1000 

noncomputable def Ns150p2245 := @Enclosure.norm_gt_of_isNear qz824 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 76117890369564079753 36893488147419103232 553175275399385690241 

noncomputable def Ns150p2246 := @Ns150p2245 322818021289917153280000 123907773 1342177280 1213 1342177280 (Ns150p2240 (RS151to168.d4 qz218 qz231 qz298) RS151to168.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2247 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz825 qz3 qz231 400547 1000 424572 1000 

noncomputable def Ns150p2248 := @Enclosure.norm_gt_of_isNear qz825 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 68996668191873247113 36893488147419103232 225276055515579727537 

noncomputable def Ns150p2249 := @Ns150p2248 129127208515966861312000 123907773 1342177280 1213 1342177280 (Ns150p2242 (RS151to168.d38 qz218 qz231 qz298) RS151to168.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2250 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz297 (@BSN.thirtyTwoPi_le_dec qz218 423080 1000 qz221 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz824 qz825 (Ns150p2241 rfl rfl) (Ns150p2243 rfl rfl)) (Ns150p2244 qz10 qz221 rfl rfl rfl rfl (Ns150p2246 rfl)) (Ns150p2247 qz10 qz234 rfl rfl rfl rfl (Ns150p2249 rfl)) 

noncomputable abbrev qz826 := (@Enclosure.dec_le_dec qz908 qz912 424572 1000 426063 1000 (@Eq.refl Real qz908) qz915 rfl rfl rfl)

noncomputable abbrev qz615 := qz826

noncomputable abbrev qz299 := (RS151to168.d3 qz570 qz582 qz615)

noncomputable abbrev qz827 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz299)

noncomputable def Ns150p2251 := @Enclosure.Real.IsNear.of_eq qz827 (hardyZApproximantRS₀ qz231) Bool.true 68996668191873247113 36893488147419103232 225276055515579727537 129127208515966861312000 

noncomputable abbrev qz300 := qz615

noncomputable def Ns150p2252 := @Enclosure.Real.IsNear.neg_val qz827 68996668191873247113 36893488147419103232 225276055515579727537 129127208515966861312000 (Ns150p2251 (RS151to168.d4 qz231 qz244 qz300) RS151to168.d59) rfl 

noncomputable abbrev qz828 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz299)

noncomputable def Ns150p2253 := @Enclosure.Real.IsNear.of_eq qz828 (hardyZApproximantRS₀ qz244) Bool.false 157867458824134067809 36893488147419103232 8240217843221576595829 Ns150p1358 

noncomputable def Ns150p2254 := @Enclosure.Real.IsNear.pos_val qz828 157867458824134067809 36893488147419103232 8240217843221576595829 Ns150p1358 (Ns150p2253 (RS151to168.d38 qz231 qz244 qz300) RS151to168.d60) rfl 

noncomputable def Ns150p2255 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz827 qz3 qz231 400547 1000 424572 1000 

noncomputable def Ns150p2256 := @Enclosure.norm_gt_of_isNear qz827 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 68996668191873247113 36893488147419103232 225276055515579727537 

noncomputable def Ns150p2257 := @Ns150p2256 129127208515966861312000 123907773 1342177280 1213 1342177280 (Ns150p2251 (RS151to168.d4 qz231 qz244 qz300) RS151to168.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2258 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz828 qz3 qz244 400547 1000 426063 1000 

noncomputable def Ns150p2259 := @Enclosure.norm_gt_of_isNear qz828 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 157867458824134067809 36893488147419103232 8240217843221576595829 

noncomputable def Ns150p2260 := @Ns150p2259 Ns150p1358 123907773 1342177280 1213 1342177280 (Ns150p2253 (RS151to168.d38 qz231 qz244 qz300) RS151to168.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2261 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz299 (@BSN.thirtyTwoPi_le_dec qz231 424572 1000 qz234 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz827 qz828 (Ns150p2252 rfl rfl) (Ns150p2254 rfl rfl)) (Ns150p2255 qz10 qz234 rfl rfl rfl rfl (Ns150p2257 rfl)) (Ns150p2258 qz10 qz247 rfl rfl rfl rfl (Ns150p2260 rfl)) 

noncomputable abbrev qz922 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 426063 1000) (Enclosure.sfrac Bool.false 427552 1000) 426063 1000 427552 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 426063 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 427552 1000)) rfl rfl rfl)

noncomputable abbrev qz829 := qz922

noncomputable abbrev qz616 := qz829

noncomputable abbrev qz301 := (RS151to168.d3 qz582 qz595 qz616)

noncomputable abbrev qz830 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz301)

noncomputable def Ns150p2262 := @Enclosure.Real.IsNear.of_eq qz830 (hardyZApproximantRS₀ qz244) Bool.false 157867458824134067809 36893488147419103232 8240217843221576595829 Ns150p1358 

noncomputable abbrev qz302 := qz616

noncomputable def Ns150p2263 := @Enclosure.Real.IsNear.pos_val qz830 157867458824134067809 36893488147419103232 8240217843221576595829 Ns150p1358 (Ns150p2262 (RS151to168.d4 qz244 qz256 qz302) RS151to168.d60) rfl 

noncomputable abbrev qz831 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz301)

noncomputable def Ns150p2264 := @Enclosure.Real.IsNear.of_eq qz831 (hardyZApproximantRS₀ qz256) Bool.true 8265060605337999 9007199254740992 9332322801257230109893 Ns150p422 

noncomputable def Ns150p2265 := @Enclosure.Real.IsNear.neg_val qz831 8265060605337999 9007199254740992 9332322801257230109893 Ns150p422 (Ns150p2264 (RS151to168.d38 qz244 qz256 qz302) RS151to168.d61) rfl 

noncomputable def Ns150p2266 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz830 qz3 qz244 400547 1000 426063 1000 

noncomputable def Ns150p2267 := @Enclosure.norm_gt_of_isNear qz830 (hardyZErrorBoundRS₀ qz3) Bool.false Bool.false 157867458824134067809 36893488147419103232 8240217843221576595829 

noncomputable def Ns150p2268 := @Ns150p2267 Ns150p1358 123907773 1342177280 1213 1342177280 (Ns150p2262 (RS151to168.d4 qz244 qz256 qz302) RS151to168.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2269 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz831 qz3 qz256 400547 1000 427552 1000 

noncomputable def Ns150p2270 := @Enclosure.norm_gt_of_isNear qz831 (hardyZErrorBoundRS₀ qz3) Bool.true Bool.false 8265060605337999 9007199254740992 9332322801257230109893 

noncomputable def Ns150p2271 := @Ns150p2270 Ns150p422 123907773 1342177280 1213 1342177280 (Ns150p2264 (RS151to168.d38 qz244 qz256 qz302) RS151to168.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz3) (hardyZErrorBoundRS₀ qz3) Bool.false 123907773 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz3)) RS151to168.d40) rfl rfl rfl rfl 

noncomputable def Ns150p2272 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz301 (@BSN.thirtyTwoPi_le_dec qz244 426063 1000 qz247 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz830 qz831 (Ns150p2263 rfl rfl) (Ns150p2265 rfl rfl)) (Ns150p2266 qz10 qz247 rfl rfl rfl rfl (Ns150p2268 rfl)) (Ns150p2269 qz10 (@Eq.refl Real qz256) rfl rfl rfl rfl (Ns150p2271 rfl)) 

noncomputable def Ns150p2273 := @List.cons RS151to168.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz299 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz299) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz299) Ns150p2261)) (@List.cons RS151to168.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz301 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz301) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz301) Ns150p2272)) (@List.nil RS151to168.d0)) 

noncomputable def Ns150p2274 := @List.cons RS151to168.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz295 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz295) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz295) Ns150p2239)) (@List.cons RS151to168.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz297 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz297) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz297) Ns150p2250)) Ns150p2273) 

noncomputable def Ns150p2275 := @List.cons RS151to168.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz291 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz291) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz291) Ns150p2217)) (@List.cons RS151to168.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz293 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz293) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz293) Ns150p2228)) Ns150p2274) 

noncomputable def Ns150p2276 := @List.cons RS151to168.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz287 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz287) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz287) Ns150p2195)) (@List.cons RS151to168.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz289 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz289) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz289) Ns150p2206)) Ns150p2275) 

noncomputable def Ns150p2277 := @List.cons RS151to168.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz283 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz283) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz283) Ns150p2173)) (@List.cons RS151to168.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz285 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz285) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz285) Ns150p2184)) Ns150p2276) 

noncomputable def Ns150p2278 := @List.cons RS151to168.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz279 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz279) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz279) Ns150p2151)) (@List.cons RS151to168.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz281 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz281) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz281) Ns150p2162)) Ns150p2277) 

noncomputable def Ns150p2279 := @List.cons RS151to168.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz275 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz275) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz275) Ns150p2129)) (@List.cons RS151to168.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz277 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz277) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz277) Ns150p2140)) Ns150p2278) 

noncomputable def Ns150p2280 := @List.cons RS151to168.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz271 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz271) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz271) Ns150p2107)) (@List.cons RS151to168.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz273 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz273) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz273) Ns150p2118)) Ns150p2279) 

noncomputable def Ns150p2281 := @List.cons RS151to168.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz267 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz267) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz267) Ns150p2085)) (@List.cons RS151to168.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz269 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz269) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz269) Ns150p2096)) Ns150p2280) 

noncomputable abbrev qz832 := (RS151to168.d2 qz908 qz912 (@Enclosure.dec_le_dec qz908 qz912 424572 1000 426063 1000 (@Eq.refl Real qz908) qz915 rfl rfl rfl))

noncomputable abbrev qz833 := (@List.cons RS151to168.d1 (RS151to168.d2 qz912 qz917 qz922) (@List.nil RS151to168.d1))

noncomputable abbrev qz617 := (@List.cons RS151to168.d1 (RS151to168.d2 qz755 qz764 (@Enclosure.dec_le_dec qz755 qz764 423080 1000 424572 1000 qz759 qz768 rfl rfl rfl)) (@List.cons RS151to168.d1 qz832 qz833))

noncomputable abbrev qz303 := (@List.cons RS151to168.d1 (RS151to168.d2 qz534 qz546 qz612) (@List.cons RS151to168.d1 (RS151to168.d2 qz546 qz558 qz613) qz617))

noncomputable def Ns150p2282 := @List.cons RS151to168.d1 (RS151to168.d2 qz166 qz179 qz290) (@List.cons RS151to168.d1 (RS151to168.d2 qz179 qz192 qz292) qz303) 

noncomputable abbrev qz834 := (RS151to168.d2 qz878 qz882 (@Enclosure.dec_le_dec qz878 qz882 414477 1000 415227 1000 (@Eq.refl Real qz878) qz885 rfl rfl rfl))

noncomputable abbrev qz835 := (@List.cons RS151to168.d1 (RS151to168.d2 qz882 qz887 qz921) Ns150p2282)

noncomputable abbrev qz618 := (@List.cons RS151to168.d1 (RS151to168.d2 qz693 qz702 (@Enclosure.dec_le_dec qz693 qz702 412601 1000 414477 1000 qz697 qz706 rfl rfl rfl)) (@List.cons RS151to168.d1 qz834 qz835))

noncomputable abbrev qz304 := (@List.cons RS151to168.d1 (RS151to168.d2 qz450 qz462 qz607) (@List.cons RS151to168.d1 (RS151to168.d2 qz462 qz474 qz608) qz618))

noncomputable def Ns150p2283 := @List.cons RS151to168.d1 (RS151to168.d2 qz75 qz88 qz276) (@List.cons RS151to168.d1 (RS151to168.d2 qz88 qz101 qz278) qz304) 

noncomputable def Ns150p2284 := @List.IsChain.cons_cons RS151to168.d1 RS151to168.d62 (RS151to168.d2 qz62 qz75 qz274) (RS151to168.d2 qz75 qz88 qz276) (@List.cons RS151to168.d1 (RS151to168.d2 qz88 qz101 qz278) qz304) 

noncomputable def Ns150p2285 := @List.IsChain.cons_cons RS151to168.d1 RS151to168.d62 (RS151to168.d2 qz75 qz88 qz276) (RS151to168.d2 qz88 qz101 qz278) qz304 (@Enclosure.dec_le_dec qz88 qz88 408091 1000 408091 1000 qz91 qz91 rfl rfl rfl) 

noncomputable abbrev qz836 := (RS151to168.d2 qz882 qz887 qz921)

noncomputable abbrev qz619 := qz836

noncomputable abbrev qz305 := qz619

noncomputable def Ns150p2286 := @List.IsChain.cons_cons RS151to168.d1 RS151to168.d62 qz305 (RS151to168.d2 qz166 qz179 qz290) (@List.cons RS151to168.d1 (RS151to168.d2 qz179 qz192 qz292) qz303) 

noncomputable def Ns150p2287 := @List.IsChain.cons_cons RS151to168.d1 RS151to168.d62 (RS151to168.d2 qz166 qz179 qz290) (RS151to168.d2 qz179 qz192 qz292) qz303 (@Enclosure.dec_le_dec qz179 qz179 418597 1000 418597 1000 qz182 qz182 rfl rfl rfl) 

noncomputable abbrev qz306 := qz617

noncomputable abbrev qz620 := (@List.cons RS151to168.d1 qz832 qz833)

noncomputable abbrev qz307 := qz620

noncomputable abbrev qz621 := qz832

noncomputable abbrev qz308 := qz621

noncomputable abbrev qz622 := qz833

noncomputable abbrev qz309 := qz622

noncomputable abbrev qz837 := (RS151to168.d2 qz912 qz917 qz922)

noncomputable abbrev qz623 := qz837

noncomputable abbrev qz310 := qz623

noncomputable def Ns150p2288 := @List.IsChain.cons_cons RS151to168.d1 RS151to168.d62 (RS151to168.d2 qz192 qz205 qz294) (RS151to168.d2 qz205 qz218 qz296) qz306 (@Enclosure.dec_le_dec qz205 qz205 421587 1000 421587 1000 qz208 qz208 rfl rfl rfl) (@List.IsChain.cons_cons RS151to168.d1 RS151to168.d62 (RS151to168.d2 qz205 qz218 qz296) (RS151to168.d2 qz218 qz231 qz298) qz307 (@Enclosure.dec_le_dec qz218 qz218 423080 1000 423080 1000 qz221 qz221 rfl rfl rfl) (@List.IsChain.cons_cons RS151to168.d1 RS151to168.d62 (RS151to168.d2 qz218 qz231 qz298) qz308 qz309 (@Enclosure.dec_le_dec qz231 qz231 424572 1000 424572 1000 qz234 qz234 rfl rfl rfl) (@List.IsChain.cons_cons RS151to168.d1 RS151to168.d62 qz308 qz310 (@List.nil RS151to168.d1) (@Enclosure.dec_le_dec qz244 qz244 426063 1000 426063 1000 qz247 qz247 rfl rfl rfl) (@List.IsChain.singleton RS151to168.d1 RS151to168.d62 qz310)))) 

noncomputable abbrev qz311 := (@List.cons RS151to168.d1 (RS151to168.d2 qz546 qz558 qz613) qz617)

noncomputable def Ns150p2289 := @List.IsChain.cons_cons RS151to168.d1 RS151to168.d62 (RS151to168.d2 qz179 qz192 qz292) (RS151to168.d2 qz192 qz205 qz294) qz311 (@Enclosure.dec_le_dec qz192 qz192 420092 1000 420092 1000 qz195 qz195 rfl rfl rfl) Ns150p2288 

noncomputable abbrev qz312 := qz618

noncomputable abbrev qz624 := (@List.cons RS151to168.d1 qz834 qz835)

noncomputable abbrev qz313 := qz624

noncomputable abbrev qz625 := qz834

noncomputable abbrev qz314 := qz625

noncomputable abbrev qz626 := qz835

noncomputable abbrev qz315 := qz626

noncomputable def Ns150p2290 := @List.IsChain.cons_cons RS151to168.d1 RS151to168.d62 (RS151to168.d2 qz101 qz114 qz280) (RS151to168.d2 qz114 qz127 qz282) qz312 (@Enclosure.dec_le_dec qz114 qz114 411099 1000 411099 1000 qz117 qz117 rfl rfl rfl) (@List.IsChain.cons_cons RS151to168.d1 RS151to168.d62 (RS151to168.d2 qz114 qz127 qz282) (RS151to168.d2 qz127 qz140 qz284) qz313 (@Enclosure.dec_le_dec qz127 qz127 412601 1000 412601 1000 qz130 qz130 rfl rfl rfl) (@List.IsChain.cons_cons RS151to168.d1 RS151to168.d62 (RS151to168.d2 qz127 qz140 qz284) qz314 qz315 (@Enclosure.dec_le_dec qz140 qz140 414477 1000 414477 1000 qz143 qz143 rfl rfl rfl) (@List.IsChain.cons_cons RS151to168.d1 RS151to168.d62 qz314 qz305 Ns150p2282 (@Enclosure.dec_le_dec qz153 qz153 415227 1000 415227 1000 qz156 qz156 rfl rfl rfl) (Ns150p2286 (@Enclosure.dec_le_dec qz166 qz166 416351 1000 416351 1000 qz169 qz169 rfl rfl rfl) (Ns150p2287 Ns150p2289))))) 

noncomputable abbrev qz316 := (@List.cons RS151to168.d1 (RS151to168.d2 qz462 qz474 qz608) qz618)

noncomputable def Ns150p2291 := @List.IsChain.cons_cons RS151to168.d1 RS151to168.d62 (RS151to168.d2 qz88 qz101 qz278) (RS151to168.d2 qz101 qz114 qz280) qz316 (@Enclosure.dec_le_dec qz101 qz101 409595 1000 409595 1000 qz104 qz104 rfl rfl rfl) Ns150p2290 

noncomputable def Ns150p2292 := Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns150p2281 (@List.IsChain.cons_cons RS151to168.d1 RS151to168.d62 (RS151to168.d2 qz3 qz27 qz268) (RS151to168.d2 qz27 qz47 qz270) (@List.cons RS151to168.d1 (RS151to168.d2 qz47 qz62 qz272) (@List.cons RS151to168.d1 (RS151to168.d2 qz62 qz75 qz274) Ns150p2283)) (@Enclosure.dec_le_dec qz27 qz27 402058 1000 402058 1000 qz30 qz30 rfl rfl rfl) (@List.IsChain.cons_cons RS151to168.d1 RS151to168.d62 (RS151to168.d2 qz27 qz47 qz270) (RS151to168.d2 qz47 qz62 qz272) (@List.cons RS151to168.d1 (RS151to168.d2 qz62 qz75 qz274) Ns150p2283) (@Enclosure.dec_le_dec qz47 qz47 403568 1000 403568 1000 qz51 qz51 rfl rfl rfl) (@List.IsChain.cons_cons RS151to168.d1 RS151to168.d62 (RS151to168.d2 qz47 qz62 qz272) (RS151to168.d2 qz62 qz75 qz274) Ns150p2283 (@Enclosure.dec_le_dec qz62 qz62 405077 1000 405077 1000 qz65 qz65 rfl rfl rfl) (Ns150p2284 (@Enclosure.dec_le_dec qz75 qz75 406585 1000 406585 1000 qz78 qz78 rfl rfl rfl) (Ns150p2285 Ns150p2291))))) 

noncomputable abbrev qz627 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz628 := (Zeta.Certificates.CertifiedZeroIntervals.intervals Ns150p2292)

theorem RS151to168.d63 : Zeta.Certificates.BatchSpec 18 400547 1000 427552 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz627 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 18) (And (@Eq (Option Real) (@Option.map qz627 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz627 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz3)) (@Eq (Option Real) (@Option.map qz627 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz627 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz256)))) Ns150p2292 (@And.intro (@Eq Nat (@List.length qz627 qz628) 18) (And (@Eq (Option Real) (@Option.map qz627 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz627 qz628)) (@Option.some Real qz3)) (@Eq (Option Real) (@Option.map qz627 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz627 qz628)) (@Option.some Real qz256))) (@Eq.refl Nat 18) (@And.intro (@Eq (Option Real) (@Option.map qz627 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz627 qz628)) (@Option.some Real qz3)) (@Eq (Option Real) (@Option.map qz627 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz627 qz628)) (@Option.some Real qz256)) (@Eq.refl (Option Real) (@Option.some Real qz3)) (@Eq.refl (Option Real) (@Option.some Real qz256))))

theorem solution : Zeta.Certificates.BatchSpec 18 400547 1000 427552 1000 := RS151to168.d63
#print axioms solution
#check solution
