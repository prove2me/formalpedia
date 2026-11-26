-- Prove2me | solution 1 for RHHeight1000.rs_main_0205_0222
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T07:51:00.134872+00:00
-- url     : https://prove2.me/submissions/ee5667af-d7c2-414a-a753-8066de7d9e73

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

noncomputable def RS205to222.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS205to222.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS205to222.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS205to222.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS205to222.d2 a b h 

theorem RS205to222.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS205to222.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS205to222.d3 a b h)) 

noncomputable def Ns204p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns204p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns204p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns204p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns204p0 Ns204p1 Ns204p2 Ns204p1 153643044 134217728 1 40960000 153643044 134217728 1 40960000 76821522 67108864 2 67108864 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns204p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns204p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns204p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns204p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns204p8 := nat_lit 167537954069964697925743468333314178468718661948561187618563575975392713740913527107727581163208035826476740967700482432525301063254420572874757592895482956004842597348203117269212172556829666669574421653274845612596416189641484794702002223261246862056663160605878293700340502480877986491439034432953223334258717026053687371824342493299510132312376251152844516906794910572262907940062760396663270105627554083664899640691826599584783763757814813433640133591539937449421955686657622469485188711283992428713614179785896055117030632677201478317872225272595773536303110412989181984739022579128493081560758017763072115692678596043664844667144619713966763611484179303468167142547433165016751768184247559143333542643815355903304572487929375 

noncomputable def Ns204p9 := nat_lit 17907736863639440849562382641391758203535690054199171304015283257442503423240620144819838407313611418261944516207295868563739563278604805791797182761045687776939279949642059267526948014748996956777332184087524644234759874591635243045607722412471722018588244283882362848653445974523544951031470230725674276297342086185092985546835544820091590454230569790847977790484558207349923322458845585052164126500435851662252152223728079705692133047658564669873831757357628115566356048471439549797170528303905720944834637690907185213991407615774042056720704508980680095051114888612186461088301140868302968264130481206655302741383410655080008578156649725227045954510069588220729495895148666460653631514375880874422615237249871322129146554264800 

noncomputable def Ns204p10 := nat_lit 55164646516618494962085419356369025784335016154267579706247610053041231157772817011486486467101704279863254798704146668052276438579475100451766223896220272709675360577301802978530276301158911649961092601279696986330335403118086533522541958716560166657634553390183479955483588238249446822384543398154260439705049143284278540285021213103458182619368483938376641172730818250587232036579805400979202432024046862170503602539341971086573372247299262086029843105216008583038025403798224342134620653974939981235680083776396058604459065501719125356177784467570909658245422960948263734871602033841948787585406240093531041217463298165642337705122589129757920995868559518021463265498464182174549661735402095023640043996665674913376875 

noncomputable def Ns204p11 := BSN.log_dyadic_bound Ns204p6 Ns204p7 15 14 Ns204p8 134217728 40960000 Ns204p9 Ns204p10 153643044 Ns204p4 Ns204p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns204p6) (BSN.artanhQ Ns204p7) 0 14 Ns204p9 Ns204p8 Ns204p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns204p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns204p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns204p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns204p15 := nat_lit 167537954069966963268140139327979112712430526945422964221951926912223381190141639739514890494967825643602350173964944759828460064784215684919760383437959917620844610857567326816719640593037578236900835917107172977527392439886629774248115214831425484905681376157923696414882114961796820014026232307332015059110330001516939277521159573995394989771587717775443426002499543257897301982481613760098955890450106043861450716722534643739571053080256776912576113428445260435254713579381797931690799491102381747484553243404562568585572234105168360737285205910186933811836504830286397217473365026331067977496463917110493303316865058355012304571237619413071097245713770677768486493924969821719264401216877841676972336093778875903304572487929375 

noncomputable def Ns204p16 := nat_lit 17907736863639702486765313263906285882628955290251965205176678923530777959693011244026517850256414903756943142851250712732214241881959351517241344993825585048584379523049477943740273636414656012170312373198803997844271825165684859407921203335666024680974464565759223251918458072775203410604089667122984485578465112081892102496937045858735135721609691262763214794451343726045584198128451069547586972080574568545086657023793200560105564573365716615162566961587407171758966967827997201380802107846920231945878242774600967607639551032178207663699700360114112068650063802902647517702890145150192721997537569966984346993833704449560383184487996362781528900358997452380059737141488304159449328022742959995775545894292303322129146554264800 

noncomputable def Ns204p17 := nat_lit 55164646516619937449385584700664297411818070214438189962773666351465523500358685366424500506990751111492356556545320273548942244833046464529601272738875466881799996765940232256588350019911833156887888425998391295014189841212513610526066550079316346993943774342801096070086869790972589246312728227659319758310961510342377923950694747797317942483020440897997204711883064182772445608288320382376665481938194224815739627075458138172195220395246294556718284728034954178416253903237031389214179719385823921869528509431462690683227358218086518156757026652846493301460983550768858152506145788622699720737745394141184245149692548799188169247529408201840608223422296381897323845616153036586108326210125693898345963996665674913376875 

noncomputable def Ns204p18 := BSN.log_dyadic_bound Ns204p13 Ns204p14 15 14 Ns204p15 134217728 40960000 Ns204p16 Ns204p17 153643044 Ns204p12 Ns204p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base14 (BSN.artanhP Ns204p13) (BSN.artanhQ Ns204p14) 0 14 Ns204p16 Ns204p15 Ns204p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns204p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 76821522 67108864 2 67108864 38410761 33554432 1 33554432 (Ns204p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns204p0 Ns204p1 153643044 134217728 1 40960000 Bool.false (BSN.logfrac_isNear Ns204p4 Ns204p5 1 Ns204p0 Ns204p1 153643044 134217728 40960000 rfl rfl rfl (Ns204p11 rfl))) (BSN.isNear_log_sfrac Ns204p2 Ns204p1 153643044 134217728 1 40960000 Bool.false (BSN.logfrac_isNear Ns204p12 Ns204p5 1 Ns204p2 Ns204p1 153643044 134217728 40960000 rfl rfl rfl (Ns204p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS205to222.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 33554432 := Ns204p19 

noncomputable def Ns204p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 8388608 2560000 385100712855 135135 5814539 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz316 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz0 := qz316

theorem RS205to222.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 5814539 8388608 1 2560000 := BSN.isNear_log_sfrac 2 1 5814539 8388608 1 2560000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 5814539 8388608 2560000 rfl rfl rfl (Ns204p20 rfl)) 

theorem RS205to222.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 93032624 134217728 53 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 5814539 8388608 1 2560000 93032624 134217728 53 134217728 RS205to222.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz319 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def Ns204p21 := @Enclosure.Real.IsNear.inv_image qz317 23726567 16777216 1 16777216 5931641 5931642 8388608 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 23726567 16777216 1 16777216 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 23726567 16777216 1 16777216 23726567 16777216 1 16777216 (BSN.sqrt_enclosure 2 1 11863283 11863284 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS205to222.d8 : Enclosure.Real.IsNear qz320 Bool.false 11863283 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 11863283 16777216 1 16777216 11863283 16777216 1 16777216 (Ns204p21 rfl rfl) rfl 

theorem RS205to222.d9 : Enclosure.Real.IsNear qz320 Bool.false 94906264 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 11863283 16777216 1 16777216 94906264 134217728 8 134217728 RS205to222.d8 rfl 

noncomputable def Ns204p22 := BSN.log_dyadic_bound 1 2 12 11 1326382131865190400 8388608 2560000 130797573554866995 13749310575 9215827 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 1) (BSN.artanhQ 2) 0 11 130797573554866995 1326382131865190400 13749310575 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS205to222.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 9215827 8388608 1 2560000 := BSN.isNear_log_sfrac 3 1 9215827 8388608 1 2560000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 9215827 8388608 2560000 rfl rfl rfl (Ns204p22 rfl)) 

theorem RS205to222.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 147453232 134217728 53 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 9215827 8388608 1 2560000 147453232 134217728 53 134217728 RS205to222.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns204p23 := @Enclosure.Real.IsNear.inv_image qz321 29058991 16777216 1 16777216 4843164 4843166 8388608 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 29058991 16777216 1 16777216 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 29058991 16777216 1 16777216 29058991 16777216 1 16777216 (BSN.sqrt_enclosure 3 1 14529495 14529496 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS205to222.d12 : Enclosure.Real.IsNear qz323 Bool.false 4843165 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 9686330 16777216 2 16777216 4843165 8388608 1 8388608 (Ns204p23 rfl rfl) rfl 

theorem RS205to222.d13 : Enclosure.Real.IsNear qz323 Bool.false 77490640 134217728 16 134217728 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 4843165 8388608 1 8388608 77490640 134217728 16 134217728 RS205to222.d12 rfl 

noncomputable def Ns204p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns204p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns204p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns204p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns204p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns204p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns204p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns204p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns204p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns204p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns204p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns204p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns204p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns204p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns204p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns204p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns204p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns204p25 Ns204p26 Ns204p27 Ns204p28 200200021673987500790625 Ns204p29 Ns204p30 Ns204p31 Ns204p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns204p32 Ns204p33 151412625 Ns204p34 Ns204p35 1322214852783825 Ns204p27 Ns204p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns204p32 Ns204p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns204p34 Ns204p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns204p36 Ns204p37 1267389585 Ns204p38 Ns204p39 1927077560082675 Ns204p29 Ns204p30 Ns204p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns204p36 Ns204p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns204p38 Ns204p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS205to222.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns204p24 Ns204p25 1 Ns204p26 := Ns204p40 rfl rfl rfl 

noncomputable def Ns204p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns204p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns204p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns204p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns204p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns204p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns204p25 Ns204p26 Ns204p42 Ns204p43 9945 Ns204p44 Ns204p45 65835 Ns204p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns204p42 Ns204p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns204p44 Ns204p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS205to222.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns204p41 Ns204p25 1 Ns204p26 := Ns204p46 rfl 

noncomputable def Ns204p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns204p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS205to222.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns204p47 Ns204p25 1 Ns204p48 := BSN.pi_combine Ns204p24 Ns204p41 Ns204p25 Ns204p26 Ns204p48 Ns204p47 rfl rfl rfl rfl RS205to222.d14 RS205to222.d15 

theorem RS205to222.d17 : Enclosure.Real.IsNear Real.pi Bool.false 7074237752028440 2251799813685248 1 2251799813685248 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns204p47 Ns204p25 1 Ns204p48 7074237752028440 2251799813685248 1 2251799813685248 RS205to222.d16 rfl 

noncomputable def Ns204p49 := nat_lit 178719669545544893480837345123291015625 

noncomputable def Ns204p50 := nat_lit 27745388228251122714770036239987464375 

noncomputable def Ns204p51 := nat_lit 1274524447665412456340166714375 

noncomputable def Ns204p52 := BSN.log_dyadic_bound 3 5 16 15 Ns204p49 8388608 2560000 Ns204p50 Ns204p51 11629079 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP 3) (BSN.artanhQ 5) 0 15 Ns204p50 Ns204p49 Ns204p51 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS205to222.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 11629079 8388608 1 2560000 := BSN.isNear_log_sfrac 4 1 11629079 8388608 1 2560000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 11629079 8388608 2560000 rfl rfl rfl (Ns204p52 rfl)) 

theorem RS205to222.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 186065264 134217728 53 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 11629079 8388608 1 2560000 186065264 134217728 53 134217728 RS205to222.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns204p53 := @Enclosure.Real.IsNear.inv_image qz325 33554433 16777216 1 16777216 4194303 4194304 8388608 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 33554433 16777216 1 16777216 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 33554433 16777216 1 16777216 33554433 16777216 1 16777216 (BSN.sqrt_enclosure 4 1 16777216 16777217 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS205to222.d20 : Enclosure.Real.IsNear qz327 Bool.false 8388607 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 8388607 16777216 1 16777216 8388607 16777216 1 16777216 (Ns204p53 rfl rfl) rfl 

theorem RS205to222.d21 : Enclosure.Real.IsNear qz327 Bool.false 67108856 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 8388607 16777216 1 16777216 67108856 134217728 8 134217728 RS205to222.d20 rfl 

noncomputable def Ns204p54 := nat_lit 159424323765613091421820433543167414255940625 

noncomputable def Ns204p55 := nat_lit 33013339099500162583200499609923570567289500 

noncomputable def Ns204p56 := nat_lit 351657888879851162997374110924800000 

noncomputable def Ns204p57 := nat_lit 2289063575687431840984260 

noncomputable def Ns204p58 := nat_lit 3325435793429257756623375 

noncomputable def Ns204p59 := BSN.log_dyadic_bound 2 3 21 20 Ns204p54 8388608 2560000 Ns204p55 Ns204p56 13500943 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 20 10 9927050056596826020 47940881637414340575 686533194547200 Ns204p57 Ns204p58 512222703392784384000 Ns204p55 Ns204p54 Ns204p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 10 20 Ns204p57 Ns204p58 512222703392784384000 rfl rfl rfl rfl)) rfl rfl 

theorem RS205to222.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 13500943 8388608 1 2560000 := BSN.isNear_log_sfrac 5 1 13500943 8388608 1 2560000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 13500943 8388608 2560000 rfl rfl rfl (Ns204p59 rfl rfl)) 

theorem RS205to222.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 216015088 134217728 53 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 13500943 8388608 1 2560000 216015088 134217728 53 134217728 RS205to222.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns204p60 := @Enclosure.Real.IsNear.inv_image qz328 37514995 16777216 1 16777216 3751499 3751500 8388608 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 37514995 16777216 1 16777216 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 37514995 16777216 1 16777216 37514995 16777216 1 16777216 (BSN.sqrt_enclosure 5 1 18757497 18757498 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS205to222.d24 : Enclosure.Real.IsNear qz329 Bool.false 7502999 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 7502999 16777216 1 16777216 7502999 16777216 1 16777216 (Ns204p60 rfl rfl) rfl 

theorem RS205to222.d25 : Enclosure.Real.IsNear qz329 Bool.false 60023992 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 7502999 16777216 1 16777216 60023992 134217728 8 134217728 RS205to222.d24 rfl 

noncomputable def Ns204p61 := BSN.log_dyadic_bound 2 10 5 4 94500000000 8388608 2560000 1291130880 26880 3401287 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 10) 0 4 1291130880 94500000000 26880 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) (@Nat.cast Real Real.instNatCast 1))

theorem RS205to222.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683410914551 2251799813685248 195312501 500000000000000 := BSN.isNear_log_sfrac 6 1 4034683410914551 2251799813685248 195312501 500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 541526040612241437360128 302231454903657293676544 1000000005120000 2560000000000000000000 4034683410914551 2251799813685248 195312501 500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 3401287 8388608 24973259072661432 36028797018963968 2560000 1000000000000000 rfl rfl rfl rfl (Ns204p61 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS205to222.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 240485871 134217728 53 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683410914551 2251799813685248 195312501 500000000000000 240485871 134217728 53 134217728 RS205to222.d26 rfl 

noncomputable abbrev qz331 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns204p62 := @Enclosure.Real.IsNear.inv_image qz331 41095619 16777216 1 16777216 3424634 3424635 8388608 (@Enclosure.Real.IsNear.of_eq qz331 (Real.sqrt qz330) Bool.false 41095619 16777216 1 16777216 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 41095619 16777216 1 16777216 41095619 16777216 1 16777216 (BSN.sqrt_enclosure 6 1 20547809 20547810 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS205to222.d28 : Enclosure.Real.IsNear qz332 Bool.false 6849269 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 6849269 16777216 1 16777216 6849269 16777216 1 16777216 (Ns204p62 rfl rfl) rfl 

theorem RS205to222.d29 : Enclosure.Real.IsNear qz332 Bool.false 54794152 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 6849269 16777216 1 16777216 54794152 134217728 8 134217728 RS205to222.d28 rfl 

noncomputable def Ns204p63 := BSN.log_dyadic_bound 3 11 6 5 269619528727395 8388608 2560000 6999933372849 55801305 4694397 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 3) (BSN.artanhQ 11) 0 5 6999933372849 269619528727395 55801305 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) (@Nat.cast Real Real.instNatCast 1))

theorem RS205to222.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 195312501 500000000000000 := BSN.isNear_log_sfrac 7 1 4381799983422711 2251799813685248 195312501 500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 588115238325433934020608 302231454903657293676544 1000000005120000 2560000000000000000000 4381799983422711 2251799813685248 195312501 500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 4694397 8388608 24973259072661432 36028797018963968 2560000 1000000000000000 rfl rfl rfl rfl (Ns204p63 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS205to222.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 261175631 134217728 53 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381799983422711 2251799813685248 195312501 500000000000000 261175631 134217728 53 134217728 RS205to222.d30 rfl 

noncomputable abbrev qz334 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns204p64 := @Enclosure.Real.IsNear.inv_image qz334 44388341 16777216 1 16777216 3170595 3170596 8388608 (@Enclosure.Real.IsNear.of_eq qz334 (Real.sqrt qz333) Bool.false 44388341 16777216 1 16777216 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 44388341 16777216 1 16777216 44388341 16777216 1 16777216 (BSN.sqrt_enclosure 7 1 22194170 22194171 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz335 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS205to222.d32 : Enclosure.Real.IsNear qz335 Bool.false 6341191 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 6341191 16777216 1 16777216 6341191 16777216 1 16777216 (Ns204p64 rfl rfl) rfl 

theorem RS205to222.d33 : Enclosure.Real.IsNear qz335 Bool.false 50729528 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 6341191 16777216 1 16777216 50729528 134217728 8 134217728 RS205to222.d32 rfl 

noncomputable def Ns204p65 := BSN.log_dyadic_bound 0 16 1 0 1 8388608 2560000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz843 := (Enclosure.sfrac Bool.false 8 1)

noncomputable abbrev qz628 := qz843

noncomputable abbrev qz336 := qz628

noncomputable abbrev qz1 := qz336

noncomputable abbrev qz337 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) (@Nat.cast Real Real.instNatCast 1))

theorem RS205to222.d34 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 9364972152248037 4503599627370496 390625003 1000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 390625003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz337) Bool.false 628472642529000809299968 302231454903657293676544 1000000007680000 2560000000000000000000 9364972152248037 4503599627370496 390625003 1000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 8388608 24973259072661432 36028797018963968 2560000 1000000000000000 rfl rfl rfl rfl (Ns204p65 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS205to222.d35 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 279097919 134217728 53 134217728 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 9364972152248037 4503599627370496 390625003 1000000000000000 279097919 134217728 53 134217728 RS205to222.d34 rfl 

noncomputable abbrev qz338 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns204p66 := @Enclosure.Real.IsNear.inv_image qz338 47453133 16777216 1 16777216 2965820 2965821 8388608 (@Enclosure.Real.IsNear.of_eq qz338 (Real.sqrt qz337) Bool.false 47453133 16777216 1 16777216 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz337) Bool.false 47453133 16777216 1 16777216 47453133 16777216 1 16777216 (BSN.sqrt_enclosure 8 1 23726566 23726567 8388608 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz339 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS205to222.d36 : Enclosure.Real.IsNear qz339 Bool.false 5931641 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz339 Bool.false 5931641 16777216 1 16777216 5931641 16777216 1 16777216 (Ns204p66 rfl rfl) rfl 

theorem RS205to222.d37 : Enclosure.Real.IsNear qz339 Bool.false 47453128 134217728 8 134217728 := @Enclosure.Real.IsNear.recentre' qz339 Bool.false 5931641 16777216 1 16777216 47453128 134217728 8 134217728 RS205to222.d36 rfl 

theorem RS205to222.d38 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz844 := (@instHMul Real Real.instMul)

noncomputable abbrev qz629 := qz844

noncomputable abbrev qz340 := (@HMul.hMul Real Real Real qz629 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz2 := qz340

theorem RS205to222.d39 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS205to222.d38 rfl 

noncomputable abbrev qz3 := (@Inv.inv Real Real.instInv qz340)

theorem RS205to222.d40 : Enclosure.Real.IsNear qz3 Bool.false 2670177 16777216 1 16777216 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 2670177 16777216 1 16777216 2670177 16777216 1 16777216 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 1335088 1335089 8388608 RS205to222.d39 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns204p67 := nat_lit 24659003037143860329475735552 

noncomputable abbrev qz845 := (Enclosure.sfrac Bool.false 479682 1000)

noncomputable abbrev qz630 := qz845

noncomputable abbrev qz341 := qz630

noncomputable abbrev qz4 := qz341

noncomputable abbrev qz342 := qz629

noncomputable abbrev qz5 := qz342

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 8)

noncomputable abbrev qz7 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz846 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 479682 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz631 := qz846

noncomputable abbrev qz343 := qz631

noncomputable abbrev qz8 := qz343

noncomputable abbrev qz9 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz847 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 479682 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz632 := qz847

noncomputable abbrev qz344 := qz632

noncomputable abbrev qz10 := qz344

noncomputable abbrev qz633 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz8 qz9))

noncomputable def Ns204p68 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 8) (@HMul.hMul Real Real Real qz5 qz633 (Zeta.RiemannSiegel.correction qz10)) 323115497 67108864 93545 67108864 12178533069938342471 73786976294838206464 50448480389313081979 368934881474191032320000 Ns204p67 

noncomputable def Ns204p69 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos BSN.quadSignNeg 7 8 479682 1000 126 134217728 67108864 2251799813685248 Bool.false 107311926387 1759 279097919 53 47453128 8 

noncomputable def Ns204p70 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 479682 1000 38 85 134217728 67108864 2251799813685248 Bool.false 107311926387 1759 

noncomputable def Ns204p71 := Ns204p70 240485871 53 54794152 8 261175631 53 50729528 8 Bool.true 204483518 62533 Bool.true 33326048 Bool.true 48881941 7074237752028440 1 Bool.false 130101538 Bool.true Bool.false 47808461 Bool.true Bool.true 275667141 

noncomputable def Ns204p72 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 479682 1000 85 17 134217728 67108864 2251799813685248 Bool.false 107311926387 1759 

noncomputable def Ns204p73 := Ns204p72 186065264 53 67108856 8 216015088 53 60023992 8 Bool.true 103023422 36765 Bool.false 139327719 Bool.false 109288804 7074237752028440 1 Bool.false 115618752 Bool.true Bool.false 97605993 Bool.true Bool.true 204483518 

noncomputable def Ns204p74 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 479682 1000 297 173 134217728 67108864 2251799813685248 Bool.false 107311926387 1759 

noncomputable def Ns204p75 := Ns204p74 93032624 53 94906264 8 147453232 53 77490640 16 Bool.true 110888 1821 Bool.false 69723143 Bool.false 107897609 7074237752028440 1 Bool.false 66629301 Bool.true Bool.false 96645846 Bool.true Bool.true 103023422 

noncomputable def Ns204p76 := nat_lit 1370786603712998560979510171896213367482081027646763957 

noncomputable def Ns204p77 := nat_lit 1714477315961045426656670117327212157331593756672000 

noncomputable def Ns204p78 := nat_lit 12190163831546127657043510287360000 

noncomputable def Ns204p79 := nat_lit 35084430791469933046551048064304517120 

noncomputable abbrev qz11 := (@Eq.refl Real qz341)

noncomputable def Ns204p80 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 479682 1000 920380284496 16000000 959364 4000 2000 Ns204p78 Ns204p79 qz11 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns204p81 := nat_lit 252663386796379894759743314883910047894297175015851532554240 

noncomputable abbrev qz848 := (@instHSub Real Real.instSub)

noncomputable abbrev qz634 := qz848

noncomputable abbrev qz345 := qz634

noncomputable abbrev qz12 := qz345

noncomputable abbrev qz346 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz347 := (@HMul.hMul Real Real Real qz629 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz348 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz349 := (Enclosure.sfrac Bool.false 479682 2000)

noncomputable abbrev qz635 := (Real.log (Enclosure.sfrac Bool.false 920380284496 16000000))

noncomputable abbrev qz13 := (@HSub.hSub Real Real Real qz345 (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 479682 4000) qz635) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 959364)))))) qz349)

noncomputable abbrev qz350 := (@HSub.hSub Real Real Real qz12 qz13 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 479682 2000) (Real.log Real.pi)))

noncomputable def Ns204p82 := @Enclosure.Real.IsNear.addLit_ft_p qz350 (Enclosure.sfrac Bool.true Ns204p78 Ns204p79) 7201584603078254080377 9007199254740992000 2683078659437001 204800000000000000000 Ns204p78 Ns204p79 0 1 Ns204p81 

noncomputable def Ns204p83 := nat_lit 241645080856236267218732580864000 

noncomputable abbrev qz351 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 479682 2000) (Real.log Real.pi))

noncomputable def Ns204p84 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz351 9674539618907387539833 9007199254740992000 1190630242599 200000000000000000 9212475329001 33554432000 239841 33554432000 Ns204p83 7201584603078254080377 9007199254740992000 

noncomputable def Ns204p85 := nat_lit 3869815847562955015933200 

noncomputable abbrev qz14 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 479682 4000) qz635) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 959364))))))

noncomputable def Ns204p86 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz349 2366967059072744360421 1801439850948198400 1190630242599 200000000000000000 479682 2000 0 1 Ns204p85 9674539618907387539833 9007199254740992000 1190630242599 200000000000000000 

noncomputable def Ns204p87 := nat_lit 5329935982619125147488292328762769408 

noncomputable def Ns204p88 := nat_lit 26499541507204520985231360 

noncomputable def Ns204p89 := nat_lit 2417851639229258349412352 

noncomputable def Ns204p90 := nat_lit 11168259831851740602653958129328519518096189406056817696918290524487719530539100333003121943731970358013636558482812543500675724622018739888300658524160 

noncomputable def Ns204p91 := nat_lit 293189012733425944213184324096916368806279685894228445596732093666008011482099582792100386847335755089537362171821476855760857525305937710896279191552 

noncomputable def Ns204p92 := nat_lit 155017628176169014319640407138691354928714566023536023717242280492647240727283685502885310214737626497267614023852380598883764711207517626040320 

noncomputable def Ns204p93 := BSN.log_dyadic_bound 396092284496 1444668284496 7 6 Ns204p90 67108864 20480000 Ns204p91 Ns204p92 37765230 1840760568992 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 396092284496) (BSN.artanhQ 1444668284496) 0 6 Ns204p91 Ns204p90 Ns204p92 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz352 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns204p94 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 479682 4000) qz635 479682 4000 0 1 49359242445238905 4503599627370496 2441407 50000000000000 2367674013461708842821 1801439850948198400 585549496287 100000000000000000 (Enclosure.Real.IsNear.const Bool.false 479682 4000) (BSN.isNear_log_sfrac 920380284496 16000000 49359242445238905 4503599627370496 2441407 50000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 920380284496) qz352)) Bool.false Ns204p88 Ns204p89 1000000307200000 20480000000000000000000 49359242445238905 4503599627370496 2441407 50000000000000 (BSN.log_rat_reduce_isNear 920380284496 16000000 15 1840760568992 1048576000000 37765230 67108864 24973259072661432 36028797018963968 20480000 1000000000000000 rfl rfl rfl rfl (Ns204p93 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns204p95 := BSN.arctan_dyadic_bound_f 1000 959364 1 0 8388608 2560000 0 1 1 0 1 1 8743 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 959364) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 959364) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz15 := qz347

noncomputable abbrev qz16 := qz348

noncomputable abbrev qz353 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz17 := (@Enclosure.Real.IsNear.mulLit_ff qz353 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz354 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 959364)))

noncomputable def Ns204p96 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz354 884279719003555 562949953421312 1 2000000000000000 8743 8388608 1 2560000 7412954053628210970624 883692986205603 562949953421312 781250001 2000000000000000 qz17 (Ns204p95 rfl) rfl rfl 

noncomputable abbrev qz18 := qz346

noncomputable abbrev qz355 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns204p97 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 479682 4000) qz635) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz354)) 2367674013461708842821 1801439850948198400 585549496287 100000000000000000 883692986205603 2251799813685248 781250001 8000000000000000 Ns204p87 2366967059072744360421 1801439850948198400 1190630242599 200000000000000000 (Ns204p94 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz354) 1 4 0 1 883692986205603 562949953421312 781250001 2000000000000000 883692986205603 2251799813685248 781250001 8000000000000000 qz355 Ns204p96 rfl) 

noncomputable def Ns204p98 := @Ns204p82 Ns204p76 Ns204p77 2683078659437001 204800000000000000000 (@Ns204p84 2683078659437001 204800000000000000000 (Ns204p86 (Ns204p97 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 479682 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz349 (Real.log Real.pi) 479682 2000 0 1 38410761 33554432 1 33554432 9212475329001 33554432000 239841 33554432000 (Enclosure.Real.IsNear.const Bool.false 479682 2000) RS205to222.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns204p78 Ns204p79) 

noncomputable abbrev qz356 := (@instHAdd Real Real.instAdd)

noncomputable def Ns204p99 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns204p76 Ns204p77 2683078659437001 204800000000000000000 6706995399 8388608 221 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz356 qz350 (Enclosure.sfrac Bool.true Ns204p78 Ns204p79)) Bool.false Ns204p76 Ns204p77 2683078659437001 204800000000000000000 Ns204p80 (Ns204p98 rfl rfl)) 

noncomputable def Ns204p100 := nat_lit 1208925819614629174706176 

noncomputable abbrev qz357 := (BSN.sinEvenQ 34359738368)

noncomputable abbrev qz358 := (BSN.sinOddQ 34359738368)

noncomputable def Ns204p101 := BSN.sin_dyadic_bound_f 28387897 34359738368 1 0 16777216 5125001 0 1 1 0 1 1 13861 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 28387897) qz357 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 28387897) qz358 0 0 rfl) rfl rfl 

noncomputable abbrev qz359 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable abbrev qz360 := (@Nat.cast Real Real.instNatCast Ns204p100)

noncomputable def Ns204p102 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6706995399) qz359) Bool.false 6706995399 8388608 221 16777216 Bool.true 13861 16777216 1 2560000 (Ns204p99 rfl) (Enclosure.sfrac_false_div 6706995399 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6706995399) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 998810336865359495168) qz360) 226375608064910080 72057594037927936 Bool.false 13861 16777216 127 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q1 6706995399 8388608 226375608064910080 72057594037927936 127 998810336865359495168 Ns204p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 13861 16777216 998810336865359495168 Ns204p100 28387897 34359738368 5125001 5120000 (Ns204p101 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p103 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns204p76 Ns204p77 2683078659437001 204800000000000000000 107311926387 134217728 1759 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz356 qz350 (Enclosure.sfrac Bool.true Ns204p78 Ns204p79)) Bool.false Ns204p76 Ns204p77 2683078659437001 204800000000000000000 Ns204p80 (Ns204p98 rfl rfl)) 

noncomputable def Ns204p104 := Ns204p75 36765 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 297 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66629301 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 173 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 96645846 134217728) qz11 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 13861 16777216 142221 10485760000 110888 134217728 1821 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 13861 16777216 142221 10485760000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 13861 16777216 582537216 42949672960000 13861 16777216 142221 10485760000 (Ns204p102 rfl rfl) rfl)) rfl) (Ns204p103 rfl) RS205to222.d7 

noncomputable def Ns204p105 := nat_lit 23192074715632226108332944603867987738309879706879304872995852375745 

noncomputable def Ns204p106 := nat_lit 38215724400686031908940493885850326479880652218951261491964367528263680 

noncomputable def Ns204p107 := nat_lit 558490318608356492557736598832569717325697307923410467956971201 

noncomputable def Ns204p108 := nat_lit 60740243842330464373217380484208524677935919531899636764707683030721 

noncomputable def Ns204p109 := nat_lit 700621614012577251663909054573922652131145290680773127352680071351500800 

noncomputable abbrev qz361 := (BSN.sinEvenQ 134217728)

noncomputable abbrev qz362 := (BSN.sinOddQ 134217728)

noncomputable def Ns204p110 := BSN.sin_dyadic_bound_f 69723143 134217728 3 2 134217728 67108864 Ns204p105 Ns204p106 Ns204p107 Ns204p108 Ns204p109 Ns204p107 66629301 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 69723143) qz361 0 2 Ns204p105 Ns204p106 Ns204p107 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 69723143) qz362 0 2 Ns204p108 Ns204p109 Ns204p107 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p111 := nat_lit 133023563699405584460125514069668597302757761665164565331436988215105 

noncomputable def Ns204p112 := nat_lit 18369382902471836715640607003961907993388328917887466212639321921 

noncomputable def Ns204p113 := nat_lit 348365306878505862040884356818744673656185794685754424732276410232641 

noncomputable def Ns204p114 := BSN.sin_dyadic_bound_f 107897609 134217728 3 2 134217728 67108864 Ns204p111 Ns204p106 Ns204p112 Ns204p113 Ns204p109 Ns204p112 96645846 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 107897609) qz361 0 2 Ns204p111 Ns204p106 Ns204p112 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 107897609) qz362 0 2 Ns204p113 Ns204p109 Ns204p112 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p115 := nat_lit 369945852860445487325177922782589343278442994096390802420760922646465 

noncomputable def Ns204p116 := nat_lit 142003882017759844699214474879259618198068350762532394184324245441 

noncomputable def Ns204p117 := nat_lit 968675894063614188960238688614119954918839540541693715797123034343361 

noncomputable def Ns204p118 := BSN.sin_dyadic_bound_f 139327719 134217728 3 2 134217728 67108864 Ns204p115 Ns204p106 Ns204p116 Ns204p117 Ns204p109 Ns204p116 115618752 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 139327719) qz361 0 2 Ns204p115 Ns204p106 Ns204p116 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 139327719) qz362 0 2 Ns204p117 Ns204p109 Ns204p116 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p119 := nat_lit 140019054753510824627495964828910080750224032835439392429221204787200 

noncomputable def Ns204p120 := nat_lit 20351919977469972266857666730331106932816628381559034091772379136 

noncomputable def Ns204p121 := nat_lit 366683621245898160735962138329582056363171716218294932211811714400256 

noncomputable def Ns204p122 := BSN.sin_dyadic_bound_f 109288804 134217728 3 2 134217728 67108864 Ns204p119 Ns204p106 Ns204p120 Ns204p121 Ns204p109 Ns204p120 97605993 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 109288804) qz361 0 2 Ns204p119 Ns204p106 Ns204p120 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 109288804) qz362 0 2 Ns204p121 Ns204p109 Ns204p120 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p123 := Ns204p73 62533 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 85 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 115618752 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 17 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 97605993 134217728) qz11 rfl rfl (Ns204p104 RS205to222.d9 RS205to222.d11 RS205to222.d13 RS205to222.d17 (Ns204p110 rfl rfl) (Ns204p114 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns204p103 rfl) RS205to222.d19 RS205to222.d21 RS205to222.d23 RS205to222.d25 RS205to222.d17 (Ns204p118 rfl rfl) (Ns204p122 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns204p124 := nat_lit 1233488946381583668477785276416 

noncomputable def Ns204p125 := nat_lit 7788445287802241442795744493830144 

noncomputable def Ns204p126 := nat_lit 116826679317033621641936167407452160 

noncomputable abbrev qz363 := (BSN.cosEvenQ 134217728)

noncomputable abbrev qz364 := (BSN.cosOddQ 134217728)

noncomputable def Ns204p127 := BSN.cos_dyadic_bound_f 33326048 134217728 2 1 134217728 67108864 Ns204p124 Ns204p125 Ns204p124 Ns204p124 Ns204p126 Ns204p124 130101538 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 33326048) qz363 0 1 Ns204p124 Ns204p125 Ns204p124 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 33326048) qz364 0 1 Ns204p124 Ns204p126 Ns204p124 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p128 := nat_lit 5709443374295992134507331005361 

noncomputable def Ns204p129 := nat_lit 38942226439011207213978722469150720 

noncomputable def Ns204p130 := nat_lit 272595585073078450497851057284055040 

noncomputable def Ns204p131 := BSN.sin_dyadic_bound_f 48881941 134217728 2 1 134217728 67108864 Ns204p128 Ns204p129 Ns204p128 Ns204p128 Ns204p130 Ns204p128 47808461 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 48881941) qz361 0 1 Ns204p128 Ns204p129 Ns204p128 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 48881941) qz362 0 1 Ns204p128 Ns204p130 Ns204p128 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p132 := Ns204p71 83924 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 38 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 130101538 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 85 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 47808461 134217728) qz11 rfl rfl (Ns204p123 rfl rfl) (Ns204p103 rfl) RS205to222.d27 RS205to222.d29 RS205to222.d31 RS205to222.d33 RS205to222.d17 (Ns204p127 rfl rfl) (Ns204p131 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns204p133 := BSN.cos_dyadic_bound_f 1903613 134217728 1 0 134217728 67108864 0 1 1 0 1 1 134204228 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 1903613) qz363 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 1903613) qz364 0 0 rfl) rfl rfl 

noncomputable def Ns204p134 := Ns204p69 Bool.true 275667141 83924 Bool.true 1903613 7074237752028440 1 Bool.false 134204228 Bool.true Bool.true 323115497 93545 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 126 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 134204228 134217728) qz11 rfl (Ns204p132 rfl) (Ns204p103 rfl) RS205to222.d35 RS205to222.d37 RS205to222.d17 (Ns204p133 rfl rfl) rfl 

noncomputable def Ns204p135 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 8) 323115497 134217728 93545 134217728 323115497 134217728 93545 134217728 86735655777861632 323115497 67108864 93545 67108864 (Ns204p134 rfl rfl rfl rfl) 

noncomputable def Ns204p136 := @Enclosure.Real.IsNear.mulLit_ff qz633 (Zeta.RiemannSiegel.correction qz10) 354737 1048576 1 8388608 34331161028983 70368744177664 4442288022933 10995116277760000 12178533069938342471 73786976294838206464 

noncomputable abbrev qz636 := (@HPow.hPow Real Real Real qz7 qz8 qz9)

noncomputable def Ns204p137 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz636 1 1 0 1 354737 1048576 1 8388608 354737 1048576 1 8388608 

noncomputable abbrev qz365 := (@Enclosure.Real.IsNear.of_eq qz8 (@HMul.hMul Real Real Real qz5 qz4 qz3) Bool.false 640417921857 8388608000 239841 8388608000 (BSN.t_div_two_pi_mk qz4 479682 1000 qz11) (@Enclosure.Real.IsNear.mulLit_ff qz4 qz3 479682 1000 0 1 2670177 16777216 1 16777216 640417921857 8388608000 239841 8388608000 (Enclosure.Real.IsNear.const Bool.false 479682 1000) RS205to222.d40 rfl))

noncomputable def Ns204p138 := @Enclosure.Real.IsNear.sqrt_image qz8 640417921857 8388608000 239841 8388608000 73295381 73295409 8388608 qz365 

noncomputable abbrev qz849 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 479682 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz637 := qz849

noncomputable abbrev qz366 := qz637

noncomputable abbrev qz19 := qz366

noncomputable def Ns204p139 := @Enclosure.Real.IsNear.sqrt_image qz19 73295395 8388608 7 4194304 24796092 24796098 8388608 (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 146590790 16777216 28 16777216 73295395 8388608 7 4194304 (Ns204p138 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz638 := (Real.sqrt qz849)

noncomputable abbrev qz367 := qz638

noncomputable abbrev qz20 := qz367

noncomputable def Ns204p140 := @Enclosure.Real.IsNear.inv_image qz20 24796095 8388608 3 8388608 2837895 2837897 8388608 (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 49592190 16777216 6 16777216 24796095 8388608 3 8388608 (Ns204p139 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns204p141 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz20) Bool.false 5675792 16777216 2 16777216 354737 1048576 1 8388608 (Ns204p140 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz21 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz344))

noncomputable abbrev qz639 := (@HMul.hMul Real Real Real qz844 qz847 qz847)

noncomputable abbrev qz640 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz368 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz639 qz632) qz640)

noncomputable abbrev qz22 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz368))

noncomputable def Ns204p142 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz10) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz21) qz22) Bool.false 34331161028983 

noncomputable def Ns204p143 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz21) qz22 106848469 8388608 7445 

noncomputable abbrev qz641 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz21))

noncomputable def Ns204p144 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz21) (@Neg.neg Real Real.instNeg qz641) Bool.true 106848469 8388608 7445 4194304 (BSN.inv_eq_neg_inv_neg qz21) 

noncomputable def Ns204p145 := @Enclosure.Real.IsNear.recentre' qz641 Bool.false 213696938 16777216 29780 16777216 106848469 8388608 

noncomputable def Ns204p146 := @Enclosure.Real.IsNear.recentre' qz21 Bool.true 1317169 16777216 469897216 42949672960000 1317169 16777216 114721 10485760000 

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz342 qz340 qz344)

noncomputable abbrev qz369 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable def Ns204p147 := @Enclosure.Real.IsNear.cos_image qz23 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 77742241) qz369) Bool.false 77742241 16777216 177 16777216 Bool.true 1317169 16777216 1 

noncomputable def Ns204p148 := nat_lit 37780505577975853301374589 

noncomputable def Ns204p149 := nat_lit 3602879701896396800000000000000 

noncomputable def Ns204p150 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz10 884279719003555 140737488355328 1 500000000000000 6186531 8388608 7 4194304 5470623894286782117705 1180591620717411303424 Ns204p148 

noncomputable def Ns204p151 := @Enclosure.Real.IsNear.subLit_ff_p qz19 qz1 73295395 8388608 7 4194304 8 1 0 1 6186531 6186531 8388608 7 

noncomputable abbrev qz370 := (Enclosure.Real.IsNear.const Bool.false 8 1)

noncomputable def Ns204p152 := @Ns204p151 4194304 (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 146590790 16777216 28 16777216 73295395 8388608 7 4194304 (Ns204p138 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns204p153 := @Enclosure.Real.IsNear.recentre' qz23 Bool.false 5470623894286782117705 1180591620717411303424 Ns204p148 Ns204p149 77742241 16777216 177 16777216 (@Ns204p150 Ns204p149 RS205to222.d39 (Ns204p152 rfl rfl) rfl) 

noncomputable def Ns204p154 := nat_lit 3607932735880836616814592 

noncomputable def Ns204p155 := nat_lit 268732004664613096023469637660920973304390298245053250621540622450533481084453758506762599277550747881307548457942225610988059314377041 

noncomputable def Ns204p156 := nat_lit 1296985566167364170939292694987530979374979352933922598450371085822004482258776525817524027815363891144507173707470555812298386676121600 

noncomputable def Ns204p157 := nat_lit 330022522948073978271199661820135066440807581406656697338309082028569819794537974009259991095257833082724415400732721441643188561 

noncomputable def Ns204p158 := nat_lit 1627107636531951176189230222340064988005147739026803785969095446687465418648162777829695872208516218988052674868155615665790289255354705 

noncomputable def Ns204p159 := nat_lit 118025686521230139555475635243865319123123121116986956458983768809802407885548663849394686531198114094150152807379820578919153187527065600 

noncomputable abbrev qz642 := (BSN.cosEvenQ 34359738368)

noncomputable abbrev qz643 := (BSN.cosOddQ 34359738368)

noncomputable def Ns204p160 := BSN.cos_dyadic_bound_f 51271807931 34359738368 4 3 16777216 5125001 Ns204p155 Ns204p156 Ns204p157 Ns204p158 Ns204p159 Ns204p157 1317169 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 51271807931) qz642 0 3 Ns204p155 Ns204p156 Ns204p157 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 51271807931) qz643 0 3 Ns204p158 Ns204p159 Ns204p157 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz371 := (@Nat.cast Real Real.instNatCast Ns204p89)

noncomputable def Ns204p161 := @Ns204p147 2560000 (Ns204p153 rfl) (Enclosure.sfrac_false_div 77742241 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 77742241) qz369) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns204p154) qz371) 226375608064910080 72057594037927936 Bool.false 1317169 16777216 0 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q2 77742241 16777216 226375608064910080 72057594037927936 0 Ns204p154 Ns204p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1317169 16777216 Ns204p154 Ns204p89 51271807931 34359738368 5125001 5120000 (Ns204p160 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p162 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz21) 1317169 16777216 114721 10485760000 106833579 106863359 8388608 (@Enclosure.Real.IsNear.neg qz21 Bool.true 1317169 16777216 114721 10485760000 (Ns204p146 (Ns204p161 rfl rfl) rfl)) 

noncomputable def Ns204p163 := Ns204p144 (@Enclosure.Real.IsNear.neg qz641 Bool.false 106848469 8388608 7445 4194304 (@Ns204p145 7445 4194304 (Ns204p162 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns204p164 := @Enclosure.Real.IsNear.recentre' qz22 Bool.true 321307 8388608 

noncomputable abbrev qz24 := (@HMul.hMul Real Real Real qz342 qz340 qz368)

noncomputable abbrev qz372 := (@Nat.cast Real Real.instNatCast 2097152)

noncomputable def Ns204p165 := @Enclosure.Real.IsNear.cos_image qz24 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 3374545)) qz372) Bool.true 3374545 2097152 

noncomputable def Ns204p166 := nat_lit 15935838386262964860532448005 

noncomputable def Ns204p167 := nat_lit 9903520314283042199192993792 

noncomputable def Ns204p168 := nat_lit 980483647594150809212409714443333 

noncomputable def Ns204p169 := @Enclosure.Real.IsNear.recentre' qz24 Bool.true Ns204p166 Ns204p167 Ns204p168 

noncomputable def Ns204p170 := nat_lit 37778931862957161709568000000000000000 

noncomputable abbrev qz25 := qz368

noncomputable def Ns204p171 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz25 884279719003555 140737488355328 1 500000000000000 18021264135991 

noncomputable abbrev qz373 := (@HSub.hSub Real Real Real qz634 qz639 qz632)

noncomputable abbrev qz26 := qz373

noncomputable abbrev qz374 := qz640

noncomputable abbrev qz27 := qz374

noncomputable def Ns204p172 := @Enclosure.Real.IsNear.subLit_tf qz26 qz27 13623217624887 70368744177664 36332947 8796093022208 1 16 

noncomputable abbrev qz375 := qz639

noncomputable abbrev qz28 := qz375

noncomputable def Ns204p173 := @Enclosure.Real.IsNear.subLit_ff_n qz28 qz10 38273165813961 70368744177664 21652883 8796093022208 6186531 8388608 7 4194304 

noncomputable def Ns204p174 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz10 6186531 8388608 7 4194304 6186531 8388608 7 4194304 38273165813961 70368744177664 

noncomputable def Ns204p175 := nat_lit 972201944920285458819641803111353943630919659033630775113892170541234956662571890625 

noncomputable def Ns204p176 := nat_lit 3466537250751077332112698720796095110148055492926080949987665366995300109908547993600 

noncomputable def Ns204p177 := nat_lit 2180633535272882464318257824634016809420804333906106652902951893448652587890625 

noncomputable def Ns204p178 := nat_lit 5882385603957497757937239170681308148556396671517382340327563675407510727004357490625 

noncomputable def Ns204p179 := nat_lit 315454889818348037222255583592444655023473049856273366448877548396572310001677867417600 

noncomputable def Ns204p180 := BSN.cos_dyadic_bound_t 3374545 2097152 4 3 8388608 2560000 Ns204p175 Ns204p176 Ns204p177 Ns204p178 Ns204p179 Ns204p177 321307 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 3374545) (BSN.cosEvenQ 2097152) 0 3 Ns204p175 Ns204p176 Ns204p177 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 3374545) (BSN.cosOddQ 2097152) 0 3 Ns204p178 Ns204p179 Ns204p177 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz376 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns204p181 := @Ns204p164 283234304 10737418240000 321307 8388608 69149 2621440000 (@Ns204p165 109 4194304 Bool.true 321307 8388608 1 2560000 (@Ns204p169 Ns204p170 3374545 2097152 109 4194304 (@Ns204p171 70368744177664 36332947 8796093022208 Ns204p166 Ns204p167 Ns204p168 Ns204p170 RS205to222.d39 (@Ns204p172 0 1 288340226175856 18021264135991 70368744177664 36332947 8796093022208 (@Ns204p173 114279832353868087296 13623217624887 70368744177664 36332947 8796093022208 (@Ns204p174 21652883 8796093022208 (Ns204p152 rfl rfl) (Ns204p152 rfl rfl) rfl) (Ns204p152 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 3374545 2097152) (BSN.cos_neg_of_bound 3374545 2097152 Bool.true 321307 8388608 1 2560000 (Ns204p180 rfl rfl)) rfl rfl) 

noncomputable abbrev qz29 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 8) (Enclosure.sfrac Bool.false 1 1) Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 8 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1))

noncomputable def Ns204p182 := @Ns204p136 50448480389313081979 368934881474191032320000 (Ns204p137 qz29 (@Enclosure.Real.IsNear.of_eq qz636 (@Inv.inv Real Real.instInv qz20) Bool.false 354737 1048576 1 8388608 (BSN.rpow_neg_quarter_mk qz8 (BSN.t_div_two_pi_nonneg qz4 479682 1000 qz11)) Ns204p141) rfl) (@Ns204p142 70368744177664 4442288022933 10995116277760000 (BSN.correction_mk qz10 (BSN.cos_two_pi_p_ne_zero_mk qz4 479682 1000 8 qz11 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 479682 1000 8 qz11 rfl rfl rfl))) (@Ns204p143 4194304 321307 8388608 69149 2621440000 34331161028983 70368744177664 4442288022933 10995116277760000 Ns204p163 (Ns204p181 rfl) rfl)) 

noncomputable def Ns204p183 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 367447779136059587143 73786976294838206464 564717556490842681979 368934881474191032320000 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 8) (@HMul.hMul Real Real Real qz5 qz633 (Zeta.RiemannSiegel.correction qz10))) Bool.true 367447779136059587143 73786976294838206464 564717556490842681979 368934881474191032320000 (BSN.hardyZApproximantRS₀_eq qz4 8 (@BSN.floor_sqrt_eq_dec qz4 479682 1000 8 qz11 rfl rfl rfl)) (@Ns204p68 367447779136059587143 73786976294838206464 564717556490842681979 368934881474191032320000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 8)) Bool.true 323115497 67108864 93545 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 8) (Ns204p135 (Ns204p134 rfl rfl rfl rfl) rfl rfl)) (Ns204p182 rfl) rfl rfl)) 

theorem RS205to222.d41 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 367447779136059587143 73786976294838206464 564717556490842681979 368934881474191032320000 := Ns204p183 

theorem RS205to222.d42 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS205to222.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS205to222.d3 a b h)) 

noncomputable def Ns204p184 := nat_lit 8224879818764274913855406080 

noncomputable abbrev qz850 := (Enclosure.sfrac Bool.false 481854 1000)

noncomputable abbrev qz644 := qz850

noncomputable abbrev qz377 := qz644

noncomputable abbrev qz30 := qz377

noncomputable abbrev qz851 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 481854 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz645 := qz851

noncomputable abbrev qz378 := qz645

noncomputable abbrev qz31 := qz378

noncomputable abbrev qz852 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 481854 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz646 := qz852

noncomputable abbrev qz379 := qz646

noncomputable abbrev qz32 := qz379

noncomputable abbrev qz647 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz31 qz9))

noncomputable def Ns204p185 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz30) qz30 8) (@HMul.hMul Real Real Real qz5 qz647 (Zeta.RiemannSiegel.correction qz32)) 18472945 67108864 93967 67108864 202419225248833367775 1180591620717411303424 177491489478583925169 737869762948382064640000 Ns204p184 

noncomputable def Ns204p186 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz30) qz30 Real.sin BSN.quadSignNeg 7 8 481854 1000 125 134217728 67108864 2251799813685248 Bool.false 107944163234 1767 279097919 53 47453128 8 

noncomputable def Ns204p187 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz30) qz30 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 481854 1000 37 84 134217728 67108864 2251799813685248 Bool.false 107944163234 1767 

noncomputable def Ns204p188 := Ns204p187 240485871 53 54794152 8 261175631 53 50729528 8 Bool.false 105212931 62815 Bool.true 134253227 Bool.true 194747278 7074237752028440 1 Bool.false 112959499 Bool.true Bool.false 16042986 Bool.false Bool.false 65161091 

noncomputable def Ns204p189 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz30) qz30 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 481854 1000 86 18 134217728 67108864 2251799813685248 Bool.false 107944163234 1767 

noncomputable def Ns204p190 := Ns204p189 186065264 53 67108856 8 216015088 53 60023992 8 Bool.false 185424441 36931 Bool.false 156602099 Bool.false 61512166 7074237752028440 1 Bool.false 52763355 Bool.true Bool.false 120367172 Bool.true Bool.false 105212931 

noncomputable def Ns204p191 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz30) qz30 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 481854 1000 299 174 134217728 67108864 2251799813685248 Bool.false 107944163234 1767 

noncomputable def Ns204p192 := Ns204p191 93032624 53 94906264 8 147453232 53 77490640 16 Bool.false 134217656 1829 Bool.false 78235703 Bool.false 209037322 7074237752028440 1 Bool.false 73879953 Bool.false Bool.false 1791338 Bool.true Bool.false 185424441 

noncomputable def Ns204p193 := nat_lit 1416750228699486320709240479365332724768002971823986571 

noncomputable def Ns204p194 := nat_lit 1761586649453934126086040040916435014163458162688000 

noncomputable def Ns204p195 := nat_lit 12468659485109196370868097131520000 

noncomputable def Ns204p196 := nat_lit 36048458798826248163946639506884628480 

noncomputable abbrev qz380 := (@Eq.refl Real qz644)

noncomputable abbrev qz33 := qz380

noncomputable def Ns204p197 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz30 481854 1000 928734109264 16000000 963708 4000 2000 Ns204p195 Ns204p196 qz33 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns204p198 := nat_lit 261135402153889318633127205156618127829238307766597204766720 

noncomputable abbrev qz381 := (Enclosure.sfrac Bool.false 481854 2000)

noncomputable abbrev qz648 := (Real.log (Enclosure.sfrac Bool.false 928734109264 16000000))

noncomputable abbrev qz34 := (@HSub.hSub Real Real Real qz345 (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 481854 4000) qz648) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 963708)))))) qz381)

noncomputable abbrev qz382 := (@HSub.hSub Real Real Real qz12 qz34 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 481854 2000) (Real.log Real.pi)))

noncomputable def Ns204p199 := @Enclosure.Real.IsNear.addLit_ft_p qz382 (Enclosure.sfrac Bool.true Ns204p195 Ns204p196) 7244013285530321047239 9007199254740992000 2695137079073847 204800000000000000000 Ns204p195 Ns204p196 0 1 Ns204p198 

noncomputable def Ns204p200 := nat_lit 243068751196423741517749813248000 

noncomputable abbrev qz383 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 481854 2000) (Real.log Real.pi))

noncomputable def Ns204p201 := @Enclosure.Real.IsNear.subLit_ff_p qz34 qz383 9728165841176209936071 9007199254740992000 1195932978603 200000000000000000 9254189415447 33554432000 240927 33554432000 Ns204p200 7244013285530321047239 9007199254740992000 

noncomputable def Ns204p202 := nat_lit 3891266336470483974428400 

noncomputable abbrev qz35 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 481854 4000) qz648) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 963708))))))

noncomputable def Ns204p203 := @Enclosure.Real.IsNear.subLit_ff_p qz35 qz381 2379648667204638583131 1801439850948198400 1195932978603 200000000000000000 481854 2000 0 1 Ns204p202 9728165841176209936071 9007199254740992000 1195932978603 200000000000000000 

noncomputable def Ns204p204 := nat_lit 5358492425447753884131614934316351488 

noncomputable def Ns204p205 := nat_lit 26521388108708925071687680 

noncomputable def Ns204p206 := nat_lit 11968356504042001616459516985855786263438336409010785377185659679193486510641572366160322883399507377653500143547077471051693322582078410092847258664960 

noncomputable def Ns204p207 := nat_lit 324308755338428175175817012469527759644260934311201279101777065491732398403588951895838384292641936887864264249548478589832333415325544620797892493312 

noncomputable def Ns204p208 := nat_lit 199137218373531848394667178344880515023267733483817337832025724058059530615850489778715042369934458493789234896772763165593408727495284275281920 

noncomputable def Ns204p209 := BSN.log_dyadic_bound 404446109264 1453022109264 7 6 Ns204p206 67108864 20480000 Ns204p207 Ns204p208 38371595 1857468218528 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 404446109264) (BSN.artanhQ 1453022109264) 0 6 Ns204p207 Ns204p206 Ns204p208 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns204p210 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 481854 4000) qz648 481854 4000 0 1 49399934911558265 4503599627370496 2441407 50000000000000 2380355623687399622331 1801439850948198400 588200864289 100000000000000000 (Enclosure.Real.IsNear.const Bool.false 481854 4000) (BSN.isNear_log_sfrac 928734109264 16000000 49399934911558265 4503599627370496 2441407 50000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 928734109264) qz352)) Bool.false Ns204p205 Ns204p89 1000000307200000 20480000000000000000000 49399934911558265 4503599627370496 2441407 50000000000000 (BSN.log_rat_reduce_isNear 928734109264 16000000 15 1857468218528 1048576000000 38371595 67108864 24973259072661432 36028797018963968 20480000 1000000000000000 rfl rfl rfl rfl (Ns204p209 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns204p211 := BSN.arctan_dyadic_bound_f 1000 963708 1 0 8388608 2560000 0 1 1 0 1 1 8704 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 963708) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 963708) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz384 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 963708)))

noncomputable def Ns204p212 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz384 884279719003555 562949953421312 1 2000000000000000 8704 8388608 1 2560000 7412976008676394401792 883695603451299 562949953421312 781250001 2000000000000000 qz17 (Ns204p211 rfl) rfl rfl 

noncomputable def Ns204p213 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 481854 4000) qz648) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz384)) 2380355623687399622331 1801439850948198400 588200864289 100000000000000000 883695603451299 2251799813685248 781250001 8000000000000000 Ns204p204 2379648667204638583131 1801439850948198400 1195932978603 200000000000000000 (Ns204p210 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz384) 1 4 0 1 883695603451299 562949953421312 781250001 2000000000000000 883695603451299 2251799813685248 781250001 8000000000000000 qz355 Ns204p212 rfl) 

noncomputable def Ns204p214 := @Ns204p199 Ns204p193 Ns204p194 2695137079073847 204800000000000000000 (@Ns204p201 2695137079073847 204800000000000000000 (Ns204p203 (Ns204p213 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 481854 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz381 (Real.log Real.pi) 481854 2000 0 1 38410761 33554432 1 33554432 9254189415447 33554432000 240927 33554432000 (Enclosure.Real.IsNear.const Bool.false 481854 2000) RS205to222.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns204p195 Ns204p196) 

noncomputable def Ns204p215 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz30) Bool.false Ns204p193 Ns204p194 2695137079073847 204800000000000000000 3373255101 4194304 111 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz30) (@HAdd.hAdd Real Real Real qz356 qz382 (Enclosure.sfrac Bool.true Ns204p195 Ns204p196)) Bool.false Ns204p193 Ns204p194 2695137079073847 204800000000000000000 Ns204p197 (Ns204p214 rfl rfl)) 

noncomputable def Ns204p216 := nat_lit 854884511937168966943486283111476191067070019395526442533665896408428908956264986694648939207076961111217364125358827887154473673424896 

noncomputable def Ns204p217 := nat_lit 16860812360175734222210805034837902731874731588140993779854824115686058269364094835627812361599730584878593258197117225559879026789580800 

noncomputable def Ns204p218 := nat_lit 606197761374524093686096695387694850592409941964565932691281015488254006722890984799243704782542083104047431065126517337275498496 

noncomputable def Ns204p219 := nat_lit 4269124974409880009043824985175207855657840838933647572761869625685014923111096230234366557588019947710638774816912625641056661202272256 

noncomputable def Ns204p220 := nat_lit 590128432606150697777378176219326595615615605584934782294918844049012039427743319246973432655990570470750764036899102894595765937635328000 

noncomputable def Ns204p221 := BSN.sin_dyadic_bound_f 53936719348 34359738368 4 3 16777216 5125001 Ns204p216 Ns204p217 Ns204p218 Ns204p219 Ns204p220 Ns204p218 16777207 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53936719348) qz357 0 3 Ns204p216 Ns204p217 Ns204p218 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53936719348) qz358 0 3 Ns204p219 Ns204p220 Ns204p218 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz385 := (@Nat.cast Real Real.instNatCast 4194304)

noncomputable abbrev qz386 := (@Nat.cast Real Real.instNatCast 604462909807314587353088)

noncomputable def Ns204p222 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz30) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3373255101) qz385) Bool.false 3373255101 4194304 111 8388608 Bool.false 16777207 16777216 1 2560000 (Ns204p215 rfl) (Enclosure.sfrac_false_div 3373255101 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3373255101) qz385) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 948864801412960382615552) qz386) 226375608064910080 72057594037927936 Bool.false 16777207 16777216 127 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q3 3373255101 4194304 226375608064910080 72057594037927936 127 948864801412960382615552 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777207 16777216 948864801412960382615552 604462909807314587353088 53936719348 34359738368 5125001 5120000 (Ns204p221 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p223 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz30) Bool.false Ns204p193 Ns204p194 2695137079073847 204800000000000000000 107944163234 134217728 1767 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz30) (@HAdd.hAdd Real Real Real qz356 qz382 (Enclosure.sfrac Bool.true Ns204p195 Ns204p196)) Bool.false Ns204p193 Ns204p194 2695137079073847 204800000000000000000 Ns204p197 (Ns204p214 rfl rfl)) 

noncomputable def Ns204p224 := Ns204p192 36931 BSN.abs_quadSignPos (BSN.cos_quad_nat3 299 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 73879953 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 174 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 1791338 134217728) qz33 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 1) Bool.false 16777207 16777216 71423 5242880000 134217656 134217728 1829 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz30)) Bool.false 16777207 16777216 71423 5242880000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz30) qz30) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz30)) Bool.false 16777207 16777216 292548608 21474836480000 16777207 16777216 71423 5242880000 (Ns204p222 rfl rfl) rfl)) rfl) (Ns204p223 rfl) RS205to222.d7 

noncomputable def Ns204p225 := nat_lit 36766971253021146428334314577639973189915250648284519085828704789825 

noncomputable def Ns204p226 := nat_lit 1403588866767720466014378344470278317293144611650327475605693761 

noncomputable def Ns204p227 := nat_lit 96292176042604426241073467281261263618216705654231068504114674754881 

noncomputable def Ns204p228 := BSN.sin_dyadic_bound_f 78235703 134217728 3 2 134217728 67108864 Ns204p225 Ns204p106 Ns204p226 Ns204p227 Ns204p109 Ns204p226 73879953 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 78235703) qz361 0 2 Ns204p225 Ns204p106 Ns204p226 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 78235703) qz362 0 2 Ns204p227 Ns204p109 Ns204p226 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p229 := nat_lit 4027348541798751135212719415765274212393137203761362759945071043529391314847898939630097531148014945898496 

noncomputable def Ns204p230 := nat_lit 16370259324565974446773555668639125346849261288577159159185037526614652227207809159774062022111344040345600 

noncomputable def Ns204p231 := nat_lit 6961230198469186621775579575854823123510996898048272814005597049501406807591022844883015920244822016 

noncomputable def Ns204p232 := nat_lit 24375699150404515386561783459312777095316698176139314448513609125201844236378528829222925023398283218063360 

noncomputable def Ns204p233 := nat_lit 1489693598535503674656393565846160406563282777260521483485838414921933352675910633539439644012132307671449600 

noncomputable def Ns204p234 := BSN.cos_dyadic_bound_f 209037322 134217728 4 3 134217728 67108864 Ns204p229 Ns204p230 Ns204p231 Ns204p232 Ns204p233 Ns204p231 1791338 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 209037322) qz363 0 3 Ns204p229 Ns204p230 Ns204p231 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 209037322) qz364 0 3 Ns204p232 Ns204p233 Ns204p231 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p235 := nat_lit 1265534564298998545508451097751402754351667540478576363223279239055465338840420380991736538033618148994481 

noncomputable def Ns204p236 := nat_lit 217555939955470228836108138611125428734588986527923881457243499002130335160842329564935260011834801 

noncomputable def Ns204p237 := nat_lit 7671935041832657126685784375173160460819186355085035570083933389249030709459012841646593595771712192720305 

noncomputable def Ns204p238 := BSN.cos_dyadic_bound_f 156602099 134217728 4 3 134217728 67108864 Ns204p235 Ns204p230 Ns204p236 Ns204p237 Ns204p233 Ns204p236 52763355 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 156602099) qz363 0 3 Ns204p235 Ns204p230 Ns204p236 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 156602099) qz364 0 3 Ns204p237 Ns204p233 Ns204p236 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p239 := nat_lit 7805564153212884806602281448025344339464319031726676391022444421376 

noncomputable def Ns204p240 := nat_lit 4246191600076225767660054876205591831097850246550140165773818614251520 

noncomputable def Ns204p241 := nat_lit 204968989131182958531458846060312713627027583610503661628170496 

noncomputable def Ns204p242 := nat_lit 23416282521660392053889781426383912392965703040012808165744076923136 

noncomputable def Ns204p243 := nat_lit 191078622003430159544702469429251632399403261094756307459821837641318400 

noncomputable def Ns204p244 := BSN.cos_dyadic_bound_f 61512166 134217728 3 2 134217728 67108864 Ns204p239 Ns204p240 Ns204p241 Ns204p242 Ns204p243 Ns204p241 120367172 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 61512166) qz363 0 2 Ns204p239 Ns204p240 Ns204p241 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 61512166) qz364 0 2 Ns204p242 Ns204p243 Ns204p241 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p245 := Ns204p190 62815 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 86 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 52763355 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 18 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 120367172 134217728) qz33 rfl rfl (Ns204p224 RS205to222.d9 RS205to222.d11 RS205to222.d13 RS205to222.d17 (Ns204p228 rfl rfl) (Ns204p234 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns204p223 rfl) RS205to222.d19 RS205to222.d21 RS205to222.d23 RS205to222.d25 RS205to222.d17 (Ns204p238 rfl rfl) (Ns204p244 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns204p246 := nat_lit 318906959247061412731742300724161085479944370413707870304869936204385 

noncomputable def Ns204p247 := nat_lit 105535328888624506667880510385184098449927282277682055854755613281 

noncomputable def Ns204p248 := nat_lit 835061645590769736524719933451226830573792516436023413184227847637601 

noncomputable def Ns204p249 := BSN.sin_dyadic_bound_f 134253227 134217728 3 2 134217728 67108864 Ns204p246 Ns204p106 Ns204p247 Ns204p248 Ns204p109 Ns204p247 112959499 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 134253227) qz361 0 2 Ns204p246 Ns204p106 Ns204p247 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 134253227) qz362 0 2 Ns204p248 Ns204p109 Ns204p247 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p250 := nat_lit 3031343282030404143969125239951624872683792364923715609607148957999951499770673277716358297380428188880896 

noncomputable def Ns204p251 := nat_lit 2976163283631831496908260847429298313429649984692767612439591304325399774055957505421368304885436416 

noncomputable def Ns204p252 := nat_lit 18357872556618416279302962731236455005688469433185384993077402365569314922827039937066351666579553876316160 

noncomputable def Ns204p253 := BSN.cos_dyadic_bound_f 194747278 134217728 4 3 134217728 67108864 Ns204p250 Ns204p230 Ns204p251 Ns204p252 Ns204p233 Ns204p251 16042986 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 194747278) qz363 0 3 Ns204p250 Ns204p230 Ns204p251 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 194747278) qz364 0 3 Ns204p252 Ns204p233 Ns204p251 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p254 := Ns204p188 84303 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 37 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 112959499 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 84 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 16042986 134217728) qz33 rfl rfl (Ns204p245 rfl rfl) (Ns204p223 rfl) RS205to222.d27 RS205to222.d29 RS205to222.d31 RS205to222.d33 RS205to222.d17 (Ns204p249 rfl rfl) (Ns204p253 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns204p255 := nat_lit 6647481315720782591897553466581906226920134131171268311873942916077062102837980407264137904061266294677121 

noncomputable def Ns204p256 := nat_lit 212813371219357667808056223692308629509040396751503069069405487845990478953701519077062806287447472524492800 

noncomputable def Ns204p257 := nat_lit 1793183163907099342168474147386055221481306366885996497130178481469409473418875323488495609241083521 

noncomputable def Ns204p258 := nat_lit 33211993999334571641574644603893265095063505649636925116846302263700355515373525816993386818305987957694081 

noncomputable def Ns204p259 := nat_lit 7448467992677518373281967829230802032816413886302607417429192074609666763379553167697198220060661538357248000 

noncomputable def Ns204p260 := BSN.sin_dyadic_bound_f 186696161 134217728 4 3 134217728 67108864 Ns204p255 Ns204p256 Ns204p257 Ns204p258 Ns204p259 Ns204p257 132054031 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 186696161) qz361 0 3 Ns204p255 Ns204p256 Ns204p257 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 186696161) qz362 0 3 Ns204p258 Ns204p259 Ns204p257 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz387 := (BSN.cos_quad_nat1 125 rfl)

noncomputable def Ns204p261 := Ns204p186 Bool.false 65161091 84303 Bool.true 186696161 7074237752028440 1 Bool.false 132054031 Bool.true Bool.false 18472945 93967 BSN.abs_quadSignNeg qz387 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132054031 134217728) qz33 rfl (Ns204p254 rfl) (Ns204p223 rfl) RS205to222.d35 RS205to222.d37 RS205to222.d17 (Ns204p260 rfl rfl) rfl 

noncomputable def Ns204p262 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 8) 18472945 134217728 93967 134217728 18472945 134217728 93967 134217728 4958793414737920 18472945 67108864 93967 67108864 (Ns204p261 rfl rfl rfl rfl) 

noncomputable def Ns204p263 := @Enclosure.Real.IsNear.mulLit_ff qz647 (Zeta.RiemannSiegel.correction qz32) 2834693 8388608 1 8388608 71407812150675 140737488355328 62598241501901 87960930222080000 202419225248833367775 1180591620717411303424 

noncomputable abbrev qz649 := (@HPow.hPow Real Real Real qz7 qz31 qz9)

noncomputable def Ns204p264 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz649 1 1 0 1 2834693 8388608 1 8388608 2834693 8388608 1 8388608 

noncomputable def Ns204p265 := @Enclosure.Real.IsNear.sqrt_image qz31 643317734079 8388608000 240927 8388608000 73461134 73461162 8388608 (@Enclosure.Real.IsNear.of_eq qz31 (@HMul.hMul Real Real Real qz5 qz30 qz3) Bool.false 643317734079 8388608000 240927 8388608000 (BSN.t_div_two_pi_mk qz30 481854 1000 qz33) (@Enclosure.Real.IsNear.mulLit_ff qz30 qz3 481854 1000 0 1 2670177 16777216 1 16777216 643317734079 8388608000 240927 8388608000 (Enclosure.Real.IsNear.const Bool.false 481854 1000) RS205to222.d40 rfl)) 

noncomputable abbrev qz853 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 481854 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz650 := qz853

noncomputable abbrev qz388 := qz650

noncomputable abbrev qz36 := qz388

noncomputable def Ns204p266 := @Enclosure.Real.IsNear.sqrt_image qz36 18365287 2097152 7 4194304 24824114 24824120 8388608 (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 146922296 16777216 28 16777216 18365287 2097152 7 4194304 (Ns204p265 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns204p267 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz36) 24824117 8388608 3 8388608 2834692 2834694 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz36) Bool.false 49648234 16777216 6 16777216 24824117 8388608 3 8388608 (Ns204p266 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns204p268 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz36)) Bool.false 5669386 16777216 2 16777216 2834693 8388608 1 8388608 (Ns204p267 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz342 qz340 qz379)

noncomputable abbrev qz651 := (@HMul.hMul Real Real Real qz844 qz852 qz852)

noncomputable abbrev qz389 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz651 qz646) qz640)

noncomputable abbrev qz38 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz389))

noncomputable def Ns204p269 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz32) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz37)) qz38) Bool.false 71407812150675 

noncomputable def Ns204p270 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz37)) qz38 368364425 16777216 88487 

noncomputable def Ns204p271 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz37)) Bool.false 368364425 16777216 88487 16777216 368364425 16777216 88487 

noncomputable def Ns204p272 := @Enclosure.Real.IsNear.recentre' (Real.cos qz37) Bool.false 764121 16777216 469897216 42949672960000 764121 16777216 114721 10485760000 

noncomputable def Ns204p273 := @Enclosure.Real.IsNear.cos_image qz37 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 39912577) qz359) Bool.false 39912577 8388608 177 16777216 Bool.false 764121 16777216 1 

noncomputable def Ns204p274 := nat_lit 188902527890591170221086833 

noncomputable def Ns204p275 := nat_lit 18014398509481984000000000000000 

noncomputable def Ns204p276 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz32 884279719003555 140737488355328 1 500000000000000 1588071 2097152 7 4194304 1404298977637694592405 295147905179352825856 Ns204p274 

noncomputable def Ns204p277 := @Enclosure.Real.IsNear.subLit_ff_p qz36 qz1 18365287 2097152 7 4194304 8 1 0 1 1588071 1588071 2097152 7 

noncomputable def Ns204p278 := @Ns204p277 4194304 (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 146922296 16777216 28 16777216 18365287 2097152 7 4194304 (Ns204p265 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns204p279 := @Enclosure.Real.IsNear.recentre' qz37 Bool.false 1404298977637694592405 295147905179352825856 Ns204p274 Ns204p275 39912577 8388608 177 16777216 (@Ns204p276 Ns204p275 RS205to222.d39 (Ns204p278 rfl rfl) rfl) 

noncomputable def Ns204p280 := BSN.sin_dyadic_bound_f 1565462937 34359738368 1 0 16777216 5125001 0 1 1 0 1 1 764121 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 1565462937) qz357 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 1565462937) qz358 0 0 rfl) rfl rfl 

noncomputable def Ns204p281 := @Ns204p273 2560000 (Ns204p279 rfl) (Enclosure.sfrac_false_div 39912577 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 39912577) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 55079830492571682996224) qz360) 226375608064910080 72057594037927936 Bool.false 764121 16777216 0 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q3 39912577 8388608 226375608064910080 72057594037927936 0 55079830492571682996224 Ns204p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 764121 16777216 55079830492571682996224 Ns204p100 1565462937 34359738368 5125001 5120000 (Ns204p280 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p282 := @Enclosure.Real.IsNear.inv_image (Real.cos qz37) 764121 16777216 114721 10485760000 184137969 184226456 8388608 (Ns204p272 (Ns204p281 rfl rfl) rfl) rfl 

noncomputable def Ns204p283 := @Enclosure.Real.IsNear.recentre' qz38 Bool.false 193851 8388608 

noncomputable abbrev qz39 := (@HMul.hMul Real Real Real qz342 qz340 qz389)

noncomputable def Ns204p284 := @Enclosure.Real.IsNear.cos_image qz39 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 6491463)) qz385) Bool.true 6491463 4194304 

noncomputable def Ns204p285 := nat_lit 957970886147500860491315725 

noncomputable def Ns204p286 := nat_lit 618970019642690137449562112 

noncomputable def Ns204p287 := nat_lit 398455691177550257640021108531863 

noncomputable def Ns204p288 := @Enclosure.Real.IsNear.recentre' qz39 Bool.true Ns204p285 Ns204p286 Ns204p287 

noncomputable def Ns204p289 := nat_lit 15111572745182864683827200000000000000 

noncomputable abbrev qz40 := qz389

noncomputable def Ns204p290 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz40 884279719003555 140737488355328 1 500000000000000 1083334679695 

noncomputable abbrev qz390 := (@HSub.hSub Real Real Real qz634 qz651 qz646)

noncomputable abbrev qz41 := qz390

noncomputable def Ns204p291 := @Enclosure.Real.IsNear.subLit_tf qz41 qz27 808456772751 4398046511104 73826165 17592186044416 1 16 

noncomputable abbrev qz391 := qz651

noncomputable abbrev qz42 := qz391

noncomputable def Ns204p292 := @Enclosure.Real.IsNear.subLit_ff_n qz42 qz32 2521969501041 4398046511104 44466037 17592186044416 1588071 2097152 7 4194304 

noncomputable def Ns204p293 := @Enclosure.Real.IsNear.mulLit_ff qz32 qz32 1588071 2097152 7 4194304 1588071 2097152 7 4194304 2521969501041 4398046511104 

noncomputable def Ns204p294 := nat_lit 3406094640382425484142561250410945358962256193076896420030620432562464143531770048950561 

noncomputable def Ns204p295 := nat_lit 14198936579076412752333613960380805571166435299025227571149477343212749250185412581785600 

noncomputable def Ns204p296 := nat_lit 5599007285284944433560411863190641978094369977771140959699039433363118069544661281 

noncomputable def Ns204p297 := nat_lit 20616725107153554644221219071442729804443317324388338948038981300624849542455991298175265 

noncomputable def Ns204p298 := nat_lit 1292103228695953560462358870394653306976145612211295708974602438232360181766872544942489600 

noncomputable def Ns204p299 := BSN.cos_dyadic_bound_f 6491463 4194304 4 3 8388608 2560000 Ns204p294 Ns204p295 Ns204p296 Ns204p297 Ns204p298 Ns204p296 193851 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 6491463) (BSN.cosEvenQ 4194304) 0 3 Ns204p294 Ns204p295 Ns204p296 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 6491463) (BSN.cosOddQ 4194304) 0 3 Ns204p297 Ns204p298 Ns204p296 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p300 := @Ns204p283 288354304 10737418240000 193851 8388608 70399 2621440000 (@Ns204p284 111 4194304 Bool.false 193851 8388608 1 2560000 (@Ns204p288 Ns204p289 6491463 4194304 111 4194304 (@Ns204p290 4398046511104 73826165 17592186044416 Ns204p285 Ns204p286 Ns204p287 Ns204p289 RS205to222.d39 (@Ns204p291 0 1 17333354875120 1083334679695 4398046511104 73826165 17592186044416 (@Ns204p292 1695456737888305152 808456772751 4398046511104 73826165 17592186044416 (@Ns204p293 44466037 17592186044416 (Ns204p278 rfl rfl) (Ns204p278 rfl rfl) rfl) (Ns204p278 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 6491463 4194304) (BSN.cos_neg_of_bound 6491463 4194304 Bool.false 193851 8388608 1 2560000 (Ns204p299 rfl rfl)) rfl rfl) 

noncomputable def Ns204p301 := @Ns204p263 177491489478583925169 737869762948382064640000 (Ns204p264 qz29 (@Enclosure.Real.IsNear.of_eq qz649 (@Inv.inv Real Real.instInv (Real.sqrt qz36)) Bool.false 2834693 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz31 (BSN.t_div_two_pi_nonneg qz30 481854 1000 qz33)) Ns204p268) rfl) (@Ns204p269 140737488355328 62598241501901 87960930222080000 (BSN.correction_mk qz32 (BSN.cos_two_pi_p_ne_zero_mk qz30 481854 1000 8 qz33 rfl rfl (@BSN.floor_sqrt_eq_dec qz30 481854 1000 8 qz33 rfl rfl rfl))) (@Ns204p270 16777216 193851 8388608 70399 2621440000 71407812150675 140737488355328 62598241501901 87960930222080000 (@Ns204p271 16777216 (Ns204p282 rfl rfl rfl rfl rfl) rfl) (Ns204p300 rfl) rfl)) 

noncomputable def Ns204p302 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz30) (hardyZApproximantRS₀ qz30) Bool.false 122560259979430957345 1180591620717411303424 1210669580750857845169 737869762948382064640000 (@Eq.refl Real (hardyZApproximantRS₀ qz30)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz30) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz30) qz30 8) (@HMul.hMul Real Real Real qz5 qz647 (Zeta.RiemannSiegel.correction qz32))) Bool.false 122560259979430957345 1180591620717411303424 1210669580750857845169 737869762948382064640000 (BSN.hardyZApproximantRS₀_eq qz30 8 (@BSN.floor_sqrt_eq_dec qz30 481854 1000 8 qz33 rfl rfl rfl)) (@Ns204p185 122560259979430957345 1180591620717411303424 1210669580750857845169 737869762948382064640000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz30) qz30 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz30) qz30 8)) Bool.false 18472945 67108864 93967 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz30) qz30 8) (Ns204p262 (Ns204p261 rfl rfl rfl rfl) rfl rfl)) (Ns204p301 rfl) rfl rfl)) 

theorem RS205to222.d43 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz30) Bool.false 122560259979430957345 1180591620717411303424 1210669580750857845169 737869762948382064640000 := Ns204p302 

noncomputable abbrev qz652 := (@HMul.hMul Real Real Real qz844 (Real.sqrt qz849) qz846)

noncomputable abbrev qz392 := qz652

noncomputable abbrev qz43 := qz392

noncomputable abbrev qz393 := (@HMul.hMul Real Real Real qz629 (@HMul.hMul Real Real Real qz629 qz652 qz652) qz652)

noncomputable abbrev qz44 := (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz393))

noncomputable abbrev qz45 := (@HMul.hMul Real Real Real qz342 (@HMul.hMul Real Real Real qz342 qz367 qz367) qz367)

noncomputable abbrev qz394 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz43))

noncomputable def Ns204p303 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz356 (@HAdd.hAdd Real Real Real qz356 qz394 qz44) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz45))) Bool.false 

noncomputable def Ns204p304 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz356 qz394 qz44) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz45)) 14869001 536870912 

noncomputable def Ns204p305 := @Enclosure.Real.IsNear.addLit_ff qz394 qz44 1858625 67108864 25 67108864 

noncomputable def Ns204p306 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz43) 25 4 0 1 74345 16777216 1 16777216 1858625 

noncomputable def Ns204p307 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz43) Bool.false 74345 16777216 1 16777216 74345 16777216 1 16777216 

noncomputable def Ns204p308 := @Enclosure.Real.IsNear.mulLit_ff qz20 qz8 24796095 8388608 3 8388608 640417921857 8388608000 239841 8388608000 3175972726013749683 14073748835532800 7868374705989 

noncomputable def Ns204p309 := @Enclosure.Real.IsNear.sqrt_image qz8 640417921857 8388608000 239841 8388608000 73295381 73295409 8388608 qz365 

noncomputable def Ns204p310 := @Enclosure.Real.IsNear.sqrt_image qz19 73295395 8388608 7 4194304 24796092 24796098 8388608 (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 146590790 16777216 28 16777216 73295395 8388608 7 4194304 (Ns204p309 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz395 := (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 49592190 16777216 6 16777216 24796095 8388608 3 8388608 (Ns204p310 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns204p311 := @Ns204p308 70368744177664000 qz395 

noncomputable def Ns204p312 := Ns204p311 qz365 

noncomputable def Ns204p313 := @Enclosure.Real.IsNear.inv_image qz43 3175972726013749683 14073748835532800 7868374705989 70368744177664000 37172 37173 8388608 (Ns204p312 rfl) rfl rfl 

noncomputable abbrev qz46 := (@Inv.inv Real Real.instInv qz393)

noncomputable def Ns204p314 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz46 1 32 0 1 1 

noncomputable def Ns204p315 := @Enclosure.Real.IsNear.recentre' qz46 Bool.false 1 16777216 1 16777216 

noncomputable def Ns204p316 := nat_lit 32035410446953382344937857909483468182684369749639394987 

noncomputable def Ns204p317 := nat_lit 2787593149816327892691964784081045188247552000000 

noncomputable def Ns204p318 := nat_lit 5952508724877400005952262783096755977557340097757889 

noncomputable def Ns204p319 := nat_lit 348449143727040986586495598010130648530944000000000 

noncomputable abbrev qz47 := qz393

noncomputable def Ns204p320 := @Enclosure.Real.IsNear.inv_image qz47 Ns204p316 Ns204p317 Ns204p318 Ns204p319 0 1 

noncomputable def Ns204p321 := nat_lit 10086802756383208312398480769782600489 

noncomputable def Ns204p322 := nat_lit 198070406285660843983859875840000 

noncomputable def Ns204p323 := nat_lit 249897496554095718986947861982991 

noncomputable def Ns204p324 := nat_lit 4951760157141521099596496896000000 

noncomputable abbrev qz396 := (@HMul.hMul Real Real Real qz629 qz652 qz652)

noncomputable abbrev qz48 := qz396

noncomputable def Ns204p325 := @Enclosure.Real.IsNear.mulLit_ff qz48 qz43 Ns204p321 Ns204p322 Ns204p323 Ns204p324 3175972726013749683 14073748835532800 7868374705989 

noncomputable def Ns204p326 := @Enclosure.Real.IsNear.mulLit_ff qz43 qz43 3175972726013749683 14073748835532800 7868374705989 70368744177664000 3175972726013749683 14073748835532800 7868374705989 70368744177664000 Ns204p321 

noncomputable def Ns204p327 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz45) 13 10 0 1 649591 16777216 1 

noncomputable def Ns204p328 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz45) Bool.false 649591 16777216 1 16777216 649591 16777216 

noncomputable def Ns204p329 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz20 qz20) qz20 614846327249025 70368744177664 148776579 70368744177664 24796095 8388608 3 8388608 15245787940867912557375 

noncomputable def Ns204p330 := @Enclosure.Real.IsNear.mulLit_ff qz20 qz20 24796095 8388608 3 8388608 24796095 8388608 3 8388608 614846327249025 70368744177664 148776579 

noncomputable def Ns204p331 := @Ns204p330 70368744177664 qz395 

noncomputable def Ns204p332 := Ns204p331 qz395 

noncomputable def Ns204p333 := @Ns204p329 590295810358705651712 5533617614735817 590295810358705651712 (Ns204p332 rfl) qz395 

noncomputable def Ns204p334 := @Enclosure.Real.IsNear.inv_image qz45 15245787940867912557375 590295810358705651712 5533617614735817 590295810358705651712 324795 324796 8388608 (Ns204p333 rfl) 

noncomputable def Ns204p335 := @Ns204p304 201 536870912 8444683 167772160 13 167772160 7028309078573056 209459933 2684354560 1213 2684354560 (@Ns204p305 1 536870912 1 536870912 997841765924864 14869001 536870912 201 536870912 (@Ns204p306 67108864 25 67108864 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns204p307 (Ns204p313 rfl rfl rfl rfl) rfl) rfl) (@Ns204p314 16777216 1 16777216 1 536870912 1 536870912 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns204p315 1 16777216 1 16777216 (@Ns204p320 8388608 (@Ns204p325 70368744177664000 Ns204p316 Ns204p317 Ns204p318 Ns204p319 (@Ns204p326 Ns204p322 Ns204p323 Ns204p324 (Ns204p312 rfl) (Ns204p312 rfl) rfl) (Ns204p312 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns204p327 16777216 8444683 167772160 13 167772160 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns204p328 1 16777216 (Ns204p334 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS205to222.d44 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 := @Ns204p303 209459933 2684354560 1213 2684354560 (BSN.hardyZErrorBoundRS₀_mk qz4 479682 1000 qz11 rfl rfl) (Ns204p335 rfl rfl) 

noncomputable def Ns204p336 := nat_lit 1847314799410876915419971584 

noncomputable abbrev qz854 := (Enclosure.sfrac Bool.false 483302 1000)

noncomputable abbrev qz653 := qz854

noncomputable abbrev qz397 := qz653

noncomputable abbrev qz49 := qz397

noncomputable abbrev qz855 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 483302 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz654 := qz855

noncomputable abbrev qz398 := qz654

noncomputable abbrev qz50 := qz398

noncomputable abbrev qz856 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 483302 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz655 := qz856

noncomputable abbrev qz399 := qz655

noncomputable abbrev qz51 := qz399

noncomputable abbrev qz656 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz50 qz9))

noncomputable def Ns204p337 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz49) qz49 8) (@HMul.hMul Real Real Real qz5 qz656 (Zeta.RiemannSiegel.correction qz51)) 1195483 2097152 94243 67108864 207871240091688107571 1180591620717411303424 63982505166173004061 737869762948382064640000 Ns204p336 

noncomputable def Ns204p338 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz49) qz49 Real.sin BSN.quadSignNeg 7 8 483302 1000 125 134217728 67108864 2251799813685248 Bool.false 108366019721 1772 279097919 53 47453128 8 

noncomputable def Ns204p339 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz49) qz49 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 483302 1000 37 84 134217728 67108864 2251799813685248 Bool.false 108366019721 1772 

noncomputable def Ns204p340 := Ns204p339 240485871 53 54794152 8 261175631 53 50729528 8 Bool.false 8977485 62998 Bool.true 60620282 Bool.true 151073105 7074237752028440 1 Bool.false 58580178 Bool.true Bool.false 57801000 Bool.false Bool.false 6908952 

noncomputable def Ns204p341 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz49) qz49 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 483302 1000 87 18 134217728 67108864 2251799813685248 Bool.false 108366019721 1772 

noncomputable def Ns204p342 := Ns204p341 186065264 53 67108856 8 216015088 53 60023992 8 Bool.true 18128698 37036 Bool.false 98207369 Bool.false 170578806 7074237752028440 1 Bool.false 89675815 Bool.false Bool.false 39649328 Bool.true Bool.false 8977485 

noncomputable def Ns204p343 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz49) qz49 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 483302 1000 300 175 134217728 67108864 2251799813685248 Bool.false 108366019721 1772 

noncomputable def Ns204p344 := Ns204p343 93032624 53 94906264 8 147453232 53 77490640 16 Bool.true 134217712 1829 Bool.false 154552236 Bool.false 206552815 7074237752028440 1 Bool.false 54641953 Bool.false Bool.false 134149623 Bool.false Bool.true 18128698 

noncomputable def Ns204p345 := nat_lit 2606624596036211377895739643623547966321115932589075843 

noncomputable def Ns204p346 := nat_lit 3228458809592509516318945340606639904931924515225600 

noncomputable def Ns204p347 := nat_lit 12657133960889479569079166735360000 

noncomputable def Ns204p348 := nat_lit 36703327277706529415797210056173752320 

noncomputable abbrev qz400 := (@Eq.refl Real qz653)

noncomputable abbrev qz52 := qz400

noncomputable def Ns204p349 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz49 483302 1000 934324292816 16000000 966604 4000 2000 Ns204p347 Ns204p348 qz52 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns204p350 := nat_lit 53383671726821609019304747901410262350256454299424273264640 

noncomputable abbrev qz401 := (Enclosure.sfrac Bool.false 483302 2000)

noncomputable abbrev qz657 := (Real.log (Enclosure.sfrac Bool.false 934324292816 16000000))

noncomputable abbrev qz53 := (@HSub.hSub Real Real Real qz345 (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 483302 4000) qz657) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 966604)))))) qz401)

noncomputable abbrev qz402 := (@HSub.hSub Real Real Real qz12 qz53 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 483302 2000) (Real.log Real.pi)))

noncomputable def Ns204p351 := @Enclosure.Real.IsNear.addLit_ft_p qz402 (Enclosure.sfrac Bool.true Ns204p347 Ns204p348) 1454464717162364496127 1801439850948198400 2703176025498411 204800000000000000000 Ns204p347 Ns204p348 0 1 Ns204p350 

noncomputable def Ns204p352 := nat_lit 244018687242118962222538424320000 

noncomputable abbrev qz403 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 483302 2000) (Real.log Real.pi))

noncomputable def Ns204p353 := @Enclosure.Real.IsNear.subLit_ff_p qz53 qz403 9763941168002214989051 9007199254740992000 1199468135939 200000000000000000 9281998806411 33554432000 241651 33554432000 Ns204p352 1454464717162364496127 1801439850948198400 

noncomputable def Ns204p354 := nat_lit 19527882336004429978102000 

noncomputable abbrev qz54 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 483302 4000) qz657) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 966604))))))

noncomputable def Ns204p355 := @Enclosure.Real.IsNear.subLit_ff_p qz54 qz401 11940539875109630446843 9007199254740992000 1199468135939 200000000000000000 483302 2000 0 1 Ns204p354 9763941168002214989051 9007199254740992000 1199468135939 200000000000000000 

noncomputable def Ns204p356 := nat_lit 26887705466073140263039297884797272064 

noncomputable def Ns204p357 := nat_lit 26535897878045981373628416 

noncomputable def Ns204p358 := nat_lit 12532747166461101204643346624091171486466503832652838152185589726393707348061197279642280740204481518506097527850853959672878863142374665768741172674560 

noncomputable def Ns204p359 := nat_lit 346728647769676694259243871864133874080674675573910680693117358898659075865387413000917689365827804504064143013460947096832018120979596195307488018432 

noncomputable def Ns204p360 := nat_lit 234796746085467487841766542390618964964333480299786922936364321052666256590501150428064135033943731609800797029960117209832151305479223634821120 

noncomputable def Ns204p361 := BSN.log_dyadic_bound 410036292816 1458612292816 7 6 Ns204p358 67108864 20480000 Ns204p359 Ns204p360 38774322 1868648585632 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 410036292816) (BSN.artanhQ 1458612292816) 0 6 Ns204p359 Ns204p358 Ns204p360 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns204p362 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 483302 4000) qz657 483302 4000 0 1 49426961463030393 4503599627370496 2441407 50000000000000 11944074664502757498843 9007199254740992000 589968442957 100000000000000000 (Enclosure.Real.IsNear.const Bool.false 483302 4000) (BSN.isNear_log_sfrac 934324292816 16000000 49426961463030393 4503599627370496 2441407 50000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 934324292816) qz352)) Bool.false Ns204p357 Ns204p89 1000000307200000 20480000000000000000000 49426961463030393 4503599627370496 2441407 50000000000000 (BSN.log_rat_reduce_isNear 934324292816 16000000 15 1868648585632 1048576000000 38774322 67108864 24973259072661432 36028797018963968 20480000 1000000000000000 rfl rfl rfl rfl (Ns204p361 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns204p363 := BSN.arctan_dyadic_bound_f 1000 966604 1 0 8388608 2560000 0 1 1 0 1 1 8678 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 966604) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 966604) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz404 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 966604)))

noncomputable def Ns204p364 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz404 884279719003555 562949953421312 1 2000000000000000 8678 8388608 1 2560000 7412990645375183355904 883697348281763 562949953421312 781250001 2000000000000000 qz17 (Ns204p363 rfl) rfl rfl 

noncomputable def Ns204p365 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 483302 4000) qz657) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz404)) 11944074664502757498843 9007199254740992000 589968442957 100000000000000000 883697348281763 2251799813685248 781250001 8000000000000000 Ns204p356 11940539875109630446843 9007199254740992000 1199468135939 200000000000000000 (Ns204p362 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz404) 1 4 0 1 883697348281763 562949953421312 781250001 2000000000000000 883697348281763 2251799813685248 781250001 8000000000000000 qz355 Ns204p364 rfl) 

noncomputable def Ns204p366 := @Ns204p351 Ns204p345 Ns204p346 2703176025498411 204800000000000000000 (@Ns204p353 2703176025498411 204800000000000000000 (Ns204p355 (Ns204p365 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 483302 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz401 (Real.log Real.pi) 483302 2000 0 1 38410761 33554432 1 33554432 9281998806411 33554432000 241651 33554432000 (Enclosure.Real.IsNear.const Bool.false 483302 2000) RS205to222.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns204p347 Ns204p348) 

noncomputable def Ns204p367 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz49) Bool.false Ns204p345 Ns204p346 2703176025498411 204800000000000000000 13545752465 16777216 111 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz49) (@HAdd.hAdd Real Real Real qz356 qz402 (Enclosure.sfrac Bool.true Ns204p347 Ns204p348)) Bool.false Ns204p345 Ns204p346 2703176025498411 204800000000000000000 Ns204p349 (Ns204p366 rfl rfl)) 

noncomputable def Ns204p368 := BSN.cos_dyadic_bound_f 15527822 34359738368 1 0 16777216 5125001 0 1 1 0 1 1 16777214 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 15527822) qz642 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 15527822) qz643 0 0 rfl) rfl rfl 

noncomputable def Ns204p369 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz49) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13545752465) qz369) Bool.false 13545752465 16777216 111 8388608 Bool.true 16777214 16777216 1 2560000 (Ns204p367 rfl) (Enclosure.sfrac_false_div 13545752465 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13545752465) qz369) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1092673385330701762560) qz371) 226375608064910080 72057594037927936 Bool.false 16777214 16777216 128 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q2 13545752465 16777216 226375608064910080 72057594037927936 128 1092673385330701762560 Ns204p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777214 16777216 1092673385330701762560 Ns204p89 15527822 34359738368 5125001 5120000 (Ns204p368 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p370 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz49) Bool.false Ns204p345 Ns204p346 2703176025498411 204800000000000000000 108366019721 134217728 1772 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz49) (@HAdd.hAdd Real Real Real qz356 qz402 (Enclosure.sfrac Bool.true Ns204p347 Ns204p348)) Bool.false Ns204p345 Ns204p346 2703176025498411 204800000000000000000 Ns204p349 (Ns204p366 rfl rfl)) 

noncomputable def Ns204p371 := Ns204p344 37036 BSN.abs_quadSignPos (BSN.cos_quad_nat0 300 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 54641953 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 175 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 134149623 134217728) qz52 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz49) qz49 1) Bool.true 8388607 8388608 71423 5242880000 134217712 134217728 1829 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz49) qz49 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz49)) Bool.true 8388607 8388608 71423 5242880000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz49) qz49) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz49)) Bool.true 16777214 16777216 292548608 21474836480000 8388607 8388608 71423 5242880000 (Ns204p369 rfl rfl) rfl)) rfl) (Ns204p370 rfl) RS205to222.d7 

noncomputable def Ns204p372 := nat_lit 1200494815424478691677107261567789103291251404740591143632382488541134217757796417761035138251670868197376 

noncomputable def Ns204p373 := nat_lit 185739174795027302805253599258319866889698758517587273719052222763898219492346351827558946933047296 

noncomputable def Ns204p374 := nat_lit 7277924990890408835094203631350937729949469250795793194774231071328516626240741047426536866425895984824320 

noncomputable def Ns204p375 := BSN.cos_dyadic_bound_f 154552236 134217728 4 3 134217728 67108864 Ns204p372 Ns204p230 Ns204p373 Ns204p374 Ns204p233 Ns204p373 54641953 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 154552236) qz363 0 3 Ns204p372 Ns204p230 Ns204p373 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 154552236) qz364 0 3 Ns204p374 Ns204p233 Ns204p373 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p376 := nat_lit 9965696655087535306865254397962549944435677690316415152310335063752921942763115961351712132460054798290625 

noncomputable def Ns204p377 := nat_lit 6030779050081018923284066450879484218678374988577343437827061077840739505074073934495347090087890625 

noncomputable def Ns204p378 := nat_lit 49771430646614683459039464545883891175561085756031659515658013547826707062973974975895538217279529639890625 

noncomputable def Ns204p379 := BSN.sin_dyadic_bound_f 206552815 134217728 4 3 134217728 67108864 Ns204p376 Ns204p256 Ns204p377 Ns204p378 Ns204p259 Ns204p377 134149623 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 206552815) qz361 0 3 Ns204p376 Ns204p256 Ns204p377 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 206552815) qz362 0 3 Ns204p378 Ns204p259 Ns204p377 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p380 := nat_lit 91293275217350473746435593029169840975746246708532147948766752172865 

noncomputable def Ns204p381 := nat_lit 8652719212026324036540755358378232852761093717988917238873746241 

noncomputable def Ns204p382 := nat_lit 239087425928622245763653106234388399702335699608707453047430936292161 

noncomputable def Ns204p383 := BSN.sin_dyadic_bound_f 98207369 134217728 3 2 134217728 67108864 Ns204p380 Ns204p106 Ns204p381 Ns204p382 Ns204p109 Ns204p381 89675815 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 98207369) qz361 0 2 Ns204p380 Ns204p106 Ns204p381 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 98207369) qz362 0 2 Ns204p382 Ns204p109 Ns204p381 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p384 := nat_lit 1782293074086477561733463085479312318707310850484561557544929980510264003924106992698833785975569294626816 

noncomputable def Ns204p385 := nat_lit 606877228276614985354161512803479072625543429104768071391914106691545015131053499656232750583975936 

noncomputable def Ns204p386 := nat_lit 10801398161266474240881997981105141117498887941230692038589427652476148662916181924151072256463903705600000 

noncomputable def Ns204p387 := BSN.cos_dyadic_bound_f 170578806 134217728 4 3 134217728 67108864 Ns204p384 Ns204p230 Ns204p385 Ns204p386 Ns204p233 Ns204p385 39649328 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 170578806) qz363 0 3 Ns204p384 Ns204p230 Ns204p385 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 170578806) qz364 0 3 Ns204p386 Ns204p233 Ns204p385 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p388 := Ns204p342 62998 BSN.abs_quadSignPos (BSN.cos_quad_nat3 87 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 89675815 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 18 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 39649328 134217728) qz52 rfl rfl (Ns204p371 RS205to222.d9 RS205to222.d11 RS205to222.d13 RS205to222.d17 (Ns204p375 rfl rfl) (Ns204p379 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns204p370 rfl) RS205to222.d19 RS205to222.d21 RS205to222.d23 RS205to222.d25 RS205to222.d17 (Ns204p383 rfl rfl) (Ns204p387 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns204p389 := nat_lit 13504291667642176749560148706576 

noncomputable def Ns204p390 := BSN.sin_dyadic_bound_f 60620282 134217728 2 1 134217728 67108864 Ns204p389 Ns204p129 Ns204p389 Ns204p389 Ns204p130 Ns204p389 58580178 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 60620282) qz361 0 1 Ns204p389 Ns204p129 Ns204p389 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 60620282) qz362 0 1 Ns204p389 Ns204p130 Ns204p389 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p391 := nat_lit 1095893128800202561232367246756045013166066414803728176921902885714887824534877875794499763880349971890625 

noncomputable def Ns204p392 := nat_lit 141333744096963213634823521380554183856774210834211300511078048489847637422772052690299277587890625 

noncomputable def Ns204p393 := nat_lit 6644186900005827681289390726011382566712364089577413633792864946818154380073110518617424921989343917490625 

noncomputable def Ns204p394 := BSN.cos_dyadic_bound_f 151073105 134217728 4 3 134217728 67108864 Ns204p391 Ns204p230 Ns204p392 Ns204p393 Ns204p233 Ns204p392 57801000 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 151073105) qz363 0 3 Ns204p391 Ns204p230 Ns204p392 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 151073105) qz364 0 3 Ns204p393 Ns204p233 Ns204p392 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p395 := Ns204p340 84550 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 37 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 58580178 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 84 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 57801000 134217728) qz52 rfl rfl (Ns204p388 rfl rfl) (Ns204p370 rfl) RS205to222.d27 RS205to222.d29 RS205to222.d31 RS205to222.d33 RS205to222.d17 (Ns204p390 rfl rfl) (Ns204p394 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns204p396 := nat_lit 800674380375444130744894892975370512956519654154130768042828144640000 

noncomputable def Ns204p397 := nat_lit 664581084778943080865414598953315611155989341514330308633600000000 

noncomputable def Ns204p398 := nat_lit 2095928341131759196486656905584807880087108444803128810088666931200000 

noncomputable def Ns204p399 := BSN.sin_dyadic_bound_f 168973460 134217728 3 2 134217728 67108864 Ns204p396 Ns204p106 Ns204p397 Ns204p398 Ns204p109 Ns204p397 127744249 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 168973460) qz361 0 2 Ns204p396 Ns204p106 Ns204p397 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 168973460) qz362 0 2 Ns204p398 Ns204p109 Ns204p397 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p400 := Ns204p338 Bool.false 6908952 84550 Bool.true 168973460 7074237752028440 1 Bool.false 127744249 Bool.true Bool.true 38255456 94243 BSN.abs_quadSignNeg qz387 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 127744249 134217728) qz52 rfl (Ns204p395 rfl) (Ns204p370 rfl) RS205to222.d35 RS205to222.d37 RS205to222.d17 (Ns204p399 rfl rfl) rfl 

noncomputable def Ns204p401 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz49) qz49 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz49) qz49 8) 38255456 134217728 94243 134217728 38255456 134217728 94243 134217728 10269120775847936 1195483 2097152 94243 67108864 (Ns204p400 rfl rfl rfl rfl) 

noncomputable def Ns204p402 := @Enclosure.Real.IsNear.mulLit_ff qz656 (Zeta.RiemannSiegel.correction qz51) 2832567 8388608 1 8388608 73386168832613 140737488355328 22571969608727 87960930222080000 207871240091688107571 1180591620717411303424 

noncomputable abbrev qz658 := (@HPow.hPow Real Real Real qz7 qz50 qz9)

noncomputable def Ns204p403 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz658 1 1 0 1 2832567 8388608 1 8388608 2832567 8388608 1 8388608 

noncomputable def Ns204p404 := @Enclosure.Real.IsNear.sqrt_image qz50 645250942227 8388608000 241651 8388608000 73571429 73571457 8388608 (@Enclosure.Real.IsNear.of_eq qz50 (@HMul.hMul Real Real Real qz5 qz49 qz3) Bool.false 645250942227 8388608000 241651 8388608000 (BSN.t_div_two_pi_mk qz49 483302 1000 qz52) (@Enclosure.Real.IsNear.mulLit_ff qz49 qz3 483302 1000 0 1 2670177 16777216 1 16777216 645250942227 8388608000 241651 8388608000 (Enclosure.Real.IsNear.const Bool.false 483302 1000) RS205to222.d40 rfl)) 

noncomputable abbrev qz857 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 483302 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz659 := qz857

noncomputable abbrev qz405 := qz659

noncomputable abbrev qz55 := qz405

noncomputable def Ns204p405 := @Enclosure.Real.IsNear.sqrt_image qz55 73571443 8388608 7 4194304 24842742 24842748 8388608 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 147142886 16777216 28 16777216 73571443 8388608 7 4194304 (Ns204p404 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns204p406 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz55) 24842745 8388608 3 8388608 2832566 2832568 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz55) Bool.false 49685490 16777216 6 16777216 24842745 8388608 3 8388608 (Ns204p405 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns204p407 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz55)) Bool.false 5665134 16777216 2 16777216 2832567 8388608 1 8388608 (Ns204p406 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz56 := (@HMul.hMul Real Real Real qz342 qz340 qz399)

noncomputable abbrev qz660 := (@HMul.hMul Real Real Real qz844 qz856 qz856)

noncomputable abbrev qz406 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz660 qz655) qz640)

noncomputable abbrev qz57 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz406))

noncomputable def Ns204p408 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz51) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz56)) qz57) Bool.false 73386168832613 

noncomputable def Ns204p409 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz56)) qz57 131253689 16777216 11235 

noncomputable def Ns204p410 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz56)) Bool.false 131253689 16777216 11235 16777216 131253689 16777216 11235 

noncomputable def Ns204p411 := @Enclosure.Real.IsNear.recentre' (Real.cos qz56) Bool.false 2144511 16777216 469897216 42949672960000 2144511 16777216 114721 10485760000 

noncomputable def Ns204p412 := @Enclosure.Real.IsNear.cos_image qz56 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 40605581) qz359) Bool.false 40605581 8388608 177 16777216 Bool.false 2144511 16777216 1 

noncomputable def Ns204p413 := nat_lit 188902527891064883638999153 

noncomputable def Ns204p414 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz51 884279719003555 140737488355328 1 500000000000000 6462579 8388608 7 4194304 5714727542158275468345 1180591620717411303424 Ns204p413 

noncomputable def Ns204p415 := @Enclosure.Real.IsNear.subLit_ff_p qz55 qz1 73571443 8388608 7 4194304 8 1 0 1 6462579 6462579 8388608 7 

noncomputable def Ns204p416 := @Ns204p415 4194304 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 147142886 16777216 28 16777216 73571443 8388608 7 4194304 (Ns204p404 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns204p417 := @Enclosure.Real.IsNear.recentre' qz56 Bool.false 5714727542158275468345 1180591620717411303424 Ns204p413 Ns204p275 40605581 8388608 177 16777216 (@Ns204p414 Ns204p275 RS205to222.d39 (Ns204p416 rfl rfl) rfl) 

noncomputable def Ns204p418 := nat_lit 376176905030594699011173445670979955681 

noncomputable def Ns204p419 := nat_lit 167255588988979673561517887044862711294853120 

noncomputable def Ns204p420 := nat_lit 1170789122922857714930625209314038979063971840 

noncomputable def Ns204p421 := BSN.sin_dyadic_bound_f 4404007321 34359738368 2 1 16777216 5125001 Ns204p418 Ns204p419 Ns204p418 Ns204p418 Ns204p420 Ns204p418 2144511 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 4404007321) qz357 0 1 Ns204p418 Ns204p419 Ns204p418 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 4404007321) qz358 0 1 Ns204p418 Ns204p420 Ns204p418 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p422 := @Ns204p412 2560000 (Ns204p417 rfl) (Enclosure.sfrac_false_div 40605581 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 40605581) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 154952232289892105715712) qz360) 226375608064910080 72057594037927936 Bool.false 2144511 16777216 0 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q3 40605581 8388608 226375608064910080 72057594037927936 0 154952232289892105715712 Ns204p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 2144511 16777216 154952232289892105715712 Ns204p100 4404007321 34359738368 5125001 5120000 (Ns204p421 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p423 := @Enclosure.Real.IsNear.inv_image (Real.cos qz56) 2144511 16777216 114721 10485760000 65621227 65632462 8388608 (Ns204p411 (Ns204p422 rfl rfl) rfl) rfl 

noncomputable def Ns204p424 := @Enclosure.Real.IsNear.recentre' qz57 Bool.false 559117 8388608 

noncomputable abbrev qz58 := (@HMul.hMul Real Real Real qz342 qz340 qz406)

noncomputable def Ns204p425 := @Enclosure.Real.IsNear.cos_image qz58 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 6308631)) qz385) Bool.true 6308631 4194304 

noncomputable def Ns204p426 := nat_lit 14895834306299171697144026725 

noncomputable def Ns204p427 := nat_lit 201311346019738649096214982318537 

noncomputable def Ns204p428 := @Enclosure.Real.IsNear.recentre' qz58 Bool.true Ns204p426 Ns204p167 Ns204p427 

noncomputable def Ns204p429 := nat_lit 7555786372591432341913600000000000000 

noncomputable abbrev qz59 := qz406

noncomputable def Ns204p430 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz59 884279719003555 140737488355328 1 500000000000000 16845161079895 

noncomputable abbrev qz407 := (@HSub.hSub Real Real Real qz634 qz660 qz655)

noncomputable abbrev qz60 := qz407

noncomputable def Ns204p431 := @Enclosure.Real.IsNear.subLit_tf qz60 qz27 12447114568791 70368744177664 37299115 8796093022208 1 16 

noncomputable abbrev qz408 := qz660

noncomputable abbrev qz61 := qz408

noncomputable def Ns204p432 := @Enclosure.Real.IsNear.subLit_ff_n qz61 qz51 41764927331241 70368744177664 22619051 8796093022208 6462579 8388608 7 4194304 

noncomputable def Ns204p433 := @Enclosure.Real.IsNear.mulLit_ff qz51 qz51 6462579 8388608 7 4194304 6462579 8388608 7 4194304 41764927331241 70368744177664 

noncomputable def Ns204p434 := nat_lit 3037155779803690718633230648006235604266507150785502430682094022877785386231519223551841 

noncomputable def Ns204p435 := nat_lit 3973941855117239600629900466844304511812317688871971092559455820234985259240068961 

noncomputable def Ns204p436 := nat_lit 18388084114103327735470142957119272632419478711243252544649097077827788401811755588982625 

noncomputable def Ns204p437 := BSN.cos_dyadic_bound_f 6308631 4194304 4 3 8388608 2560000 Ns204p434 Ns204p295 Ns204p435 Ns204p436 Ns204p298 Ns204p435 559117 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 6308631) (BSN.cosEvenQ 4194304) 0 3 Ns204p434 Ns204p295 Ns204p435 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 6308631) (BSN.cosOddQ 4194304) 0 3 Ns204p436 Ns204p298 Ns204p435 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p438 := @Ns204p424 18182144 671088640000 559117 8388608 4439 163840000 (@Ns204p425 7 262144 Bool.false 559117 8388608 1 2560000 (@Ns204p428 Ns204p429 6308631 4194304 7 262144 (@Ns204p430 70368744177664 37299115 8796093022208 Ns204p426 Ns204p167 Ns204p427 Ns204p429 RS205to222.d39 (@Ns204p431 0 1 269522577278320 16845161079895 70368744177664 37299115 8796093022208 (@Ns204p432 104413964848676732928 12447114568791 70368744177664 37299115 8796093022208 (@Ns204p433 22619051 8796093022208 (Ns204p416 rfl rfl) (Ns204p416 rfl rfl) rfl) (Ns204p416 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 6308631 4194304) (BSN.cos_neg_of_bound 6308631 4194304 Bool.false 559117 8388608 1 2560000 (Ns204p437 rfl rfl)) rfl rfl) 

noncomputable def Ns204p439 := @Ns204p402 63982505166173004061 737869762948382064640000 (Ns204p403 qz29 (@Enclosure.Real.IsNear.of_eq qz658 (@Inv.inv Real Real.instInv (Real.sqrt qz55)) Bool.false 2832567 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz50 (BSN.t_div_two_pi_nonneg qz49 483302 1000 qz52)) Ns204p407) rfl) (@Ns204p408 140737488355328 22571969608727 87960930222080000 (BSN.correction_mk qz51 (BSN.cos_two_pi_p_ne_zero_mk qz49 483302 1000 8 qz52 rfl rfl (@BSN.floor_sqrt_eq_dec qz49 483302 1000 8 qz52 rfl rfl rfl))) (@Ns204p409 16777216 559117 8388608 4439 163840000 73386168832613 140737488355328 22571969608727 87960930222080000 (@Ns204p410 16777216 (Ns204p423 rfl rfl rfl rfl rfl) rfl) (Ns204p438 rfl) rfl)) 

noncomputable def Ns204p440 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz49) (hardyZApproximantRS₀ qz49) Bool.true 880868339257658441267 1180591620717411303424 1100195248531108684061 737869762948382064640000 (@Eq.refl Real (hardyZApproximantRS₀ qz49)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz49) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz49) qz49 8) (@HMul.hMul Real Real Real qz5 qz656 (Zeta.RiemannSiegel.correction qz51))) Bool.true 880868339257658441267 1180591620717411303424 1100195248531108684061 737869762948382064640000 (BSN.hardyZApproximantRS₀_eq qz49 8 (@BSN.floor_sqrt_eq_dec qz49 483302 1000 8 qz52 rfl rfl rfl)) (@Ns204p337 880868339257658441267 1180591620717411303424 1100195248531108684061 737869762948382064640000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz49) qz49 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz49) qz49 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz49) qz49 8)) Bool.true 1195483 2097152 94243 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz49) qz49 8) (Ns204p401 (Ns204p400 rfl rfl rfl rfl) rfl rfl)) (Ns204p439 rfl) rfl rfl)) 

theorem RS205to222.d45 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz49) Bool.true 880868339257658441267 1180591620717411303424 1100195248531108684061 737869762948382064640000 := Ns204p440 

noncomputable def Ns204p441 := nat_lit 36522639486296354442767761408 

noncomputable abbrev qz858 := (Enclosure.sfrac Bool.false 484748 1000)

noncomputable abbrev qz661 := qz858

noncomputable abbrev qz409 := qz661

noncomputable abbrev qz62 := qz409

noncomputable abbrev qz859 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 484748 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz662 := qz859

noncomputable abbrev qz410 := qz662

noncomputable abbrev qz63 := qz410

noncomputable abbrev qz860 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 484748 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz663 := qz860

noncomputable abbrev qz411 := qz663

noncomputable abbrev qz64 := qz411

noncomputable abbrev qz664 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz63 qz9))

noncomputable def Ns204p442 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 8) (@HMul.hMul Real Real Real qz5 qz664 (Zeta.RiemannSiegel.correction qz64)) 135888253 67108864 47265 33554432 53413118796580325565 295147905179352825856 41051261777820444403 737869762948382064640000 Ns204p441 

noncomputable def Ns204p443 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin BSN.quadSignNeg 7 8 484748 1000 125 134217728 67108864 2251799813685248 Bool.false 108787584201 1778 279097919 53 47453128 8 

noncomputable def Ns204p444 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 484748 1000 36 84 134217728 67108864 2251799813685248 Bool.false 108787584201 1778 

noncomputable def Ns204p445 := Ns204p444 240485871 53 54794152 8 261175631 53 50729528 8 Bool.false 137921932 63190 Bool.true 197627085 Bool.true 107168587 7074237752028440 1 Bool.false 13180352 Bool.false Bool.false 93657766 Bool.false Bool.false 178702092 

noncomputable def Ns204p446 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 484748 1000 88 19 134217728 67108864 2251799813685248 Bool.false 108787584201 1778 

noncomputable def Ns204p447 := Ns204p446 186065264 53 67108856 8 216015088 53 60023992 8 Bool.false 44256073 37150 Bool.false 39892763 Bool.false 68956754 7074237752028440 1 Bool.false 128332696 Bool.false Bool.false 65962932 Bool.false Bool.false 137921932 

noncomputable def Ns204p448 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 484748 1000 302 176 134217728 67108864 2251799813685248 Bool.false 108787584201 1778 

noncomputable def Ns204p449 := Ns204p448 93032624 53 94906264 8 147453232 53 77490640 16 Bool.false 134217720 1837 Bool.false 19934114 Bool.false 204071208 7074237752028440 1 Bool.false 132740132 Bool.true Bool.false 6754651 Bool.false Bool.false 44256073 

noncomputable def Ns204p450 := nat_lit 13008263945084888754765863526589985046659732086647259 

noncomputable def Ns204p451 := nat_lit 16049070716606292607548235790810897807019343872000 

noncomputable def Ns204p452 := nat_lit 12847615701782740930253782384640000 

noncomputable def Ns204p453 := nat_lit 37367154649939137994191226993712824320 

noncomputable abbrev qz412 := (@Eq.refl Real qz661)

noncomputable abbrev qz65 := qz412

noncomputable def Ns204p454 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz62 484748 1000 939923494016 16000000 969496 4000 2000 Ns204p452 Ns204p453 qz65 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns204p455 := nat_lit 136401533744813323109173701132576201602862752324882362531840 

noncomputable abbrev qz413 := (Enclosure.sfrac Bool.false 484748 2000)

noncomputable abbrev qz665 := (Real.log (Enclosure.sfrac Bool.false 939923494016 16000000))

noncomputable abbrev qz66 := (@HSub.hSub Real Real Real qz345 (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 484748 4000) qz665) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 969496)))))) qz413)

noncomputable abbrev qz414 := (@HSub.hSub Real Real Real qz12 qz66 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 484748 2000) (Real.log Real.pi)))

noncomputable def Ns204p456 := @Enclosure.Real.IsNear.addLit_ft_p qz414 (Enclosure.sfrac Bool.true Ns204p452 Ns204p453) 3650307144955517111387 4503599627370496000 1355601934202907 102400000000000000000 Ns204p452 Ns204p453 0 1 Ns204p455 

noncomputable def Ns204p457 := nat_lit 61241991437262020969435758592000 

noncomputable abbrev qz415 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 484748 2000) (Real.log Real.pi))

noncomputable def Ns204p458 := @Enclosure.Real.IsNear.subLit_ff_p qz66 qz415 4899843293917893004379 4503599627370496000 1202998410461 200000000000000000 4654884893307 16777216000 121187 16777216000 Ns204p457 3650307144955517111387 4503599627370496000 

noncomputable def Ns204p459 := nat_lit 9799686587835786008758000 

noncomputable abbrev qz67 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 484748 4000) qz665) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 969496))))))

noncomputable def Ns204p460 := @Enclosure.Real.IsNear.subLit_ff_p qz67 qz413 5991398750002189601883 4503599627370496000 1202998410461 200000000000000000 484748 2000 0 1 Ns204p459 4899843293917893004379 4503599627370496000 1202998410461 200000000000000000 

noncomputable def Ns204p461 := nat_lit 13491430588968958305752184268190121984 

noncomputable def Ns204p462 := nat_lit 26550344308757878336913408 

noncomputable def Ns204p463 := nat_lit 422000017761862059403173287118295168346595253871048577734375378758932572260808318759853820856077524601585940019296482737824196959500675297203665847695803383956968551156704870400 

noncomputable def Ns204p464 := nat_lit 11916322485872956628697441555377139827349297926109974119379352702407942844422952403985262577021246840925296213237487940792742028435125842832571694000555950711794531559528202240 

noncomputable def Ns204p465 := nat_lit 620504073139585770584232091868828176592061731685813135537571023311605575470344318583698796523177306683630914935053327330591188757001711337602297714018594735605006991360 

noncomputable def Ns204p466 := BSN.log_dyadic_bound 415635494016 1464211494016 8 7 Ns204p463 67108864 20480000 Ns204p464 Ns204p465 39175291 1879846988032 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 415635494016) (BSN.artanhQ 1464211494016) 0 7 Ns204p464 Ns204p463 Ns204p465 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns204p467 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 484748 4000) qz665 484748 4000 0 1 49453870037119609 4503599627370496 2441407 50000000000000 5993166148188414055883 4503599627370496000 295866790109 50000000000000000 (Enclosure.Real.IsNear.const Bool.false 484748 4000) (BSN.isNear_log_sfrac 939923494016 16000000 49453870037119609 4503599627370496 2441407 50000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 939923494016) qz352)) Bool.false Ns204p462 Ns204p89 1000000307200000 20480000000000000000000 49453870037119609 4503599627370496 2441407 50000000000000 (BSN.log_rat_reduce_isNear 939923494016 16000000 15 1879846988032 1048576000000 39175291 67108864 24973259072661432 36028797018963968 20480000 1000000000000000 rfl rfl rfl rfl (Ns204p466 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns204p468 := BSN.arctan_dyadic_bound_f 1000 969496 1 0 8388608 2560000 0 1 1 0 1 1 8652 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 969496) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 969496) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz416 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 969496)))

noncomputable def Ns204p469 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz416 884279719003555 562949953421312 1 2000000000000000 8652 8388608 1 2560000 7413005282073972310016 883699093112227 562949953421312 781250001 2000000000000000 qz17 (Ns204p468 rfl) rfl rfl 

noncomputable def Ns204p470 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 484748 4000) qz665) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz416)) 5993166148188414055883 4503599627370496000 295866790109 50000000000000000 883699093112227 2251799813685248 781250001 8000000000000000 Ns204p461 5991398750002189601883 4503599627370496000 1202998410461 200000000000000000 (Ns204p467 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz416) 1 4 0 1 883699093112227 562949953421312 781250001 2000000000000000 883699093112227 2251799813685248 781250001 8000000000000000 qz355 Ns204p469 rfl) 

noncomputable def Ns204p471 := @Ns204p456 Ns204p450 Ns204p451 1355601934202907 102400000000000000000 (@Ns204p458 1355601934202907 102400000000000000000 (Ns204p460 (Ns204p470 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 484748 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz413 (Real.log Real.pi) 484748 2000 0 1 38410761 33554432 1 33554432 4654884893307 16777216000 121187 16777216000 (Enclosure.Real.IsNear.const Bool.false 484748 2000) RS205to222.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns204p452 Ns204p453) 

noncomputable def Ns204p472 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns204p450 Ns204p451 1355601934202907 102400000000000000000 13598448025 16777216 223 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz356 qz414 (Enclosure.sfrac Bool.true Ns204p452 Ns204p453)) Bool.false Ns204p450 Ns204p451 1355601934202907 102400000000000000000 Ns204p454 (Ns204p471 rfl rfl)) 

noncomputable def Ns204p473 := nat_lit 3797370739911539923353600 

noncomputable def Ns204p474 := nat_lit 856611483073080148827120165332439828809533783835160652787735394575899770153658236471243293729527742779347077768809805391032318433427456 

noncomputable def Ns204p475 := nat_lit 609871571349010250074549398238030448074763413599580013110732343254362622321528862455959434058041656616161641085686410249928441856 

noncomputable def Ns204p476 := nat_lit 4277738443032357749789038878726142229176929015315208744215443183981599455360582883188009488388060753555350087354726630802912334122582016 

noncomputable def Ns204p477 := BSN.sin_dyadic_bound_f 53963883884 34359738368 4 3 16777216 5125001 Ns204p474 Ns204p217 Ns204p475 Ns204p476 Ns204p220 Ns204p475 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53963883884) qz357 0 3 Ns204p474 Ns204p217 Ns204p475 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53963883884) qz358 0 3 Ns204p476 Ns204p220 Ns204p475 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p478 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz62) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13598448025) qz369) Bool.false 13598448025 16777216 223 16777216 Bool.false 16777215 16777216 1 2560000 (Ns204p472 rfl) (Enclosure.sfrac_false_div 13598448025 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13598448025) qz369) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns204p473) qz371) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 128 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q3 13598448025 16777216 226375608064910080 72057594037927936 128 Ns204p473 Ns204p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns204p473 Ns204p89 53963883884 34359738368 5125001 5120000 (Ns204p477 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p479 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns204p450 Ns204p451 1355601934202907 102400000000000000000 108787584201 134217728 1778 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz356 qz414 (Enclosure.sfrac Bool.true Ns204p452 Ns204p453)) Bool.false Ns204p450 Ns204p451 1355601934202907 102400000000000000000 Ns204p454 (Ns204p471 rfl rfl)) 

noncomputable def Ns204p480 := Ns204p449 37150 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 302 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132740132 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 176 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 6754651 134217728) qz65 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) Bool.false 16777215 16777216 143471 10485760000 134217720 134217728 1837 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.false 16777215 16777216 143471 10485760000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz62) qz62) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.false 16777215 16777216 587657216 42949672960000 16777215 16777216 143471 10485760000 (Ns204p478 rfl rfl) rfl)) rfl) (Ns204p479 rfl) RS205to222.d7 

noncomputable def Ns204p481 := nat_lit 157902043454128798980017280016 

noncomputable def Ns204p482 := BSN.cos_dyadic_bound_f 19934114 134217728 2 1 134217728 67108864 Ns204p481 Ns204p125 Ns204p481 Ns204p481 Ns204p126 Ns204p481 132740132 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 19934114) qz363 0 1 Ns204p481 Ns204p125 Ns204p481 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 19934114) qz364 0 1 Ns204p481 Ns204p126 Ns204p481 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p483 := nat_lit 3656888262089893943501473661263796887056521046013202592476531058274925956273761933674297535865266861244416 

noncomputable def Ns204p484 := nat_lit 5216519360374219776166455638641298400890829630202872529091343421273308294237088430032869937995841536 

noncomputable def Ns204p485 := nat_lit 22138196137231539216505434177814660306784247482781003093124599420075574099307147590414708425499369222963200 

noncomputable def Ns204p486 := BSN.cos_dyadic_bound_f 204071208 134217728 4 3 134217728 67108864 Ns204p483 Ns204p230 Ns204p484 Ns204p485 Ns204p233 Ns204p484 6754651 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 204071208) qz363 0 3 Ns204p483 Ns204p230 Ns204p484 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 204071208) qz364 0 3 Ns204p485 Ns204p233 Ns204p484 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p487 := nat_lit 2532657528652061996169519640561 

noncomputable def Ns204p488 := BSN.cos_dyadic_bound_f 39892763 134217728 2 1 134217728 67108864 Ns204p487 Ns204p125 Ns204p487 Ns204p487 Ns204p126 Ns204p487 128332696 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 39892763) qz363 0 1 Ns204p487 Ns204p125 Ns204p487 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 39892763) qz364 0 1 Ns204p487 Ns204p126 Ns204p487 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p489 := nat_lit 22189042587041398121987251087930816950003628290720094937528477958400 

noncomputable def Ns204p490 := nat_lit 511227818657481583454300840164811613080584246024152871871201536 

noncomputable def Ns204p491 := nat_lit 58113331454354406777879112552744253745493086482154304779353460326656 

noncomputable def Ns204p492 := BSN.sin_dyadic_bound_f 68956754 134217728 3 2 134217728 67108864 Ns204p489 Ns204p106 Ns204p490 Ns204p491 Ns204p109 Ns204p490 65962932 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 68956754) qz361 0 2 Ns204p489 Ns204p106 Ns204p490 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 68956754) qz362 0 2 Ns204p491 Ns204p109 Ns204p490 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p493 := Ns204p447 63190 BSN.abs_quadSignPos (BSN.cos_quad_nat0 88 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 128332696 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 19 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 65962932 134217728) qz65 rfl rfl (Ns204p480 RS205to222.d9 RS205to222.d11 RS205to222.d13 RS205to222.d17 (Ns204p482 rfl rfl) (Ns204p486 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns204p479 rfl) RS205to222.d19 RS205to222.d21 RS205to222.d23 RS205to222.d25 RS205to222.d17 (Ns204p488 rfl rfl) (Ns204p492 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns204p494 := nat_lit 3215174538794359116893711294308783049947537129274600246724349301445130691674318460057212438038067225640625 

noncomputable def Ns204p495 := nat_lit 3549421520594892510501357275459790207823115678085094813499323213230589923410723503827443398681640625 

noncomputable def Ns204p496 := nat_lit 19469092607058610185708530922785791324966045955928893196738867700304833334842100323085738751327457715240625 

noncomputable def Ns204p497 := BSN.cos_dyadic_bound_f 197627085 134217728 4 3 134217728 67108864 Ns204p494 Ns204p230 Ns204p495 Ns204p496 Ns204p233 Ns204p495 13180352 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 197627085) qz363 0 3 Ns204p494 Ns204p230 Ns204p495 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 197627085) qz364 0 3 Ns204p496 Ns204p233 Ns204p495 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p498 := nat_lit 71932291541218333459029558369163973340398302631622398360064988572001 

noncomputable def Ns204p499 := nat_lit 17399630961982878562707573732683339094532206905013428086341921121 

noncomputable def Ns204p500 := nat_lit 215762075361731034619963259960026553343005843481057168224022281873761 

noncomputable def Ns204p501 := BSN.cos_dyadic_bound_f 107168587 134217728 3 2 134217728 67108864 Ns204p498 Ns204p240 Ns204p499 Ns204p500 Ns204p243 Ns204p499 93657766 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 107168587) qz363 0 2 Ns204p498 Ns204p240 Ns204p499 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 107168587) qz364 0 2 Ns204p500 Ns204p243 Ns204p499 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p502 := Ns204p445 84807 BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 13180352 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 84 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 93657766 134217728) qz65 rfl rfl (Ns204p493 rfl rfl) (Ns204p479 rfl) RS205to222.d27 RS205to222.d29 RS205to222.d31 RS205to222.d33 RS205to222.d17 (Ns204p497 rfl rfl) (Ns204p501 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns204p503 := nat_lit 510248241547755761192430672007539046859639614202545912268088898873825 

noncomputable def Ns204p504 := nat_lit 270060181169097918109991730220865621146054181924965289386785761761 

noncomputable def Ns204p505 := nat_lit 1335927201855562739827045106742244673626724425664503635947892320102881 

noncomputable def Ns204p506 := BSN.sin_dyadic_bound_f 150984571 134217728 3 2 134217728 67108864 Ns204p503 Ns204p106 Ns204p504 Ns204p505 Ns204p109 Ns204p504 121095833 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 150984571) qz361 0 2 Ns204p503 Ns204p106 Ns204p504 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 150984571) qz362 0 2 Ns204p505 Ns204p109 Ns204p504 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p507 := Ns204p443 Bool.false 178702092 84807 Bool.true 150984571 7074237752028440 1 Bool.false 121095833 Bool.true Bool.false 135888253 94530 BSN.abs_quadSignNeg qz387 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 121095833 134217728) qz65 rfl (Ns204p502 rfl) (Ns204p479 rfl) RS205to222.d35 RS205to222.d37 RS205to222.d17 (Ns204p506 rfl rfl) rfl 

noncomputable def Ns204p508 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 8) 135888253 134217728 94530 134217728 135888253 134217728 94530 134217728 36477225159098368 135888253 67108864 47265 33554432 (Ns204p507 rfl rfl rfl rfl) 

noncomputable def Ns204p509 := @Enclosure.Real.IsNear.mulLit_ff qz664 (Zeta.RiemannSiegel.correction qz64) 5660905 16777216 1 16777216 9435438113973 17592186044416 14495090779651 87960930222080000 53413118796580325565 295147905179352825856 

noncomputable abbrev qz666 := (@HPow.hPow Real Real Real qz7 qz63 qz9)

noncomputable def Ns204p510 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz666 1 1 0 1 5660905 16777216 1 16777216 5660905 16777216 1 16777216 

noncomputable def Ns204p511 := @Enclosure.Real.IsNear.sqrt_image qz63 323590740099 4194304000 121187 4194304000 73681406 73681435 8388608 (@Enclosure.Real.IsNear.of_eq qz63 (@HMul.hMul Real Real Real qz5 qz62 qz3) Bool.false 323590740099 4194304000 121187 4194304000 (BSN.t_div_two_pi_mk qz62 484748 1000 qz65) (@Enclosure.Real.IsNear.mulLit_ff qz62 qz3 484748 1000 0 1 2670177 16777216 1 16777216 323590740099 4194304000 121187 4194304000 (Enclosure.Real.IsNear.const Bool.false 484748 1000) RS205to222.d40 rfl)) 

noncomputable abbrev qz861 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 484748 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz667 := qz861

noncomputable abbrev qz417 := qz667

noncomputable abbrev qz68 := qz417

noncomputable def Ns204p512 := @Enclosure.Real.IsNear.sqrt_image qz68 147362841 16777216 29 16777216 24861303 24861309 8388608 (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 147362841 16777216 29 16777216 147362841 16777216 29 16777216 (Ns204p511 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns204p513 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz68) 12430653 4194304 3 8388608 2830452 2830453 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz68) Bool.false 49722612 16777216 6 16777216 12430653 4194304 3 8388608 (Ns204p512 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns204p514 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz68)) Bool.false 5660905 16777216 1 16777216 5660905 16777216 1 16777216 (Ns204p513 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz69 := (@HMul.hMul Real Real Real qz342 qz340 qz411)

noncomputable abbrev qz668 := (@HMul.hMul Real Real Real qz844 qz860 qz860)

noncomputable abbrev qz418 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz668 qz663) qz640)

noncomputable abbrev qz70 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz418))

noncomputable def Ns204p515 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz64) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz69)) qz70) Bool.false 9435438113973 

noncomputable def Ns204p516 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz69)) qz70 40137649 8388608 1091 

noncomputable def Ns204p517 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz69)) Bool.false 80275298 16777216 4364 16777216 40137649 8388608 1091 

noncomputable def Ns204p518 := @Enclosure.Real.IsNear.recentre' (Real.cos qz69) Bool.false 3506371 16777216 60977152 5368709120000 3506371 16777216 14887 1310720000 

noncomputable def Ns204p519 := @Enclosure.Real.IsNear.cos_image qz69 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 20648295) qz385) Bool.false 20648295 4194304 23 2097152 Bool.false 3506371 16777216 1 

noncomputable def Ns204p520 := nat_lit 782596186975192979074348939 

noncomputable def Ns204p521 := nat_lit 72057594037927936000000000000000 

noncomputable def Ns204p522 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz64 884279719003555 140737488355328 1 500000000000000 13145113 16777216 29 16777216 11623956829909977876715 2361183241434822606848 Ns204p520 

noncomputable def Ns204p523 := @Enclosure.Real.IsNear.subLit_ff_p qz68 qz1 147362841 16777216 29 16777216 8 1 0 1 13145113 13145113 16777216 29 

noncomputable def Ns204p524 := @Ns204p523 16777216 (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 147362841 16777216 29 16777216 147362841 16777216 29 16777216 (Ns204p511 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns204p525 := @Enclosure.Real.IsNear.recentre' qz69 Bool.false 11623956829909977876715 2361183241434822606848 Ns204p520 Ns204p521 20648295 4194304 23 2097152 (@Ns204p522 Ns204p521 RS205to222.d39 (Ns204p524 rfl rfl) rfl) 

noncomputable def Ns204p526 := nat_lit 2739083761298693956444416198066241350625 

noncomputable def Ns204p527 := BSN.sin_dyadic_bound_f 7234380185 34359738368 2 1 16777216 5125001 Ns204p526 Ns204p419 Ns204p526 Ns204p526 Ns204p420 Ns204p526 3506371 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 7234380185) qz357 0 1 Ns204p526 Ns204p419 Ns204p526 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 7234380185) qz358 0 1 Ns204p526 Ns204p420 Ns204p526 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p528 := @Ns204p519 2560000 (Ns204p525 rfl) (Enclosure.sfrac_false_div 20648295 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 20648295) qz385) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 127268562143500597985280) qz386) 226375608064910080 72057594037927936 Bool.false 3506371 16777216 0 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q3 20648295 4194304 226375608064910080 72057594037927936 0 127268562143500597985280 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 3506371 16777216 127268562143500597985280 604462909807314587353088 7234380185 34359738368 5125001 5120000 (Ns204p527 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p529 := @Enclosure.Real.IsNear.inv_image (Real.cos qz69) 3506371 16777216 14887 1310720000 40135467 40139831 8388608 (Ns204p518 (Ns204p528 rfl rfl) rfl) rfl 

noncomputable def Ns204p530 := @Enclosure.Real.IsNear.recentre' qz70 Bool.false 940308 8388608 

noncomputable abbrev qz71 := (@HMul.hMul Real Real Real qz342 qz340 qz418)

noncomputable def Ns204p531 := @Enclosure.Real.IsNear.cos_image qz71 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 6117253)) qz385) Bool.true 6117253 4194304 

noncomputable def Ns204p532 := nat_lit 57775821805800962596442080525 

noncomputable def Ns204p533 := nat_lit 39614081257132168796771975168 

noncomputable def Ns204p534 := nat_lit 33704438582962946433592864410147813 

noncomputable def Ns204p535 := @Enclosure.Real.IsNear.recentre' qz71 Bool.true Ns204p532 Ns204p533 Ns204p534 

noncomputable def Ns204p536 := nat_lit 1208925819614629174706176000000000000000 

noncomputable abbrev qz72 := qz418

noncomputable def Ns204p537 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz72 884279719003555 140737488355328 1 500000000000000 65336590407055 

noncomputable abbrev qz419 := (@HSub.hSub Real Real Real qz634 qz668 qz663)

noncomputable abbrev qz73 := qz419

noncomputable def Ns204p538 := @Enclosure.Real.IsNear.subLit_tf qz73 qz27 47744404362639 281474976710656 1248956659 281474976710656 1 16 

noncomputable abbrev qz420 := qz668

noncomputable abbrev qz74 := qz420

noncomputable def Ns204p539 := @Enclosure.Real.IsNear.subLit_ff_n qz74 qz64 172793995782769 281474976710656 762417395 281474976710656 13145113 16777216 29 16777216 

noncomputable def Ns204p540 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz64 13145113 16777216 29 16777216 13145113 16777216 29 16777216 172793995782769 281474976710656 

noncomputable def Ns204p541 := nat_lit 2684103546103470879326206214442169103204685254550581624288995742924036128720925175331921 

noncomputable def Ns204p542 := nat_lit 2745853176117050260231290337115434445874677786907484239034421001275257992478735441 

noncomputable def Ns204p543 := nat_lit 16254389013736215217265917460886479702255298915762432493624603937841916683229736219720785 

noncomputable def Ns204p544 := BSN.cos_dyadic_bound_f 6117253 4194304 4 3 8388608 2560000 Ns204p541 Ns204p295 Ns204p542 Ns204p543 Ns204p298 Ns204p542 940308 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 6117253) (BSN.cosEvenQ 4194304) 0 3 Ns204p541 Ns204p295 Ns204p542 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 6117253) (BSN.cosOddQ 4194304) 0 3 Ns204p543 Ns204p298 Ns204p542 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p545 := @Ns204p530 1217417216 42949672960000 235077 2097152 297221 10485760000 (@Ns204p531 469 16777216 Bool.false 940308 8388608 1 2560000 (@Ns204p535 Ns204p536 6117253 4194304 469 16777216 (@Ns204p537 281474976710656 1248956659 281474976710656 Ns204p532 Ns204p533 Ns204p534 Ns204p536 RS205to222.d39 (@Ns204p538 0 1 1045385446512880 65336590407055 281474976710656 1248956659 281474976710656 (@Ns204p539 801018184783336833024 47744404362639 281474976710656 1248956659 281474976710656 (@Ns204p540 762417395 281474976710656 (Ns204p524 rfl rfl) (Ns204p524 rfl rfl) rfl) (Ns204p524 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 6117253 4194304) (BSN.cos_neg_of_bound 6117253 4194304 Bool.false 940308 8388608 1 2560000 (Ns204p544 rfl rfl)) rfl rfl) 

noncomputable def Ns204p546 := @Ns204p509 41051261777820444403 737869762948382064640000 (Ns204p510 qz29 (@Enclosure.Real.IsNear.of_eq qz666 (@Inv.inv Real Real.instInv (Real.sqrt qz68)) Bool.false 5660905 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz63 (BSN.t_div_two_pi_nonneg qz62 484748 1000 qz65)) Ns204p514) rfl) (@Ns204p515 17592186044416 14495090779651 87960930222080000 (BSN.correction_mk qz64 (BSN.cos_two_pi_p_ne_zero_mk qz62 484748 1000 8 qz65 rfl rfl (@BSN.floor_sqrt_eq_dec qz62 484748 1000 8 qz65 rfl rfl rfl))) (@Ns204p516 4194304 235077 2097152 297221 10485760000 9435438113973 17592186044416 14495090779651 87960930222080000 (@Ns204p517 4194304 (Ns204p529 rfl rfl rfl rfl rfl) rfl) (Ns204p545 rfl) rfl)) 

noncomputable def Ns204p547 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (hardyZApproximantRS₀ qz62) Bool.false 544229738210087335747 295147905179352825856 1080419603514473244403 737869762948382064640000 (@Eq.refl Real (hardyZApproximantRS₀ qz62)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 8) (@HMul.hMul Real Real Real qz5 qz664 (Zeta.RiemannSiegel.correction qz64))) Bool.false 544229738210087335747 295147905179352825856 1080419603514473244403 737869762948382064640000 (BSN.hardyZApproximantRS₀_eq qz62 8 (@BSN.floor_sqrt_eq_dec qz62 484748 1000 8 qz65 rfl rfl rfl)) (@Ns204p442 544229738210087335747 295147905179352825856 1080419603514473244403 737869762948382064640000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 8)) Bool.false 135888253 67108864 47265 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz62) qz62 8) (Ns204p508 (Ns204p507 rfl rfl rfl rfl) rfl rfl)) (Ns204p546 rfl) rfl rfl)) 

theorem RS205to222.d46 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz62) Bool.false 544229738210087335747 295147905179352825856 1080419603514473244403 737869762948382064640000 := Ns204p547 

noncomputable def Ns204p548 := nat_lit 16386742911256452420461395968 

noncomputable abbrev qz862 := (Enclosure.sfrac Bool.false 486193 1000)

noncomputable abbrev qz669 := qz862

noncomputable abbrev qz421 := qz669

noncomputable abbrev qz75 := qz421

noncomputable abbrev qz863 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 486193 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz670 := qz863

noncomputable abbrev qz422 := qz670

noncomputable abbrev qz76 := qz422

noncomputable abbrev qz864 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 486193 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz671 := qz864

noncomputable abbrev qz423 := qz671

noncomputable abbrev qz77 := qz423

noncomputable abbrev qz672 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz76 qz9))

noncomputable def Ns204p549 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz75) qz75 8) (@HMul.hMul Real Real Real qz5 qz672 (Zeta.RiemannSiegel.correction qz77)) 21513939 33554432 23703 16777216 109885777689328518825 590295810358705651712 15061260478495640787 368934881474191032320000 Ns204p548 

noncomputable def Ns204p550 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz75) qz75 Real.sin BSN.quadSignNeg 7 8 486193 1000 125 134217728 67108864 2251799813685248 Bool.false 109209146156 1783 279097919 53 47453128 8 

noncomputable def Ns204p551 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz75) qz75 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 486193 1000 36 84 134217728 67108864 2251799813685248 Bool.false 109209146156 1783 

noncomputable def Ns204p552 := Ns204p551 240485871 53 54794152 8 261175631 53 50729528 8 Bool.true 81795369 63380 Bool.true 123567214 Bool.true 63005419 7074237752028440 1 Bool.false 81242646 Bool.false Bool.false 119699083 Bool.false Bool.true 3386205 

noncomputable def Ns204p553 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz75) qz75 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 486193 1000 88 19 134217728 67108864 2251799813685248 Bool.false 109209146156 1783 

noncomputable def Ns204p554 := Ns204p553 186065264 53 67108856 8 216015088 53 60023992 8 Bool.true 149164504 37263 Bool.false 192590412 Bool.false 178376907 7074237752028440 1 Bool.false 18182225 Bool.false Bool.false 130313626 Bool.false Bool.true 81795369 

noncomputable def Ns204p555 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz75) qz75 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 486193 1000 303 177 134217728 67108864 2251799813685248 Bool.false 109209146156 1783 

noncomputable def Ns204p556 := Ns204p555 93032624 53 94906264 8 147453232 53 77490640 16 Bool.true 134217664 1845 Bool.false 96235213 Bool.false 201734528 7074237752028440 1 Bool.false 88198828 Bool.false Bool.false 133909748 Bool.true Bool.true 149164504 

noncomputable def Ns204p557 := nat_lit 1742468727722500832220171777446011063273924372470167038849 

noncomputable def Ns204p558 := nat_lit 2141489078312613371111845697022620633279667470598144000 

noncomputable def Ns204p559 := nat_lit 13040249767998751496408182812640000 

noncomputable def Ns204p560 := nat_lit 38040487707615493404344521213691277120 

noncomputable abbrev qz424 := (@Eq.refl Real qz669)

noncomputable abbrev qz78 := qz424

noncomputable def Ns204p561 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz75 486193 1000 945535532996 16000000 972386 4000 2000 Ns204p559 Ns204p560 qz78 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns204p562 := nat_lit 557589992871200266310454968782723540247655799190453452431680 

noncomputable abbrev qz425 := (Enclosure.sfrac Bool.false 486193 2000)

noncomputable abbrev qz673 := (Real.log (Enclosure.sfrac Bool.false 945535532996 16000000))

noncomputable abbrev qz79 := (@HSub.hSub Real Real Real qz345 (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 486193 4000) qz673) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 972386)))))) qz425)

noncomputable abbrev qz426 := (@HSub.hSub Real Real Real qz12 qz79 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 486193 2000) (Real.log Real.pi)))

noncomputable def Ns204p563 := @Enclosure.Real.IsNear.addLit_ft_p qz426 (Enclosure.sfrac Bool.true Ns204p559 Ns204p560) 14657809649265611216489 18014398509481984000 5438452319109273 409600000000000000000 Ns204p559 Ns204p560 0 1 Ns204p562 

noncomputable def Ns204p564 := nat_lit 983668954290453603004234858496000 

noncomputable abbrev qz427 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 486193 2000) (Real.log Real.pi))

noncomputable def Ns204p565 := @Enclosure.Real.IsNear.subLit_ff_p qz79 qz427 19670853365773689001577 18014398509481984000 150815780447 25000000000000000 18675043122873 67108864000 486193 67108864000 Ns204p564 14657809649265611216489 18014398509481984000 

noncomputable def Ns204p566 := nat_lit 39341706731547378003154000 

noncomputable abbrev qz80 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 486193 4000) qz673) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 972386))))))

noncomputable def Ns204p567 := @Enclosure.Real.IsNear.subLit_ff_p qz80 qz425 24050090593033976125033 18014398509481984000 150815780447 25000000000000000 486193 2000 0 1 Ns204p566 19670853365773689001577 18014398509481984000 150815780447 25000000000000000 

noncomputable def Ns204p568 := nat_lit 54155989516507243019691120090555613184 

noncomputable def Ns204p569 := nat_lit 26564737741109360404201472 

noncomputable def Ns204p570 := nat_lit 445217119845711721743054607186370048429712065076127803893062240356478450706828276331300341529701554279009608879985524515007495113487566366926097694131371676024087137451664998400 

noncomputable def Ns204p571 := nat_lit 12828159774817503149651817742135014242921804072428108211971379453091725228632905856272302388392836198326707842062220477023957402806787335125680286254293654946726076860113879040 

noncomputable def Ns204p572 := nat_lit 748671037393226092292008392721985675772120528029691528261154306175236670277432887468840058162911406609546347502696572155800168463022952234377221662224501286281737666560 

noncomputable def Ns204p573 := BSN.log_dyadic_bound 421247532996 1469823532996 8 7 Ns204p570 67108864 20480000 Ns204p571 Ns204p572 39574789 1891071065992 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 421247532996) (BSN.artanhQ 1469823532996) 0 7 Ns204p571 Ns204p570 Ns204p572 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns204p574 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 486193 4000) qz673 486193 4000 0 1 49480679894069881 4503599627370496 2441407 50000000000000 24057160199737517653033 18014398509481984000 1186994993551 200000000000000000 (Enclosure.Real.IsNear.const Bool.false 486193 4000) (BSN.isNear_log_sfrac 945535532996 16000000 49480679894069881 4503599627370496 2441407 50000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 945535532996) qz352)) Bool.false Ns204p569 Ns204p89 1000000307200000 20480000000000000000000 49480679894069881 4503599627370496 2441407 50000000000000 (BSN.log_rat_reduce_isNear 945535532996 16000000 15 1891071065992 1048576000000 39574789 67108864 24973259072661432 36028797018963968 20480000 1000000000000000 rfl rfl rfl rfl (Ns204p573 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns204p575 := BSN.arctan_dyadic_bound_f 1000 972386 1 0 8388608 2560000 0 1 1 0 1 1 8626 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 972386) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 972386) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz428 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 972386)))

noncomputable def Ns204p576 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz428 884279719003555 562949953421312 1 2000000000000000 8626 8388608 1 2560000 7413019918772761264128 883700837942691 562949953421312 781250001 2000000000000000 qz17 (Ns204p575 rfl) rfl rfl 

noncomputable def Ns204p577 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 486193 4000) qz673) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz428)) 24057160199737517653033 18014398509481984000 1186994993551 200000000000000000 883700837942691 2251799813685248 781250001 8000000000000000 Ns204p568 24050090593033976125033 18014398509481984000 150815780447 25000000000000000 (Ns204p574 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz428) 1 4 0 1 883700837942691 562949953421312 781250001 2000000000000000 883700837942691 2251799813685248 781250001 8000000000000000 qz355 Ns204p576 rfl) 

noncomputable def Ns204p578 := @Ns204p563 Ns204p557 Ns204p558 5438452319109273 409600000000000000000 (@Ns204p565 5438452319109273 409600000000000000000 (Ns204p567 (Ns204p577 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 486193 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz425 (Real.log Real.pi) 486193 2000 0 1 38410761 33554432 1 33554432 18675043122873 67108864000 486193 67108864000 (Enclosure.Real.IsNear.const Bool.false 486193 2000) RS205to222.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns204p559 Ns204p560) 

noncomputable def Ns204p579 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz75) Bool.false Ns204p557 Ns204p558 5438452319109273 409600000000000000000 13651143269 16777216 7 524288 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz75) (@HAdd.hAdd Real Real Real qz356 qz426 (Enclosure.sfrac Bool.true Ns204p559 Ns204p560)) Bool.false Ns204p557 Ns204p558 5438452319109273 409600000000000000000 Ns204p561 (Ns204p578 rfl rfl)) 

noncomputable def Ns204p580 := nat_lit 3795650792401978741751808 

noncomputable def Ns204p581 := nat_lit 855057482329915645173656783779679623597217952333034705333953920314034624121409409963947368341942616908775355454196649144112014950400000 

noncomputable def Ns204p582 := nat_lit 606565058371292112723399957884907911670239048656596633811760456575605555800337815893775488614237999947685212628975616000000000000 

noncomputable def Ns204p583 := nat_lit 4269987686218210876270657465700985337993185967047981950057115391152563636022667319517387225790912057319235325640312491220509130752000000 

noncomputable def Ns204p584 := BSN.sin_dyadic_bound_f 53939441960 34359738368 4 3 16777216 5125001 Ns204p581 Ns204p217 Ns204p582 Ns204p583 Ns204p220 Ns204p582 16777208 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53939441960) qz357 0 3 Ns204p581 Ns204p217 Ns204p582 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53939441960) qz358 0 3 Ns204p583 Ns204p220 Ns204p582 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p585 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz75) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13651143269) qz369) Bool.false 13651143269 16777216 7 524288 Bool.true 16777208 16777216 1 2560000 (Ns204p579 rfl) (Enclosure.sfrac_false_div 13651143269 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13651143269) qz369) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns204p580) qz371) 226375608064910080 72057594037927936 Bool.false 16777208 16777216 129 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q1 13651143269 16777216 226375608064910080 72057594037927936 129 Ns204p580 Ns204p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777208 16777216 Ns204p580 Ns204p89 53939441960 34359738368 5125001 5120000 (Ns204p584 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p586 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz75) Bool.false Ns204p557 Ns204p558 5438452319109273 409600000000000000000 109209146156 134217728 1783 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz75) (@HAdd.hAdd Real Real Real qz356 qz426 (Enclosure.sfrac Bool.true Ns204p559 Ns204p560)) Bool.false Ns204p557 Ns204p558 5438452319109273 409600000000000000000 Ns204p561 (Ns204p578 rfl rfl)) 

noncomputable def Ns204p587 := Ns204p556 37263 BSN.abs_quadSignPos (BSN.cos_quad_nat3 303 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 88198828 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 177 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133909748 134217728) qz78 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz75) qz75 1) Bool.true 2097151 2097152 4503 327680000 134217664 134217728 1845 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz75) qz75 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz75)) Bool.true 2097151 2097152 4503 327680000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz75) qz75) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz75)) Bool.true 16777208 16777216 18444288 1342177280000 2097151 2097152 4503 327680000 (Ns204p585 rfl rfl) rfl)) rfl) (Ns204p586 rfl) RS205to222.d7 

noncomputable def Ns204p588 := nat_lit 84177364054988374314954907856337151482961972249030264521255749443105 

noncomputable def Ns204p589 := nat_lit 7356514496042662751127079734988420854425624906693246487159397921 

noncomputable def Ns204p590 := nat_lit 220452614358642625561380076732740653583517047735706522775642990468641 

noncomputable def Ns204p591 := BSN.sin_dyadic_bound_f 96235213 134217728 3 2 134217728 67108864 Ns204p588 Ns204p106 Ns204p589 Ns204p590 Ns204p109 Ns204p589 88198828 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 96235213) qz361 0 2 Ns204p588 Ns204p106 Ns204p589 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 96235213) qz362 0 2 Ns204p590 Ns204p109 Ns204p589 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p592 := nat_lit 9066332571715928340949803184475508071686643686956799156071476201555221684501100079438953007038061573308416 

noncomputable def Ns204p593 := nat_lit 4543210278699014355757667353064468195845973062535638486422527867617980681023310571412914756089020416 

noncomputable def Ns204p594 := nat_lit 45284429148105682562257219369475338698432841441252979065937224719050694298171448790308009475224583616331776 

noncomputable def Ns204p595 := BSN.sin_dyadic_bound_f 201734528 134217728 4 3 134217728 67108864 Ns204p592 Ns204p256 Ns204p593 Ns204p594 Ns204p259 Ns204p593 133909748 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 201734528) qz361 0 3 Ns204p592 Ns204p256 Ns204p593 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 201734528) qz362 0 3 Ns204p594 Ns204p259 Ns204p593 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p596 := nat_lit 2898934164508946786451535424397928558363343687855413939910354393679040756780863175016399435186385438375936 

noncomputable def Ns204p597 := nat_lit 2603849907513931914727706810071078958136556981446750805604745324462125870109826906541974047116230656 

noncomputable def Ns204p598 := nat_lit 17557342513395305666455373967122124880441215895158315693957537136357627653478701717888040619682301413949440 

noncomputable def Ns204p599 := BSN.cos_dyadic_bound_f 192590412 134217728 4 3 134217728 67108864 Ns204p596 Ns204p230 Ns204p597 Ns204p598 Ns204p233 Ns204p597 18182225 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 192590412) qz363 0 3 Ns204p596 Ns204p230 Ns204p597 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 192590412) qz364 0 3 Ns204p598 Ns204p233 Ns204p597 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p600 := nat_lit 5538351831096338579573943013982809182206843023215823892691207380843840550552175065834035983206423876198801 

noncomputable def Ns204p601 := nat_lit 1037680246458772738456534202964978018759622513940846046085954745232809567393297313350818945769267601 

noncomputable def Ns204p602 := nat_lit 27674112831613893901566071860669045638690109524508726474741059742362091719507621998402382669090378958889361 

noncomputable def Ns204p603 := BSN.sin_dyadic_bound_f 178376907 134217728 4 3 134217728 67108864 Ns204p600 Ns204p256 Ns204p601 Ns204p602 Ns204p259 Ns204p601 130313626 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 178376907) qz361 0 3 Ns204p600 Ns204p256 Ns204p601 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 178376907) qz362 0 3 Ns204p602 Ns204p259 Ns204p601 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p604 := Ns204p554 63380 BSN.abs_quadSignPos (BSN.cos_quad_nat0 88 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 18182225 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 19 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 130313626 134217728) qz78 rfl rfl (Ns204p587 RS205to222.d9 RS205to222.d11 RS205to222.d13 RS205to222.d17 (Ns204p591 rfl rfl) (Ns204p595 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns204p586 rfl) RS205to222.d19 RS205to222.d21 RS205to222.d23 RS205to222.d25 RS205to222.d17 (Ns204p599 rfl rfl) (Ns204p603 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns204p605 := nat_lit 127159118723376290636631172864467753267665635002254293795947509268736 

noncomputable def Ns204p606 := nat_lit 54353315397554596862538983983956443810230545954257058813246259456 

noncomputable def Ns204p607 := nat_lit 381368649539333762716168440625435346915376443914854367270216035287296 

noncomputable def Ns204p608 := BSN.cos_dyadic_bound_f 123567214 134217728 3 2 134217728 67108864 Ns204p605 Ns204p240 Ns204p606 Ns204p607 Ns204p243 Ns204p606 81242646 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 123567214) qz363 0 2 Ns204p605 Ns204p240 Ns204p606 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 123567214) qz364 0 2 Ns204p607 Ns204p243 Ns204p606 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p609 := nat_lit 8591578895107970627916025812948794899902787064201102116404948455521 

noncomputable def Ns204p610 := nat_lit 248326594374091213894148767675987487912815870177937833233567841 

noncomputable def Ns204p611 := nat_lit 25774240032135163701320289141311032724732535560862950473548378230881 

noncomputable def Ns204p612 := BSN.cos_dyadic_bound_f 63005419 134217728 3 2 134217728 67108864 Ns204p609 Ns204p240 Ns204p610 Ns204p611 Ns204p243 Ns204p610 119699083 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 63005419) qz363 0 2 Ns204p609 Ns204p240 Ns204p610 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 63005419) qz364 0 2 Ns204p611 Ns204p243 Ns204p610 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p613 := Ns204p552 85061 BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 81242646 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 84 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 119699083 134217728) qz78 rfl rfl (Ns204p604 rfl rfl) (Ns204p586 rfl) RS205to222.d27 RS205to222.d29 RS205to222.d31 RS205to222.d33 RS205to222.d17 (Ns204p608 rfl rfl) (Ns204p612 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns204p614 := nat_lit 304573724989092011999270323788990442759790110800709523875381752219105 

noncomputable def Ns204p615 := nat_lit 96264832473324561785404538034688892023404430909930228104268989921 

noncomputable def Ns204p616 := nat_lit 797537231909331791659960193052442615688555254447051723113831010780641 

noncomputable def Ns204p617 := BSN.sin_dyadic_bound_f 132719109 134217728 3 2 134217728 67108864 Ns204p614 Ns204p106 Ns204p615 Ns204p616 Ns204p109 Ns204p615 112123593 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 132719109) qz361 0 2 Ns204p614 Ns204p106 Ns204p615 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 132719109) qz362 0 2 Ns204p616 Ns204p109 Ns204p615 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p618 := Ns204p550 Bool.true 3386205 85061 Bool.true 132719109 7074237752028440 1 Bool.false 112123593 Bool.true Bool.true 43027878 94812 BSN.abs_quadSignNeg qz387 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 112123593 134217728) qz78 rfl (Ns204p613 rfl) (Ns204p586 rfl) RS205to222.d35 RS205to222.d37 RS205to222.d17 (Ns204p617 rfl rfl) rfl 

noncomputable def Ns204p619 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz75) qz75 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz75) qz75 8) 43027878 134217728 94812 134217728 43027878 134217728 94812 134217728 11550208051642368 21513939 33554432 23703 16777216 (Ns204p618 rfl rfl rfl rfl) 

noncomputable def Ns204p620 := @Enclosure.Real.IsNear.mulLit_ff qz672 (Zeta.RiemannSiegel.correction qz77) 2828347 8388608 1 8388608 38851589882475 70368744177664 2658261683997 21990232555520000 109885777689328518825 590295810358705651712 

noncomputable abbrev qz674 := (@HPow.hPow Real Real Real qz7 qz76 qz9)

noncomputable def Ns204p621 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz674 1 1 0 1 2828347 8388608 1 8388608 2828347 8388608 1 8388608 

noncomputable def Ns204p622 := @Enclosure.Real.IsNear.sqrt_image qz76 1298221366161 16777216000 486193 16777216000 73791144 73791173 8388608 (@Enclosure.Real.IsNear.of_eq qz76 (@HMul.hMul Real Real Real qz5 qz75 qz3) Bool.false 1298221366161 16777216000 486193 16777216000 (BSN.t_div_two_pi_mk qz75 486193 1000 qz78) (@Enclosure.Real.IsNear.mulLit_ff qz75 qz3 486193 1000 0 1 2670177 16777216 1 16777216 1298221366161 16777216000 486193 16777216000 (Enclosure.Real.IsNear.const Bool.false 486193 1000) RS205to222.d40 rfl)) 

noncomputable abbrev qz865 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 486193 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz675 := qz865

noncomputable abbrev qz429 := qz675

noncomputable abbrev qz81 := qz429

noncomputable def Ns204p623 := @Enclosure.Real.IsNear.sqrt_image qz81 147582317 16777216 29 16777216 24879810 24879816 8388608 (@Enclosure.Real.IsNear.recentre' qz81 Bool.false 147582317 16777216 29 16777216 147582317 16777216 29 16777216 (Ns204p622 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns204p624 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz81) 24879813 8388608 3 8388608 2828346 2828348 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz81) Bool.false 49759626 16777216 6 16777216 24879813 8388608 3 8388608 (Ns204p623 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns204p625 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz81)) Bool.false 5656694 16777216 2 16777216 2828347 8388608 1 8388608 (Ns204p624 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz82 := (@HMul.hMul Real Real Real qz342 qz340 qz423)

noncomputable abbrev qz676 := (@HMul.hMul Real Real Real qz844 qz864 qz864)

noncomputable abbrev qz430 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz676 qz671) qz640)

noncomputable abbrev qz83 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz430))

noncomputable def Ns204p626 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz77) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz82)) qz83) Bool.false 38851589882475 

noncomputable def Ns204p627 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz82)) qz83 58137129 16777216 2277 

noncomputable def Ns204p628 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz82)) Bool.false 58137129 16777216 2277 16777216 58137129 16777216 2277 

noncomputable def Ns204p629 := @Enclosure.Real.IsNear.recentre' (Real.cos qz82) Bool.false 4841570 16777216 485257216 42949672960000 2420785 8388608 118471 10485760000 

noncomputable def Ns204p630 := @Enclosure.Real.IsNear.cos_image qz82 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 83972189) qz369) Bool.false 83972189 16777216 183 16777216 Bool.false 4841570 16777216 1 

noncomputable def Ns204p631 := nat_lit 782596186977078263558862731 

noncomputable def Ns204p632 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz77 884279719003555 140737488355328 1 500000000000000 13364589 16777216 29 16777216 11818035005518002113895 2361183241434822606848 Ns204p631 

noncomputable def Ns204p633 := @Enclosure.Real.IsNear.subLit_ff_p qz81 qz1 147582317 16777216 29 16777216 8 1 0 1 13364589 13364589 16777216 29 

noncomputable def Ns204p634 := @Ns204p633 16777216 (@Enclosure.Real.IsNear.recentre' qz81 Bool.false 147582317 16777216 29 16777216 147582317 16777216 29 16777216 (Ns204p622 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns204p635 := @Enclosure.Real.IsNear.recentre' qz82 Bool.false 11818035005518002113895 2361183241434822606848 Ns204p631 Ns204p521 83972189 16777216 183 16777216 (@Ns204p632 Ns204p521 RS205to222.d39 (Ns204p634 rfl rfl) rfl) 

noncomputable def Ns204p636 := nat_lit 10236430241361152409795424238345406794721 

noncomputable def Ns204p637 := BSN.sin_dyadic_bound_f 10058590617 34359738368 2 1 16777216 5125001 Ns204p636 Ns204p419 Ns204p636 Ns204p636 Ns204p420 Ns204p636 4841570 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 10058590617) qz357 0 1 Ns204p636 Ns204p419 Ns204p636 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 10058590617) qz358 0 1 Ns204p636 Ns204p420 Ns204p636 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p638 := @Ns204p630 2560000 (Ns204p635 rfl) (Enclosure.sfrac_false_div 83972189 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 83972189) qz369) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 707810389967300322131968) qz371) 226375608064910080 72057594037927936 Bool.false 4841570 16777216 0 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q3 83972189 16777216 226375608064910080 72057594037927936 0 707810389967300322131968 Ns204p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 4841570 16777216 707810389967300322131968 Ns204p89 10058590617 34359738368 5125001 5120000 (Ns204p637 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p639 := @Enclosure.Real.IsNear.inv_image (Real.cos qz82) 2420785 8388608 118471 10485760000 29067426 29069703 8388608 (Ns204p629 (Ns204p638 rfl rfl) rfl) rfl 

noncomputable def Ns204p640 := @Enclosure.Real.IsNear.recentre' qz83 Bool.false 1336550 8388608 

noncomputable abbrev qz84 := (@HMul.hMul Real Real Real qz342 qz340 qz430)

noncomputable def Ns204p641 := @Enclosure.Real.IsNear.cos_image qz84 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 23669047)) qz369) Bool.true 23669047 16777216 

noncomputable def Ns204p642 := nat_lit 55886958678790325220427051045 

noncomputable def Ns204p643 := nat_lit 34047960744360168282119799236375837 

noncomputable def Ns204p644 := @Enclosure.Real.IsNear.recentre' qz84 Bool.true Ns204p642 Ns204p533 Ns204p643 

noncomputable abbrev qz85 := qz430

noncomputable def Ns204p645 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz85 884279719003555 140737488355328 1 500000000000000 63200543309719 

noncomputable abbrev qz431 := (@HSub.hSub Real Real Real qz634 qz676 qz671)

noncomputable abbrev qz86 := qz431

noncomputable def Ns204p646 := @Enclosure.Real.IsNear.subLit_tf qz86 qz27 45608357265303 281474976710656 1261686267 281474976710656 1 16 

noncomputable abbrev qz432 := qz676

noncomputable abbrev qz87 := qz432

noncomputable def Ns204p647 := @Enclosure.Real.IsNear.subLit_ff_n qz87 qz77 178612239138921 281474976710656 775147003 281474976710656 13364589 16777216 29 16777216 

noncomputable def Ns204p648 := @Enclosure.Real.IsNear.mulLit_ff qz77 qz77 13364589 16777216 29 16777216 13364589 16777216 29 16777216 178612239138921 281474976710656 

noncomputable def Ns204p649 := nat_lit 39412243476123383653475800229534979510203403169939451178668550796959926164959281754439757169121 

noncomputable def Ns204p650 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600 

noncomputable def Ns204p651 := nat_lit 30915000972085929840439462942962735262154548091162710286785330707638602237518723619062241 

noncomputable def Ns204p652 := nat_lit 238725813188799555503464873537570871414200677089467695598049548234435038266649035667982838759905 

noncomputable def Ns204p653 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600 

noncomputable def Ns204p654 := BSN.cos_dyadic_bound_f 23669047 16777216 4 3 8388608 2560000 Ns204p649 Ns204p650 Ns204p651 Ns204p652 Ns204p653 Ns204p651 1336550 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 23669047) (BSN.cosEvenQ 16777216) 0 3 Ns204p649 Ns204p650 Ns204p651 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 23669047) (BSN.cosOddQ 16777216) 0 3 Ns204p652 Ns204p653 Ns204p651 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p655 := @Ns204p640 615108608 21474836480000 668275 4194304 150173 5242880000 (@Ns204p641 237 8388608 Bool.false 1336550 8388608 1 2560000 (@Ns204p644 Ns204p536 23669047 16777216 237 8388608 (@Ns204p645 281474976710656 1261686267 281474976710656 Ns204p642 Ns204p533 Ns204p643 Ns204p536 RS205to222.d39 (@Ns204p646 0 1 1011208692955504 63200543309719 281474976710656 1261686267 281474976710656 (@Ns204p647 765181261245157736448 45608357265303 281474976710656 1261686267 281474976710656 (@Ns204p648 775147003 281474976710656 (Ns204p634 rfl rfl) (Ns204p634 rfl rfl) rfl) (Ns204p634 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 23669047 16777216) (BSN.cos_neg_of_bound 23669047 16777216 Bool.false 1336550 8388608 1 2560000 (Ns204p654 rfl rfl)) rfl rfl) 

noncomputable def Ns204p656 := @Ns204p620 15061260478495640787 368934881474191032320000 (Ns204p621 qz29 (@Enclosure.Real.IsNear.of_eq qz674 (@Inv.inv Real Real.instInv (Real.sqrt qz81)) Bool.false 2828347 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz76 (BSN.t_div_two_pi_nonneg qz75 486193 1000 qz78)) Ns204p625) rfl) (@Ns204p626 70368744177664 2658261683997 21990232555520000 (BSN.correction_mk qz77 (BSN.cos_two_pi_p_ne_zero_mk qz75 486193 1000 8 qz78 rfl rfl (@BSN.floor_sqrt_eq_dec qz75 486193 1000 8 qz78 rfl rfl rfl))) (@Ns204p627 16777216 668275 4194304 150173 5242880000 38851589882475 70368744177664 2658261683997 21990232555520000 (@Ns204p628 16777216 (Ns204p639 rfl rfl rfl rfl rfl) rfl) (Ns204p655 rfl) rfl)) 

noncomputable def Ns204p657 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz75) (hardyZApproximantRS₀ qz75) Bool.true 488362995125545633449 590295810358705651712 536295742741986200787 368934881474191032320000 (@Eq.refl Real (hardyZApproximantRS₀ qz75)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz75) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz75) qz75 8) (@HMul.hMul Real Real Real qz5 qz672 (Zeta.RiemannSiegel.correction qz77))) Bool.true 488362995125545633449 590295810358705651712 536295742741986200787 368934881474191032320000 (BSN.hardyZApproximantRS₀_eq qz75 8 (@BSN.floor_sqrt_eq_dec qz75 486193 1000 8 qz78 rfl rfl rfl)) (@Ns204p549 488362995125545633449 590295810358705651712 536295742741986200787 368934881474191032320000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz75) qz75 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz75) qz75 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz75) qz75 8)) Bool.true 21513939 33554432 23703 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz75) qz75 8) (Ns204p619 (Ns204p618 rfl rfl rfl rfl) rfl rfl)) (Ns204p656 rfl) rfl rfl)) 

theorem RS205to222.d47 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz75) Bool.true 488362995125545633449 590295810358705651712 536295742741986200787 368934881474191032320000 := Ns204p657 

noncomputable def Ns204p658 := nat_lit 118598266657160524906308304896 

noncomputable abbrev qz866 := (Enclosure.sfrac Bool.false 487638 1000)

noncomputable abbrev qz677 := qz866

noncomputable abbrev qz433 := qz677

noncomputable abbrev qz88 := qz433

noncomputable abbrev qz867 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 487638 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz678 := qz867

noncomputable abbrev qz434 := qz678

noncomputable abbrev qz89 := qz434

noncomputable abbrev qz868 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 487638 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz679 := qz868

noncomputable abbrev qz435 := qz679

noncomputable abbrev qz90 := qz435

noncomputable abbrev qz680 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz89 qz9))

noncomputable def Ns204p659 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz88) qz88 8) (@HMul.hMul Real Real Real qz5 qz680 (Zeta.RiemannSiegel.correction qz90)) 106886727 33554432 5943 4194304 226238596586852110311 1180591620717411303424 38510488097029843 1180591620717411303424 Ns204p658 

noncomputable def Ns204p660 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz88) qz88 Real.sin BSN.quadSignNeg 7 8 487638 1000 125 134217728 67108864 2251799813685248 Bool.false 109630996464 1788 279097919 53 47453128 8 

noncomputable def Ns204p661 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz88) qz88 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 487638 1000 36 84 134217728 67108864 2251799813685248 Bool.false 109630996464 1788 

noncomputable def Ns204p662 := Ns204p661 240485871 53 54794152 8 261175631 53 50729528 8 Bool.false 148046185 63563 Bool.true 49218989 Bool.true 18553898 7074237752028440 1 Bool.false 125293859 Bool.false Bool.false 132937348 Bool.false Bool.false 249442773 

noncomputable def Ns204p663 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz88) qz88 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 487638 1000 89 20 134217728 67108864 2251799813685248 Bool.false 109630996464 1788 

noncomputable def Ns204p664 := Ns204p663 186065264 53 67108856 8 216015088 53 60023992 8 Bool.false 154307233 37368 Bool.false 134747699 Bool.false 77256699 7074237752028440 1 Bool.false 113225787 Bool.true Bool.false 112590137 Bool.false Bool.false 148046185 

noncomputable def Ns204p665 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz88) qz88 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 487638 1000 304 178 134217728 67108864 2251799813685248 Bool.false 109630996464 1788 

noncomputable def Ns204p666 := Ns204p665 93032624 53 94906264 8 147453232 53 77490640 16 Bool.false 134217712 1845 Bool.false 172824665 Bool.false 199686202 7074237752028440 1 Bool.false 37498250 Bool.false Bool.false 11129717 Bool.true Bool.false 154307233 

noncomputable def Ns204p667 := nat_lit 309136217383901581928912572131038570681316167271689779 

noncomputable def Ns204p668 := nat_lit 378465598945634675776001551732081924379341383270400 

noncomputable def Ns204p669 := nat_lit 13235187583957327763862529520640000 

noncomputable def Ns204p670 := nat_lit 38723901417491925735521521864811089920 

noncomputable abbrev qz436 := (@Eq.refl Real qz677)

noncomputable abbrev qz91 := qz436

noncomputable def Ns204p671 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz88 487638 1000 951164276176 16000000 975276 4000 2000 Ns204p669 Ns204p670 qz91 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns204p672 := nat_lit 56979987588200739581137165295193029347980195951517860065280 

noncomputable abbrev qz437 := (Enclosure.sfrac Bool.false 487638 2000)

noncomputable abbrev qz681 := (Real.log (Enclosure.sfrac Bool.false 951164276176 16000000))

noncomputable abbrev qz92 := (@HSub.hSub Real Real Real qz345 (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 487638 4000) qz681) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 975276)))))) qz437)

noncomputable abbrev qz438 := (@HSub.hSub Real Real Real qz12 qz92 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 487638 2000) (Real.log Real.pi)))

noncomputable def Ns204p673 := @Enclosure.Real.IsNear.addLit_ft_p qz438 (Enclosure.sfrac Bool.true Ns204p669 Ns204p670) 1471442942080642665559 1801439850948198400 2727248450703459 204800000000000000000 Ns204p669 Ns204p670 0 1 Ns204p672 

noncomputable def Ns204p674 := nat_lit 246867160709624314188991037440000 

noncomputable abbrev qz439 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 487638 2000) (Real.log Real.pi))

noncomputable def Ns204p675 := @Enclosure.Real.IsNear.subLit_ff_p qz92 qz439 9871186128986539326899 9007199254740992000 1210054076691 200000000000000000 9365273336259 33554432000 243819 33554432000 Ns204p674 1471442942080642665559 1801439850948198400 

noncomputable def Ns204p676 := nat_lit 19742372257973078653798000 

noncomputable abbrev qz93 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 487638 4000) qz681) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 975276))))))

noncomputable def Ns204p677 := @Enclosure.Real.IsNear.subLit_ff_p qz93 qz437 12067312444078233255347 9007199254740992000 1210054076691 200000000000000000 487638 2000 0 1 Ns204p676 9871186128986539326899 9007199254740992000 1210054076691 200000000000000000 

noncomputable def Ns204p678 := nat_lit 27173171913257040319440477031871021056 

noncomputable def Ns204p679 := nat_lit 26579088479336374999187456 

noncomputable def Ns204p680 := nat_lit 469690135349774060084574474775702378425685129016220967004933552186200055148990333955207407918286776350515667546735554950393662906597314478787624857776704659630752418534680166400 

noncomputable def Ns204p681 := nat_lit 13805496965301001352542421691999351417674843694128769539121402214033789688594247878973131219272466103021527845869086112045216442267489060494541026602347252402596319017660579840 

noncomputable def Ns204p682 := nat_lit 901563077384235095734480821457824675622277350755191699120351448460593260014329073581397883408817956450125410739852378748589718331436589864095876330838564172344338677760 

noncomputable def Ns204p683 := BSN.log_dyadic_bound 426876276176 1475452276176 8 7 Ns204p680 67108864 20480000 Ns204p681 Ns204p682 39973102 1902328552352 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 426876276176) (BSN.artanhQ 1475452276176) 0 7 Ns204p681 Ns204p680 Ns204p682 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns204p684 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 487638 4000) qz681 487638 4000 0 1 49507410227016313 4503599627370496 2441407 50000000000000 12070847254140890419347 9007199254740992000 595261413333 100000000000000000 (Enclosure.Real.IsNear.const Bool.false 487638 4000) (BSN.isNear_log_sfrac 951164276176 16000000 49507410227016313 4503599627370496 2441407 50000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 951164276176) qz352)) Bool.false Ns204p679 Ns204p89 1000000307200000 20480000000000000000000 49507410227016313 4503599627370496 2441407 50000000000000 (BSN.log_rat_reduce_isNear 951164276176 16000000 15 1902328552352 1048576000000 39973102 67108864 24973259072661432 36028797018963968 20480000 1000000000000000 rfl rfl rfl rfl (Ns204p683 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns204p685 := BSN.arctan_dyadic_bound_f 1000 975276 1 0 8388608 2560000 0 1 1 0 1 1 8601 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 975276) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 975276) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz440 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 975276)))

noncomputable def Ns204p686 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz440 884279719003555 562949953421312 1 2000000000000000 8601 8388608 1 2560000 7413033992521596796928 883702515664291 562949953421312 781250001 2000000000000000 qz17 (Ns204p685 rfl) rfl rfl 

noncomputable def Ns204p687 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 487638 4000) qz681) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz440)) 12070847254140890419347 9007199254740992000 595261413333 100000000000000000 883702515664291 2251799813685248 781250001 8000000000000000 Ns204p678 12067312444078233255347 9007199254740992000 1210054076691 200000000000000000 (Ns204p684 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz440) 1 4 0 1 883702515664291 562949953421312 781250001 2000000000000000 883702515664291 2251799813685248 781250001 8000000000000000 qz355 Ns204p686 rfl) 

noncomputable def Ns204p688 := @Ns204p673 Ns204p667 Ns204p668 2727248450703459 204800000000000000000 (@Ns204p675 2727248450703459 204800000000000000000 (Ns204p677 (Ns204p687 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 487638 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz437 (Real.log Real.pi) 487638 2000 0 1 38410761 33554432 1 33554432 9365273336259 33554432000 243819 33554432000 (Enclosure.Real.IsNear.const Bool.false 487638 2000) RS205to222.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns204p669 Ns204p670) 

noncomputable def Ns204p689 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz88) Bool.false Ns204p667 Ns204p668 2727248450703459 204800000000000000000 6851937279 8388608 7 524288 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz88) (@HAdd.hAdd Real Real Real qz356 qz438 (Enclosure.sfrac Bool.true Ns204p669 Ns204p670)) Bool.false Ns204p667 Ns204p668 2727248450703459 204800000000000000000 Ns204p671 (Ns204p688 rfl rfl)) 

noncomputable def Ns204p690 := BSN.cos_dyadic_bound_f 16669378 34359738368 1 0 16777216 5125001 0 1 1 0 1 1 16777214 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 16669378) qz642 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 16669378) qz643 0 0 rfl) rfl rfl 

noncomputable def Ns204p691 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz88) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6851937279) qz359) Bool.false 6851937279 8388608 7 524288 Bool.false 16777214 16777216 1 2560000 (Ns204p689 rfl) (Enclosure.sfrac_false_div 6851937279 8388608) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6851937279) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 586501605136676159488) qz360) 226375608064910080 72057594037927936 Bool.false 16777214 16777216 130 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q0 6851937279 8388608 226375608064910080 72057594037927936 130 586501605136676159488 Ns204p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777214 16777216 586501605136676159488 Ns204p100 16669378 34359738368 5125001 5120000 (Ns204p690 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p692 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz88) Bool.false Ns204p667 Ns204p668 2727248450703459 204800000000000000000 109630996464 134217728 1788 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz88) (@HAdd.hAdd Real Real Real qz356 qz438 (Enclosure.sfrac Bool.true Ns204p669 Ns204p670)) Bool.false Ns204p667 Ns204p668 2727248450703459 204800000000000000000 Ns204p671 (Ns204p688 rfl rfl)) 

noncomputable def Ns204p693 := Ns204p666 37368 BSN.abs_quadSignPos (BSN.cos_quad_nat0 304 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 37498250 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 178 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 11129717 134217728) qz91 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz88) qz88 1) Bool.false 8388607 8388608 4503 327680000 134217712 134217728 1845 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz88) qz88 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz88)) Bool.false 8388607 8388608 4503 327680000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz88) qz88) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz88)) Bool.false 16777214 16777216 18444288 1342177280000 8388607 8388608 4503 327680000 (Ns204p691 rfl rfl) rfl)) rfl) (Ns204p692 rfl) RS205to222.d7 

noncomputable def Ns204p694 := nat_lit 1878183056582131292666028852100929068597402972455440392105942552060770381407474071950197245119556019390625 

noncomputable def Ns204p695 := nat_lit 710016897872557257959638253494609028584905636886134437497833206649839867584494641313575332275390625 

noncomputable def Ns204p696 := nat_lit 11381897264314486538129907287761284980426078188390646961501465245225291017376166922735032028505146188990625 

noncomputable def Ns204p697 := BSN.cos_dyadic_bound_f 172824665 134217728 4 3 134217728 67108864 Ns204p694 Ns204p230 Ns204p695 Ns204p696 Ns204p233 Ns204p695 37498250 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 172824665) qz363 0 3 Ns204p694 Ns204p230 Ns204p695 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 172824665) qz364 0 3 Ns204p696 Ns204p233 Ns204p695 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p698 := nat_lit 3351677750558179077542735566329735725480001753578271238190544168097777604596790152153880748160693623525376 

noncomputable def Ns204p699 := nat_lit 4019543029402628766753301369612905700463747927194342930790087154181309458646974350316722095625015296 

noncomputable def Ns204p700 := nat_lit 20294072892976693272131836109776621270787506742000967607664085452630820174660815101338653734169133131960320 

noncomputable def Ns204p701 := BSN.cos_dyadic_bound_f 199686202 134217728 4 3 134217728 67108864 Ns204p698 Ns204p230 Ns204p699 Ns204p700 Ns204p233 Ns204p699 11129717 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 199686202) qz363 0 3 Ns204p698 Ns204p230 Ns204p699 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 199686202) qz364 0 3 Ns204p700 Ns204p233 Ns204p699 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p702 := nat_lit 323632868615020457415811379646059054379663730095232882365653414221345 

noncomputable def Ns204p703 := nat_lit 108685313401978328016420044884980635479273772382493183021622138401 

noncomputable def Ns204p704 := nat_lit 847433927293831328319860361857483745203581421284609702947057268069921 

noncomputable def Ns204p705 := BSN.sin_dyadic_bound_f 134747699 134217728 3 2 134217728 67108864 Ns204p702 Ns204p106 Ns204p703 Ns204p704 Ns204p109 Ns204p703 113225787 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 134747699) qz361 0 2 Ns204p702 Ns204p106 Ns204p703 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 134747699) qz362 0 2 Ns204p704 Ns204p109 Ns204p703 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p706 := nat_lit 19423244702206472614563888314297511760115866388749012917318396032481 

noncomputable def Ns204p707 := nat_lit 1269080533389335062642965911426371395867765041147691399110866401 

noncomputable def Ns204p708 := nat_lit 58267195945552639173566379011069682537555863636164743369156966364641 

noncomputable def Ns204p709 := BSN.cos_dyadic_bound_f 77256699 134217728 3 2 134217728 67108864 Ns204p706 Ns204p240 Ns204p707 Ns204p708 Ns204p243 Ns204p707 112590137 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 77256699) qz363 0 2 Ns204p706 Ns204p240 Ns204p707 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 77256699) qz364 0 2 Ns204p708 Ns204p243 Ns204p707 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p710 := Ns204p664 63563 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 89 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 113225787 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 20 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 112590137 134217728) qz91 rfl rfl (Ns204p693 RS205to222.d9 RS205to222.d11 RS205to222.d13 RS205to222.d17 (Ns204p697 rfl rfl) (Ns204p701 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns204p692 rfl) RS205to222.d19 RS205to222.d21 RS205to222.d23 RS205to222.d25 RS205to222.d17 (Ns204p705 rfl rfl) (Ns204p709 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns204p711 := nat_lit 3199515680645971728879545679495751927866059121811009169639109968161 

noncomputable def Ns204p712 := nat_lit 34439870474220282718065534265170704698364667421554519046766881 

noncomputable def Ns204p713 := nat_lit 9598478162196966746073200907418725442188780636098184399879236370721 

noncomputable def Ns204p714 := BSN.cos_dyadic_bound_f 49218989 134217728 3 2 134217728 67108864 Ns204p711 Ns204p240 Ns204p712 Ns204p713 Ns204p243 Ns204p712 125293859 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 49218989) qz363 0 2 Ns204p711 Ns204p240 Ns204p712 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 49218989) qz364 0 2 Ns204p713 Ns204p243 Ns204p712 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p715 := nat_lit 118506087197878347109879315216 

noncomputable def Ns204p716 := BSN.cos_dyadic_bound_f 18553898 134217728 2 1 134217728 67108864 Ns204p715 Ns204p125 Ns204p715 Ns204p715 Ns204p126 Ns204p715 132937348 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 18553898) qz363 0 1 Ns204p715 Ns204p125 Ns204p715 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 18553898) qz364 0 1 Ns204p715 Ns204p126 Ns204p715 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p717 := Ns204p662 85308 BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 125293859 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 84 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 132937348 134217728) qz91 rfl rfl (Ns204p710 rfl rfl) (Ns204p692 rfl) RS205to222.d27 RS205to222.d29 RS205to222.d31 RS205to222.d33 RS205to222.d17 (Ns204p714 rfl rfl) (Ns204p716 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns204p718 := nat_lit 166737347797247026573245353004961921522769205725340393505653794423040 

noncomputable def Ns204p719 := nat_lit 28858436308786906300162680766559297551498740936584751686075433216 

noncomputable def Ns204p720 := nat_lit 436646330572099414605442327815563936554074064652470369583506291835136 

noncomputable def Ns204p721 := BSN.sin_dyadic_bound_f 114165294 134217728 3 2 134217728 67108864 Ns204p718 Ns204p106 Ns204p719 Ns204p720 Ns204p109 Ns204p719 100888078 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 114165294) qz361 0 2 Ns204p718 Ns204p106 Ns204p719 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 114165294) qz362 0 2 Ns204p720 Ns204p109 Ns204p719 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p722 := Ns204p660 Bool.false 249442773 85308 Bool.true 114165294 7074237752028440 1 Bool.false 100888078 Bool.true Bool.false 213773454 95088 BSN.abs_quadSignNeg qz387 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 100888078 134217728) qz91 rfl (Ns204p717 rfl) (Ns204p692 rfl) RS205to222.d35 RS205to222.d37 RS205to222.d17 (Ns204p721 rfl rfl) rfl 

noncomputable def Ns204p723 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz88) qz88 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz88) qz88 8) 213773454 134217728 95088 134217728 213773454 134217728 95088 134217728 57384374605185024 106886727 33554432 5943 4194304 (Ns204p722 rfl rfl rfl rfl) 

noncomputable def Ns204p724 := @Enclosure.Real.IsNear.mulLit_ff qz680 (Zeta.RiemannSiegel.correction qz90) 2826249 8388608 1 8388608 80049067363439 140737488355328 4249274549941 43980465111040000 226238596586852110311 1180591620717411303424 

noncomputable abbrev qz682 := (@HPow.hPow Real Real Real qz7 qz89 qz9)

noncomputable def Ns204p725 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz682 1 1 0 1 2826249 8388608 1 8388608 2826249 8388608 1 8388608 

noncomputable def Ns204p726 := @Enclosure.Real.IsNear.sqrt_image qz89 651039885963 8388608000 243819 8388608000 73900719 73900748 8388608 (@Enclosure.Real.IsNear.of_eq qz89 (@HMul.hMul Real Real Real qz5 qz88 qz3) Bool.false 651039885963 8388608000 243819 8388608000 (BSN.t_div_two_pi_mk qz88 487638 1000 qz91) (@Enclosure.Real.IsNear.mulLit_ff qz88 qz3 487638 1000 0 1 2670177 16777216 1 16777216 651039885963 8388608000 243819 8388608000 (Enclosure.Real.IsNear.const Bool.false 487638 1000) RS205to222.d40 rfl)) 

noncomputable abbrev qz869 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 487638 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz683 := qz869

noncomputable abbrev qz441 := qz683

noncomputable abbrev qz94 := qz441

noncomputable def Ns204p727 := @Enclosure.Real.IsNear.sqrt_image qz94 147801467 16777216 29 16777216 24898276 24898282 8388608 (@Enclosure.Real.IsNear.recentre' qz94 Bool.false 147801467 16777216 29 16777216 147801467 16777216 29 16777216 (Ns204p726 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns204p728 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz94) 24898279 8388608 3 8388608 2826248 2826250 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz94) Bool.false 49796558 16777216 6 16777216 24898279 8388608 3 8388608 (Ns204p727 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns204p729 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz94)) Bool.false 5652498 16777216 2 16777216 2826249 8388608 1 8388608 (Ns204p728 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz95 := (@HMul.hMul Real Real Real qz342 qz340 qz435)

noncomputable abbrev qz684 := (@HMul.hMul Real Real Real qz844 qz868 qz868)

noncomputable abbrev qz442 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz684 qz679) qz640)

noncomputable abbrev qz96 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz442))

noncomputable def Ns204p730 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz90) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz95)) qz96) Bool.false 80049067363439 

noncomputable def Ns204p731 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz95)) qz96 45826619 16777216 1415 

noncomputable def Ns204p732 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz95)) Bool.false 45826619 16777216 1415 16777216 45826619 16777216 1415 

noncomputable def Ns204p733 := @Enclosure.Real.IsNear.recentre' (Real.cos qz95) Bool.false 6142172 16777216 485257216 42949672960000 1535543 4194304 118471 10485760000 

noncomputable def Ns204p734 := @Enclosure.Real.IsNear.cos_image qz95 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 85349149) qz369) Bool.false 85349149 16777216 183 16777216 Bool.false 6142172 16777216 1 

noncomputable def Ns204p735 := nat_lit 782596186978960747724699531 

noncomputable def Ns204p736 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz90 884279719003555 140737488355328 1 500000000000000 13583739 16777216 29 16777216 12011824905937631192145 2361183241434822606848 Ns204p735 

noncomputable def Ns204p737 := @Enclosure.Real.IsNear.subLit_ff_p qz94 qz1 147801467 16777216 29 16777216 8 1 0 1 13583739 13583739 16777216 29 

noncomputable def Ns204p738 := @Ns204p737 16777216 (@Enclosure.Real.IsNear.recentre' qz94 Bool.false 147801467 16777216 29 16777216 147801467 16777216 29 16777216 (Ns204p726 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns204p739 := @Enclosure.Real.IsNear.recentre' qz95 Bool.false 12011824905937631192145 2361183241434822606848 Ns204p735 Ns204p521 85349149 16777216 183 16777216 (@Ns204p736 Ns204p521 RS205to222.d39 (Ns204p738 rfl rfl) rfl) 

noncomputable def Ns204p740 := nat_lit 27509028402479249012889858813685887552481 

noncomputable def Ns204p741 := BSN.sin_dyadic_bound_f 12878604697 34359738368 2 1 16777216 5125001 Ns204p740 Ns204p419 Ns204p740 Ns204p740 Ns204p420 Ns204p740 6142172 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 12878604697) qz357 0 1 Ns204p740 Ns204p419 Ns204p740 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 12878604697) qz358 0 1 Ns204p740 Ns204p420 Ns204p740 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p742 := @Ns204p734 2560000 (Ns204p739 rfl) (Enclosure.sfrac_false_div 85349149 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 85349149) qz369) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 906251239340230823641088) qz371) 226375608064910080 72057594037927936 Bool.false 6142172 16777216 0 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q3 85349149 16777216 226375608064910080 72057594037927936 0 906251239340230823641088 Ns204p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 6142172 16777216 906251239340230823641088 Ns204p89 12878604697 34359738368 5125001 5120000 (Ns204p741 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p743 := @Enclosure.Real.IsNear.inv_image (Real.cos qz95) 1535543 4194304 118471 10485760000 22912602 22914017 8388608 (Ns204p733 (Ns204p742 rfl rfl) rfl) rfl 

noncomputable def Ns204p744 := @Enclosure.Real.IsNear.recentre' qz96 Bool.false 1746781 8388608 

noncomputable abbrev qz97 := (@HMul.hMul Real Real Real qz342 qz340 qz442)

noncomputable def Ns204p745 := @Enclosure.Real.IsNear.cos_image qz97 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 22834271)) qz369) Bool.true 22834271 16777216 

noncomputable def Ns204p746 := nat_lit 53915899897153430867089537045 

noncomputable def Ns204p747 := nat_lit 34390972653042757473397862758701137 

noncomputable def Ns204p748 := @Enclosure.Real.IsNear.recentre' qz97 Bool.true Ns204p746 Ns204p533 Ns204p747 

noncomputable abbrev qz98 := qz442

noncomputable def Ns204p749 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz98 884279719003555 140737488355328 1 500000000000000 60971544114919 

noncomputable abbrev qz443 := (@HSub.hSub Real Real Real qz634 qz684 qz679)

noncomputable abbrev qz99 := qz443

noncomputable def Ns204p750 := @Enclosure.Real.IsNear.subLit_tf qz99 qz27 43379358070503 281474976710656 1274396967 281474976710656 1 16 

noncomputable abbrev qz444 := qz684

noncomputable abbrev qz100 := qz444

noncomputable def Ns204p751 := @Enclosure.Real.IsNear.subLit_ff_n qz100 qz90 184517965220121 281474976710656 787857703 281474976710656 13583739 16777216 29 16777216 

noncomputable def Ns204p752 := @Enclosure.Real.IsNear.mulLit_ff qz90 qz90 13583739 16777216 29 16777216 13583739 16777216 29 16777216 184517965220121 281474976710656 

noncomputable def Ns204p753 := nat_lit 36259649906095245931701222114090820561576604116586404413738241 

noncomputable def Ns204p754 := nat_lit 253092741970790968397859029543733109897246971520789871559966720 

noncomputable def Ns204p755 := nat_lit 73908979890829445018457744406738875351565786827110509743361 

noncomputable def Ns204p756 := nat_lit 108631131758504078905066750853458983934026680776104992221728001 

noncomputable def Ns204p757 := nat_lit 11389173388685593577903656329467989945376113718435544220198502400 

noncomputable def Ns204p758 := BSN.cos_dyadic_bound_f 22834271 16777216 3 2 8388608 2560000 Ns204p753 Ns204p754 Ns204p755 Ns204p756 Ns204p757 Ns204p755 1746781 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 22834271) (BSN.cosEvenQ 16777216) 0 2 Ns204p753 Ns204p754 Ns204p755 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 22834271) (BSN.cosOddQ 16777216) 0 2 Ns204p756 Ns204p757 Ns204p755 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p759 := @Ns204p744 1243017216 42949672960000 1746781 8388608 303471 10485760000 (@Ns204p745 479 16777216 Bool.false 1746781 8388608 1 2560000 (@Ns204p748 Ns204p536 22834271 16777216 479 16777216 (@Ns204p749 281474976710656 1274396967 281474976710656 Ns204p746 Ns204p533 Ns204p747 Ns204p536 RS205to222.d39 (@Ns204p750 0 1 975544705838704 60971544114919 281474976710656 1274396967 281474976710656 (@Ns204p751 727784860290172059648 43379358070503 281474976710656 1274396967 281474976710656 (@Ns204p752 787857703 281474976710656 (Ns204p738 rfl rfl) (Ns204p738 rfl rfl) rfl) (Ns204p738 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 22834271 16777216) (BSN.cos_neg_of_bound 22834271 16777216 Bool.false 1746781 8388608 1 2560000 (Ns204p758 rfl rfl)) rfl rfl) 

noncomputable def Ns204p760 := @Ns204p724 38510488097029843 1180591620717411303424 (Ns204p725 qz29 (@Enclosure.Real.IsNear.of_eq qz682 (@Inv.inv Real Real.instInv (Real.sqrt qz94)) Bool.false 2826249 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz89 (BSN.t_div_two_pi_nonneg qz88 487638 1000 qz91)) Ns204p729) rfl) (@Ns204p730 140737488355328 4249274549941 43980465111040000 (BSN.correction_mk qz90 (BSN.cos_two_pi_p_ne_zero_mk qz88 487638 1000 8 qz91 rfl rfl (@BSN.floor_sqrt_eq_dec qz88 487638 1000 8 qz91 rfl rfl rfl))) (@Ns204p731 16777216 1746781 8388608 303471 10485760000 80049067363439 140737488355328 4249274549941 43980465111040000 (@Ns204p732 16777216 (Ns204p743 rfl rfl rfl rfl rfl) rfl) (Ns204p759 rfl) rfl)) 

noncomputable def Ns204p761 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz88) (hardyZApproximantRS₀ qz88) Bool.false 3534503777538553622553 1180591620717411303424 1711316274688458451 1180591620717411303424 (@Eq.refl Real (hardyZApproximantRS₀ qz88)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz88) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz88) qz88 8) (@HMul.hMul Real Real Real qz5 qz680 (Zeta.RiemannSiegel.correction qz90))) Bool.false 3534503777538553622553 1180591620717411303424 1711316274688458451 1180591620717411303424 (BSN.hardyZApproximantRS₀_eq qz88 8 (@BSN.floor_sqrt_eq_dec qz88 487638 1000 8 qz91 rfl rfl rfl)) (@Ns204p659 3534503777538553622553 1180591620717411303424 1711316274688458451 1180591620717411303424 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz88) qz88 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz88) qz88 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz88) qz88 8)) Bool.false 106886727 33554432 5943 4194304 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz88) qz88 8) (Ns204p723 (Ns204p722 rfl rfl rfl rfl) rfl rfl)) (Ns204p760 rfl) rfl rfl)) 

theorem RS205to222.d48 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz88) Bool.false 3534503777538553622553 1180591620717411303424 1711316274688458451 1180591620717411303424 := Ns204p761 

noncomputable def Ns204p762 := nat_lit 79423157929136880604653027328 

noncomputable abbrev qz870 := (Enclosure.sfrac Bool.false 489081 1000)

noncomputable abbrev qz685 := qz870

noncomputable abbrev qz445 := qz685

noncomputable abbrev qz101 := qz445

noncomputable abbrev qz871 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 489081 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz686 := qz871

noncomputable abbrev qz446 := qz686

noncomputable abbrev qz102 := qz446

noncomputable abbrev qz872 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 489081 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz687 := qz872

noncomputable abbrev qz447 := qz687

noncomputable abbrev qz103 := qz447

noncomputable abbrev qz688 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz102 qz9))

noncomputable def Ns204p763 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz101) qz101 8) (@HMul.hMul Real Real Real qz5 qz688 (Zeta.RiemannSiegel.correction qz103)) 60650347 33554432 95373 67108864 233050181488200906225 1180591620717411303424 505036081706019393 18446744073709551616000 Ns204p762 

noncomputable def Ns204p764 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz101) qz101 Real.sin BSN.quadSignNeg 7 8 489081 1000 125 134217728 67108864 2251799813685248 Bool.false 110052549507 1794 279097919 53 47453128 8 

noncomputable def Ns204p765 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz101) qz101 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 489081 1000 35 83 134217728 67108864 2251799813685248 Bool.false 110052549507 1794 

noncomputable def Ns204p766 := Ns204p765 240485871 53 54794152 8 261175631 53 50729528 8 Bool.true 193948429 63754 Bool.true 185515772 Bool.true 184706005 7074237752028440 1 Bool.false 131837833 Bool.false Bool.false 131683619 Bool.false Bool.true 90354141 

noncomputable def Ns204p767 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz101) qz101 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 489081 1000 90 20 134217728 67108864 2251799813685248 Bool.false 110052549507 1794 

noncomputable def Ns204p768 := Ns204p767 186065264 53 67108856 8 216015088 53 60023992 8 Bool.true 148134759 37481 Bool.false 76979852 Bool.false 187099970 7074237752028440 1 Bool.false 112740598 Bool.true Bool.false 23605327 Bool.false Bool.true 193948429 

noncomputable def Ns204p769 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz101) qz101 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 489081 1000 306 179 134217728 67108864 2251799813685248 Bool.false 110052549507 1794 

noncomputable def Ns204p770 := Ns204p769 93032624 53 94906264 8 147453232 53 77490640 16 Bool.true 134217720 1853 Bool.false 38474203 Bool.false 197635517 7074237752028440 1 Bool.false 128740970 Bool.true Bool.false 133569824 Bool.false Bool.true 148134759 

noncomputable def Ns204p771 := nat_lit 40432081257011575186785165357538791845174322481833734589 

noncomputable def Ns204p772 := nat_lit 49310098756563570972894415817714754152239203142860800 

noncomputable def Ns204p773 := nat_lit 13432175108347230192244286112480000 

noncomputable def Ns204p774 := nat_lit 39416549029975568419463782131322985280 

noncomputable abbrev qz448 := (@Eq.refl Real qz685)

noncomputable abbrev qz104 := qz448

noncomputable def Ns204p775 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz101 489081 1000 956801898244 16000000 978162 4000 2000 Ns204p773 Ns204p774 qz104 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns204p776 := nat_lit 116444394020193336537941276229711720514102048747681155616320 

noncomputable abbrev qz449 := (Enclosure.sfrac Bool.false 489081 2000)

noncomputable abbrev qz689 := (Real.log (Enclosure.sfrac Bool.false 956801898244 16000000))

noncomputable abbrev qz105 := (@HSub.hSub Real Real Real qz345 (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 489081 4000) qz689) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 978162)))))) qz449)

noncomputable abbrev qz450 := (@HSub.hSub Real Real Real qz12 qz105 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 489081 2000) (Real.log Real.pi)))

noncomputable def Ns204p777 := @Enclosure.Real.IsNear.addLit_ft_p qz450 (Enclosure.sfrac Bool.true Ns204p773 Ns204p774) 2954201858872792409469 3602879701896396800 5470519276670241 409600000000000000000 Ns204p773 Ns204p774 0 1 Ns204p776 

noncomputable def Ns204p778 := nat_lit 991265653878207095536437166080000 

noncomputable abbrev qz451 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 489081 2000) (Real.log Real.pi))

noncomputable def Ns204p779 := @Enclosure.Real.IsNear.subLit_ff_p qz105 qz451 19813830630568899574641 18014398509481984000 75848564187 12500000000000000 18785973400641 67108864000 489081 67108864000 Ns204p778 2954201858872792409469 3602879701896396800 

noncomputable def Ns204p780 := nat_lit 39627661261137799149282000 

noncomputable abbrev qz106 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 489081 4000) qz689) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 978162))))))

noncomputable def Ns204p781 := @Enclosure.Real.IsNear.subLit_ff_p qz106 qz449 24219080649276878682993 18014398509481984000 75848564187 12500000000000000 489081 2000 0 1 Ns204p780 19813830630568899574641 18014398509481984000 75848564187 12500000000000000 

noncomputable def Ns204p782 := nat_lit 54536521293669670580343006244072587264 

noncomputable def Ns204p783 := nat_lit 26593376959802140824436736 

noncomputable def Ns204p784 := nat_lit 495449030499539676314294218432561957628495474759268973720618227798029800124778634036309456177480513801004931941884757916858090705188009702232724980428987703676505089391355494400 

noncomputable def Ns204p785 := nat_lit 14851284038798160945884857725646464409308063525512252835768798027901337337841860584409817783771833870247094168336560939986270429999762648553949159253630588165682358846635376640 

noncomputable def Ns204p786 := nat_lit 1083350007764194252909218538385573113577589273691010238628415178707436325442472048402541070179899142123693488113553565930787782162791179719794093179945474258790997032960 

noncomputable def Ns204p787 := BSN.log_dyadic_bound 432513898244 1481089898244 8 7 Ns204p784 67108864 20480000 Ns204p785 Ns204p786 40369687 1913603796488 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 432513898244) (BSN.artanhQ 1481089898244) 0 7 Ns204p785 Ns204p784 Ns204p786 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns204p788 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 489081 4000) qz689 489081 4000 0 1 49534024595845753 4503599627370496 2441407 50000000000000 24226150283360836722993 18014398509481984000 1194045776967 200000000000000000 (Enclosure.Real.IsNear.const Bool.false 489081 4000) (BSN.isNear_log_sfrac 956801898244 16000000 49534024595845753 4503599627370496 2441407 50000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 956801898244) qz352)) Bool.false Ns204p783 Ns204p89 1000000307200000 20480000000000000000000 49534024595845753 4503599627370496 2441407 50000000000000 (BSN.log_rat_reduce_isNear 956801898244 16000000 15 1913603796488 1048576000000 40369687 67108864 24973259072661432 36028797018963968 20480000 1000000000000000 rfl rfl rfl rfl (Ns204p787 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns204p789 := BSN.arctan_dyadic_bound_f 1000 978162 1 0 8388608 2560000 0 1 1 0 1 1 8575 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 978162) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 978162) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz452 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 978162)))

noncomputable def Ns204p790 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz452 884279719003555 562949953421312 1 2000000000000000 8575 8388608 1 2560000 7413048629220385751040 883704260494755 562949953421312 781250001 2000000000000000 qz17 (Ns204p789 rfl) rfl rfl 

noncomputable def Ns204p791 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 489081 4000) qz689) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz452)) 24226150283360836722993 18014398509481984000 1194045776967 200000000000000000 883704260494755 2251799813685248 781250001 8000000000000000 Ns204p782 24219080649276878682993 18014398509481984000 75848564187 12500000000000000 (Ns204p788 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz452) 1 4 0 1 883704260494755 562949953421312 781250001 2000000000000000 883704260494755 2251799813685248 781250001 8000000000000000 qz355 Ns204p790 rfl) 

noncomputable def Ns204p792 := @Ns204p777 Ns204p771 Ns204p772 5470519276670241 409600000000000000000 (@Ns204p779 5470519276670241 409600000000000000000 (Ns204p781 (Ns204p791 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 489081 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz449 (Real.log Real.pi) 489081 2000 0 1 38410761 33554432 1 33554432 18785973400641 67108864000 489081 67108864000 (Enclosure.Real.IsNear.const Bool.false 489081 2000) RS205to222.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns204p773 Ns204p774) 

noncomputable def Ns204p793 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz101) Bool.false Ns204p771 Ns204p772 5470519276670241 409600000000000000000 859785543 1048576 225 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz101) (@HAdd.hAdd Real Real Real qz356 qz450 (Enclosure.sfrac Bool.true Ns204p773 Ns204p774)) Bool.false Ns204p771 Ns204p772 5470519276670241 409600000000000000000 Ns204p775 (Ns204p792 rfl rfl)) 

noncomputable def Ns204p794 := nat_lit 856497789541394949706640076517722262227911909195809151499356155790152623166102945245785167164545989430422416802024910103773184000000000 

noncomputable def Ns204p795 := nat_lit 609629255231292480240723990328626661699141819379407031943803427321174410695414616174136931766283037310976000000000000000000000000 

noncomputable def Ns204p796 := nat_lit 4277171384690992090877355476325515324228954649920532275569969645498140425794452875063827300591108648853635612890980000118865920000000000 

noncomputable def Ns204p797 := BSN.sin_dyadic_bound_f 53962096800 34359738368 4 3 16777216 5125001 Ns204p794 Ns204p217 Ns204p795 Ns204p796 Ns204p220 Ns204p795 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53962096800) qz357 0 3 Ns204p794 Ns204p217 Ns204p795 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53962096800) qz358 0 3 Ns204p796 Ns204p220 Ns204p795 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p798 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz101) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 859785543) (@Nat.cast Real Real.instNatCast 1048576)) Bool.false 859785543 1048576 225 16777216 Bool.true 16777215 16777216 1 2560000 (Ns204p793 rfl) (Enclosure.sfrac_false_div 859785543 1048576) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 859785543) (@Nat.cast Real Real.instNatCast 1048576)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 237327811563595881250816) (@Nat.cast Real Real.instNatCast 151115727451828646838272)) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 130 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q1 859785543 1048576 226375608064910080 72057594037927936 130 237327811563595881250816 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 237327811563595881250816 151115727451828646838272 53962096800 34359738368 5125001 5120000 (Ns204p797 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p799 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz101) Bool.false Ns204p771 Ns204p772 5470519276670241 409600000000000000000 110052549507 134217728 1794 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz101) (@HAdd.hAdd Real Real Real qz356 qz450 (Enclosure.sfrac Bool.true Ns204p773 Ns204p774)) Bool.false Ns204p771 Ns204p772 5470519276670241 409600000000000000000 Ns204p775 (Ns204p792 rfl rfl)) 

noncomputable def Ns204p800 := Ns204p770 37481 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 306 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 128740970 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 179 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133569824 134217728) qz104 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz101) qz101 1) Bool.true 16777215 16777216 144721 10485760000 134217720 134217728 1853 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz101) qz101 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz101)) Bool.true 16777215 16777216 144721 10485760000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz101) qz101) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz101)) Bool.true 16777215 16777216 592777216 42949672960000 16777215 16777216 144721 10485760000 (Ns204p798 rfl rfl) rfl)) rfl) (Ns204p799 rfl) RS205to222.d7 

noncomputable def Ns204p801 := nat_lit 2191182387448850733831155773681 

noncomputable def Ns204p802 := BSN.cos_dyadic_bound_f 38474203 134217728 2 1 134217728 67108864 Ns204p801 Ns204p125 Ns204p801 Ns204p801 Ns204p126 Ns204p801 128740970 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 38474203) qz363 0 1 Ns204p801 Ns204p125 Ns204p801 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 38474203) qz364 0 1 Ns204p801 Ns204p126 Ns204p801 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p803 := nat_lit 8350509146460917345267148803562450012603764306903435129285907157837096634754846599976200822537559210194161 

noncomputable def Ns204p804 := nat_lit 3551239231752853910241798631641276325703031562766804340510276514486447190575628371949418341306987761 

noncomputable def Ns204p805 := nat_lit 41712466725390667824082228337852494329800983208614330582702527011718469875840955823083778789633378755015921 

noncomputable def Ns204p806 := BSN.sin_dyadic_bound_f 197635517 134217728 4 3 134217728 67108864 Ns204p803 Ns204p256 Ns204p804 Ns204p805 Ns204p259 Ns204p804 133569824 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 197635517) qz361 0 3 Ns204p803 Ns204p256 Ns204p804 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 197635517) qz362 0 3 Ns204p805 Ns204p259 Ns204p804 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p807 := nat_lit 19146309412287342542717079409004523072776364426266702472937105063936 

noncomputable def Ns204p808 := nat_lit 1233151894140661047676445124442288822612403069677429245471686656 

noncomputable def Ns204p809 := nat_lit 57436461933073746306055885336764684640683868472660752560320371818496 

noncomputable def Ns204p810 := BSN.cos_dyadic_bound_f 76979852 134217728 3 2 134217728 67108864 Ns204p807 Ns204p240 Ns204p808 Ns204p809 Ns204p243 Ns204p808 112740598 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 76979852) qz363 0 2 Ns204p807 Ns204p240 Ns204p808 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 76979852) qz364 0 2 Ns204p809 Ns204p243 Ns204p808 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p811 := nat_lit 2581517374987935008160408347109782181294278549769946183153548293538550655870782677506521247800634944000000 

noncomputable def Ns204p812 := nat_lit 1840283000504860219166836927512219901951299624993953352562770992861718780812926356091441000000000000 

noncomputable def Ns204p813 := nat_lit 15637780521961350460778621594269082532242729976544390660998118602727812825752208256818925880425695193600000 

noncomputable def Ns204p814 := BSN.cos_dyadic_bound_f 187099970 134217728 4 3 134217728 67108864 Ns204p811 Ns204p230 Ns204p812 Ns204p813 Ns204p233 Ns204p812 23605327 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 187099970) qz363 0 3 Ns204p811 Ns204p230 Ns204p812 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 187099970) qz364 0 3 Ns204p813 Ns204p233 Ns204p812 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p815 := Ns204p768 63754 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 90 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 112740598 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 20 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 23605327 134217728) qz104 rfl rfl (Ns204p800 RS205to222.d9 RS205to222.d11 RS205to222.d13 RS205to222.d17 (Ns204p802 rfl rfl) (Ns204p806 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns204p799 rfl) RS205to222.d19 RS205to222.d21 RS205to222.d23 RS205to222.d25 RS205to222.d17 (Ns204p810 rfl rfl) (Ns204p814 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns204p816 := nat_lit 6480752975780047831880659897808734257126341308390266217925872360386066997749215034357079141093031821705216 

noncomputable def Ns204p817 := nat_lit 1661766713174424788410772985278365056932532133629565870637662697052338249726882652166134656156041216 

noncomputable def Ns204p818 := nat_lit 32379609754561408132642226342728902428134334638620511531133597380299962484808572588671333149428894008344576 

noncomputable def Ns204p819 := BSN.sin_dyadic_bound_f 185515772 134217728 4 3 134217728 67108864 Ns204p816 Ns204p256 Ns204p817 Ns204p818 Ns204p259 Ns204p817 131837833 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 185515772) qz361 0 3 Ns204p816 Ns204p256 Ns204p817 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 185515772) qz362 0 3 Ns204p818 Ns204p259 Ns204p817 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p820 := nat_lit 6368205815599107007690249772592559052982374474491916476957546777087548042961807845804669846268230405540625 

noncomputable def Ns204p821 := nat_lit 1576783914526525989841138626798708894560859499171696022073110702467386269060286102928304297119140625 

noncomputable def Ns204p822 := nat_lit 31817704777854970839332360727506166961269363941468772935624723024544036584514884399527143500131259551140625 

noncomputable def Ns204p823 := BSN.sin_dyadic_bound_f 184706005 134217728 4 3 134217728 67108864 Ns204p820 Ns204p256 Ns204p821 Ns204p822 Ns204p259 Ns204p821 131683619 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 184706005) qz361 0 3 Ns204p820 Ns204p256 Ns204p821 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 184706005) qz362 0 3 Ns204p822 Ns204p259 Ns204p821 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p824 := Ns204p766 85564 BSN.abs_quadSignPos (BSN.cos_quad_nat3 35 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 131837833 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 83 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 131683619 134217728) qz104 rfl rfl (Ns204p815 rfl rfl) (Ns204p799 rfl) RS205to222.d27 RS205to222.d29 RS205to222.d31 RS205to222.d33 RS205to222.d17 (Ns204p819 rfl rfl) (Ns204p823 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns204p825 := nat_lit 81124245659643869102711764163203640125909484319080415080884861992960 

noncomputable def Ns204p826 := nat_lit 6832592925941640290538471893207892240770203278943519754179117056 

noncomputable def Ns204p827 := nat_lit 212457200148615751660917558139611006599468354792282797608429777125376 

noncomputable def Ns204p828 := BSN.sin_dyadic_bound_f 95350548 134217728 3 2 134217728 67108864 Ns204p825 Ns204p106 Ns204p826 Ns204p827 Ns204p109 Ns204p826 87530078 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 95350548) qz361 0 2 Ns204p825 Ns204p106 Ns204p826 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 95350548) qz362 0 2 Ns204p827 Ns204p109 Ns204p826 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p829 := Ns204p764 Bool.true 90354141 85564 Bool.true 95350548 7074237752028440 1 Bool.false 87530078 Bool.true Bool.true 121300694 95373 BSN.abs_quadSignNeg qz387 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 87530078 134217728) qz104 rfl (Ns204p824 rfl) (Ns204p799 rfl) RS205to222.d35 RS205to222.d37 RS205to222.d17 (Ns204p828 rfl rfl) rfl 

noncomputable def Ns204p830 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz101) qz101 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz101) qz101 8) 121300694 134217728 95373 134217728 121300694 134217728 95373 134217728 32561407107006464 60650347 33554432 95373 67108864 (Ns204p829 rfl rfl rfl rfl) 

noncomputable def Ns204p831 := @Enclosure.Real.IsNear.mulLit_ff qz688 (Zeta.RiemannSiegel.correction qz103) 5648325 16777216 1 16777216 41260051694653 70368744177664 1428788333813 17592186044416000 233050181488200906225 1180591620717411303424 

noncomputable abbrev qz690 := (@HPow.hPow Real Real Real qz7 qz102 qz9)

noncomputable def Ns204p832 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz690 1 1 0 1 5648325 16777216 1 16777216 5648325 16777216 1 16777216 

noncomputable def Ns204p833 := @Enclosure.Real.IsNear.sqrt_image qz102 1305932837337 16777216000 489081 16777216000 74009980 74010009 8388608 (@Enclosure.Real.IsNear.of_eq qz102 (@HMul.hMul Real Real Real qz5 qz101 qz3) Bool.false 1305932837337 16777216000 489081 16777216000 (BSN.t_div_two_pi_mk qz101 489081 1000 qz104) (@Enclosure.Real.IsNear.mulLit_ff qz101 qz3 489081 1000 0 1 2670177 16777216 1 16777216 1305932837337 16777216000 489081 16777216000 (Enclosure.Real.IsNear.const Bool.false 489081 1000) RS205to222.d40 rfl)) 

noncomputable abbrev qz873 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 489081 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz691 := qz873

noncomputable abbrev qz453 := qz691

noncomputable abbrev qz107 := qz453

noncomputable def Ns204p834 := @Enclosure.Real.IsNear.sqrt_image qz107 148019989 16777216 29 16777216 24916675 24916681 8388608 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 148019989 16777216 29 16777216 148019989 16777216 29 16777216 (Ns204p833 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns204p835 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz107) 12458339 4194304 3 8388608 2824162 2824163 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz107) Bool.false 49833356 16777216 6 16777216 12458339 4194304 3 8388608 (Ns204p834 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns204p836 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 5648325 16777216 1 16777216 5648325 16777216 1 16777216 (Ns204p835 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz108 := (@HMul.hMul Real Real Real qz342 qz340 qz447)

noncomputable abbrev qz692 := (@HMul.hMul Real Real Real qz844 qz872 qz872)

noncomputable abbrev qz454 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz692 qz687) qz640)

noncomputable abbrev qz109 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz454))

noncomputable def Ns204p837 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz103) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz108)) qz109) Bool.false 41260051694653 

noncomputable def Ns204p838 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz108)) qz109 19024027 8388608 61 

noncomputable def Ns204p839 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz108)) Bool.false 38048054 16777216 976 16777216 19024027 8388608 61 

noncomputable def Ns204p840 := @Enclosure.Real.IsNear.recentre' (Real.cos qz108) Bool.false 7397881 16777216 485257216 42949672960000 7397881 16777216 118471 10485760000 

noncomputable def Ns204p841 := @Enclosure.Real.IsNear.cos_image qz108 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 86722163) qz369) Bool.false 86722163 16777216 183 16777216 Bool.false 7397881 16777216 1 

noncomputable def Ns204p842 := nat_lit 156519237396167567482322511 

noncomputable def Ns204p843 := nat_lit 14411518807585587200000000000000 

noncomputable def Ns204p844 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz103 884279719003555 140737488355328 1 500000000000000 13802261 16777216 29 16777216 12205059478693726037855 2361183241434822606848 Ns204p842 

noncomputable def Ns204p845 := @Enclosure.Real.IsNear.subLit_ff_p qz107 qz1 148019989 16777216 29 16777216 8 1 0 1 13802261 13802261 16777216 29 

noncomputable def Ns204p846 := @Ns204p845 16777216 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 148019989 16777216 29 16777216 148019989 16777216 29 16777216 (Ns204p833 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns204p847 := @Enclosure.Real.IsNear.recentre' qz108 Bool.false 12205059478693726037855 2361183241434822606848 Ns204p842 Ns204p843 86722163 16777216 183 16777216 (@Ns204p844 Ns204p843 RS205to222.d39 (Ns204p846 rfl rfl) rfl) 

noncomputable def Ns204p848 := nat_lit 60610974995260414258149522626746676349921 

noncomputable def Ns204p849 := BSN.sin_dyadic_bound_f 15690537369 34359738368 2 1 16777216 5125001 Ns204p848 Ns204p419 Ns204p848 Ns204p848 Ns204p420 Ns204p848 7397881 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 15690537369) qz357 0 1 Ns204p848 Ns204p419 Ns204p848 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 15690537369) qz358 0 1 Ns204p848 Ns204p420 Ns204p848 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p850 := @Ns204p841 2560000 (Ns204p847 rfl) (Enclosure.sfrac_false_div 86722163 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 86722163) qz369) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1104123410181013997879296) qz371) 226375608064910080 72057594037927936 Bool.false 7397881 16777216 0 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q3 86722163 16777216 226375608064910080 72057594037927936 0 1104123410181013997879296 Ns204p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 7397881 16777216 1104123410181013997879296 Ns204p89 15690537369 34359738368 5125001 5120000 (Ns204p849 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p851 := @Enclosure.Real.IsNear.inv_image (Real.cos qz108) 7397881 16777216 118471 10485760000 19023539 19024515 8388608 (Ns204p840 (Ns204p850 rfl rfl) rfl) rfl 

noncomputable def Ns204p852 := @Enclosure.Real.IsNear.recentre' qz109 Bool.false 2168839 8388608 

noncomputable abbrev qz110 := (@HMul.hMul Real Real Real qz342 qz340 qz454)

noncomputable def Ns204p853 := @Enclosure.Real.IsNear.cos_image qz110 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 21966069)) qz369) Bool.true 21966069 16777216 

noncomputable def Ns204p854 := nat_lit 51865916053451735965438820405 

noncomputable def Ns204p855 := nat_lit 34733001620913880962616131974691213 

noncomputable def Ns204p856 := @Enclosure.Real.IsNear.recentre' qz110 Bool.true Ns204p854 Ns204p533 Ns204p855 

noncomputable abbrev qz111 := qz454

noncomputable def Ns204p857 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz111 884279719003555 140737488355328 1 500000000000000 58653291417671 

noncomputable abbrev qz455 := (@HSub.hSub Real Real Real qz634 qz692 qz687)

noncomputable abbrev qz112 := qz455

noncomputable def Ns204p858 := @Enclosure.Real.IsNear.subLit_tf qz112 qz27 41061105373255 281474976710656 1287071243 281474976710656 1 16 

noncomputable abbrev qz456 := qz692

noncomputable abbrev qz113 := qz456

noncomputable def Ns204p859 := @Enclosure.Real.IsNear.subLit_ff_n qz113 qz103 190502408712121 281474976710656 800531979 281474976710656 13802261 16777216 29 16777216 

noncomputable def Ns204p860 := @Enclosure.Real.IsNear.mulLit_ff qz103 qz103 13802261 16777216 29 16777216 13802261 16777216 29 16777216 190502408712121 281474976710656 

noncomputable def Ns204p861 := nat_lit 31042537222338649923464083717043951504063472903658183271162721 

noncomputable def Ns204p862 := nat_lit 54202428823828725096145867005691586378089413998471142220641 

noncomputable def Ns204p863 := nat_lit 93019206809368292320199959417120471339434239882977607529046881 

noncomputable def Ns204p864 := BSN.cos_dyadic_bound_f 21966069 16777216 3 2 8388608 2560000 Ns204p861 Ns204p754 Ns204p862 Ns204p863 Ns204p757 Ns204p862 2168839 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 21966069) (BSN.cosEvenQ 16777216) 0 2 Ns204p861 Ns204p754 Ns204p862 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 21966069) (BSN.cosOddQ 16777216) 0 2 Ns204p863 Ns204p757 Ns204p862 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p865 := @Ns204p852 1253257216 42949672960000 2168839 8388608 305971 10485760000 (@Ns204p853 483 16777216 Bool.false 2168839 8388608 1 2560000 (@Ns204p856 Ns204p536 21966069 16777216 483 16777216 (@Ns204p857 281474976710656 1287071243 281474976710656 Ns204p854 Ns204p533 Ns204p855 Ns204p536 RS205to222.d39 (@Ns204p858 0 1 938452662682736 58653291417671 281474976710656 1287071243 281474976710656 (@Ns204p859 688891034045859758080 41061105373255 281474976710656 1287071243 281474976710656 (@Ns204p860 800531979 281474976710656 (Ns204p846 rfl rfl) (Ns204p846 rfl rfl) rfl) (Ns204p846 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 21966069 16777216) (BSN.cos_neg_of_bound 21966069 16777216 Bool.false 2168839 8388608 1 2560000 (Ns204p864 rfl rfl)) rfl rfl) 

noncomputable def Ns204p866 := @Ns204p831 505036081706019393 18446744073709551616000 (Ns204p832 qz29 (@Enclosure.Real.IsNear.of_eq qz690 (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 5648325 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz102 (BSN.t_div_two_pi_nonneg qz101 489081 1000 qz104)) Ns204p836) rfl) (@Ns204p837 70368744177664 1428788333813 17592186044416000 (BSN.correction_mk qz103 (BSN.cos_two_pi_p_ne_zero_mk qz101 489081 1000 8 qz104 rfl rfl (@BSN.floor_sqrt_eq_dec qz101 489081 1000 8 qz104 rfl rfl rfl))) (@Ns204p838 1048576 2168839 8388608 305971 10485760000 41260051694653 70368744177664 1428788333813 17592186044416000 (@Ns204p839 1048576 (Ns204p851 rfl rfl rfl rfl rfl) rfl) (Ns204p865 rfl) rfl)) 

noncomputable def Ns204p867 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz101) (hardyZApproximantRS₀ qz101) Bool.true 2366994557652976530929 1180591620717411303424 26720966700676131393 18446744073709551616000 (@Eq.refl Real (hardyZApproximantRS₀ qz101)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz101) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz101) qz101 8) (@HMul.hMul Real Real Real qz5 qz688 (Zeta.RiemannSiegel.correction qz103))) Bool.true 2366994557652976530929 1180591620717411303424 26720966700676131393 18446744073709551616000 (BSN.hardyZApproximantRS₀_eq qz101 8 (@BSN.floor_sqrt_eq_dec qz101 489081 1000 8 qz104 rfl rfl rfl)) (@Ns204p763 2366994557652976530929 1180591620717411303424 26720966700676131393 18446744073709551616000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz101) qz101 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz101) qz101 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz101) qz101 8)) Bool.true 60650347 33554432 95373 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz101) qz101 8) (Ns204p830 (Ns204p829 rfl rfl rfl rfl) rfl rfl)) (Ns204p866 rfl) rfl rfl)) 

theorem RS205to222.d49 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz101) Bool.true 2366994557652976530929 1180591620717411303424 26720966700676131393 18446744073709551616000 := Ns204p867 

noncomputable def Ns204p868 := nat_lit 137653944688237262739767033856 

noncomputable abbrev qz874 := (Enclosure.sfrac Bool.false 490524 1000)

noncomputable abbrev qz693 := qz874

noncomputable abbrev qz457 := qz693

noncomputable abbrev qz114 := qz457

noncomputable abbrev qz875 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 490524 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz694 := qz875

noncomputable abbrev qz458 := qz694

noncomputable abbrev qz115 := qz458

noncomputable abbrev qz876 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 490524 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz695 := qz876

noncomputable abbrev qz459 := qz695

noncomputable abbrev qz116 := qz459

noncomputable abbrev qz696 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz115 qz9))

noncomputable def Ns204p869 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 8) (@HMul.hMul Real Real Real qz5 qz696 (Zeta.RiemannSiegel.correction qz116)) 123424887 33554432 95653 67108864 240219911693217942651 1180591620717411303424 17041332249589043461 737869762948382064640000 Ns204p868 

noncomputable def Ns204p870 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.sin BSN.quadSignNeg 7 8 490524 1000 125 134217728 67108864 2251799813685248 Bool.false 110474388115 1798 279097919 53 47453128 8 

noncomputable def Ns204p871 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 490524 1000 35 83 134217728 67108864 2251799813685248 Bool.false 110474388115 1798 

noncomputable def Ns204p872 := Ns204p871 240485871 53 54794152 8 261175631 53 50729528 8 Bool.false 188361711 63942 Bool.true 110698276 Bool.true 139743832 7074237752028440 1 Bool.false 98568059 Bool.false Bool.false 115829532 Bool.false Bool.false 272381392 

noncomputable def Ns204p873 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 490524 1000 91 21 134217728 67108864 2251799813685248 Bool.false 110474388115 1798 

noncomputable def Ns204p874 := Ns204p873 186065264 53 67108856 8 216015088 53 60023992 8 Bool.false 214672605 37593 Bool.false 19497570 Bool.false 86400092 7074237752028440 1 Bool.false 19429066 Bool.false Bool.false 80555302 Bool.true Bool.false 188361711 

noncomputable def Ns204p875 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz114) qz114 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 490524 1000 307 180 134217728 67108864 2251799813685248 Bool.false 110474388115 1798 

noncomputable def Ns204p876 := Ns204p875 93032624 53 94906264 8 147453232 53 77490640 16 Bool.false 134217648 1861 Bool.false 115238021 Bool.false 195870397 7074237752028440 1 Bool.false 101592348 Bool.false Bool.false 14927370 Bool.false Bool.false 214672605 

noncomputable def Ns204p877 := nat_lit 1575884854516035200376683542525685234856049517242523 

noncomputable def Ns204p878 := nat_lit 1914576657736055695855033604952964857092636672000 

noncomputable def Ns204p879 := nat_lit 13631501192672575364065825259520000 

noncomputable def Ns204p880 := nat_lit 40119490399082427059056475862340730880 

noncomputable abbrev qz460 := (@Eq.refl Real qz693)

noncomputable abbrev qz117 := qz460

noncomputable def Ns204p881 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz114 490524 1000 962456178304 16000000 981048 4000 2000 Ns204p879 Ns204p880 qz117 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns204p882 := nat_lit 148719153348810551364316319005867162874197528073288621752320 

noncomputable abbrev qz461 := (Enclosure.sfrac Bool.false 490524 2000)

noncomputable abbrev qz697 := (Real.log (Enclosure.sfrac Bool.false 962456178304 16000000))

noncomputable abbrev qz118 := (@HSub.hSub Real Real Real qz345 (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 490524 4000) qz697) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 981048)))))) qz461)

noncomputable abbrev qz462 := (@HSub.hSub Real Real Real qz12 qz118 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 490524 2000) (Real.log Real.pi)))

noncomputable def Ns204p883 := @Enclosure.Real.IsNear.addLit_ft_p qz462 (Enclosure.sfrac Bool.true Ns204p879 Ns204p880) 3706906873947621244639 4503599627370496000 1371635412983391 102400000000000000000 Ns204p879 Ns204p880 0 1 Ns204p882 

noncomputable def Ns204p884 := nat_lit 12438315463220802861499469004800 

noncomputable abbrev qz463 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 490524 2000) (Real.log Real.pi))

noncomputable def Ns204p885 := @Enclosure.Real.IsNear.subLit_ff_p qz118 qz463 994266366551685401747 900719925474099200 1217099977293 200000000000000000 4710350032191 16777216000 122631 16777216000 Ns204p884 3706906873947621244639 4503599627370496000 

noncomputable def Ns204p886 := nat_lit 9942663665516854017470000 

noncomputable abbrev qz119 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 490524 4000) qz697) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 981048))))))

noncomputable def Ns204p887 := @Enclosure.Real.IsNear.subLit_ff_p qz119 qz461 6075893684566569598687 4503599627370496000 1217099977293 200000000000000000 490524 2000 0 1 Ns204p886 994266366551685401747 900719925474099200 1217099977293 200000000000000000 

noncomputable def Ns204p888 := nat_lit 13681696266878376403936744329892069376 

noncomputable def Ns204p889 := nat_lit 26607623322604191480807424 

noncomputable def Ns204p890 := nat_lit 522596572846610979832927705427283213432204902495100242623654462765424877488630241173595715126330254137600502951642119706539428556089256584933345714129704076549666397160367718400 

noncomputable def Ns204p891 := nat_lit 15971545122160936774029293238529261823902354841951019898143023556500798681845218436169513071564029019312603159251429369736640503703502182597577191535536199856331954683159511040 

noncomputable def Ns204p892 := nat_lit 1299390005415120675410838781767230867080651786092419795340075272373820495421089535082992969866104721251650136732384847667816891851974579789179779633822125531503064514560 

noncomputable def Ns204p893 := BSN.log_dyadic_bound 438168178304 1486744178304 8 7 Ns204p890 67108864 20480000 Ns204p891 Ns204p892 40765103 1924912356608 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 438168178304) (BSN.artanhQ 1486744178304) 0 7 Ns204p891 Ns204p890 Ns204p892 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns204p894 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 490524 4000) qz697 490524 4000 0 1 49560560514413177 4503599627370496 2441407 50000000000000 6077661096443002308687 4503599627370496000 299392181817 50000000000000000 (Enclosure.Real.IsNear.const Bool.false 490524 4000) (BSN.isNear_log_sfrac 962456178304 16000000 49560560514413177 4503599627370496 2441407 50000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 962456178304) qz352)) Bool.false Ns204p889 Ns204p89 1000000307200000 20480000000000000000000 49560560514413177 4503599627370496 2441407 50000000000000 (BSN.log_rat_reduce_isNear 962456178304 16000000 15 1924912356608 1048576000000 40765103 67108864 24973259072661432 36028797018963968 20480000 1000000000000000 rfl rfl rfl rfl (Ns204p893 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns204p895 := BSN.arctan_dyadic_bound_f 1000 981048 1 0 8388608 2560000 0 1 1 0 1 1 8550 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 981048) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 981048) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz464 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 981048)))

noncomputable def Ns204p896 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz464 884279719003555 562949953421312 1 2000000000000000 8550 8388608 1 2560000 7413062702969221283840 883705938216355 562949953421312 781250001 2000000000000000 qz17 (Ns204p895 rfl) rfl rfl 

noncomputable def Ns204p897 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 490524 4000) qz697) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz464)) 6077661096443002308687 4503599627370496000 299392181817 50000000000000000 883705938216355 2251799813685248 781250001 8000000000000000 Ns204p888 6075893684566569598687 4503599627370496000 1217099977293 200000000000000000 (Ns204p894 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz464) 1 4 0 1 883705938216355 562949953421312 781250001 2000000000000000 883705938216355 2251799813685248 781250001 8000000000000000 qz355 Ns204p896 rfl) 

noncomputable def Ns204p898 := @Ns204p883 Ns204p877 Ns204p878 1371635412983391 102400000000000000000 (@Ns204p885 1371635412983391 102400000000000000000 (Ns204p887 (Ns204p897 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 490524 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz461 (Real.log Real.pi) 490524 2000 0 1 38410761 33554432 1 33554432 4710350032191 16777216000 122631 16777216000 (Enclosure.Real.IsNear.const Bool.false 490524 2000) RS205to222.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns204p879 Ns204p880) 

noncomputable def Ns204p899 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz114) Bool.false Ns204p877 Ns204p878 1371635412983391 102400000000000000000 6904649257 8388608 113 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz114) (@HAdd.hAdd Real Real Real qz356 qz462 (Enclosure.sfrac Bool.true Ns204p879 Ns204p880)) Bool.false Ns204p877 Ns204p878 1371635412983391 102400000000000000000 Ns204p881 (Ns204p898 rfl rfl)) 

noncomputable def Ns204p900 := BSN.cos_dyadic_bound_f 36327993 34359738368 1 0 16777216 5125001 0 1 1 0 1 1 16777206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 36327993) qz642 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 36327993) qz643 0 0 rfl) rfl rfl 

noncomputable def Ns204p901 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz114) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6904649257) qz359) Bool.false 6904649257 8388608 113 8388608 Bool.false 16777206 16777216 1 2560000 (Ns204p899 rfl) (Enclosure.sfrac_false_div 6904649257 8388608) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6904649257) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1278177652836866719744) qz360) 226375608064910080 72057594037927936 Bool.false 16777206 16777216 131 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q0 6904649257 8388608 226375608064910080 72057594037927936 131 1278177652836866719744 Ns204p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777206 16777216 1278177652836866719744 Ns204p100 36327993 34359738368 5125001 5120000 (Ns204p900 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p902 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz114) Bool.false Ns204p877 Ns204p878 1371635412983391 102400000000000000000 110474388115 134217728 1798 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz114) (@HAdd.hAdd Real Real Real qz356 qz462 (Enclosure.sfrac Bool.true Ns204p879 Ns204p880)) Bool.false Ns204p877 Ns204p878 1371635412983391 102400000000000000000 Ns204p881 (Ns204p898 rfl rfl)) 

noncomputable def Ns204p903 := Ns204p876 37593 BSN.abs_quadSignPos (BSN.cos_quad_nat3 307 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 101592348 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 180 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 14927370 134217728) qz117 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 1) Bool.false 8388603 8388608 72673 5242880000 134217648 134217728 1861 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz114)) Bool.false 8388603 8388608 72673 5242880000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz114) qz114) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz114)) Bool.false 16777206 16777216 297668608 21474836480000 8388603 8388608 72673 5242880000 (Ns204p901 rfl rfl) rfl)) rfl) (Ns204p902 rfl) RS205to222.d7 

noncomputable def Ns204p904 := nat_lit 173094202673955496651872842572401948071143729183681768567299030534625 

noncomputable def Ns204p905 := nat_lit 31100425562931653563894179811269352812306940253204284741996923361 

noncomputable def Ns204p906 := nat_lit 453291606314210125696753997112786856472251746149232777405724704000481 

noncomputable def Ns204p907 := BSN.sin_dyadic_bound_f 115238021 134217728 3 2 134217728 67108864 Ns204p904 Ns204p106 Ns204p905 Ns204p906 Ns204p109 Ns204p905 101592348 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 115238021) qz361 0 2 Ns204p904 Ns204p106 Ns204p905 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 115238021) qz362 0 2 Ns204p906 Ns204p109 Ns204p905 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p908 := nat_lit 3102068336940828257360233434833165081405023086076407835764548160831331235063230540047095909653268315566321 

noncomputable def Ns204p909 := nat_lit 3188787969681904127664587122465727429965262067946521198909000092488513519551602936199847762136985841 

noncomputable def Ns204p910 := nat_lit 18785417983009083573870960123247494663059658731022930193503267348129481509996626713167508654523477849862385 

noncomputable def Ns204p911 := BSN.cos_dyadic_bound_f 195870397 134217728 4 3 134217728 67108864 Ns204p908 Ns204p230 Ns204p909 Ns204p910 Ns204p233 Ns204p909 14927370 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 195870397) qz363 0 3 Ns204p908 Ns204p230 Ns204p909 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 195870397) qz364 0 3 Ns204p910 Ns204p233 Ns204p909 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p912 := nat_lit 144518003385910170121844010000 

noncomputable def Ns204p913 := BSN.sin_dyadic_bound_f 19497570 134217728 2 1 134217728 67108864 Ns204p912 Ns204p129 Ns204p912 Ns204p912 Ns204p130 Ns204p912 19429066 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 19497570) qz361 0 1 Ns204p912 Ns204p129 Ns204p912 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 19497570) qz362 0 1 Ns204p912 Ns204p130 Ns204p912 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p914 := nat_lit 54689354705251033983874873504018619400331021354779467724517439242240 

noncomputable def Ns204p915 := nat_lit 3105372046924989149632399800698122955640985273331584374228975616 

noncomputable def Ns204p916 := nat_lit 143228996482819591403906216244180968135129256238741783379987398721536 

noncomputable def Ns204p917 := BSN.sin_dyadic_bound_f 86400092 134217728 3 2 134217728 67108864 Ns204p914 Ns204p106 Ns204p915 Ns204p916 Ns204p109 Ns204p915 80555302 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 86400092) qz361 0 2 Ns204p914 Ns204p106 Ns204p915 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 86400092) qz362 0 2 Ns204p916 Ns204p109 Ns204p915 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p918 := Ns204p874 63942 BSN.abs_quadSignPos (BSN.cos_quad_nat3 91 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 19429066 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 21 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 80555302 134217728) qz117 rfl rfl (Ns204p903 RS205to222.d9 RS205to222.d11 RS205to222.d13 RS205to222.d17 (Ns204p907 rfl rfl) (Ns204p911 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns204p902 rfl) RS205to222.d19 RS205to222.d21 RS205to222.d23 RS205to222.d25 RS205to222.d17 (Ns204p913 rfl rfl) (Ns204p917 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns204p919 := nat_lit 147384291284326345703386413784873888103765127485315055594461498245120 

noncomputable def Ns204p920 := nat_lit 22548977761945569414882010745585426893134283427559685205042200576 

noncomputable def Ns204p921 := nat_lit 385969969304478231634578417609653044818700735526466239447543379460096 

noncomputable def Ns204p922 := BSN.sin_dyadic_bound_f 110698276 134217728 3 2 134217728 67108864 Ns204p919 Ns204p106 Ns204p920 Ns204p921 Ns204p109 Ns204p920 98568059 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 110698276) qz361 0 2 Ns204p919 Ns204p106 Ns204p920 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 110698276) qz362 0 2 Ns204p921 Ns204p109 Ns204p920 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p923 := nat_lit 374386903022638354486187065796672852404068120030270421757132611256320 

noncomputable def Ns204p924 := nat_lit 145432404666053073913121419178913331215998405607204828412144254976 

noncomputable def Ns204p925 := nat_lit 980301664975545890106059166217377325188685840755915630117918129258496 

noncomputable def Ns204p926 := BSN.sin_dyadic_bound_f 139743832 134217728 3 2 134217728 67108864 Ns204p923 Ns204p106 Ns204p924 Ns204p925 Ns204p109 Ns204p924 115829532 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 139743832) qz361 0 2 Ns204p923 Ns204p106 Ns204p924 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 139743832) qz362 0 2 Ns204p925 Ns204p109 Ns204p924 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p927 := Ns204p872 85815 BSN.abs_quadSignPos (BSN.cos_quad_nat3 35 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 98568059 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 83 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 115829532 134217728) qz117 rfl rfl (Ns204p918 rfl rfl) (Ns204p902 rfl) RS205to222.d27 RS205to222.d29 RS205to222.d31 RS205to222.d33 RS205to222.d17 (Ns204p922 rfl rfl) (Ns204p926 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns204p928 := nat_lit 33174246680624576002734831658634976279933919437694033420467566169505 

noncomputable def Ns204p929 := nat_lit 1142693042525486669089514256234209982451653625377559788926946721 

noncomputable def Ns204p930 := nat_lit 86883081708138372076365080844771987250331533945233761956804410625441 

noncomputable def Ns204p931 := BSN.sin_dyadic_bound_f 76250237 134217728 3 2 134217728 67108864 Ns204p928 Ns204p106 Ns204p929 Ns204p930 Ns204p109 Ns204p929 72214326 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 76250237) qz361 0 2 Ns204p928 Ns204p106 Ns204p929 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 76250237) qz362 0 2 Ns204p930 Ns204p109 Ns204p929 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p932 := Ns204p870 Bool.false 272381392 85815 Bool.true 76250237 7074237752028440 1 Bool.false 72214326 Bool.true Bool.false 246849774 95653 BSN.abs_quadSignNeg qz387 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 72214326 134217728) qz117 rfl (Ns204p927 rfl) (Ns204p902 rfl) RS205to222.d35 RS205to222.d37 RS205to222.d17 (Ns204p931 rfl rfl) rfl 

noncomputable def Ns204p933 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 8) 246849774 134217728 95653 134217728 246849774 134217728 95653 134217728 66263231647186944 123424887 33554432 95653 67108864 (Ns204p932 rfl rfl rfl rfl) 

noncomputable def Ns204p934 := @Enclosure.Real.IsNear.mulLit_ff qz696 (Zeta.RiemannSiegel.correction qz116) 2822083 8388608 1 8388608 85121490648297 140737488355328 6019711432379 87960930222080000 240219911693217942651 1180591620717411303424 

noncomputable abbrev qz698 := (@HPow.hPow Real Real Real qz7 qz115 qz9)

noncomputable def Ns204p935 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz698 1 1 0 1 2822083 8388608 1 8388608 2822083 8388608 1 8388608 

noncomputable def Ns204p936 := @Enclosure.Real.IsNear.sqrt_image qz115 327446475687 4194304000 122631 4194304000 74119081 74119109 8388608 (@Enclosure.Real.IsNear.of_eq qz115 (@HMul.hMul Real Real Real qz5 qz114 qz3) Bool.false 327446475687 4194304000 122631 4194304000 (BSN.t_div_two_pi_mk qz114 490524 1000 qz117) (@Enclosure.Real.IsNear.mulLit_ff qz114 qz3 490524 1000 0 1 2670177 16777216 1 16777216 327446475687 4194304000 122631 4194304000 (Enclosure.Real.IsNear.const Bool.false 490524 1000) RS205to222.d40 rfl)) 

noncomputable abbrev qz877 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 490524 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz699 := qz877

noncomputable abbrev qz465 := qz699

noncomputable abbrev qz120 := qz465

noncomputable def Ns204p937 := @Enclosure.Real.IsNear.sqrt_image qz120 74119095 8388608 7 4194304 24935033 24935039 8388608 (@Enclosure.Real.IsNear.recentre' qz120 Bool.false 148238190 16777216 28 16777216 74119095 8388608 7 4194304 (Ns204p936 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns204p938 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz120) 6233759 2097152 3 8388608 2822082 2822084 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz120) Bool.false 49870072 16777216 6 16777216 6233759 2097152 3 8388608 (Ns204p937 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns204p939 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz120)) Bool.false 5644166 16777216 2 16777216 2822083 8388608 1 8388608 (Ns204p938 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz121 := (@HMul.hMul Real Real Real qz342 qz340 qz459)

noncomputable abbrev qz700 := (@HMul.hMul Real Real Real qz844 qz876 qz876)

noncomputable abbrev qz466 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz700 qz695) qz640)

noncomputable abbrev qz122 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz466))

noncomputable def Ns204p940 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz116) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz121)) qz122) Bool.false 85121490648297 

noncomputable def Ns204p941 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz121)) qz122 32720749 16777216 699 

noncomputable def Ns204p942 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz121)) Bool.false 32720749 16777216 699 16777216 32720749 16777216 699 

noncomputable def Ns204p943 := @Enclosure.Real.IsNear.recentre' (Real.cos qz121) Bool.false 8602339 16777216 469897216 42949672960000 8602339 16777216 114721 10485760000 

noncomputable def Ns204p944 := @Enclosure.Real.IsNear.cos_image qz121 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11011645) qz372) Bool.false 11011645 2097152 177 16777216 Bool.false 8602339 16777216 1 

noncomputable def Ns204p945 := nat_lit 37780505578683406213717629 

noncomputable def Ns204p946 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz116 884279719003555 140737488355328 1 500000000000000 7010231 8388608 7 4194304 6199005098830010371205 1180591620717411303424 Ns204p945 

noncomputable def Ns204p947 := @Enclosure.Real.IsNear.subLit_ff_p qz120 qz1 74119095 8388608 7 4194304 8 1 0 1 7010231 7010231 8388608 7 

noncomputable def Ns204p948 := @Ns204p947 4194304 (@Enclosure.Real.IsNear.recentre' qz120 Bool.false 148238190 16777216 28 16777216 74119095 8388608 7 4194304 (Ns204p936 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns204p949 := @Enclosure.Real.IsNear.recentre' qz121 Bool.false 6199005098830010371205 1180591620717411303424 Ns204p945 Ns204p149 11011645 2097152 177 16777216 (@Ns204p946 Ns204p149 RS205to222.d39 (Ns204p948 rfl rfl) rfl) 

noncomputable def Ns204p950 := nat_lit 117093006545533024264602340340927000390625 

noncomputable def Ns204p951 := BSN.sin_dyadic_bound_f 18498339225 34359738368 2 1 16777216 5125001 Ns204p950 Ns204p419 Ns204p950 Ns204p950 Ns204p420 Ns204p950 8602339 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 18498339225) qz357 0 1 Ns204p950 Ns204p419 Ns204p950 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 18498339225) qz358 0 1 Ns204p950 Ns204p420 Ns204p950 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p952 := @Ns204p944 2560000 (Ns204p949 rfl) (Enclosure.sfrac_false_div 11011645 2097152) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11011645) qz372) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 162713112585931021352960) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 8602339 16777216 0 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q3 11011645 2097152 226375608064910080 72057594037927936 0 162713112585931021352960 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8602339 16777216 162713112585931021352960 302231454903657293676544 18498339225 34359738368 5125001 5120000 (Ns204p951 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p953 := @Enclosure.Real.IsNear.inv_image (Real.cos qz121) 8602339 16777216 114721 10485760000 16360025 16360724 8388608 (Ns204p943 (Ns204p952 rfl rfl) rfl) rfl 

noncomputable def Ns204p954 := @Enclosure.Real.IsNear.recentre' qz122 Bool.false 2601453 8388608 

noncomputable abbrev qz123 := (@HMul.hMul Real Real Real qz342 qz340 qz466)

noncomputable def Ns204p955 := @Enclosure.Real.IsNear.cos_image qz123 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 21063455)) qz369) Bool.true 21063455 16777216 

noncomputable def Ns204p956 := nat_lit 12433669384113623760553409005 

noncomputable def Ns204p957 := nat_lit 1058283153690401810850271791420783 

noncomputable def Ns204p958 := @Enclosure.Real.IsNear.recentre' qz123 Bool.true Ns204p956 Ns204p167 Ns204p957 

noncomputable abbrev qz124 := qz466

noncomputable def Ns204p959 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz124 884279719003555 140737488355328 1 500000000000000 14060787686191 

noncomputable abbrev qz467 := (@HSub.hSub Real Real Real qz634 qz700 qz695)

noncomputable abbrev qz125 := qz467

noncomputable def Ns204p960 := @Enclosure.Real.IsNear.subLit_tf qz125 qz27 9662741175087 70368744177664 39215897 8796093022208 1 16 

noncomputable abbrev qz468 := qz700

noncomputable abbrev qz126 := qz468

noncomputable def Ns204p961 := @Enclosure.Real.IsNear.subLit_ff_n qz126 qz116 49143338673361 70368744177664 24535833 8796093022208 7010231 8388608 7 4194304 

noncomputable def Ns204p962 := @Enclosure.Real.IsNear.mulLit_ff qz116 qz116 7010231 8388608 7 4194304 7010231 8388608 7 4194304 49143338673361 70368744177664 

noncomputable def Ns204p963 := nat_lit 26239109526838678857173138006674896816491297284075338573690625 

noncomputable def Ns204p964 := nat_lit 38746892138344212463561475917788202612137288418717312890625 

noncomputable def Ns204p965 := nat_lit 78639834796239348146592291068189114044249617275388581095290625 

noncomputable def Ns204p966 := BSN.cos_dyadic_bound_f 21063455 16777216 3 2 8388608 2560000 Ns204p963 Ns204p754 Ns204p964 Ns204p965 Ns204p757 Ns204p964 2601453 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 21063455) (BSN.cosEvenQ 16777216) 0 2 Ns204p963 Ns204p754 Ns204p964 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 21063455) (BSN.cosOddQ 16777216) 0 2 Ns204p965 Ns204p757 Ns204p964 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p967 := @Ns204p954 1222537216 42949672960000 2601453 8388608 298471 10485760000 (@Ns204p955 471 16777216 Bool.false 2601453 8388608 1 2560000 (@Ns204p958 Ns204p170 21063455 16777216 471 16777216 (@Ns204p959 70368744177664 39215897 8796093022208 Ns204p956 Ns204p167 Ns204p957 Ns204p170 RS205to222.d39 (@Ns204p960 0 1 224972602979056 14060787686191 70368744177664 39215897 8796093022208 (@Ns204p961 81056947923264208896 9662741175087 70368744177664 39215897 8796093022208 (@Ns204p962 24535833 8796093022208 (Ns204p948 rfl rfl) (Ns204p948 rfl rfl) rfl) (Ns204p948 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 21063455 16777216) (BSN.cos_neg_of_bound 21063455 16777216 Bool.false 2601453 8388608 1 2560000 (Ns204p966 rfl rfl)) rfl rfl) 

noncomputable def Ns204p968 := @Ns204p934 17041332249589043461 737869762948382064640000 (Ns204p935 qz29 (@Enclosure.Real.IsNear.of_eq qz698 (@Inv.inv Real Real.instInv (Real.sqrt qz120)) Bool.false 2822083 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz115 (BSN.t_div_two_pi_nonneg qz114 490524 1000 qz117)) Ns204p939) rfl) (@Ns204p940 140737488355328 6019711432379 87960930222080000 (BSN.correction_mk qz116 (BSN.cos_two_pi_p_ne_zero_mk qz114 490524 1000 8 qz117 rfl rfl (@BSN.floor_sqrt_eq_dec qz114 490524 1000 8 qz117 rfl rfl rfl))) (@Ns204p941 16777216 2601453 8388608 298471 10485760000 85121490648297 140737488355328 6019711432379 87960930222080000 (@Ns204p942 16777216 (Ns204p953 rfl rfl rfl rfl rfl) rfl) (Ns204p967 rfl) rfl)) 

noncomputable def Ns204p969 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz114) (hardyZApproximantRS₀ qz114) Bool.false 4102407237536825619333 1180591620717411303424 1068757189566166323461 737869762948382064640000 (@Eq.refl Real (hardyZApproximantRS₀ qz114)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz114) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 8) (@HMul.hMul Real Real Real qz5 qz696 (Zeta.RiemannSiegel.correction qz116))) Bool.false 4102407237536825619333 1180591620717411303424 1068757189566166323461 737869762948382064640000 (BSN.hardyZApproximantRS₀_eq qz114 8 (@BSN.floor_sqrt_eq_dec qz114 490524 1000 8 qz117 rfl rfl rfl)) (@Ns204p869 4102407237536825619333 1180591620717411303424 1068757189566166323461 737869762948382064640000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz114) qz114 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz114) qz114 8)) Bool.false 123424887 33554432 95653 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz114) qz114 8) (Ns204p933 (Ns204p932 rfl rfl rfl rfl) rfl rfl)) (Ns204p968 rfl) rfl rfl)) 

theorem RS205to222.d50 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz114) Bool.false 4102407237536825619333 1180591620717411303424 1068757189566166323461 737869762948382064640000 := Ns204p969 

noncomputable def Ns204p970 := nat_lit 26465863097160216263492894720 

noncomputable abbrev qz878 := (Enclosure.sfrac Bool.false 491965 1000)

noncomputable abbrev qz701 := qz878

noncomputable abbrev qz469 := qz701

noncomputable abbrev qz127 := qz469

noncomputable abbrev qz879 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 491965 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz702 := qz879

noncomputable abbrev qz470 := qz702

noncomputable abbrev qz128 := qz470

noncomputable abbrev qz880 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 491965 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz703 := qz880

noncomputable abbrev qz471 := qz703

noncomputable abbrev qz129 := qz471

noncomputable abbrev qz704 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz128 qz9))

noncomputable def Ns204p971 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz127) qz127 8) (@HMul.hMul Real Real Real qz5 qz704 (Zeta.RiemannSiegel.correction qz129)) 165257173 67108864 95931 67108864 30967725571308482859 147573952589676412928 394057845154191951 18446744073709551616000 Ns204p970 

noncomputable def Ns204p972 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz127) qz127 Real.sin BSN.quadSignNeg 7 8 491965 1000 125 134217728 67108864 2251799813685248 Bool.false 110895926616 1804 279097919 53 47453128 8 

noncomputable def Ns204p973 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz127) qz127 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 491965 1000 35 83 134217728 67108864 2251799813685248 Bool.false 110895926616 1804 

noncomputable def Ns204p974 := Ns204p973 240485871 53 54794152 8 261175631 53 50729528 8 Bool.true 192998995 64126 Bool.true 35699915 Bool.true 94559415 7074237752028440 1 Bool.false 35280451 Bool.false Bool.false 86928811 Bool.false Bool.true 145739814 

noncomputable def Ns204p975 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz127) qz127 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 491965 1000 91 21 134217728 67108864 2251799813685248 Bool.false 110895926616 1804 

noncomputable def Ns204p976 := Ns204p975 186065264 53 67108856 8 216015088 53 60023992 8 Bool.true 197758403 37699 Bool.false 172916026 Bool.false 196660851 7074237752028440 1 Bool.false 128898609 Bool.false Bool.false 133470650 Bool.true Bool.true 192998995 

noncomputable def Ns204p977 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz127) qz127 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 491965 1000 308 181 134217728 67108864 2251799813685248 Bool.false 110895926616 1804 

noncomputable def Ns204p978 := Ns204p977 93032624 53 94906264 8 147453232 53 77490640 16 Bool.true 134217720 1861 Bool.false 191887796 Bool.false 194100077 7074237752028440 1 Bool.false 18878112 Bool.false Bool.false 133176564 Bool.true Bool.true 197758403 

noncomputable def Ns204p979 := nat_lit 24309976685494206372691589098796125421485375531245017 

noncomputable def Ns204p980 := nat_lit 29422449841211283971473118911331079385030380748800 

noncomputable def Ns204p981 := nat_lit 13832905418668313840078789500000000 

noncomputable def Ns204p982 := nat_lit 40831851568239435584063866268205000000 

noncomputable abbrev qz705 := (@Eq.refl Real qz878)

noncomputable abbrev qz472 := qz705

noncomputable abbrev qz130 := qz472

noncomputable def Ns204p983 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz127 491965 1000 968119244900 16000000 983930 4000 2000 Ns204p981 Ns204p982 qz130 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns204p984 := nat_lit 121549883427471031863457945493980627107426877656225085000000 

noncomputable abbrev qz473 := (Enclosure.sfrac Bool.false 491965 2000)

noncomputable abbrev qz706 := (Real.log (Enclosure.sfrac Bool.false 968119244900 16000000))

noncomputable abbrev qz131 := (@HSub.hSub Real Real Real qz345 (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 491965 4000) qz706) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 983930)))))) qz473)

noncomputable abbrev qz474 := (@HSub.hSub Real Real Real qz12 qz131 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 491965 2000) (Real.log Real.pi)))

noncomputable def Ns204p985 := @Enclosure.Real.IsNear.addLit_ft_p qz474 (Enclosure.sfrac Bool.true Ns204p981 Ns204p982) 2976841083550355968337 3602879701896396800 1100508364032513 81920000000000000000 Ns204p981 Ns204p982 0 1 Ns204p984 

noncomputable def Ns204p986 := nat_lit 1598179387404747806645728313344 

noncomputable abbrev qz475 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 491965 2000) (Real.log Real.pi))

noncomputable def Ns204p987 := @Enclosure.Real.IsNear.subLit_ff_p qz131 qz475 159654105043303997945 144115188075855872 61030902239 10000000000000000 3779350007073 13421772800 98393 13421772800 Ns204p986 2976841083550355968337 3602879701896396800 

noncomputable def Ns204p988 := nat_lit 7982705252165199897250000 

noncomputable abbrev qz132 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 491965 4000) qz706) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 983930))))))

noncomputable def Ns204p989 := @Enclosure.Real.IsNear.subLit_ff_p qz132 qz473 4877597982354330374481 3602879701896396800 61030902239 10000000000000000 491965 2000 0 1 Ns204p988 159654105043303997945 144115188075855872 61030902239 10000000000000000 

noncomputable def Ns204p990 := nat_lit 10983374227897022699208875952505356288 

noncomputable def Ns204p991 := nat_lit 26621808220278527784648704 

noncomputable def Ns204p992 := nat_lit 551165450516354131761193298458225598595805913543971193716629537154196530304391096328658081313165123741423361785890685585867740526155958479533825070250000000000000000000000000000 

noncomputable def Ns204p993 := nat_lit 17169581126792771232299967740731713843311583996637334312901267010572384534225345626896604343781654551708108727101843876585393352053747093160559592150000000000000000000000000000 

noncomputable def Ns204p994 := nat_lit 1555313927389434866443954406063130197062359569010411349485553515896660540260879435773651840922761290107079418886530339205807198366495385671350000000000000000000000000000 

noncomputable def Ns204p995 := BSN.log_dyadic_bound 443831244900 1492407244900 8 7 Ns204p992 67108864 20480000 Ns204p993 Ns204p994 41158813 1936238489800 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 443831244900) (BSN.artanhQ 1492407244900) 0 7 Ns204p993 Ns204p992 Ns204p994 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns204p996 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 491965 4000) qz706 491965 4000 0 1 49586981945258617 4503599627370496 2441407 50000000000000 4879011914539831102481 3602879701896396800 240217358951 40000000000000000 (Enclosure.Real.IsNear.const Bool.false 491965 4000) (BSN.isNear_log_sfrac 968119244900 16000000 49586981945258617 4503599627370496 2441407 50000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 968119244900) qz352)) Bool.false Ns204p991 Ns204p89 1000000307200000 20480000000000000000000 49586981945258617 4503599627370496 2441407 50000000000000 (BSN.log_rat_reduce_isNear 968119244900 16000000 15 1936238489800 1048576000000 41158813 67108864 24973259072661432 36028797018963968 20480000 1000000000000000 rfl rfl rfl rfl (Ns204p995 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns204p997 := BSN.arctan_dyadic_bound_f 1000 983930 1 0 8388608 2560000 0 1 1 0 1 1 8525 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 983930) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 983930) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz476 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 983930)))

noncomputable def Ns204p998 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz476 884279719003555 562949953421312 1 2000000000000000 8525 8388608 1 2560000 7413076776718056816640 883707615937955 562949953421312 781250001 2000000000000000 qz17 (Ns204p997 rfl) rfl rfl 

noncomputable def Ns204p999 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 491965 4000) qz706) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz476)) 4879011914539831102481 3602879701896396800 240217358951 40000000000000000 883707615937955 2251799813685248 781250001 8000000000000000 Ns204p990 4877597982354330374481 3602879701896396800 61030902239 10000000000000000 (Ns204p996 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz476) 1 4 0 1 883707615937955 562949953421312 781250001 2000000000000000 883707615937955 2251799813685248 781250001 8000000000000000 qz355 Ns204p998 rfl) 

noncomputable def Ns204p1000 := @Ns204p985 Ns204p979 Ns204p980 1100508364032513 81920000000000000000 (@Ns204p987 1100508364032513 81920000000000000000 (Ns204p989 (Ns204p999 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 491965 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz473 (Real.log Real.pi) 491965 2000 0 1 38410761 33554432 1 33554432 3779350007073 13421772800 98393 13421772800 (Enclosure.Real.IsNear.const Bool.false 491965 2000) RS205to222.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns204p981 Ns204p982) 

noncomputable def Ns204p1001 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz127) Bool.false Ns204p979 Ns204p980 1100508364032513 81920000000000000000 13861990827 16777216 113 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz127) (@HAdd.hAdd Real Real Real qz356 qz474 (Enclosure.sfrac Bool.true Ns204p981 Ns204p982)) Bool.false Ns204p979 Ns204p980 1100508364032513 81920000000000000000 Ns204p983 (Ns204p1000 rfl rfl)) 

noncomputable def Ns204p1002 := nat_lit 3798366479816200651014144 

noncomputable def Ns204p1003 := nat_lit 857512121178347186715632462994718250303969286017571891265626048109217244762012610162015830293247125668692151813896332002797873007221601 

noncomputable def Ns204p1004 := nat_lit 611793374847720236506953550215379645789810653416971313340262031459184807670501257108028373191864342494856666396212908853299829601 

noncomputable def Ns204p1005 := nat_lit 4282230462895172541854274326283914480115127799171880236238265731876641888724952183028398893430961085964245072319106065776345305540254561 

noncomputable def Ns204p1006 := BSN.sin_dyadic_bound_f 53978034199 34359738368 4 3 16777216 5125001 Ns204p1003 Ns204p217 Ns204p1004 Ns204p1005 Ns204p220 Ns204p1004 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53978034199) qz357 0 3 Ns204p1003 Ns204p217 Ns204p1004 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53978034199) qz358 0 3 Ns204p1005 Ns204p220 Ns204p1004 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1007 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz127) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13861990827) qz369) Bool.false 13861990827 16777216 113 8388608 Bool.true 16777215 16777216 1 2560000 (Ns204p1001 rfl) (Enclosure.sfrac_false_div 13861990827 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13861990827) qz369) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns204p1002) qz371) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 131 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q1 13861990827 16777216 226375608064910080 72057594037927936 131 Ns204p1002 Ns204p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns204p1002 Ns204p89 53978034199 34359738368 5125001 5120000 (Ns204p1006 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p1008 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz127) Bool.false Ns204p979 Ns204p980 1100508364032513 81920000000000000000 110895926616 134217728 1804 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz127) (@HAdd.hAdd Real Real Real qz356 qz474 (Enclosure.sfrac Bool.true Ns204p981 Ns204p982)) Bool.false Ns204p979 Ns204p980 1100508364032513 81920000000000000000 Ns204p983 (Ns204p1000 rfl rfl)) 

noncomputable def Ns204p1009 := Ns204p978 37699 BSN.abs_quadSignPos (BSN.cos_quad_nat0 308 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 18878112 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 181 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133176564 134217728) qz130 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 1) Bool.true 16777215 16777216 72673 5242880000 134217720 134217728 1861 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz127)) Bool.true 16777215 16777216 72673 5242880000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz127) qz127) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz127)) Bool.true 16777215 16777216 297668608 21474836480000 16777215 16777216 72673 5242880000 (Ns204p1007 rfl rfl) rfl)) rfl) (Ns204p1008 rfl) RS205to222.d7 

noncomputable def Ns204p1010 := nat_lit 2856756639421028657659141762978516499389346644819775649061135365097300307913535072293636025440337496375296 

noncomputable def Ns204p1011 := nat_lit 2492116011927337084925692997624655997079560903730589346918886058365911339792780064819503773113122816 

noncomputable def Ns204p1012 := nat_lit 17302316497710836341550751419512256760566351697672769443034295277417974672031766575807492292520056937512960 

noncomputable def Ns204p1013 := BSN.cos_dyadic_bound_f 191887796 134217728 4 3 134217728 67108864 Ns204p1010 Ns204p230 Ns204p1011 Ns204p1012 Ns204p233 Ns204p1011 18878112 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 191887796) qz363 0 3 Ns204p1010 Ns204p230 Ns204p1011 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 191887796) qz364 0 3 Ns204p1012 Ns204p233 Ns204p1011 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1014 := nat_lit 7767992973405307869935988857422816863195382527405248843948133478684755655955807872313586469459783445609521 

noncomputable def Ns204p1015 := nat_lit 2859621094722480500397730522304569947661274231567061988501233309926157559026140925222281980695247921 

noncomputable def Ns204p1016 := nat_lit 38805275854435535757373223973952534287391768889811385220466878515607206293980916762001745068307168708754481 

noncomputable def Ns204p1017 := BSN.sin_dyadic_bound_f 194100077 134217728 4 3 134217728 67108864 Ns204p1014 Ns204p256 Ns204p1015 Ns204p1016 Ns204p259 Ns204p1015 133176564 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 194100077) qz361 0 3 Ns204p1014 Ns204p256 Ns204p1015 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 194100077) qz362 0 3 Ns204p1016 Ns204p259 Ns204p1015 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1018 := nat_lit 4890065138335830418681997566333637082972309184648512372433659284336327226304913823267832295974648732389376 

noncomputable def Ns204p1019 := nat_lit 714534085670621883153942630875259945163410586930469206732760391589309441017835193035464181655474176 

noncomputable def Ns204p1020 := nat_lit 24436565793088172008961873593494874731919856640390065270610437338134314590241885488363896841879695773863936 

noncomputable def Ns204p1021 := BSN.sin_dyadic_bound_f 172916026 134217728 4 3 134217728 67108864 Ns204p1018 Ns204p256 Ns204p1019 Ns204p1020 Ns204p259 Ns204p1019 128898609 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 172916026) qz361 0 3 Ns204p1018 Ns204p256 Ns204p1019 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 172916026) qz362 0 3 Ns204p1020 Ns204p259 Ns204p1019 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1022 := nat_lit 8186748110820696949203797282591744577171775445425939763799718700097491306553833371841550932586303986068401 

noncomputable def Ns204p1023 := nat_lit 3346686020030894096782851001374371589205778116691361499073196259191138702108519240297450068960865201 

noncomputable def Ns204p1024 := nat_lit 40895216028652226034543970722809795993432500401803873738705966390086909964231234697050089617721494015830961 

noncomputable def Ns204p1025 := BSN.sin_dyadic_bound_f 196660851 134217728 4 3 134217728 67108864 Ns204p1022 Ns204p256 Ns204p1023 Ns204p1024 Ns204p259 Ns204p1023 133470650 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 196660851) qz361 0 3 Ns204p1022 Ns204p256 Ns204p1023 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 196660851) qz362 0 3 Ns204p1024 Ns204p259 Ns204p1023 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1026 := Ns204p976 64126 BSN.abs_quadSignPos (BSN.cos_quad_nat3 91 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 128898609 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 21 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133470650 134217728) qz130 rfl rfl (Ns204p1009 RS205to222.d9 RS205to222.d11 RS205to222.d13 RS205to222.d17 (Ns204p1013 rfl rfl) (Ns204p1017 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns204p1008 rfl) RS205to222.d19 RS205to222.d21 RS205to222.d23 RS205to222.d25 RS205to222.d17 (Ns204p1021 rfl rfl) (Ns204p1025 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns204p1027 := nat_lit 1624309290395629053803002200625 

noncomputable def Ns204p1028 := BSN.sin_dyadic_bound_f 35699915 134217728 2 1 134217728 67108864 Ns204p1027 Ns204p129 Ns204p1027 Ns204p1027 Ns204p130 Ns204p1027 35280451 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 35699915) qz361 0 1 Ns204p1027 Ns204p129 Ns204p1027 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 35699915) qz362 0 1 Ns204p1027 Ns204p130 Ns204p1027 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1029 := nat_lit 78464968738738570835845091308574049751107564946584267431587986530625 

noncomputable def Ns204p1030 := nat_lit 6392021306800816015760387194854859961613762555639054299937890625 

noncomputable def Ns204p1031 := nat_lit 205493140566961436582235436609854651003439104958821094328149589090625 

noncomputable def Ns204p1032 := BSN.sin_dyadic_bound_f 94559415 134217728 3 2 134217728 67108864 Ns204p1029 Ns204p106 Ns204p1030 Ns204p1031 Ns204p109 Ns204p1030 86928811 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 94559415) qz361 0 2 Ns204p1029 Ns204p106 Ns204p1030 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 94559415) qz362 0 2 Ns204p1031 Ns204p109 Ns204p1030 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1033 := Ns204p974 86064 BSN.abs_quadSignPos (BSN.cos_quad_nat3 35 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 35280451 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 83 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 86928811 134217728) qz130 rfl rfl (Ns204p1026 rfl rfl) (Ns204p1008 rfl) RS205to222.d27 RS205to222.d29 RS205to222.d31 RS205to222.d33 RS205to222.d17 (Ns204p1028 rfl rfl) (Ns204p1032 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns204p1034 := nat_lit 10476105391225775385757060843536 

noncomputable def Ns204p1035 := BSN.sin_dyadic_bound_f 56891838 134217728 2 1 134217728 67108864 Ns204p1034 Ns204p129 Ns204p1034 Ns204p1034 Ns204p130 Ns204p1034 55203433 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 56891838) qz361 0 1 Ns204p1034 Ns204p129 Ns204p1034 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 56891838) qz362 0 1 Ns204p1034 Ns204p130 Ns204p1034 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1036 := Ns204p972 Bool.true 145739814 86064 Bool.true 56891838 7074237752028440 1 Bool.false 55203433 Bool.true Bool.true 165257173 95931 BSN.abs_quadSignNeg qz387 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 55203433 134217728) qz130 rfl (Ns204p1033 rfl) (Ns204p1008 rfl) RS205to222.d35 RS205to222.d37 RS205to222.d17 (Ns204p1035 rfl rfl) rfl 

noncomputable def Ns204p1037 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 8) 165257173 134217728 95931 134217728 165257173 134217728 95931 134217728 44360884591525888 165257173 67108864 95931 67108864 (Ns204p1036 rfl rfl rfl rfl) 

noncomputable def Ns204p1038 := @Enclosure.Real.IsNear.mulLit_ff qz704 (Zeta.RiemannSiegel.correction qz129) 1410007 4194304 1 8388608 21962816901837 35184372088832 1392493192759 21990232555520000 30967725571308482859 147573952589676412928 

noncomputable abbrev qz707 := (@HPow.hPow Real Real Real qz7 qz128 qz9)

noncomputable def Ns204p1039 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz707 1 1 0 1 1410007 4194304 1 8388608 1410007 4194304 1 8388608 

noncomputable def Ns204p1040 := @Enclosure.Real.IsNear.sqrt_image qz128 262726725561 3355443200 98393 3355443200 74227870 74227899 8388608 (@Enclosure.Real.IsNear.of_eq qz128 (@HMul.hMul Real Real Real qz5 qz127 qz3) Bool.false 262726725561 3355443200 98393 3355443200 (BSN.t_div_two_pi_mk qz127 491965 1000 qz130) (@Enclosure.Real.IsNear.mulLit_ff qz127 qz3 491965 1000 0 1 2670177 16777216 1 16777216 262726725561 3355443200 98393 3355443200 (Enclosure.Real.IsNear.const Bool.false 491965 1000) RS205to222.d40 rfl)) 

noncomputable abbrev qz881 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 491965 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz708 := qz881

noncomputable abbrev qz477 := qz708

noncomputable abbrev qz133 := qz477

noncomputable def Ns204p1041 := @Enclosure.Real.IsNear.sqrt_image qz133 148455769 16777216 29 16777216 24953326 24953332 8388608 (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 148455769 16777216 29 16777216 148455769 16777216 29 16777216 (Ns204p1040 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns204p1042 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz133) 24953329 8388608 3 8388608 2820013 2820015 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz133) Bool.false 49906658 16777216 6 16777216 24953329 8388608 3 8388608 (Ns204p1041 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns204p1043 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz133)) Bool.false 5640028 16777216 2 16777216 1410007 4194304 1 8388608 (Ns204p1042 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz134 := (@HMul.hMul Real Real Real qz342 qz340 qz471)

noncomputable abbrev qz709 := (@HMul.hMul Real Real Real qz844 qz880 qz880)

noncomputable abbrev qz478 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz709 qz703) qz640)

noncomputable abbrev qz135 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz478))

noncomputable def Ns204p1044 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz129) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz134)) qz135) Bool.false 21962816901837 

noncomputable def Ns204p1045 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz134)) qz135 28880469 16777216 563 

noncomputable def Ns204p1046 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz134)) Bool.false 28880469 16777216 563 16777216 28880469 16777216 563 

noncomputable def Ns204p1047 := @Enclosure.Real.IsNear.recentre' (Real.cos qz134) Bool.false 9746205 16777216 485257216 42949672960000 9746205 16777216 118471 10485760000 

noncomputable def Ns204p1048 := @Enclosure.Real.IsNear.cos_image qz134 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44730125) qz359) Bool.false 44730125 8388608 183 16777216 Bool.false 9746205 16777216 1 

noncomputable def Ns204p1049 := nat_lit 156519237396916231821622863 

noncomputable def Ns204p1050 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz129 884279719003555 140737488355328 1 500000000000000 14238041 16777216 29 16777216 12590410894641095235755 2361183241434822606848 Ns204p1049 

noncomputable def Ns204p1051 := @Enclosure.Real.IsNear.subLit_ff_p qz133 qz1 148455769 16777216 29 16777216 8 1 0 1 14238041 14238041 16777216 29 

noncomputable def Ns204p1052 := @Ns204p1051 16777216 (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 148455769 16777216 29 16777216 148455769 16777216 29 16777216 (Ns204p1040 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns204p1053 := @Enclosure.Real.IsNear.recentre' qz134 Bool.false 12590410894641095235755 2361183241434822606848 Ns204p1049 Ns204p843 44730125 8388608 183 16777216 (@Ns204p1050 Ns204p843 RS205to222.d39 (Ns204p1052 rfl rfl) rfl) 

noncomputable def Ns204p1054 := nat_lit 205762710772148421521389573031853889350625 

noncomputable def Ns204p1055 := BSN.sin_dyadic_bound_f 21298139545 34359738368 2 1 16777216 5125001 Ns204p1054 Ns204p419 Ns204p1054 Ns204p1054 Ns204p420 Ns204p1054 9746205 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 21298139545) qz357 0 1 Ns204p1054 Ns204p419 Ns204p1054 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 21298139545) qz358 0 1 Ns204p1054 Ns204p420 Ns204p1054 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1056 := @Ns204p1048 2560000 (Ns204p1053 rfl) (Enclosure.sfrac_false_div 44730125 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44730125) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 749361666577034987438080) qz360) 226375608064910080 72057594037927936 Bool.false 9746205 16777216 0 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q3 44730125 8388608 226375608064910080 72057594037927936 0 749361666577034987438080 Ns204p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 9746205 16777216 749361666577034987438080 Ns204p100 21298139545 34359738368 5125001 5120000 (Ns204p1055 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p1057 := @Enclosure.Real.IsNear.inv_image (Real.cos qz134) 9746205 16777216 118471 10485760000 14439953 14440516 8388608 (Ns204p1047 (Ns204p1056 rfl rfl) rfl) rfl 

noncomputable def Ns204p1058 := @Enclosure.Real.IsNear.recentre' qz135 Bool.false 3041892 8388608 

noncomputable abbrev qz136 := (@HMul.hMul Real Real Real qz342 qz340 qz478)

noncomputable def Ns204p1059 := @Enclosure.Real.IsNear.cos_image qz136 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 628997)) (@Nat.cast Real Real.instNatCast 524288)) Bool.true 628997 524288 

noncomputable def Ns204p1060 := nat_lit 47525669915414745215740101005 

noncomputable def Ns204p1061 := nat_lit 35415081153493406027873071634136933 

noncomputable def Ns204p1062 := @Enclosure.Real.IsNear.recentre' qz136 Bool.true Ns204p1060 Ns204p533 Ns204p1061 

noncomputable abbrev qz137 := qz478

noncomputable def Ns204p1063 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz137 884279719003555 140737488355328 1 500000000000000 53745063800591 

noncomputable abbrev qz479 := (@HSub.hSub Real Real Real qz634 qz709 qz703)

noncomputable abbrev qz138 := qz479

noncomputable def Ns204p1064 := @Enclosure.Real.IsNear.subLit_tf qz138 qz27 36152877756175 281474976710656 1312346483 281474976710656 1 16 

noncomputable abbrev qz480 := qz709

noncomputable abbrev qz139 := qz480

noncomputable def Ns204p1065 := @Enclosure.Real.IsNear.subLit_ff_n qz139 qz129 202721811517681 281474976710656 825807219 281474976710656 14238041 16777216 29 16777216 

noncomputable def Ns204p1066 := @Enclosure.Real.IsNear.mulLit_ff qz129 qz129 14238041 16777216 29 16777216 14238041 16777216 29 16777216 202721811517681 281474976710656 

noncomputable def Ns204p1067 := nat_lit 19893832446100557782229182710427553917584139689441 

noncomputable def Ns204p1068 := nat_lit 230186507879617209617080361152814575595809375518720 

noncomputable def Ns204p1069 := nat_lit 24501269801363628159998801343253109901087022561 

noncomputable def Ns204p1070 := nat_lit 59632494798698946090367550528596155532950245023201 

noncomputable def Ns204p1071 := nat_lit 10358392854582774432768616251876655901811421898342400 

noncomputable def Ns204p1072 := BSN.cos_dyadic_bound_f 628997 524288 3 2 8388608 2560000 Ns204p1067 Ns204p1068 Ns204p1069 Ns204p1070 Ns204p1071 Ns204p1069 3041892 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 628997) (BSN.cosEvenQ 524288) 0 2 Ns204p1067 Ns204p1068 Ns204p1069 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 628997) (BSN.cosOddQ 524288) 0 2 Ns204p1070 Ns204p1071 Ns204p1069 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1073 := @Ns204p1058 319074304 10737418240000 760473 2097152 77899 2621440000 (@Ns204p1059 123 4194304 Bool.false 3041892 8388608 1 2560000 (@Ns204p1062 Ns204p536 628997 524288 123 4194304 (@Ns204p1063 281474976710656 1312346483 281474976710656 Ns204p1060 Ns204p533 Ns204p1061 Ns204p536 RS205to222.d39 (@Ns204p1064 0 1 859921020809456 53745063800591 281474976710656 1312346483 281474976710656 (@Ns204p1065 606544639136943308800 36152877756175 281474976710656 1312346483 281474976710656 (@Ns204p1066 825807219 281474976710656 (Ns204p1052 rfl rfl) (Ns204p1052 rfl rfl) rfl) (Ns204p1052 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 628997 524288) (BSN.cos_neg_of_bound 628997 524288 Bool.false 3041892 8388608 1 2560000 (Ns204p1072 rfl rfl)) rfl rfl) 

noncomputable def Ns204p1074 := @Ns204p1038 394057845154191951 18446744073709551616000 (Ns204p1039 qz29 (@Enclosure.Real.IsNear.of_eq qz707 (@Inv.inv Real Real.instInv (Real.sqrt qz133)) Bool.false 1410007 4194304 1 8388608 (BSN.rpow_neg_quarter_mk qz128 (BSN.t_div_two_pi_nonneg qz127 491965 1000 qz130)) Ns204p1043) rfl) (@Ns204p1044 35184372088832 1392493192759 21990232555520000 (BSN.correction_mk qz129 (BSN.cos_two_pi_p_ne_zero_mk qz127 491965 1000 8 qz130 rfl rfl (@BSN.floor_sqrt_eq_dec qz127 491965 1000 8 qz130 rfl rfl rfl))) (@Ns204p1045 16777216 760473 2097152 77899 2621440000 21962816901837 35184372088832 1392493192759 21990232555520000 (@Ns204p1046 16777216 (Ns204p1057 rfl rfl rfl rfl rfl) rfl) (Ns204p1073 rfl) rfl)) 

noncomputable def Ns204p1075 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz127) (hardyZApproximantRS₀ qz127) Bool.true 394372092145088557355 147573952589676412928 26763370336199055951 18446744073709551616000 (@Eq.refl Real (hardyZApproximantRS₀ qz127)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz127) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz127) qz127 8) (@HMul.hMul Real Real Real qz5 qz704 (Zeta.RiemannSiegel.correction qz129))) Bool.true 394372092145088557355 147573952589676412928 26763370336199055951 18446744073709551616000 (BSN.hardyZApproximantRS₀_eq qz127 8 (@BSN.floor_sqrt_eq_dec qz127 491965 1000 8 qz130 rfl rfl rfl)) (@Ns204p971 394372092145088557355 147573952589676412928 26763370336199055951 18446744073709551616000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz127) qz127 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 8)) Bool.true 165257173 67108864 95931 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz127) qz127 8) (Ns204p1037 (Ns204p1036 rfl rfl rfl rfl) rfl rfl)) (Ns204p1074 rfl) rfl rfl)) 

theorem RS205to222.d51 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz127) Bool.true 394372092145088557355 147573952589676412928 26763370336199055951 18446744073709551616000 := Ns204p1075 

noncomputable def Ns204p1076 := nat_lit 12492288100104592891215609856 

noncomputable abbrev qz882 := (Enclosure.sfrac Bool.false 493405 1000)

noncomputable abbrev qz710 := qz882

noncomputable abbrev qz481 := qz710

noncomputable abbrev qz140 := qz481

noncomputable abbrev qz883 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 493405 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz711 := qz883

noncomputable abbrev qz482 := qz711

noncomputable abbrev qz141 := qz482

noncomputable abbrev qz884 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 493405 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz712 := qz884

noncomputable abbrev qz483 := qz712

noncomputable abbrev qz142 := qz483

noncomputable abbrev qz713 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz141 qz9))

noncomputable def Ns204p1077 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz140) qz140 8) (@HMul.hMul Real Real Real qz5 qz713 (Zeta.RiemannSiegel.correction qz142)) 12555957 33554432 12027 8388608 511247728719462694615 2361183241434822606848 5752239264953372819 295147905179352825856000 Ns204p1076 

noncomputable def Ns204p1078 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz140) qz140 Real.sin BSN.quadSignNeg 7 8 493405 1000 125 134217728 67108864 2251799813685248 Bool.false 111317455429 1810 279097919 53 47453128 8 

noncomputable def Ns204p1079 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz140) qz140 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 493405 1000 34 83 134217728 67108864 2251799813685248 Bool.false 111317455429 1810 

noncomputable def Ns204p1080 := Ns204p1079 240485871 53 54794152 8 261175631 53 50729528 8 Bool.false 35868401 64317 Bool.true 171299471 Bool.true 49123511 7074237752028440 1 Bool.false 38960258 Bool.true Bool.false 48034109 Bool.false Bool.false 38118128 

noncomputable def Ns204p1081 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz140) qz140 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 493405 1000 92 22 134217728 67108864 2251799813685248 Bool.false 111317455429 1810 

noncomputable def Ns204p1082 := Ns204p1081 186065264 53 67108856 8 216015088 53 60023992 8 Bool.false 37406509 37812 Bool.false 115682144 Bool.false 96299223 7074237752028440 1 Bool.false 87375344 Bool.false Bool.false 101127906 Bool.true Bool.false 35868401 

noncomputable def Ns204p1083 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz140) qz140 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 493405 1000 310 182 134217728 67108864 2251799813685248 Bool.false 111317455429 1810 

noncomputable def Ns204p1084 := Ns204p1083 93032624 53 94906264 8 147453232 53 77490640 16 Bool.false 134217680 1869 Bool.false 57792203 Bool.false 192467521 7074237752028440 1 Bool.false 121966539 Bool.true Bool.false 18303976 Bool.true Bool.false 37406509 

noncomputable def Ns204p1085 := nat_lit 24834089809238951741365661596046070535942577648670137 

noncomputable def Ns204p1086 := nat_lit 29942968946510380990380698855409436857075970867200 

noncomputable def Ns204p1087 := nat_lit 14036540983451135494914101500000000 

noncomputable def Ns204p1088 := nat_lit 41554216937564865383931548913645000000 

noncomputable abbrev qz714 := (@Eq.refl Real qz882)

noncomputable abbrev qz484 := qz714

noncomputable abbrev qz143 := qz484

noncomputable def Ns204p1089 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz140 493405 1000 973794976100 16000000 986810 4000 2000 Ns204p1087 Ns204p1088 qz143 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns204p1090 := nat_lit 124170449046194758706828307980230352679712888243350685000000 

noncomputable abbrev qz485 := (Enclosure.sfrac Bool.false 493405 2000)

noncomputable abbrev qz715 := (Real.log (Enclosure.sfrac Bool.false 973794976100 16000000))

noncomputable abbrev qz144 := (@HSub.hSub Real Real Real qz345 (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 493405 4000) qz715) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 986810)))))) qz485)

noncomputable abbrev qz486 := (@HSub.hSub Real Real Real qz12 qz144 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 493405 2000) (Real.log Real.pi)))

noncomputable def Ns204p1091 := @Enclosure.Real.IsNear.addLit_ft_p qz486 (Enclosure.sfrac Bool.true Ns204p1087 Ns204p1088) 2988156407921951709553 3602879701896396800 1103706176974881 81920000000000000000 Ns204p1087 Ns204p1088 0 1 Ns204p1090 

noncomputable def Ns204p1092 := nat_lit 40106356397992555978191955558400 

noncomputable abbrev qz487 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 493405 2000) (Real.log Real.pi))

noncomputable def Ns204p1093 := @Enclosure.Real.IsNear.subLit_ff_p qz144 qz487 4005637463775766190449 3602879701896396800 61206683543 10000000000000000 3790412306241 13421772800 98681 13421772800 Ns204p1092 2988156407921951709553 3602879701896396800 

noncomputable def Ns204p1094 := nat_lit 8011274927551532380898000 

noncomputable abbrev qz145 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 493405 4000) qz715) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 986810))))))

noncomputable def Ns204p1095 := @Enclosure.Real.IsNear.subLit_ff_p qz145 qz485 4894476893432862022001 3602879701896396800 61206683543 10000000000000000 493405 2000 0 1 Ns204p1094 4005637463775766190449 3602879701896396800 61206683543 10000000000000000 

noncomputable def Ns204p1096 := nat_lit 11021382156718870131467735520665141248 

noncomputable def Ns204p1097 := nat_lit 26635941812945909083799552 

noncomputable def Ns204p1098 := nat_lit 581247728138802298620457638256308477873326214102975248696314387646362381623968576126515542731486586034008492109140172593710192405201705907766895630250000000000000000000000000000 

noncomputable def Ns204p1099 := nat_lit 18451292332493034464260407449662602592748571279596311610602969225963191505411212151400073813358577412208137816828796826251480804040860992333521928150000000000000000000000000000 

noncomputable def Ns204p1100 := nat_lit 1858137943651943614373321073307150959913935365204188292875835133394042556751149184284170997788213642333397201737975722961721217550698742375350000000000000000000000000000 

noncomputable def Ns204p1101 := BSN.log_dyadic_bound 449506976100 1498082976100 8 7 Ns204p1098 67108864 20480000 Ns204p1099 Ns204p1100 41551099 1947589952200 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 449506976100) (BSN.artanhQ 1498082976100) 0 7 Ns204p1099 Ns204p1098 Ns204p1100 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns204p1102 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 493405 4000) qz715 493405 4000 0 1 49613307813081721 4503599627370496 2441407 50000000000000 4895890828302717310001 3602879701896396800 240920484167 40000000000000000 (Enclosure.Real.IsNear.const Bool.false 493405 4000) (BSN.isNear_log_sfrac 973794976100 16000000 49613307813081721 4503599627370496 2441407 50000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 973794976100) qz352)) Bool.false Ns204p1097 Ns204p89 1000000307200000 20480000000000000000000 49613307813081721 4503599627370496 2441407 50000000000000 (BSN.log_rat_reduce_isNear 973794976100 16000000 15 1947589952200 1048576000000 41551099 67108864 24973259072661432 36028797018963968 20480000 1000000000000000 rfl rfl rfl rfl (Ns204p1101 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns204p1103 := BSN.arctan_dyadic_bound_f 1000 986810 1 0 8388608 2560000 0 1 1 0 1 1 8500 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 986810) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 986810) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz488 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 986810)))

noncomputable def Ns204p1104 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz488 884279719003555 562949953421312 1 2000000000000000 8500 8388608 1 2560000 7413090850466892349440 883709293659555 562949953421312 781250001 2000000000000000 qz17 (Ns204p1103 rfl) rfl rfl 

noncomputable def Ns204p1105 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 493405 4000) qz715) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz488)) 4895890828302717310001 3602879701896396800 240920484167 40000000000000000 883709293659555 2251799813685248 781250001 8000000000000000 Ns204p1096 4894476893432862022001 3602879701896396800 61206683543 10000000000000000 (Ns204p1102 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz488) 1 4 0 1 883709293659555 562949953421312 781250001 2000000000000000 883709293659555 2251799813685248 781250001 8000000000000000 qz355 Ns204p1104 rfl) 

noncomputable def Ns204p1106 := @Ns204p1091 Ns204p1085 Ns204p1086 1103706176974881 81920000000000000000 (@Ns204p1093 1103706176974881 81920000000000000000 (Ns204p1095 (Ns204p1105 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 493405 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz485 (Real.log Real.pi) 493405 2000 0 1 38410761 33554432 1 33554432 3790412306241 13421772800 98681 13421772800 (Enclosure.Real.IsNear.const Bool.false 493405 2000) RS205to222.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns204p1087 Ns204p1088) 

noncomputable def Ns204p1107 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz140) Bool.false Ns204p1085 Ns204p1086 1103706176974881 81920000000000000000 1739335241 2097152 227 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz140) (@HAdd.hAdd Real Real Real qz356 qz486 (Enclosure.sfrac Bool.true Ns204p1087 Ns204p1088)) Bool.false Ns204p1085 Ns204p1086 1103706176974881 81920000000000000000 Ns204p1089 (Ns204p1106 rfl rfl)) 

noncomputable def Ns204p1108 := nat_lit 855417498784277486818188958343251722139934446862037924314879347527895047987947302758237100348517134210013160524911270271307060213487921 

noncomputable def Ns204p1109 := nat_lit 607330016341752072920382489919506112730059314098337184384893423161269449421630164772455138534927124861307961849356168026361993521 

noncomputable def Ns204p1110 := nat_lit 4271783312640482372952545351234690593567679704476985546181706822679867527871692506776002202785783620060683023442688864207859332659583281 

noncomputable def Ns204p1111 := BSN.sin_dyadic_bound_f 53945107411 34359738368 4 3 16777216 5125001 Ns204p1108 Ns204p217 Ns204p1109 Ns204p1110 Ns204p220 Ns204p1109 16777210 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53945107411) qz357 0 3 Ns204p1108 Ns204p217 Ns204p1109 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53945107411) qz358 0 3 Ns204p1110 Ns204p220 Ns204p1109 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1112 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz140) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1739335241) qz372) Bool.false 1739335241 2097152 227 16777216 Bool.false 16777210 16777216 1 2560000 (Ns204p1107 rfl) (Enclosure.sfrac_false_div 1739335241 2097152) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1739335241) qz372) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474506182885305149816832) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 16777210 16777216 131 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q3 1739335241 2097152 226375608064910080 72057594037927936 131 474506182885305149816832 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777210 16777216 474506182885305149816832 302231454903657293676544 53945107411 34359738368 5125001 5120000 (Ns204p1111 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p1113 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz140) Bool.false Ns204p1085 Ns204p1086 1103706176974881 81920000000000000000 111317455429 134217728 1810 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz140) (@HAdd.hAdd Real Real Real qz356 qz486 (Enclosure.sfrac Bool.true Ns204p1087 Ns204p1088)) Bool.false Ns204p1085 Ns204p1086 1103706176974881 81920000000000000000 Ns204p1089 (Ns204p1106 rfl rfl)) 

noncomputable def Ns204p1114 := Ns204p1084 37812 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 310 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 121966539 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 182 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 18303976 134217728) qz143 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz140) qz140 1) Bool.false 8388605 8388608 145971 10485760000 134217680 134217728 1869 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz140) qz140 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz140)) Bool.false 8388605 8388608 145971 10485760000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz140) qz140) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz140)) Bool.false 16777210 16777216 597897216 42949672960000 8388605 8388608 145971 10485760000 (Ns204p1112 rfl rfl) rfl)) rfl) (Ns204p1113 rfl) RS205to222.d7 

noncomputable def Ns204p1115 := nat_lit 6081835911438885272273376959311173996868729032610651216917608742241 

noncomputable def Ns204p1116 := nat_lit 124438279644324664575932889921213449844001525846728977222417761 

noncomputable def Ns204p1117 := nat_lit 18245258857757367167490979012153679563706499094780260192798381391201 

noncomputable def Ns204p1118 := BSN.cos_dyadic_bound_f 57792203 134217728 3 2 134217728 67108864 Ns204p1115 Ns204p240 Ns204p1116 Ns204p1117 Ns204p243 Ns204p1116 121966539 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 57792203) qz363 0 2 Ns204p1115 Ns204p240 Ns204p1116 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 57792203) qz364 0 2 Ns204p1117 Ns204p243 Ns204p1116 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1119 := nat_lit 2891523488509907773367033014240555232219901415543937625859871580676874551570159776598454642552751089253121 

noncomputable def Ns204p1120 := nat_lit 2583981685234566725499679039706674461976910235583052976247434335382324204054242605730275158767696641 

noncomputable def Ns204p1121 := nat_lit 17512534826427730920011028986474720836041783228805946254980965478601564529266344638430141281030574337161985 

noncomputable def Ns204p1122 := BSN.cos_dyadic_bound_f 192467521 134217728 4 3 134217728 67108864 Ns204p1119 Ns204p230 Ns204p1120 Ns204p1121 Ns204p233 Ns204p1120 18303976 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 192467521) qz363 0 3 Ns204p1119 Ns204p230 Ns204p1120 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 192467521) qz364 0 3 Ns204p1121 Ns204p233 Ns204p1120 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1123 := nat_lit 97669005524219242095326083000219188871086856890702568119182710276096 

noncomputable def Ns204p1124 := nat_lit 32072338898641810146657553547261225640911022415290166729209020416 

noncomputable def Ns204p1125 := nat_lit 292942871894860442665684933893563044161978748627277124024089712787456 

noncomputable def Ns204p1126 := BSN.cos_dyadic_bound_f 115682144 134217728 3 2 134217728 67108864 Ns204p1123 Ns204p240 Ns204p1124 Ns204p1125 Ns204p243 Ns204p1124 87375344 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 115682144) qz363 0 2 Ns204p1123 Ns204p240 Ns204p1124 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 115682144) qz364 0 2 Ns204p1125 Ns204p243 Ns204p1124 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1127 := nat_lit 46893046199862418698726518660634223775458318561497521439978926749761 

noncomputable def Ns204p1128 := nat_lit 7395750710558043853058826943412966728417441892646291669071804481 

noncomputable def Ns204p1129 := nat_lit 140664347098166140008473438328015845392918120800707271736598636640321 

noncomputable def Ns204p1130 := BSN.cos_dyadic_bound_f 96299223 134217728 3 2 134217728 67108864 Ns204p1127 Ns204p240 Ns204p1128 Ns204p1129 Ns204p243 Ns204p1128 101127906 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 96299223) qz363 0 2 Ns204p1127 Ns204p240 Ns204p1128 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 96299223) qz364 0 2 Ns204p1129 Ns204p243 Ns204p1128 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1131 := Ns204p1082 64317 BSN.abs_quadSignPos (BSN.cos_quad_nat0 92 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 87375344 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 22 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 101127906 134217728) qz143 rfl rfl (Ns204p1114 RS205to222.d9 RS205to222.d11 RS205to222.d13 RS205to222.d17 (Ns204p1118 rfl rfl) (Ns204p1122 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns204p1113 rfl) RS205to222.d19 RS205to222.d21 RS205to222.d23 RS205to222.d25 RS205to222.d17 (Ns204p1126 rfl rfl) (Ns204p1130 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns204p1132 := nat_lit 1812651784595062213526431898414905948986964350666444774251776669627672697767206630118209230034383675507521 

noncomputable def Ns204p1133 := nat_lit 638369694669626308271752051194042300036106357665510382977510971671728135226863949882583837864543041 

noncomputable def Ns204p1134 := nat_lit 10985190787406256437467318364073136733314965276129266918482329876698604863785648954234776675987858361598785 

noncomputable def Ns204p1135 := BSN.cos_dyadic_bound_f 171299471 134217728 4 3 134217728 67108864 Ns204p1132 Ns204p230 Ns204p1133 Ns204p1134 Ns204p233 Ns204p1133 38960258 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 171299471) qz363 0 3 Ns204p1132 Ns204p230 Ns204p1133 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 171299471) qz364 0 3 Ns204p1134 Ns204p233 Ns204p1133 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1136 := nat_lit 5823144915139682987901667028641 

noncomputable def Ns204p1137 := BSN.sin_dyadic_bound_f 49123511 134217728 2 1 134217728 67108864 Ns204p1136 Ns204p129 Ns204p1136 Ns204p1136 Ns204p130 Ns204p1136 48034109 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 49123511) qz361 0 1 Ns204p1136 Ns204p129 Ns204p1136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 49123511) qz362 0 1 Ns204p1136 Ns204p130 Ns204p1136 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1138 := Ns204p1080 86320 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 34 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 38960258 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 83 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 48034109 134217728) qz143 rfl rfl (Ns204p1131 rfl rfl) (Ns204p1113 rfl) RS205to222.d27 RS205to222.d29 RS205to222.d31 RS205to222.d33 RS205to222.d17 (Ns204p1135 rfl rfl) (Ns204p1137 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns204p1139 := nat_lit 1928231574410473863794061926656 

noncomputable def Ns204p1140 := BSN.sin_dyadic_bound_f 37264028 134217728 2 1 134217728 67108864 Ns204p1139 Ns204p129 Ns204p1139 Ns204p1139 Ns204p130 Ns204p1139 36787131 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 37264028) qz361 0 1 Ns204p1139 Ns204p129 Ns204p1139 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 37264028) qz362 0 1 Ns204p1139 Ns204p130 Ns204p1139 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1141 := Ns204p1078 Bool.false 38118128 86320 Bool.true 37264028 7074237752028440 1 Bool.false 36787131 Bool.true Bool.false 25111914 96216 BSN.abs_quadSignNeg qz387 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 36787131 134217728) qz143 rfl (Ns204p1138 rfl) (Ns204p1113 rfl) RS205to222.d35 RS205to222.d37 RS205to222.d17 (Ns204p1140 rfl rfl) rfl 

noncomputable def Ns204p1142 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz140) qz140 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz140) qz140 8) 25111914 134217728 96216 134217728 25111914 134217728 96216 134217728 6740928085622784 12555957 33554432 12027 8388608 (Ns204p1141 rfl rfl rfl rfl) 

noncomputable def Ns204p1143 := @Enclosure.Real.IsNear.mulLit_ff qz713 (Zeta.RiemannSiegel.correction qz142) 5635909 16777216 1 16777216 90712559184235 140737488355328 2546571979971 43980465111040000 511247728719462694615 2361183241434822606848 

noncomputable abbrev qz716 := (@HPow.hPow Real Real Real qz7 qz141 qz9)

noncomputable def Ns204p1144 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz716 1 1 0 1 5635909 16777216 1 16777216 5635909 16777216 1 16777216 

noncomputable def Ns204p1145 := @Enclosure.Real.IsNear.sqrt_image qz141 263495736537 3355443200 98681 3355443200 74336424 74336453 8388608 (@Enclosure.Real.IsNear.of_eq qz141 (@HMul.hMul Real Real Real qz5 qz140 qz3) Bool.false 263495736537 3355443200 98681 3355443200 (BSN.t_div_two_pi_mk qz140 493405 1000 qz143) (@Enclosure.Real.IsNear.mulLit_ff qz140 qz3 493405 1000 0 1 2670177 16777216 1 16777216 263495736537 3355443200 98681 3355443200 (Enclosure.Real.IsNear.const Bool.false 493405 1000) RS205to222.d40 rfl)) 

noncomputable abbrev qz885 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 493405 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz717 := qz885

noncomputable abbrev qz489 := qz717

noncomputable abbrev qz146 := qz489

noncomputable def Ns204p1146 := @Enclosure.Real.IsNear.sqrt_image qz146 148672877 16777216 29 16777216 24971566 24971572 8388608 (@Enclosure.Real.IsNear.recentre' qz146 Bool.false 148672877 16777216 29 16777216 148672877 16777216 29 16777216 (Ns204p1145 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns204p1147 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz146) 24971569 8388608 3 8388608 2817954 2817955 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz146) Bool.false 49943138 16777216 6 16777216 24971569 8388608 3 8388608 (Ns204p1146 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns204p1148 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz146)) Bool.false 5635909 16777216 1 16777216 5635909 16777216 1 16777216 (Ns204p1147 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz147 := (@HMul.hMul Real Real Real qz342 qz340 qz483)

noncomputable abbrev qz718 := (@HMul.hMul Real Real Real qz844 qz884 qz884)

noncomputable abbrev qz490 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz718 qz712) qz640)

noncomputable abbrev qz148 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz490))

noncomputable def Ns204p1149 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz142) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz147)) qz148) Bool.false 90712559184235 

noncomputable def Ns204p1150 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz147)) qz148 26006795 16777216 459 

noncomputable def Ns204p1151 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz147)) Bool.false 26006795 16777216 459 16777216 26006795 16777216 459 

noncomputable def Ns204p1152 := @Enclosure.Real.IsNear.recentre' (Real.cos qz147) Bool.false 10823132 16777216 60977152 5368709120000 2705783 4194304 14887 1310720000 

noncomputable def Ns204p1153 := @Enclosure.Real.IsNear.cos_image qz147 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 90824379) qz369) Bool.false 90824379 16777216 23 2097152 Bool.false 10823132 16777216 1 

noncomputable def Ns204p1154 := nat_lit 782596186986446102627514251 

noncomputable def Ns204p1155 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz142 884279719003555 140737488355328 1 500000000000000 14455149 16777216 29 16777216 12782395095874519054695 2361183241434822606848 Ns204p1154 

noncomputable def Ns204p1156 := @Enclosure.Real.IsNear.subLit_ff_p qz146 qz1 148672877 16777216 29 16777216 8 1 0 1 14455149 14455149 16777216 29 

noncomputable def Ns204p1157 := @Ns204p1156 16777216 (@Enclosure.Real.IsNear.recentre' qz146 Bool.false 148672877 16777216 29 16777216 148672877 16777216 29 16777216 (Ns204p1145 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns204p1158 := @Enclosure.Real.IsNear.recentre' qz147 Bool.false 12782395095874519054695 2361183241434822606848 Ns204p1154 Ns204p521 90824379 16777216 23 2097152 (@Ns204p1155 Ns204p521 RS205to222.d39 (Ns204p1157 rfl rfl) rfl) 

noncomputable def Ns204p1159 := nat_lit 1695315040548799169691648 

noncomputable def Ns204p1160 := nat_lit 1420032711322305513562512087602904709618363648705133298978363542317129129516042486094785 

noncomputable def Ns204p1161 := nat_lit 704955687610872565255254336748118540842396593755240389471857687246053587015266059818106880 

noncomputable def Ns204p1162 := nat_lit 113491912806097026757103756712056638209144655988853800632494155110117702740133878721 

noncomputable def Ns204p1163 := nat_lit 3718949542747209330810877299544359481110042369546605257837547144103255148642341532539841 

noncomputable def Ns204p1164 := nat_lit 12924187606199330363012996173715506582110604218846073806984057599510982428613211096665292800 

noncomputable def Ns204p1165 := BSN.sin_dyadic_bound_f 24091875737 34359738368 3 2 16777216 5125001 Ns204p1160 Ns204p1161 Ns204p1162 Ns204p1163 Ns204p1164 Ns204p1162 10823132 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 24091875737) qz357 0 2 Ns204p1160 Ns204p1161 Ns204p1162 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 24091875737) qz358 0 2 Ns204p1163 Ns204p1164 Ns204p1162 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1166 := @Ns204p1153 2560000 (Ns204p1158 rfl) (Enclosure.sfrac_false_div 90824379 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 90824379) qz369) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns204p1159) qz371) 226375608064910080 72057594037927936 Bool.false 10823132 16777216 0 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q3 90824379 16777216 226375608064910080 72057594037927936 0 Ns204p1159 Ns204p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 10823132 16777216 Ns204p1159 Ns204p89 24091875737 34359738368 5125001 5120000 (Ns204p1165 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p1167 := @Enclosure.Real.IsNear.inv_image (Real.cos qz147) 2705783 4194304 14887 1310720000 13003168 13003627 8388608 (Ns204p1152 (Ns204p1166 rfl rfl) rfl) rfl 

noncomputable def Ns204p1168 := @Enclosure.Real.IsNear.recentre' qz148 Bool.false 3488033 8388608 

noncomputable abbrev qz149 := (@HMul.hMul Real Real Real qz342 qz340 qz490)

noncomputable def Ns204p1169 := @Enclosure.Real.IsNear.cos_image qz149 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 9579517)) qz359) Bool.true 9579517 8388608 

noncomputable def Ns204p1170 := nat_lit 45237991165106499058270353445 

noncomputable def Ns204p1171 := nat_lit 35754896939345774017383921298230557 

noncomputable def Ns204p1172 := @Enclosure.Real.IsNear.recentre' qz149 Bool.true Ns204p1170 Ns204p533 Ns204p1171 

noncomputable abbrev qz150 := qz490

noncomputable def Ns204p1173 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz150 884279719003555 140737488355328 1 500000000000000 51158010517399 

noncomputable abbrev qz491 := (@HSub.hSub Real Real Real qz634 qz718 qz712)

noncomputable abbrev qz151 := qz491

noncomputable def Ns204p1174 := @Enclosure.Real.IsNear.subLit_tf qz151 qz27 33565824472983 281474976710656 1324938747 281474976710656 1 16 

noncomputable abbrev qz492 := qz718

noncomputable abbrev qz152 := qz492

noncomputable def Ns204p1175 := @Enclosure.Real.IsNear.subLit_ff_n qz152 qz142 208951332612201 281474976710656 838399483 281474976710656 14455149 16777216 29 16777216 

noncomputable def Ns204p1176 := @Enclosure.Real.IsNear.mulLit_ff qz142 qz142 14455149 16777216 29 16777216 14455149 16777216 29 16777216 208951332612201 281474976710656 

noncomputable def Ns204p1177 := nat_lit 70126593495930313187693190701654397029272212224420967676321 

noncomputable def Ns204p1178 := nat_lit 988643523323402220304136834155207460536120982503085435781120 

noncomputable def Ns204p1179 := nat_lit 70916762308647988044423664284577726617420604876742785441 

noncomputable def Ns204p1180 := nat_lit 210237946963173643586990724776394035634581795463509417458081 

noncomputable def Ns204p1181 := nat_lit 44488958549553099913686157536984335724125444212638844610150400 

noncomputable def Ns204p1182 := BSN.cos_dyadic_bound_f 9579517 8388608 3 2 8388608 2560000 Ns204p1177 Ns204p1178 Ns204p1179 Ns204p1180 Ns204p1181 Ns204p1179 3488033 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 9579517) (BSN.cosEvenQ 8388608) 0 2 Ns204p1177 Ns204p1178 Ns204p1179 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 9579517) (BSN.cosOddQ 8388608) 0 2 Ns204p1180 Ns204p1181 Ns204p1179 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1183 := @Ns204p1168 1289097216 42949672960000 3488033 8388608 314721 10485760000 (@Ns204p1169 497 16777216 Bool.false 3488033 8388608 1 2560000 (@Ns204p1172 Ns204p536 9579517 8388608 497 16777216 (@Ns204p1173 281474976710656 1324938747 281474976710656 Ns204p1170 Ns204p533 Ns204p1171 Ns204p536 RS205to222.d39 (@Ns204p1174 0 1 818528168278384 51158010517399 281474976710656 1324938747 281474976710656 (@Ns204p1175 563141087401321955328 33565824472983 281474976710656 1324938747 281474976710656 (@Ns204p1176 838399483 281474976710656 (Ns204p1157 rfl rfl) (Ns204p1157 rfl rfl) rfl) (Ns204p1157 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 9579517 8388608) (BSN.cos_neg_of_bound 9579517 8388608 Bool.false 3488033 8388608 1 2560000 (Ns204p1182 rfl rfl)) rfl rfl) 

noncomputable def Ns204p1184 := @Ns204p1143 5752239264953372819 295147905179352825856000 (Ns204p1144 qz29 (@Enclosure.Real.IsNear.of_eq qz716 (@Inv.inv Real Real.instInv (Real.sqrt qz146)) Bool.false 5635909 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz141 (BSN.t_div_two_pi_nonneg qz140 493405 1000 qz143)) Ns204p1148) rfl) (@Ns204p1149 140737488355328 2546571979971 43980465111040000 (BSN.correction_mk qz142 (BSN.cos_two_pi_p_ne_zero_mk qz140 493405 1000 8 qz143 rfl rfl (@BSN.floor_sqrt_eq_dec qz140 493405 1000 8 qz143 rfl rfl rfl))) (@Ns204p1150 16777216 3488033 8388608 314721 10485760000 90712559184235 140737488355328 2546571979971 43980465111040000 (@Ns204p1151 16777216 (Ns204p1167 rfl rfl rfl rfl rfl) rfl) (Ns204p1183 rfl) rfl)) 

noncomputable def Ns204p1185 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz140) (hardyZApproximantRS₀ qz140) Bool.false 372299197319286849833 2361183241434822606848 428914682377335836819 295147905179352825856000 (@Eq.refl Real (hardyZApproximantRS₀ qz140)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz140) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz140) qz140 8) (@HMul.hMul Real Real Real qz5 qz713 (Zeta.RiemannSiegel.correction qz142))) Bool.false 372299197319286849833 2361183241434822606848 428914682377335836819 295147905179352825856000 (BSN.hardyZApproximantRS₀_eq qz140 8 (@BSN.floor_sqrt_eq_dec qz140 493405 1000 8 qz143 rfl rfl rfl)) (@Ns204p1077 372299197319286849833 2361183241434822606848 428914682377335836819 295147905179352825856000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz140) qz140 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz140) qz140 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz140) qz140 8)) Bool.false 12555957 33554432 12027 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz140) qz140 8) (Ns204p1142 (Ns204p1141 rfl rfl rfl rfl) rfl rfl)) (Ns204p1184 rfl) rfl rfl)) 

theorem RS205to222.d52 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz140) Bool.false 372299197319286849833 2361183241434822606848 428914682377335836819 295147905179352825856000 := Ns204p1185 

noncomputable def Ns204p1186 := nat_lit 10161413177557406569201664000 

noncomputable abbrev qz886 := (Enclosure.sfrac Bool.false 494845 1000)

noncomputable abbrev qz719 := qz886

noncomputable abbrev qz493 := qz719

noncomputable abbrev qz153 := qz493

noncomputable abbrev qz887 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 494845 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz720 := qz887

noncomputable abbrev qz494 := qz720

noncomputable abbrev qz154 := qz494

noncomputable abbrev qz888 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 494845 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz721 := qz888

noncomputable abbrev qz495 := qz721

noncomputable abbrev qz155 := qz495

noncomputable abbrev qz722 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz154 qz9))

noncomputable def Ns204p1187 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz153) qz153 8) (@HMul.hMul Real Real Real qz5 qz722 (Zeta.RiemannSiegel.correction qz155)) 26928461 33554432 96499 67108864 65968463531240999487 295147905179352825856 667813161322093087 36893488147419103232000 Ns204p1186 

noncomputable def Ns204p1188 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz153) qz153 Real.sin BSN.quadSignNeg 7 8 494845 1000 125 134217728 67108864 2251799813685248 Bool.false 111739266330 1815 279097919 53 47453128 8 

noncomputable def Ns204p1189 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz153) qz153 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 494845 1000 34 83 134217728 67108864 2251799813685248 Bool.false 111739266330 1815 

noncomputable def Ns204p1190 := Ns204p1189 240485871 53 54794152 8 261175631 53 50729528 8 Bool.true 7603266 64507 Bool.true 95788224 Bool.true 3405519 7074237752028440 1 Bool.false 101463150 Bool.true Bool.false 3405153 Bool.false Bool.true 47738393 

noncomputable def Ns204p1191 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz153) qz153 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 494845 1000 93 22 134217728 67108864 2251799813685248 Bool.false 111739266330 1815 

noncomputable def Ns204p1192 := Ns204p1191 186065264 53 67108856 8 216015088 53 60023992 8 Bool.false 22524121 37925 Bool.false 58730351 Bool.false 207048397 7074237752028440 1 Bool.false 56874008 Bool.true Bool.false 3779817 Bool.true Bool.true 7603266 

noncomputable def Ns204p1193 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz153) qz153 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 494845 1000 311 183 134217728 67108864 2251799813685248 Bool.false 111739266330 1815 

noncomputable def Ns204p1194 := Ns204p1193 93032624 53 94906264 8 147453232 53 77490640 16 Bool.true 134217712 1877 Bool.false 134807411 Bool.false 191117054 7074237752028440 1 Bool.false 113257839 Bool.false Bool.false 132772867 Bool.false Bool.false 22524121 

noncomputable def Ns204p1195 := nat_lit 5073581276430286158416487466920860293716303007307653 

noncomputable def Ns204p1196 := nat_lit 6094227876254292042507470347071917600024234557440 

noncomputable def Ns204p1197 := nat_lit 14242567710475750310340773500000000 

noncomputable def Ns204p1198 := nat_lit 42287200659562402000526059785645000000 

noncomputable abbrev qz889 := (@Eq.refl Real (Enclosure.sfrac Bool.false 494845 1000))

noncomputable abbrev qz723 := qz889

noncomputable abbrev qz496 := qz723

noncomputable abbrev qz156 := qz496

noncomputable def Ns204p1199 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz153 494845 1000 979487296100 16000000 989690 4000 2000 Ns204p1197 Ns204p1198 qz156 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns204p1200 := nat_lit 25367906382151430792082437334604301468581515036538265000000 

noncomputable abbrev qz497 := (Enclosure.sfrac Bool.false 494845 2000)

noncomputable abbrev qz724 := (Real.log (Enclosure.sfrac Bool.false 979487296100 16000000))

noncomputable abbrev qz157 := (@HSub.hSub Real Real Real qz345 (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 494845 4000) qz724) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 989690)))))) qz497)

noncomputable abbrev qz498 := (@HSub.hSub Real Real Real qz12 qz157 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 494845 2000) (Real.log Real.pi)))

noncomputable def Ns204p1201 := @Enclosure.Real.IsNear.addLit_ft_p qz498 (Enclosure.sfrac Bool.true Ns204p1197 Ns204p1198) 599895860906711657757 720575940379279360 1106903989917249 81920000000000000000 Ns204p1197 Ns204p1198 0 1 Ns204p1200 

noncomputable def Ns204p1202 := nat_lit 40258329743751429327629058048000 

noncomputable abbrev qz499 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 494845 2000) (Real.log Real.pi))

noncomputable def Ns204p1203 := @Enclosure.Real.IsNear.subLit_ff_p qz157 qz499 4019929873708943270289 3602879701896396800 61382464847 10000000000000000 3801474605409 13421772800 98969 13421772800 Ns204p1202 599895860906711657757 720575940379279360 

noncomputable def Ns204p1204 := nat_lit 8039859747417886540578000 

noncomputable abbrev qz158 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 494845 4000) qz724) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 989690))))))

noncomputable def Ns204p1205 := @Enclosure.Real.IsNear.subLit_ff_p qz158 qz497 4911363376751404507537 3602879701896396800 61382464847 10000000000000000 494845 2000 0 1 Ns204p1204 4019929873708943270289 3602879701896396800 61382464847 10000000000000000 

noncomputable def Ns204p1206 := nat_lit 11059407136709363148751320126561714176 

noncomputable def Ns204p1207 := nat_lit 26650034224698297707134976 

noncomputable def Ns204p1208 := nat_lit 612943365972128381503547933764842389309113906821913663100741261156822869791723134273680365414581548713719806886422067578567789440914931637987278830250000000000000000000000000000 

noncomputable def Ns204p1209 := nat_lit 19823131130369863606706634883577724429289674946411798036623338181966490742339924663478209836629600797270144214296488815828323782209332668326391848150000000000000000000000000000 

noncomputable def Ns204p1210 := nat_lit 2216103253659368779484777438454558367807793220213116779334066268487751995468669060170922448582382580643399906585743221078884518910189701255350000000000000000000000000000 

noncomputable def Ns204p1211 := BSN.log_dyadic_bound 455199296100 1503775296100 8 7 Ns204p1208 67108864 20480000 Ns204p1209 Ns204p1210 41942242 1958974592200 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 455199296100) (BSN.artanhQ 1503775296100) 0 7 Ns204p1209 Ns204p1208 Ns204p1210 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns204p1212 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 494845 4000) qz724 494845 4000 0 1 49639556975473273 4503599627370496 2441407 50000000000000 4912777314305614355537 3602879701896396800 241623609383 40000000000000000 (Enclosure.Real.IsNear.const Bool.false 494845 4000) (BSN.isNear_log_sfrac 979487296100 16000000 49639556975473273 4503599627370496 2441407 50000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 979487296100) qz352)) Bool.false Ns204p1207 Ns204p89 1000000307200000 20480000000000000000000 49639556975473273 4503599627370496 2441407 50000000000000 (BSN.log_rat_reduce_isNear 979487296100 16000000 15 1958974592200 1048576000000 41942242 67108864 24973259072661432 36028797018963968 20480000 1000000000000000 rfl rfl rfl rfl (Ns204p1211 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns204p1213 := BSN.arctan_dyadic_bound_f 1000 989690 1 0 8388608 2560000 0 1 1 0 1 1 8475 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 989690) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 989690) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz500 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 989690)))

noncomputable def Ns204p1214 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz500 884279719003555 562949953421312 1 2000000000000000 8475 8388608 1 2560000 7413104924215727882240 883710971381155 562949953421312 781250001 2000000000000000 qz17 (Ns204p1213 rfl) rfl rfl 

noncomputable def Ns204p1215 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 494845 4000) qz724) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz500)) 4912777314305614355537 3602879701896396800 241623609383 40000000000000000 883710971381155 2251799813685248 781250001 8000000000000000 Ns204p1206 4911363376751404507537 3602879701896396800 61382464847 10000000000000000 (Ns204p1212 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz500) 1 4 0 1 883710971381155 562949953421312 781250001 2000000000000000 883710971381155 2251799813685248 781250001 8000000000000000 qz355 Ns204p1214 rfl) 

noncomputable def Ns204p1216 := @Ns204p1201 Ns204p1195 Ns204p1196 1106903989917249 81920000000000000000 (@Ns204p1203 1106903989917249 81920000000000000000 (Ns204p1205 (Ns204p1215 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 494845 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz497 (Real.log Real.pi) 494845 2000 0 1 38410761 33554432 1 33554432 3801474605409 13421772800 98969 13421772800 (Enclosure.Real.IsNear.const Bool.false 494845 2000) RS205to222.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns204p1197 Ns204p1198) 

noncomputable def Ns204p1217 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz153) Bool.false Ns204p1195 Ns204p1196 1106903989917249 81920000000000000000 13967408291 16777216 57 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz153) (@HAdd.hAdd Real Real Real qz356 qz498 (Enclosure.sfrac Bool.true Ns204p1197 Ns204p1198)) Bool.false Ns204p1195 Ns204p1196 1106903989917249 81920000000000000000 Ns204p1199 (Ns204p1216 rfl rfl)) 

noncomputable def Ns204p1218 := BSN.cos_dyadic_bound_f 12246381 34359738368 1 0 16777216 5125001 0 1 1 0 1 1 16777214 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 12246381) qz642 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 12246381) qz643 0 0 rfl) rfl rfl 

noncomputable def Ns204p1219 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz153) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13967408291) qz369) Bool.false 13967408291 16777216 57 4194304 Bool.true 16777214 16777216 1 2560000 (Ns204p1217 rfl) (Enclosure.sfrac_false_div 13967408291 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13967408291) qz369) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 861762474274143076352) qz371) 226375608064910080 72057594037927936 Bool.false 16777214 16777216 132 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q2 13967408291 16777216 226375608064910080 72057594037927936 132 861762474274143076352 Ns204p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777214 16777216 861762474274143076352 Ns204p89 12246381 34359738368 5125001 5120000 (Ns204p1218 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p1220 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz153) Bool.false Ns204p1195 Ns204p1196 1106903989917249 81920000000000000000 111739266330 134217728 1815 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz153) (@HAdd.hAdd Real Real Real qz356 qz498 (Enclosure.sfrac Bool.true Ns204p1197 Ns204p1198)) Bool.false Ns204p1195 Ns204p1196 1106903989917249 81920000000000000000 Ns204p1199 (Ns204p1216 rfl rfl)) 

noncomputable def Ns204p1221 := Ns204p1194 37925 BSN.abs_quadSignPos (BSN.cos_quad_nat3 311 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 113257839 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 183 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 132772867 134217728) qz156 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz153) qz153 1) Bool.true 8388607 8388608 36649 2621440000 134217712 134217728 1877 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz153) qz153 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz153)) Bool.true 8388607 8388608 36649 2621440000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz153) qz153) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz153)) Bool.true 16777214 16777216 150114304 10737418240000 8388607 8388608 36649 2621440000 (Ns204p1219 rfl rfl) rfl)) rfl) (Ns204p1220 rfl) RS205to222.d7 

noncomputable def Ns204p1222 := nat_lit 324207100925793645692779510832838360916724321169333034353115435082785 

noncomputable def Ns204p1223 := nat_lit 109071213393376150688247470226117428202412966464094242466175362081 

noncomputable def Ns204p1224 := nat_lit 848937244269679796379974889610401040850521696354930365960833284154401 

noncomputable def Ns204p1225 := BSN.sin_dyadic_bound_f 134807411 134217728 3 2 134217728 67108864 Ns204p1222 Ns204p106 Ns204p1223 Ns204p1224 Ns204p109 Ns204p1223 113257839 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 134807411) qz361 0 2 Ns204p1222 Ns204p106 Ns204p1223 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 134807411) qz362 0 2 Ns204p1224 Ns204p109 Ns204p1223 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1226 := nat_lit 7300726225209431307259786158462002663120826520396585942361573804347285509271817058659106906424741220847616 

noncomputable def Ns204p1227 := nat_lit 2374615551078978888294980482968559640962666143898185897414052518954823321882696828857152670290415616 

noncomputable def Ns204p1228 := nat_lit 36472985167318381355187655838418208015684152527509075926795406432986644301526538349120908290280305333374976 

noncomputable def Ns204p1229 := BSN.sin_dyadic_bound_f 191117054 134217728 4 3 134217728 67108864 Ns204p1226 Ns204p256 Ns204p1227 Ns204p1228 Ns204p259 Ns204p1227 132772867 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 191117054) qz361 0 3 Ns204p1226 Ns204p256 Ns204p1227 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 191117054) qz362 0 3 Ns204p1228 Ns204p259 Ns204p1227 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1230 := nat_lit 11897354043548257297747579406401 

noncomputable def Ns204p1231 := BSN.sin_dyadic_bound_f 58730351 134217728 2 1 134217728 67108864 Ns204p1230 Ns204p129 Ns204p1230 Ns204p1230 Ns204p130 Ns204p1230 56874008 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 58730351) qz361 0 1 Ns204p1230 Ns204p129 Ns204p1230 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 58730351) qz362 0 1 Ns204p1230 Ns204p130 Ns204p1230 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1232 := nat_lit 3875738333257039479157076381849777057004594596039962191339737697993712468205894087908326399737067060934321 

noncomputable def Ns204p1233 := nat_lit 6206724515700228384273550543561255557664226791704672138478585299393375103010098735310335663804593841 

noncomputable def Ns204p1234 := nat_lit 23460120019831549624383601980939594480897379211699097243924116118893130986897991861549966209920399177758385 

noncomputable def Ns204p1235 := BSN.cos_dyadic_bound_f 207048397 134217728 4 3 134217728 67108864 Ns204p1232 Ns204p230 Ns204p1233 Ns204p1234 Ns204p233 Ns204p1233 3779817 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 207048397) qz363 0 3 Ns204p1232 Ns204p230 Ns204p1233 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 207048397) qz364 0 3 Ns204p1234 Ns204p233 Ns204p1233 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1236 := Ns204p1192 64507 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 93 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 56874008 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 22 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 3779817 134217728) qz156 rfl rfl (Ns204p1221 RS205to222.d9 RS205to222.d11 RS205to222.d13 RS205to222.d17 (Ns204p1225 rfl rfl) (Ns204p1229 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns204p1220 rfl) RS205to222.d19 RS205to222.d21 RS205to222.d23 RS205to222.d25 RS205to222.d17 (Ns204p1231 rfl rfl) (Ns204p1235 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns204p1237 := nat_lit 45905461296510176998641636698140425471130258217736620939318610886656 

noncomputable def Ns204p1238 := nat_lit 7087563598967722401648211821913986932858048966235346194269208576 

noncomputable def Ns204p1239 := nat_lit 137702208762332595551121613670777448439525058555277392125567294242816 

noncomputable def Ns204p1240 := BSN.cos_dyadic_bound_f 95788224 134217728 3 2 134217728 67108864 Ns204p1237 Ns204p240 Ns204p1238 Ns204p1239 Ns204p243 Ns204p1238 101463150 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 95788224) qz363 0 2 Ns204p1237 Ns204p240 Ns204p1238 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 95788224) qz364 0 2 Ns204p1239 Ns204p243 Ns204p1238 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1241 := BSN.sin_dyadic_bound_f 3405519 134217728 1 0 134217728 67108864 0 1 1 0 1 1 3405153 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 3405519) qz361 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 3405519) qz362 0 0 rfl) rfl rfl 

noncomputable def Ns204p1242 := Ns204p1190 86574 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 34 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 101463150 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 83 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 3405153 134217728) qz156 rfl rfl (Ns204p1236 rfl rfl) (Ns204p1220 rfl) RS205to222.d27 RS205to222.d29 RS205to222.d31 RS205to222.d33 RS205to222.d17 (Ns204p1240 rfl rfl) (Ns204p1241 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns204p1243 := nat_lit 90700855989198255229637610000 

noncomputable def Ns204p1244 := BSN.sin_dyadic_bound_f 17354130 134217728 2 1 134217728 67108864 Ns204p1243 Ns204p129 Ns204p1243 Ns204p1243 Ns204p130 Ns204p1243 17305815 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 17354130) qz361 0 1 Ns204p1243 Ns204p129 Ns204p1243 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 17354130) qz362 0 1 Ns204p1243 Ns204p130 Ns204p1243 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1245 := Ns204p1188 Bool.true 47738393 86574 Bool.true 17354130 7074237752028440 1 Bool.false 17305815 Bool.true Bool.true 53856922 96499 BSN.abs_quadSignNeg qz387 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 17305815 134217728) qz156 rfl (Ns204p1242 rfl) (Ns204p1220 rfl) RS205to222.d35 RS205to222.d37 RS205to222.d17 (Ns204p1244 rfl rfl) rfl 

noncomputable def Ns204p1246 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz153) qz153 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz153) qz153 8) 53856922 134217728 96499 134217728 53856922 134217728 96499 134217728 14457107415826432 26928461 33554432 96499 67108864 (Ns204p1245 rfl rfl rfl rfl) 

noncomputable def Ns204p1247 := @Enclosure.Real.IsNear.mulLit_ff qz722 (Zeta.RiemannSiegel.correction qz155) 1407951 4194304 1 8388608 46854232520337 70368744177664 472235564783 8796093022208000 65968463531240999487 295147905179352825856 

noncomputable abbrev qz725 := (@HPow.hPow Real Real Real qz7 qz154 qz9)

noncomputable def Ns204p1248 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz725 1 1 0 1 1407951 4194304 1 8388608 1407951 4194304 1 8388608 

noncomputable def Ns204p1249 := @Enclosure.Real.IsNear.sqrt_image qz154 264264747513 3355443200 98969 3355443200 74444820 74444849 8388608 (@Enclosure.Real.IsNear.of_eq qz154 (@HMul.hMul Real Real Real qz5 qz153 qz3) Bool.false 264264747513 3355443200 98969 3355443200 (BSN.t_div_two_pi_mk qz153 494845 1000 qz156) (@Enclosure.Real.IsNear.mulLit_ff qz153 qz3 494845 1000 0 1 2670177 16777216 1 16777216 264264747513 3355443200 98969 3355443200 (Enclosure.Real.IsNear.const Bool.false 494845 1000) RS205to222.d40 rfl)) 

noncomputable abbrev qz890 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 494845 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz726 := qz890

noncomputable abbrev qz501 := qz726

noncomputable abbrev qz159 := qz501

noncomputable def Ns204p1250 := @Enclosure.Real.IsNear.sqrt_image qz159 148889669 16777216 29 16777216 24989766 24989772 8388608 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 148889669 16777216 29 16777216 148889669 16777216 29 16777216 (Ns204p1249 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns204p1251 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz159) 24989769 8388608 3 8388608 2815901 2815903 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz159) Bool.false 49979538 16777216 6 16777216 24989769 8388608 3 8388608 (Ns204p1250 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns204p1252 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz159)) Bool.false 5631804 16777216 2 16777216 1407951 4194304 1 8388608 (Ns204p1251 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz342 qz340 qz495)

noncomputable abbrev qz727 := (@HMul.hMul Real Real Real qz844 qz888 qz888)

noncomputable abbrev qz502 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz727 qz721) qz640)

noncomputable abbrev qz161 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz502))

noncomputable def Ns204p1253 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz155) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz160)) qz161) Bool.false 46854232520337 

noncomputable def Ns204p1254 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz160)) qz161 11899539 8388608 191 

noncomputable def Ns204p1255 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz160)) Bool.false 23799078 16777216 382 16777216 11899539 8388608 191 

noncomputable def Ns204p1256 := @Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.false 11827138 16777216 485257216 42949672960000 5913569 8388608 118471 10485760000 

noncomputable def Ns204p1257 := @Enclosure.Real.IsNear.cos_image qz160 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23046631) qz385) Bool.false 23046631 4194304 183 16777216 Bool.false 11827138 16777216 1 

noncomputable def Ns204p1258 := nat_lit 156519237397661666345516623 

noncomputable def Ns204p1259 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz155 884279719003555 140737488355328 1 500000000000000 14671941 16777216 29 16777216 12974099864716737750255 2361183241434822606848 Ns204p1258 

noncomputable def Ns204p1260 := @Enclosure.Real.IsNear.subLit_ff_p qz159 qz1 148889669 16777216 29 16777216 8 1 0 1 14671941 14671941 16777216 29 

noncomputable def Ns204p1261 := @Ns204p1260 16777216 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 148889669 16777216 29 16777216 148889669 16777216 29 16777216 (Ns204p1249 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns204p1262 := @Enclosure.Real.IsNear.recentre' qz160 Bool.false 12974099864716737750255 2361183241434822606848 Ns204p1258 Ns204p843 23046631 4194304 183 16777216 (@Ns204p1259 Ns204p843 RS205to222.d39 (Ns204p1261 rfl rfl) rfl) 

noncomputable def Ns204p1263 := nat_lit 2201162592859985725876323406669381893718204344055490185130461391972691176006457781869505 

noncomputable def Ns204p1264 := nat_lit 272668070578374691016352839735870298761623530116638670937565351465190480304336231361 

noncomputable def Ns204p1265 := nat_lit 5764508185376169056366820541441189741159206843953714022255404730311818962096420503378881 

noncomputable def Ns204p1266 := BSN.sin_dyadic_bound_f 26881548697 34359738368 3 2 16777216 5125001 Ns204p1263 Ns204p1161 Ns204p1264 Ns204p1265 Ns204p1164 Ns204p1264 11827138 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26881548697) qz357 0 2 Ns204p1263 Ns204p1161 Ns204p1264 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26881548697) qz358 0 2 Ns204p1265 Ns204p1164 Ns204p1264 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1267 := @Ns204p1257 2560000 (Ns204p1262 rfl) (Enclosure.sfrac_false_div 23046631 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23046631) qz385) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 472905205852596466614272) qz386) 226375608064910080 72057594037927936 Bool.false 11827138 16777216 0 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q3 23046631 4194304 226375608064910080 72057594037927936 0 472905205852596466614272 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 11827138 16777216 472905205852596466614272 604462909807314587353088 26881548697 34359738368 5125001 5120000 (Ns204p1266 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p1268 := @Enclosure.Real.IsNear.inv_image (Real.cos qz160) 5913569 8388608 118471 10485760000 11899348 11899730 8388608 (Ns204p1256 (Ns204p1267 rfl rfl) rfl) rfl 

noncomputable def Ns204p1269 := @Enclosure.Real.IsNear.recentre' qz161 Bool.false 3937483 8388608 

noncomputable abbrev qz162 := (@HMul.hMul Real Real Real qz342 qz340 qz502)

noncomputable def Ns204p1270 := @Enclosure.Real.IsNear.cos_image qz162 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 9078173)) qz359) Bool.true 9078173 8388608 

noncomputable def Ns204p1271 := nat_lit 42870461424705972287659994005 

noncomputable def Ns204p1272 := nat_lit 36094218124407269371373322896751533 

noncomputable def Ns204p1273 := @Enclosure.Real.IsNear.recentre' qz162 Bool.true Ns204p1271 Ns204p533 Ns204p1272 

noncomputable abbrev qz163 := qz502

noncomputable def Ns204p1274 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz163 884279719003555 140737488355328 1 500000000000000 48480656633191 

noncomputable abbrev qz503 := (@HSub.hSub Real Real Real qz634 qz727 qz721)

noncomputable abbrev qz164 := qz503

noncomputable def Ns204p1275 := @Enclosure.Real.IsNear.subLit_tf qz164 qz27 30888470588775 281474976710656 1337512683 281474976710656 1 16 

noncomputable abbrev qz504 := qz727

noncomputable abbrev qz165 := qz504

noncomputable def Ns204p1276 := @Enclosure.Real.IsNear.subLit_ff_n qz165 qz155 215265852707481 281474976710656 850973419 281474976710656 14671941 16777216 29 16777216 

noncomputable def Ns204p1277 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz155 14671941 16777216 29 16777216 14671941 16777216 29 16777216 215265852707481 281474976710656 

noncomputable def Ns204p1278 := nat_lit 56547984839281946852936284362543562193930238784238236736161 

noncomputable def Ns204p1279 := nat_lit 46130444315954340136337752391978498964420400994059819681 

noncomputable def Ns204p1280 := nat_lit 169551693629213931878536177582846729583861875550726590569121 

noncomputable def Ns204p1281 := BSN.cos_dyadic_bound_f 9078173 8388608 3 2 8388608 2560000 Ns204p1278 Ns204p1178 Ns204p1279 Ns204p1280 Ns204p1181 Ns204p1279 3937483 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 9078173) (BSN.cosEvenQ 8388608) 0 2 Ns204p1278 Ns204p1178 Ns204p1279 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 9078173) (BSN.cosOddQ 8388608) 0 2 Ns204p1280 Ns204p1181 Ns204p1279 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1282 := @Ns204p1269 650948608 21474836480000 3937483 8388608 158923 5242880000 (@Ns204p1270 251 8388608 Bool.false 3937483 8388608 1 2560000 (@Ns204p1273 Ns204p536 9078173 8388608 251 8388608 (@Ns204p1274 281474976710656 1337512683 281474976710656 Ns204p1271 Ns204p533 Ns204p1272 Ns204p536 RS205to222.d39 (@Ns204p1275 0 1 775690506131056 48480656633191 281474976710656 1337512683 281474976710656 (@Ns204p1276 518222542977525350400 30888470588775 281474976710656 1337512683 281474976710656 (@Ns204p1277 850973419 281474976710656 (Ns204p1261 rfl rfl) (Ns204p1261 rfl rfl) rfl) (Ns204p1261 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 9078173 8388608) (BSN.cos_neg_of_bound 9078173 8388608 Bool.false 3937483 8388608 1 2560000 (Ns204p1281 rfl rfl)) rfl rfl) 

noncomputable def Ns204p1283 := @Ns204p1247 667813161322093087 36893488147419103232000 (Ns204p1248 qz29 (@Enclosure.Real.IsNear.of_eq qz725 (@Inv.inv Real Real.instInv (Real.sqrt qz159)) Bool.false 1407951 4194304 1 8388608 (BSN.rpow_neg_quarter_mk qz154 (BSN.t_div_two_pi_nonneg qz153 494845 1000 qz156)) Ns204p1252) rfl) (@Ns204p1253 70368744177664 472235564783 8796093022208000 (BSN.correction_mk qz155 (BSN.cos_two_pi_p_ne_zero_mk qz153 494845 1000 8 qz156 rfl rfl (@BSN.floor_sqrt_eq_dec qz153 494845 1000 8 qz156 rfl rfl rfl))) (@Ns204p1254 8388608 3937483 8388608 158923 5242880000 46854232520337 70368744177664 472235564783 8796093022208000 (@Ns204p1255 8388608 (Ns204p1268 rfl rfl rfl rfl rfl) rfl) (Ns204p1282 rfl) rfl)) 

noncomputable def Ns204p1284 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz153) (hardyZApproximantRS₀ qz153) Bool.true 302833711432141261375 295147905179352825856 53718699445700205087 36893488147419103232000 (@Eq.refl Real (hardyZApproximantRS₀ qz153)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz153) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz153) qz153 8) (@HMul.hMul Real Real Real qz5 qz722 (Zeta.RiemannSiegel.correction qz155))) Bool.true 302833711432141261375 295147905179352825856 53718699445700205087 36893488147419103232000 (BSN.hardyZApproximantRS₀_eq qz153 8 (@BSN.floor_sqrt_eq_dec qz153 494845 1000 8 qz156 rfl rfl rfl)) (@Ns204p1187 302833711432141261375 295147905179352825856 53718699445700205087 36893488147419103232000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz153) qz153 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz153) qz153 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz153) qz153 8)) Bool.true 26928461 33554432 96499 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz153) qz153 8) (Ns204p1246 (Ns204p1245 rfl rfl rfl rfl) rfl rfl)) (Ns204p1283 rfl) rfl rfl)) 

theorem RS205to222.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz153) Bool.true 302833711432141261375 295147905179352825856 53718699445700205087 36893488147419103232000 := Ns204p1284 

noncomputable def Ns204p1285 := nat_lit 10950314693020856567952572416 

noncomputable abbrev qz891 := (Enclosure.sfrac Bool.false 496283 1000)

noncomputable abbrev qz728 := qz891

noncomputable abbrev qz505 := qz728

noncomputable abbrev qz166 := qz505

noncomputable abbrev qz892 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 496283 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz729 := qz892

noncomputable abbrev qz506 := qz729

noncomputable abbrev qz167 := qz506

noncomputable abbrev qz893 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 496283 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz730 := qz893

noncomputable abbrev qz507 := qz730

noncomputable abbrev qz168 := qz507

noncomputable abbrev qz731 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz167 qz9))

noncomputable def Ns204p1286 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz166) qz166 8) (@HMul.hMul Real Real Real qz5 qz731 (Zeta.RiemannSiegel.correction qz168)) 52589881 67108864 96773 67108864 68120338287362340105 295147905179352825856 3137042429159182967 184467440737095516160000 Ns204p1285 

noncomputable def Ns204p1287 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz166) qz166 Real.cos BSN.quadSignPos 7 8 496283 1000 124 134217728 67108864 2251799813685248 Bool.false 112160771881 1820 279097919 53 47453128 8 

noncomputable def Ns204p1288 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz166) qz166 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 496283 1000 34 82 134217728 67108864 2251799813685248 Bool.false 112160771881 1820 

noncomputable def Ns204p1289 := Ns204p1288 240485871 53 54794152 8 261175631 53 50729528 8 Bool.false 121584718 64688 Bool.true 20101355 Bool.true 168299239 7074237752028440 1 Bool.false 132715282 Bool.true Bool.false 41821336 Bool.true Bool.false 51596959 

noncomputable def Ns204p1290 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz166) qz166 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 496283 1000 94 23 134217728 67108864 2251799813685248 Bool.false 112160771881 1820 

noncomputable def Ns204p1291 := Ns204p1290 186065264 53 67108856 8 216015088 53 60023992 8 Bool.false 145715567 38029 Bool.false 1845338 Bool.false 107095538 7074237752028440 1 Bool.false 134205042 Bool.true Bool.false 96087563 Bool.false Bool.false 121584718 

noncomputable def Ns204p1292 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz166) qz166 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 496283 1000 313 184 134217728 67108864 2251799813685248 Bool.false 112160771881 1820 

noncomputable def Ns204p1293 := Ns204p1292 93032624 53 94906264 8 147453232 53 77490640 16 Bool.false 134217680 1877 Bool.false 874620 Bool.false 189756143 7074237752028440 1 Bool.false 874613 Bool.true Bool.false 20986104 Bool.false Bool.false 145715567 

noncomputable def Ns204p1294 := nat_lit 80971295656375700538821792327696443976483278367701972283 

noncomputable def Ns204p1295 := nat_lit 96894691021363806815284568746663532941471149258178560 

noncomputable def Ns204p1296 := nat_lit 14450715415636826298743043988640000 

noncomputable def Ns204p1297 := nat_lit 43029886774343409612379826588341350720 

noncomputable abbrev qz894 := (@Eq.refl Real (Enclosure.sfrac Bool.false 496283 1000))

noncomputable abbrev qz732 := qz894

noncomputable abbrev qz508 := qz732

noncomputable abbrev qz169 := qz508

noncomputable def Ns204p1298 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz166 496283 1000 985188264356 16000000 992566 4000 2000 Ns204p1296 Ns204p1297 qz169 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns204p1299 := nat_lit 25910814610040224172422973544862862072474649077664631130560 

noncomputable abbrev qz733 := (Real.log (Enclosure.sfrac Bool.false 985188264356 16000000))

noncomputable abbrev qz170 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 496283 4000) qz733) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 992566))))))

noncomputable abbrev qz734 := (Enclosure.sfrac Bool.false 496283 2000)

noncomputable abbrev qz509 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz170 qz734) (@HMul.hMul Real Real Real qz5 qz734 (Real.log Real.pi)))

noncomputable def Ns204p1300 := @Enclosure.Real.IsNear.addLit_ft_p qz509 (Enclosure.sfrac Bool.true Ns204p1296 Ns204p1297) 602158800899457993723 720575940379279360 5550486807263763 409600000000000000000 Ns204p1296 Ns204p1297 0 1 Ns204p1299 

noncomputable def Ns204p1301 := nat_lit 1010254826899120104361741516800000 

noncomputable abbrev qz510 := (@HSub.hSub Real Real Real qz12 qz170 qz734)

noncomputable abbrev qz511 := (@HMul.hMul Real Real Real qz5 qz734 (Real.log Real.pi))

noncomputable def Ns204p1302 := @Enclosure.Real.IsNear.subLit_ff_p qz510 qz511 20171049813350938569603 18014398509481984000 615580020103 100000000000000000 19062607701363 67108864000 496283 67108864000 Ns204p1301 602158800899457993723 720575940379279360 

noncomputable def Ns204p1303 := nat_lit 40342099626701877139206000 

noncomputable abbrev qz512 := qz734

noncomputable def Ns204p1304 := @Enclosure.Real.IsNear.subLit_ff_p qz170 qz512 24641169681091562302339 18014398509481984000 615580020103 100000000000000000 496283 2000 0 1 Ns204p1303 20171049813350938569603 18014398509481984000 615580020103 100000000000000000 

noncomputable def Ns204p1305 := nat_lit 55486981296868561869913440547160195072 

noncomputable def Ns204p1306 := nat_lit 26664066180129288508932096 

noncomputable def Ns204p1307 := nat_lit 646289562812056887831585814176179105159518772193609984885930434498271398436657397104466434942139684766998279521938167392538401276911374792326894100492065067487453384146314854400 

noncomputable def Ns204p1308 := nat_lit 21288997915563966229982230848260696971009017411519077409472655724332695407702658012391676232939827129854635555936181092060710254736851251846352848048646183823743904754842992640 

noncomputable def Ns204p1309 := nat_lit 2637942027377848281270550367485814910894356715492790610591203197569320385143283396824012787515966679572494087053152701821866071070846018434585280618223255510292847656960 

noncomputable def Ns204p1310 := BSN.log_dyadic_bound 460900264356 1509476264356 8 7 Ns204p1307 67108864 20480000 Ns204p1308 Ns204p1309 42331707 1970376528712 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 460900264356) (BSN.artanhQ 1509476264356) 0 7 Ns204p1308 Ns204p1307 Ns204p1309 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns204p1311 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 496283 4000) qz733 496283 4000 0 1 49665693529191033 4503599627370496 2441407 50000000000000 24648239381747513430339 18014398509481984000 1211628790181 200000000000000000 (Enclosure.Real.IsNear.const Bool.false 496283 4000) (BSN.isNear_log_sfrac 985188264356 16000000 49665693529191033 4503599627370496 2441407 50000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 985188264356) qz352)) Bool.false Ns204p1306 Ns204p89 1000000307200000 20480000000000000000000 49665693529191033 4503599627370496 2441407 50000000000000 (BSN.log_rat_reduce_isNear 985188264356 16000000 15 1970376528712 1048576000000 42331707 67108864 24973259072661432 36028797018963968 20480000 1000000000000000 rfl rfl rfl rfl (Ns204p1310 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns204p1312 := BSN.arctan_dyadic_bound_f 1000 992566 1 0 8388608 2560000 0 1 1 0 1 1 8451 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 992566) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 992566) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz513 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 992566)))

noncomputable def Ns204p1313 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz513 884279719003555 562949953421312 1 2000000000000000 8451 8388608 1 2560000 7413118435014609993728 883712581993891 562949953421312 781250001 2000000000000000 qz17 (Ns204p1312 rfl) rfl rfl 

noncomputable def Ns204p1314 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 496283 4000) qz733) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz513)) 24648239381747513430339 18014398509481984000 1211628790181 200000000000000000 883712581993891 2251799813685248 781250001 8000000000000000 Ns204p1305 24641169681091562302339 18014398509481984000 615580020103 100000000000000000 (Ns204p1311 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz513) 1 4 0 1 883712581993891 562949953421312 781250001 2000000000000000 883712581993891 2251799813685248 781250001 8000000000000000 qz355 Ns204p1313 rfl) 

noncomputable def Ns204p1315 := @Ns204p1300 Ns204p1294 Ns204p1295 5550486807263763 409600000000000000000 (@Ns204p1302 5550486807263763 409600000000000000000 (Ns204p1304 (Ns204p1314 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 496283 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz512 (Real.log Real.pi) 496283 2000 0 1 38410761 33554432 1 33554432 19062607701363 67108864000 496283 67108864000 (Enclosure.Real.IsNear.const Bool.false 496283 2000) RS205to222.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns204p1296 Ns204p1297) 

noncomputable def Ns204p1316 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz166) Bool.false Ns204p1294 Ns204p1295 5550486807263763 409600000000000000000 14020096485 16777216 57 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz166) (@HAdd.hAdd Real Real Real qz356 qz509 (Enclosure.sfrac Bool.true Ns204p1296 Ns204p1297)) Bool.false Ns204p1294 Ns204p1295 5550486807263763 409600000000000000000 Ns204p1298 (Ns204p1315 rfl rfl)) 

noncomputable def Ns204p1317 := nat_lit 3796078276525116610314240 

noncomputable def Ns204p1318 := nat_lit 855443522981440509402996264941572313905384047878959451860324912366686877252339625264994087206338409547733354303106620638742828369140625 

noncomputable def Ns204p1319 := nat_lit 607385337056827818826783702110301179079070295861801470293231982411622107119140944766030282735588485820699133910238742828369140625 

noncomputable def Ns204p1320 := nat_lit 4271913111457858755283594853440430150724417156476117302577254962343585366803836693277548843450285131240723488718997462238742828369140625 

noncomputable def Ns204p1321 := BSN.sin_dyadic_bound_f 53945516875 34359738368 4 3 16777216 5125001 Ns204p1318 Ns204p217 Ns204p1319 Ns204p1320 Ns204p220 Ns204p1319 16777210 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53945516875) qz357 0 3 Ns204p1318 Ns204p217 Ns204p1319 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53945516875) qz358 0 3 Ns204p1320 Ns204p220 Ns204p1319 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1322 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz166) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 14020096485) qz369) Bool.false 14020096485 16777216 57 4194304 Bool.false 16777210 16777216 1 2560000 (Ns204p1316 rfl) (Enclosure.sfrac_false_div 14020096485 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 14020096485) qz369) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns204p1317) qz371) 226375608064910080 72057594037927936 Bool.false 16777210 16777216 132 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q3 14020096485 16777216 226375608064910080 72057594037927936 132 Ns204p1317 Ns204p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777210 16777216 Ns204p1317 Ns204p89 53945516875 34359738368 5125001 5120000 (Ns204p1321 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p1323 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz166) Bool.false Ns204p1294 Ns204p1295 5550486807263763 409600000000000000000 112160771881 134217728 1820 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz166) (@HAdd.hAdd Real Real Real qz356 qz509 (Enclosure.sfrac Bool.true Ns204p1296 Ns204p1297)) Bool.false Ns204p1294 Ns204p1295 5550486807263763 409600000000000000000 Ns204p1298 (Ns204p1315 rfl rfl)) 

noncomputable def Ns204p1324 := Ns204p1293 38029 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 313 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 874613 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 184 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 20986104 134217728) qz169 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz166) qz166 1) Bool.false 8388605 8388608 36649 2621440000 134217680 134217728 1877 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz166) qz166 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz166)) Bool.false 8388605 8388608 36649 2621440000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz166) qz166) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz166)) Bool.false 16777210 16777216 150114304 10737418240000 8388605 8388608 36649 2621440000 (Ns204p1322 rfl rfl) rfl)) rfl) (Ns204p1323 rfl) RS205to222.d7 

noncomputable def Ns204p1325 := BSN.sin_dyadic_bound_f 874620 134217728 1 0 134217728 67108864 0 1 1 0 1 1 874613 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 874620) qz361 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 874620) qz362 0 0 rfl) rfl rfl 

noncomputable def Ns204p1326 := nat_lit 2731618777978288916393140197437313940998946054766745970839554908568455567239622046753931022857438664908481 

noncomputable def Ns204p1327 := nat_lit 2179466164840501065111955032483138541058169595515981549917689213748939555990651537250004499412868801 

noncomputable def Ns204p1328 := nat_lit 16545598663859502109523463786893585033273945146918152629741896882022967173162639694482868251449183894298305 

noncomputable def Ns204p1329 := BSN.cos_dyadic_bound_f 189756143 134217728 4 3 134217728 67108864 Ns204p1326 Ns204p230 Ns204p1327 Ns204p1328 Ns204p233 Ns204p1327 20986104 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 189756143) qz363 0 3 Ns204p1326 Ns204p230 Ns204p1327 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 189756143) qz364 0 3 Ns204p1328 Ns204p233 Ns204p1327 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1330 := BSN.cos_dyadic_bound_f 1845338 134217728 1 0 134217728 67108864 0 1 1 0 1 1 134205042 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 1845338) qz363 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 1845338) qz364 0 0 rfl) rfl rfl 

noncomputable def Ns204p1331 := nat_lit 129111533370121561651594480812811827126156225502548064867419494990080 

noncomputable def Ns204p1332 := nat_lit 17304976546609786749070268850393161488749628237039064044572426496 

noncomputable def Ns204p1333 := nat_lit 338121236483528626575629907407797005926094043584765916168121750569216 

noncomputable def Ns204p1334 := BSN.sin_dyadic_bound_f 107095538 134217728 3 2 134217728 67108864 Ns204p1331 Ns204p106 Ns204p1332 Ns204p1333 Ns204p109 Ns204p1332 96087563 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 107095538) qz361 0 2 Ns204p1331 Ns204p106 Ns204p1332 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 107095538) qz362 0 2 Ns204p1333 Ns204p109 Ns204p1332 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1335 := Ns204p1291 64688 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 94 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 134205042 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 23 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 96087563 134217728) qz169 rfl rfl (Ns204p1324 RS205to222.d9 RS205to222.d11 RS205to222.d13 RS205to222.d17 (Ns204p1325 rfl rfl) (Ns204p1329 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns204p1323 rfl) RS205to222.d19 RS205to222.d21 RS205to222.d23 RS205to222.d25 RS205to222.d17 (Ns204p1330 rfl rfl) (Ns204p1334 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns204p1336 := nat_lit 163268098208254785106537800625 

noncomputable def Ns204p1337 := BSN.cos_dyadic_bound_f 20101355 134217728 2 1 134217728 67108864 Ns204p1336 Ns204p125 Ns204p1336 Ns204p1336 Ns204p126 Ns204p1336 132715282 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 20101355) qz363 0 1 Ns204p1336 Ns204p125 Ns204p1336 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 20101355) qz364 0 1 Ns204p1336 Ns204p126 Ns204p1336 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1338 := nat_lit 1688776398256804888061097870551262267216345432314882875254659488610396670823692459925394970591051920656801 

noncomputable def Ns204p1339 := nat_lit 516399516215694992500615137416723736163731433989755162381074315217887059061263346305265128631650721 

noncomputable def Ns204p1340 := nat_lit 10235204602619243581621639331277666076405277683017970974552342216534066497797509765257975626428802355120545 

noncomputable def Ns204p1341 := BSN.cos_dyadic_bound_f 168299239 134217728 4 3 134217728 67108864 Ns204p1338 Ns204p230 Ns204p1339 Ns204p1340 Ns204p233 Ns204p1339 41821336 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 168299239) qz363 0 3 Ns204p1338 Ns204p230 Ns204p1339 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 168299239) qz364 0 3 Ns204p1340 Ns204p233 Ns204p1339 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1342 := Ns204p1289 86819 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 34 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132715282 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 82 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 41821336 134217728) qz169 rfl rfl (Ns204p1335 rfl rfl) (Ns204p1323 rfl) RS205to222.d27 RS205to222.d29 RS205to222.d31 RS205to222.d33 RS205to222.d17 (Ns204p1337 rfl rfl) (Ns204p1341 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns204p1343 := nat_lit 3949260473765237886371909463937198328009320860992046795780030763253547386720119495585087252653846178508881 

noncomputable def Ns204p1344 := nat_lit 6565436947244061423575631078691687572834255620049183107899611936530258355438496324938866796480901201 

noncomputable def Ns204p1345 := nat_lit 23904142577566789370317127236403322118184587302522339349463278627943084498041162022345327129533587977089105 

noncomputable def Ns204p1346 := BSN.cos_dyadic_bound_f 208020101 134217728 4 3 134217728 67108864 Ns204p1343 Ns204p230 Ns204p1344 Ns204p1345 Ns204p233 Ns204p1344 2808408 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 208020101) qz363 0 3 Ns204p1343 Ns204p230 Ns204p1344 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 208020101) qz364 0 3 Ns204p1345 Ns204p233 Ns204p1344 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz735 := (BSN.cos_quad_nat0 124 rfl)

noncomputable def Ns204p1347 := Ns204p1287 Bool.false 51596959 86819 Bool.true 208020101 7074237752028440 1 Bool.false 2808408 Bool.false Bool.false 52589881 96773 BSN.abs_quadSignPos qz735 (BSN.sfrac_eq_quadSignPos_mul Bool.false 2808408 134217728) qz169 rfl (Ns204p1342 rfl) (Ns204p1323 rfl) RS205to222.d35 RS205to222.d37 RS205to222.d17 (Ns204p1346 rfl rfl) rfl 

noncomputable def Ns204p1348 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz166) qz166 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz166) qz166 8) 52589881 134217728 96773 134217728 52589881 134217728 96773 134217728 14116988687220736 52589881 67108864 96773 67108864 (Ns204p1347 rfl rfl rfl rfl) 

noncomputable def Ns204p1349 := @Enclosure.Real.IsNear.mulLit_ff qz731 (Zeta.RiemannSiegel.correction qz168) 703465 2097152 1 8388608 96835433585697 140737488355328 4437904918063 87960930222080000 68120338287362340105 295147905179352825856 

noncomputable abbrev qz736 := (@HPow.hPow Real Real Real qz7 qz167 qz9)

noncomputable def Ns204p1350 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz736 1 1 0 1 703465 2097152 1 8388608 703465 2097152 1 8388608 

noncomputable def Ns204p1351 := @Enclosure.Real.IsNear.sqrt_image qz167 1325163452091 16777216000 496283 16777216000 74552909 74552938 8388608 (@Enclosure.Real.IsNear.of_eq qz167 (@HMul.hMul Real Real Real qz5 qz166 qz3) Bool.false 1325163452091 16777216000 496283 16777216000 (BSN.t_div_two_pi_mk qz166 496283 1000 qz169) (@Enclosure.Real.IsNear.mulLit_ff qz166 qz3 496283 1000 0 1 2670177 16777216 1 16777216 1325163452091 16777216000 496283 16777216000 (Enclosure.Real.IsNear.const Bool.false 496283 1000) RS205to222.d40 rfl)) 

noncomputable abbrev qz895 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 496283 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz737 := qz895

noncomputable abbrev qz514 := qz737

noncomputable abbrev qz171 := qz514

noncomputable def Ns204p1352 := @Enclosure.Real.IsNear.sqrt_image qz171 149105847 16777216 29 16777216 25007901 25007907 8388608 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 149105847 16777216 29 16777216 149105847 16777216 29 16777216 (Ns204p1351 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns204p1353 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz171) 781497 262144 3 8388608 2813859 2813861 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz171) Bool.false 50015808 16777216 6 16777216 781497 262144 3 8388608 (Ns204p1352 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns204p1354 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz171)) Bool.false 5627720 16777216 2 16777216 703465 2097152 1 8388608 (Ns204p1353 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz342 qz340 qz507)

noncomputable abbrev qz738 := (@HMul.hMul Real Real Real qz844 qz893 qz893)

noncomputable abbrev qz515 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz738 qz730) qz640)

noncomputable abbrev qz173 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz515))

noncomputable def Ns204p1355 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz168) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz172)) qz173) Bool.false 96835433585697 

noncomputable def Ns204p1356 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz172)) qz173 22075227 16777216 329 

noncomputable def Ns204p1357 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz172)) Bool.false 22075227 16777216 329 16777216 22075227 16777216 329 

noncomputable def Ns204p1358 := @Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.false 12750717 16777216 485257216 42949672960000 12750717 16777216 118471 10485760000 

noncomputable def Ns204p1359 := @Enclosure.Real.IsNear.cos_image qz172 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46772405) qz359) Bool.false 46772405 8388608 183 16777216 Bool.false 12750717 16777216 1 

noncomputable def Ns204p1360 := nat_lit 782596186990165286607812491 

noncomputable def Ns204p1361 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz168 884279719003555 140737488355328 1 500000000000000 14888119 16777216 29 16777216 13165261685811488263045 2361183241434822606848 Ns204p1360 

noncomputable def Ns204p1362 := @Enclosure.Real.IsNear.subLit_ff_p qz171 qz1 149105847 16777216 29 16777216 8 1 0 1 14888119 14888119 16777216 29 

noncomputable def Ns204p1363 := @Ns204p1362 16777216 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 149105847 16777216 29 16777216 149105847 16777216 29 16777216 (Ns204p1351 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns204p1364 := @Enclosure.Real.IsNear.recentre' qz172 Bool.false 13165261685811488263045 2361183241434822606848 Ns204p1360 Ns204p521 46772405 8388608 183 16777216 (@Ns204p1361 Ns204p521 RS205to222.d39 (Ns204p1363 rfl rfl) rfl) 

noncomputable def Ns204p1365 := nat_lit 3263922855178916608147012767909703793072622175289388635015808921845011604003836987890625 

noncomputable def Ns204p1366 := nat_lit 599456771322173370033572541208445664441261945884082062279796574911274218902587890625 

noncomputable def Ns204p1367 := nat_lit 8547398833553117121595455274696791498400153177845538863607237029425174042703254587890625 

noncomputable def Ns204p1368 := BSN.sin_dyadic_bound_f 29663318425 34359738368 3 2 16777216 5125001 Ns204p1365 Ns204p1161 Ns204p1366 Ns204p1367 Ns204p1164 Ns204p1366 12750717 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 29663318425) qz357 0 2 Ns204p1365 Ns204p1161 Ns204p1366 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 29663318425) qz358 0 2 Ns204p1367 Ns204p1164 Ns204p1366 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1369 := @Ns204p1359 2560000 (Ns204p1364 rfl) (Enclosure.sfrac_false_div 46772405 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46772405) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1043685232880593917706240) qz360) 226375608064910080 72057594037927936 Bool.false 12750717 16777216 0 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q3 46772405 8388608 226375608064910080 72057594037927936 0 1043685232880593917706240 Ns204p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 12750717 16777216 1043685232880593917706240 Ns204p100 29663318425 34359738368 5125001 5120000 (Ns204p1368 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p1370 := @Enclosure.Real.IsNear.inv_image (Real.cos qz172) 12750717 16777216 118471 10485760000 11037449 11037778 8388608 (Ns204p1358 (Ns204p1369 rfl rfl) rfl) rfl 

noncomputable def Ns204p1371 := @Enclosure.Real.IsNear.recentre' qz173 Bool.false 4386611 8388608 

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz342 qz340 qz515)

noncomputable def Ns204p1372 := @Enclosure.Real.IsNear.cos_image qz174 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 17121445)) qz369) Bool.true 17121445 16777216 

noncomputable def Ns204p1373 := nat_lit 40426869686895867263745419245 

noncomputable def Ns204p1374 := nat_lit 36432578281350558979011948082117497 

noncomputable def Ns204p1375 := @Enclosure.Real.IsNear.recentre' qz174 Bool.true Ns204p1373 Ns204p533 Ns204p1374 

noncomputable abbrev qz175 := qz515

noncomputable def Ns204p1376 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz175 884279719003555 140737488355328 1 500000000000000 45717286982959 

noncomputable abbrev qz516 := (@HSub.hSub Real Real Real qz634 qz738 qz730)

noncomputable abbrev qz176 := qz516

noncomputable def Ns204p1377 := @Enclosure.Real.IsNear.subLit_tf qz176 qz27 28125100938543 281474976710656 1350051007 281474976710656 1 16 

noncomputable abbrev qz517 := qz738

noncomputable abbrev qz177 := qz517

noncomputable def Ns204p1378 := @Enclosure.Real.IsNear.subLit_ff_n qz177 qz168 221656087358161 281474976710656 863511743 281474976710656 14888119 16777216 29 16777216 

noncomputable def Ns204p1379 := @Enclosure.Real.IsNear.mulLit_ff qz168 qz168 14888119 16777216 29 16777216 14888119 16777216 29 16777216 221656087358161 281474976710656 

noncomputable def Ns204p1380 := nat_lit 11445395956438550270500246087232241766638575434280710385190625 

noncomputable def Ns204p1381 := nat_lit 7384537845868556024679714662455003311298583172670500390625 

noncomputable def Ns204p1382 := nat_lit 34321418793623913699451378832371815293293129136496790154790625 

noncomputable def Ns204p1383 := BSN.cos_dyadic_bound_f 17121445 16777216 3 2 8388608 2560000 Ns204p1380 Ns204p754 Ns204p1381 Ns204p1382 Ns204p757 Ns204p1381 4386611 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 17121445) (BSN.cosEvenQ 16777216) 0 2 Ns204p1380 Ns204p754 Ns204p1381 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 17121445) (BSN.cosOddQ 16777216) 0 2 Ns204p1382 Ns204p757 Ns204p1381 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1384 := @Ns204p1371 656068608 21474836480000 4386611 8388608 160173 5242880000 (@Ns204p1372 253 8388608 Bool.false 4386611 8388608 1 2560000 (@Ns204p1375 Ns204p536 17121445 16777216 253 8388608 (@Ns204p1376 281474976710656 1350051007 281474976710656 Ns204p1373 Ns204p533 Ns204p1374 Ns204p536 RS205to222.d39 (@Ns204p1377 0 1 731476591727344 45717286982959 281474976710656 1350051007 281474976710656 (@Ns204p1378 471860893467738636288 28125100938543 281474976710656 1350051007 281474976710656 (@Ns204p1379 863511743 281474976710656 (Ns204p1363 rfl rfl) (Ns204p1363 rfl rfl) rfl) (Ns204p1363 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 17121445 16777216) (BSN.cos_neg_of_bound 17121445 16777216 Bool.false 4386611 8388608 1 2560000 (Ns204p1383 rfl rfl)) rfl rfl) 

noncomputable def Ns204p1385 := @Ns204p1349 3137042429159182967 184467440737095516160000 (Ns204p1350 qz29 (@Enclosure.Real.IsNear.of_eq qz736 (@Inv.inv Real Real.instInv (Real.sqrt qz171)) Bool.false 703465 2097152 1 8388608 (BSN.rpow_neg_quarter_mk qz167 (BSN.t_div_two_pi_nonneg qz166 496283 1000 qz169)) Ns204p1354) rfl) (@Ns204p1355 140737488355328 4437904918063 87960930222080000 (BSN.correction_mk qz168 (BSN.cos_two_pi_p_ne_zero_mk qz166 496283 1000 8 qz169 rfl rfl (@BSN.floor_sqrt_eq_dec qz166 496283 1000 8 qz169 rfl rfl rfl))) (@Ns204p1356 16777216 4386611 8388608 160173 5242880000 96835433585697 140737488355328 4437904918063 87960930222080000 (@Ns204p1357 16777216 (Ns204p1370 rfl rfl rfl rfl rfl) rfl) (Ns204p1384 rfl) rfl)) 

noncomputable def Ns204p1386 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz166) (hardyZApproximantRS₀ qz166) Bool.false 163172404364062198519 295147905179352825856 269144639316076302967 184467440737095516160000 (@Eq.refl Real (hardyZApproximantRS₀ qz166)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz166) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz166) qz166 8) (@HMul.hMul Real Real Real qz5 qz731 (Zeta.RiemannSiegel.correction qz168))) Bool.false 163172404364062198519 295147905179352825856 269144639316076302967 184467440737095516160000 (BSN.hardyZApproximantRS₀_eq qz166 8 (@BSN.floor_sqrt_eq_dec qz166 496283 1000 8 qz169 rfl rfl rfl)) (@Ns204p1286 163172404364062198519 295147905179352825856 269144639316076302967 184467440737095516160000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz166) qz166 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz166) qz166 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz166) qz166 8)) Bool.false 52589881 67108864 96773 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz166) qz166 8) (Ns204p1348 (Ns204p1347 rfl rfl rfl rfl) rfl rfl)) (Ns204p1385 rfl) rfl rfl)) 

theorem RS205to222.d54 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz166) Bool.false 163172404364062198519 295147905179352825856 269144639316076302967 184467440737095516160000 := Ns204p1386 

noncomputable def Ns204p1387 := nat_lit 204090258153197850129674010624 

noncomputable abbrev qz896 := (Enclosure.sfrac Bool.false 497721 1000)

noncomputable abbrev qz739 := qz896

noncomputable abbrev qz518 := qz739

noncomputable abbrev qz178 := qz518

noncomputable abbrev qz897 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 497721 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz740 := qz897

noncomputable abbrev qz519 := qz740

noncomputable abbrev qz179 := qz519

noncomputable abbrev qz898 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 497721 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz741 := qz898

noncomputable abbrev qz520 := qz741

noncomputable abbrev qz180 := qz520

noncomputable abbrev qz742 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz179 qz9))

noncomputable def Ns204p1388 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz178) qz178 8) (@HMul.hMul Real Real Real qz5 qz742 (Zeta.RiemannSiegel.correction qz180)) 329743333 67108864 97053 67108864 140728804313873096827 590295810358705651712 5966025517038554621 368934881474191032320000 Ns204p1387 

noncomputable def Ns204p1389 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz178) qz178 Real.cos BSN.quadSignPos 7 8 497721 1000 124 134217728 67108864 2251799813685248 Bool.false 112582557265 1825 279097919 53 47453128 8 

noncomputable def Ns204p1390 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz178) qz178 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 497721 1000 33 82 134217728 67108864 2251799813685248 Bool.false 112582557265 1825 

noncomputable def Ns204p1391 := Ns204p1390 240485871 53 54794152 8 261175631 53 50729528 8 Bool.true 256655926 64877 Bool.true 154963368 Bool.true 122084413 7074237752028440 1 Bool.false 122758218 Bool.true Bool.false 82417965 Bool.true Bool.true 337922813 

noncomputable def Ns204p1392 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz178) qz178 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 497721 1000 94 24 134217728 67108864 2251799813685248 Bool.false 112582557265 1825 

noncomputable def Ns204p1393 := Ns204p1392 186065264 53 67108856 8 216015088 53 60023992 8 Bool.true 289961541 38141 Bool.false 156068873 Bool.false 7422511 7074237752028440 1 Bool.false 53253233 Bool.true Bool.false 134012540 Bool.false Bool.true 256655926 

noncomputable def Ns204p1394 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz178) qz178 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 497721 1000 314 185 134217728 67108864 2251799813685248 Bool.false 112582557265 1825 

noncomputable def Ns204p1395 := Ns204p1394 93032624 53 94906264 8 147453232 53 77490640 16 Bool.true 134217720 1885 Bool.false 78050377 Bool.false 188675066 7074237752028440 1 Bool.false 112156137 Bool.true Bool.false 132393561 Bool.true Bool.true 289961541 

noncomputable def Ns204p1396 := nat_lit 229719624196927942308883688678769422024418341073758354161 

noncomputable def Ns204p1397 := nat_lit 273865213097767687517556571603323430685959587364864000 

noncomputable def Ns204p1398 := nat_lit 14661289615569138973009081248480000 

noncomputable def Ns204p1399 := nat_lit 43783410992402401754084613550864284480 

noncomputable abbrev qz521 := (@Eq.refl Real qz739)

noncomputable abbrev qz181 := qz521

noncomputable def Ns204p1400 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz178 497721 1000 990905775364 16000000 995442 4000 2000 Ns204p1398 Ns204p1399 qz181 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns204p1401 := nat_lit 661592517687152473849585023394855935430324822292424059983680 

noncomputable abbrev qz743 := (Real.log (Enclosure.sfrac Bool.false 990905775364 16000000))

noncomputable abbrev qz182 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 497721 4000) qz743) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 995442))))))

noncomputable abbrev qz744 := (Enclosure.sfrac Bool.false 497721 2000)

noncomputable abbrev qz522 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz182 qz744) (@HMul.hMul Real Real Real qz5 qz744 (Real.log Real.pi)))

noncomputable def Ns204p1402 := @Enclosure.Real.IsNear.addLit_ft_p qz522 (Enclosure.sfrac Bool.true Ns204p1398 Ns204p1399) 15110581080954848309041 18014398509481984000 5566453664941281 409600000000000000000 Ns204p1398 Ns204p1399 0 1 Ns204p1401 

noncomputable def Ns204p1403 := nat_lit 1014053930722771905312062439424000 

noncomputable abbrev qz523 := (@HSub.hSub Real Real Real qz12 qz182 qz744)

noncomputable abbrev qz524 := (@HMul.hMul Real Real Real qz5 qz744 (Real.log Real.pi))

noncomputable def Ns204p1404 := @Enclosure.Real.IsNear.subLit_ff_p qz523 qz524 20242487816806900854577 18014398509481984000 77166923967 12500000000000000 19117842375681 67108864000 497721 67108864000 Ns204p1403 15110581080954848309041 18014398509481984000 

noncomputable def Ns204p1405 := nat_lit 40484975633613801709154000 

noncomputable abbrev qz525 := qz744

noncomputable def Ns204p1406 := @Enclosure.Real.IsNear.subLit_ff_p qz182 qz525 24725560037075842133809 18014398509481984000 77166923967 12500000000000000 497721 2000 0 1 Ns204p1405 20242487816806900854577 18014398509481984000 77166923967 12500000000000000 

noncomputable def Ns204p1407 := nat_lit 55677011484750794948014773848225349632 

noncomputable def Ns204p1408 := nat_lit 26678057567134835957301248 

noncomputable def Ns204p1409 := nat_lit 681417982414525222326506905073841539844987923375117750903525933149126857397029970281647719410387134519457602769632041210827667423848112073707657288726398990112837193582405222400 

noncomputable def Ns204p1410 := nat_lit 22857097750912526692393722436680672021746500144846897652124971331016855283237919447405652209364359853591702477850378402043037059752049108043687513800914086067052230544394813440 

noncomputable def Ns204p1411 := nat_lit 3134914851715612979735979751685852139131308073791141388353504120515276970748892218326114316753446736131062536464321106655994657169104910261816490758405559451256000348160 

noncomputable def Ns204p1412 := BSN.log_dyadic_bound 466617775364 1515193775364 8 7 Ns204p1409 67108864 20480000 Ns204p1410 Ns204p1411 42720046 1981811550728 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 466617775364) (BSN.artanhQ 1515193775364) 0 7 Ns204p1410 Ns204p1409 Ns204p1411 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns204p1413 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 497721 4000) qz743 497721 4000 0 1 49691754518327929 4503599627370496 2441407 50000000000000 24732629750616695149809 18014398509481984000 1215139533447 200000000000000000 (Enclosure.Real.IsNear.const Bool.false 497721 4000) (BSN.isNear_log_sfrac 990905775364 16000000 49691754518327929 4503599627370496 2441407 50000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 990905775364) qz352)) Bool.false Ns204p1408 Ns204p89 1000000307200000 20480000000000000000000 49691754518327929 4503599627370496 2441407 50000000000000 (BSN.log_rat_reduce_isNear 990905775364 16000000 15 1981811550728 1048576000000 42720046 67108864 24973259072661432 36028797018963968 20480000 1000000000000000 rfl rfl rfl rfl (Ns204p1412 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns204p1414 := BSN.arctan_dyadic_bound_f 1000 995442 1 0 8388608 2560000 0 1 1 0 1 1 8427 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 995442) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 995442) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz526 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 995442)))

noncomputable def Ns204p1415 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz526 884279719003555 562949953421312 1 2000000000000000 8427 8388608 1 2560000 7413131945813492105216 883714192606627 562949953421312 781250001 2000000000000000 qz17 (Ns204p1414 rfl) rfl rfl 

noncomputable def Ns204p1416 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 497721 4000) qz743) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz526)) 24732629750616695149809 18014398509481984000 1215139533447 200000000000000000 883714192606627 2251799813685248 781250001 8000000000000000 Ns204p1407 24725560037075842133809 18014398509481984000 77166923967 12500000000000000 (Ns204p1413 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz526) 1 4 0 1 883714192606627 562949953421312 781250001 2000000000000000 883714192606627 2251799813685248 781250001 8000000000000000 qz355 Ns204p1415 rfl) 

noncomputable def Ns204p1417 := @Ns204p1402 Ns204p1396 Ns204p1397 5566453664941281 409600000000000000000 (@Ns204p1404 5566453664941281 409600000000000000000 (Ns204p1406 (Ns204p1416 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 497721 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz525 (Real.log Real.pi) 497721 2000 0 1 38410761 33554432 1 33554432 19117842375681 67108864000 497721 67108864000 (Enclosure.Real.IsNear.const Bool.false 497721 2000) RS205to222.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns204p1398 Ns204p1399) 

noncomputable def Ns204p1418 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz178) Bool.false Ns204p1396 Ns204p1397 5566453664941281 409600000000000000000 7036409829 8388608 229 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz178) (@HAdd.hAdd Real Real Real qz356 qz522 (Enclosure.sfrac Bool.true Ns204p1398 Ns204p1399)) Bool.false Ns204p1396 Ns204p1397 5566453664941281 409600000000000000000 Ns204p1400 (Ns204p1417 rfl rfl)) 

noncomputable def Ns204p1419 := nat_lit 1899191661051663003680768 

noncomputable def Ns204p1420 := nat_lit 857527361051483481207961683964066625822223851936883111844906680402818305417195013418393819278659492881138628314368564083782000156218401 

noncomputable def Ns204p1421 := nat_lit 611825928677465605968901237188954781475510367949703583302424891702480960077925038394844518755533439098020592611323606494715450401 

noncomputable def Ns204p1422 := nat_lit 4282306473139418440029060894765285101814613275564823157953652027063398582114936949956640043246647354605623162229359357469974029204067361 

noncomputable def Ns204p1423 := BSN.sin_dyadic_bound_f 53978273543 34359738368 4 3 16777216 5125001 Ns204p1420 Ns204p217 Ns204p1421 Ns204p1422 Ns204p220 Ns204p1421 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53978273543) qz357 0 3 Ns204p1420 Ns204p217 Ns204p1421 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53978273543) qz358 0 3 Ns204p1422 Ns204p220 Ns204p1421 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1424 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz178) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7036409829) qz359) Bool.false 7036409829 8388608 229 16777216 Bool.true 16777215 16777216 1 2560000 (Ns204p1418 rfl) (Enclosure.sfrac_false_div 7036409829 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7036409829) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns204p1419) qz360) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 133 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q1 7036409829 8388608 226375608064910080 72057594037927936 133 Ns204p1419 Ns204p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 Ns204p1419 Ns204p100 53978273543 34359738368 5125001 5120000 (Ns204p1423 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p1425 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz178) Bool.false Ns204p1396 Ns204p1397 5566453664941281 409600000000000000000 112582557265 134217728 1825 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz178) (@HAdd.hAdd Real Real Real qz356 qz522 (Enclosure.sfrac Bool.true Ns204p1398 Ns204p1399)) Bool.false Ns204p1396 Ns204p1397 5566453664941281 409600000000000000000 Ns204p1400 (Ns204p1417 rfl rfl)) 

noncomputable def Ns204p1426 := Ns204p1395 38141 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 314 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 112156137 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 185 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132393561 134217728) qz181 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 1) Bool.true 16777215 16777216 147221 10485760000 134217720 134217728 1885 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz178)) Bool.true 16777215 16777216 147221 10485760000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz178) qz178) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz178)) Bool.true 16777215 16777216 603017216 42949672960000 16777215 16777216 147221 10485760000 (Ns204p1424 rfl rfl) rfl)) rfl) (Ns204p1425 rfl) RS205to222.d7 

noncomputable def Ns204p1427 := nat_lit 20233843896430441291034404370482857378270995359352811994277452196161 

noncomputable def Ns204p1428 := nat_lit 1377209599257250087712937956804735401391338838398456887713474881 

noncomputable def Ns204p1429 := nat_lit 60698777270092809372927787235534962664010203400381639069056929638721 

noncomputable def Ns204p1430 := BSN.cos_dyadic_bound_f 78050377 134217728 3 2 134217728 67108864 Ns204p1427 Ns204p240 Ns204p1428 Ns204p1429 Ns204p243 Ns204p1428 112156137 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 78050377) qz363 0 2 Ns204p1427 Ns204p240 Ns204p1428 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 78050377) qz364 0 2 Ns204p1429 Ns204p243 Ns204p1428 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1431 := nat_lit 6934206305649254043546182354414604382284266641551322926068782668754693910922624717373590258528890436653056 

noncomputable def Ns204p1432 := nat_lit 2035045515341600004696161906080624946589754617638971355014482969234513705162334966254616372572000256 

noncomputable def Ns204p1433 := nat_lit 34643382045595895762887587845579765540695165384899318799922868947871002929592425012413141513780338838409216 

noncomputable def Ns204p1434 := BSN.sin_dyadic_bound_f 188675066 134217728 4 3 134217728 67108864 Ns204p1431 Ns204p256 Ns204p1432 Ns204p1433 Ns204p259 Ns204p1432 132393561 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 188675066) qz361 0 3 Ns204p1431 Ns204p256 Ns204p1432 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 188675066) qz362 0 3 Ns204p1433 Ns204p259 Ns204p1432 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1435 := nat_lit 1248367305730455747521048102911264269193687165382092387639456385507148875923758374438695213100369830168801 

noncomputable def Ns204p1436 := nat_lit 208831270778302405274869401503964186756946094532379278338240578717037121461984118771649221007722721 

noncomputable def Ns204p1437 := nat_lit 7567938870365895037187171531817467805166708674702727484633573482080126963566119832941652324180065319864545 

noncomputable def Ns204p1438 := BSN.cos_dyadic_bound_f 156068873 134217728 4 3 134217728 67108864 Ns204p1435 Ns204p230 Ns204p1436 Ns204p1437 Ns204p233 Ns204p1436 53253233 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 156068873) qz363 0 3 Ns204p1435 Ns204p230 Ns204p1436 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 156068873) qz364 0 3 Ns204p1437 Ns204p233 Ns204p1436 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1439 := nat_lit 3035312423946993175054904641 

noncomputable def Ns204p1440 := BSN.cos_dyadic_bound_f 7422511 134217728 2 1 134217728 67108864 Ns204p1439 Ns204p125 Ns204p1439 Ns204p1439 Ns204p126 Ns204p1439 134012540 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 7422511) qz363 0 1 Ns204p1439 Ns204p125 Ns204p1439 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 7422511) qz364 0 1 Ns204p1439 Ns204p126 Ns204p1439 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1441 := Ns204p1393 64877 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 94 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 53253233 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 24 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 134012540 134217728) qz181 rfl rfl (Ns204p1426 RS205to222.d9 RS205to222.d11 RS205to222.d13 RS205to222.d17 (Ns204p1430 rfl rfl) (Ns204p1434 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns204p1425 rfl) RS205to222.d19 RS205to222.d21 RS205to222.d23 RS205to222.d25 RS205to222.d17 (Ns204p1438 rfl rfl) (Ns204p1440 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns204p1442 := nat_lit 566229680121780228608273349873262405302149276261778299733520857169920 

noncomputable def Ns204p1443 := nat_lit 332531180992212340685787175292328463649983924604671023475826098176 

noncomputable def Ns204p1444 := nat_lit 1482444111740198921612938927574737767802576701950535603359308050333696 

noncomputable def Ns204p1445 := BSN.sin_dyadic_bound_f 154963368 134217728 3 2 134217728 67108864 Ns204p1442 Ns204p106 Ns204p1443 Ns204p1444 Ns204p109 Ns204p1443 122758218 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 154963368) qz361 0 2 Ns204p1442 Ns204p106 Ns204p1443 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 154963368) qz362 0 2 Ns204p1444 Ns204p109 Ns204p1443 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1446 := nat_lit 121162050754115420306035231522540583259753097351604609933361312900001 

noncomputable def Ns204p1447 := nat_lit 49349386173237568670693415497317776631139057682041927903109129121 

noncomputable def Ns204p1448 := nat_lit 363387453489999785780764307736627114225997013939449745944277720441761 

noncomputable def Ns204p1449 := BSN.cos_dyadic_bound_f 122084413 134217728 3 2 134217728 67108864 Ns204p1446 Ns204p240 Ns204p1447 Ns204p1448 Ns204p243 Ns204p1447 82417965 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 122084413) qz363 0 2 Ns204p1446 Ns204p240 Ns204p1447 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 122084413) qz364 0 2 Ns204p1448 Ns204p243 Ns204p1447 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1450 := Ns204p1391 87071 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 33 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 122758218 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 82 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 82417965 134217728) qz181 rfl rfl (Ns204p1441 rfl rfl) (Ns204p1425 rfl) RS205to222.d27 RS205to222.d29 RS205to222.d31 RS205to222.d33 RS205to222.d17 (Ns204p1445 rfl rfl) (Ns204p1449 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns204p1451 := nat_lit 2608034754174193075390449748126031283009675856369241039208345707370478184574748623067738321503868369140625 

noncomputable def Ns204p1452 := nat_lit 1897446829670249004364540280836742226492527829736970634176477002177308549478310179769992828369140625 

noncomputable def Ns204p1453 := nat_lit 15798169911449766629870184144353194498492702417872785314933136198715665848998140502103727569159804369140625 

noncomputable def Ns204p1454 := BSN.cos_dyadic_bound_f 187577525 134217728 4 3 134217728 67108864 Ns204p1451 Ns204p230 Ns204p1452 Ns204p1453 Ns204p233 Ns204p1452 23135067 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 187577525) qz363 0 3 Ns204p1451 Ns204p230 Ns204p1452 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 187577525) qz364 0 3 Ns204p1453 Ns204p233 Ns204p1452 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1455 := Ns204p1389 Bool.true 337922813 87071 Bool.true 187577525 7074237752028440 1 Bool.false 23135067 Bool.false Bool.true 329743333 97053 BSN.abs_quadSignPos qz735 (BSN.sfrac_eq_quadSignPos_mul Bool.false 23135067 134217728) qz181 rfl (Ns204p1450 rfl) (Ns204p1425 rfl) RS205to222.d35 RS205to222.d37 RS205to222.d17 (Ns204p1454 rfl rfl) rfl 

noncomputable def Ns204p1456 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 8) 329743333 134217728 97053 134217728 329743333 134217728 97053 134217728 88514801956814848 329743333 67108864 97053 67108864 (Ns204p1455 rfl rfl rfl rfl) 

noncomputable def Ns204p1457 := @Enclosure.Real.IsNear.mulLit_ff qz742 (Zeta.RiemannSiegel.correction qz180) 5623651 16777216 1 16777216 25024455520777 35184372088832 1058099831273 21990232555520000 140728804313873096827 590295810358705651712 

noncomputable abbrev qz745 := (@HPow.hPow Real Real Real qz7 qz179 qz9)

noncomputable def Ns204p1458 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz745 1 1 0 1 5623651 16777216 1 16777216 5623651 16777216 1 16777216 

noncomputable def Ns204p1459 := @Enclosure.Real.IsNear.sqrt_image qz179 1329003166617 16777216000 497721 16777216000 74660841 74660870 8388608 (@Enclosure.Real.IsNear.of_eq qz179 (@HMul.hMul Real Real Real qz5 qz178 qz3) Bool.false 1329003166617 16777216000 497721 16777216000 (BSN.t_div_two_pi_mk qz178 497721 1000 qz181) (@Enclosure.Real.IsNear.mulLit_ff qz178 qz3 497721 1000 0 1 2670177 16777216 1 16777216 1329003166617 16777216000 497721 16777216000 (Enclosure.Real.IsNear.const Bool.false 497721 1000) RS205to222.d40 rfl)) 

noncomputable abbrev qz899 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 497721 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz746 := qz899

noncomputable abbrev qz527 := qz746

noncomputable abbrev qz183 := qz527

noncomputable def Ns204p1460 := @Enclosure.Real.IsNear.sqrt_image qz183 149321711 16777216 29 16777216 25025997 25026002 8388608 (@Enclosure.Real.IsNear.recentre' qz183 Bool.false 149321711 16777216 29 16777216 149321711 16777216 29 16777216 (Ns204p1459 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns204p1461 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz183) 50051999 16777216 5 16777216 2811825 2811826 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz183) Bool.false 50051999 16777216 5 16777216 50051999 16777216 5 16777216 (Ns204p1460 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns204p1462 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz183)) Bool.false 5623651 16777216 1 16777216 5623651 16777216 1 16777216 (Ns204p1461 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz184 := (@HMul.hMul Real Real Real qz342 qz340 qz520)

noncomputable abbrev qz747 := (@HMul.hMul Real Real Real qz844 qz898 qz898)

noncomputable abbrev qz528 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz747 qz741) qz640)

noncomputable abbrev qz185 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz528))

noncomputable def Ns204p1463 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz180) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz184)) qz185) Bool.false 25024455520777 

noncomputable def Ns204p1464 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz184)) qz185 10356257 8388608 145 

noncomputable def Ns204p1465 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz184)) Bool.false 20712514 16777216 290 16777216 10356257 8388608 145 

noncomputable def Ns204p1466 := @Enclosure.Real.IsNear.recentre' (Real.cos qz184) Bool.false 13589610 16777216 485257216 42949672960000 6794805 8388608 118471 10485760000 

noncomputable def Ns204p1467 := @Enclosure.Real.IsNear.cos_image qz184 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23725281) qz385) Bool.false 23725281 4194304 183 16777216 Bool.false 13589610 16777216 1 

noncomputable def Ns204p1468 := nat_lit 782596186992019544248579979 

noncomputable def Ns204p1469 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz180 884279719003555 140737488355328 1 500000000000000 15103983 16777216 29 16777216 13356145843074471659565 2361183241434822606848 Ns204p1468 

noncomputable def Ns204p1470 := @Enclosure.Real.IsNear.subLit_ff_p qz183 qz1 149321711 16777216 29 16777216 8 1 0 1 15103983 15103983 16777216 29 

noncomputable def Ns204p1471 := @Ns204p1470 16777216 (@Enclosure.Real.IsNear.recentre' qz183 Bool.false 149321711 16777216 29 16777216 149321711 16777216 29 16777216 (Ns204p1459 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns204p1472 := @Enclosure.Real.IsNear.recentre' qz184 Bool.false 13356145843074471659565 2361183241434822606848 Ns204p1468 Ns204p521 23725281 4194304 183 16777216 (@Ns204p1469 Ns204p521 RS205to222.d39 (Ns204p1471 rfl rfl) rfl) 

noncomputable def Ns204p1473 := nat_lit 4669548307429722550958095143138887681385367029658594244200868466512230395390807263239105 

noncomputable def Ns204p1474 := nat_lit 1226758750943335315280307844268774255049154153281219218153713579723423767709900954561 

noncomputable def Ns204p1475 := nat_lit 12227783195766793661998842971711127816739215018571958189410978066498194063732964897414081 

noncomputable def Ns204p1476 := BSN.sin_dyadic_bound_f 32441049497 34359738368 3 2 16777216 5125001 Ns204p1473 Ns204p1161 Ns204p1474 Ns204p1475 Ns204p1164 Ns204p1474 13589610 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 32441049497) qz357 0 2 Ns204p1473 Ns204p1161 Ns204p1474 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 32441049497) qz358 0 2 Ns204p1475 Ns204p1164 Ns204p1474 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1477 := @Ns204p1467 2560000 (Ns204p1472 rfl) (Enclosure.sfrac_false_div 23725281 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23725281) qz385) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 570708978240276054147072) qz386) 226375608064910080 72057594037927936 Bool.false 13589610 16777216 0 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q3 23725281 4194304 226375608064910080 72057594037927936 0 570708978240276054147072 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 13589610 16777216 570708978240276054147072 604462909807314587353088 32441049497 34359738368 5125001 5120000 (Ns204p1476 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p1478 := @Enclosure.Real.IsNear.inv_image (Real.cos qz184) 6794805 8388608 118471 10485760000 10356112 10356402 8388608 (Ns204p1466 (Ns204p1477 rfl rfl) rfl) rfl 

noncomputable def Ns204p1479 := @Enclosure.Real.IsNear.recentre' qz185 Bool.false 4832722 8388608 

noncomputable abbrev qz186 := (@HMul.hMul Real Real Real qz342 qz340 qz528)

noncomputable def Ns204p1480 := @Enclosure.Real.IsNear.cos_image qz186 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16053119)) qz369) Bool.true 16053119 16777216 

noncomputable def Ns204p1481 := nat_lit 37904357309459469658840822525 

noncomputable def Ns204p1482 := nat_lit 36770446967887732437706383221455433 

noncomputable def Ns204p1483 := @Enclosure.Real.IsNear.recentre' qz186 Bool.true Ns204p1481 Ns204p533 Ns204p1482 

noncomputable abbrev qz187 := qz528

noncomputable def Ns204p1484 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz187 884279719003555 140737488355328 1 500000000000000 42864668831455 

noncomputable abbrev qz529 := (@HSub.hSub Real Real Real qz634 qz747 qz741)

noncomputable abbrev qz188 := qz529

noncomputable def Ns204p1485 := @Enclosure.Real.IsNear.subLit_tf qz188 qz27 25272482787039 281474976710656 1362571119 281474976710656 1 16 

noncomputable abbrev qz530 := qz747

noncomputable abbrev qz189 := qz530

noncomputable def Ns204p1486 := @Enclosure.Real.IsNear.subLit_ff_n qz189 qz180 228130302464289 281474976710656 876031855 281474976710656 15103983 16777216 29 16777216 

noncomputable def Ns204p1487 := @Enclosure.Real.IsNear.mulLit_ff qz180 qz180 15103983 16777216 29 16777216 15103983 16777216 29 16777216 228130302464289 281474976710656 

noncomputable def Ns204p1488 := nat_lit 8843887285599383084363637765208596566601641355723475969336321 

noncomputable def Ns204p1489 := nat_lit 4410373811456119383031026653455197373021267756984933770241 

noncomputable def Ns204p1490 := nat_lit 26522841109175237014324851242318879305058881531656458040468481 

noncomputable def Ns204p1491 := BSN.cos_dyadic_bound_f 16053119 16777216 3 2 8388608 2560000 Ns204p1488 Ns204p754 Ns204p1489 Ns204p1490 Ns204p757 Ns204p1489 4832722 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 16053119) (BSN.cosEvenQ 16777216) 0 2 Ns204p1488 Ns204p754 Ns204p1489 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 16053119) (BSN.cosOddQ 16777216) 0 2 Ns204p1490 Ns204p757 Ns204p1489 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1492 := @Ns204p1479 2592768 83886080000 2416361 4194304 633 20480000 (@Ns204p1480 1 32768 Bool.false 4832722 8388608 1 2560000 (@Ns204p1483 Ns204p536 16053119 16777216 1 32768 (@Ns204p1484 281474976710656 1362571119 281474976710656 Ns204p1481 Ns204p533 Ns204p1482 Ns204p536 RS205to222.d39 (@Ns204p1485 0 1 685834701303280 42864668831455 281474976710656 1362571119 281474976710656 (@Ns204p1486 424001902574435303424 25272482787039 281474976710656 1362571119 281474976710656 (@Ns204p1487 876031855 281474976710656 (Ns204p1471 rfl rfl) (Ns204p1471 rfl rfl) rfl) (Ns204p1471 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16053119 16777216) (BSN.cos_neg_of_bound 16053119 16777216 Bool.false 4832722 8388608 1 2560000 (Ns204p1491 rfl rfl)) rfl rfl) 

noncomputable def Ns204p1493 := @Ns204p1457 5966025517038554621 368934881474191032320000 (Ns204p1458 qz29 (@Enclosure.Real.IsNear.of_eq qz745 (@Inv.inv Real Real.instInv (Real.sqrt qz183)) Bool.false 5623651 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz179 (BSN.t_div_two_pi_nonneg qz178 497721 1000 qz181)) Ns204p1462) rfl) (@Ns204p1463 35184372088832 1058099831273 21990232555520000 (BSN.correction_mk qz180 (BSN.cos_two_pi_p_ne_zero_mk qz178 497721 1000 8 qz181 rfl rfl (@BSN.floor_sqrt_eq_dec qz178 497721 1000 8 qz181 rfl rfl rfl))) (@Ns204p1464 8388608 2416361 4194304 633 20480000 25024455520777 35184372088832 1058099831273 21990232555520000 (@Ns204p1465 8388608 (Ns204p1478 rfl rfl rfl rfl rfl) rfl) (Ns204p1492 rfl) rfl)) 

noncomputable def Ns204p1494 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz178) (hardyZApproximantRS₀ qz178) Bool.true 3041181834834782036091 590295810358705651712 539520535569759194621 368934881474191032320000 (@Eq.refl Real (hardyZApproximantRS₀ qz178)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz178) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz178) qz178 8) (@HMul.hMul Real Real Real qz5 qz742 (Zeta.RiemannSiegel.correction qz180))) Bool.true 3041181834834782036091 590295810358705651712 539520535569759194621 368934881474191032320000 (BSN.hardyZApproximantRS₀_eq qz178 8 (@BSN.floor_sqrt_eq_dec qz178 497721 1000 8 qz181 rfl rfl rfl)) (@Ns204p1388 3041181834834782036091 590295810358705651712 539520535569759194621 368934881474191032320000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz178) qz178 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 8)) Bool.true 329743333 67108864 97053 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz178) qz178 8) (Ns204p1456 (Ns204p1455 rfl rfl rfl rfl) rfl rfl)) (Ns204p1493 rfl) rfl rfl)) 

theorem RS205to222.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz178) Bool.true 3041181834834782036091 590295810358705651712 539520535569759194621 368934881474191032320000 := Ns204p1494 

noncomputable def Ns204p1495 := nat_lit 1998977296811369596429795328 

noncomputable abbrev qz900 := (Enclosure.sfrac Bool.false 499158 1000)

noncomputable abbrev qz748 := qz900

noncomputable abbrev qz531 := qz748

noncomputable abbrev qz190 := qz531

noncomputable abbrev qz901 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 499158 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz749 := qz901

noncomputable abbrev qz532 := qz749

noncomputable abbrev qz191 := qz532

noncomputable abbrev qz902 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 499158 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz750 := qz902

noncomputable abbrev qz533 := qz750

noncomputable abbrev qz192 := qz533

noncomputable abbrev qz751 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz191 qz9))

noncomputable def Ns204p1496 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz190) qz190 8) (@HMul.hMul Real Real Real qz5 qz751 (Zeta.RiemannSiegel.correction qz192)) 58314829 16777216 6083 4194304 9087333424025905125 36893488147419103232 717458571814748757 46116860184273879040000 Ns204p1495 

noncomputable def Ns204p1497 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz190) qz190 Real.cos BSN.quadSignPos 7 8 499158 1000 124 134217728 67108864 2251799813685248 Bool.false 113004327665 1830 279097919 53 47453128 8 

noncomputable def Ns204p1498 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz190) qz190 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 499158 1000 33 82 134217728 67108864 2251799813685248 Bool.false 113004327665 1830 

noncomputable def Ns204p1499 := Ns204p1498 240485871 53 54794152 8 261175631 53 50729528 8 Bool.false 291225788 65059 Bool.true 78771165 Bool.true 75623394 7074237752028440 1 Bool.false 74326405 Bool.true Bool.false 113470859 Bool.true Bool.false 217994214 

noncomputable def Ns204p1500 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz190) qz190 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 499158 1000 95 24 134217728 67108864 2251799813685248 Bool.false 113004327665 1830 

noncomputable def Ns204p1501 := Ns204p1500 186065264 53 67108856 8 216015088 53 60023992 8 Bool.false 207845649 38246 Bool.false 99634774 Bool.false 118779229 7074237752028440 1 Bool.false 90732768 Bool.false Bool.false 85001355 Bool.false Bool.false 291225788 

noncomputable def Ns204p1502 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz190) qz190 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 499158 1000 315 186 134217728 67108864 2251799813685248 Bool.false 113004327665 1830 

noncomputable def Ns204p1503 := Ns204p1502 93032624 53 94906264 8 147453232 53 77490640 16 Bool.false 134217656 1885 Bool.false 155304182 Bool.false 187726457 7074237752028440 1 Bool.false 122895618 Bool.false Bool.false 22988350 Bool.true Bool.false 207845649 

noncomputable def Ns204p1504 := nat_lit 1832839820980096268955258851464315289874718895142683263 

noncomputable def Ns204p1505 := nat_lit 2176904209260703626237737163044938773596399992832000 

noncomputable def Ns204p1506 := nat_lit 14874162471003848468936123888640000 

noncomputable def Ns204p1507 := nat_lit 44547364003270405728789306675490590720 

noncomputable abbrev qz534 := (@Eq.refl Real qz748)

noncomputable abbrev qz193 := qz534

noncomputable def Ns204p1508 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz190 499158 1000 996635835856 16000000 998316 4000 2000 Ns204p1506 Ns204p1507 qz193 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns204p1509 := nat_lit 337829035803051344293833311501902594229708186752699379036160 

noncomputable abbrev qz752 := (Real.log (Enclosure.sfrac Bool.false 996635835856 16000000))

noncomputable abbrev qz194 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 499158 4000) qz752) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 998316))))))

noncomputable abbrev qz753 := (Enclosure.sfrac Bool.false 499158 2000)

noncomputable abbrev qz535 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz194 qz753) (@HMul.hMul Real Real Real qz5 qz753 (Real.log Real.pi)))

noncomputable def Ns204p1510 := @Enclosure.Real.IsNear.addLit_ft_p qz535 (Enclosure.sfrac Bool.true Ns204p1506 Ns204p1507) 7583595064183708721203 9007199254740992000 2791204709550819 204800000000000000000 Ns204p1506 Ns204p1507 0 1 Ns204p1509 

noncomputable def Ns204p1511 := nat_lit 254463224896687889793413021696000 

noncomputable abbrev qz536 := (@HSub.hSub Real Real Real qz12 qz194 qz753)

noncomputable abbrev qz537 := (@HMul.hMul Real Real Real qz5 qz753 (Real.log Real.pi))

noncomputable def Ns204p1512 := @Enclosure.Real.IsNear.subLit_ff_p qz536 qz537 10156956749198444732467 9007199254740992000 1238179085331 200000000000000000 9586519319619 33554432000 249579 33554432000 Ns204p1511 7583595064183708721203 9007199254740992000 

noncomputable def Ns204p1513 := nat_lit 4062782699679377892986800 

noncomputable abbrev qz538 := qz753

noncomputable def Ns204p1514 := @Enclosure.Real.IsNear.subLit_ff_p qz194 qz538 2480992906399489354967 1801439850948198400 1238179085331 200000000000000000 499158 2000 0 1 Ns204p1513 10156956749198444732467 9007199254740992000 1238179085331 200000000000000000 

noncomputable def Ns204p1515 := nat_lit 5586699364384792059934618502683426816 

noncomputable def Ns204p1516 := nat_lit 26691998874112527045754880 

noncomputable def Ns204p1517 := nat_lit 718395547080016150460904975899378430896518117416277005517165804081036967740653418038125921393391658046161028042171504431176221515528605655352815401015364523933386146604017254400 

noncomputable def Ns204p1518 := nat_lit 24532990939020267219745831828211104126675047224962641187936204056057744871318335629046382826196691190605300640165950242796709036346006080122229511973787798427911531837144432640 

noncomputable def Ns204p1519 := nat_lit 3719074383636406211064000430718756887048128747009674446339942952360188042873175925055981377291237235863281192673185413959009343326371219089017878819609160076110027816960 

noncomputable def Ns204p1520 := BSN.log_dyadic_bound 472347835856 1520923835856 8 7 Ns204p1517 67108864 20480000 Ns204p1518 Ns204p1519 43106995 1993271671712 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 472347835856) (BSN.artanhQ 1520923835856) 0 7 Ns204p1518 Ns204p1517 Ns204p1519 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns204p1521 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 499158 4000) qz752 499158 4000 0 1 49717722226143865 4503599627370496 2441407 50000000000000 2481699879095751936567 1801439850948198400 609323917653 100000000000000000 (Enclosure.Real.IsNear.const Bool.false 499158 4000) (BSN.isNear_log_sfrac 996635835856 16000000 49717722226143865 4503599627370496 2441407 50000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 996635835856) qz352)) Bool.false Ns204p1516 Ns204p89 1000000307200000 20480000000000000000000 49717722226143865 4503599627370496 2441407 50000000000000 (BSN.log_rat_reduce_isNear 996635835856 16000000 15 1993271671712 1048576000000 43106995 67108864 24973259072661432 36028797018963968 20480000 1000000000000000 rfl rfl rfl rfl (Ns204p1520 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns204p1522 := BSN.arctan_dyadic_bound_f 1000 998316 1 0 8388608 2560000 0 1 1 0 1 1 8402 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 998316) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 998316) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz539 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 998316)))

noncomputable def Ns204p1523 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz539 884279719003555 562949953421312 1 2000000000000000 8402 8388608 1 2560000 7413146019562327638016 883715870328227 562949953421312 781250001 2000000000000000 qz17 (Ns204p1522 rfl) rfl rfl 

noncomputable def Ns204p1524 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 499158 4000) qz752) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz539)) 2481699879095751936567 1801439850948198400 609323917653 100000000000000000 883715870328227 2251799813685248 781250001 8000000000000000 Ns204p1515 2480992906399489354967 1801439850948198400 1238179085331 200000000000000000 (Ns204p1521 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz539) 1 4 0 1 883715870328227 562949953421312 781250001 2000000000000000 883715870328227 2251799813685248 781250001 8000000000000000 qz355 Ns204p1523 rfl) 

noncomputable def Ns204p1525 := @Ns204p1510 Ns204p1504 Ns204p1505 2791204709550819 204800000000000000000 (@Ns204p1512 2791204709550819 204800000000000000000 (Ns204p1514 (Ns204p1524 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 499158 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz538 (Real.log Real.pi) 499158 2000 0 1 38410761 33554432 1 33554432 9586519319619 33554432000 249579 33554432000 (Enclosure.Real.IsNear.const Bool.false 499158 2000) RS205to222.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns204p1506 Ns204p1507) 

noncomputable def Ns204p1526 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz190) Bool.false Ns204p1504 Ns204p1505 2791204709550819 204800000000000000000 7062770479 8388608 229 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz190) (@HAdd.hAdd Real Real Real qz356 qz535 (Enclosure.sfrac Bool.true Ns204p1506 Ns204p1507)) Bool.false Ns204p1504 Ns204p1505 2791204709550819 204800000000000000000 Ns204p1508 (Ns204p1525 rfl rfl)) 

noncomputable def Ns204p1527 := BSN.cos_dyadic_bound_f 35043488 34359738368 1 0 16777216 5125001 0 1 1 0 1 1 16777207 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 35043488) qz642 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 35043488) qz643 0 0 rfl) rfl rfl 

noncomputable def Ns204p1528 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz190) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7062770479) qz359) Bool.false 7062770479 8388608 229 16777216 Bool.false 16777207 16777216 1 2560000 (Ns204p1526 rfl) (Enclosure.sfrac_false_div 7062770479 8388608) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7062770479) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1232983148965446811648) qz360) 226375608064910080 72057594037927936 Bool.false 16777207 16777216 134 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q0 7062770479 8388608 226375608064910080 72057594037927936 134 1232983148965446811648 Ns204p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777207 16777216 1232983148965446811648 Ns204p100 35043488 34359738368 5125001 5120000 (Ns204p1527 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p1529 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz190) Bool.false Ns204p1504 Ns204p1505 2791204709550819 204800000000000000000 113004327665 134217728 1830 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz190) (@HAdd.hAdd Real Real Real qz356 qz535 (Enclosure.sfrac Bool.true Ns204p1506 Ns204p1507)) Bool.false Ns204p1504 Ns204p1505 2791204709550819 204800000000000000000 Ns204p1508 (Ns204p1525 rfl rfl)) 

noncomputable def Ns204p1530 := Ns204p1503 38246 BSN.abs_quadSignPos (BSN.cos_quad_nat3 315 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 122895618 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 186 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 22988350 134217728) qz193 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz190) qz190 1) Bool.false 16777207 16777216 147221 10485760000 134217656 134217728 1885 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz190) qz190 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz190)) Bool.false 16777207 16777216 147221 10485760000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz190) qz190) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz190)) Bool.false 16777207 16777216 603017216 42949672960000 16777207 16777216 147221 10485760000 (Ns204p1528 rfl rfl) rfl)) rfl) (Ns204p1529 rfl) RS205to222.d7 

noncomputable def Ns204p1531 := nat_lit 571230378848798479605207621356314067638902571678525803385262790795520 

noncomputable def Ns204p1532 := nat_lit 338427155624376739622179328211763619228327698567790517180684165376 

noncomputable def Ns204p1533 := nat_lit 1495531633971080360435203098925622559861232300027029252790729058672896 

noncomputable def Ns204p1534 := BSN.sin_dyadic_bound_f 155304182 134217728 3 2 134217728 67108864 Ns204p1531 Ns204p106 Ns204p1532 Ns204p1533 Ns204p109 Ns204p1532 122895618 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 155304182) qz361 0 2 Ns204p1531 Ns204p106 Ns204p1532 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 155304182) qz362 0 2 Ns204p1533 Ns204p109 Ns204p1532 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1535 := nat_lit 2616346349183071448999482244401586842732645196306030314088719234370556663441227774359042652571400952002081 

noncomputable def Ns204p1536 := nat_lit 1915604305087702965627118830841027294652983881421088832824849746926192793394359227780506658371450401 

noncomputable def Ns204p1537 := nat_lit 15848441277993587606945866763394295694955899722036270315823898360698979943722365128527282712301304698025505 

noncomputable def Ns204p1538 := BSN.cos_dyadic_bound_f 187726457 134217728 4 3 134217728 67108864 Ns204p1535 Ns204p230 Ns204p1536 Ns204p1537 Ns204p233 Ns204p1536 22988350 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 187726457) qz363 0 3 Ns204p1535 Ns204p230 Ns204p1536 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 187726457) qz364 0 3 Ns204p1537 Ns204p233 Ns204p1536 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1539 := nat_lit 96718307608310593094614485080412886512519301795095301902979927793920 

noncomputable def Ns204p1540 := nat_lit 9711526963252988252492957859411752344611445989001535676642386176 

noncomputable def Ns204p1541 := nat_lit 253294129835253905647771996135975655171849752836505502497661437501696 

noncomputable def Ns204p1542 := BSN.sin_dyadic_bound_f 99634774 134217728 3 2 134217728 67108864 Ns204p1539 Ns204p106 Ns204p1540 Ns204p1541 Ns204p109 Ns204p1540 90732768 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 99634774) qz361 0 2 Ns204p1539 Ns204p106 Ns204p1540 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 99634774) qz362 0 2 Ns204p1541 Ns204p109 Ns204p1540 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1543 := nat_lit 108559879759628637809864657040362553446170639471553911464644446023841 

noncomputable def Ns204p1544 := nat_lit 39620870715252481208980539099150377737234631944724872896862515361 

noncomputable def Ns204p1545 := nat_lit 325600397537455408467176010042889359583037449150772284648139613040801 

noncomputable def Ns204p1546 := BSN.cos_dyadic_bound_f 118779229 134217728 3 2 134217728 67108864 Ns204p1543 Ns204p240 Ns204p1544 Ns204p1545 Ns204p243 Ns204p1544 85001355 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 118779229) qz363 0 2 Ns204p1543 Ns204p240 Ns204p1544 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 118779229) qz364 0 2 Ns204p1545 Ns204p243 Ns204p1544 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1547 := Ns204p1501 65059 BSN.abs_quadSignPos (BSN.cos_quad_nat3 95 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 90732768 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 24 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 85001355 134217728) qz193 rfl rfl (Ns204p1530 RS205to222.d9 RS205to222.d11 RS205to222.d13 RS205to222.d17 (Ns204p1534 rfl rfl) (Ns204p1538 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns204p1529 rfl) RS205to222.d19 RS205to222.d21 RS205to222.d23 RS205to222.d25 RS205to222.d17 (Ns204p1542 rfl rfl) (Ns204p1546 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns204p1548 := nat_lit 37783956371682531918473008925936218340557102888936365009147476030625 

noncomputable def Ns204p1549 := nat_lit 1482306963202999491712282915336153953295968807833885595875390625 

noncomputable def Ns204p1550 := nat_lit 98955581047894778739680822538446218071248980759620653494897686590625 

noncomputable def Ns204p1551 := BSN.sin_dyadic_bound_f 78771165 134217728 3 2 134217728 67108864 Ns204p1548 Ns204p106 Ns204p1549 Ns204p1550 Ns204p109 Ns204p1549 74326405 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 78771165) qz361 0 2 Ns204p1548 Ns204p106 Ns204p1549 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 78771165) qz362 0 2 Ns204p1550 Ns204p109 Ns204p1549 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1552 := nat_lit 17831978206981116725218466979220088319771761793027480620100984996096 

noncomputable def Ns204p1553 := nat_lit 1069668773617595692121824646263094742362990518578955310382940416 

noncomputable def Ns204p1554 := nat_lit 53493795283396114984271157288367738769830559398045283949682189107456 

noncomputable def Ns204p1555 := BSN.cos_dyadic_bound_f 75623394 134217728 3 2 134217728 67108864 Ns204p1552 Ns204p240 Ns204p1553 Ns204p1554 Ns204p243 Ns204p1553 113470859 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 75623394) qz363 0 2 Ns204p1552 Ns204p240 Ns204p1553 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 75623394) qz364 0 2 Ns204p1554 Ns204p243 Ns204p1553 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1556 := Ns204p1499 87317 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 33 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 74326405 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 82 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 113470859 134217728) qz193 rfl rfl (Ns204p1547 rfl rfl) (Ns204p1529 rfl) RS205to222.d27 RS205to222.d29 RS205to222.d31 RS205to222.d33 RS205to222.d17 (Ns204p1551 rfl rfl) (Ns204p1555 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns204p1557 := nat_lit 1632089189208729050581875009398618567843593785002956010669069186780510317245757561995632654415715532148736 

noncomputable def Ns204p1558 := nat_lit 466192452342686148729572453673784939242812155615823129330950283577031397062042030714254170391187456 

noncomputable def Ns204p1559 := nat_lit 9891963998439142110601652817460765451303965114214790977701971421707867627607766311494001882736790506967040 

noncomputable def Ns204p1560 := BSN.cos_dyadic_bound_f 166870834 134217728 4 3 134217728 67108864 Ns204p1557 Ns204p230 Ns204p1558 Ns204p1559 Ns204p233 Ns204p1558 43176234 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 166870834) qz363 0 3 Ns204p1557 Ns204p230 Ns204p1558 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 166870834) qz364 0 3 Ns204p1559 Ns204p233 Ns204p1558 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1561 := Ns204p1497 Bool.false 217994214 87317 Bool.true 166870834 7074237752028440 1 Bool.false 43176234 Bool.false Bool.false 233259316 97328 BSN.abs_quadSignPos qz735 (BSN.sfrac_eq_quadSignPos_mul Bool.false 43176234 134217728) qz193 rfl (Ns204p1556 rfl) (Ns204p1529 rfl) RS205to222.d35 RS205to222.d37 RS205to222.d17 (Ns204p1560 rfl rfl) rfl 

noncomputable def Ns204p1562 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz190) qz190 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz190) qz190 8) 233259316 134217728 97328 134217728 233259316 134217728 97328 134217728 62615070856708096 58314829 16777216 6083 4194304 (Ns204p1561 rfl rfl rfl rfl) 

noncomputable def Ns204p1563 := @Enclosure.Real.IsNear.mulLit_ff qz751 (Zeta.RiemannSiegel.correction qz192) 351225 1048576 1 8388608 25873253396045 35184372088832 1015610537503 21990232555520000 9087333424025905125 36893488147419103232 

noncomputable abbrev qz754 := (@HPow.hPow Real Real Real qz7 qz191 qz9)

noncomputable def Ns204p1564 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz754 1 1 0 1 351225 1048576 1 8388608 351225 1048576 1 8388608 

noncomputable def Ns204p1565 := @Enclosure.Real.IsNear.sqrt_image qz191 666420105483 8388608000 249579 8388608000 74768542 74768571 8388608 (@Enclosure.Real.IsNear.of_eq qz191 (@HMul.hMul Real Real Real qz5 qz190 qz3) Bool.false 666420105483 8388608000 249579 8388608000 (BSN.t_div_two_pi_mk qz190 499158 1000 qz193) (@Enclosure.Real.IsNear.mulLit_ff qz190 qz3 499158 1000 0 1 2670177 16777216 1 16777216 666420105483 8388608000 249579 8388608000 (Enclosure.Real.IsNear.const Bool.false 499158 1000) RS205to222.d40 rfl)) 

noncomputable abbrev qz903 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 499158 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz755 := qz903

noncomputable abbrev qz540 := qz755

noncomputable abbrev qz195 := qz540

noncomputable def Ns204p1566 := @Enclosure.Real.IsNear.sqrt_image qz195 149537113 16777216 29 16777216 25044040 25044046 8388608 (@Enclosure.Real.IsNear.recentre' qz195 Bool.false 149537113 16777216 29 16777216 149537113 16777216 29 16777216 (Ns204p1565 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns204p1567 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz195) 25044043 8388608 3 8388608 2809799 2809801 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz195) Bool.false 50088086 16777216 6 16777216 25044043 8388608 3 8388608 (Ns204p1566 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns204p1568 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz195)) Bool.false 5619600 16777216 2 16777216 351225 1048576 1 8388608 (Ns204p1567 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz196 := (@HMul.hMul Real Real Real qz342 qz340 qz533)

noncomputable abbrev qz756 := (@HMul.hMul Real Real Real qz844 qz902 qz902)

noncomputable abbrev qz541 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz756 qz750) qz640)

noncomputable abbrev qz197 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz541))

noncomputable def Ns204p1569 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz192) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz196)) qz197) Bool.false 25873253396045 

noncomputable def Ns204p1570 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz196)) qz197 4907771 4194304 65 

noncomputable def Ns204p1571 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz196)) Bool.false 19631084 16777216 260 16777216 4907771 4194304 65 

noncomputable def Ns204p1572 := @Enclosure.Real.IsNear.recentre' (Real.cos qz196) Bool.false 14338229 16777216 485257216 42949672960000 14338229 16777216 118471 10485760000 

noncomputable def Ns204p1573 := @Enclosure.Real.IsNear.cos_image qz196 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 48127267) qz359) Bool.false 48127267 8388608 183 16777216 Bool.false 14338229 16777216 1 

noncomputable def Ns204p1574 := nat_lit 782596186993869833339565963 

noncomputable def Ns204p1575 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz192 884279719003555 140737488355328 1 500000000000000 15319385 16777216 29 16777216 13546621463107275413675 2361183241434822606848 Ns204p1574 

noncomputable def Ns204p1576 := @Enclosure.Real.IsNear.subLit_ff_p qz195 qz1 149537113 16777216 29 16777216 8 1 0 1 15319385 15319385 16777216 29 

noncomputable def Ns204p1577 := @Ns204p1576 16777216 (@Enclosure.Real.IsNear.recentre' qz195 Bool.false 149537113 16777216 29 16777216 149537113 16777216 29 16777216 (Ns204p1565 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns204p1578 := @Enclosure.Real.IsNear.recentre' qz196 Bool.false 13546621463107275413675 2361183241434822606848 Ns204p1574 Ns204p521 48127267 8388608 183 16777216 (@Ns204p1575 Ns204p521 RS205to222.d39 (Ns204p1577 rfl rfl) rfl) 

noncomputable def Ns204p1579 := nat_lit 1238941424827424156155904 

noncomputable def Ns204p1580 := nat_lit 6482513751179133587445312905206780325138484971673239936284636493433109242216655477398465 

noncomputable def Ns204p1581 := nat_lit 2363783810158389835351898781735055885977107701969448762320980025751051339231953542081 

noncomputable def Ns204p1582 := nat_lit 16974185126919379145480487867990186951547307227626725487511242562759308217922960230308801 

noncomputable def Ns204p1583 := BSN.sin_dyadic_bound_f 35212833177 34359738368 3 2 16777216 5125001 Ns204p1580 Ns204p1161 Ns204p1581 Ns204p1582 Ns204p1164 Ns204p1581 14338229 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 35212833177) qz357 0 2 Ns204p1580 Ns204p1161 Ns204p1581 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 35212833177) qz358 0 2 Ns204p1582 Ns204p1164 Ns204p1581 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1584 := @Ns204p1573 2560000 (Ns204p1578 rfl) (Enclosure.sfrac_false_div 48127267 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 48127267) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns204p1579) qz360) 226375608064910080 72057594037927936 Bool.false 14338229 16777216 0 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q3 48127267 8388608 226375608064910080 72057594037927936 0 Ns204p1579 Ns204p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 14338229 16777216 Ns204p1579 Ns204p100 35212833177 34359738368 5125001 5120000 (Ns204p1583 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p1585 := @Enclosure.Real.IsNear.inv_image (Real.cos qz196) 14338229 16777216 118471 10485760000 9815412 9815672 8388608 (Ns204p1572 (Ns204p1584 rfl rfl) rfl) rfl 

noncomputable def Ns204p1586 := @Enclosure.Real.IsNear.recentre' qz197 Bool.false 5271895 8388608 

noncomputable abbrev qz198 := (@HMul.hMul Real Real Real qz342 qz340 qz541)

noncomputable def Ns204p1587 := @Enclosure.Real.IsNear.cos_image qz198 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7476145)) qz359) Bool.true 7476145 8388608 

noncomputable def Ns204p1588 := nat_lit 35305098046197584644085137805 

noncomputable def Ns204p1589 := nat_lit 37107592535547499629316636392046437 

noncomputable def Ns204p1590 := @Enclosure.Real.IsNear.recentre' qz198 Bool.true Ns204p1588 Ns204p533 Ns204p1589 

noncomputable abbrev qz199 := qz541

noncomputable def Ns204p1591 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz199 884279719003555 140737488355328 1 500000000000000 39925260398351 

noncomputable abbrev qz542 := (@HSub.hSub Real Real Real qz634 qz756 qz750)

noncomputable abbrev qz200 := qz542

noncomputable def Ns204p1592 := @Enclosure.Real.IsNear.subLit_tf qz200 qz27 22333074353935 281474976710656 1375064435 281474976710656 1 16 

noncomputable abbrev qz543 := qz756

noncomputable abbrev qz201 := qz543

noncomputable def Ns204p1593 := @Enclosure.Real.IsNear.subLit_ff_n qz201 qz192 234683556778225 281474976710656 888525171 281474976710656 15319385 16777216 29 16777216 

noncomputable def Ns204p1594 := @Enclosure.Real.IsNear.mulLit_ff qz192 qz192 15319385 16777216 29 16777216 15319385 16777216 29 16777216 234683556778225 281474976710656 

noncomputable def Ns204p1595 := nat_lit 25998171575628960678286683449939093834245696167457287690625 

noncomputable def Ns204p1596 := nat_lit 9759368744019289999433708364507963442435429557562890625 

noncomputable def Ns204p1597 := nat_lit 77974995989398843454861182933088265575852217643256737290625 

noncomputable def Ns204p1598 := BSN.cos_dyadic_bound_f 7476145 8388608 3 2 8388608 2560000 Ns204p1595 Ns204p1178 Ns204p1596 Ns204p1597 Ns204p1181 Ns204p1596 5271895 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 7476145) (BSN.cosEvenQ 8388608) 0 2 Ns204p1595 Ns204p1178 Ns204p1596 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 7476145) (BSN.cosOddQ 8388608) 0 2 Ns204p1597 Ns204p1181 Ns204p1596 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1599 := @Ns204p1586 334434304 10737418240000 5271895 8388608 81649 2621440000 (@Ns204p1587 129 4194304 Bool.false 5271895 8388608 1 2560000 (@Ns204p1590 Ns204p536 7476145 8388608 129 4194304 (@Ns204p1591 281474976710656 1375064435 281474976710656 Ns204p1588 Ns204p533 Ns204p1589 Ns204p536 RS205to222.d39 (@Ns204p1592 0 1 638804166373616 39925260398351 281474976710656 1375064435 281474976710656 (@Ns204p1593 374686812380027944960 22333074353935 281474976710656 1375064435 281474976710656 (@Ns204p1594 888525171 281474976710656 (Ns204p1577 rfl rfl) (Ns204p1577 rfl rfl) rfl) (Ns204p1577 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7476145 8388608) (BSN.cos_neg_of_bound 7476145 8388608 Bool.false 5271895 8388608 1 2560000 (Ns204p1598 rfl rfl)) rfl rfl) 

noncomputable def Ns204p1600 := @Ns204p1563 717458571814748757 46116860184273879040000 (Ns204p1564 qz29 (@Enclosure.Real.IsNear.of_eq qz754 (@Inv.inv Real Real.instInv (Real.sqrt qz195)) Bool.false 351225 1048576 1 8388608 (BSN.rpow_neg_quarter_mk qz191 (BSN.t_div_two_pi_nonneg qz190 499158 1000 qz193)) Ns204p1568) rfl) (@Ns204p1569 35184372088832 1015610537503 21990232555520000 (BSN.correction_mk qz192 (BSN.cos_two_pi_p_ne_zero_mk qz190 499158 1000 8 qz193 rfl rfl (@BSN.floor_sqrt_eq_dec qz190 499158 1000 8 qz193 rfl rfl rfl))) (@Ns204p1570 4194304 5271895 8388608 81649 2621440000 25873253396045 35184372088832 1015610537503 21990232555520000 (@Ns204p1571 4194304 (Ns204p1585 rfl rfl rfl rfl rfl) rfl) (Ns204p1599 rfl) rfl)) 

noncomputable def Ns204p1601 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz190) (hardyZApproximantRS₀ qz190) Bool.false 119148331690512275483 36893488147419103232 67600750889428828757 46116860184273879040000 (@Eq.refl Real (hardyZApproximantRS₀ qz190)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz190) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz190) qz190 8) (@HMul.hMul Real Real Real qz5 qz751 (Zeta.RiemannSiegel.correction qz192))) Bool.false 119148331690512275483 36893488147419103232 67600750889428828757 46116860184273879040000 (BSN.hardyZApproximantRS₀_eq qz190 8 (@BSN.floor_sqrt_eq_dec qz190 499158 1000 8 qz193 rfl rfl rfl)) (@Ns204p1496 119148331690512275483 36893488147419103232 67600750889428828757 46116860184273879040000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz190) qz190 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz190) qz190 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz190) qz190 8)) Bool.false 58314829 16777216 6083 4194304 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz190) qz190 8) (Ns204p1562 (Ns204p1561 rfl rfl rfl rfl) rfl rfl)) (Ns204p1600 rfl) rfl rfl)) 

theorem RS205to222.d56 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz190) Bool.false 119148331690512275483 36893488147419103232 67600750889428828757 46116860184273879040000 := Ns204p1601 

noncomputable def Ns204p1602 := nat_lit 4703074491837661545372844032 

noncomputable abbrev qz904 := (Enclosure.sfrac Bool.false 500593 1000)

noncomputable abbrev qz757 := qz904

noncomputable abbrev qz544 := qz757

noncomputable abbrev qz202 := qz544

noncomputable abbrev qz905 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 500593 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz758 := qz905

noncomputable abbrev qz545 := qz758

noncomputable abbrev qz203 := qz545

noncomputable abbrev qz906 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 500593 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz759 := qz906

noncomputable abbrev qz546 := qz759

noncomputable abbrev qz204 := qz546

noncomputable abbrev qz760 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz203 qz9))

noncomputable def Ns204p1603 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz202) qz202 8) (@HMul.hMul Real Real Real qz5 qz760 (Zeta.RiemannSiegel.correction qz204)) 46658133 67108864 97617 67108864 18780111345727045755 73786976294838206464 1113851367995377797 73786976294838206464000 Ns204p1602 

noncomputable def Ns204p1604 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz202) qz202 Real.cos BSN.quadSignPos 7 8 500593 1000 124 134217728 67108864 2251799813685248 Bool.false 113425788247 1835 279097919 53 47453128 8 

noncomputable def Ns204p1605 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz202) qz202 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 500593 1000 33 82 134217728 67108864 2251799813685248 Bool.false 113425788247 1835 

noncomputable def Ns204p1606 := Ns204p1605 240485871 53 54794152 8 261175631 53 50729528 8 Bool.true 18187060 65255 Bool.true 2407808 Bool.true 28949843 7074237752028440 1 Bool.false 2407678 Bool.true Bool.false 131107672 Bool.true Bool.true 68724028 

noncomputable def Ns204p1607 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz202) qz202 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 500593 1000 96 25 134217728 67108864 2251799813685248 Bool.false 113425788247 1835 

noncomputable def Ns204p1608 := Ns204p1607 186065264 53 67108856 8 216015088 53 60023992 8 Bool.true 73180913 38366 Bool.false 43262988 Bool.false 19429446 7074237752028440 1 Bool.false 127305315 Bool.false Bool.false 19361657 Bool.true Bool.true 18187060 

noncomputable def Ns204p1609 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz202) qz202 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 500593 1000 317 187 134217728 67108864 2251799813685248 Bool.false 113425788247 1835 

noncomputable def Ns204p1610 := Ns204p1609 93032624 53 94906264 8 147453232 53 77490640 16 Bool.true 134217712 1901 Bool.false 21605520 Bool.false 186762937 7074237752028440 1 Bool.false 21512331 Bool.true Bool.false 132065957 Bool.false Bool.true 73180913 

noncomputable def Ns204p1611 := nat_lit 2156125979993248728898643444045141919361939590663974398273 

noncomputable def Ns204p1612 := nat_lit 2551362743763468741688864687478851990778538406969344000 

noncomputable def Ns204p1613 := nat_lit 15089199375137256683243673372640000 

noncomputable def Ns204p1614 := nat_lit 45321306596752264214147215559315853120 

noncomputable abbrev qz547 := (@Eq.refl Real qz757)

noncomputable abbrev qz205 := qz547

noncomputable def Ns204p1615 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz202 500593 1000 1002374406596 16000000 1001186 4000 2000 Ns204p1613 Ns204p1614 qz205 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns204p1616 := nat_lit 689960313597839593247565902094445414195820669012471807447360 

noncomputable abbrev qz548 := (Real.log (Enclosure.sfrac Bool.false 1002374406596 16000000))

noncomputable abbrev qz549 := (Enclosure.sfrac Bool.false 500593 2000)

noncomputable abbrev qz206 := (@HSub.hSub Real Real Real qz345 (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 500593 4000) qz548) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 1001186)))))) qz549)

noncomputable abbrev qz550 := (@HSub.hSub Real Real Real qz12 qz206 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 500593 2000) (Real.log Real.pi)))

noncomputable def Ns204p1617 := @Enclosure.Real.IsNear.addLit_ft_p qz550 (Enclosure.sfrac Bool.true Ns204p1613 Ns204p1614) 15223757592861037866153 18014398509481984000 5598342966227673 409600000000000000000 Ns204p1613 Ns204p1614 0 1 Ns204p1616 

noncomputable def Ns204p1618 := nat_lit 1021649077868278761058511880192000 

noncomputable abbrev qz551 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 500593 2000) (Real.log Real.pi))

noncomputable def Ns204p1619 := @Enclosure.Real.IsNear.subLit_ff_p qz206 qz551 20385276975447640681641 18014398509481984000 155210313047 25000000000000000 19228158081273 67108864000 500593 67108864000 Ns204p1618 15223757592861037866153 18014398509481984000 

noncomputable def Ns204p1620 := nat_lit 40770553950895281363282000 

noncomputable abbrev qz207 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 500593 4000) qz548) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 1001186))))))

noncomputable def Ns204p1621 := @Enclosure.Real.IsNear.subLit_ff_p qz207 qz549 24894217871976198089897 18014398509481984000 155210313047 25000000000000000 500593 2000 0 1 Ns204p1620 20385276975447640681641 18014398509481984000 155210313047 25000000000000000 

noncomputable def Ns204p1622 := nat_lit 56056795165955973807616967577966739456 

noncomputable def Ns204p1623 := nat_lit 26705880805632730881589248 

noncomputable def Ns204p1624 := nat_lit 757288330838195541848096697458564605920147892764384176862831382055736008468309533315126643047624004447411120152938110021499361840250209706772408132005400791597372510440941158400 

noncomputable def Ns204p1625 := nat_lit 26322331364021621472031442103206889822391025297830709104989247960598683110806485042979095839257360674455078718532598224792709420062189107073888742565425331774119413921391575040 

noncomputable def Ns204p1626 := nat_lit 4404102158288036942463829014509290891751538310798678148180995631725215767931586840993018853766380722738618669431060703364715677608467557405668038181237117681515689410560 

noncomputable def Ns204p1627 := BSN.log_dyadic_bound 478086406596 1526662406596 8 7 Ns204p1624 67108864 20480000 Ns204p1625 Ns204p1626 43492296 2004748813192 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 478086406596) (BSN.artanhQ 1526662406596) 0 7 Ns204p1625 Ns204p1624 Ns204p1626 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns204p1628 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 500593 4000) qz548 500593 4000 0 1 49743579338551929 4503599627370496 2441407 50000000000000 24901287611823725793897 18014398509481984000 1222151254351 200000000000000000 (Enclosure.Real.IsNear.const Bool.false 500593 4000) (BSN.isNear_log_sfrac 1002374406596 16000000 49743579338551929 4503599627370496 2441407 50000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1002374406596) qz352)) Bool.false Ns204p1623 Ns204p89 1000000307200000 20480000000000000000000 49743579338551929 4503599627370496 2441407 50000000000000 (BSN.log_rat_reduce_isNear 1002374406596 16000000 15 2004748813192 1048576000000 43492296 67108864 24973259072661432 36028797018963968 20480000 1000000000000000 rfl rfl rfl rfl (Ns204p1627 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns204p1629 := BSN.arctan_dyadic_bound_f 1000 1001186 1 0 8388608 2560000 0 1 1 0 1 1 8378 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1001186) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1001186) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz552 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1001186)))

noncomputable def Ns204p1630 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz552 884279719003555 562949953421312 1 2000000000000000 8378 8388608 1 2560000 7413159530361209749504 883717480940963 562949953421312 781250001 2000000000000000 qz17 (Ns204p1629 rfl) rfl rfl 

noncomputable def Ns204p1631 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 500593 4000) qz548) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz552)) 24901287611823725793897 18014398509481984000 1222151254351 200000000000000000 883717480940963 2251799813685248 781250001 8000000000000000 Ns204p1622 24894217871976198089897 18014398509481984000 155210313047 25000000000000000 (Ns204p1628 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz552) 1 4 0 1 883717480940963 562949953421312 781250001 2000000000000000 883717480940963 2251799813685248 781250001 8000000000000000 qz355 Ns204p1630 rfl) 

noncomputable def Ns204p1632 := @Ns204p1617 Ns204p1611 Ns204p1612 5598342966227673 409600000000000000000 (@Ns204p1619 5598342966227673 409600000000000000000 (Ns204p1621 (Ns204p1631 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 500593 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz549 (Real.log Real.pi) 500593 2000 0 1 38410761 33554432 1 33554432 19228158081273 67108864000 500593 67108864000 (Enclosure.Real.IsNear.const Bool.false 500593 2000) RS205to222.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns204p1613 Ns204p1614) 

noncomputable def Ns204p1633 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz202) Bool.false Ns204p1611 Ns204p1612 5598342966227673 409600000000000000000 7089111765 8388608 231 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz202) (@HAdd.hAdd Real Real Real qz356 qz550 (Enclosure.sfrac Bool.true Ns204p1613 Ns204p1614)) Bool.false Ns204p1611 Ns204p1612 5598342966227673 409600000000000000000 Ns204p1615 (Ns204p1632 rfl rfl)) 

noncomputable def Ns204p1634 := nat_lit 1898436132380705449574400 

noncomputable def Ns204p1635 := nat_lit 856160884073088161054824874642797815958296640518708244583742635346264734670668413800156960743122477788284171647688262581785008700133376 

noncomputable def Ns204p1636 := nat_lit 608911581532529984279337955742442346156529892413367342172832144477800306808139214194059734430483126166060853306447704053676773376 

noncomputable def Ns204p1637 := nat_lit 4275491032454174854653756432556300192175424975406404051640258536352556868568123784660100240944498402046660267866661813017051301533454336 

noncomputable def Ns204p1638 := BSN.sin_dyadic_bound_f 53956800126 34359738368 4 3 16777216 5125001 Ns204p1635 Ns204p217 Ns204p1636 Ns204p1637 Ns204p220 Ns204p1636 16777214 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53956800126) qz357 0 3 Ns204p1635 Ns204p217 Ns204p1636 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53956800126) qz358 0 3 Ns204p1637 Ns204p220 Ns204p1636 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1639 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz202) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7089111765) qz359) Bool.false 7089111765 8388608 231 16777216 Bool.true 16777214 16777216 1 2560000 (Ns204p1633 rfl) (Enclosure.sfrac_false_div 7089111765 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7089111765) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns204p1634) qz360) 226375608064910080 72057594037927936 Bool.false 16777214 16777216 134 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q1 7089111765 8388608 226375608064910080 72057594037927936 134 Ns204p1634 Ns204p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777214 16777216 Ns204p1634 Ns204p100 53956800126 34359738368 5125001 5120000 (Ns204p1638 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p1640 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz202) Bool.false Ns204p1611 Ns204p1612 5598342966227673 409600000000000000000 113425788247 134217728 1835 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz202) (@HAdd.hAdd Real Real Real qz356 qz550 (Enclosure.sfrac Bool.true Ns204p1613 Ns204p1614)) Bool.false Ns204p1611 Ns204p1612 5598342966227673 409600000000000000000 Ns204p1615 (Ns204p1632 rfl rfl)) 

noncomputable def Ns204p1641 := Ns204p1610 38366 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 317 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 21512331 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 187 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 132065957 134217728) qz205 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz202) qz202 1) Bool.true 8388607 8388608 148471 10485760000 134217712 134217728 1901 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz202) qz202 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz202)) Bool.true 8388607 8388608 148471 10485760000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz202) qz202) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz202)) Bool.true 16777214 16777216 608137216 42949672960000 8388607 8388608 148471 10485760000 (Ns204p1639 rfl rfl) rfl)) rfl) (Ns204p1640 rfl) RS205to222.d7 

noncomputable def Ns204p1642 := nat_lit 217900834439832059376476160000 

noncomputable def Ns204p1643 := BSN.sin_dyadic_bound_f 21605520 134217728 2 1 134217728 67108864 Ns204p1642 Ns204p129 Ns204p1642 Ns204p1642 Ns204p130 Ns204p1642 21512331 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 21605520) qz361 0 1 Ns204p1642 Ns204p129 Ns204p1642 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 21605520) qz362 0 1 Ns204p1642 Ns204p130 Ns204p1642 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1644 := nat_lit 6657008680347126928008902659192759066473085645324593821567971880321463138230072157200600086819345051656481 

noncomputable def Ns204p1645 := nat_lit 1800894780553562368580807963947338897057703626954039516424857265319196859235968085455045325742907681 

noncomputable def Ns204p1646 := nat_lit 33259558006119828756207137325545851984833396781388104525859766831610257806050646161344292454755030482788641 

noncomputable def Ns204p1647 := BSN.sin_dyadic_bound_f 186762937 134217728 4 3 134217728 67108864 Ns204p1644 Ns204p256 Ns204p1645 Ns204p1646 Ns204p259 Ns204p1645 132065957 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 186762937) qz361 0 3 Ns204p1644 Ns204p256 Ns204p1645 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 186762937) qz362 0 3 Ns204p1646 Ns204p259 Ns204p1645 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1648 := nat_lit 3503208971810356060958982164736 

noncomputable def Ns204p1649 := BSN.cos_dyadic_bound_f 43262988 134217728 2 1 134217728 67108864 Ns204p1648 Ns204p125 Ns204p1648 Ns204p1648 Ns204p126 Ns204p1648 127305315 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 43262988) qz363 0 1 Ns204p1648 Ns204p125 Ns204p1648 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 43262988) qz364 0 1 Ns204p1648 Ns204p126 Ns204p1648 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1650 := nat_lit 142508795770891066499215351056 

noncomputable def Ns204p1651 := BSN.sin_dyadic_bound_f 19429446 134217728 2 1 134217728 67108864 Ns204p1650 Ns204p129 Ns204p1650 Ns204p1650 Ns204p130 Ns204p1650 19361657 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 19429446) qz361 0 1 Ns204p1650 Ns204p129 Ns204p1650 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 19429446) qz362 0 1 Ns204p1650 Ns204p130 Ns204p1650 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1652 := Ns204p1608 65255 BSN.abs_quadSignPos (BSN.cos_quad_nat0 96 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 127305315 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 25 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 19361657 134217728) qz205 rfl rfl (Ns204p1641 RS205to222.d9 RS205to222.d11 RS205to222.d13 RS205to222.d17 (Ns204p1643 rfl rfl) (Ns204p1647 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns204p1640 rfl) RS205to222.d19 RS205to222.d21 RS205to222.d23 RS205to222.d25 RS205to222.d17 (Ns204p1649 rfl rfl) (Ns204p1651 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns204p1653 := BSN.sin_dyadic_bound_f 2407808 134217728 1 0 134217728 67108864 0 1 1 0 1 1 2407678 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 2407808) qz361 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 2407808) qz362 0 0 rfl) rfl rfl 

noncomputable def Ns204p1654 := nat_lit 702400563423888383001998173201 

noncomputable def Ns204p1655 := BSN.cos_dyadic_bound_f 28949843 134217728 2 1 134217728 67108864 Ns204p1654 Ns204p125 Ns204p1654 Ns204p1654 Ns204p126 Ns204p1654 131107672 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 28949843) qz363 0 1 Ns204p1654 Ns204p125 Ns204p1654 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 28949843) qz364 0 1 Ns204p1654 Ns204p126 Ns204p1654 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1656 := Ns204p1606 87577 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 33 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 2407678 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 82 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 131107672 134217728) qz205 rfl rfl (Ns204p1652 rfl rfl) (Ns204p1640 rfl) RS205to222.d27 RS205to222.d29 RS205to222.d31 RS205to222.d33 RS205to222.d17 (Ns204p1653 rfl rfl) (Ns204p1655 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns204p1657 := nat_lit 953618504250041627077365650881934169036536320618778743283395448923282228131693980302722884268035182759936 

noncomputable def Ns204p1658 := nat_lit 93159389170320087214336899134676224855895345605549418015846081946590359126160476654627976648134656 

noncomputable def Ns204p1659 := nat_lit 5782080824636194918676648429960946354393760129836629363026671245690311661199685960618830078479923926077440 

noncomputable def Ns204p1660 := BSN.cos_dyadic_bound_f 145915766 134217728 4 3 134217728 67108864 Ns204p1657 Ns204p230 Ns204p1658 Ns204p1659 Ns204p233 Ns204p1658 62411783 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 145915766) qz363 0 3 Ns204p1657 Ns204p230 Ns204p1658 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 145915766) qz364 0 3 Ns204p1659 Ns204p233 Ns204p1658 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1661 := Ns204p1604 Bool.true 68724028 87577 Bool.true 145915766 7074237752028440 1 Bool.false 62411783 Bool.false Bool.true 46658133 97617 BSN.abs_quadSignPos qz735 (BSN.sfrac_eq_quadSignPos_mul Bool.false 62411783 134217728) qz205 rfl (Ns204p1656 rfl) (Ns204p1640 rfl) RS205to222.d35 RS205to222.d37 RS205to222.d17 (Ns204p1660 rfl rfl) rfl 

noncomputable def Ns204p1662 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz202) qz202 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz202) qz202 8) 46658133 134217728 97617 134217728 46658133 134217728 97617 134217728 12524697207963648 46658133 67108864 97617 67108864 (Ns204p1661 rfl rfl rfl rfl) 

noncomputable def Ns204p1663 := @Enclosure.Real.IsNear.mulLit_ff qz760 (Zeta.RiemannSiegel.correction qz204) 350973 1048576 1 8388608 53508706782935 70368744177664 985797327473 21990232555520000 18780111345727045755 73786976294838206464 

noncomputable abbrev qz761 := (@HPow.hPow Real Real Real qz7 qz203 qz9)

noncomputable def Ns204p1664 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz761 1 1 0 1 350973 1048576 1 8388608 350973 1048576 1 8388608 

noncomputable def Ns204p1665 := @Enclosure.Real.IsNear.sqrt_image qz203 1336671914961 16777216000 500593 16777216000 74875939 74875968 8388608 (@Enclosure.Real.IsNear.of_eq qz203 (@HMul.hMul Real Real Real qz5 qz202 qz3) Bool.false 1336671914961 16777216000 500593 16777216000 (BSN.t_div_two_pi_mk qz202 500593 1000 qz205) (@Enclosure.Real.IsNear.mulLit_ff qz202 qz3 500593 1000 0 1 2670177 16777216 1 16777216 1336671914961 16777216000 500593 16777216000 (Enclosure.Real.IsNear.const Bool.false 500593 1000) RS205to222.d40 rfl)) 

noncomputable abbrev qz907 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 500593 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz762 := qz907

noncomputable abbrev qz553 := qz762

noncomputable abbrev qz208 := qz553

noncomputable def Ns204p1666 := @Enclosure.Real.IsNear.sqrt_image qz208 149751907 16777216 29 16777216 25062021 25062026 8388608 (@Enclosure.Real.IsNear.recentre' qz208 Bool.false 149751907 16777216 29 16777216 149751907 16777216 29 16777216 (Ns204p1665 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns204p1667 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz208) 50124047 16777216 5 16777216 2807783 2807785 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz208) Bool.false 50124047 16777216 5 16777216 50124047 16777216 5 16777216 (Ns204p1666 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns204p1668 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz208)) Bool.false 5615568 16777216 2 16777216 350973 1048576 1 8388608 (Ns204p1667 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz209 := (@HMul.hMul Real Real Real qz342 qz340 qz546)

noncomputable abbrev qz763 := (@HMul.hMul Real Real Real qz844 qz906 qz906)

noncomputable abbrev qz554 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz763 qz759) qz640)

noncomputable abbrev qz210 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz554))

noncomputable def Ns204p1669 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz204) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz209)) qz210) Bool.false 53508706782935 

noncomputable def Ns204p1670 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz209)) qz210 9387583 8388608 119 

noncomputable def Ns204p1671 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz209)) Bool.false 18775166 16777216 238 16777216 9387583 8388608 119 

noncomputable def Ns204p1672 := @Enclosure.Real.IsNear.recentre' (Real.cos qz209) Bool.false 14991877 16777216 485257216 42949672960000 14991877 16777216 118471 10485760000 

noncomputable def Ns204p1673 := @Enclosure.Real.IsNear.cos_image qz209 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 97604125) qz369) Bool.false 97604125 16777216 183 16777216 Bool.false 14991877 16777216 1 

noncomputable def Ns204p1674 := nat_lit 782596186995714899750320011 

noncomputable def Ns204p1675 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz204 884279719003555 140737488355328 1 500000000000000 15534179 16777216 29 16777216 13736559441070925006345 2361183241434822606848 Ns204p1674 

noncomputable def Ns204p1676 := @Enclosure.Real.IsNear.subLit_ff_p qz208 qz1 149751907 16777216 29 16777216 8 1 0 1 15534179 15534179 16777216 29 

noncomputable def Ns204p1677 := @Ns204p1676 16777216 (@Enclosure.Real.IsNear.recentre' qz208 Bool.false 149751907 16777216 29 16777216 149751907 16777216 29 16777216 (Ns204p1665 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns204p1678 := @Enclosure.Real.IsNear.recentre' qz209 Bool.false 13736559441070925006345 2361183241434822606848 Ns204p1674 Ns204p521 97604125 16777216 183 16777216 (@Ns204p1675 Ns204p521 RS205to222.d39 (Ns204p1677 rfl rfl) rfl) 

noncomputable def Ns204p1679 := nat_lit 2672379410445330714460160 

noncomputable def Ns204p1680 := nat_lit 8771396024095885876171380440129699327166518287403403056788270599007844394687253266930625 

noncomputable def Ns204p1681 := nat_lit 4326597867606214152035231692092791452933917254589422173868060891850140311824187890625 

noncomputable def Ns204p1682 := nat_lit 22965698904655957709916986968076300384988512029549101322354446136909930330342709871090625 

noncomputable def Ns204p1683 := BSN.sin_dyadic_bound_f 37976795545 34359738368 3 2 16777216 5125001 Ns204p1680 Ns204p1161 Ns204p1681 Ns204p1682 Ns204p1164 Ns204p1681 14991877 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 37976795545) qz357 0 2 Ns204p1680 Ns204p1161 Ns204p1681 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 37976795545) qz358 0 2 Ns204p1682 Ns204p1164 Ns204p1681 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1684 := @Ns204p1673 2560000 (Ns204p1678 rfl) (Enclosure.sfrac_false_div 97604125 16777216) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 97604125) qz369) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns204p1679) qz371) 226375608064910080 72057594037927936 Bool.false 14991877 16777216 0 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q3 97604125 16777216 226375608064910080 72057594037927936 0 Ns204p1679 Ns204p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 14991877 16777216 Ns204p1679 Ns204p89 37976795545 34359738368 5125001 5120000 (Ns204p1683 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p1685 := @Enclosure.Real.IsNear.inv_image (Real.cos qz209) 14991877 16777216 118471 10485760000 9387464 9387702 8388608 (Ns204p1672 (Ns204p1684 rfl rfl) rfl) rfl 

noncomputable def Ns204p1686 := @Enclosure.Real.IsNear.recentre' qz210 Bool.false 5699945 8388608 

noncomputable abbrev qz211 := (@HMul.hMul Real Real Real qz342 qz340 qz554)

noncomputable def Ns204p1687 := @Enclosure.Real.IsNear.cos_image qz211 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 6909981)) qz359) Bool.true 6909981 8388608 

noncomputable def Ns204p1688 := nat_lit 32631464969964921627603968645 

noncomputable def Ns204p1689 := nat_lit 37443786466243319821006610129662017 

noncomputable def Ns204p1690 := @Enclosure.Real.IsNear.recentre' qz211 Bool.true Ns204p1688 Ns204p533 Ns204p1689 

noncomputable abbrev qz212 := qz554

noncomputable def Ns204p1691 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz212 884279719003555 140737488355328 1 500000000000000 36901745306039 

noncomputable abbrev qz555 := (@HSub.hSub Real Real Real qz634 qz763 qz759)

noncomputable abbrev qz213 := qz555

noncomputable def Ns204p1692 := @Enclosure.Real.IsNear.subLit_tf qz213 qz27 19309559261623 281474976710656 1387522487 281474976710656 1 16 

noncomputable abbrev qz556 := qz763

noncomputable abbrev qz214 := qz556

noncomputable def Ns204p1693 := @Enclosure.Real.IsNear.subLit_ff_n qz214 qz204 241310717204041 281474976710656 900983223 281474976710656 15534179 16777216 29 16777216 

noncomputable def Ns204p1694 := @Enclosure.Real.IsNear.mulLit_ff qz204 qz204 15534179 16777216 29 16777216 15534179 16777216 29 16777216 241310717204041 281474976710656 

noncomputable def Ns204p1695 := nat_lit 18971221739034765294746365187642167426573461952737211317921 

noncomputable def Ns204p1696 := nat_lit 5197743281887035406104277348708595505241818918051643041 

noncomputable def Ns204p1697 := nat_lit 56903269730540521813426887008229085088709902220375530667681 

noncomputable def Ns204p1698 := BSN.cos_dyadic_bound_f 6909981 8388608 3 2 8388608 2560000 Ns204p1695 Ns204p1178 Ns204p1696 Ns204p1697 Ns204p1181 Ns204p1696 5699945 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 6909981) (BSN.cosEvenQ 8388608) 0 2 Ns204p1695 Ns204p1178 Ns204p1696 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 6909981) (BSN.cosOddQ 8388608) 0 2 Ns204p1697 Ns204p1181 Ns204p1696 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1699 := @Ns204p1686 1350537216 42949672960000 5699945 8388608 329721 10485760000 (@Ns204p1687 521 16777216 Bool.false 5699945 8388608 1 2560000 (@Ns204p1690 Ns204p536 6909981 8388608 521 16777216 (@Ns204p1691 281474976710656 1387522487 281474976710656 Ns204p1688 Ns204p533 Ns204p1689 Ns204p536 RS205to222.d39 (@Ns204p1692 0 1 590427924896624 36901745306039 281474976710656 1387522487 281474976710656 (@Ns204p1693 323960646597049581568 19309559261623 281474976710656 1387522487 281474976710656 (@Ns204p1694 900983223 281474976710656 (Ns204p1677 rfl rfl) (Ns204p1677 rfl rfl) rfl) (Ns204p1677 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 6909981 8388608) (BSN.cos_neg_of_bound 6909981 8388608 Bool.false 5699945 8388608 1 2560000 (Ns204p1698 rfl rfl)) rfl rfl) 

noncomputable def Ns204p1700 := @Ns204p1663 1113851367995377797 73786976294838206464000 (Ns204p1664 qz29 (@Enclosure.Real.IsNear.of_eq qz761 (@Inv.inv Real Real.instInv (Real.sqrt qz208)) Bool.false 350973 1048576 1 8388608 (BSN.rpow_neg_quarter_mk qz203 (BSN.t_div_two_pi_nonneg qz202 500593 1000 qz205)) Ns204p1668) rfl) (@Ns204p1669 70368744177664 985797327473 21990232555520000 (BSN.correction_mk qz204 (BSN.cos_two_pi_p_ne_zero_mk qz202 500593 1000 8 qz205 rfl rfl (@BSN.floor_sqrt_eq_dec qz202 500593 1000 8 qz205 rfl rfl rfl))) (@Ns204p1670 8388608 5699945 8388608 329721 10485760000 53508706782935 70368744177664 985797327473 21990232555520000 (@Ns204p1671 8388608 (Ns204p1685 rfl rfl rfl rfl rfl) rfl) (Ns204p1699 rfl) rfl)) 

noncomputable def Ns204p1701 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz202) (hardyZApproximantRS₀ qz202) Bool.true 70081271109546147963 73786976294838206464 108444877936605169797 73786976294838206464000 (@Eq.refl Real (hardyZApproximantRS₀ qz202)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz202) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz202) qz202 8) (@HMul.hMul Real Real Real qz5 qz760 (Zeta.RiemannSiegel.correction qz204))) Bool.true 70081271109546147963 73786976294838206464 108444877936605169797 73786976294838206464000 (BSN.hardyZApproximantRS₀_eq qz202 8 (@BSN.floor_sqrt_eq_dec qz202 500593 1000 8 qz205 rfl rfl rfl)) (@Ns204p1603 70081271109546147963 73786976294838206464 108444877936605169797 73786976294838206464000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz202) qz202 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz202) qz202 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz202) qz202 8)) Bool.true 46658133 67108864 97617 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz202) qz202 8) (Ns204p1662 (Ns204p1661 rfl rfl rfl rfl) rfl rfl)) (Ns204p1700 rfl) rfl rfl)) 

theorem RS205to222.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz202) Bool.true 70081271109546147963 73786976294838206464 108444877936605169797 73786976294838206464000 := Ns204p1701 

noncomputable def Ns204p1702 := nat_lit 1778675245997541983908790272 

noncomputable abbrev qz908 := (Enclosure.sfrac Bool.false 502028 1000)

noncomputable abbrev qz764 := qz908

noncomputable abbrev qz557 := qz764

noncomputable abbrev qz215 := qz557

noncomputable abbrev qz909 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 502028 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz765 := qz909

noncomputable abbrev qz558 := qz765

noncomputable abbrev qz216 := qz558

noncomputable abbrev qz910 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 502028 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz766 := qz910

noncomputable abbrev qz559 := qz766

noncomputable abbrev qz217 := qz559

noncomputable abbrev qz767 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz216 qz9))

noncomputable def Ns204p1703 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz215) qz215 8) (@HMul.hMul Real Real Real qz5 qz767 (Zeta.RiemannSiegel.correction qz217)) 41756923 67108864 48945 33554432 19407895826531086875 73786976294838206464 85053196783411527 5764607523034234880000 Ns204p1702 

noncomputable def Ns204p1704 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz215) qz215 Real.cos BSN.quadSignPos 7 8 502028 1000 124 134217728 67108864 2251799813685248 Bool.false 113847524867 1840 279097919 53 47453128 8 

noncomputable def Ns204p1705 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz215) qz215 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 502028 1000 32 81 134217728 67108864 2251799813685248 Bool.false 113847524867 1840 

noncomputable def Ns204p1706 := Ns204p1705 240485871 53 54794152 8 261175631 53 50729528 8 Bool.false 34839403 65436 Bool.true 136597127 Bool.true 192828967 7074237752028440 1 Bool.false 70504662 Bool.false Bool.false 133012575 Bool.true Bool.false 13348784 

noncomputable def Ns204p1707 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz215) qz215 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 502028 1000 96 25 134217728 67108864 2251799813685248 Bool.false 113847524867 1840 

noncomputable def Ns204p1708 := Ns204p1707 186065264 53 67108856 8 216015088 53 60023992 8 Bool.false 78195466 38470 Bool.false 197995954 Bool.false 131184415 7074237752028440 1 Bool.false 12813217 Bool.false Bool.false 111272715 Bool.true Bool.false 34839403 

noncomputable def Ns204p1709 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz215) qz215 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 502028 1000 318 188 134217728 67108864 2251799813685248 Bool.false 113847524867 1840 

noncomputable def Ns204p1710 := Ns204p1709 93032624 53 94906264 8 147453232 53 77490640 16 Bool.false 134217720 1901 Bool.false 99011611 Bool.false 186075455 7074237752028440 1 Bool.false 99324005 Bool.true Bool.false 24613175 Bool.false Bool.false 78195466 

noncomputable def Ns204p1711 := nat_lit 16797126464798141442183113838922539070069900719918427 

noncomputable def Ns204p1712 := nat_lit 19802557443978725400102342852952674167414587392000 

noncomputable def Ns204p1713 := nat_lit 15306716163838527387513617776640000 

noncomputable def Ns204p1714 := nat_lit 46106421956742940005153284531442155520 

noncomputable abbrev qz768 := (@Eq.refl Real qz908)

noncomputable abbrev qz560 := qz768

noncomputable abbrev qz218 := qz560

noncomputable def Ns204p1715 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz215 502028 1000 1008129451136 16000000 1004056 4000 2000 Ns204p1713 Ns204p1714 qz218 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns204p1716 := nat_lit 176130636799521759608786007767620403279376162172891845099520 

noncomputable abbrev qz561 := (Real.log (Enclosure.sfrac Bool.false 1008129451136 16000000))

noncomputable abbrev qz562 := (Enclosure.sfrac Bool.false 502028 2000)

noncomputable abbrev qz219 := (@HSub.hSub Real Real Real qz345 (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 502028 4000) qz561) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 1004056)))))) qz562)

noncomputable abbrev qz563 := (@HSub.hSub Real Real Real qz12 qz219 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 502028 2000) (Real.log Real.pi)))

noncomputable def Ns204p1717 := @Enclosure.Real.IsNear.addLit_ft_p qz563 (Enclosure.sfrac Bool.true Ns204p1713 Ns204p1714) 3820090526653507323451 4503599627370496000 1403569128338427 102400000000000000000 Ns204p1713 Ns204p1714 0 1 Ns204p1716 

noncomputable def Ns204p1718 := nat_lit 64090483905219649523119292416000 

noncomputable abbrev qz564 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 502028 2000) (Real.log Real.pi))

noncomputable def Ns204p1719 := @Enclosure.Real.IsNear.subLit_ff_p qz219 qz564 5114169375439440725563 4503599627370496000 1245185923421 200000000000000000 4820819380827 16777216000 125507 16777216000 Ns204p1718 3820090526653507323451 4503599627370496000 

noncomputable def Ns204p1720 := nat_lit 10228338750878881451126000 

noncomputable abbrev qz220 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 502028 4000) qz561) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 1004056))))))

noncomputable def Ns204p1721 := @Enclosure.Real.IsNear.subLit_ff_p qz220 qz562 6244635932304218408507 4503599627370496000 1245185923421 200000000000000000 502028 2000 0 1 Ns204p1720 5114169375439440725563 4503599627370496000 1245185923421 200000000000000000 

noncomputable def Ns204p1722 := nat_lit 14061670028894843954726821265183604736 

noncomputable def Ns204p1723 := nat_lit 26719722997389822800166912 

noncomputable def Ns204p1724 := nat_lit 798248942890587264532574520260898650763130647895172161216347029429776904336297380952356774372089311304932448414605090865133423429913858648305113258911720925205119316307371622400 

noncomputable def Ns204p1725 := nat_lit 28234971189436235728393118294022647405478785986225851018855188147221753814115420833684102625207328575778461822904691640558365910378827772425694692354707372315306177756334653440 

noncomputable def Ns204p1726 := nat_lit 5207279083748719983538769827384286511682752477681240563803176036452622719573726509612360109946718912755793384170338828287418158714511015140120878198806857443323318108160 

noncomputable def Ns204p1727 := BSN.log_dyadic_bound 483841451136 1532417451136 8 7 Ns204p1724 67108864 20480000 Ns204p1725 Ns204p1726 43876494 2016258902272 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 483841451136) (BSN.artanhQ 1532417451136) 0 7 Ns204p1725 Ns204p1724 Ns204p1726 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns204p1728 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 502028 4000) qz561 502028 4000 0 1 49769362429883001 4503599627370496 2441407 50000000000000 6246403370487325806507 4503599627370496000 306413668349 50000000000000000 (Enclosure.Real.IsNear.const Bool.false 502028 4000) (BSN.isNear_log_sfrac 1008129451136 16000000 49769362429883001 4503599627370496 2441407 50000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1008129451136) qz352)) Bool.false Ns204p1723 Ns204p89 1000000307200000 20480000000000000000000 49769362429883001 4503599627370496 2441407 50000000000000 (BSN.log_rat_reduce_isNear 1008129451136 16000000 15 2016258902272 1048576000000 43876494 67108864 24973259072661432 36028797018963968 20480000 1000000000000000 rfl rfl rfl rfl (Ns204p1727 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns204p1729 := BSN.arctan_dyadic_bound_f 1000 1004056 1 0 8388608 2560000 0 1 1 0 1 1 8354 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1004056) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1004056) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz565 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1004056)))

noncomputable def Ns204p1730 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz565 884279719003555 562949953421312 1 2000000000000000 8354 8388608 1 2560000 7413173041160091860992 883719091553699 562949953421312 781250001 2000000000000000 qz17 (Ns204p1729 rfl) rfl rfl 

noncomputable def Ns204p1731 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 502028 4000) qz561) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz565)) 6246403370487325806507 4503599627370496000 306413668349 50000000000000000 883719091553699 2251799813685248 781250001 8000000000000000 Ns204p1722 6244635932304218408507 4503599627370496000 1245185923421 200000000000000000 (Ns204p1728 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz565) 1 4 0 1 883719091553699 562949953421312 781250001 2000000000000000 883719091553699 2251799813685248 781250001 8000000000000000 qz355 Ns204p1730 rfl) 

noncomputable def Ns204p1732 := @Ns204p1717 Ns204p1711 Ns204p1712 1403569128338427 102400000000000000000 (@Ns204p1719 1403569128338427 102400000000000000000 (Ns204p1721 (Ns204p1731 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 502028 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz562 (Real.log Real.pi) 502028 2000 0 1 38410761 33554432 1 33554432 4820819380827 16777216000 125507 16777216000 (Enclosure.Real.IsNear.const Bool.false 502028 2000) RS205to222.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns204p1713 Ns204p1714) 

noncomputable def Ns204p1733 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz215) Bool.false Ns204p1711 Ns204p1712 1403569128338427 102400000000000000000 222358447 262144 231 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz215) (@HAdd.hAdd Real Real Real qz356 qz563 (Enclosure.sfrac Bool.true Ns204p1713 Ns204p1714)) Bool.false Ns204p1711 Ns204p1712 1403569128338427 102400000000000000000 Ns204p1715 (Ns204p1732 rfl rfl)) 

noncomputable def Ns204p1734 := nat_lit 857450998883088968400996453937745426534933657569017439862970763803489054265022593365766193617336036997649916539622280588571342729056256 

noncomputable def Ns204p1735 := nat_lit 611662823346239254107041447757571077789218824824098836784634501334403135282888632674584081253150442474457261094578305496602054656 

noncomputable def Ns204p1736 := nat_lit 4281925609891355290752657728733650308053129812049905632958834872589418355760451959742418979413798632731544476632241289584448994272546816 

noncomputable def Ns204p1737 := BSN.sin_dyadic_bound_f 53977074234 34359738368 4 3 16777216 5125001 Ns204p1734 Ns204p217 Ns204p1735 Ns204p1736 Ns204p220 Ns204p1735 16777215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 53977074234) qz357 0 3 Ns204p1734 Ns204p217 Ns204p1735 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 53977074234) qz358 0 3 Ns204p1736 Ns204p220 Ns204p1735 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1738 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz215) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 222358447) (@Nat.cast Real Real.instNatCast 262144)) Bool.false 222358447 262144 231 16777216 Bool.false 16777215 16777216 1 2560000 (Ns204p1733 rfl) (Enclosure.sfrac_false_div 222358447 262144) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 222358447) (@Nat.cast Real Real.instNatCast 262144)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 59348420754192155541504) (@Nat.cast Real Real.instNatCast 37778931862957161709568)) 226375608064910080 72057594037927936 Bool.false 16777215 16777216 134 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q3 222358447 262144 226375608064910080 72057594037927936 134 59348420754192155541504 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16777215 16777216 59348420754192155541504 37778931862957161709568 53977074234 34359738368 5125001 5120000 (Ns204p1737 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p1739 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz215) Bool.false Ns204p1711 Ns204p1712 1403569128338427 102400000000000000000 113847524867 134217728 1840 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz215) (@HAdd.hAdd Real Real Real qz356 qz563 (Enclosure.sfrac Bool.true Ns204p1713 Ns204p1714)) Bool.false Ns204p1711 Ns204p1712 1403569128338427 102400000000000000000 Ns204p1715 (Ns204p1732 rfl rfl)) 

noncomputable def Ns204p1740 := Ns204p1710 38470 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 318 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 99324005 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat0 188 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 24613175 134217728) qz218 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz215) qz215 1) Bool.false 16777215 16777216 148471 10485760000 134217720 134217728 1901 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz215) qz215 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz215)) Bool.false 16777215 16777216 148471 10485760000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz215) qz215) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz215)) Bool.false 16777215 16777216 608137216 42949672960000 16777215 16777216 148471 10485760000 (Ns204p1738 rfl rfl) rfl)) rfl) (Ns204p1739 rfl) RS205to222.d7 

noncomputable def Ns204p1741 := nat_lit 52404655507698590405356713388439416050147472122689767059194489460961 

noncomputable def Ns204p1742 := nat_lit 9236108267643150375456086819808562305184989748705553224380307681 

noncomputable def Ns204p1743 := nat_lit 157195494306560484915319227991678631025832046388571890071134707767521 

noncomputable def Ns204p1744 := BSN.cos_dyadic_bound_f 99011611 134217728 3 2 134217728 67108864 Ns204p1741 Ns204p240 Ns204p1742 Ns204p1743 Ns204p243 Ns204p1742 99324005 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 99011611) qz363 0 2 Ns204p1741 Ns204p240 Ns204p1742 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 99011611) qz364 0 2 Ns204p1743 Ns204p243 Ns204p1742 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1745 := nat_lit 2525313886228252241824369604658902740604859131704018945022571740815903338430417044353851980393490216890625 

noncomputable def Ns204p1746 := nat_lit 1722935722164356235639676264002219712870844441573163539716241844349472477879095408418809980712890625 

noncomputable def Ns204p1747 := nat_lit 15297819584430319413410663645404803915375726150867804112529478459526245846183856766823906907384037570490625 

noncomputable def Ns204p1748 := BSN.cos_dyadic_bound_f 186075455 134217728 4 3 134217728 67108864 Ns204p1745 Ns204p230 Ns204p1746 Ns204p1747 Ns204p233 Ns204p1746 24613175 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 186075455) qz363 0 3 Ns204p1745 Ns204p230 Ns204p1746 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 186075455) qz364 0 3 Ns204p1747 Ns204p233 Ns204p1746 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1749 := nat_lit 3239313913700156914228435819010218575437483812438741895965094185689275975830124677505094563158086480695296 

noncomputable def Ns204p1750 := nat_lit 3629742259518860277551941209265354452101393743947546584350754631654438834078612676714858193995042816 

noncomputable def Ns204p1751 := nat_lit 19614992434678585929527807755788021779501872409809434393611680646150336884117900483023401752040141440552960 

noncomputable def Ns204p1752 := BSN.cos_dyadic_bound_f 197995954 134217728 4 3 134217728 67108864 Ns204p1749 Ns204p230 Ns204p1750 Ns204p1751 Ns204p233 Ns204p1750 12813217 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 197995954) qz363 0 3 Ns204p1749 Ns204p230 Ns204p1750 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 197995954) qz364 0 3 Ns204p1751 Ns204p233 Ns204p1750 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1753 := nat_lit 290724302447876654009886010607941573171591757561965636834341361530625 

noncomputable def Ns204p1754 := nat_lit 87711783853678384578374320135178375596090792718136898909312890625 

noncomputable def Ns204p1755 := nat_lit 761278782570580519308003136026294783793679979950271112920278964090625 

noncomputable def Ns204p1756 := BSN.sin_dyadic_bound_f 131184415 134217728 3 2 134217728 67108864 Ns204p1753 Ns204p106 Ns204p1754 Ns204p1755 Ns204p109 Ns204p1754 111272715 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 131184415) qz361 0 2 Ns204p1753 Ns204p106 Ns204p1754 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 131184415) qz362 0 2 Ns204p1755 Ns204p109 Ns204p1754 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1757 := Ns204p1708 65436 BSN.abs_quadSignPos (BSN.cos_quad_nat0 96 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 12813217 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 25 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 111272715 134217728) qz218 rfl rfl (Ns204p1740 RS205to222.d9 RS205to222.d11 RS205to222.d13 RS205to222.d17 (Ns204p1744 rfl rfl) (Ns204p1748 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns204p1739 rfl) RS205to222.d19 RS205to222.d21 RS205to222.d23 RS205to222.d25 RS205to222.d17 (Ns204p1752 rfl rfl) (Ns204p1756 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns204p1758 := nat_lit 189929453391151330842345661207956263660866502904788931049648153748161 

noncomputable def Ns204p1759 := nat_lit 121208344797152520439112793999608432867466869767808255566375346881 

noncomputable def Ns204p1760 := nat_lit 569545943483859687486158758035869574116864574974831176637811710550721 

noncomputable def Ns204p1761 := BSN.cos_dyadic_bound_f 136597127 134217728 3 2 134217728 67108864 Ns204p1758 Ns204p240 Ns204p1759 Ns204p1760 Ns204p243 Ns204p1759 70504662 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 136597127) qz363 0 2 Ns204p1758 Ns204p240 Ns204p1759 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 136597127) qz364 0 2 Ns204p1760 Ns204p243 Ns204p1759 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1762 := nat_lit 7566217365363819620502533567607610292498838346588426163934312232013707038030734821177433992832613972339361 

noncomputable def Ns204p1763 := nat_lit 2642818245928101155796027451490085696841270874906693182511108294202239156395238648137549542003468961 

noncomputable def Ns204p1764 := nat_lit 37798174335340163642836650106253668432543294508399705432703949307973861450431558429861114087933747765865121 

noncomputable def Ns204p1765 := BSN.sin_dyadic_bound_f 192828967 134217728 4 3 134217728 67108864 Ns204p1762 Ns204p256 Ns204p1763 Ns204p1764 Ns204p259 Ns204p1763 133012575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 192828967) qz361 0 3 Ns204p1762 Ns204p256 Ns204p1763 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 192828967) qz362 0 3 Ns204p1764 Ns204p259 Ns204p1763 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1766 := Ns204p1706 87822 BSN.abs_quadSignPos (BSN.cos_quad_nat0 32 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 70504662 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 81 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133012575 134217728) qz218 rfl rfl (Ns204p1757 rfl rfl) (Ns204p1739 rfl) RS205to222.d27 RS205to222.d29 RS205to222.d31 RS205to222.d33 RS205to222.d17 (Ns204p1761 rfl rfl) (Ns204p1765 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns204p1767 := nat_lit 131823669717882179344364933481353300451391613702625592371851468800000 

noncomputable def Ns204p1768 := nat_lit 58412285984129831529359177280937337465065235544135819289600000000 

noncomputable def Ns204p1769 := nat_lit 395354184581678278370036082089498026679244710636788505476975206400000 

noncomputable def Ns204p1770 := BSN.cos_dyadic_bound_f 124684660 134217728 3 2 134217728 67108864 Ns204p1767 Ns204p240 Ns204p1768 Ns204p1769 Ns204p243 Ns204p1768 80350361 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 124684660) qz363 0 2 Ns204p1767 Ns204p240 Ns204p1768 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 124684660) qz364 0 2 Ns204p1769 Ns204p243 Ns204p1768 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1771 := Ns204p1704 Bool.false 13348784 87822 Bool.true 124684660 7074237752028440 1 Bool.false 80350361 Bool.false Bool.false 41756923 97890 BSN.abs_quadSignPos qz735 (BSN.sfrac_eq_quadSignPos_mul Bool.false 80350361 134217728) qz218 rfl (Ns204p1766 rfl) (Ns204p1739 rfl) RS205to222.d35 RS205to222.d37 RS205to222.d17 (Ns204p1770 rfl rfl) rfl 

noncomputable def Ns204p1772 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz215) qz215 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz215) qz215 8) 41756923 134217728 97890 134217728 41756923 134217728 97890 134217728 11209038666661888 41756923 67108864 48945 33554432 (Ns204p1771 rfl rfl rfl rfl) 

noncomputable def Ns204p1773 := @Enclosure.Real.IsNear.mulLit_ff qz767 (Zeta.RiemannSiegel.correction qz217) 2805775 8388608 1 8388608 6917124796725 8796093022208 3855488798931 87960930222080000 19407895826531086875 73786976294838206464 

noncomputable abbrev qz769 := (@HPow.hPow Real Real Real qz7 qz216 qz9)

noncomputable def Ns204p1774 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz769 1 1 0 1 2805775 8388608 1 8388608 2805775 8388608 1 8388608 

noncomputable def Ns204p1775 := @Enclosure.Real.IsNear.sqrt_image qz216 335125904739 4194304000 125507 4194304000 74983182 74983211 8388608 (@Enclosure.Real.IsNear.of_eq qz216 (@HMul.hMul Real Real Real qz5 qz215 qz3) Bool.false 335125904739 4194304000 125507 4194304000 (BSN.t_div_two_pi_mk qz215 502028 1000 qz218) (@Enclosure.Real.IsNear.mulLit_ff qz215 qz3 502028 1000 0 1 2670177 16777216 1 16777216 335125904739 4194304000 125507 4194304000 (Enclosure.Real.IsNear.const Bool.false 502028 1000) RS205to222.d40 rfl)) 

noncomputable abbrev qz911 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 502028 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz770 := qz911

noncomputable abbrev qz566 := qz770

noncomputable abbrev qz221 := qz566

noncomputable def Ns204p1776 := @Enclosure.Real.IsNear.sqrt_image qz221 149966393 16777216 29 16777216 25079962 25079968 8388608 (@Enclosure.Real.IsNear.recentre' qz221 Bool.false 149966393 16777216 29 16777216 149966393 16777216 29 16777216 (Ns204p1775 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns204p1777 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz221) 25079965 8388608 3 8388608 2805774 2805776 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz221) Bool.false 50159930 16777216 6 16777216 25079965 8388608 3 8388608 (Ns204p1776 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns204p1778 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz221)) Bool.false 5611550 16777216 2 16777216 2805775 8388608 1 8388608 (Ns204p1777 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz222 := (@HMul.hMul Real Real Real qz342 qz340 qz559)

noncomputable abbrev qz771 := (@HMul.hMul Real Real Real qz844 qz910 qz910)

noncomputable abbrev qz567 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz771 qz766) qz640)

noncomputable abbrev qz223 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz567))

noncomputable def Ns204p1779 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz217) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz222)) qz223) Bool.false 6917124796725 

noncomputable def Ns204p1780 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz222)) qz223 2262975 2097152 111 

noncomputable def Ns204p1781 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz222)) Bool.false 18103800 16777216 222 16777216 2262975 2097152 111 

noncomputable def Ns204p1782 := @Enclosure.Real.IsNear.recentre' (Real.cos qz222) Bool.false 15547839 16777216 485257216 42949672960000 15547839 16777216 118471 10485760000 

noncomputable def Ns204p1783 := @Enclosure.Real.IsNear.cos_image qz222 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24737945) qz385) Bool.false 24737945 4194304 183 16777216 Bool.false 15547839 16777216 1 

noncomputable def Ns204p1784 := nat_lit 782596186997557320461219723 

noncomputable def Ns204p1785 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz217 884279719003555 140737488355328 1 500000000000000 15748665 16777216 29 16777216 13926225060881121504075 2361183241434822606848 Ns204p1784 

noncomputable def Ns204p1786 := @Enclosure.Real.IsNear.subLit_ff_p qz221 qz1 149966393 16777216 29 16777216 8 1 0 1 15748665 15748665 16777216 29 

noncomputable def Ns204p1787 := @Ns204p1786 16777216 (@Enclosure.Real.IsNear.recentre' qz221 Bool.false 149966393 16777216 29 16777216 149966393 16777216 29 16777216 (Ns204p1775 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns204p1788 := @Enclosure.Real.IsNear.recentre' qz222 Bool.false 13926225060881121504075 2361183241434822606848 Ns204p1784 Ns204p521 24737945 4194304 183 16777216 (@Ns204p1785 Ns204p521 RS205to222.d39 (Ns204p1787 rfl rfl) rfl) 

noncomputable def Ns204p1789 := nat_lit 11614812168596205001123755823911269002978042356120740336702314286317350866660851423730625 

noncomputable def Ns204p1790 := nat_lit 7583936508099398790162859370387436847420911852570086914056382477238739249008187890625 

noncomputable def Ns204p1791 := nat_lit 30407467401500756928711477766501267729094286599221587407788065178248960977708597615090625 

noncomputable def Ns204p1792 := BSN.sin_dyadic_bound_f 40736792985 34359738368 3 2 16777216 5125001 Ns204p1789 Ns204p1161 Ns204p1790 Ns204p1791 Ns204p1164 Ns204p1790 15547839 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 40736792985) qz357 0 2 Ns204p1789 Ns204p1161 Ns204p1790 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 40736792985) qz358 0 2 Ns204p1791 Ns204p1164 Ns204p1790 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1793 := @Ns204p1783 2560000 (Ns204p1788 rfl) (Enclosure.sfrac_false_div 24737945 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24737945) qz385) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 716649241057924564910080) qz386) 226375608064910080 72057594037927936 Bool.false 15547839 16777216 0 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q3 24737945 4194304 226375608064910080 72057594037927936 0 716649241057924564910080 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 15547839 16777216 716649241057924564910080 604462909807314587353088 40736792985 34359738368 5125001 5120000 (Ns204p1792 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p1794 := @Enclosure.Real.IsNear.inv_image (Real.cos qz222) 15547839 16777216 118471 10485760000 9051789 9052011 8388608 (Ns204p1782 (Ns204p1793 rfl rfl) rfl) rfl 

noncomputable def Ns204p1795 := @Enclosure.Real.IsNear.recentre' qz223 Bool.false 6113302 8388608 

noncomputable abbrev qz224 := (@HMul.hMul Real Real Real qz342 qz340 qz567)

noncomputable def Ns204p1796 := @Enclosure.Real.IsNear.cos_image qz224 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 1581847)) qz372) Bool.true 1581847 2097152 

noncomputable def Ns204p1797 := nat_lit 29880246044608780624629744205 

noncomputable def Ns204p1798 := nat_lit 37779498317687279177297650883328677 

noncomputable def Ns204p1799 := @Enclosure.Real.IsNear.recentre' qz224 Bool.true Ns204p1797 Ns204p533 Ns204p1798 

noncomputable abbrev qz225 := qz567

noncomputable def Ns204p1800 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz225 884279719003555 140737488355328 1 500000000000000 33790491178831 

noncomputable abbrev qz568 := (@HSub.hSub Real Real Real qz634 qz771 qz766)

noncomputable abbrev qz226 := qz568

noncomputable def Ns204p1801 := @Enclosure.Real.IsNear.subLit_tf qz226 qz27 16198305134415 281474976710656 1399962675 281474976710656 1 16 

noncomputable abbrev qz569 := qz771

noncomputable abbrev qz227 := qz569

noncomputable def Ns204p1802 := @Enclosure.Real.IsNear.subLit_ff_n qz227 qz217 248020449282225 281474976710656 913423411 281474976710656 15748665 16777216 29 16777216 

noncomputable def Ns204p1803 := @Enclosure.Real.IsNear.mulLit_ff qz217 qz217 15748665 16777216 29 16777216 15748665 16777216 29 16777216 248020449282225 281474976710656 

noncomputable def Ns204p1804 := nat_lit 203502846647714249105044398939349537341794197193586241 

noncomputable def Ns204p1805 := nat_lit 15085502980398593449464978548510856026246963233994833920 

noncomputable def Ns204p1806 := nat_lit 39202683973948477103512658715116084058293520528961 

noncomputable def Ns204p1807 := nat_lit 610430134575194850360926171500618379857266004539700801 

noncomputable def Ns204p1808 := nat_lit 678847634117936705225924034682988521181113345529767526400 

noncomputable def Ns204p1809 := BSN.cos_dyadic_bound_f 1581847 2097152 3 2 8388608 2560000 Ns204p1804 Ns204p1805 Ns204p1806 Ns204p1807 Ns204p1808 Ns204p1806 6113302 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1581847) (BSN.cosEvenQ 2097152) 0 2 Ns204p1804 Ns204p1805 Ns204p1806 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1581847) (BSN.cosOddQ 2097152) 0 2 Ns204p1807 Ns204p1808 Ns204p1806 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1810 := @Ns204p1795 1360777216 42949672960000 3056651 4194304 332221 10485760000 (@Ns204p1796 525 16777216 Bool.false 6113302 8388608 1 2560000 (@Ns204p1799 Ns204p536 1581847 2097152 525 16777216 (@Ns204p1800 281474976710656 1399962675 281474976710656 Ns204p1797 Ns204p533 Ns204p1798 Ns204p536 RS205to222.d39 (@Ns204p1801 0 1 540647858861296 33790491178831 281474976710656 1399962675 281474976710656 (@Ns204p1802 271762464073989488640 16198305134415 281474976710656 1399962675 281474976710656 (@Ns204p1803 913423411 281474976710656 (Ns204p1787 rfl rfl) (Ns204p1787 rfl rfl) rfl) (Ns204p1787 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 1581847 2097152) (BSN.cos_neg_of_bound 1581847 2097152 Bool.false 6113302 8388608 1 2560000 (Ns204p1809 rfl rfl)) rfl rfl) 

noncomputable def Ns204p1811 := @Ns204p1773 85053196783411527 5764607523034234880000 (Ns204p1774 qz29 (@Enclosure.Real.IsNear.of_eq qz769 (@Inv.inv Real Real.instInv (Real.sqrt qz221)) Bool.false 2805775 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz216 (BSN.t_div_two_pi_nonneg qz215 502028 1000 qz218)) Ns204p1778) rfl) (@Ns204p1779 8796093022208 3855488798931 87960930222080000 (BSN.correction_mk qz217 (BSN.cos_two_pi_p_ne_zero_mk qz215 502028 1000 8 qz218 rfl rfl (@BSN.floor_sqrt_eq_dec qz215 502028 1000 8 qz218 rfl rfl rfl))) (@Ns204p1780 8388608 3056651 4194304 332221 10485760000 6917124796725 8796093022208 3855488798931 87960930222080000 (@Ns204p1781 8388608 (Ns204p1794 rfl rfl rfl rfl rfl) rfl) (Ns204p1810 rfl) rfl)) 

noncomputable def Ns204p1812 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz215) (hardyZApproximantRS₀ qz215) Bool.false 26504326552116006373 73786976294838206464 8493740168892211527 5764607523034234880000 (@Eq.refl Real (hardyZApproximantRS₀ qz215)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz215) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz215) qz215 8) (@HMul.hMul Real Real Real qz5 qz767 (Zeta.RiemannSiegel.correction qz217))) Bool.false 26504326552116006373 73786976294838206464 8493740168892211527 5764607523034234880000 (BSN.hardyZApproximantRS₀_eq qz215 8 (@BSN.floor_sqrt_eq_dec qz215 502028 1000 8 qz218 rfl rfl rfl)) (@Ns204p1703 26504326552116006373 73786976294838206464 8493740168892211527 5764607523034234880000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz215) qz215 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz215) qz215 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz215) qz215 8)) Bool.false 41756923 67108864 48945 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz215) qz215 8) (Ns204p1772 (Ns204p1771 rfl rfl rfl rfl) rfl rfl)) (Ns204p1811 rfl) rfl rfl)) 

theorem RS205to222.d58 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz215) Bool.false 26504326552116006373 73786976294838206464 8493740168892211527 5764607523034234880000 := Ns204p1812 

noncomputable def Ns204p1813 := nat_lit 63411437540055437656165711872 

noncomputable abbrev qz912 := (Enclosure.sfrac Bool.false 503462 1000)

noncomputable abbrev qz772 := qz912

noncomputable abbrev qz570 := qz772

noncomputable abbrev qz228 := qz570

noncomputable abbrev qz913 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 503462 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz773 := qz913

noncomputable abbrev qz571 := qz773

noncomputable abbrev qz229 := qz571

noncomputable abbrev qz914 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 503462 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz774 := qz914

noncomputable abbrev qz572 := qz774

noncomputable abbrev qz230 := qz572

noncomputable abbrev qz775 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz229 qz9))

noncomputable def Ns204p1814 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz228) qz228 8) (@HMul.hMul Real Real Real qz5 qz775 (Zeta.RiemannSiegel.correction qz230)) 196604487 67108864 49083 33554432 80228374200226848375 295147905179352825856 2680970953175277273 184467440737095516160000 Ns204p1813 

noncomputable def Ns204p1815 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz228) qz228 Real.cos BSN.quadSignPos 7 8 503462 1000 124 134217728 67108864 2251799813685248 Bool.false 114269242376 1846 279097919 53 47453128 8 

noncomputable def Ns204p1816 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz228) qz228 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 503462 1000 32 81 134217728 67108864 2251799813685248 Bool.false 114269242376 1846 

noncomputable def Ns204p1817 := Ns204p1816 240485871 53 54794152 8 261175631 53 50729528 8 Bool.true 235303366 65619 Bool.true 59736357 Bool.true 145637313 7074237752028440 1 Bool.false 121142276 Bool.false Bool.false 118694367 Bool.true Bool.true 230709494 

noncomputable def Ns204p1818 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz228) qz228 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 503462 1000 97 26 134217728 67108864 2251799813685248 Bool.false 114269242376 1846 

noncomputable def Ns204p1819 := Ns204p1818 186065264 53 67108856 8 216015088 53 60023992 8 Bool.true 118516994 38575 Bool.false 142067161 Bool.false 32307573 7074237752028440 1 Bool.false 116985886 Bool.true Bool.false 130348085 Bool.true Bool.true 235303366 

noncomputable def Ns204p1820 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz228) qz228 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 503462 1000 319 189 134217728 67108864 2251799813685248 Bool.false 114269242376 1846 

noncomputable def Ns204p1821 := Ns204p1820 93032624 53 94906264 8 147453232 53 77490640 16 Bool.true 134217704 1901 Bool.false 176491623 Bool.false 185516315 7074237752028440 1 Bool.false 129849381 Bool.false Bool.false 131837935 Bool.true Bool.true 118516994 

noncomputable def Ns204p1822 := nat_lit 17561970202856685428899826209098793466389880991758086831 

noncomputable def Ns204p1823 := nat_lit 20627840797833155332634334752811001759592840429568000 

noncomputable def Ns204p1824 := nat_lit 15526580026153222523333621519360000 

noncomputable def Ns204p1825 := nat_lit 46902279786611769242504885261976145920 

noncomputable abbrev qz776 := (@Eq.refl Real qz912)

noncomputable abbrev qz573 := qz776

noncomputable abbrev qz231 := qz573

noncomputable def Ns204p1826 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz228 503462 1000 1013896941776 16000000 1006924 4000 2000 Ns204p1824 Ns204p1825 qz231 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns204p1827 := nat_lit 359669149754504917583868440762343290191664762711205618298880 

noncomputable abbrev qz574 := (Real.log (Enclosure.sfrac Bool.false 1013896941776 16000000))

noncomputable abbrev qz575 := (Enclosure.sfrac Bool.false 503462 2000)

noncomputable abbrev qz232 := (@HSub.hSub Real Real Real qz345 (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 503462 4000) qz574) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 1006924)))))) qz575)

noncomputable abbrev qz576 := (@HSub.hSub Real Real Real qz12 qz232 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 503462 2000) (Real.log Real.pi)))

noncomputable def Ns204p1828 := @Enclosure.Real.IsNear.addLit_ft_p qz576 (Enclosure.sfrac Bool.true Ns204p1824 Ns204p1825) 7668482027779220334939 9007199254740992000 2815099478481291 204800000000000000000 Ns204p1824 Ns204p1825 0 1 Ns204p1827 

noncomputable def Ns204p1829 := nat_lit 51462311748867991948345579929600 

noncomputable abbrev qz577 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 503462 2000) (Real.log Real.pi))

noncomputable def Ns204p1830 := @Enclosure.Real.IsNear.subLit_ff_p qz232 qz577 2052806515244916072927 1801439850948198400 1248686901059 200000000000000000 9669179277291 33554432000 251731 33554432000 Ns204p1829 7668482027779220334939 9007199254740992000 

noncomputable def Ns204p1831 := nat_lit 20528065152449160729270000 

noncomputable abbrev qz233 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 503462 4000) qz574) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 1006924))))))

noncomputable def Ns204p1832 := @Enclosure.Real.IsNear.subLit_ff_p qz233 qz575 12531423851819785021787 9007199254740992000 1248686901059 200000000000000000 503462 2000 0 1 Ns204p1831 2052806515244916072927 1801439850948198400 1248686901059 200000000000000000 

noncomputable def Ns204p1833 := nat_lit 28218257894738664753371971572440498176 

noncomputable def Ns204p1834 := nat_lit 26733516045867780851892224 

noncomputable def Ns204p1835 := nat_lit 841354228158073325412948371393589980038725830331821805398189271831185822201580271350793354629316491795977402753970781788136113433719399755925277259529773506648536912018957926400 

noncomputable def Ns204p1836 := nat_lit 30277510974620380518334607981508820518216807865391217143726783907090060391868093042681689383933979648773049432671120425254810763441071572338563631863325166348234387261059235840 

noncomputable def Ns204p1837 := nat_lit 6146934943919284531515676493771979803626723716649995001288822037287491887268008883409627604844805277404256810464648628907233132842473525906398192329602105747984623861760 

noncomputable def Ns204p1838 := BSN.log_dyadic_bound 489608941776 1538184941776 8 7 Ns204p1835 67108864 20480000 Ns204p1836 Ns204p1837 44259328 2027793883552 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 489608941776) (BSN.artanhQ 1538184941776) 0 7 Ns204p1836 Ns204p1835 Ns204p1837 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns204p1839 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 503462 4000) qz574 503462 4000 0 1 49795053984723577 4503599627370496 2441407 50000000000000 12534958734628450761787 9007199254740992000 614577825517 100000000000000000 (Enclosure.Real.IsNear.const Bool.false 503462 4000) (BSN.isNear_log_sfrac 1013896941776 16000000 49795053984723577 4503599627370496 2441407 50000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1013896941776) qz352)) Bool.false Ns204p1834 Ns204p89 1000000307200000 20480000000000000000000 49795053984723577 4503599627370496 2441407 50000000000000 (BSN.log_rat_reduce_isNear 1013896941776 16000000 15 2027793883552 1048576000000 44259328 67108864 24973259072661432 36028797018963968 20480000 1000000000000000 rfl rfl rfl rfl (Ns204p1838 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns204p1840 := BSN.arctan_dyadic_bound_f 1000 1006924 1 0 8388608 2560000 0 1 1 0 1 1 8330 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1006924) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1006924) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz578 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1006924)))

noncomputable def Ns204p1841 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz578 884279719003555 562949953421312 1 2000000000000000 8330 8388608 1 2560000 7413186551958973972480 883720702166435 562949953421312 781250001 2000000000000000 qz17 (Ns204p1840 rfl) rfl rfl 

noncomputable def Ns204p1842 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 503462 4000) qz574) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz578)) 12534958734628450761787 9007199254740992000 614577825517 100000000000000000 883720702166435 2251799813685248 781250001 8000000000000000 Ns204p1833 12531423851819785021787 9007199254740992000 1248686901059 200000000000000000 (Ns204p1839 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz578) 1 4 0 1 883720702166435 562949953421312 781250001 2000000000000000 883720702166435 2251799813685248 781250001 8000000000000000 qz355 Ns204p1841 rfl) 

noncomputable def Ns204p1843 := @Ns204p1828 Ns204p1822 Ns204p1823 2815099478481291 204800000000000000000 (@Ns204p1830 2815099478481291 204800000000000000000 (Ns204p1832 (Ns204p1842 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 503462 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz575 (Real.log Real.pi) 503462 2000 0 1 38410761 33554432 1 33554432 9669179277291 33554432000 251731 33554432000 (Enclosure.Real.IsNear.const Bool.false 503462 2000) RS205to222.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns204p1824 Ns204p1825) 

noncomputable def Ns204p1844 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz228) Bool.false Ns204p1822 Ns204p1823 2815099478481291 204800000000000000000 14283655297 16777216 231 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz228) (@HAdd.hAdd Real Real Real qz356 qz576 (Enclosure.sfrac Bool.true Ns204p1824 Ns204p1825)) Bool.false Ns204p1822 Ns204p1823 2815099478481291 204800000000000000000 Ns204p1826 (Ns204p1843 rfl rfl)) 

noncomputable def Ns204p1845 := BSN.cos_dyadic_bound_f 20304852 34359738368 1 0 16777216 5125001 0 1 1 0 1 1 16777213 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 20304852) qz642 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 20304852) qz643 0 0 rfl) rfl rfl 

noncomputable def Ns204p1846 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz228) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 14283655297) qz369) Bool.false 14283655297 16777216 231 16777216 Bool.true 16777213 16777216 1 2560000 (Ns204p1844 rfl) (Enclosure.sfrac_false_div 14283655297 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 14283655297) qz369) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1428826954533357748224) qz371) 226375608064910080 72057594037927936 Bool.false 16777213 16777216 135 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q2 14283655297 16777216 226375608064910080 72057594037927936 135 1428826954533357748224 Ns204p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777213 16777216 1428826954533357748224 Ns204p89 20304852 34359738368 5125001 5120000 (Ns204p1845 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p1847 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz228) Bool.false Ns204p1822 Ns204p1823 2815099478481291 204800000000000000000 114269242376 134217728 1846 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz228) (@HAdd.hAdd Real Real Real qz356 qz576 (Enclosure.sfrac Bool.true Ns204p1824 Ns204p1825)) Bool.false Ns204p1822 Ns204p1823 2815099478481291 204800000000000000000 Ns204p1826 (Ns204p1843 rfl rfl)) 

noncomputable def Ns204p1848 := Ns204p1821 38575 BSN.abs_quadSignPos (BSN.cos_quad_nat3 319 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 129849381 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 189 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 131837935 134217728) qz231 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz228) qz228 1) Bool.true 16777213 16777216 148471 10485760000 134217704 134217728 1901 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz228) qz228 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz228)) Bool.true 16777213 16777216 148471 10485760000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz228) qz228) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz228)) Bool.true 16777213 16777216 608137216 42949672960000 16777213 16777216 148471 10485760000 (Ns204p1846 rfl rfl) rfl)) rfl) (Ns204p1847 rfl) RS205to222.d7 

noncomputable def Ns204p1849 := nat_lit 5307668387134876031510509816316727992645165889154322733453180005974412873787442829982283592281315495356321 

noncomputable def Ns204p1850 := nat_lit 913459216983460951292766495259753178490897067449987997419273461332610196379535737639238884701218721 

noncomputable def Ns204p1851 := nat_lit 26522133774867348900298010898706933821226640780484498481711158669826231345396664983589477320889485863397281 

noncomputable def Ns204p1852 := BSN.sin_dyadic_bound_f 176491623 134217728 4 3 134217728 67108864 Ns204p1849 Ns204p256 Ns204p1850 Ns204p1851 Ns204p259 Ns204p1850 129849381 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 176491623) qz361 0 3 Ns204p1849 Ns204p256 Ns204p1850 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 176491623) qz362 0 3 Ns204p1851 Ns204p259 Ns204p1850 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1853 := nat_lit 6480828943628396604855144197343011046393657879951393084686534424736301023227843029665211532201632844540625 

noncomputable def Ns204p1854 := nat_lit 1661825081506681537763073637996908708814023205996201827254498804954891199317605837424399531494140625 

noncomputable def Ns204p1855 := nat_lit 32379989028107999622262718949323665097000530454897920569340242104703825702245588877416171213108854246140625 

noncomputable def Ns204p1856 := BSN.sin_dyadic_bound_f 185516315 134217728 4 3 134217728 67108864 Ns204p1853 Ns204p256 Ns204p1854 Ns204p1855 Ns204p259 Ns204p1854 131837935 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 185516315) qz361 0 3 Ns204p1853 Ns204p256 Ns204p1854 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 185516315) qz362 0 3 Ns204p1855 Ns204p259 Ns204p1854 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1857 := nat_lit 399922984141949251060858356567180003322676721423622369156659457166785 

noncomputable def Ns204p1858 := nat_lit 165939437874620300410023953660843983968192438275496254524241350081 

noncomputable def Ns204p1859 := nat_lit 1047148675567593891339679466512877689871061958828469687188687901822401 

noncomputable def Ns204p1860 := BSN.sin_dyadic_bound_f 142067161 134217728 3 2 134217728 67108864 Ns204p1857 Ns204p106 Ns204p1858 Ns204p1859 Ns204p109 Ns204p1858 116985886 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 142067161) qz361 0 2 Ns204p1857 Ns204p106 Ns204p1858 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 142067161) qz362 0 2 Ns204p1859 Ns204p109 Ns204p1858 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1861 := nat_lit 1089475171058229117684232808241 

noncomputable def Ns204p1862 := BSN.cos_dyadic_bound_f 32307573 134217728 2 1 134217728 67108864 Ns204p1861 Ns204p125 Ns204p1861 Ns204p1861 Ns204p126 Ns204p1861 130348085 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 32307573) qz363 0 1 Ns204p1861 Ns204p125 Ns204p1861 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 32307573) qz364 0 1 Ns204p1861 Ns204p126 Ns204p1861 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1863 := Ns204p1819 65619 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 97 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 116985886 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 26 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 130348085 134217728) qz231 rfl rfl (Ns204p1848 RS205to222.d9 RS205to222.d11 RS205to222.d13 RS205to222.d17 (Ns204p1852 rfl rfl) (Ns204p1856 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns204p1847 rfl) RS205to222.d19 RS205to222.d21 RS205to222.d23 RS205to222.d25 RS205to222.d17 (Ns204p1860 rfl rfl) (Ns204p1862 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns204p1864 := nat_lit 6942468086140711615407907094027638682868571490024326926955627117281 

noncomputable def Ns204p1865 := nat_lit 162147355583382645298563026718286424540531632854367999195839201 

noncomputable def Ns204p1866 := nat_lit 20827079963710968080933124156029479475756633406807272044868489673441 

noncomputable def Ns204p1867 := BSN.cos_dyadic_bound_f 59736357 134217728 3 2 134217728 67108864 Ns204p1864 Ns204p240 Ns204p1865 Ns204p1866 Ns204p243 Ns204p1865 121142276 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 59736357) qz363 0 2 Ns204p1864 Ns204p240 Ns204p1865 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 59736357) qz364 0 2 Ns204p1866 Ns204p243 Ns204p1865 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1868 := nat_lit 441683316684163490013831231333187973822045335943655930565954194619905 

noncomputable def Ns204p1869 := nat_lit 202386370024900880875387496723663195048864582953788927950451883521 

noncomputable def Ns204p1870 := nat_lit 1156461965764197396229093073735082571980039622908602255122722159050241 

noncomputable def Ns204p1871 := BSN.sin_dyadic_bound_f 145637313 134217728 3 2 134217728 67108864 Ns204p1868 Ns204p106 Ns204p1869 Ns204p1870 Ns204p109 Ns204p1869 118694367 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 145637313) qz361 0 2 Ns204p1868 Ns204p106 Ns204p1869 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 145637313) qz362 0 2 Ns204p1870 Ns204p109 Ns204p1869 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1872 := Ns204p1817 88069 BSN.abs_quadSignPos (BSN.cos_quad_nat0 32 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 121142276 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 81 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 118694367 134217728) qz231 rfl rfl (Ns204p1863 rfl rfl) (Ns204p1847 rfl) RS205to222.d27 RS205to222.d29 RS205to222.d31 RS205to222.d33 RS205to222.d17 (Ns204p1867 rfl rfl) (Ns204p1871 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns204p1873 := nat_lit 61837174208840611168210679792014249733858124855823294156424024920321 

noncomputable def Ns204p1874 := nat_lit 12859408620078527101438004274771786263645426176224219175596560641 

noncomputable def Ns204p1875 := nat_lit 185485803809281676450429163367493205629047083715117434030920881639681 

noncomputable def Ns204p1876 := BSN.cos_dyadic_bound_f 103193567 134217728 3 2 134217728 67108864 Ns204p1873 Ns204p240 Ns204p1874 Ns204p1875 Ns204p243 Ns204p1874 96463538 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 103193567) qz363 0 2 Ns204p1873 Ns204p240 Ns204p1874 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 103193567) qz364 0 2 Ns204p1875 Ns204p243 Ns204p1874 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1877 := Ns204p1815 Bool.true 230709494 88069 Bool.true 103193567 7074237752028440 1 Bool.false 96463538 Bool.false Bool.true 196604487 98166 BSN.abs_quadSignPos qz735 (BSN.sfrac_eq_quadSignPos_mul Bool.false 96463538 134217728) qz231 rfl (Ns204p1872 rfl) (Ns204p1847 rfl) RS205to222.d35 RS205to222.d37 RS205to222.d17 (Ns204p1876 rfl rfl) rfl 

noncomputable def Ns204p1878 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz228) qz228 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz228) qz228 8) 196604487 134217728 98166 134217728 196604487 134217728 98166 134217728 52775615119491072 196604487 67108864 49083 33554432 (Ns204p1877 rfl rfl rfl rfl) 

noncomputable def Ns204p1879 := @Enclosure.Real.IsNear.mulLit_ff qz775 (Zeta.RiemannSiegel.correction qz230) 2803775 8388608 1 8388608 28614412426185 35184372088832 1899643156521 43980465111040000 80228374200226848375 295147905179352825856 

noncomputable abbrev qz777 := (@HPow.hPow Real Real Real qz7 qz229 qz9)

noncomputable def Ns204p1880 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz777 1 1 0 1 2803775 8388608 1 8388608 2803775 8388608 1 8388608 

noncomputable def Ns204p1881 := @Enclosure.Real.IsNear.sqrt_image qz229 672166326387 8388608000 251731 8388608000 75090197 75090226 8388608 (@Enclosure.Real.IsNear.of_eq qz229 (@HMul.hMul Real Real Real qz5 qz228 qz3) Bool.false 672166326387 8388608000 251731 8388608000 (BSN.t_div_two_pi_mk qz228 503462 1000 qz231) (@Enclosure.Real.IsNear.mulLit_ff qz228 qz3 503462 1000 0 1 2670177 16777216 1 16777216 672166326387 8388608000 251731 8388608000 (Enclosure.Real.IsNear.const Bool.false 503462 1000) RS205to222.d40 rfl)) 

noncomputable abbrev qz915 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 503462 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz778 := qz915

noncomputable abbrev qz579 := qz778

noncomputable abbrev qz234 := qz579

noncomputable def Ns204p1882 := @Enclosure.Real.IsNear.sqrt_image qz234 150180423 16777216 29 16777216 25097853 25097858 8388608 (@Enclosure.Real.IsNear.recentre' qz234 Bool.false 150180423 16777216 29 16777216 150180423 16777216 29 16777216 (Ns204p1881 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns204p1883 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz234) 50195711 16777216 5 16777216 2803774 2803776 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz234) Bool.false 50195711 16777216 5 16777216 50195711 16777216 5 16777216 (Ns204p1882 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns204p1884 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz234)) Bool.false 5607550 16777216 2 16777216 2803775 8388608 1 8388608 (Ns204p1883 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz235 := (@HMul.hMul Real Real Real qz342 qz340 qz572)

noncomputable abbrev qz779 := (@HMul.hMul Real Real Real qz844 qz914 qz914)

noncomputable abbrev qz580 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz779 qz774) qz640)

noncomputable abbrev qz236 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz580))

noncomputable def Ns204p1885 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz230) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz235)) qz236) Bool.false 28614412426185 

noncomputable def Ns204p1886 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz235)) qz236 17589245 16777216 209 

noncomputable def Ns204p1887 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz235)) Bool.false 17589245 16777216 209 16777216 17589245 16777216 209 

noncomputable def Ns204p1888 := @Enclosure.Real.IsNear.recentre' (Real.cos qz235) Bool.false 16002675 16777216 485257216 42949672960000 16002675 16777216 118471 10485760000 

noncomputable def Ns204p1889 := @Enclosure.Real.IsNear.cos_image qz235 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50148285) qz359) Bool.false 50148285 8388608 183 16777216 Bool.false 16002675 16777216 1 

noncomputable def Ns204p1890 := nat_lit 782596186999395824161945483 

noncomputable def Ns204p1891 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz230 884279719003555 140737488355328 1 500000000000000 15962695 16777216 29 16777216 14115487449139452380725 2361183241434822606848 Ns204p1890 

noncomputable def Ns204p1892 := @Enclosure.Real.IsNear.subLit_ff_p qz234 qz1 150180423 16777216 29 16777216 8 1 0 1 15962695 15962695 16777216 29 

noncomputable def Ns204p1893 := @Ns204p1892 16777216 (@Enclosure.Real.IsNear.recentre' qz234 Bool.false 150180423 16777216 29 16777216 150180423 16777216 29 16777216 (Ns204p1881 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns204p1894 := @Enclosure.Real.IsNear.recentre' qz235 Bool.false 14115487449139452380725 2361183241434822606848 Ns204p1890 Ns204p521 50148285 8388608 183 16777216 (@Ns204p1891 Ns204p521 RS205to222.d39 (Ns204p1893 rfl rfl) rfl) 

noncomputable def Ns204p1895 := nat_lit 1530200814002114238873600 

noncomputable def Ns204p1896 := nat_lit 15091908184458458176085668287314636877656498457555823293553595560411867444739731065330625 

noncomputable def Ns204p1897 := nat_lit 12799381684098162570673387602074207526443267089142973941648483945907292977456187890625 

noncomputable def Ns204p1898 := nat_lit 39505703388950279150348040982087357391200397337359020001496747969928183880926271343090625 

noncomputable def Ns204p1899 := BSN.sin_dyadic_bound_f 43490922905 34359738368 3 2 16777216 5125001 Ns204p1896 Ns204p1161 Ns204p1897 Ns204p1898 Ns204p1164 Ns204p1897 16002675 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 43490922905) qz357 0 2 Ns204p1896 Ns204p1161 Ns204p1897 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 43490922905) qz358 0 2 Ns204p1898 Ns204p1164 Ns204p1897 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1900 := @Ns204p1889 2560000 (Ns204p1894 rfl) (Enclosure.sfrac_false_div 50148285 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50148285) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns204p1895) qz360) 226375608064910080 72057594037927936 Bool.false 16002675 16777216 0 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q3 50148285 8388608 226375608064910080 72057594037927936 0 Ns204p1895 Ns204p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16002675 16777216 Ns204p1895 Ns204p100 43490922905 34359738368 5125001 5120000 (Ns204p1899 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p1901 := @Enclosure.Real.IsNear.inv_image (Real.cos qz235) 16002675 16777216 118471 10485760000 8794518 8794727 8388608 (Ns204p1888 (Ns204p1900 rfl rfl) rfl) rfl 

noncomputable def Ns204p1902 := @Enclosure.Real.IsNear.recentre' qz236 Bool.false 6507252 8388608 

noncomputable abbrev qz237 := (@HMul.hMul Real Real Real qz342 qz340 qz580)

noncomputable def Ns204p1903 := @Enclosure.Real.IsNear.cos_image qz237 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 11457719)) qz369) Bool.true 11457719 16777216 

noncomputable def Ns204p1904 := nat_lit 27053774284574958113092406605 

noncomputable def Ns204p1905 := nat_lit 38114496441408089127115128691385817 

noncomputable def Ns204p1906 := @Enclosure.Real.IsNear.recentre' qz237 Bool.true Ns204p1904 Ns204p533 Ns204p1905 

noncomputable abbrev qz238 := qz580

noncomputable def Ns204p1907 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz238 884279719003555 140737488355328 1 500000000000000 30594136338511 

noncomputable abbrev qz581 := (@HSub.hSub Real Real Real qz634 qz779 qz774)

noncomputable abbrev qz239 := qz581

noncomputable def Ns204p1908 := @Enclosure.Real.IsNear.subLit_tf qz239 qz27 13001950294095 281474976710656 1412376415 281474976710656 1 16 

noncomputable abbrev qz582 := qz779

noncomputable abbrev qz240 := qz582

noncomputable def Ns204p1909 := @Enclosure.Real.IsNear.subLit_ff_n qz240 qz230 254807631663025 281474976710656 925837151 281474976710656 15962695 16777216 29 16777216 

noncomputable def Ns204p1910 := @Enclosure.Real.IsNear.mulLit_ff qz230 qz230 15962695 16777216 29 16777216 15962695 16777216 29 16777216 254807631663025 281474976710656 

noncomputable def Ns204p1911 := nat_lit 2294234268249705540949764331254412021351676326963328599859521 

noncomputable def Ns204p1912 := nat_lit 297019755291205838015000854105374819316462788747132805441 

noncomputable def Ns204p1913 := nat_lit 6882108765238534211173262992055025314416396055312491533967681 

noncomputable def Ns204p1914 := BSN.cos_dyadic_bound_f 11457719 16777216 3 2 8388608 2560000 Ns204p1911 Ns204p754 Ns204p1912 Ns204p1913 Ns204p757 Ns204p1912 6507252 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 11457719) (BSN.cosEvenQ 16777216) 0 2 Ns204p1911 Ns204p754 Ns204p1912 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 11457719) (BSN.cosOddQ 16777216) 0 2 Ns204p1913 Ns204p757 Ns204p1912 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1915 := @Ns204p1902 686788608 21474836480000 1626813 2097152 167673 5242880000 (@Ns204p1903 265 8388608 Bool.false 6507252 8388608 1 2560000 (@Ns204p1906 Ns204p536 11457719 16777216 265 8388608 (@Ns204p1907 281474976710656 1412376415 281474976710656 Ns204p1904 Ns204p533 Ns204p1905 Ns204p536 RS205to222.d39 (@Ns204p1908 0 1 489506181416176 30594136338511 281474976710656 1412376415 281474976710656 (@Ns204p1909 218136528505295339520 13001950294095 281474976710656 1412376415 281474976710656 (@Ns204p1910 925837151 281474976710656 (Ns204p1893 rfl rfl) (Ns204p1893 rfl rfl) rfl) (Ns204p1893 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 11457719 16777216) (BSN.cos_neg_of_bound 11457719 16777216 Bool.false 6507252 8388608 1 2560000 (Ns204p1914 rfl rfl)) rfl rfl) 

noncomputable def Ns204p1916 := @Ns204p1879 2680970953175277273 184467440737095516160000 (Ns204p1880 qz29 (@Enclosure.Real.IsNear.of_eq qz777 (@Inv.inv Real Real.instInv (Real.sqrt qz234)) Bool.false 2803775 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz229 (BSN.t_div_two_pi_nonneg qz228 503462 1000 qz231)) Ns204p1884) rfl) (@Ns204p1885 35184372088832 1899643156521 43980465111040000 (BSN.correction_mk qz230 (BSN.cos_two_pi_p_ne_zero_mk qz228 503462 1000 8 qz231 rfl rfl (@BSN.floor_sqrt_eq_dec qz228 503462 1000 8 qz231 rfl rfl rfl))) (@Ns204p1886 16777216 1626813 2097152 167673 5242880000 28614412426185 35184372088832 1899643156521 43980465111040000 (@Ns204p1887 16777216 (Ns204p1901 rfl rfl rfl rfl rfl) rfl) (Ns204p1915 rfl) rfl)) 

noncomputable def Ns204p1917 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz228) (hardyZApproximantRS₀ qz228) Bool.true 944904052317968572023 295147905179352825856 272517617083822317273 184467440737095516160000 (@Eq.refl Real (hardyZApproximantRS₀ qz228)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz228) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz228) qz228 8) (@HMul.hMul Real Real Real qz5 qz775 (Zeta.RiemannSiegel.correction qz230))) Bool.true 944904052317968572023 295147905179352825856 272517617083822317273 184467440737095516160000 (BSN.hardyZApproximantRS₀_eq qz228 8 (@BSN.floor_sqrt_eq_dec qz228 503462 1000 8 qz231 rfl rfl rfl)) (@Ns204p1814 944904052317968572023 295147905179352825856 272517617083822317273 184467440737095516160000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz228) qz228 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz228) qz228 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz228) qz228 8)) Bool.true 196604487 67108864 49083 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz228) qz228 8) (Ns204p1878 (Ns204p1877 rfl rfl rfl rfl) rfl rfl)) (Ns204p1916 rfl) rfl rfl)) 

theorem RS205to222.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz228) Bool.true 944904052317968572023 295147905179352825856 272517617083822317273 184467440737095516160000 := Ns204p1917 

noncomputable def Ns204p1918 := nat_lit 7052865117964574089910681600 

noncomputable abbrev qz916 := (Enclosure.sfrac Bool.false 504895 1000)

noncomputable abbrev qz780 := qz916

noncomputable abbrev qz583 := qz780

noncomputable abbrev qz241 := qz583

noncomputable abbrev qz917 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 504895 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz781 := qz917

noncomputable abbrev qz584 := qz781

noncomputable abbrev qz242 := qz584

noncomputable abbrev qz918 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 504895 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz782 := qz918

noncomputable abbrev qz585 := qz782

noncomputable abbrev qz243 := qz585

noncomputable abbrev qz783 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz242 qz9))

noncomputable def Ns204p1919 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz241) qz241 8) (@HMul.hMul Real Real Real qz5 qz783 (Zeta.RiemannSiegel.correction qz243)) 66643195 67108864 6153 4194304 41454055628031284865 147573952589676412928 2131115576238488501 147573952589676412928000 Ns204p1918 

noncomputable def Ns204p1920 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz241) qz241 Real.cos BSN.quadSignPos 7 8 504895 1000 124 134217728 67108864 2251799813685248 Bool.false 114690939796 1851 279097919 53 47453128 8 

noncomputable def Ns204p1921 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz241) qz241 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 504895 1000 31 81 134217728 67108864 2251799813685248 Bool.false 114690939796 1851 

noncomputable def Ns204p1922 := Ns204p1921 240485871 53 54794152 8 261175631 53 50729528 8 Bool.false 7217801 65808 Bool.true 193483904 Bool.true 98204572 7074237752028440 1 Bool.false 133098561 Bool.false Bool.false 89673734 Bool.true Bool.false 27661572 

noncomputable def Ns204p1923 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz241) qz241 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 504895 1000 98 26 134217728 67108864 2251799813685248 Bool.false 114690939796 1851 

noncomputable def Ns204p1924 := Ns204p1923 186065264 53 67108856 8 216015088 53 60023992 8 Bool.false 89412290 38687 Bool.false 86304343 Bool.false 144455372 7074237752028440 1 Bool.false 107413118 Bool.true Bool.false 63700962 Bool.true Bool.false 7217801 

noncomputable def Ns204p1925 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz241) qz241 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 504895 1000 321 190 134217728 67108864 2251799813685248 Bool.false 114690939796 1851 

noncomputable def Ns204p1926 := Ns204p1925 93032624 53 94906264 8 147453232 53 77490640 16 Bool.false 134217672 1909 Bool.false 43215864 Bool.false 185084540 7074237752028440 1 Bool.false 42473003 Bool.true Bool.false 25586606 Bool.true Bool.false 89412290 

noncomputable def Ns204p1927 := nat_lit 29376440407504080659035766970765009725101409553894059 

noncomputable def Ns204p1928 := nat_lit 34377947335967256566484523564056508048369464115200 

noncomputable def Ns204p1929 := nat_lit 15748807179379485610313348500000000 

noncomputable def Ns204p1930 := nat_lit 47708985839677387717056749555445000000 

noncomputable abbrev qz919 := (@Eq.refl Real (Enclosure.sfrac Bool.false 504895 1000))

noncomputable abbrev qz784 := qz919

noncomputable abbrev qz586 := qz784

noncomputable abbrev qz244 := qz586

noncomputable def Ns204p1931 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz241 504895 1000 1019676844100 16000000 1009790 4000 2000 Ns204p1929 Ns204p1930 qz244 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns204p1932 := nat_lit 146882202037520403295178834853825048625507047769470295000000 

noncomputable abbrev qz587 := (Enclosure.sfrac Bool.false 504895 2000)

noncomputable abbrev qz785 := (Real.log (Enclosure.sfrac Bool.false 1019676844100 16000000))

noncomputable abbrev qz245 := (@HSub.hSub Real Real Real qz345 (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 504895 4000) qz785) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 1009790)))))) qz587)

noncomputable abbrev qz588 := (@HSub.hSub Real Real Real qz12 qz245 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 504895 2000) (Real.log Real.pi)))

noncomputable def Ns204p1933 := @Enclosure.Real.IsNear.addLit_ft_p qz588 (Enclosure.sfrac Bool.true Ns204p1929 Ns204p1930) 3078712661639159032731 3602879701896396800 1129222059410859 81920000000000000000 Ns204p1929 Ns204p1930 0 1 Ns204p1932 

noncomputable def Ns204p1934 := nat_lit 8264356372200813624076649103360 

noncomputable abbrev qz589 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 504895 2000) (Real.log Real.pi))

noncomputable def Ns204p1935 := @Enclosure.Real.IsNear.subLit_ff_p qz245 qz589 823977591840934293279 720575940379279360 125218543729 20000000000000000 3878680235019 13421772800 100979 13421772800 Ns204p1934 3078712661639159032731 3602879701896396800 

noncomputable def Ns204p1936 := nat_lit 8239775918409342932790000 

noncomputable abbrev qz246 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 504895 4000) qz785) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 1009790))))))

noncomputable def Ns204p1937 := @Enclosure.Real.IsNear.subLit_ff_p qz246 qz587 5029425932749162097563 3602879701896396800 125218543729 20000000000000000 504895 2000 0 1 Ns204p1936 823977591840934293279 720575940379279360 125218543729 20000000000000000 

noncomputable def Ns204p1938 := nat_lit 11325260378308317848763548984749850624 

noncomputable def Ns204p1939 := nat_lit 26747260311354575226404864 

noncomputable def Ns204p1940 := nat_lit 886712451304968113397740723268265973898019111510346162799670527127555192105704743690265902768789619722013821936814663141346097420437003220474313410250000000000000000000000000000 

noncomputable def Ns204p1941 := nat_lit 32458225911723652740079188754816250070358402548295323503114144660777894240577294616972465696306795469814879876233238307546048640756223296273728596150000000000000000000000000000 

noncomputable def Ns204p1942 := nat_lit 7244609112445852932520690902861880441518308432680111608158886504250304277404981495478443076290020583378997874835719197275160039374414810227350000000000000000000000000000 

noncomputable def Ns204p1943 := BSN.log_dyadic_bound 495388844100 1543964844100 8 7 Ns204p1940 67108864 20480000 Ns204p1941 Ns204p1942 44640808 2039353688200 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 495388844100) (BSN.artanhQ 1543964844100) 0 7 Ns204p1941 Ns204p1940 Ns204p1942 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns204p1944 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 504895 4000) qz785 504895 4000 0 1 49820654674162297 4503599627370496 2441407 50000000000000 5030839888342234588763 3602879701896396800 246530837453 40000000000000000 (Enclosure.Real.IsNear.const Bool.false 504895 4000) (BSN.isNear_log_sfrac 1019676844100 16000000 49820654674162297 4503599627370496 2441407 50000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1019676844100) qz352)) Bool.false Ns204p1939 Ns204p89 1000000307200000 20480000000000000000000 49820654674162297 4503599627370496 2441407 50000000000000 (BSN.log_rat_reduce_isNear 1019676844100 16000000 15 2039353688200 1048576000000 44640808 67108864 24973259072661432 36028797018963968 20480000 1000000000000000 rfl rfl rfl rfl (Ns204p1943 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns204p1945 := BSN.arctan_dyadic_bound_f 1000 1009790 1 0 8388608 2560000 0 1 1 0 1 1 8307 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1009790) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1009790) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz590 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1009790)))

noncomputable def Ns204p1946 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz590 884279719003555 562949953421312 1 2000000000000000 8307 8388608 1 2560000 7413199499807902662656 883722245670307 562949953421312 781250001 2000000000000000 qz17 (Ns204p1945 rfl) rfl rfl 

noncomputable def Ns204p1947 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 504895 4000) qz785) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz590)) 5030839888342234588763 3602879701896396800 246530837453 40000000000000000 883722245670307 2251799813685248 781250001 8000000000000000 Ns204p1938 5029425932749162097563 3602879701896396800 125218543729 20000000000000000 (Ns204p1944 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz590) 1 4 0 1 883722245670307 562949953421312 781250001 2000000000000000 883722245670307 2251799813685248 781250001 8000000000000000 qz355 Ns204p1946 rfl) 

noncomputable def Ns204p1948 := @Ns204p1933 Ns204p1927 Ns204p1928 1129222059410859 81920000000000000000 (@Ns204p1935 1129222059410859 81920000000000000000 (Ns204p1937 (Ns204p1947 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 504895 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz587 (Real.log Real.pi) 504895 2000 0 1 38410761 33554432 1 33554432 3878680235019 13421772800 100979 13421772800 (Enclosure.Real.IsNear.const Bool.false 504895 2000) RS205to222.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns204p1929 Ns204p1930) 

noncomputable def Ns204p1949 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz241) Bool.false Ns204p1927 Ns204p1928 1129222059410859 81920000000000000000 7168183737 8388608 29 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz241) (@HAdd.hAdd Real Real Real qz356 qz588 (Enclosure.sfrac Bool.true Ns204p1929 Ns204p1930)) Bool.false Ns204p1927 Ns204p1928 1129222059410859 81920000000000000000 Ns204p1931 (Ns204p1948 rfl rfl)) 

noncomputable def Ns204p1950 := BSN.cos_dyadic_bound_f 30541712 34359738368 1 0 16777216 5125001 0 1 1 0 1 1 16777209 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 30541712) qz642 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 30541712) qz643 0 0 rfl) rfl rfl 

noncomputable def Ns204p1951 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz241) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7168183737) qz359) Bool.false 7168183737 8388608 29 2097152 Bool.false 16777209 16777216 1 2560000 (Ns204p1949 rfl) (Enclosure.sfrac_false_div 7168183737 8388608) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7168183737) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1074590962330321813504) qz360) 226375608064910080 72057594037927936 Bool.false 16777209 16777216 136 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q0 7168183737 8388608 226375608064910080 72057594037927936 136 1074590962330321813504 Ns204p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777209 16777216 1074590962330321813504 Ns204p100 30541712 34359738368 5125001 5120000 (Ns204p1950 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p1952 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz241) Bool.false Ns204p1927 Ns204p1928 1129222059410859 81920000000000000000 114690939796 134217728 1851 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz241) (@HAdd.hAdd Real Real Real qz356 qz588 (Enclosure.sfrac Bool.true Ns204p1929 Ns204p1930)) Bool.false Ns204p1927 Ns204p1928 1129222059410859 81920000000000000000 Ns204p1931 (Ns204p1948 rfl rfl)) 

noncomputable def Ns204p1953 := Ns204p1926 38687 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 321 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 42473003 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 190 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 25586606 134217728) qz244 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz241) qz241 1) Bool.false 16777209 16777216 18637 1310720000 134217672 134217728 1909 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz241) qz241 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz241)) Bool.false 16777209 16777216 18637 1310720000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz241) qz241) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz241)) Bool.false 16777209 16777216 76337152 5368709120000 16777209 16777216 18637 1310720000 (Ns204p1951 rfl rfl) rfl)) rfl) (Ns204p1952 rfl) RS205to222.d7 

noncomputable def Ns204p1954 := nat_lit 3487970478529453470416812118016 

noncomputable def Ns204p1955 := BSN.sin_dyadic_bound_f 43215864 134217728 2 1 134217728 67108864 Ns204p1954 Ns204p129 Ns204p1954 Ns204p1954 Ns204p130 Ns204p1954 42473003 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 43215864) qz361 0 1 Ns204p1954 Ns204p129 Ns204p1954 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 43215864) qz362 0 1 Ns204p1954 Ns204p130 Ns204p1954 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1956 := nat_lit 2471834759541794211152620231143039746082005675131179705369740981611545752494991547887089203334610944000000 

noncomputable def Ns204p1957 := nat_lit 1616001378631560792313478966706301778863548756746075173152563748548080063258706404642816000000000000 

noncomputable def Ns204p1958 := nat_lit 14974317180466479095280559286770159679541909260947998307463209149408630000457876478218254979830749593600000 

noncomputable def Ns204p1959 := BSN.cos_dyadic_bound_f 185084540 134217728 4 3 134217728 67108864 Ns204p1956 Ns204p230 Ns204p1957 Ns204p1958 Ns204p233 Ns204p1957 25586606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 185084540) qz363 0 3 Ns204p1956 Ns204p230 Ns204p1957 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 185084540) qz364 0 3 Ns204p1958 Ns204p233 Ns204p1957 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1960 := nat_lit 30249876690892479753659443334149646271762994170297094835863271484481 

noncomputable def Ns204p1961 := nat_lit 3077947489320317801187506187190700477126774638421130506039438401 

noncomputable def Ns204p1962 := nat_lit 90743474177698798625375954990074557414334728961614442246577735576641 

noncomputable def Ns204p1963 := BSN.cos_dyadic_bound_f 86304343 134217728 3 2 134217728 67108864 Ns204p1960 Ns204p240 Ns204p1961 Ns204p1962 Ns204p243 Ns204p1961 107413118 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 86304343) qz363 0 2 Ns204p1960 Ns204p240 Ns204p1961 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 86304343) qz364 0 2 Ns204p1962 Ns204p243 Ns204p1961 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1964 := nat_lit 915980751239262356235484063675239355123460744654412355630552147407607884733964939430137540089181473079296 

noncomputable def Ns204p1965 := nat_lit 82566592937226942860752062489126000867825141465864775511294165804881239485459410434884317600546816 

noncomputable def Ns204p1966 := nat_lit 5553992927997123929576916506404500100026895252756716493248722243191126035841908933889292001716332354600960 

noncomputable def Ns204p1967 := BSN.cos_dyadic_bound_f 144455372 134217728 4 3 134217728 67108864 Ns204p1964 Ns204p230 Ns204p1965 Ns204p1966 Ns204p233 Ns204p1965 63700962 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 144455372) qz363 0 3 Ns204p1964 Ns204p230 Ns204p1965 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 144455372) qz364 0 3 Ns204p1966 Ns204p233 Ns204p1965 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1968 := Ns204p1924 65808 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 98 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 107413118 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 26 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 63700962 134217728) qz244 rfl rfl (Ns204p1953 RS205to222.d9 RS205to222.d11 RS205to222.d13 RS205to222.d17 (Ns204p1955 rfl rfl) (Ns204p1959 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns204p1952 rfl) RS205to222.d19 RS205to222.d21 RS205to222.d23 RS205to222.d25 RS205to222.d17 (Ns204p1963 rfl rfl) (Ns204p1967 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns204p1969 := nat_lit 7669683264935432182756999444714665887710600426464124332681781320640164787421662748553152952609019229372416 

noncomputable def Ns204p1970 := nat_lit 2752568279676995393876495319637255295169358953886703045910170738461785534271089634085459813692604416 

noncomputable def Ns204p1971 := nat_lit 38314598692147962470339170356820217663895322134594697765339280255899997669561584618963670282677409888075776 

noncomputable def Ns204p1972 := BSN.sin_dyadic_bound_f 193483904 134217728 4 3 134217728 67108864 Ns204p1969 Ns204p256 Ns204p1970 Ns204p1971 Ns204p259 Ns204p1970 133098561 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 193483904) qz361 0 3 Ns204p1969 Ns204p256 Ns204p1970 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 193483904) qz362 0 3 Ns204p1971 Ns204p259 Ns204p1970 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1973 := nat_lit 91282874344877959314968839686608389257316411068179308428299247616000 

noncomputable def Ns204p1974 := nat_lit 8650747934835853589926264146453901472112151686133295411311476736 

noncomputable def Ns204p1975 := nat_lit 239060188739928730633391842370594379833445275980596830072022572793856 

noncomputable def Ns204p1976 := BSN.sin_dyadic_bound_f 98204572 134217728 3 2 134217728 67108864 Ns204p1973 Ns204p106 Ns204p1974 Ns204p1975 Ns204p109 Ns204p1974 89673734 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 98204572) qz361 0 2 Ns204p1973 Ns204p106 Ns204p1974 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 98204572) qz362 0 2 Ns204p1975 Ns204p109 Ns204p1974 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1977 := Ns204p1922 88322 BSN.abs_quadSignPos (BSN.cos_quad_nat3 31 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 133098561 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 81 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 89673734 134217728) qz244 rfl rfl (Ns204p1968 rfl rfl) (Ns204p1952 rfl) RS205to222.d27 RS205to222.d29 RS205to222.d31 RS205to222.d33 RS205to222.d17 (Ns204p1972 rfl rfl) (Ns204p1976 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns204p1978 := nat_lit 23988815705596475683915201506136799697754545920861200806416257908736 

noncomputable def Ns204p1979 := nat_lit 1935752801099924429071943717190667463016241608928428099377299456 

noncomputable def Ns204p1980 := nat_lit 71962575611187227202887460630976017758337605279365745563050019127296 

noncomputable def Ns204p1981 := BSN.cos_dyadic_bound_f 81443464 134217728 3 2 134217728 67108864 Ns204p1978 Ns204p240 Ns204p1979 Ns204p1980 Ns204p243 Ns204p1979 110256692 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 81443464) qz363 0 2 Ns204p1978 Ns204p240 Ns204p1979 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 81443464) qz364 0 2 Ns204p1980 Ns204p243 Ns204p1979 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p1982 := Ns204p1920 Bool.false 27661572 88322 Bool.true 81443464 7074237752028440 1 Bool.false 110256692 Bool.false Bool.false 66643195 98448 BSN.abs_quadSignPos qz735 (BSN.sfrac_eq_quadSignPos_mul Bool.false 110256692 134217728) qz244 rfl (Ns204p1977 rfl) (Ns204p1952 rfl) RS205to222.d35 RS205to222.d37 RS205to222.d17 (Ns204p1981 rfl rfl) rfl 

noncomputable def Ns204p1983 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz241) qz241 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz241) qz241 8) 66643195 134217728 98448 134217728 66643195 134217728 98448 134217728 17889396439121920 66643195 67108864 6153 4194304 (Ns204p1982 rfl rfl rfl rfl) 

noncomputable def Ns204p1984 := @Enclosure.Real.IsNear.mulLit_ff qz783 (Zeta.RiemannSiegel.correction qz243) 350223 1048576 1 8388608 118364743686255 140737488355328 1888367579309 43980465111040000 41454055628031284865 147573952589676412928 

noncomputable abbrev qz786 := (@HPow.hPow Real Real Real qz7 qz242 qz9)

noncomputable def Ns204p1985 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz786 1 1 0 1 350223 1048576 1 8388608 350223 1048576 1 8388608 

noncomputable def Ns204p1986 := @Enclosure.Real.IsNear.sqrt_image qz242 269631803283 3355443200 100979 3355443200 75196985 75197014 8388608 (@Enclosure.Real.IsNear.of_eq qz242 (@HMul.hMul Real Real Real qz5 qz241 qz3) Bool.false 269631803283 3355443200 100979 3355443200 (BSN.t_div_two_pi_mk qz241 504895 1000 qz244) (@Enclosure.Real.IsNear.mulLit_ff qz241 qz3 504895 1000 0 1 2670177 16777216 1 16777216 269631803283 3355443200 100979 3355443200 (Enclosure.Real.IsNear.const Bool.false 504895 1000) RS205to222.d40 rfl)) 

noncomputable abbrev qz920 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 504895 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz787 := qz920

noncomputable abbrev qz591 := qz787

noncomputable abbrev qz247 := qz591

noncomputable def Ns204p1987 := @Enclosure.Real.IsNear.sqrt_image qz247 150393999 16777216 29 16777216 25115692 25115698 8388608 (@Enclosure.Real.IsNear.recentre' qz247 Bool.false 150393999 16777216 29 16777216 150393999 16777216 29 16777216 (Ns204p1986 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns204p1988 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz247) 25115695 8388608 3 8388608 2801783 2801785 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz247) Bool.false 50231390 16777216 6 16777216 25115695 8388608 3 8388608 (Ns204p1987 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns204p1989 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz247)) Bool.false 5603568 16777216 2 16777216 350223 1048576 1 8388608 (Ns204p1988 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz248 := (@HMul.hMul Real Real Real qz342 qz340 qz585)

noncomputable abbrev qz788 := (@HMul.hMul Real Real Real qz844 qz918 qz918)

noncomputable abbrev qz592 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz788 qz782) qz640)

noncomputable abbrev qz249 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz592))

noncomputable def Ns204p1990 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz243) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz248)) qz249) Bool.false 118364743686255 

noncomputable def Ns204p1991 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz248)) qz249 17211265 16777216 201 

noncomputable def Ns204p1992 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz248)) Bool.false 17211265 16777216 201 16777216 17211265 16777216 201 

noncomputable def Ns204p1993 := @Enclosure.Real.IsNear.recentre' (Real.cos qz248) Bool.false 16354113 16777216 485257216 42949672960000 16354113 16777216 118471 10485760000 

noncomputable def Ns204p1994 := @Enclosure.Real.IsNear.cos_image qz248 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 25409627) qz385) Bool.false 25409627 4194304 183 16777216 Bool.false 16354113 16777216 1 

noncomputable def Ns204p1995 := nat_lit 31303847480049217121294659 

noncomputable def Ns204p1996 := nat_lit 2882303761517117440000000000000 

noncomputable def Ns204p1997 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz243 884279719003555 140737488355328 1 500000000000000 16176271 16777216 29 16777216 14304348374405355643405 2361183241434822606848 Ns204p1995 

noncomputable def Ns204p1998 := @Enclosure.Real.IsNear.subLit_ff_p qz247 qz1 150393999 16777216 29 16777216 8 1 0 1 16176271 16176271 16777216 29 

noncomputable def Ns204p1999 := @Ns204p1998 16777216 (@Enclosure.Real.IsNear.recentre' qz247 Bool.false 150393999 16777216 29 16777216 150393999 16777216 29 16777216 (Ns204p1986 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns204p2000 := @Enclosure.Real.IsNear.recentre' qz248 Bool.false 14304348374405355643405 2361183241434822606848 Ns204p1995 Ns204p1996 25409627 4194304 183 16777216 (@Ns204p1997 Ns204p1996 RS205to222.d39 (Ns204p1999 rfl rfl) rfl) 

noncomputable def Ns204p2001 := nat_lit 19288286358369344811375097117026333029564723787511035808928209975118059749984534274464705 

noncomputable def Ns204p2002 := nat_lit 20896973363884178295382756040273378565193667005268285758059488628277091479305180109761 

noncomputable def Ns204p2003 := nat_lit 50483107267425804883980348939575191512135391601663230846441786953244374530421571855801281 

noncomputable def Ns204p2004 := BSN.sin_dyadic_bound_f 46239211929 34359738368 3 2 16777216 5125001 Ns204p2001 Ns204p1161 Ns204p2002 Ns204p2003 Ns204p1164 Ns204p2002 16354113 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 46239211929) qz357 0 2 Ns204p2001 Ns204p1161 Ns204p2002 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 46239211929) qz358 0 2 Ns204p2003 Ns204p1164 Ns204p2002 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p2005 := @Ns204p1994 2560000 (Ns204p2000 rfl) (Enclosure.sfrac_false_div 25409627 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 25409627) qz385) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 813448818815091588726784) qz386) 226375608064910080 72057594037927936 Bool.false 16354113 16777216 0 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q3 25409627 4194304 226375608064910080 72057594037927936 0 813448818815091588726784 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16354113 16777216 813448818815091588726784 604462909807314587353088 46239211929 34359738368 5125001 5120000 (Ns204p2004 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p2006 := @Enclosure.Real.IsNear.inv_image (Real.cos qz248) 16354113 16777216 118471 10485760000 8605532 8605733 8388608 (Ns204p1993 (Ns204p2005 rfl rfl) rfl) rfl 

noncomputable def Ns204p2007 := @Enclosure.Real.IsNear.recentre' qz249 Bool.false 6877167 8388608 

noncomputable abbrev qz250 := (@HMul.hMul Real Real Real qz342 qz340 qz592)

noncomputable def Ns204p2008 := @Enclosure.Real.IsNear.cos_image qz250 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 5114499)) qz359) Bool.true 5114499 8388608 

noncomputable def Ns204p2009 := nat_lit 24152539965871468667617916605 

noncomputable def Ns204p2010 := nat_lit 38448783967790501882132412720697353 

noncomputable def Ns204p2011 := @Enclosure.Real.IsNear.recentre' qz250 Bool.true Ns204p2009 Ns204p533 Ns204p2010 

noncomputable abbrev qz251 := qz592

noncomputable def Ns204p2012 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz251 884279719003555 140737488355328 1 500000000000000 27313235220511 

noncomputable abbrev qz593 := (@HSub.hSub Real Real Real qz634 qz788 qz782)

noncomputable abbrev qz252 := qz593

noncomputable def Ns204p2013 := @Enclosure.Real.IsNear.subLit_tf qz252 qz27 9721049176095 281474976710656 1424763823 281474976710656 1 16 

noncomputable abbrev qz594 := qz788

noncomputable abbrev qz253 := qz594

noncomputable def Ns204p2014 := @Enclosure.Real.IsNear.subLit_ff_n qz253 qz243 261671743465441 281474976710656 938224559 281474976710656 16176271 16777216 29 16777216 

noncomputable def Ns204p2015 := @Enclosure.Real.IsNear.mulLit_ff qz243 qz243 16176271 16777216 29 16777216 16176271 16777216 29 16777216 261671743465441 281474976710656 

noncomputable def Ns204p2016 := nat_lit 5692682924481085645615571481813281965946413181866622629281 

noncomputable def Ns204p2017 := nat_lit 468192857710310733792844456463969985511663879046084001 

noncomputable def Ns204p2018 := nat_lit 17077112387727836315379128756526917957868216217841775719841 

noncomputable def Ns204p2019 := BSN.cos_dyadic_bound_f 5114499 8388608 3 2 8388608 2560000 Ns204p2016 Ns204p1178 Ns204p2017 Ns204p2018 Ns204p1181 Ns204p2017 6877167 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 5114499) (BSN.cosEvenQ 8388608) 0 2 Ns204p2016 Ns204p1178 Ns204p2017 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 5114499) (BSN.cosOddQ 8388608) 0 2 Ns204p2018 Ns204p1181 Ns204p2017 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p2020 := @Ns204p2007 1386377216 42949672960000 6877167 8388608 338471 10485760000 (@Ns204p2008 535 16777216 Bool.false 6877167 8388608 1 2560000 (@Ns204p2011 Ns204p536 5114499 8388608 535 16777216 (@Ns204p2012 281474976710656 1424763823 281474976710656 Ns204p2009 Ns204p533 Ns204p2010 Ns204p536 RS205to222.d39 (@Ns204p2013 0 1 437011763528176 27313235220511 281474976710656 1424763823 281474976710656 (@Ns204p2014 163092141773967851520 9721049176095 281474976710656 1424763823 281474976710656 (@Ns204p2015 938224559 281474976710656 (Ns204p1999 rfl rfl) (Ns204p1999 rfl rfl) rfl) (Ns204p1999 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 5114499 8388608) (BSN.cos_neg_of_bound 5114499 8388608 Bool.false 6877167 8388608 1 2560000 (Ns204p2019 rfl rfl)) rfl rfl) 

noncomputable def Ns204p2021 := @Ns204p1984 2131115576238488501 147573952589676412928000 (Ns204p1985 qz29 (@Enclosure.Real.IsNear.of_eq qz786 (@Inv.inv Real Real.instInv (Real.sqrt qz247)) Bool.false 350223 1048576 1 8388608 (BSN.rpow_neg_quarter_mk qz242 (BSN.t_div_two_pi_nonneg qz241 504895 1000 qz244)) Ns204p1989) rfl) (@Ns204p1990 140737488355328 1888367579309 43980465111040000 (BSN.correction_mk qz243 (BSN.cos_two_pi_p_ne_zero_mk qz241 504895 1000 8 qz244 rfl rfl (@BSN.floor_sqrt_eq_dec qz241 504895 1000 8 qz244 rfl rfl rfl))) (@Ns204p1991 16777216 6877167 8388608 338471 10485760000 118364743686255 140737488355328 1888367579309 43980465111040000 (@Ns204p1992 16777216 (Ns204p2006 rfl rfl rfl rfl rfl) rfl) (Ns204p2020 rfl) rfl)) 

noncomputable def Ns204p2022 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz241) (hardyZApproximantRS₀ qz241) Bool.false 105095880001255483775 147573952589676412928 218620557038821784501 147573952589676412928000 (@Eq.refl Real (hardyZApproximantRS₀ qz241)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz241) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz241) qz241 8) (@HMul.hMul Real Real Real qz5 qz783 (Zeta.RiemannSiegel.correction qz243))) Bool.false 105095880001255483775 147573952589676412928 218620557038821784501 147573952589676412928000 (BSN.hardyZApproximantRS₀_eq qz241 8 (@BSN.floor_sqrt_eq_dec qz241 504895 1000 8 qz244 rfl rfl rfl)) (@Ns204p1919 105095880001255483775 147573952589676412928 218620557038821784501 147573952589676412928000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz241) qz241 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz241) qz241 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz241) qz241 8)) Bool.false 66643195 67108864 6153 4194304 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz241) qz241 8) (Ns204p1983 (Ns204p1982 rfl rfl rfl rfl) rfl rfl)) (Ns204p2021 rfl) rfl rfl)) 

theorem RS205to222.d60 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz241) Bool.false 105095880001255483775 147573952589676412928 218620557038821784501 147573952589676412928000 := Ns204p2022 

noncomputable def Ns204p2023 := nat_lit 325604033131215653848481792 

noncomputable abbrev qz921 := (Enclosure.sfrac Bool.false 506327 1000)

noncomputable abbrev qz789 := qz921

noncomputable abbrev qz595 := qz789

noncomputable abbrev qz254 := qz595

noncomputable abbrev qz922 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 506327 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz790 := qz922

noncomputable abbrev qz596 := qz790

noncomputable abbrev qz255 := qz596

noncomputable abbrev qz923 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 506327 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz791 := qz923

noncomputable abbrev qz597 := qz791

noncomputable abbrev qz256 := qz597

noncomputable abbrev qz792 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz255 qz9))

noncomputable def Ns204p2024 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz254) qz254 8) (@HMul.hMul Real Real Real qz5 qz792 (Zeta.RiemannSiegel.correction qz256)) 3955891 16777216 98727 67108864 10708416426791772255 36893488147419103232 10594797537153288099 737869762948382064640000 Ns204p2023 

noncomputable def Ns204p2025 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz254) qz254 Real.cos BSN.quadSignPos 7 8 506327 1000 124 134217728 67108864 2251799813685248 Bool.false 115112615660 1856 279097919 53 47453128 8 

noncomputable def Ns204p2026 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz254) qz254 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 506327 1000 31 81 134217728 67108864 2251799813685248 Bool.false 115112615660 1856 

noncomputable def Ns204p2027 := Ns204p2026 240485871 53 54794152 8 261175631 53 50729528 8 Bool.true 81774304 65996 Bool.true 116183807 Bool.true 50532212 7074237752028440 1 Bool.false 102207897 Bool.false Bool.false 49346838 Bool.true Bool.true 58699460 

noncomputable def Ns204p2028 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz254) qz254 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 506327 1000 99 27 134217728 67108864 2251799813685248 Bool.false 115112615660 1856 

noncomputable def Ns204p2029 := Ns204p2028 186065264 53 67108856 8 216015088 53 60023992 8 Bool.true 117152098 38799 Bool.false 30706035 Bool.false 45968916 7074237752028440 1 Bool.false 30438879 Bool.false Bool.false 45075457 Bool.false Bool.true 81774304 

noncomputable def Ns204p2030 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz254) qz254 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 506327 1000 322 191 134217728 67108864 2251799813685248 Bool.false 115112615660 1856 

noncomputable def Ns204p2031 := Ns204p2030 93032624 53 94906264 8 147453232 53 77490640 16 Bool.true 134217656 1917 Bool.false 120840297 Bool.false 184778661 7074237752028440 1 Bool.false 83396338 Bool.true Bool.false 131697652 Bool.false Bool.true 117152098 

noncomputable def Ns204p2032 := nat_lit 468590092547059238353402804476883947583886440147736959051 

noncomputable def Ns204p2033 := nat_lit 546361467195406468190818231331377231000071597509836800 

noncomputable def Ns204p2034 := nat_lit 15973413876940310386767603395360000 

noncomputable def Ns204p2035 := nat_lit 48526646451865793014130388567950656320 

noncomputable def Ns204p2036 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz254 506327 1000 1025469123716 16000000 1012654 4000 2000 Ns204p2034 Ns204p2035 (@Eq.refl Real qz254) rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns204p2037 := nat_lit 149948829615058956273088897432602863226843660847275826896320 

noncomputable abbrev qz598 := (Enclosure.sfrac Bool.false 506327 2000)

noncomputable abbrev qz793 := (Real.log (Enclosure.sfrac Bool.false 1025469123716 16000000))

noncomputable abbrev qz257 := (@HSub.hSub Real Real Real qz345 (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 506327 4000) qz793) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 1012654)))))) qz598)

noncomputable abbrev qz599 := (@HSub.hSub Real Real Real qz12 qz257 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 506327 2000) (Real.log Real.pi)))

noncomputable def Ns204p2038 := @Enclosure.Real.IsNear.addLit_ft_p qz599 (Enclosure.sfrac Bool.true Ns204p2034 Ns204p2035) 3090031933570431663251 3602879701896396800 5662010533628847 409600000000000000000 Ns204p2034 Ns204p2035 0 1 Ns204p2037 

noncomputable def Ns204p2039 := nat_lit 1036842663928175664552025784320000 

noncomputable abbrev qz600 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 506327 2000) (Real.log Real.pi))

noncomputable def Ns204p2040 := @Enclosure.Real.IsNear.subLit_ff_p qz257 qz600 20670801235806418251487 18014398509481984000 627840766057 100000000000000000 19448405384847 67108864000 506327 67108864000 Ns204p2039 3090031933570431663251 3602879701896396800 

noncomputable def Ns204p2041 := nat_lit 41341602471612836502974000 

noncomputable abbrev qz258 := (@HSub.hSub Real Real Real qz345 (@HMul.hMul Real Real Real qz342 (Enclosure.sfrac Bool.false 506327 4000) qz793) (@HMul.hMul Real Real Real qz342 qz346 (@HSub.hSub Real Real Real qz345 qz347 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz348 (@Nat.cast Real Real.instNatCast 1012654))))))

noncomputable def Ns204p2042 := @Enclosure.Real.IsNear.subLit_ff_p qz258 qz598 25231389412861660507871 18014398509481984000 627840766057 100000000000000000 506327 2000 0 1 Ns204p2041 20670801235806418251487 18014398509481984000 627840766057 100000000000000000 

noncomputable def Ns204p2043 := nat_lit 56816037978901826058878029967820587008 

noncomputable def Ns204p2044 := nat_lit 26760956082080582075416576 

noncomputable def Ns204p2045 := nat_lit 934437123224526035470456511437275721540562306640045518933464085781430783583536066179541706163999952369210403196313049031533167782023322796140792358171861074760229393751500390400 

noncomputable def Ns204p2046 := nat_lit 34785886561709561739035172156240954326474538538383075380206422909661269828281697690519553795946902059539165542067817078328540533921882511776479414893692216787194304430069514240 

noncomputable def Ns204p2047 := nat_lit 8524986962802621414405516128462984507929464183035375023039988400371960456945116658743476068774902784610145989216564184622298278406065138081480803635156647225953993359360 

noncomputable def Ns204p2048 := BSN.log_dyadic_bound 501181123716 1549757123716 8 7 Ns204p2045 67108864 20480000 Ns204p2046 Ns204p2047 45020942 2050938247432 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 501181123716) (BSN.artanhQ 1549757123716) 0 7 Ns204p2046 Ns204p2045 Ns204p2047 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns204p2049 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 506327 4000) qz793 506327 4000 0 1 49846165035070073 4503599627370496 2441407 50000000000000 25238459203711924851871 18014398509481984000 1236150282089 200000000000000000 (Enclosure.Real.IsNear.const Bool.false 506327 4000) (BSN.isNear_log_sfrac 1025469123716 16000000 49846165035070073 4503599627370496 2441407 50000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1025469123716) qz352)) Bool.false Ns204p2044 Ns204p89 1000000307200000 20480000000000000000000 49846165035070073 4503599627370496 2441407 50000000000000 (BSN.log_rat_reduce_isNear 1025469123716 16000000 15 2050938247432 1048576000000 45020942 67108864 24973259072661432 36028797018963968 20480000 1000000000000000 rfl rfl rfl rfl (Ns204p2048 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns204p2050 := BSN.arctan_dyadic_bound_f 1000 1012654 1 0 8388608 2560000 0 1 1 0 1 1 8283 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1012654) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1012654) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz601 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1012654)))

noncomputable def Ns204p2051 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz601 884279719003555 562949953421312 1 2000000000000000 8283 8388608 1 2560000 7413213010606784774144 883723856283043 562949953421312 781250001 2000000000000000 qz17 (Ns204p2050 rfl) rfl rfl 

noncomputable def Ns204p2052 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 506327 4000) qz793) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz601)) 25238459203711924851871 18014398509481984000 1236150282089 200000000000000000 883723856283043 2251799813685248 781250001 8000000000000000 Ns204p2043 25231389412861660507871 18014398509481984000 627840766057 100000000000000000 (Ns204p2049 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz601) 1 4 0 1 883723856283043 562949953421312 781250001 2000000000000000 883723856283043 2251799813685248 781250001 8000000000000000 qz355 Ns204p2051 rfl) 

noncomputable def Ns204p2053 := @Ns204p2038 Ns204p2032 Ns204p2033 5662010533628847 409600000000000000000 (@Ns204p2040 5662010533628847 409600000000000000000 (Ns204p2042 (Ns204p2052 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 506327 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz598 (Real.log Real.pi) 506327 2000 0 1 38410761 33554432 1 33554432 19448405384847 67108864000 506327 67108864000 (Enclosure.Real.IsNear.const Bool.false 506327 2000) RS205to222.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns204p2034 Ns204p2035) 

noncomputable def Ns204p2054 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz254) Bool.false Ns204p2032 Ns204p2033 5662010533628847 409600000000000000000 14389076957 16777216 233 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz254) (@HAdd.hAdd Real Real Real qz356 qz599 (Enclosure.sfrac Bool.true Ns204p2034 Ns204p2035)) Bool.false Ns204p2032 Ns204p2033 5662010533628847 409600000000000000000 Ns204p2036 (Ns204p2053 rfl rfl)) 

noncomputable def Ns204p2055 := BSN.cos_dyadic_bound_f 35261259 34359738368 1 0 16777216 5125001 0 1 1 0 1 1 16777207 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 35261259) qz642 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 35261259) qz643 0 0 rfl) rfl rfl 

noncomputable def Ns204p2056 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz254) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 14389076957) qz369) Bool.false 14389076957 16777216 233 16777216 Bool.true 16777207 16777216 1 2560000 (Ns204p2054 rfl) (Enclosure.sfrac_false_div 14389076957 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 14389076957) qz369) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2481290578111573786624) qz371) 226375608064910080 72057594037927936 Bool.false 16777207 16777216 136 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q2 14389076957 16777216 226375608064910080 72057594037927936 136 2481290578111573786624 Ns204p89 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 16777207 16777216 2481290578111573786624 Ns204p89 35261259 34359738368 5125001 5120000 (Ns204p2055 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p2057 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz254) Bool.false Ns204p2032 Ns204p2033 5662010533628847 409600000000000000000 115112615660 134217728 1856 134217728 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz254) (@HAdd.hAdd Real Real Real qz356 qz599 (Enclosure.sfrac Bool.true Ns204p2034 Ns204p2035)) Bool.false Ns204p2032 Ns204p2033 5662010533628847 409600000000000000000 Ns204p2036 (Ns204p2053 rfl rfl)) 

noncomputable def Ns204p2058 := Ns204p2031 38799 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 322 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 83396338 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 191 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 131697652 134217728) (@Eq.refl Real qz254) rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz254) qz254 1) Bool.true 16777207 16777216 149721 10485760000 134217656 134217728 1917 134217728 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz254) qz254 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz254)) Bool.true 16777207 16777216 149721 10485760000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz254) qz254) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz254)) Bool.true 16777207 16777216 613257216 42949672960000 16777207 16777216 149721 10485760000 (Ns204p2056 rfl rfl) rfl)) rfl) (Ns204p2057 rfl) RS205to222.d7 

noncomputable def Ns204p2059 := nat_lit 116296266578577902522692031647419201318806644354572556239059988722241 

noncomputable def Ns204p2060 := nat_lit 45466787737064897270424166660882415404276499508771679731647197761 

noncomputable def Ns204p2061 := nat_lit 348797866160259577773535246608935839125611380064700125357716671771201 

noncomputable def Ns204p2062 := BSN.cos_dyadic_bound_f 120840297 134217728 3 2 134217728 67108864 Ns204p2059 Ns204p240 Ns204p2060 Ns204p2061 Ns204p243 Ns204p2060 83396338 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 120840297) qz363 0 2 Ns204p2059 Ns204p240 Ns204p2060 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 120840297) qz364 0 2 Ns204p2061 Ns204p243 Ns204p2060 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p2063 := nat_lit 6378243626245924074403572932338245926352270146066255799748474449273856005879734084059188004696785247367121 

noncomputable def Ns204p2064 := nat_lit 1584242967644667279822000797848674086614608600877383924943581042819989234478428785516220915892973521 

noncomputable def Ns204p2065 := nat_lit 31867820321175871498842802267740301110986913772255265981509222223193556726045126084092724944126913067184081 

noncomputable def Ns204p2066 := BSN.sin_dyadic_bound_f 184778661 134217728 4 3 134217728 67108864 Ns204p2063 Ns204p256 Ns204p2064 Ns204p2065 Ns204p259 Ns204p2064 131697652 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 184778661) qz361 0 3 Ns204p2063 Ns204p256 Ns204p2064 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 184778661) qz362 0 3 Ns204p2065 Ns204p259 Ns204p2064 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p2067 := nat_lit 888986083540855125010680500625 

noncomputable def Ns204p2068 := BSN.sin_dyadic_bound_f 30706035 134217728 2 1 134217728 67108864 Ns204p2067 Ns204p129 Ns204p2067 Ns204p2067 Ns204p130 Ns204p2067 30438879 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 30706035) qz361 0 1 Ns204p2067 Ns204p129 Ns204p2067 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 30706035) qz362 0 1 Ns204p2067 Ns204p130 Ns204p2067 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p2069 := nat_lit 4465365892645060048204905083136 

noncomputable def Ns204p2070 := BSN.sin_dyadic_bound_f 45968916 134217728 2 1 134217728 67108864 Ns204p2069 Ns204p129 Ns204p2069 Ns204p2069 Ns204p130 Ns204p2069 45075457 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 45968916) qz361 0 1 Ns204p2069 Ns204p129 Ns204p2069 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 45968916) qz362 0 1 Ns204p2069 Ns204p130 Ns204p2069 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p2071 := Ns204p2029 65996 BSN.abs_quadSignPos (BSN.cos_quad_nat3 99 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 30438879 134217728) BSN.abs_quadSignPos (BSN.cos_quad_nat3 27 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 45075457 134217728) (@Eq.refl Real qz254) rfl rfl (Ns204p2058 RS205to222.d9 RS205to222.d11 RS205to222.d13 RS205to222.d17 (Ns204p2062 rfl rfl) (Ns204p2066 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns204p2057 rfl) RS205to222.d19 RS205to222.d21 RS205to222.d23 RS205to222.d25 RS205to222.d17 (Ns204p2068 rfl rfl) (Ns204p2070 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns204p2072 := nat_lit 178848112774294296635092812126935902241241006481210465839756046854145 

noncomputable def Ns204p2073 := nat_lit 33202044198037531293533812846338126366611635776896050360611072001 

noncomputable def Ns204p2074 := nat_lit 468357968242069192326958310349747577474847169564293388355920085739521 

noncomputable def Ns204p2075 := BSN.sin_dyadic_bound_f 116183807 134217728 3 2 134217728 67108864 Ns204p2072 Ns204p106 Ns204p2073 Ns204p2074 Ns204p109 Ns204p2073 102207897 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 116183807) qz361 0 2 Ns204p2072 Ns204p106 Ns204p2073 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 116183807) qz362 0 2 Ns204p2074 Ns204p109 Ns204p2073 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p2076 := nat_lit 6520384974193104063351412347136 

noncomputable def Ns204p2077 := BSN.sin_dyadic_bound_f 50532212 134217728 2 1 134217728 67108864 Ns204p2076 Ns204p129 Ns204p2076 Ns204p2076 Ns204p130 Ns204p2076 49346838 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 50532212) qz361 0 1 Ns204p2076 Ns204p129 Ns204p2076 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 50532212) qz362 0 1 Ns204p2076 Ns204p130 Ns204p2076 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p2078 := Ns204p2027 88573 BSN.abs_quadSignPos (BSN.cos_quad_nat3 31 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 102207897 134217728) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 81 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 49346838 134217728) (@Eq.refl Real qz254) rfl rfl (Ns204p2071 rfl rfl) (Ns204p2057 rfl) RS205to222.d27 RS205to222.d29 RS205to222.d31 RS205to222.d33 RS205to222.d17 (Ns204p2075 rfl rfl) (Ns204p2077 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns204p2079 := nat_lit 6803804382585228381779060266206609176306502345565930044912238206241 

noncomputable def Ns204p2080 := nat_lit 155734964679670501520709834812208882131913508104990467772521761 

noncomputable def Ns204p2081 := nat_lit 20411101677826325804334139378950203111155243209681580153801169575201 

noncomputable def Ns204p2082 := BSN.cos_dyadic_bound_f 59435821 134217728 3 2 134217728 67108864 Ns204p2079 Ns204p240 Ns204p2080 Ns204p2081 Ns204p243 Ns204p2080 121271360 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 59435821) qz363 0 2 Ns204p2079 Ns204p240 Ns204p2080 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 59435821) qz364 0 2 Ns204p2081 Ns204p243 Ns204p2080 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p2083 := Ns204p2025 Bool.true 58699460 88573 Bool.true 59435821 7074237752028440 1 Bool.false 121271360 Bool.false Bool.true 15823564 98727 BSN.abs_quadSignPos qz735 (BSN.sfrac_eq_quadSignPos_mul Bool.false 121271360 134217728) (@Eq.refl Real qz254) rfl (Ns204p2078 rfl) (Ns204p2057 rfl) RS205to222.d35 RS205to222.d37 RS205to222.d17 (Ns204p2082 rfl rfl) rfl 

noncomputable def Ns204p2084 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz254) qz254 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz254) qz254 8) 15823564 134217728 98727 134217728 15823564 134217728 98727 134217728 4247605617885184 3955891 16777216 98727 67108864 (Ns204p2083 rfl rfl rfl rfl) 

noncomputable def Ns204p2085 := @Enclosure.Real.IsNear.mulLit_ff qz792 (Zeta.RiemannSiegel.correction qz256) 5599601 16777216 1 16777216 1912353474255 2199023255552 3770464567899 87960930222080000 10708416426791772255 36893488147419103232 

noncomputable abbrev qz794 := (@HPow.hPow Real Real Real qz7 qz255 qz9)

noncomputable def Ns204p2086 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz794 1 1 0 1 5599601 16777216 1 16777216 5599601 16777216 1 16777216 

noncomputable def Ns204p2087 := @Enclosure.Real.IsNear.sqrt_image qz255 1351982709879 16777216000 506327 16777216000 75303548 75303577 8388608 (@Enclosure.Real.IsNear.of_eq qz255 (@HMul.hMul Real Real Real qz5 qz254 qz3) Bool.false 1351982709879 16777216000 506327 16777216000 (BSN.t_div_two_pi_mk qz254 506327 1000 (@Eq.refl Real qz254)) (@Enclosure.Real.IsNear.mulLit_ff qz254 qz3 506327 1000 0 1 2670177 16777216 1 16777216 1351982709879 16777216000 506327 16777216000 (Enclosure.Real.IsNear.const Bool.false 506327 1000) RS205to222.d40 rfl)) 

noncomputable abbrev qz924 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 506327 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz795 := qz924

noncomputable abbrev qz602 := qz795

noncomputable abbrev qz259 := qz602

noncomputable def Ns204p2088 := @Enclosure.Real.IsNear.sqrt_image qz259 150607125 16777216 29 16777216 25133482 25133488 8388608 (@Enclosure.Real.IsNear.recentre' qz259 Bool.false 150607125 16777216 29 16777216 150607125 16777216 29 16777216 (Ns204p2087 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns204p2089 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz259) 25133485 8388608 3 8388608 2799800 2799801 8388608 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz259) Bool.false 50266970 16777216 6 16777216 25133485 8388608 3 8388608 (Ns204p2088 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns204p2090 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz259)) Bool.false 5599601 16777216 1 16777216 5599601 16777216 1 16777216 (Ns204p2089 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz260 := (@HMul.hMul Real Real Real qz342 qz340 qz597)

noncomputable abbrev qz796 := (@HMul.hMul Real Real Real qz844 qz923 qz923)

noncomputable abbrev qz603 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz796 qz791) qz640)

noncomputable abbrev qz261 := (Real.cos (@HMul.hMul Real Real Real qz342 qz340 qz603))

noncomputable def Ns204p2091 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz256) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz260)) qz261) Bool.false 1912353474255 

noncomputable def Ns204p2092 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz260)) qz261 16955743 16777216 195 

noncomputable def Ns204p2093 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz260)) Bool.false 16955743 16777216 195 16777216 16955743 16777216 195 

noncomputable def Ns204p2094 := @Enclosure.Real.IsNear.recentre' (Real.cos qz260) Bool.false 16600569 16777216 485257216 42949672960000 16600569 16777216 118471 10485760000 

noncomputable def Ns204p2095 := @Enclosure.Real.IsNear.cos_image qz260 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51488809) qz359) Bool.false 51488809 8388608 183 16777216 Bool.false 16600569 16777216 1 

noncomputable def Ns204p2096 := nat_lit 782596187003061166432221067 

noncomputable def Ns204p2097 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz256 884279719003555 140737488355328 1 500000000000000 16389397 16777216 29 16777216 14492811373797707306335 2361183241434822606848 Ns204p2096 

noncomputable def Ns204p2098 := @Enclosure.Real.IsNear.subLit_ff_p qz259 qz1 150607125 16777216 29 16777216 8 1 0 1 16389397 16389397 16777216 29 

noncomputable def Ns204p2099 := @Ns204p2098 16777216 (@Enclosure.Real.IsNear.recentre' qz259 Bool.false 150607125 16777216 29 16777216 150607125 16777216 29 16777216 (Ns204p2087 rfl rfl rfl rfl rfl rfl) rfl) qz370 

noncomputable def Ns204p2100 := @Enclosure.Real.IsNear.recentre' qz260 Bool.false 14492811373797707306335 2361183241434822606848 Ns204p2096 Ns204p521 51488809 8388608 183 16777216 (@Ns204p2097 Ns204p521 RS205to222.d39 (Ns204p2099 rfl rfl) rfl) 

noncomputable def Ns204p2101 := nat_lit 1723390682382312855830528 

noncomputable def Ns204p2102 := nat_lit 24294593280143905188661122197276824999554780116713253167332017728329837423290130959489985 

noncomputable def Ns204p2103 := nat_lit 33133818239083508736131824502530726067426527880903317351900100126309860960547374685121 

noncomputable def Ns204p2104 := nat_lit 63575051456561235527587297086530444299486685927203724353014112935897453476585647239650241 

noncomputable def Ns204p2105 := BSN.sin_dyadic_bound_f 48981709209 34359738368 3 2 16777216 5125001 Ns204p2102 Ns204p1161 Ns204p2103 Ns204p2104 Ns204p1164 Ns204p2103 16600569 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 48981709209) qz357 0 2 Ns204p2102 Ns204p1161 Ns204p2103 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 48981709209) qz358 0 2 Ns204p2104 Ns204p1164 Ns204p2103 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p2106 := @Ns204p2095 2560000 (Ns204p2100 rfl) (Enclosure.sfrac_false_div 51488809 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51488809) qz359) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns204p2101) qz360) 226375608064910080 72057594037927936 Bool.false 16600569 16777216 0 1000000000000000 5120000 2560000 (BSN.sin_reduce_arg_pos_rat_q3 51488809 8388608 226375608064910080 72057594037927936 0 Ns204p2101 Ns204p100 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 16600569 16777216 Ns204p2101 Ns204p100 48981709209 34359738368 5125001 5120000 (Ns204p2105 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns204p2107 := @Enclosure.Real.IsNear.inv_image (Real.cos qz260) 16600569 16777216 118471 10485760000 8477774 8477969 8388608 (Ns204p2094 (Ns204p2106 rfl rfl) rfl) rfl 

noncomputable def Ns204p2108 := @Enclosure.Real.IsNear.recentre' qz261 Bool.false 7218240 8388608 

noncomputable abbrev qz262 := (@HMul.hMul Real Real Real qz342 qz340 qz603)

noncomputable def Ns204p2109 := @Enclosure.Real.IsNear.cos_image qz262 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 1121101)) qz372) Bool.true 1121101 2097152 

noncomputable def Ns204p2110 := nat_lit 21177000946189295270327432245 

noncomputable def Ns204p2111 := nat_lit 7756473431520803357643819096210921 

noncomputable def Ns204p2112 := @Enclosure.Real.IsNear.recentre' qz262 Bool.true Ns204p2110 Ns204p533 Ns204p2111 

noncomputable def Ns204p2113 := nat_lit 241785163922925834941235200000000000000 

noncomputable abbrev qz263 := qz603

noncomputable def Ns204p2114 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz263 884279719003555 140737488355328 1 500000000000000 23948305599559 

noncomputable abbrev qz604 := (@HSub.hSub Real Real Real qz634 qz796 qz791)

noncomputable abbrev qz264 := qz604

noncomputable def Ns204p2115 := @Enclosure.Real.IsNear.subLit_tf qz264 qz27 6356119555143 281474976710656 1437125131 281474976710656 1 16 

noncomputable abbrev qz605 := qz796

noncomputable abbrev qz265 := qz605

noncomputable def Ns204p2116 := @Enclosure.Real.IsNear.subLit_ff_n qz265 qz256 268612334023609 281474976710656 950585867 281474976710656 16389397 16777216 29 16777216 

noncomputable def Ns204p2117 := @Enclosure.Real.IsNear.mulLit_ff qz256 qz256 16389397 16777216 29 16777216 16389397 16777216 29 16777216 268612334023609 281474976710656 

noncomputable def Ns204p2118 := nat_lit 51336823042271359365223222202765327594816507091931681 

noncomputable def Ns204p2119 := nat_lit 2495501984765014970869947528733883684707370848801 

noncomputable def Ns204p2120 := nat_lit 154005478122844548065727926713238515017080106534097441 

noncomputable def Ns204p2121 := BSN.cos_dyadic_bound_f 1121101 2097152 3 2 8388608 2560000 Ns204p2118 Ns204p1805 Ns204p2119 Ns204p2120 Ns204p1808 Ns204p2119 7218240 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1121101) (BSN.cosEvenQ 2097152) 0 2 Ns204p2118 Ns204p1805 Ns204p2119 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1121101) (BSN.cosOddQ 2097152) 0 2 Ns204p2120 Ns204p1808 Ns204p2119 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns204p2122 := @Ns204p2108 1396617216 42949672960000 112785 131072 340971 10485760000 (@Ns204p2109 539 16777216 Bool.false 7218240 8388608 1 2560000 (@Ns204p2112 Ns204p2113 1121101 2097152 539 16777216 (@Ns204p2114 281474976710656 1437125131 281474976710656 Ns204p2110 Ns204p533 Ns204p2111 Ns204p2113 RS205to222.d39 (@Ns204p2115 0 1 383172889592944 23948305599559 281474976710656 1437125131 281474976710656 (@Ns204p2116 106637990698458021888 6356119555143 281474976710656 1437125131 281474976710656 (@Ns204p2117 950585867 281474976710656 (Ns204p2099 rfl rfl) (Ns204p2099 rfl rfl) rfl) (Ns204p2099 rfl rfl) rfl rfl) qz376 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 1121101 2097152) (BSN.cos_neg_of_bound 1121101 2097152 Bool.false 7218240 8388608 1 2560000 (Ns204p2121 rfl rfl)) rfl rfl) 

noncomputable def Ns204p2123 := @Ns204p2085 10594797537153288099 737869762948382064640000 (Ns204p2086 qz29 (@Enclosure.Real.IsNear.of_eq qz794 (@Inv.inv Real Real.instInv (Real.sqrt qz259)) Bool.false 5599601 16777216 1 16777216 (BSN.rpow_neg_quarter_mk qz255 (BSN.t_div_two_pi_nonneg qz254 506327 1000 (@Eq.refl Real qz254))) Ns204p2090) rfl) (@Ns204p2091 2199023255552 3770464567899 87960930222080000 (BSN.correction_mk qz256 (BSN.cos_two_pi_p_ne_zero_mk qz254 506327 1000 8 (@Eq.refl Real qz254) rfl rfl (@BSN.floor_sqrt_eq_dec qz254 506327 1000 8 (@Eq.refl Real qz254) rfl rfl rfl))) (@Ns204p2092 16777216 112785 131072 340971 10485760000 1912353474255 2199023255552 3770464567899 87960930222080000 (@Ns204p2093 16777216 (Ns204p2107 rfl rfl rfl rfl rfl) rfl) (Ns204p2122 rfl) rfl)) 

noncomputable def Ns204p2124 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz254) (hardyZApproximantRS₀ qz254) Bool.true 19407512732220629087 36893488147419103232 1096109642291564808099 737869762948382064640000 (@Eq.refl Real (hardyZApproximantRS₀ qz254)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz254) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz254) qz254 8) (@HMul.hMul Real Real Real qz5 qz792 (Zeta.RiemannSiegel.correction qz256))) Bool.true 19407512732220629087 36893488147419103232 1096109642291564808099 737869762948382064640000 (BSN.hardyZApproximantRS₀_eq qz254 8 (@BSN.floor_sqrt_eq_dec qz254 506327 1000 8 (@Eq.refl Real qz254) rfl rfl rfl)) (@Ns204p2024 19407512732220629087 36893488147419103232 1096109642291564808099 737869762948382064640000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz254) qz254 8) (@HAdd.hAdd Real Real Real qz356 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz254) qz254 8) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz254) qz254 8)) Bool.true 3955891 16777216 98727 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz254) qz254 8) (Ns204p2084 (Ns204p2083 rfl rfl rfl rfl) rfl rfl)) (Ns204p2123 rfl) rfl rfl)) 

theorem RS205to222.d61 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz254) Bool.true 19407512732220629087 36893488147419103232 1096109642291564808099 737869762948382064640000 := Ns204p2124 

noncomputable def RS205to222.d62 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz266 := (RS205to222.d3 qz341 qz377 (@Enclosure.dec_le_dec qz341 qz377 479682 1000 481854 1000 (@Eq.refl Real qz341) qz380 rfl rfl rfl))

noncomputable abbrev qz797 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz266)

noncomputable def Ns204p2125 := @Enclosure.Real.IsNear.of_eq qz797 (hardyZApproximantRS₀ qz4) Bool.true 367447779136059587143 73786976294838206464 564717556490842681979 368934881474191032320000 

noncomputable abbrev qz267 := (@Enclosure.dec_le_dec qz341 qz377 479682 1000 481854 1000 (@Eq.refl Real qz341) qz380 rfl rfl rfl)

noncomputable def Ns204p2126 := @Enclosure.Real.IsNear.neg_val qz797 367447779136059587143 73786976294838206464 564717556490842681979 368934881474191032320000 (Ns204p2125 (RS205to222.d4 qz4 qz30 qz267) RS205to222.d41) rfl 

noncomputable abbrev qz798 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz266)

noncomputable def Ns204p2127 := @Enclosure.Real.IsNear.of_eq qz798 (hardyZApproximantRS₀ qz30) Bool.false 122560259979430957345 1180591620717411303424 1210669580750857845169 737869762948382064640000 

noncomputable def Ns204p2128 := @Enclosure.Real.IsNear.pos_val qz798 122560259979430957345 1180591620717411303424 1210669580750857845169 737869762948382064640000 (Ns204p2127 (RS205to222.d42 qz4 qz30 qz267) RS205to222.d43) rfl 

noncomputable def Ns204p2129 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz797 qz4 qz4 479682 1000 479682 1000 

noncomputable def Ns204p2130 := @Enclosure.norm_gt_of_isNear qz797 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 367447779136059587143 73786976294838206464 564717556490842681979 

noncomputable def Ns204p2131 := @Ns204p2130 368934881474191032320000 209459933 2684354560 1213 2684354560 (Ns204p2125 (RS205to222.d4 qz4 qz30 qz267) RS205to222.d41) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2132 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz798 qz4 qz30 479682 1000 481854 1000 

noncomputable def Ns204p2133 := @Enclosure.norm_gt_of_isNear qz798 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 122560259979430957345 1180591620717411303424 1210669580750857845169 

noncomputable def Ns204p2134 := @Ns204p2133 737869762948382064640000 209459933 2684354560 1213 2684354560 (Ns204p2127 (RS205to222.d42 qz4 qz30 qz267) RS205to222.d43) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2135 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz266 (@BSN.thirtyTwoPi_le_dec qz4 479682 1000 qz11 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz797 qz798 (Ns204p2126 rfl rfl) (Ns204p2128 rfl rfl)) (Ns204p2129 qz11 qz11 rfl rfl rfl rfl (Ns204p2131 rfl)) (Ns204p2132 qz11 qz33 rfl rfl rfl rfl (Ns204p2134 rfl)) 

noncomputable abbrev qz268 := (RS205to222.d3 qz377 qz397 (@Enclosure.dec_le_dec qz377 qz397 481854 1000 483302 1000 qz380 qz400 rfl rfl rfl))

noncomputable abbrev qz799 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz268)

noncomputable def Ns204p2136 := @Enclosure.Real.IsNear.of_eq qz799 (hardyZApproximantRS₀ qz30) Bool.false 122560259979430957345 1180591620717411303424 1210669580750857845169 737869762948382064640000 

noncomputable abbrev qz269 := (@Enclosure.dec_le_dec qz377 qz397 481854 1000 483302 1000 qz380 qz400 rfl rfl rfl)

noncomputable def Ns204p2137 := @Enclosure.Real.IsNear.pos_val qz799 122560259979430957345 1180591620717411303424 1210669580750857845169 737869762948382064640000 (Ns204p2136 (RS205to222.d4 qz30 qz49 qz269) RS205to222.d43) rfl 

noncomputable abbrev qz800 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz268)

noncomputable def Ns204p2138 := @Enclosure.Real.IsNear.of_eq qz800 (hardyZApproximantRS₀ qz49) Bool.true 880868339257658441267 1180591620717411303424 1100195248531108684061 737869762948382064640000 

noncomputable def Ns204p2139 := @Enclosure.Real.IsNear.neg_val qz800 880868339257658441267 1180591620717411303424 1100195248531108684061 737869762948382064640000 (Ns204p2138 (RS205to222.d42 qz30 qz49 qz269) RS205to222.d45) rfl 

noncomputable def Ns204p2140 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz799 qz4 qz30 479682 1000 481854 1000 

noncomputable def Ns204p2141 := @Enclosure.norm_gt_of_isNear qz799 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 122560259979430957345 1180591620717411303424 1210669580750857845169 

noncomputable def Ns204p2142 := @Ns204p2141 737869762948382064640000 209459933 2684354560 1213 2684354560 (Ns204p2136 (RS205to222.d4 qz30 qz49 qz269) RS205to222.d43) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2143 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz800 qz4 qz49 479682 1000 483302 1000 

noncomputable def Ns204p2144 := @Enclosure.norm_gt_of_isNear qz800 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 880868339257658441267 1180591620717411303424 1100195248531108684061 

noncomputable def Ns204p2145 := @Ns204p2144 737869762948382064640000 209459933 2684354560 1213 2684354560 (Ns204p2138 (RS205to222.d42 qz30 qz49 qz269) RS205to222.d45) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2146 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz268 (@BSN.thirtyTwoPi_le_dec qz30 481854 1000 qz33 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz799 qz800 (Ns204p2137 rfl rfl) (Ns204p2139 rfl rfl)) (Ns204p2140 qz11 qz33 rfl rfl rfl rfl (Ns204p2142 rfl)) (Ns204p2143 qz11 qz52 rfl rfl rfl rfl (Ns204p2145 rfl)) 

noncomputable abbrev qz270 := (RS205to222.d3 qz397 qz409 (@Enclosure.dec_le_dec qz397 qz409 483302 1000 484748 1000 qz400 qz412 rfl rfl rfl))

noncomputable abbrev qz801 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz270)

noncomputable def Ns204p2147 := @Enclosure.Real.IsNear.of_eq qz801 (hardyZApproximantRS₀ qz49) Bool.true 880868339257658441267 1180591620717411303424 1100195248531108684061 737869762948382064640000 

noncomputable abbrev qz271 := (@Enclosure.dec_le_dec qz397 qz409 483302 1000 484748 1000 qz400 qz412 rfl rfl rfl)

noncomputable def Ns204p2148 := @Enclosure.Real.IsNear.neg_val qz801 880868339257658441267 1180591620717411303424 1100195248531108684061 737869762948382064640000 (Ns204p2147 (RS205to222.d4 qz49 qz62 qz271) RS205to222.d45) rfl 

noncomputable abbrev qz802 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz270)

noncomputable def Ns204p2149 := @Enclosure.Real.IsNear.of_eq qz802 (hardyZApproximantRS₀ qz62) Bool.false 544229738210087335747 295147905179352825856 1080419603514473244403 737869762948382064640000 

noncomputable def Ns204p2150 := @Enclosure.Real.IsNear.pos_val qz802 544229738210087335747 295147905179352825856 1080419603514473244403 737869762948382064640000 (Ns204p2149 (RS205to222.d42 qz49 qz62 qz271) RS205to222.d46) rfl 

noncomputable def Ns204p2151 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz801 qz4 qz49 479682 1000 483302 1000 

noncomputable def Ns204p2152 := @Enclosure.norm_gt_of_isNear qz801 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 880868339257658441267 1180591620717411303424 1100195248531108684061 

noncomputable def Ns204p2153 := @Ns204p2152 737869762948382064640000 209459933 2684354560 1213 2684354560 (Ns204p2147 (RS205to222.d4 qz49 qz62 qz271) RS205to222.d45) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2154 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz802 qz4 qz62 479682 1000 484748 1000 

noncomputable def Ns204p2155 := @Enclosure.norm_gt_of_isNear qz802 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 544229738210087335747 295147905179352825856 1080419603514473244403 

noncomputable def Ns204p2156 := @Ns204p2155 737869762948382064640000 209459933 2684354560 1213 2684354560 (Ns204p2149 (RS205to222.d42 qz49 qz62 qz271) RS205to222.d46) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2157 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz270 (@BSN.thirtyTwoPi_le_dec qz49 483302 1000 qz52 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz801 qz802 (Ns204p2148 rfl rfl) (Ns204p2150 rfl rfl)) (Ns204p2151 qz11 qz52 rfl rfl rfl rfl (Ns204p2153 rfl)) (Ns204p2154 qz11 qz65 rfl rfl rfl rfl (Ns204p2156 rfl)) 

noncomputable abbrev qz272 := (RS205to222.d3 qz409 qz421 (@Enclosure.dec_le_dec qz409 qz421 484748 1000 486193 1000 qz412 qz424 rfl rfl rfl))

noncomputable abbrev qz803 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz272)

noncomputable def Ns204p2158 := @Enclosure.Real.IsNear.of_eq qz803 (hardyZApproximantRS₀ qz62) Bool.false 544229738210087335747 295147905179352825856 1080419603514473244403 737869762948382064640000 

noncomputable abbrev qz273 := (@Enclosure.dec_le_dec qz409 qz421 484748 1000 486193 1000 qz412 qz424 rfl rfl rfl)

noncomputable def Ns204p2159 := @Enclosure.Real.IsNear.pos_val qz803 544229738210087335747 295147905179352825856 1080419603514473244403 737869762948382064640000 (Ns204p2158 (RS205to222.d4 qz62 qz75 qz273) RS205to222.d46) rfl 

noncomputable abbrev qz804 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz272)

noncomputable def Ns204p2160 := @Enclosure.Real.IsNear.of_eq qz804 (hardyZApproximantRS₀ qz75) Bool.true 488362995125545633449 590295810358705651712 536295742741986200787 368934881474191032320000 

noncomputable def Ns204p2161 := @Enclosure.Real.IsNear.neg_val qz804 488362995125545633449 590295810358705651712 536295742741986200787 368934881474191032320000 (Ns204p2160 (RS205to222.d42 qz62 qz75 qz273) RS205to222.d47) rfl 

noncomputable def Ns204p2162 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz803 qz4 qz62 479682 1000 484748 1000 

noncomputable def Ns204p2163 := @Enclosure.norm_gt_of_isNear qz803 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 544229738210087335747 295147905179352825856 1080419603514473244403 

noncomputable def Ns204p2164 := @Ns204p2163 737869762948382064640000 209459933 2684354560 1213 2684354560 (Ns204p2158 (RS205to222.d4 qz62 qz75 qz273) RS205to222.d46) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2165 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz804 qz4 qz75 479682 1000 486193 1000 

noncomputable def Ns204p2166 := @Enclosure.norm_gt_of_isNear qz804 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 488362995125545633449 590295810358705651712 536295742741986200787 

noncomputable def Ns204p2167 := @Ns204p2166 368934881474191032320000 209459933 2684354560 1213 2684354560 (Ns204p2160 (RS205to222.d42 qz62 qz75 qz273) RS205to222.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2168 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz272 (@BSN.thirtyTwoPi_le_dec qz62 484748 1000 qz65 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz803 qz804 (Ns204p2159 rfl rfl) (Ns204p2161 rfl rfl)) (Ns204p2162 qz11 qz65 rfl rfl rfl rfl (Ns204p2164 rfl)) (Ns204p2165 qz11 qz78 rfl rfl rfl rfl (Ns204p2167 rfl)) 

noncomputable abbrev qz274 := (RS205to222.d3 qz421 qz433 (@Enclosure.dec_le_dec qz421 qz433 486193 1000 487638 1000 qz424 qz436 rfl rfl rfl))

noncomputable abbrev qz805 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz274)

noncomputable def Ns204p2169 := @Enclosure.Real.IsNear.of_eq qz805 (hardyZApproximantRS₀ qz75) Bool.true 488362995125545633449 590295810358705651712 536295742741986200787 368934881474191032320000 

noncomputable abbrev qz275 := (@Enclosure.dec_le_dec qz421 qz433 486193 1000 487638 1000 qz424 qz436 rfl rfl rfl)

noncomputable def Ns204p2170 := @Enclosure.Real.IsNear.neg_val qz805 488362995125545633449 590295810358705651712 536295742741986200787 368934881474191032320000 (Ns204p2169 (RS205to222.d4 qz75 qz88 qz275) RS205to222.d47) rfl 

noncomputable abbrev qz806 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz274)

noncomputable def Ns204p2171 := @Enclosure.Real.IsNear.of_eq qz806 (hardyZApproximantRS₀ qz88) Bool.false 3534503777538553622553 1180591620717411303424 1711316274688458451 1180591620717411303424 

noncomputable def Ns204p2172 := @Enclosure.Real.IsNear.pos_val qz806 3534503777538553622553 1180591620717411303424 1711316274688458451 1180591620717411303424 (Ns204p2171 (RS205to222.d42 qz75 qz88 qz275) RS205to222.d48) rfl 

noncomputable def Ns204p2173 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz805 qz4 qz75 479682 1000 486193 1000 

noncomputable def Ns204p2174 := @Enclosure.norm_gt_of_isNear qz805 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 488362995125545633449 590295810358705651712 536295742741986200787 

noncomputable def Ns204p2175 := @Ns204p2174 368934881474191032320000 209459933 2684354560 1213 2684354560 (Ns204p2169 (RS205to222.d4 qz75 qz88 qz275) RS205to222.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2176 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz806 qz4 qz88 479682 1000 487638 1000 

noncomputable def Ns204p2177 := @Enclosure.norm_gt_of_isNear qz806 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 3534503777538553622553 1180591620717411303424 1711316274688458451 

noncomputable def Ns204p2178 := @Ns204p2177 1180591620717411303424 209459933 2684354560 1213 2684354560 (Ns204p2171 (RS205to222.d42 qz75 qz88 qz275) RS205to222.d48) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2179 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz274 (@BSN.thirtyTwoPi_le_dec qz75 486193 1000 qz78 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz805 qz806 (Ns204p2170 rfl rfl) (Ns204p2172 rfl rfl)) (Ns204p2173 qz11 qz78 rfl rfl rfl rfl (Ns204p2175 rfl)) (Ns204p2176 qz11 qz91 rfl rfl rfl rfl (Ns204p2178 rfl)) 

noncomputable abbrev qz276 := (RS205to222.d3 qz433 qz445 (@Enclosure.dec_le_dec qz433 qz445 487638 1000 489081 1000 qz436 qz448 rfl rfl rfl))

noncomputable abbrev qz807 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz276)

noncomputable def Ns204p2180 := @Enclosure.Real.IsNear.of_eq qz807 (hardyZApproximantRS₀ qz88) Bool.false 3534503777538553622553 1180591620717411303424 1711316274688458451 1180591620717411303424 

noncomputable abbrev qz277 := (@Enclosure.dec_le_dec qz433 qz445 487638 1000 489081 1000 qz436 qz448 rfl rfl rfl)

noncomputable def Ns204p2181 := @Enclosure.Real.IsNear.pos_val qz807 3534503777538553622553 1180591620717411303424 1711316274688458451 1180591620717411303424 (Ns204p2180 (RS205to222.d4 qz88 qz101 qz277) RS205to222.d48) rfl 

noncomputable abbrev qz808 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz276)

noncomputable def Ns204p2182 := @Enclosure.Real.IsNear.of_eq qz808 (hardyZApproximantRS₀ qz101) Bool.true 2366994557652976530929 1180591620717411303424 26720966700676131393 18446744073709551616000 

noncomputable def Ns204p2183 := @Enclosure.Real.IsNear.neg_val qz808 2366994557652976530929 1180591620717411303424 26720966700676131393 18446744073709551616000 (Ns204p2182 (RS205to222.d42 qz88 qz101 qz277) RS205to222.d49) rfl 

noncomputable def Ns204p2184 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz807 qz4 qz88 479682 1000 487638 1000 

noncomputable def Ns204p2185 := @Enclosure.norm_gt_of_isNear qz807 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 3534503777538553622553 1180591620717411303424 1711316274688458451 

noncomputable def Ns204p2186 := @Ns204p2185 1180591620717411303424 209459933 2684354560 1213 2684354560 (Ns204p2180 (RS205to222.d4 qz88 qz101 qz277) RS205to222.d48) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2187 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz808 qz4 qz101 479682 1000 489081 1000 

noncomputable def Ns204p2188 := @Enclosure.norm_gt_of_isNear qz808 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2366994557652976530929 1180591620717411303424 26720966700676131393 

noncomputable def Ns204p2189 := @Ns204p2188 18446744073709551616000 209459933 2684354560 1213 2684354560 (Ns204p2182 (RS205to222.d42 qz88 qz101 qz277) RS205to222.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2190 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz276 (@BSN.thirtyTwoPi_le_dec qz88 487638 1000 qz91 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz807 qz808 (Ns204p2181 rfl rfl) (Ns204p2183 rfl rfl)) (Ns204p2184 qz11 qz91 rfl rfl rfl rfl (Ns204p2186 rfl)) (Ns204p2187 qz11 qz104 rfl rfl rfl rfl (Ns204p2189 rfl)) 

noncomputable abbrev qz606 := (@Enclosure.dec_le_dec qz685 qz693 489081 1000 490524 1000 (@Eq.refl Real qz685) (@Eq.refl Real qz693) rfl rfl rfl)

noncomputable abbrev qz278 := (RS205to222.d3 qz445 qz457 qz606)

noncomputable abbrev qz809 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz278)

noncomputable def Ns204p2191 := @Enclosure.Real.IsNear.of_eq qz809 (hardyZApproximantRS₀ qz101) Bool.true 2366994557652976530929 1180591620717411303424 26720966700676131393 18446744073709551616000 

noncomputable abbrev qz279 := qz606

noncomputable def Ns204p2192 := @Enclosure.Real.IsNear.neg_val qz809 2366994557652976530929 1180591620717411303424 26720966700676131393 18446744073709551616000 (Ns204p2191 (RS205to222.d4 qz101 qz114 qz279) RS205to222.d49) rfl 

noncomputable abbrev qz810 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz278)

noncomputable def Ns204p2193 := @Enclosure.Real.IsNear.of_eq qz810 (hardyZApproximantRS₀ qz114) Bool.false 4102407237536825619333 1180591620717411303424 1068757189566166323461 737869762948382064640000 

noncomputable def Ns204p2194 := @Enclosure.Real.IsNear.pos_val qz810 4102407237536825619333 1180591620717411303424 1068757189566166323461 737869762948382064640000 (Ns204p2193 (RS205to222.d42 qz101 qz114 qz279) RS205to222.d50) rfl 

noncomputable def Ns204p2195 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz809 qz4 qz101 479682 1000 489081 1000 

noncomputable def Ns204p2196 := @Enclosure.norm_gt_of_isNear qz809 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2366994557652976530929 1180591620717411303424 26720966700676131393 

noncomputable def Ns204p2197 := @Ns204p2196 18446744073709551616000 209459933 2684354560 1213 2684354560 (Ns204p2191 (RS205to222.d4 qz101 qz114 qz279) RS205to222.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2198 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz810 qz4 qz114 479682 1000 490524 1000 

noncomputable def Ns204p2199 := @Enclosure.norm_gt_of_isNear qz810 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 4102407237536825619333 1180591620717411303424 1068757189566166323461 

noncomputable def Ns204p2200 := @Ns204p2199 737869762948382064640000 209459933 2684354560 1213 2684354560 (Ns204p2193 (RS205to222.d42 qz101 qz114 qz279) RS205to222.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2201 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz278 (@BSN.thirtyTwoPi_le_dec qz101 489081 1000 qz104 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz809 qz810 (Ns204p2192 rfl rfl) (Ns204p2194 rfl rfl)) (Ns204p2195 qz11 qz104 rfl rfl rfl rfl (Ns204p2197 rfl)) (Ns204p2198 qz11 qz117 rfl rfl rfl rfl (Ns204p2200 rfl)) 

noncomputable abbrev qz607 := (@Enclosure.dec_le_dec qz693 qz701 490524 1000 491965 1000 (@Eq.refl Real qz693) qz705 rfl rfl rfl)

noncomputable abbrev qz280 := (RS205to222.d3 qz457 qz469 qz607)

noncomputable abbrev qz811 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz280)

noncomputable def Ns204p2202 := @Enclosure.Real.IsNear.of_eq qz811 (hardyZApproximantRS₀ qz114) Bool.false 4102407237536825619333 1180591620717411303424 1068757189566166323461 737869762948382064640000 

noncomputable abbrev qz281 := qz607

noncomputable def Ns204p2203 := @Enclosure.Real.IsNear.pos_val qz811 4102407237536825619333 1180591620717411303424 1068757189566166323461 737869762948382064640000 (Ns204p2202 (RS205to222.d4 qz114 qz127 qz281) RS205to222.d50) rfl 

noncomputable abbrev qz812 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz280)

noncomputable def Ns204p2204 := @Enclosure.Real.IsNear.of_eq qz812 (hardyZApproximantRS₀ qz127) Bool.true 394372092145088557355 147573952589676412928 26763370336199055951 18446744073709551616000 

noncomputable def Ns204p2205 := @Enclosure.Real.IsNear.neg_val qz812 394372092145088557355 147573952589676412928 26763370336199055951 18446744073709551616000 (Ns204p2204 (RS205to222.d42 qz114 qz127 qz281) RS205to222.d51) rfl 

noncomputable def Ns204p2206 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz811 qz4 qz114 479682 1000 490524 1000 

noncomputable def Ns204p2207 := @Enclosure.norm_gt_of_isNear qz811 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 4102407237536825619333 1180591620717411303424 1068757189566166323461 

noncomputable def Ns204p2208 := @Ns204p2207 737869762948382064640000 209459933 2684354560 1213 2684354560 (Ns204p2202 (RS205to222.d4 qz114 qz127 qz281) RS205to222.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2209 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz812 qz4 qz127 479682 1000 491965 1000 

noncomputable def Ns204p2210 := @Enclosure.norm_gt_of_isNear qz812 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 394372092145088557355 147573952589676412928 26763370336199055951 

noncomputable def Ns204p2211 := @Ns204p2210 18446744073709551616000 209459933 2684354560 1213 2684354560 (Ns204p2204 (RS205to222.d42 qz114 qz127 qz281) RS205to222.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2212 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz280 (@BSN.thirtyTwoPi_le_dec qz114 490524 1000 qz117 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz811 qz812 (Ns204p2203 rfl rfl) (Ns204p2205 rfl rfl)) (Ns204p2206 qz11 qz117 rfl rfl rfl rfl (Ns204p2208 rfl)) (Ns204p2209 qz11 qz130 rfl rfl rfl rfl (Ns204p2211 rfl)) 

noncomputable abbrev qz608 := (@Enclosure.dec_le_dec qz701 qz710 491965 1000 493405 1000 qz705 qz714 rfl rfl rfl)

noncomputable abbrev qz282 := (RS205to222.d3 qz469 qz481 qz608)

noncomputable abbrev qz813 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz282)

noncomputable def Ns204p2213 := @Enclosure.Real.IsNear.of_eq qz813 (hardyZApproximantRS₀ qz127) Bool.true 394372092145088557355 147573952589676412928 26763370336199055951 18446744073709551616000 

noncomputable abbrev qz283 := qz608

noncomputable def Ns204p2214 := @Enclosure.Real.IsNear.neg_val qz813 394372092145088557355 147573952589676412928 26763370336199055951 18446744073709551616000 (Ns204p2213 (RS205to222.d4 qz127 qz140 qz283) RS205to222.d51) rfl 

noncomputable abbrev qz814 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz282)

noncomputable def Ns204p2215 := @Enclosure.Real.IsNear.of_eq qz814 (hardyZApproximantRS₀ qz140) Bool.false 372299197319286849833 2361183241434822606848 428914682377335836819 295147905179352825856000 

noncomputable def Ns204p2216 := @Enclosure.Real.IsNear.pos_val qz814 372299197319286849833 2361183241434822606848 428914682377335836819 295147905179352825856000 (Ns204p2215 (RS205to222.d42 qz127 qz140 qz283) RS205to222.d52) rfl 

noncomputable def Ns204p2217 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz813 qz4 qz127 479682 1000 491965 1000 

noncomputable def Ns204p2218 := @Enclosure.norm_gt_of_isNear qz813 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 394372092145088557355 147573952589676412928 26763370336199055951 

noncomputable def Ns204p2219 := @Ns204p2218 18446744073709551616000 209459933 2684354560 1213 2684354560 (Ns204p2213 (RS205to222.d4 qz127 qz140 qz283) RS205to222.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2220 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz814 qz4 qz140 479682 1000 493405 1000 

noncomputable def Ns204p2221 := @Enclosure.norm_gt_of_isNear qz814 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 372299197319286849833 2361183241434822606848 428914682377335836819 

noncomputable def Ns204p2222 := @Ns204p2221 295147905179352825856000 209459933 2684354560 1213 2684354560 (Ns204p2215 (RS205to222.d42 qz127 qz140 qz283) RS205to222.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2223 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz282 (@BSN.thirtyTwoPi_le_dec qz127 491965 1000 qz130 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz813 qz814 (Ns204p2214 rfl rfl) (Ns204p2216 rfl rfl)) (Ns204p2217 qz11 qz130 rfl rfl rfl rfl (Ns204p2219 rfl)) (Ns204p2220 qz11 qz143 rfl rfl rfl rfl (Ns204p2222 rfl)) 

noncomputable abbrev qz815 := (@Enclosure.dec_le_dec qz882 qz886 493405 1000 494845 1000 (@Eq.refl Real qz882) qz889 rfl rfl rfl)

noncomputable abbrev qz609 := qz815

noncomputable abbrev qz284 := (RS205to222.d3 qz481 qz493 qz609)

noncomputable abbrev qz816 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz284)

noncomputable def Ns204p2224 := @Enclosure.Real.IsNear.of_eq qz816 (hardyZApproximantRS₀ qz140) Bool.false 372299197319286849833 2361183241434822606848 428914682377335836819 295147905179352825856000 

noncomputable abbrev qz285 := qz609

noncomputable def Ns204p2225 := @Enclosure.Real.IsNear.pos_val qz816 372299197319286849833 2361183241434822606848 428914682377335836819 295147905179352825856000 (Ns204p2224 (RS205to222.d4 qz140 qz153 qz285) RS205to222.d52) rfl 

noncomputable abbrev qz817 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz284)

noncomputable def Ns204p2226 := @Enclosure.Real.IsNear.of_eq qz817 (hardyZApproximantRS₀ qz153) Bool.true 302833711432141261375 295147905179352825856 53718699445700205087 36893488147419103232000 

noncomputable def Ns204p2227 := @Enclosure.Real.IsNear.neg_val qz817 302833711432141261375 295147905179352825856 53718699445700205087 36893488147419103232000 (Ns204p2226 (RS205to222.d42 qz140 qz153 qz285) RS205to222.d53) rfl 

noncomputable def Ns204p2228 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz816 qz4 qz140 479682 1000 493405 1000 

noncomputable def Ns204p2229 := @Enclosure.norm_gt_of_isNear qz816 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 372299197319286849833 2361183241434822606848 428914682377335836819 

noncomputable def Ns204p2230 := @Ns204p2229 295147905179352825856000 209459933 2684354560 1213 2684354560 (Ns204p2224 (RS205to222.d4 qz140 qz153 qz285) RS205to222.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2231 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz817 qz4 qz153 479682 1000 494845 1000 

noncomputable def Ns204p2232 := @Enclosure.norm_gt_of_isNear qz817 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 302833711432141261375 295147905179352825856 53718699445700205087 

noncomputable def Ns204p2233 := @Ns204p2232 36893488147419103232000 209459933 2684354560 1213 2684354560 (Ns204p2226 (RS205to222.d42 qz140 qz153 qz285) RS205to222.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2234 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz140 493405 1000 qz143 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz816 qz817 (Ns204p2225 rfl rfl) (Ns204p2227 rfl rfl)) (Ns204p2228 qz11 qz143 rfl rfl rfl rfl (Ns204p2230 rfl)) (Ns204p2231 qz11 qz156 rfl rfl rfl rfl (Ns204p2233 rfl)) 

noncomputable abbrev qz925 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 494845 1000) (Enclosure.sfrac Bool.false 496283 1000) 494845 1000 496283 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 494845 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 496283 1000)) rfl rfl rfl)

noncomputable abbrev qz818 := qz925

noncomputable abbrev qz610 := qz818

noncomputable abbrev qz286 := (RS205to222.d3 qz493 qz505 qz610)

noncomputable abbrev qz819 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz286)

noncomputable def Ns204p2235 := @Enclosure.Real.IsNear.of_eq qz819 (hardyZApproximantRS₀ qz153) Bool.true 302833711432141261375 295147905179352825856 53718699445700205087 36893488147419103232000 

noncomputable abbrev qz287 := qz610

noncomputable def Ns204p2236 := @Enclosure.Real.IsNear.neg_val qz819 302833711432141261375 295147905179352825856 53718699445700205087 36893488147419103232000 (Ns204p2235 (RS205to222.d4 qz153 qz166 qz287) RS205to222.d53) rfl 

noncomputable abbrev qz820 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz286)

noncomputable def Ns204p2237 := @Enclosure.Real.IsNear.of_eq qz820 (hardyZApproximantRS₀ qz166) Bool.false 163172404364062198519 295147905179352825856 269144639316076302967 184467440737095516160000 

noncomputable def Ns204p2238 := @Enclosure.Real.IsNear.pos_val qz820 163172404364062198519 295147905179352825856 269144639316076302967 184467440737095516160000 (Ns204p2237 (RS205to222.d42 qz153 qz166 qz287) RS205to222.d54) rfl 

noncomputable def Ns204p2239 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz819 qz4 qz153 479682 1000 494845 1000 

noncomputable def Ns204p2240 := @Enclosure.norm_gt_of_isNear qz819 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 302833711432141261375 295147905179352825856 53718699445700205087 

noncomputable def Ns204p2241 := @Ns204p2240 36893488147419103232000 209459933 2684354560 1213 2684354560 (Ns204p2235 (RS205to222.d4 qz153 qz166 qz287) RS205to222.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2242 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz820 qz4 qz166 479682 1000 496283 1000 

noncomputable def Ns204p2243 := @Enclosure.norm_gt_of_isNear qz820 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 163172404364062198519 295147905179352825856 269144639316076302967 

noncomputable def Ns204p2244 := @Ns204p2243 184467440737095516160000 209459933 2684354560 1213 2684354560 (Ns204p2237 (RS205to222.d42 qz153 qz166 qz287) RS205to222.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2245 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz286 (@BSN.thirtyTwoPi_le_dec qz153 494845 1000 qz156 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz819 qz820 (Ns204p2236 rfl rfl) (Ns204p2238 rfl rfl)) (Ns204p2239 qz11 qz156 rfl rfl rfl rfl (Ns204p2241 rfl)) (Ns204p2242 qz11 qz169 rfl rfl rfl rfl (Ns204p2244 rfl)) 

noncomputable abbrev qz288 := (RS205to222.d3 qz505 qz518 (@Enclosure.dec_le_dec qz505 qz518 496283 1000 497721 1000 qz508 qz521 rfl rfl rfl))

noncomputable abbrev qz821 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz288)

noncomputable def Ns204p2246 := @Enclosure.Real.IsNear.of_eq qz821 (hardyZApproximantRS₀ qz166) Bool.false 163172404364062198519 295147905179352825856 269144639316076302967 184467440737095516160000 

noncomputable abbrev qz289 := (@Enclosure.dec_le_dec qz505 qz518 496283 1000 497721 1000 qz508 qz521 rfl rfl rfl)

noncomputable def Ns204p2247 := @Enclosure.Real.IsNear.pos_val qz821 163172404364062198519 295147905179352825856 269144639316076302967 184467440737095516160000 (Ns204p2246 (RS205to222.d4 qz166 qz178 qz289) RS205to222.d54) rfl 

noncomputable abbrev qz822 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz288)

noncomputable def Ns204p2248 := @Enclosure.Real.IsNear.of_eq qz822 (hardyZApproximantRS₀ qz178) Bool.true 3041181834834782036091 590295810358705651712 539520535569759194621 368934881474191032320000 

noncomputable def Ns204p2249 := @Enclosure.Real.IsNear.neg_val qz822 3041181834834782036091 590295810358705651712 539520535569759194621 368934881474191032320000 (Ns204p2248 (RS205to222.d42 qz166 qz178 qz289) RS205to222.d55) rfl 

noncomputable def Ns204p2250 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz821 qz4 qz166 479682 1000 496283 1000 

noncomputable def Ns204p2251 := @Enclosure.norm_gt_of_isNear qz821 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 163172404364062198519 295147905179352825856 269144639316076302967 

noncomputable def Ns204p2252 := @Ns204p2251 184467440737095516160000 209459933 2684354560 1213 2684354560 (Ns204p2246 (RS205to222.d4 qz166 qz178 qz289) RS205to222.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2253 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz822 qz4 qz178 479682 1000 497721 1000 

noncomputable def Ns204p2254 := @Enclosure.norm_gt_of_isNear qz822 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 3041181834834782036091 590295810358705651712 539520535569759194621 

noncomputable def Ns204p2255 := @Ns204p2254 368934881474191032320000 209459933 2684354560 1213 2684354560 (Ns204p2248 (RS205to222.d42 qz166 qz178 qz289) RS205to222.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2256 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz166 496283 1000 qz169 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz821 qz822 (Ns204p2247 rfl rfl) (Ns204p2249 rfl rfl)) (Ns204p2250 qz11 qz169 rfl rfl rfl rfl (Ns204p2252 rfl)) (Ns204p2253 qz11 qz181 rfl rfl rfl rfl (Ns204p2255 rfl)) 

noncomputable abbrev qz290 := (RS205to222.d3 qz518 qz531 (@Enclosure.dec_le_dec qz518 qz531 497721 1000 499158 1000 qz521 qz534 rfl rfl rfl))

noncomputable abbrev qz823 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz290)

noncomputable def Ns204p2257 := @Enclosure.Real.IsNear.of_eq qz823 (hardyZApproximantRS₀ qz178) Bool.true 3041181834834782036091 590295810358705651712 539520535569759194621 368934881474191032320000 

noncomputable abbrev qz291 := (@Enclosure.dec_le_dec qz518 qz531 497721 1000 499158 1000 qz521 qz534 rfl rfl rfl)

noncomputable def Ns204p2258 := @Enclosure.Real.IsNear.neg_val qz823 3041181834834782036091 590295810358705651712 539520535569759194621 368934881474191032320000 (Ns204p2257 (RS205to222.d4 qz178 qz190 qz291) RS205to222.d55) rfl 

noncomputable abbrev qz824 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz290)

noncomputable def Ns204p2259 := @Enclosure.Real.IsNear.of_eq qz824 (hardyZApproximantRS₀ qz190) Bool.false 119148331690512275483 36893488147419103232 67600750889428828757 46116860184273879040000 

noncomputable def Ns204p2260 := @Enclosure.Real.IsNear.pos_val qz824 119148331690512275483 36893488147419103232 67600750889428828757 46116860184273879040000 (Ns204p2259 (RS205to222.d42 qz178 qz190 qz291) RS205to222.d56) rfl 

noncomputable def Ns204p2261 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz823 qz4 qz178 479682 1000 497721 1000 

noncomputable def Ns204p2262 := @Enclosure.norm_gt_of_isNear qz823 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 3041181834834782036091 590295810358705651712 539520535569759194621 

noncomputable def Ns204p2263 := @Ns204p2262 368934881474191032320000 209459933 2684354560 1213 2684354560 (Ns204p2257 (RS205to222.d4 qz178 qz190 qz291) RS205to222.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2264 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz824 qz4 qz190 479682 1000 499158 1000 

noncomputable def Ns204p2265 := @Enclosure.norm_gt_of_isNear qz824 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 119148331690512275483 36893488147419103232 67600750889428828757 

noncomputable def Ns204p2266 := @Ns204p2265 46116860184273879040000 209459933 2684354560 1213 2684354560 (Ns204p2259 (RS205to222.d42 qz178 qz190 qz291) RS205to222.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2267 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz290 (@BSN.thirtyTwoPi_le_dec qz178 497721 1000 qz181 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz823 qz824 (Ns204p2258 rfl rfl) (Ns204p2260 rfl rfl)) (Ns204p2261 qz11 qz181 rfl rfl rfl rfl (Ns204p2263 rfl)) (Ns204p2264 qz11 qz193 rfl rfl rfl rfl (Ns204p2266 rfl)) 

noncomputable abbrev qz611 := (@Enclosure.dec_le_dec qz748 qz757 499158 1000 500593 1000 (@Eq.refl Real qz748) (@Eq.refl Real qz757) rfl rfl rfl)

noncomputable abbrev qz292 := (RS205to222.d3 qz531 qz544 qz611)

noncomputable abbrev qz825 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz292)

noncomputable def Ns204p2268 := @Enclosure.Real.IsNear.of_eq qz825 (hardyZApproximantRS₀ qz190) Bool.false 119148331690512275483 36893488147419103232 67600750889428828757 46116860184273879040000 

noncomputable abbrev qz293 := qz611

noncomputable def Ns204p2269 := @Enclosure.Real.IsNear.pos_val qz825 119148331690512275483 36893488147419103232 67600750889428828757 46116860184273879040000 (Ns204p2268 (RS205to222.d4 qz190 qz202 qz293) RS205to222.d56) rfl 

noncomputable abbrev qz826 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz292)

noncomputable def Ns204p2270 := @Enclosure.Real.IsNear.of_eq qz826 (hardyZApproximantRS₀ qz202) Bool.true 70081271109546147963 73786976294838206464 108444877936605169797 73786976294838206464000 

noncomputable def Ns204p2271 := @Enclosure.Real.IsNear.neg_val qz826 70081271109546147963 73786976294838206464 108444877936605169797 73786976294838206464000 (Ns204p2270 (RS205to222.d42 qz190 qz202 qz293) RS205to222.d57) rfl 

noncomputable def Ns204p2272 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz825 qz4 qz190 479682 1000 499158 1000 

noncomputable def Ns204p2273 := @Enclosure.norm_gt_of_isNear qz825 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 119148331690512275483 36893488147419103232 67600750889428828757 

noncomputable def Ns204p2274 := @Ns204p2273 46116860184273879040000 209459933 2684354560 1213 2684354560 (Ns204p2268 (RS205to222.d4 qz190 qz202 qz293) RS205to222.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2275 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz826 qz4 qz202 479682 1000 500593 1000 

noncomputable def Ns204p2276 := @Enclosure.norm_gt_of_isNear qz826 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 70081271109546147963 73786976294838206464 108444877936605169797 

noncomputable def Ns204p2277 := @Ns204p2276 73786976294838206464000 209459933 2684354560 1213 2684354560 (Ns204p2270 (RS205to222.d42 qz190 qz202 qz293) RS205to222.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2278 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz190 499158 1000 qz193 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz825 qz826 (Ns204p2269 rfl rfl) (Ns204p2271 rfl rfl)) (Ns204p2272 qz11 qz193 rfl rfl rfl rfl (Ns204p2274 rfl)) (Ns204p2275 qz11 qz205 rfl rfl rfl rfl (Ns204p2277 rfl)) 

noncomputable abbrev qz612 := (@Enclosure.dec_le_dec qz757 qz764 500593 1000 502028 1000 (@Eq.refl Real qz757) qz768 rfl rfl rfl)

noncomputable abbrev qz294 := (RS205to222.d3 qz544 qz557 qz612)

noncomputable abbrev qz827 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz294)

noncomputable def Ns204p2279 := @Enclosure.Real.IsNear.of_eq qz827 (hardyZApproximantRS₀ qz202) Bool.true 70081271109546147963 73786976294838206464 108444877936605169797 73786976294838206464000 

noncomputable abbrev qz295 := qz612

noncomputable def Ns204p2280 := @Enclosure.Real.IsNear.neg_val qz827 70081271109546147963 73786976294838206464 108444877936605169797 73786976294838206464000 (Ns204p2279 (RS205to222.d4 qz202 qz215 qz295) RS205to222.d57) rfl 

noncomputable abbrev qz828 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz294)

noncomputable def Ns204p2281 := @Enclosure.Real.IsNear.of_eq qz828 (hardyZApproximantRS₀ qz215) Bool.false 26504326552116006373 73786976294838206464 8493740168892211527 5764607523034234880000 

noncomputable def Ns204p2282 := @Enclosure.Real.IsNear.pos_val qz828 26504326552116006373 73786976294838206464 8493740168892211527 5764607523034234880000 (Ns204p2281 (RS205to222.d42 qz202 qz215 qz295) RS205to222.d58) rfl 

noncomputable def Ns204p2283 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz827 qz4 qz202 479682 1000 500593 1000 

noncomputable def Ns204p2284 := @Enclosure.norm_gt_of_isNear qz827 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 70081271109546147963 73786976294838206464 108444877936605169797 

noncomputable def Ns204p2285 := @Ns204p2284 73786976294838206464000 209459933 2684354560 1213 2684354560 (Ns204p2279 (RS205to222.d4 qz202 qz215 qz295) RS205to222.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2286 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz828 qz4 qz215 479682 1000 502028 1000 

noncomputable def Ns204p2287 := @Enclosure.norm_gt_of_isNear qz828 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 26504326552116006373 73786976294838206464 8493740168892211527 

noncomputable def Ns204p2288 := @Ns204p2287 5764607523034234880000 209459933 2684354560 1213 2684354560 (Ns204p2281 (RS205to222.d42 qz202 qz215 qz295) RS205to222.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2289 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz294 (@BSN.thirtyTwoPi_le_dec qz202 500593 1000 qz205 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz827 qz828 (Ns204p2280 rfl rfl) (Ns204p2282 rfl rfl)) (Ns204p2283 qz11 qz205 rfl rfl rfl rfl (Ns204p2285 rfl)) (Ns204p2286 qz11 qz218 rfl rfl rfl rfl (Ns204p2288 rfl)) 

noncomputable abbrev qz613 := (@Enclosure.dec_le_dec qz764 qz772 502028 1000 503462 1000 qz768 qz776 rfl rfl rfl)

noncomputable abbrev qz296 := (RS205to222.d3 qz557 qz570 qz613)

noncomputable abbrev qz829 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz296)

noncomputable def Ns204p2290 := @Enclosure.Real.IsNear.of_eq qz829 (hardyZApproximantRS₀ qz215) Bool.false 26504326552116006373 73786976294838206464 8493740168892211527 5764607523034234880000 

noncomputable abbrev qz297 := qz613

noncomputable def Ns204p2291 := @Enclosure.Real.IsNear.pos_val qz829 26504326552116006373 73786976294838206464 8493740168892211527 5764607523034234880000 (Ns204p2290 (RS205to222.d4 qz215 qz228 qz297) RS205to222.d58) rfl 

noncomputable abbrev qz830 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz296)

noncomputable def Ns204p2292 := @Enclosure.Real.IsNear.of_eq qz830 (hardyZApproximantRS₀ qz228) Bool.true 944904052317968572023 295147905179352825856 272517617083822317273 184467440737095516160000 

noncomputable def Ns204p2293 := @Enclosure.Real.IsNear.neg_val qz830 944904052317968572023 295147905179352825856 272517617083822317273 184467440737095516160000 (Ns204p2292 (RS205to222.d42 qz215 qz228 qz297) RS205to222.d59) rfl 

noncomputable def Ns204p2294 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz829 qz4 qz215 479682 1000 502028 1000 

noncomputable def Ns204p2295 := @Enclosure.norm_gt_of_isNear qz829 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 26504326552116006373 73786976294838206464 8493740168892211527 

noncomputable def Ns204p2296 := @Ns204p2295 5764607523034234880000 209459933 2684354560 1213 2684354560 (Ns204p2290 (RS205to222.d4 qz215 qz228 qz297) RS205to222.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2297 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz830 qz4 qz228 479682 1000 503462 1000 

noncomputable def Ns204p2298 := @Enclosure.norm_gt_of_isNear qz830 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 944904052317968572023 295147905179352825856 272517617083822317273 

noncomputable def Ns204p2299 := @Ns204p2298 184467440737095516160000 209459933 2684354560 1213 2684354560 (Ns204p2292 (RS205to222.d42 qz215 qz228 qz297) RS205to222.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2300 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz296 (@BSN.thirtyTwoPi_le_dec qz215 502028 1000 qz218 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz829 qz830 (Ns204p2291 rfl rfl) (Ns204p2293 rfl rfl)) (Ns204p2294 qz11 qz218 rfl rfl rfl rfl (Ns204p2296 rfl)) (Ns204p2297 qz11 qz231 rfl rfl rfl rfl (Ns204p2299 rfl)) 

noncomputable abbrev qz831 := (@Enclosure.dec_le_dec qz912 qz916 503462 1000 504895 1000 (@Eq.refl Real qz912) qz919 rfl rfl rfl)

noncomputable abbrev qz614 := qz831

noncomputable abbrev qz298 := (RS205to222.d3 qz570 qz583 qz614)

noncomputable abbrev qz832 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz298)

noncomputable def Ns204p2301 := @Enclosure.Real.IsNear.of_eq qz832 (hardyZApproximantRS₀ qz228) Bool.true 944904052317968572023 295147905179352825856 272517617083822317273 184467440737095516160000 

noncomputable abbrev qz299 := qz614

noncomputable def Ns204p2302 := @Enclosure.Real.IsNear.neg_val qz832 944904052317968572023 295147905179352825856 272517617083822317273 184467440737095516160000 (Ns204p2301 (RS205to222.d4 qz228 qz241 qz299) RS205to222.d59) rfl 

noncomputable abbrev qz833 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz298)

noncomputable def Ns204p2303 := @Enclosure.Real.IsNear.of_eq qz833 (hardyZApproximantRS₀ qz241) Bool.false 105095880001255483775 147573952589676412928 218620557038821784501 147573952589676412928000 

noncomputable def Ns204p2304 := @Enclosure.Real.IsNear.pos_val qz833 105095880001255483775 147573952589676412928 218620557038821784501 147573952589676412928000 (Ns204p2303 (RS205to222.d42 qz228 qz241 qz299) RS205to222.d60) rfl 

noncomputable def Ns204p2305 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz832 qz4 qz228 479682 1000 503462 1000 

noncomputable def Ns204p2306 := @Enclosure.norm_gt_of_isNear qz832 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 944904052317968572023 295147905179352825856 272517617083822317273 

noncomputable def Ns204p2307 := @Ns204p2306 184467440737095516160000 209459933 2684354560 1213 2684354560 (Ns204p2301 (RS205to222.d4 qz228 qz241 qz299) RS205to222.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2308 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz833 qz4 qz241 479682 1000 504895 1000 

noncomputable def Ns204p2309 := @Enclosure.norm_gt_of_isNear qz833 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 105095880001255483775 147573952589676412928 218620557038821784501 

noncomputable def Ns204p2310 := @Ns204p2309 147573952589676412928000 209459933 2684354560 1213 2684354560 (Ns204p2303 (RS205to222.d42 qz228 qz241 qz299) RS205to222.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2311 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz298 (@BSN.thirtyTwoPi_le_dec qz228 503462 1000 qz231 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz832 qz833 (Ns204p2302 rfl rfl) (Ns204p2304 rfl rfl)) (Ns204p2305 qz11 qz231 rfl rfl rfl rfl (Ns204p2307 rfl)) (Ns204p2308 qz11 qz244 rfl rfl rfl rfl (Ns204p2310 rfl)) 

noncomputable abbrev qz926 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 504895 1000) (Enclosure.sfrac Bool.false 506327 1000) 504895 1000 506327 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 504895 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 506327 1000)) rfl rfl rfl)

noncomputable abbrev qz834 := qz926

noncomputable abbrev qz615 := qz834

noncomputable abbrev qz300 := (RS205to222.d3 qz583 qz595 qz615)

noncomputable abbrev qz835 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz300)

noncomputable def Ns204p2312 := @Enclosure.Real.IsNear.of_eq qz835 (hardyZApproximantRS₀ qz241) Bool.false 105095880001255483775 147573952589676412928 218620557038821784501 147573952589676412928000 

noncomputable abbrev qz301 := qz615

noncomputable def Ns204p2313 := @Enclosure.Real.IsNear.pos_val qz835 105095880001255483775 147573952589676412928 218620557038821784501 147573952589676412928000 (Ns204p2312 (RS205to222.d4 qz241 qz254 qz301) RS205to222.d60) rfl 

noncomputable abbrev qz836 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz300)

noncomputable def Ns204p2314 := @Enclosure.Real.IsNear.of_eq qz836 (hardyZApproximantRS₀ qz254) Bool.true 19407512732220629087 36893488147419103232 1096109642291564808099 737869762948382064640000 

noncomputable def Ns204p2315 := @Enclosure.Real.IsNear.neg_val qz836 19407512732220629087 36893488147419103232 1096109642291564808099 737869762948382064640000 (Ns204p2314 (RS205to222.d42 qz241 qz254 qz301) RS205to222.d61) rfl 

noncomputable def Ns204p2316 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz835 qz4 qz241 479682 1000 504895 1000 

noncomputable def Ns204p2317 := @Enclosure.norm_gt_of_isNear qz835 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 105095880001255483775 147573952589676412928 218620557038821784501 

noncomputable def Ns204p2318 := @Ns204p2317 147573952589676412928000 209459933 2684354560 1213 2684354560 (Ns204p2312 (RS205to222.d4 qz241 qz254 qz301) RS205to222.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2319 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz836 qz4 qz254 479682 1000 506327 1000 

noncomputable def Ns204p2320 := @Enclosure.norm_gt_of_isNear qz836 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 19407512732220629087 36893488147419103232 1096109642291564808099 

noncomputable def Ns204p2321 := @Ns204p2320 737869762948382064640000 209459933 2684354560 1213 2684354560 (Ns204p2314 (RS205to222.d42 qz241 qz254 qz301) RS205to222.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 209459933 2684354560 1213 2684354560 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS205to222.d44) rfl rfl rfl rfl 

noncomputable def Ns204p2322 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz241 504895 1000 qz244 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz835 qz836 (Ns204p2313 rfl rfl) (Ns204p2315 rfl rfl)) (Ns204p2316 qz11 qz244 rfl rfl rfl rfl (Ns204p2318 rfl)) (Ns204p2319 qz11 (@Eq.refl Real qz254) rfl rfl rfl rfl (Ns204p2321 rfl)) 

noncomputable def Ns204p2323 := @List.cons RS205to222.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz298 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz298) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz298) Ns204p2311)) (@List.cons RS205to222.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns204p2322)) (@List.nil RS205to222.d0)) 

noncomputable def Ns204p2324 := @List.cons RS205to222.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz294 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz294) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz294) Ns204p2289)) (@List.cons RS205to222.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns204p2300)) Ns204p2323) 

noncomputable def Ns204p2325 := @List.cons RS205to222.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz290 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz290) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz290) Ns204p2267)) (@List.cons RS205to222.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns204p2278)) Ns204p2324) 

noncomputable def Ns204p2326 := @List.cons RS205to222.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz286 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz286) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz286) Ns204p2245)) (@List.cons RS205to222.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns204p2256)) Ns204p2325) 

noncomputable def Ns204p2327 := @List.cons RS205to222.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz282 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz282) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz282) Ns204p2223)) (@List.cons RS205to222.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns204p2234)) Ns204p2326) 

noncomputable def Ns204p2328 := @List.cons RS205to222.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz278 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz278) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz278) Ns204p2201)) (@List.cons RS205to222.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz280 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz280) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz280) Ns204p2212)) Ns204p2327) 

noncomputable def Ns204p2329 := @List.cons RS205to222.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz274 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz274) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz274) Ns204p2179)) (@List.cons RS205to222.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz276 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz276) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz276) Ns204p2190)) Ns204p2328) 

noncomputable def Ns204p2330 := @List.cons RS205to222.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz270 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz270) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz270) Ns204p2157)) (@List.cons RS205to222.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz272 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz272) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz272) Ns204p2168)) Ns204p2329) 

noncomputable def Ns204p2331 := @List.cons RS205to222.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz266 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz266) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz266) Ns204p2135)) (@List.cons RS205to222.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz268 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz268) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz268) Ns204p2146)) Ns204p2330) 

noncomputable abbrev qz837 := (RS205to222.d2 qz912 qz916 (@Enclosure.dec_le_dec qz912 qz916 503462 1000 504895 1000 (@Eq.refl Real qz912) qz919 rfl rfl rfl))

noncomputable abbrev qz838 := (@List.cons RS205to222.d1 (RS205to222.d2 qz916 qz921 qz926) (@List.nil RS205to222.d1))

noncomputable abbrev qz616 := (@List.cons RS205to222.d1 (RS205to222.d2 qz764 qz772 (@Enclosure.dec_le_dec qz764 qz772 502028 1000 503462 1000 qz768 qz776 rfl rfl rfl)) (@List.cons RS205to222.d1 qz837 qz838))

noncomputable abbrev qz302 := (@List.cons RS205to222.d1 (RS205to222.d2 qz531 qz544 qz611) (@List.cons RS205to222.d1 (RS205to222.d2 qz544 qz557 qz612) qz616))

noncomputable def Ns204p2332 := @List.cons RS205to222.d1 (RS205to222.d2 qz166 qz178 qz289) (@List.cons RS205to222.d1 (RS205to222.d2 qz178 qz190 qz291) qz302) 

noncomputable abbrev qz839 := (RS205to222.d2 qz882 qz886 (@Enclosure.dec_le_dec qz882 qz886 493405 1000 494845 1000 (@Eq.refl Real qz882) qz889 rfl rfl rfl))

noncomputable abbrev qz840 := (@List.cons RS205to222.d1 (RS205to222.d2 qz886 qz891 qz925) Ns204p2332)

noncomputable abbrev qz617 := (@List.cons RS205to222.d1 (RS205to222.d2 qz701 qz710 (@Enclosure.dec_le_dec qz701 qz710 491965 1000 493405 1000 qz705 qz714 rfl rfl rfl)) (@List.cons RS205to222.d1 qz839 qz840))

noncomputable abbrev qz303 := (@List.cons RS205to222.d1 (RS205to222.d2 qz445 qz457 qz606) (@List.cons RS205to222.d1 (RS205to222.d2 qz457 qz469 qz607) qz617))

noncomputable def Ns204p2333 := @List.cons RS205to222.d1 (RS205to222.d2 qz75 qz88 qz275) (@List.cons RS205to222.d1 (RS205to222.d2 qz88 qz101 qz277) qz303) 

noncomputable def Ns204p2334 := @List.IsChain.cons_cons RS205to222.d1 RS205to222.d62 (RS205to222.d2 qz62 qz75 qz273) (RS205to222.d2 qz75 qz88 qz275) (@List.cons RS205to222.d1 (RS205to222.d2 qz88 qz101 qz277) qz303) 

noncomputable def Ns204p2335 := @List.IsChain.cons_cons RS205to222.d1 RS205to222.d62 (RS205to222.d2 qz75 qz88 qz275) (RS205to222.d2 qz88 qz101 qz277) qz303 (@Enclosure.dec_le_dec qz88 qz88 487638 1000 487638 1000 qz91 qz91 rfl rfl rfl) 

noncomputable abbrev qz841 := (RS205to222.d2 qz886 qz891 qz925)

noncomputable abbrev qz618 := qz841

noncomputable abbrev qz304 := qz618

noncomputable def Ns204p2336 := @List.IsChain.cons_cons RS205to222.d1 RS205to222.d62 qz304 (RS205to222.d2 qz166 qz178 qz289) (@List.cons RS205to222.d1 (RS205to222.d2 qz178 qz190 qz291) qz302) 

noncomputable def Ns204p2337 := @List.IsChain.cons_cons RS205to222.d1 RS205to222.d62 (RS205to222.d2 qz166 qz178 qz289) (RS205to222.d2 qz178 qz190 qz291) qz302 (@Enclosure.dec_le_dec qz178 qz178 497721 1000 497721 1000 qz181 qz181 rfl rfl rfl) 

noncomputable abbrev qz305 := qz616

noncomputable abbrev qz619 := (@List.cons RS205to222.d1 qz837 qz838)

noncomputable abbrev qz306 := qz619

noncomputable abbrev qz620 := qz837

noncomputable abbrev qz307 := qz620

noncomputable abbrev qz621 := qz838

noncomputable abbrev qz308 := qz621

noncomputable abbrev qz842 := (RS205to222.d2 qz916 qz921 qz926)

noncomputable abbrev qz622 := qz842

noncomputable abbrev qz309 := qz622

noncomputable def Ns204p2338 := @List.IsChain.cons_cons RS205to222.d1 RS205to222.d62 (RS205to222.d2 qz190 qz202 qz293) (RS205to222.d2 qz202 qz215 qz295) qz305 (@Enclosure.dec_le_dec qz202 qz202 500593 1000 500593 1000 qz205 qz205 rfl rfl rfl) (@List.IsChain.cons_cons RS205to222.d1 RS205to222.d62 (RS205to222.d2 qz202 qz215 qz295) (RS205to222.d2 qz215 qz228 qz297) qz306 (@Enclosure.dec_le_dec qz215 qz215 502028 1000 502028 1000 qz218 qz218 rfl rfl rfl) (@List.IsChain.cons_cons RS205to222.d1 RS205to222.d62 (RS205to222.d2 qz215 qz228 qz297) qz307 qz308 (@Enclosure.dec_le_dec qz228 qz228 503462 1000 503462 1000 qz231 qz231 rfl rfl rfl) (@List.IsChain.cons_cons RS205to222.d1 RS205to222.d62 qz307 qz309 (@List.nil RS205to222.d1) (@Enclosure.dec_le_dec qz241 qz241 504895 1000 504895 1000 qz244 qz244 rfl rfl rfl) (@List.IsChain.singleton RS205to222.d1 RS205to222.d62 qz309)))) 

noncomputable abbrev qz310 := (@List.cons RS205to222.d1 (RS205to222.d2 qz544 qz557 qz612) qz616)

noncomputable def Ns204p2339 := @List.IsChain.cons_cons RS205to222.d1 RS205to222.d62 (RS205to222.d2 qz178 qz190 qz291) (RS205to222.d2 qz190 qz202 qz293) qz310 (@Enclosure.dec_le_dec qz190 qz190 499158 1000 499158 1000 qz193 qz193 rfl rfl rfl) Ns204p2338 

noncomputable abbrev qz311 := qz617

noncomputable abbrev qz623 := (@List.cons RS205to222.d1 qz839 qz840)

noncomputable abbrev qz312 := qz623

noncomputable abbrev qz624 := qz839

noncomputable abbrev qz313 := qz624

noncomputable abbrev qz625 := qz840

noncomputable abbrev qz314 := qz625

noncomputable def Ns204p2340 := @List.IsChain.cons_cons RS205to222.d1 RS205to222.d62 (RS205to222.d2 qz101 qz114 qz279) (RS205to222.d2 qz114 qz127 qz281) qz311 (@Enclosure.dec_le_dec qz114 qz114 490524 1000 490524 1000 qz117 qz117 rfl rfl rfl) (@List.IsChain.cons_cons RS205to222.d1 RS205to222.d62 (RS205to222.d2 qz114 qz127 qz281) (RS205to222.d2 qz127 qz140 qz283) qz312 (@Enclosure.dec_le_dec qz127 qz127 491965 1000 491965 1000 qz130 qz130 rfl rfl rfl) (@List.IsChain.cons_cons RS205to222.d1 RS205to222.d62 (RS205to222.d2 qz127 qz140 qz283) qz313 qz314 (@Enclosure.dec_le_dec qz140 qz140 493405 1000 493405 1000 qz143 qz143 rfl rfl rfl) (@List.IsChain.cons_cons RS205to222.d1 RS205to222.d62 qz313 qz304 Ns204p2332 (@Enclosure.dec_le_dec qz153 qz153 494845 1000 494845 1000 qz156 qz156 rfl rfl rfl) (Ns204p2336 (@Enclosure.dec_le_dec qz166 qz166 496283 1000 496283 1000 qz169 qz169 rfl rfl rfl) (Ns204p2337 Ns204p2339))))) 

noncomputable abbrev qz315 := (@List.cons RS205to222.d1 (RS205to222.d2 qz457 qz469 qz607) qz617)

noncomputable def Ns204p2341 := @List.IsChain.cons_cons RS205to222.d1 RS205to222.d62 (RS205to222.d2 qz88 qz101 qz277) (RS205to222.d2 qz101 qz114 qz279) qz315 (@Enclosure.dec_le_dec qz101 qz101 489081 1000 489081 1000 qz104 qz104 rfl rfl rfl) Ns204p2340 

noncomputable def Ns204p2342 := Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns204p2331 (@List.IsChain.cons_cons RS205to222.d1 RS205to222.d62 (RS205to222.d2 qz4 qz30 qz267) (RS205to222.d2 qz30 qz49 qz269) (@List.cons RS205to222.d1 (RS205to222.d2 qz49 qz62 qz271) (@List.cons RS205to222.d1 (RS205to222.d2 qz62 qz75 qz273) Ns204p2333)) (@Enclosure.dec_le_dec qz30 qz30 481854 1000 481854 1000 qz33 qz33 rfl rfl rfl) (@List.IsChain.cons_cons RS205to222.d1 RS205to222.d62 (RS205to222.d2 qz30 qz49 qz269) (RS205to222.d2 qz49 qz62 qz271) (@List.cons RS205to222.d1 (RS205to222.d2 qz62 qz75 qz273) Ns204p2333) (@Enclosure.dec_le_dec qz49 qz49 483302 1000 483302 1000 qz52 qz52 rfl rfl rfl) (@List.IsChain.cons_cons RS205to222.d1 RS205to222.d62 (RS205to222.d2 qz49 qz62 qz271) (RS205to222.d2 qz62 qz75 qz273) Ns204p2333 (@Enclosure.dec_le_dec qz62 qz62 484748 1000 484748 1000 qz65 qz65 rfl rfl rfl) (Ns204p2334 (@Enclosure.dec_le_dec qz75 qz75 486193 1000 486193 1000 qz78 qz78 rfl rfl rfl) (Ns204p2335 Ns204p2341))))) 

noncomputable abbrev qz626 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz627 := (Zeta.Certificates.CertifiedZeroIntervals.intervals Ns204p2342)

theorem RS205to222.d63 : Zeta.Certificates.BatchSpec 18 479682 1000 506327 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz626 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 18) (And (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz626 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz626 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz254)))) Ns204p2342 (@And.intro (@Eq Nat (@List.length qz626 qz627) 18) (And (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz626 qz627)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz626 qz627)) (@Option.some Real qz254))) (@Eq.refl Nat 18) (@And.intro (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz626 qz627)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz626 qz627)) (@Option.some Real qz254)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz254))))

theorem solution : Zeta.Certificates.BatchSpec 18 479682 1000 506327 1000 := RS205to222.d63
#print axioms solution
#check solution
