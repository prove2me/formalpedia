-- Prove2me | solution 1 for RHHeight1000.rs_main_0115_0132
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T22:01:54.232183+00:00
-- url     : https://prove2.me/submissions/1a757901-86f3-448a-a1c0-775ce9859b42

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

noncomputable def RS115to132.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS115to132.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS115to132.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS115to132.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS115to132.d2 a b h 

theorem RS115to132.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS115to132.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS115to132.d3 a b h)) 

noncomputable def Ns114p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns114p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns114p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns114p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns114p0 Ns114p1 Ns114p2 Ns114p1 76821522 67108864 1 23040000 76821522 67108864 1 23040000 38410761 33554432 2 33554432 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns114p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns114p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns114p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns114p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns114p8 := nat_lit 4564579050430662680769181008104061220617401457132102377181523838895616693352443067851710738206186456870068891932464934433532008760270543541307416978974983178670584632435273151991067990877911260800542253584783113678675870571765297427794279500566373840368605043192397583789219721854001914445657820861544585749419999617014263230075963405112904900127091763553068379337562290951837345169106631254289648555755847509739637528572205479767112592191328488981867735095152085893116377698979776390335134938272744697179058821035388170748994050345731998297589980525805272027148669105172128531226596705145339433394591280230580530674088894892093599627198529211479716891686479023042798211193766875 

noncomputable def Ns114p9 := nat_lit 487897090127139370915718269131278067469793404735814825511781216300711748025172292443098109798278438646340651351778930478625246708087138935333656000353278407183834741097045313633566773106147391845370902603761794798142555380136213880615811008223525988937457841388015247818375543397617608528881621312159551521324412657167692163397240217814307445909713899850058291308690066733028125556419716734774904437710284132364898181426902860503703874999414246848733477446908396851600224567407637334679631394476122651438668110771117818686943497967108192010818356995023330089079080278635386063923383437486637555787861728490935630579993241432729945572572039527546968749899721199864050991936636425 

noncomputable def Ns114p10 := nat_lit 6037312065319767048564142443281100833094517501602298457411621838401909436348967513970575877459259771623941548258204445821942291045664120860093665600098153114527011142424471743215189638406506367790367599859596104992621477169994698594142049192256667252266301439715334971326182286325870243632349119406725171166047972624848379242642987691741446913322611634487665631123884299676351857591585933871955560195724863436092564725843702568563820604138142931407752731605404492259322164906548421338089777140624840599546449293504664341809058329304227251421882253537858630692969727217927909816425536009981778974686700833928275616694615814871054602955126209568752228017149733267081250625 

noncomputable def Ns114p11 := BSN.log_dyadic_bound Ns114p6 Ns114p7 14 13 Ns114p8 67108864 23040000 Ns114p9 Ns114p10 76821522 Ns114p4 Ns114p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP Ns114p6) (BSN.artanhQ Ns114p7) 0 13 Ns114p9 Ns114p8 Ns114p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns114p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns114p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns114p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns114p15 := nat_lit 4564579050430719991598727864173574027249459620864950728835381976489772818715667160654947079996042508112007609792086902604246591277951902079645511578729044446029890641532783292129843149875777032317116470385319181253925715321425403083930304095443896121595862314424397722115177325385869596477930511910402142030838288588290691454497602943515837117442179176528567975378491450565217634156690207739385924001994080445739653712153122146143735369275124802705327973995316801123426696765469161725178407791303143690561306079033018690304653273985689879967765287476386100315971524212560669782530460797364817008851488910076252022325883262600059844010859170953904690437223359663042798211193766875 

noncomputable def Ns114p16 := nat_lit 487897090127146028016094362581487656757614504303373888298359177917068925336311225982425876767220472971199663852495703606478044548245204650969304786130313739004418091807374551157966311600460925549125369213480618028519005676490156484647720769146106466452899814849266557198964140238149260938822380107756357944282785296375303842904282420173433118269847736574242174913483374429734863225743639963757643848706968740179283875896315642693907130861939137742544595612595383386022728925244773380688186919137495322289344312028838765525860232491884325012249877491080249836360703014994786844727995613684463741175252463635603207543937219860925630575346787413234983278028650172664050991936636425 

noncomputable def Ns114p17 := nat_lit 6037312065319913640506765330482094651728996212510072186683329349665034025528265882310343281188309943135362157762326025787898903072857099500666458772539172249805276355211909724494669715550462680374559205875381267976760313571991112548079805305194151041203595124480241065931717334103047325628819416103687949050116922196393250525830281764599302835242983634853487222885409728030646963007168165596579721200854339637057218394652367706804217404799249814690071011337988816707639904852988452679974011323771101001271418584434659185032723127441286381829860978672625319259709832419206399165424340759332155638209605427889981579187342651500575472600628768480466654897149733267081250625 

noncomputable def Ns114p18 := BSN.log_dyadic_bound Ns114p13 Ns114p14 14 13 Ns114p15 67108864 23040000 Ns114p16 Ns114p17 76821522 Ns114p12 Ns114p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP Ns114p13) (BSN.artanhQ Ns114p14) 0 13 Ns114p16 Ns114p15 Ns114p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns114p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 38410761 33554432 2 33554432 38410761 33554432 1 16777216 (Ns114p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns114p0 Ns114p1 76821522 67108864 1 23040000 Bool.false (BSN.logfrac_isNear Ns114p4 Ns114p5 1 Ns114p0 Ns114p1 76821522 67108864 23040000 rfl rfl rfl (Ns114p11 rfl))) (BSN.isNear_log_sfrac Ns114p2 Ns114p1 76821522 67108864 1 23040000 Bool.false (BSN.logfrac_isNear Ns114p12 Ns114p5 1 Ns114p2 Ns114p1 76821522 67108864 23040000 rfl rfl rfl (Ns114p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS115to132.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 16777216 := Ns114p19 

noncomputable def Ns114p20 := BSN.log_dyadic_bound 1 3 7 6 71816279535 4194304 1440000 2852596872 10395 2907269 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1) (BSN.artanhQ 3) 0 6 2852596872 71816279535 10395 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz316 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz0 := qz316

theorem RS115to132.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 2907269 4194304 1 1440000 := BSN.isNear_log_sfrac 2 1 2907269 4194304 1 1440000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 2907269 4194304 1440000 rfl rfl rfl (Ns114p20 rfl)) 

theorem RS115to132.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 46516304 67108864 47 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 2907269 4194304 1 1440000 46516304 67108864 47 67108864 RS115to132.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz319 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def Ns114p21 := @Enclosure.Real.IsNear.inv_image qz317 11863283 8388608 1 8388608 2965820 2965822 4194304 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 11863283 8388608 1 8388608 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 11863283 8388608 1 8388608 11863283 8388608 1 8388608 (BSN.sqrt_enclosure 2 1 5931641 5931642 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS115to132.d8 : Enclosure.Real.IsNear qz320 Bool.false 2965821 4194304 1 4194304 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 5931642 8388608 2 8388608 2965821 4194304 1 4194304 (Ns114p21 rfl rfl) rfl 

theorem RS115to132.d9 : Enclosure.Real.IsNear qz320 Bool.false 47453136 67108864 16 67108864 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 2965821 4194304 1 4194304 47453136 67108864 16 67108864 RS115to132.d8 rfl 

noncomputable def Ns114p22 := BSN.log_dyadic_bound 1 2 12 11 1326382131865190400 4194304 1440000 130797573554866995 13749310575 4607913 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 1) (BSN.artanhQ 2) 0 11 130797573554866995 1326382131865190400 13749310575 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS115to132.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 4607913 4194304 1 1440000 := BSN.isNear_log_sfrac 3 1 4607913 4194304 1 1440000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 4607913 4194304 1440000 rfl rfl rfl (Ns114p22 rfl)) 

theorem RS115to132.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 73726608 67108864 47 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 4607913 4194304 1 1440000 73726608 67108864 47 67108864 RS115to132.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns114p23 := @Enclosure.Real.IsNear.inv_image qz321 14529495 8388608 1 8388608 2421582 2421583 4194304 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 14529495 8388608 1 8388608 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 14529495 8388608 1 8388608 14529495 8388608 1 8388608 (BSN.sqrt_enclosure 3 1 7264747 7264748 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS115to132.d12 : Enclosure.Real.IsNear qz323 Bool.false 4843165 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 4843165 8388608 1 8388608 4843165 8388608 1 8388608 (Ns114p23 rfl rfl) rfl 

theorem RS115to132.d13 : Enclosure.Real.IsNear qz323 Bool.false 38745320 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 4843165 8388608 1 8388608 38745320 67108864 8 67108864 RS115to132.d12 rfl 

noncomputable def Ns114p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns114p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns114p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns114p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns114p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns114p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns114p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns114p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns114p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns114p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns114p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns114p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns114p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns114p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns114p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns114p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns114p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns114p25 Ns114p26 Ns114p27 Ns114p28 200200021673987500790625 Ns114p29 Ns114p30 Ns114p31 Ns114p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns114p32 Ns114p33 151412625 Ns114p34 Ns114p35 1322214852783825 Ns114p27 Ns114p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns114p32 Ns114p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns114p34 Ns114p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns114p36 Ns114p37 1267389585 Ns114p38 Ns114p39 1927077560082675 Ns114p29 Ns114p30 Ns114p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns114p36 Ns114p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns114p38 Ns114p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS115to132.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns114p24 Ns114p25 1 Ns114p26 := Ns114p40 rfl rfl rfl 

noncomputable def Ns114p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns114p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns114p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns114p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns114p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns114p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns114p25 Ns114p26 Ns114p42 Ns114p43 9945 Ns114p44 Ns114p45 65835 Ns114p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns114p42 Ns114p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns114p44 Ns114p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS115to132.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns114p41 Ns114p25 1 Ns114p26 := Ns114p46 rfl 

noncomputable def Ns114p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns114p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS115to132.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns114p47 Ns114p25 1 Ns114p48 := BSN.pi_combine Ns114p24 Ns114p41 Ns114p25 Ns114p26 Ns114p48 Ns114p47 rfl rfl rfl rfl RS115to132.d14 RS115to132.d15 

theorem RS115to132.d17 : Enclosure.Real.IsNear Real.pi Bool.false 3537118876014220 1125899906842624 1 1125899906842624 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns114p47 Ns114p25 1 Ns114p48 3537118876014220 1125899906842624 1 1125899906842624 RS115to132.d16 rfl 

noncomputable def Ns114p49 := nat_lit 178719669545544893480837345123291015625 

noncomputable def Ns114p50 := nat_lit 27745388228251122714770036239987464375 

noncomputable def Ns114p51 := nat_lit 1274524447665412456340166714375 

noncomputable def Ns114p52 := BSN.log_dyadic_bound 3 5 16 15 Ns114p49 4194304 1440000 Ns114p50 Ns114p51 5814539 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP 3) (BSN.artanhQ 5) 0 15 Ns114p50 Ns114p49 Ns114p51 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS115to132.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 5814539 4194304 1 1440000 := BSN.isNear_log_sfrac 4 1 5814539 4194304 1 1440000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 5814539 4194304 1440000 rfl rfl rfl (Ns114p52 rfl)) 

theorem RS115to132.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 93032624 67108864 47 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 5814539 4194304 1 1440000 93032624 67108864 47 67108864 RS115to132.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns114p53 := @Enclosure.Real.IsNear.inv_image qz325 16777217 8388608 1 8388608 2097151 2097152 4194304 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 16777217 8388608 1 8388608 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 16777217 8388608 1 8388608 16777217 8388608 1 8388608 (BSN.sqrt_enclosure 4 1 8388608 8388609 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS115to132.d20 : Enclosure.Real.IsNear qz327 Bool.false 4194303 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 4194303 8388608 1 8388608 4194303 8388608 1 8388608 (Ns114p53 rfl rfl) rfl 

theorem RS115to132.d21 : Enclosure.Real.IsNear qz327 Bool.false 33554424 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 4194303 8388608 1 8388608 33554424 67108864 8 67108864 RS115to132.d20 rfl 

noncomputable def Ns114p54 := nat_lit 432044237847189949652629901200995702590625 

noncomputable def Ns114p55 := nat_lit 89467042677079332529401996239971435345500 

noncomputable def Ns114p56 := nat_lit 2254217236409302326906244300800000 

noncomputable def Ns114p57 := nat_lit 1703271991756449094855875 

noncomputable def Ns114p58 := BSN.log_dyadic_bound 2 3 20 19 Ns114p54 4194304 1440000 Ns114p55 Ns114p56 6750471 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 19 9 52520441922763380 253655458399017675 9033331507200 1156268355358836200013540 Ns114p57 249544393960587264000 Ns114p55 Ns114p54 Ns114p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 2) (BSN.artanhQ 3) 0 9 52520441922763380 253655458399017675 9033331507200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 9 19 1156268355358836200013540 Ns114p57 249544393960587264000 rfl rfl rfl rfl)) rfl rfl 

theorem RS115to132.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 6750471 4194304 1 1440000 := BSN.isNear_log_sfrac 5 1 6750471 4194304 1 1440000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 6750471 4194304 1440000 rfl rfl rfl (Ns114p58 rfl rfl)) 

theorem RS115to132.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 108007536 67108864 47 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 6750471 4194304 1 1440000 108007536 67108864 47 67108864 RS115to132.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns114p59 := @Enclosure.Real.IsNear.inv_image qz328 18757497 8388608 1 8388608 1875749 1875750 4194304 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 18757497 8388608 1 8388608 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 18757497 8388608 1 8388608 18757497 8388608 1 8388608 (BSN.sqrt_enclosure 5 1 9378748 9378749 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS115to132.d24 : Enclosure.Real.IsNear qz329 Bool.false 3751499 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 3751499 8388608 1 8388608 3751499 8388608 1 8388608 (Ns114p59 rfl rfl) rfl 

theorem RS115to132.d25 : Enclosure.Real.IsNear qz329 Bool.false 30011992 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 3751499 8388608 1 8388608 30011992 67108864 8 67108864 RS115to132.d24 rfl 

noncomputable def Ns114p60 := BSN.log_dyadic_bound 2 10 5 4 94500000000 4194304 1440000 1291130880 26880 1700643 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 10) 0 4 1291130880 94500000000 26880 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) (@Nat.cast Real Real.instNatCast 1))

theorem RS115to132.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683142479095 2251799813685248 3125000009 4500000000000000 := BSN.isNear_log_sfrac 6 1 4034683142479095 2251799813685248 3125000009 4500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 270763002291722209198080 151115727451828646838272 1000000002880000 1440000000000000000000 4034683142479095 2251799813685248 3125000009 4500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 1700643 4194304 24973259072661432 36028797018963968 1440000 1000000000000000 rfl rfl rfl rfl (Ns114p60 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS115to132.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 120242927 67108864 48 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683142479095 2251799813685248 3125000009 4500000000000000 120242927 67108864 48 67108864 RS115to132.d26 rfl 

noncomputable abbrev qz331 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns114p61 := @Enclosure.Real.IsNear.inv_image qz331 20547809 8388608 1 8388608 1712317 1712318 4194304 (@Enclosure.Real.IsNear.of_eq qz331 (Real.sqrt qz330) Bool.false 20547809 8388608 1 8388608 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 20547809 8388608 1 8388608 20547809 8388608 1 8388608 (BSN.sqrt_enclosure 6 1 10273904 10273905 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS115to132.d28 : Enclosure.Real.IsNear qz332 Bool.false 3424635 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 3424635 8388608 1 8388608 3424635 8388608 1 8388608 (Ns114p61 rfl rfl) rfl 

theorem RS115to132.d29 : Enclosure.Real.IsNear qz332 Bool.false 27397080 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 3424635 8388608 1 8388608 27397080 67108864 8 67108864 RS115to132.d28 rfl 

noncomputable def Ns114p62 := BSN.log_dyadic_bound 3 11 6 5 269619528727395 4194304 1440000 6999933372849 55801305 2347198 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 3) (BSN.artanhQ 11) 0 5 6999933372849 269619528727395 55801305 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz883 := (Enclosure.sfrac Bool.false 7 1)

noncomputable abbrev qz628 := qz883

noncomputable abbrev qz333 := qz628

noncomputable abbrev qz1 := qz333

noncomputable abbrev qz334 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) (@Nat.cast Real Real.instNatCast 1))

theorem RS115to132.d30 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 4381799714987255 2251799813685248 3125000009 4500000000000000 := BSN.isNear_log_sfrac 7 1 4381799714987255 2251799813685248 3125000009 4500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz334) Bool.false 294057601148318457528320 151115727451828646838272 1000000002880000 1440000000000000000000 4381799714987255 2251799813685248 3125000009 4500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 2347198 4194304 24973259072661432 36028797018963968 1440000 1000000000000000 rfl rfl rfl rfl (Ns114p62 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS115to132.d31 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 130587807 67108864 48 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 4381799714987255 2251799813685248 3125000009 4500000000000000 130587807 67108864 48 67108864 RS115to132.d30 rfl 

noncomputable abbrev qz335 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns114p63 := @Enclosure.Real.IsNear.inv_image qz335 22194171 8388608 1 8388608 1585297 1585298 4194304 (@Enclosure.Real.IsNear.of_eq qz335 (Real.sqrt qz334) Bool.false 22194171 8388608 1 8388608 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz334) Bool.false 22194171 8388608 1 8388608 22194171 8388608 1 8388608 (BSN.sqrt_enclosure 7 1 11097085 11097086 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz336 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS115to132.d32 : Enclosure.Real.IsNear qz336 Bool.false 3170595 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz336 Bool.false 3170595 8388608 1 8388608 3170595 8388608 1 8388608 (Ns114p63 rfl rfl) rfl 

theorem RS115to132.d33 : Enclosure.Real.IsNear qz336 Bool.false 25364760 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz336 Bool.false 3170595 8388608 1 8388608 25364760 67108864 8 67108864 RS115to132.d32 rfl 

theorem RS115to132.d34 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz884 := (@instHMul Real Real.instMul)

noncomputable abbrev qz629 := qz884

noncomputable abbrev qz337 := (@HMul.hMul Real Real Real qz629 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz2 := qz337

theorem RS115to132.d35 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS115to132.d34 rfl 

noncomputable abbrev qz3 := (@Inv.inv Real Real.instInv qz337)

theorem RS115to132.d36 : Enclosure.Real.IsNear qz3 Bool.false 1335089 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 1335089 8388608 1 8388608 1335089 8388608 1 8388608 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 667544 667545 4194304 RS115to132.d35 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns114p64 := nat_lit 5210406999362540044025856 

noncomputable abbrev qz885 := (Enclosure.sfrac Bool.false 345139 1000)

noncomputable abbrev qz630 := qz885

noncomputable abbrev qz338 := qz630

noncomputable abbrev qz4 := qz338

noncomputable abbrev qz339 := qz629

noncomputable abbrev qz5 := qz339

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 7)

noncomputable abbrev qz7 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz886 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 345139 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz631 := qz886

noncomputable abbrev qz340 := qz631

noncomputable abbrev qz8 := qz340

noncomputable abbrev qz9 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz887 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 345139 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz632 := qz887

noncomputable abbrev qz341 := qz632

noncomputable abbrev qz10 := qz341

noncomputable abbrev qz633 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz8 qz9))

noncomputable def Ns114p65 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 7) (@HMul.hMul Real Real Real qz5 qz633 (Zeta.RiemannSiegel.correction qz10)) 77195959 33554432 27099 16777216 10494830478071849 72057594037927936 412006454751044923 23058430092136939520000 Ns114p64 

noncomputable def Ns114p66 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 345139 1000 63 97 67108864 33554432 1125899906842624 Bool.false 34786777980 1206 

noncomputable def Ns114p67 := Ns114p66 120242927 48 27397080 8 130587807 48 25364760 8 Bool.true 81860408 40205 Bool.true 72641106 Bool.true 58974504 3537118876014220 1 Bool.false 59264088 Bool.false Bool.false 51671574 Bool.true Bool.true 77195959 

noncomputable def Ns114p68 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 345139 1000 25 23 67108864 33554432 1125899906842624 Bool.false 34786777980 1206 

noncomputable def Ns114p69 := Ns114p68 93032624 47 33554424 8 108007536 47 30011992 8 Bool.true 87168844 23677 Bool.false 42232238 Bool.true 66304774 3537118876014220 1 Bool.false 39499376 Bool.true Bool.false 56031667 Bool.false Bool.true 81860408 

noncomputable def Ns114p70 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 345139 1000 177 88 67108864 33554432 1125899906842624 Bool.false 34786777980 1206 

noncomputable def Ns114p71 := Ns114p70 46516304 47 47453136 16 73726608 47 38745320 8 Bool.true 67108848 1263 Bool.false 73846132 Bool.false 64386799 3537118876014220 1 Bool.false 59819875 Bool.true Bool.false 38519160 Bool.false Bool.true 87168844 

noncomputable def Ns114p72 := nat_lit 71028648443525303831182301507893200984198293885938745123 

noncomputable def Ns114p73 := nat_lit 137024817622246279591464014397849139847865626001408000 

noncomputable def Ns114p74 := nat_lit 2350789426467019039116769455520000 

noncomputable def Ns114p75 := nat_lit 4868099439016982884405991228428303680 

noncomputable abbrev qz11 := (@Eq.refl Real qz338)

noncomputable def Ns114p76 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 345139 1000 476484717284 16000000 690278 4000 2000 Ns114p74 Ns114p75 qz11 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns114p77 := nat_lit 22729167501928097225978336482525824314943454043500398439360 

noncomputable abbrev qz888 := (@instHSub Real Real.instSub)

noncomputable abbrev qz634 := qz888

noncomputable abbrev qz342 := qz634

noncomputable abbrev qz12 := qz342

noncomputable abbrev qz343 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz344 := (@HMul.hMul Real Real Real qz629 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz345 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz635 := (Real.log (Enclosure.sfrac Bool.false 476484717284 16000000))

noncomputable abbrev qz13 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 345139 4000) qz635) (@HMul.hMul Real Real Real qz339 qz343 (@HSub.hSub Real Real Real qz342 qz344 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz345 (@Nat.cast Real Real.instNatCast 690278))))))

noncomputable abbrev qz636 := (Enclosure.sfrac Bool.false 345139 2000)

noncomputable abbrev qz346 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz13 qz636) (@HMul.hMul Real Real Real qz5 qz636 (Real.log Real.pi)))

noncomputable def Ns114p78 := @Enclosure.Real.IsNear.addLit_ft_p qz346 (Enclosure.sfrac Bool.true Ns114p74 Ns114p75) 4669006654586041243027 9007199254740992000 55141022900771653 3072000000000000000000 Ns114p74 Ns114p75 0 1 Ns114p77 

noncomputable def Ns114p79 := nat_lit 313331732597709618076689891328000 

noncomputable abbrev qz347 := (@HSub.hSub Real Real Real qz12 qz13 qz636)

noncomputable abbrev qz348 := (@HMul.hMul Real Real Real qz5 qz636 (Real.log Real.pi))

noncomputable def Ns114p80 := @Enclosure.Real.IsNear.subLit_ff_p qz347 qz348 6448338005790070773139 9007199254740992000 45981647873669 6000000000000000000 13257051640779 67108864000 345139 33554432000 Ns114p79 4669006654586041243027 9007199254740992000 

noncomputable def Ns114p81 := nat_lit 12896676011580141546278000 

noncomputable abbrev qz349 := qz636

noncomputable def Ns114p82 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz349 8002705877581096392083 9007199254740992000 45981647873669 6000000000000000000 345139 2000 0 1 Ns114p81 6448338005790070773139 9007199254740992000 45981647873669 6000000000000000000 

noncomputable def Ns114p83 := nat_lit 18020491604114951945228165220961091584 

noncomputable def Ns114p84 := nat_lit 12453872868362532908171264 

noncomputable def Ns114p85 := nat_lit 1208925819614629174706176 

noncomputable def Ns114p86 := nat_lit 3563543871805143335349283826278352142184268676204267831536069802655885276910650983420969816853463078334005024264957378648244772156607152658118082560 

noncomputable def Ns114p87 := nat_lit 105406396361021905817202825428726208957250764241435305041713625541622307815914678408417647207450005435708631079909424983399999770411305860209836032 

noncomputable def Ns114p88 := nat_lit 97741871515138008256437584157706388318303824927921746435151950561124855078560174529694399100621497840805532366352955462788304808373775237120 

noncomputable def Ns114p89 := BSN.log_dyadic_bound 214340717284 738628717284 7 6 Ns114p86 33554432 11520000 Ns114p87 Ns114p88 20050171 952969434568 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 214340717284) (BSN.artanhQ 738628717284) 0 6 Ns114p87 Ns114p86 Ns114p88 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz350 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns114p90 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 345139 4000) qz635 345139 4000 0 1 23197145887394497 2251799813685248 390625063 4500000000000000 8006239734429449300083 9007199254740992000 134819943618757 18000000000000000000 (Enclosure.Real.IsNear.const Bool.false 345139 4000) (BSN.isNear_log_sfrac 476484717284 16000000 23197145887394497 2251799813685248 390625063 4500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 476484717284) qz350)) Bool.false Ns114p84 Ns114p85 1000000161280000 11520000000000000000000 23197145887394497 2251799813685248 390625063 4500000000000000 (BSN.log_rat_reduce_isNear 476484717284 16000000 14 952969434568 524288000000 20050171 33554432 24973259072661432 36028797018963968 11520000 1000000000000000 rfl rfl rfl rfl (Ns114p89 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p91 := BSN.arctan_dyadic_bound_f 1000 690278 1 0 4194304 1440000 0 1 1 0 1 1 6076 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 690278) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 690278) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz14 := qz344

noncomputable abbrev qz15 := qz345

noncomputable abbrev qz351 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz16 := (@Enclosure.Real.IsNear.mulLit_ff qz351 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz352 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 690278)))

noncomputable def Ns114p92 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz352 884279719003555 562949953421312 1 2000000000000000 6076 4194304 1 1440000 3705517478618498859008 883464212088227 562949953421312 12500000009 18000000000000000 qz16 (Ns114p91 rfl) rfl rfl 

noncomputable abbrev qz17 := qz343

noncomputable abbrev qz353 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns114p93 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 345139 4000) qz635) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz352)) 8006239734429449300083 9007199254740992000 134819943618757 18000000000000000000 883464212088227 2251799813685248 12500000009 72000000000000000 Ns114p83 8002705877581096392083 9007199254740992000 45981647873669 6000000000000000000 (Ns114p90 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz352) 1 4 0 1 883464212088227 562949953421312 12500000009 18000000000000000 883464212088227 2251799813685248 12500000009 72000000000000000 qz353 Ns114p92 rfl) 

noncomputable def Ns114p94 := @Ns114p78 Ns114p72 Ns114p73 55141022900771653 3072000000000000000000 (@Ns114p80 55141022900771653 3072000000000000000000 (Ns114p82 (Ns114p93 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 345139 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz349 (Real.log Real.pi) 345139 2000 0 1 38410761 33554432 1 16777216 13257051640779 67108864000 345139 33554432000 (Enclosure.Real.IsNear.const Bool.false 345139 2000) RS115to132.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns114p74 Ns114p75) 

noncomputable abbrev qz354 := (@instHAdd Real Real.instAdd)

noncomputable def Ns114p95 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns114p72 Ns114p73 55141022900771653 3072000000000000000000 4348347247 8388608 19 1048576 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz354 qz346 (Enclosure.sfrac Bool.true Ns114p74 Ns114p75)) Bool.false Ns114p72 Ns114p73 55141022900771653 3072000000000000000000 Ns114p76 (Ns114p94 rfl rfl)) 

noncomputable def Ns114p96 := nat_lit 1899699407357435994701824 

noncomputable def Ns114p97 := nat_lit 140202687408883711345233210945500705342889620938857733301327426790122925743763619840000 

noncomputable def Ns114p98 := nat_lit 2753733154729970958028337252922338050165611694356407771374444090804896824278383046164480 

noncomputable def Ns114p99 := nat_lit 282124429264291861863170246455495773836387849455029874645305995640648505753600000000 

noncomputable def Ns114p100 := nat_lit 366740741756838961937356133982050092264213903083604967420717527124046612700541747200000 

noncomputable def Ns114p101 := nat_lit 50485107836716134230519516303576197586369547729867475808531474998089775111770355846348800 

noncomputable abbrev qz355 := (BSN.sinEvenQ 17179869184)

noncomputable abbrev qz356 := (BSN.sinOddQ 17179869184)

noncomputable def Ns114p102 := BSN.sin_dyadic_bound_f 26996352280 17179869184 3 2 8388608 2882813 Ns114p97 Ns114p98 Ns114p99 Ns114p100 Ns114p101 Ns114p99 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26996352280) qz355 0 2 Ns114p97 Ns114p98 Ns114p99 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26996352280) qz356 0 2 Ns114p100 Ns114p101 Ns114p99 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz357 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable abbrev qz358 := (@Nat.cast Real Real.instNatCast Ns114p85)

noncomputable def Ns114p103 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4348347247) qz357) Bool.false 4348347247 8388608 19 1048576 Bool.true 8388606 8388608 1 1440000 (Ns114p95 rfl) (Enclosure.sfrac_false_div 4348347247 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4348347247) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns114p96) qz358) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 82 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q1 4348347247 8388608 226375608064910080 72057594037927936 82 Ns114p96 Ns114p85 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388606 8388608 Ns114p96 Ns114p85 26996352280 17179869184 2882813 2880000 (Ns114p102 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p104 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns114p72 Ns114p73 55141022900771653 3072000000000000000000 34786777980 67108864 1206 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz354 qz346 (Enclosure.sfrac Bool.true Ns114p74 Ns114p75)) Bool.false Ns114p72 Ns114p73 55141022900771653 3072000000000000000000 Ns114p76 (Ns114p94 rfl rfl)) 

noncomputable def Ns114p105 := Ns114p71 23677 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 177 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 59819875 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 88 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 38519160 67108864) qz11 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 4194303 4194304 110971 5898240000 67108848 67108864 1263 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 4194303 4194304 110971 5898240000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 8388606 8388608 28408576 1509949440000 4194303 4194304 110971 5898240000 (Ns114p103 rfl rfl) rfl)) rfl) (Ns114p104 rfl) RS115to132.d7 

noncomputable def Ns114p106 := nat_lit 1824831893217872068269002405787505613243671632354245601661103964160 

noncomputable def Ns114p107 := nat_lit 149280173440179812144298804241602837812033797730278365202985810657280 

noncomputable def Ns114p108 := nat_lit 884345597297825800971101061875582046415697391200631174086066176 

noncomputable def Ns114p109 := nat_lit 4777889827460706556074386422962335187563038384199175553878180560896 

noncomputable def Ns114p110 := nat_lit 2736803179736629889312144744429385359887286291721770028721406528716800 

noncomputable abbrev qz359 := (BSN.sinEvenQ 67108864)

noncomputable def Ns114p111 := BSN.sin_dyadic_bound_f 73846132 67108864 3 2 67108864 33554432 Ns114p106 Ns114p107 Ns114p108 Ns114p109 Ns114p110 Ns114p108 59819875 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 73846132) qz359 0 2 Ns114p106 Ns114p107 Ns114p108 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 73846132) (BSN.sinOddQ 67108864) 0 2 Ns114p109 Ns114p110 Ns114p108 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p112 := nat_lit 585915738314683906878002505424498063839543562370221133261914596481 

noncomputable def Ns114p113 := nat_lit 16586685937797756904922089360178093090225977525586485022553978961920 

noncomputable def Ns114p114 := nat_lit 295375640838301943538950082608235244785927683198434222091625601 

noncomputable def Ns114p115 := nat_lit 1757156463662375116746929616108277721029058831744266531341560538241 

noncomputable def Ns114p116 := nat_lit 746400867200899060721494021208014189060168988651391826014929053286400 

noncomputable abbrev qz360 := (BSN.cosEvenQ 67108864)

noncomputable def Ns114p117 := BSN.cos_dyadic_bound_f 64386799 67108864 3 2 67108864 33554432 Ns114p112 Ns114p113 Ns114p114 Ns114p115 Ns114p116 Ns114p114 38519160 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 64386799) qz360 0 2 Ns114p112 Ns114p113 Ns114p114 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 64386799) (BSN.cosOddQ 67108864) 0 2 Ns114p115 Ns114p116 Ns114p114 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p118 := nat_lit 195119307474098717818642149965890064777491016827791461717238104320 

noncomputable def Ns114p119 := nat_lit 10119353601109803064114591662037383731791469673019756294717696 

noncomputable def Ns114p120 := nat_lit 511010373954904368891482778667021156748339286455221320130194063616 

noncomputable def Ns114p121 := BSN.sin_dyadic_bound_f 42232238 67108864 3 2 67108864 33554432 Ns114p118 Ns114p107 Ns114p119 Ns114p120 Ns114p110 Ns114p119 39499376 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 42232238) qz359 0 2 Ns114p118 Ns114p107 Ns114p119 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 42232238) (BSN.sinOddQ 67108864) 0 2 Ns114p120 Ns114p110 Ns114p119 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p122 := nat_lit 1185816164647007043801239438441235414845011138603840284397301244160 

noncomputable def Ns114p123 := nat_lit 373558302133108397549897746771072896685372269606794531667026176 

noncomputable def Ns114p124 := nat_lit 3105104193967279129692927266232272920856586188859265934655947120896 

noncomputable def Ns114p125 := BSN.sin_dyadic_bound_f 66304774 67108864 3 2 67108864 33554432 Ns114p122 Ns114p107 Ns114p123 Ns114p124 Ns114p110 Ns114p123 56031667 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 66304774) qz359 0 2 Ns114p122 Ns114p107 Ns114p123 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 66304774) (BSN.sinOddQ 67108864) 0 2 Ns114p124 Ns114p110 Ns114p123 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p126 := Ns114p69 40205 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 25 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 39499376 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 23 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 56031667 67108864) qz11 rfl rfl (Ns114p105 RS115to132.d9 RS115to132.d11 RS115to132.d13 RS115to132.d17 (Ns114p111 rfl rfl) (Ns114p117 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns114p104 rfl) RS115to132.d19 RS115to132.d21 RS115to132.d23 RS115to132.d25 RS115to132.d17 (Ns114p121 rfl rfl) (Ns114p125 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns114p127 := nat_lit 1708552153356091863416951351607898548571760172937863685148877799680 

noncomputable def Ns114p128 := nat_lit 775281790301571164226578372268215305797246699961156052858716416 

noncomputable def Ns114p129 := nat_lit 4473524231129276146111839079703680992907128720180182065590051553536 

noncomputable def Ns114p130 := BSN.sin_dyadic_bound_f 72641106 67108864 3 2 67108864 33554432 Ns114p127 Ns114p107 Ns114p128 Ns114p129 Ns114p110 Ns114p128 59264088 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 72641106) qz359 0 2 Ns114p127 Ns114p107 Ns114p128 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 72641106) (BSN.sinOddQ 67108864) 0 2 Ns114p129 Ns114p110 Ns114p128 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p131 := nat_lit 742068792552157815281869745256518621815530224172868033388048547840 

noncomputable def Ns114p132 := nat_lit 146323599415147814161652176273873041355894114924863745777729536 

noncomputable def Ns114p133 := nat_lit 1943276599428026895943873324529295834116574377600014117570772729856 

noncomputable def Ns114p134 := BSN.sin_dyadic_bound_f 58974504 67108864 3 2 67108864 33554432 Ns114p131 Ns114p107 Ns114p132 Ns114p133 Ns114p110 Ns114p132 51671574 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 58974504) qz359 0 2 Ns114p131 Ns114p107 Ns114p132 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 58974504) (BSN.sinOddQ 67108864) 0 2 Ns114p133 Ns114p110 Ns114p132 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz637 := (BSN.cos_quad_nat1 97 rfl)

noncomputable def Ns114p135 := Ns114p67 54198 BSN.abs_quadSignPos (BSN.cos_quad_nat3 63 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 59264088 67108864) BSN.abs_quadSignNeg qz637 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 51671574 67108864) qz11 rfl rfl (Ns114p126 rfl rfl) (Ns114p104 rfl) RS115to132.d27 RS115to132.d29 RS115to132.d31 RS115to132.d33 RS115to132.d17 (Ns114p130 rfl rfl) (Ns114p134 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns114p136 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 7) 77195959 67108864 54198 67108864 77195959 67108864 54198 67108864 10361066227761152 77195959 33554432 27099 16777216 (Ns114p135 rfl) 

noncomputable def Ns114p137 := @Enclosure.Real.IsNear.mulLit_tf qz633 (Zeta.RiemannSiegel.correction qz10) 770329 2097152 1 4194304 13623828881 34359738368 798022097291 16492674416640000 10494830478071849 72057594037927936 

noncomputable abbrev qz638 := (@HPow.hPow Real Real Real qz7 qz8 qz9)

noncomputable def Ns114p138 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz638 1 1 0 1 770329 2097152 1 4194304 770329 2097152 1 4194304 

noncomputable abbrev qz361 := (@Enclosure.Real.IsNear.of_eq qz8 (@HMul.hMul Real Real Real qz5 qz4 qz3) Bool.false 460791282371 8388608000 345139 8388608000 (BSN.t_div_two_pi_mk qz4 345139 1000 qz11) (@Enclosure.Real.IsNear.mulLit_ff qz4 qz3 345139 1000 0 1 1335089 8388608 1 8388608 460791282371 8388608000 345139 8388608000 (Enclosure.Real.IsNear.const Bool.false 345139 1000) RS115to132.d36 rfl))

noncomputable def Ns114p139 := @Enclosure.Real.IsNear.sqrt_image qz8 460791282371 8388608000 345139 8388608000 31086148 31086172 4194304 qz361 

noncomputable abbrev qz889 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 345139 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz639 := qz889

noncomputable abbrev qz362 := qz639

noncomputable abbrev qz18 := qz362

noncomputable def Ns114p140 := @Enclosure.Real.IsNear.sqrt_image qz18 1942885 262144 3 1048576 11418614 11418619 4194304 (@Enclosure.Real.IsNear.recentre' qz18 Bool.false 62172320 8388608 24 8388608 1942885 262144 3 1048576 (Ns114p139 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz640 := (Real.sqrt qz889)

noncomputable abbrev qz363 := qz640

noncomputable abbrev qz19 := qz363

noncomputable def Ns114p141 := @Enclosure.Real.IsNear.inv_image qz19 22837233 8388608 5 8388608 1540657 1540659 4194304 (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 22837233 8388608 5 8388608 22837233 8388608 5 8388608 (Ns114p140 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns114p142 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz19) Bool.false 3081316 8388608 2 8388608 770329 2097152 1 4194304 (Ns114p141 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz20 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz341))

noncomputable abbrev qz641 := (@HMul.hMul Real Real Real qz884 qz887 qz887)

noncomputable abbrev qz642 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz364 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz641 qz632) qz642)

noncomputable abbrev qz21 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz364))

noncomputable def Ns114p143 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz10) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz20) qz21) Bool.false 13623828881 

noncomputable def Ns114p144 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz20) qz21 4937959 4194304 55 

noncomputable abbrev qz643 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz20))

noncomputable def Ns114p145 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz20) (@Neg.neg Real Real.instNeg qz643) Bool.true 4937959 4194304 55 2097152 (BSN.inv_eq_neg_inv_neg qz20) 

noncomputable def Ns114p146 := @Enclosure.Real.IsNear.recentre' qz643 Bool.false 9875918 8388608 220 8388608 4937959 4194304 

noncomputable def Ns114p147 := @Enclosure.Real.IsNear.recentre' qz20 Bool.true 7125286 8388608 28408576 1509949440000 3562643 4194304 110971 5898240000 

noncomputable abbrev qz22 := (@HMul.hMul Real Real Real qz339 qz337 qz341)

noncomputable def Ns114p148 := @Enclosure.Real.IsNear.cos_image qz22 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21689957) qz357) Bool.false 21689957 8388608 19 1048576 Bool.true 7125286 8388608 1 

noncomputable def Ns114p149 := nat_lit 80958226230838761861431637 

noncomputable def Ns114p150 := nat_lit 4503599627370496000000000000000 

noncomputable def Ns114p151 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz10 884279719003555 140737488355328 1 500000000000000 107877 262144 3 1048576 95393443246946502735 36893488147419103232 Ns114p149 

noncomputable def Ns114p152 := @Enclosure.Real.IsNear.subLit_ff_p qz18 qz1 1942885 262144 3 1048576 7 1 0 1 107877 107877 262144 3 

noncomputable abbrev qz365 := (Enclosure.Real.IsNear.const Bool.false 7 1)

noncomputable def Ns114p153 := @Ns114p152 1048576 (@Enclosure.Real.IsNear.recentre' qz18 Bool.false 62172320 8388608 24 8388608 1942885 262144 3 1048576 (Ns114p139 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns114p154 := @Enclosure.Real.IsNear.recentre' qz22 Bool.false 95393443246946502735 36893488147419103232 Ns114p149 Ns114p150 21689957 8388608 19 1048576 (@Ns114p151 Ns114p150 RS115to132.d35 (Ns114p153 rfl rfl) rfl) 

noncomputable def Ns114p155 := nat_lit 1226875995594057385508864 

noncomputable def Ns114p156 := nat_lit 24349888845143639794960303925742788741616075290312550708925942251045619724027224080640 

noncomputable def Ns114p157 := nat_lit 8538212323856768191728964054094760039755286381279453046051061550894433991173816576 

noncomputable def Ns114p158 := nat_lit 63759694631613764695442758625619721854644402915725085123207670843560889241228448317696 

noncomputable def Ns114p159 := BSN.sin_dyadic_bound_f 17434956526 17179869184 3 2 8388608 2882813 Ns114p156 Ns114p98 Ns114p157 Ns114p158 Ns114p101 Ns114p157 7125286 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 17434956526) qz355 0 2 Ns114p156 Ns114p98 Ns114p157 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 17434956526) qz356 0 2 Ns114p158 Ns114p101 Ns114p157 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p160 := @Ns114p148 1440000 (Ns114p154 rfl) (Enclosure.sfrac_false_div 21689957 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21689957) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns114p155) qz358) 226375608064910080 72057594037927936 Bool.false 7125286 8388608 0 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q1 21689957 8388608 226375608064910080 72057594037927936 0 Ns114p155 Ns114p85 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 7125286 8388608 Ns114p155 Ns114p85 17434956526 17179869184 2882813 2880000 (Ns114p159 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p161 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz20) 3562643 4194304 110971 5898240000 4937849 4938069 4194304 (@Enclosure.Real.IsNear.neg qz20 Bool.true 3562643 4194304 110971 5898240000 (Ns114p147 (Ns114p160 rfl rfl) rfl)) 

noncomputable def Ns114p162 := Ns114p145 (@Enclosure.Real.IsNear.neg qz643 Bool.false 4937959 4194304 55 2097152 (@Ns114p146 55 2097152 (Ns114p161 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p163 := @Enclosure.Real.IsNear.recentre' qz21 Bool.true 1412608 4194304 

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz339 qz337 qz364)

noncomputable abbrev qz366 := (@Nat.cast Real Real.instNatCast 4194304)

noncomputable def Ns114p164 := @Enclosure.Real.IsNear.cos_image qz23 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8029173)) qz366) Bool.true 8029173 4194304 

noncomputable def Ns114p165 := nat_lit 18514012783013034570157525 

noncomputable def Ns114p166 := nat_lit 9671406556917033397649408 

noncomputable def Ns114p167 := nat_lit 30951868093506438401499831012571 

noncomputable def Ns114p168 := @Enclosure.Real.IsNear.recentre' qz23 Bool.true Ns114p165 Ns114p166 Ns114p167 

noncomputable def Ns114p169 := nat_lit 944473296573929042739200000000000000 

noncomputable abbrev qz24 := qz364

noncomputable def Ns114p170 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz24 884279719003555 140737488355328 1 500000000000000 20936828455 

noncomputable abbrev qz367 := (@HSub.hSub Real Real Real qz634 qz641 qz632)

noncomputable abbrev qz25 := qz367

noncomputable abbrev qz368 := qz642

noncomputable abbrev qz26 := qz368

noncomputable def Ns114p171 := @Enclosure.Real.IsNear.subLit_tf qz25 qz26 16641861159 68719476736 5734785 1099511627776 1 16 

noncomputable abbrev qz369 := qz641

noncomputable abbrev qz27 := qz369

noncomputable def Ns114p172 := @Enclosure.Real.IsNear.subLit_ff_n qz27 qz10 11637447129 68719476736 2589057 1099511627776 107877 262144 3 1048576 

noncomputable def Ns114p173 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz10 107877 262144 3 1048576 107877 262144 3 1048576 11637447129 68719476736 

noncomputable def Ns114p174 := nat_lit 8008475017433376632216513600956311577547497807508852170606738663468229153386418175674001 

noncomputable def Ns114p175 := nat_lit 14198936579076412752333613960380805571166435299025227571149477343212749250185412581785600 

noncomputable def Ns114p176 := nat_lit 71787658163710919337856516985892858319620779797515028728307301674612933873055499921 

noncomputable def Ns114p177 := nat_lit 48327533598764926879483001108845142448230125071711633814562419864373609019273890365376145 

noncomputable def Ns114p178 := nat_lit 1292103228695953560462358870394653306976145612211295708974602438232360181766872544942489600 

noncomputable def Ns114p179 := BSN.cos_dyadic_bound_t 8029173 4194304 4 3 4194304 1440000 Ns114p174 Ns114p175 Ns114p176 Ns114p177 Ns114p178 Ns114p176 1412608 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 8029173) (BSN.cosEvenQ 4194304) 0 3 Ns114p174 Ns114p175 Ns114p176 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 8029173) (BSN.cosOddQ 4194304) 0 3 Ns114p177 Ns114p178 Ns114p176 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz370 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns114p180 := @Ns114p163 101457152 3019898880000 2759 8192 396317 11796480000 (@Ns114p164 69 2097152 Bool.true 1412608 4194304 1 1440000 (@Ns114p168 Ns114p169 8029173 4194304 69 2097152 (@Ns114p170 68719476736 5734785 1099511627776 Ns114p165 Ns114p166 Ns114p167 Ns114p169 RS115to132.d35 (@Ns114p171 0 1 334989255280 20936828455 68719476736 5734785 1099511627776 (@Ns114p172 4362564051664896 16641861159 68719476736 5734785 1099511627776 (@Ns114p173 2589057 1099511627776 (Ns114p153 rfl rfl) (Ns114p153 rfl rfl) rfl) (Ns114p153 rfl rfl) rfl rfl) qz370 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 8029173 4194304) (BSN.cos_neg_of_bound 8029173 4194304 Bool.true 1412608 4194304 1 1440000 (Ns114p179 rfl rfl)) rfl rfl) 

noncomputable abbrev qz28 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 7) (Enclosure.sfrac Bool.true 1 1) Bool.true 1 1 0 1 (BSN.neg_one_pow_odd_mk 7 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1))

noncomputable def Ns114p181 := @Ns114p137 412006454751044923 23058430092136939520000 (Ns114p138 qz28 (@Enclosure.Real.IsNear.of_eq qz638 (@Inv.inv Real Real.instInv qz19) Bool.false 770329 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz8 (BSN.t_div_two_pi_nonneg qz4 345139 1000 qz11)) Ns114p142) rfl) (@Ns114p143 34359738368 798022097291 16492674416640000 (BSN.correction_mk qz10 (BSN.cos_two_pi_p_ne_zero_mk qz4 345139 1000 7 qz11 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 345139 1000 7 qz11 rfl rfl rfl))) (@Ns114p144 2097152 2759 8192 396317 11796480000 13623828881 34359738368 798022097291 16492674416640000 Ns114p162 (Ns114p180 rfl) rfl)) 

noncomputable def Ns114p182 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 155282229166106583 72057594037927936 37656588456128324923 23058430092136939520000 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 7) (@HMul.hMul Real Real Real qz5 qz633 (Zeta.RiemannSiegel.correction qz10))) Bool.true 155282229166106583 72057594037927936 37656588456128324923 23058430092136939520000 (BSN.hardyZApproximantRS₀_eq qz4 7 (@BSN.floor_sqrt_eq_dec qz4 345139 1000 7 qz11 rfl rfl rfl)) (@Ns114p65 155282229166106583 72057594037927936 37656588456128324923 23058430092136939520000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 7)) Bool.true 77195959 33554432 27099 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 7) (Ns114p136 (Ns114p135 rfl) rfl rfl)) (Ns114p181 rfl) rfl rfl)) 

theorem RS115to132.d37 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 155282229166106583 72057594037927936 37656588456128324923 23058430092136939520000 := Ns114p182 

theorem RS115to132.d38 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS115to132.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS115to132.d3 a b h)) 

noncomputable def Ns114p183 := nat_lit 103974316268070007274995712 

noncomputable abbrev qz890 := (Enclosure.sfrac Bool.false 346706 1000)

noncomputable abbrev qz644 := qz890

noncomputable abbrev qz371 := qz644

noncomputable abbrev qz29 := qz371

noncomputable abbrev qz891 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 346706 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz645 := qz891

noncomputable abbrev qz372 := qz645

noncomputable abbrev qz30 := qz372

noncomputable abbrev qz892 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 346706 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz646 := qz892

noncomputable abbrev qz373 := qz646

noncomputable abbrev qz31 := qz373

noncomputable abbrev qz647 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz30 qz9))

noncomputable def Ns114p184 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz29) qz29 7) (@HMul.hMul Real Real Real qz5 qz647 (Zeta.RiemannSiegel.correction qz31)) 2215399 4194304 13611 8388608 5302553062383144711 36893488147419103232 1410314532099634271 83010348331692982272000 Ns114p183 

noncomputable def Ns114p185 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz29) qz29 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 346706 1000 63 97 67108864 33554432 1125899906842624 Bool.false 34997535415 1211 

noncomputable def Ns114p186 := Ns114p185 120242927 48 27397080 8 130587807 48 25364760 8 Bool.false 17029674 40388 Bool.true 50304338 Bool.true 52848163 3537118876014220 1 Bool.false 45724016 Bool.false Bool.false 47552719 Bool.true Bool.false 17723192 

noncomputable def Ns114p187 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz29) qz29 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 346706 1000 26 23 67108864 33554432 1125899906842624 Bool.false 34997535415 1211 

noncomputable def Ns114p188 := Ns114p187 93032624 47 33554424 8 108007536 47 30011992 8 Bool.false 39733970 23786 Bool.false 1793194 Bool.true 24795148 3537118876014220 1 Bool.false 67084907 Bool.true Bool.false 24234843 Bool.false Bool.false 17029674 

noncomputable def Ns114p189 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz29) qz29 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 346706 1000 179 89 67108864 33554432 1125899906842624 Bool.false 34997535415 1211 

noncomputable def Ns114p190 := Ns114p189 46516304 47 47453136 16 73726608 47 38745320 8 Bool.false 67108848 1271 Bool.false 883805 Bool.false 54200282 3537118876014220 1 Bool.false 883779 Bool.false Bool.false 48497084 Bool.true Bool.false 39733970 

noncomputable def Ns114p191 := nat_lit 573654941709559470711875889663653015426387162632352333 

noncomputable def Ns114p192 := nat_lit 1100001214639379157621191546974365032376440979456000 

noncomputable def Ns114p193 := nat_lit 2404641361972496113887595412480000 

noncomputable def Ns114p194 := nat_lit 5002226383291504851609677402731745280 

noncomputable abbrev qz374 := (@Eq.refl Real qz644)

noncomputable abbrev qz32 := qz374

noncomputable def Ns114p195 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz29 346706 1000 480821201744 16000000 693412 4000 2000 Ns114p193 Ns114p194 qz32 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns114p196 := nat_lit 11748453206211777960179218220311613755932409090710575779840 

noncomputable abbrev qz648 := (Real.log (Enclosure.sfrac Bool.false 480821201744 16000000))

noncomputable abbrev qz33 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 346706 4000) qz648) (@HMul.hMul Real Real Real qz339 qz343 (@HSub.hSub Real Real Real qz342 qz344 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz345 (@Nat.cast Real Real.instNatCast 693412))))))

noncomputable abbrev qz649 := (Enclosure.sfrac Bool.false 346706 2000)

noncomputable abbrev qz375 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz33 qz649) (@HMul.hMul Real Real Real qz5 qz649 (Real.log Real.pi)))

noncomputable def Ns114p197 := @Enclosure.Real.IsNear.addLit_ft_p qz375 (Enclosure.sfrac Bool.true Ns114p193 Ns114p194) 2348647009458843538553 4503599627370496000 83083429078578493 4608000000000000000000 Ns114p193 Ns114p194 0 1 Ns114p196 

noncomputable def Ns114p198 := nat_lit 78807516370890122313016016896000 

noncomputable abbrev qz376 := (@HSub.hSub Real Real Real qz12 qz33 qz649)

noncomputable abbrev qz377 := (@HMul.hMul Real Real Real qz5 qz649 (Real.log Real.pi))

noncomputable def Ns114p199 := @Enclosure.Real.IsNear.subLit_ff_p qz376 qz377 3242351944934904288377 4503599627370496000 17319631636841 2250000000000000000 6658620651633 33554432000 173353 16777216000 Ns114p198 2348647009458843538553 4503599627370496000 

noncomputable def Ns114p200 := nat_lit 1296940777973961715350800 

noncomputable abbrev qz378 := qz649

noncomputable def Ns114p201 := @Enclosure.Real.IsNear.subLit_ff_p qz33 qz378 804612890227692376293 900719925474099200 17319631636841 2250000000000000000 346706 2000 0 1 Ns114p200 3242351944934904288377 4503599627370496000 17319631636841 2250000000000000000 

noncomputable def Ns114p202 := nat_lit 1811827156303466594160848778679025664 

noncomputable def Ns114p203 := nat_lit 12464825514569906897551360 

noncomputable def Ns114p204 := nat_lit 3822869951894069805741407415572518150548018073988618082656247561717548020710321734259107969558088869226492321145068482708005234364081795239363215360 

noncomputable def Ns114p205 := nat_lit 116510979306358602433554878800240063613771725124291240485972193869547580738587129662875683242108455597350962438013220210769788055347889180552200192 

noncomputable def Ns114p206 := nat_lit 124298700553082803408887427349512435899407417177195735297226433915135940531152669438526925467863409470236371829212364863339346839772824862720 

noncomputable def Ns114p207 := BSN.log_dyadic_bound 218677201744 742965201744 7 6 Ns114p204 33554432 11520000 Ns114p205 Ns114p206 20354168 961642403488 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 218677201744) (BSN.artanhQ 742965201744) 0 6 Ns114p205 Ns114p204 Ns114p206 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns114p208 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 346706 4000) qz648 346706 4000 0 1 23217546780723905 2251799813685248 390625063 4500000000000000 804966277415766220693 900719925474099200 67716026546239 9000000000000000000 (Enclosure.Real.IsNear.const Bool.false 346706 4000) (BSN.isNear_log_sfrac 480821201744 16000000 23217546780723905 2251799813685248 390625063 4500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 480821201744) qz350)) Bool.false Ns114p203 Ns114p85 1000000161280000 11520000000000000000000 23217546780723905 2251799813685248 390625063 4500000000000000 (BSN.log_rat_reduce_isNear 480821201744 16000000 14 961642403488 524288000000 20354168 33554432 24973259072661432 36028797018963968 11520000 1000000000000000 rfl rfl rfl rfl (Ns114p207 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p209 := BSN.arctan_dyadic_bound_f 1000 693412 1 0 4194304 1440000 0 1 1 0 1 1 6048 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 693412) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 693412) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz379 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 693412)))

noncomputable def Ns114p210 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz379 884279719003555 562949953421312 1 2000000000000000 6048 4194304 1 1440000 3705533241217194655744 883467970184611 562949953421312 12500000009 18000000000000000 qz16 (Ns114p209 rfl) rfl rfl 

noncomputable def Ns114p211 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 346706 4000) qz648) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz379)) 804966277415766220693 900719925474099200 67716026546239 9000000000000000000 883467970184611 2251799813685248 12500000009 72000000000000000 Ns114p202 804612890227692376293 900719925474099200 17319631636841 2250000000000000000 (Ns114p208 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz379) 1 4 0 1 883467970184611 562949953421312 12500000009 18000000000000000 883467970184611 2251799813685248 12500000009 72000000000000000 qz353 Ns114p210 rfl) 

noncomputable def Ns114p212 := @Ns114p197 Ns114p191 Ns114p192 83083429078578493 4608000000000000000000 (@Ns114p199 83083429078578493 4608000000000000000000 (Ns114p201 (Ns114p211 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 346706 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz378 (Real.log Real.pi) 346706 2000 0 1 38410761 33554432 1 16777216 6658620651633 33554432000 173353 16777216000 (Enclosure.Real.IsNear.const Bool.false 346706 2000) RS115to132.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns114p193 Ns114p194) 

noncomputable def Ns114p213 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz29) Bool.false Ns114p191 Ns114p192 83083429078578493 4608000000000000000000 2187345963 4194304 153 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz29) (@HAdd.hAdd Real Real Real qz354 qz375 (Enclosure.sfrac Bool.true Ns114p193 Ns114p194)) Bool.false Ns114p191 Ns114p192 83083429078578493 4608000000000000000000 Ns114p195 (Ns114p212 rfl rfl)) 

noncomputable def Ns114p214 := nat_lit 139823230725818129065763801714886599714682307598744075434929822648502757411007047000320 

noncomputable def Ns114p215 := nat_lit 280602414198035786308536796199004932501235168478036071848375357294132373162492027136 

noncomputable def Ns114p216 := nat_lit 365749390849393518184881849678476038885832615342984329641823594453316721757993469337856 

noncomputable def Ns114p217 := BSN.sin_dyadic_bound_f 26978104054 17179869184 3 2 8388608 2882813 Ns114p214 Ns114p98 Ns114p215 Ns114p216 Ns114p101 Ns114p215 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26978104054) qz355 0 2 Ns114p214 Ns114p98 Ns114p215 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26978104054) qz356 0 2 Ns114p216 Ns114p101 Ns114p215 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz380 := (@Nat.cast Real Real.instNatCast 604462909807314587353088)

noncomputable def Ns114p218 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz29) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2187345963) qz366) Bool.false 2187345963 4194304 153 8388608 Bool.false 8388606 8388608 1 1440000 (Ns114p213 rfl) (Enclosure.sfrac_false_div 2187345963 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2187345963) qz366) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949207651302074080034816) qz380) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 82 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q3 2187345963 4194304 226375608064910080 72057594037927936 82 949207651302074080034816 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388606 8388608 949207651302074080034816 604462909807314587353088 26978104054 17179869184 2882813 2880000 (Ns114p217 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p219 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz29) Bool.false Ns114p191 Ns114p192 83083429078578493 4608000000000000000000 34997535415 67108864 1211 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz29) (@HAdd.hAdd Real Real Real qz354 qz375 (Enclosure.sfrac Bool.true Ns114p193 Ns114p194)) Bool.false Ns114p191 Ns114p192 83083429078578493 4608000000000000000000 Ns114p195 (Ns114p212 rfl rfl)) 

noncomputable def Ns114p220 := Ns114p190 23786 BSN.abs_quadSignPos (BSN.cos_quad_nat3 179 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 883779 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 89 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 48497084 67108864) qz32 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 1) Bool.false 4194303 4194304 893393 47185920000 67108848 67108864 1271 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz29)) Bool.false 4194303 4194304 893393 47185920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz29) qz29) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz29)) Bool.false 8388606 8388608 228708608 12079595520000 4194303 4194304 893393 47185920000 (Ns114p218 rfl rfl) rfl)) rfl) (Ns114p219 rfl) RS115to132.d7 

noncomputable def Ns114p221 := BSN.sin_dyadic_bound_f 883805 67108864 1 0 67108864 33554432 0 1 1 0 1 1 883779 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 883805) qz359 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 883805) (BSN.sinOddQ 67108864) 0 0 rfl) rfl rfl 

noncomputable def Ns114p222 := nat_lit 529381332676456765899712322581783130814367634950929852479613640960 

noncomputable def Ns114p223 := nat_lit 74475318496359756577973308570569686033287360656857945245163776 

noncomputable def Ns114p224 := nat_lit 1386354339827440280607644126166984420260242292954228986487638794496 

noncomputable def Ns114p225 := BSN.sin_dyadic_bound_f 54200282 67108864 3 2 67108864 33554432 Ns114p222 Ns114p107 Ns114p223 Ns114p224 Ns114p110 Ns114p223 48497084 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 54200282) qz359 0 2 Ns114p222 Ns114p107 Ns114p223 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 54200282) (BSN.sinOddQ 67108864) 0 2 Ns114p224 Ns114p110 Ns114p223 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p226 := nat_lit 10339727856841140726516496 

noncomputable def Ns114p227 := nat_lit 486777830487640090174734030864384 

noncomputable def Ns114p228 := nat_lit 7301667457314601352621010462965760 

noncomputable def Ns114p229 := BSN.cos_dyadic_bound_f 1793194 67108864 2 1 67108864 33554432 Ns114p226 Ns114p227 Ns114p226 Ns114p226 Ns114p228 Ns114p226 67084907 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1793194) qz360 0 1 Ns114p226 Ns114p227 Ns114p226 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1793194) (BSN.cosOddQ 67108864) 0 1 Ns114p226 Ns114p228 Ns114p226 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p230 := nat_lit 377978258395209219615010345216 

noncomputable def Ns114p231 := nat_lit 2433889152438200450873670154321920 

noncomputable def Ns114p232 := nat_lit 17037224067067403156115691080253440 

noncomputable def Ns114p233 := BSN.sin_dyadic_bound_f 24795148 67108864 2 1 67108864 33554432 Ns114p230 Ns114p231 Ns114p230 Ns114p230 Ns114p232 Ns114p230 24234843 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 24795148) qz359 0 1 Ns114p230 Ns114p231 Ns114p230 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 24795148) (BSN.sinOddQ 67108864) 0 1 Ns114p230 Ns114p232 Ns114p230 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p234 := Ns114p188 40388 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 26 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 67084907 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 23 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 24234843 67108864) qz32 rfl rfl (Ns114p220 RS115to132.d9 RS115to132.d11 RS115to132.d13 RS115to132.d17 (Ns114p221 rfl rfl) (Ns114p225 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns114p219 rfl) RS115to132.d19 RS115to132.d21 RS115to132.d23 RS115to132.d25 RS115to132.d17 (Ns114p229 rfl rfl) (Ns114p233 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns114p235 := nat_lit 392797240727567069178616310655639520392499682844359504463146533120 

noncomputable def Ns114p236 := nat_lit 41005631524388627513077568881647952810977093975106045594583296 

noncomputable def Ns114p237 := nat_lit 1028688288025921885308973926129437980532948063583077101901087785216 

noncomputable def Ns114p238 := BSN.sin_dyadic_bound_f 50304338 67108864 3 2 67108864 33554432 Ns114p235 Ns114p107 Ns114p236 Ns114p237 Ns114p110 Ns114p236 45724016 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 50304338) qz359 0 2 Ns114p235 Ns114p107 Ns114p236 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 50304338) (BSN.sinOddQ 67108864) 0 2 Ns114p237 Ns114p110 Ns114p236 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p239 := nat_lit 478493617552274154935316087011886339120477081798785733194494813345 

noncomputable def Ns114p240 := nat_lit 60846999458596228769164348424372688896769684868500524526249121 

noncomputable def Ns114p241 := nat_lit 1253099055590166011888773009419396189533511872840366014660158203041 

noncomputable def Ns114p242 := BSN.sin_dyadic_bound_f 52848163 67108864 3 2 67108864 33554432 Ns114p239 Ns114p107 Ns114p240 Ns114p241 Ns114p110 Ns114p240 47552719 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 52848163) qz359 0 2 Ns114p239 Ns114p107 Ns114p240 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 52848163) (BSN.sinOddQ 67108864) 0 2 Ns114p241 Ns114p110 Ns114p240 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p243 := Ns114p186 54444 BSN.abs_quadSignPos (BSN.cos_quad_nat3 63 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 45724016 67108864) BSN.abs_quadSignNeg qz637 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 47552719 67108864) qz32 rfl rfl (Ns114p234 rfl rfl) (Ns114p219 rfl) RS115to132.d27 RS115to132.d29 RS115to132.d31 RS115to132.d33 RS115to132.d17 (Ns114p238 rfl rfl) (Ns114p242 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns114p244 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 7) 17723192 67108864 54444 67108864 17723192 67108864 54444 67108864 2378766563147776 2215399 4194304 13611 8388608 (Ns114p243 rfl) 

noncomputable def Ns114p245 := @Enclosure.Real.IsNear.mulLit_tf qz647 (Zeta.RiemannSiegel.correction qz31) 3077829 8388608 1 8388608 1722822503259 4398046511104 4569577206887 98956046499840000 5302553062383144711 36893488147419103232 

noncomputable abbrev qz650 := (@HPow.hPow Real Real Real qz7 qz30 qz9)

noncomputable def Ns114p246 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz650 1 1 0 1 3077829 8388608 1 8388608 3077829 8388608 1 8388608 

noncomputable def Ns114p247 := @Enclosure.Real.IsNear.sqrt_image qz30 231441683417 4194304000 173353 4194304000 31156637 31156661 4194304 (@Enclosure.Real.IsNear.of_eq qz30 (@HMul.hMul Real Real Real qz5 qz29 qz3) Bool.false 231441683417 4194304000 173353 4194304000 (BSN.t_div_two_pi_mk qz29 346706 1000 qz32) (@Enclosure.Real.IsNear.mulLit_ff qz29 qz3 346706 1000 0 1 1335089 8388608 1 8388608 231441683417 4194304000 173353 4194304000 (Enclosure.Real.IsNear.const Bool.false 346706 1000) RS115to132.d36 rfl)) 

noncomputable abbrev qz893 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 346706 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz651 := qz893

noncomputable abbrev qz381 := qz651

noncomputable abbrev qz34 := qz381

noncomputable def Ns114p248 := @Enclosure.Real.IsNear.sqrt_image qz34 31156649 4194304 3 1048576 11431553 11431558 4194304 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 62313298 8388608 24 8388608 31156649 4194304 3 1048576 (Ns114p247 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns114p249 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz34) 22863111 8388608 5 8388608 1538914 1538915 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz34) Bool.false 22863111 8388608 5 8388608 22863111 8388608 5 8388608 (Ns114p248 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns114p250 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz34)) Bool.false 3077829 8388608 1 8388608 3077829 8388608 1 8388608 (Ns114p249 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz35 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz373))

noncomputable abbrev qz652 := (@HMul.hMul Real Real Real qz884 qz892 qz892)

noncomputable abbrev qz382 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz652 qz646) qz642)

noncomputable abbrev qz36 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz382))

noncomputable def Ns114p251 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz31) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz35) qz36) Bool.false 1722822503259 

noncomputable def Ns114p252 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz35) qz36 9317641 8388608 195 

noncomputable abbrev qz653 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz35))

noncomputable def Ns114p253 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz35) (@Neg.neg Real Real.instNeg qz653) Bool.true 9317641 8388608 195 8388608 (BSN.inv_eq_neg_inv_neg qz35) 

noncomputable def Ns114p254 := @Enclosure.Real.IsNear.recentre' qz653 Bool.false 9317641 8388608 195 8388608 9317641 8388608 

noncomputable def Ns114p255 := @Enclosure.Real.IsNear.recentre' qz35 Bool.true 7552206 8388608 28408576 1509949440000 3776103 4194304 110971 5898240000 

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz339 qz337 qz373)

noncomputable abbrev qz383 := (@Nat.cast Real Real.instNatCast 2097152)

noncomputable def Ns114p256 := @Enclosure.Real.IsNear.cos_image qz37 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5643937) qz383) Bool.false 5643937 2097152 19 1048576 Bool.true 7552206 8388608 1 

noncomputable def Ns114p257 := nat_lit 80958226230990135836295509 

noncomputable def Ns114p258 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz31 884279719003555 140737488355328 1 500000000000000 1796521 4194304 3 1048576 1588627085063985632155 590295810358705651712 Ns114p257 

noncomputable def Ns114p259 := @Enclosure.Real.IsNear.subLit_ff_p qz34 qz1 31156649 4194304 3 1048576 7 1 0 1 1796521 1796521 4194304 3 

noncomputable def Ns114p260 := @Ns114p259 1048576 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 62313298 8388608 24 8388608 31156649 4194304 3 1048576 (Ns114p247 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns114p261 := @Enclosure.Real.IsNear.recentre' qz37 Bool.false 1588627085063985632155 590295810358705651712 Ns114p257 Ns114p150 5643937 2097152 19 1048576 (@Ns114p258 Ns114p150 RS115to132.d35 (Ns114p260 rfl rfl) rfl) 

noncomputable def Ns114p262 := nat_lit 36184724170554095189107510047377539172005695281393916412094797417055728289693118972160 

noncomputable def Ns114p263 := nat_lit 18848447182692316995805713164898712005643009777301129999616058270389151134206607616 

noncomputable def Ns114p264 := nat_lit 94738999151250652220145507540864671345339113244963674487867948188422467847359929467136 

noncomputable def Ns114p265 := BSN.sin_dyadic_bound_f 19249056494 17179869184 3 2 8388608 2882813 Ns114p262 Ns114p98 Ns114p263 Ns114p264 Ns114p101 Ns114p263 7552206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 19249056494) qz355 0 2 Ns114p262 Ns114p98 Ns114p263 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 19249056494) qz356 0 2 Ns114p264 Ns114p101 Ns114p263 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz384 := (@Nat.cast Real Real.instNatCast 302231454903657293676544)

noncomputable def Ns114p266 := @Ns114p256 1440000 (Ns114p261 rfl) (Enclosure.sfrac_false_div 5643937 2097152) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5643937) qz383) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 338632983038739458555904) qz384) 226375608064910080 72057594037927936 Bool.false 7552206 8388608 0 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q1 5643937 2097152 226375608064910080 72057594037927936 0 338632983038739458555904 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 7552206 8388608 338632983038739458555904 302231454903657293676544 19249056494 17179869184 2882813 2880000 (Ns114p265 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p267 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz35) 3776103 4194304 110971 5898240000 4658723 4658918 4194304 (@Enclosure.Real.IsNear.neg qz35 Bool.true 3776103 4194304 110971 5898240000 (Ns114p255 (Ns114p266 rfl rfl) rfl)) 

noncomputable def Ns114p268 := Ns114p253 (@Enclosure.Real.IsNear.neg qz653 Bool.false 9317641 8388608 195 8388608 (@Ns114p254 195 8388608 (Ns114p267 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p269 := @Enclosure.Real.IsNear.recentre' qz36 Bool.true 1479192 4194304 

noncomputable abbrev qz38 := (@HMul.hMul Real Real Real qz339 qz337 qz382)

noncomputable def Ns114p270 := @Enclosure.Real.IsNear.cos_image qz38 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 4050053)) qz383) Bool.true 4050053 2097152 

noncomputable def Ns114p271 := nat_lit 4781458851156881299806256045 

noncomputable def Ns114p272 := nat_lit 2475880078570760549798248448 

noncomputable def Ns114p273 := nat_lit 63045069068727908796952183302047 

noncomputable def Ns114p274 := @Enclosure.Real.IsNear.recentre' qz38 Bool.true Ns114p271 Ns114p272 Ns114p273 

noncomputable def Ns114p275 := nat_lit 1888946593147858085478400000000000000 

noncomputable abbrev qz39 := qz382

noncomputable def Ns114p276 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz39 884279719003555 140737488355328 1 500000000000000 5407179140719 

noncomputable abbrev qz385 := (@HSub.hSub Real Real Real qz634 qz652 qz646)

noncomputable abbrev qz40 := qz385

noncomputable def Ns114p277 := @Enclosure.Real.IsNear.subLit_tf qz40 qz26 4307667512943 17592186044416 11681037 2199023255552 1 16 

noncomputable abbrev qz386 := qz652

noncomputable abbrev qz41 := qz386

noncomputable def Ns114p278 := @Enclosure.Real.IsNear.subLit_ff_n qz41 qz31 3227487703441 17592186044416 5389581 2199023255552 1796521 4194304 3 1048576 

noncomputable def Ns114p279 := @Enclosure.Real.IsNear.mulLit_ff qz31 qz31 1796521 4194304 3 1048576 1796521 4194304 3 1048576 3227487703441 17592186044416 

noncomputable def Ns114p280 := nat_lit 2025783425467771889637841077724969189208695092666514729021073891472703760375475619921 

noncomputable def Ns114p281 := nat_lit 3466537250751077332112698720796095110148055492926080949987665366995300109908547993600 

noncomputable def Ns114p282 := nat_lit 19477287662199928449097144379116528138998645130196793272897473267783453340354641 

noncomputable def Ns114p283 := nat_lit 12222374929678825999220587550751776301780498912319957937584366264356911338458237651025 

noncomputable def Ns114p284 := nat_lit 315454889818348037222255583592444655023473049856273366448877548396572310001677867417600 

noncomputable def Ns114p285 := BSN.cos_dyadic_bound_t 4050053 2097152 4 3 4194304 1440000 Ns114p280 Ns114p281 Ns114p282 Ns114p283 Ns114p284 Ns114p282 1479192 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 4050053) (BSN.cosEvenQ 2097152) 0 3 Ns114p280 Ns114p281 Ns114p282 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 4050053) (BSN.cosOddQ 2097152) 0 3 Ns114p283 Ns114p284 Ns114p282 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p286 := @Ns114p269 413028608 12079595520000 184899 524288 1613393 47185920000 (@Ns114p270 281 8388608 Bool.true 1479192 4194304 1 1440000 (@Ns114p274 Ns114p275 4050053 2097152 281 8388608 (@Ns114p276 17592186044416 11681037 2199023255552 Ns114p271 Ns114p272 Ns114p273 Ns114p275 RS115to132.d35 (@Ns114p277 0 1 86514866251504 5407179140719 17592186044416 11681037 2199023255552 (@Ns114p278 18067667080206876672 4307667512943 17592186044416 11681037 2199023255552 (@Ns114p279 5389581 2199023255552 (Ns114p260 rfl rfl) (Ns114p260 rfl rfl) rfl) (Ns114p260 rfl rfl) rfl rfl) qz370 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 4050053 2097152) (BSN.cos_neg_of_bound 4050053 2097152 Bool.true 1479192 4194304 1 1440000 (Ns114p285 rfl rfl)) rfl rfl) 

noncomputable def Ns114p287 := @Ns114p245 1410314532099634271 83010348331692982272000 (Ns114p246 qz28 (@Enclosure.Real.IsNear.of_eq qz650 (@Inv.inv Real Real.instInv (Real.sqrt qz34)) Bool.false 3077829 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz30 (BSN.t_div_two_pi_nonneg qz29 346706 1000 qz32)) Ns114p250) rfl) (@Ns114p251 4398046511104 4569577206887 98956046499840000 (BSN.correction_mk qz31 (BSN.cos_two_pi_p_ne_zero_mk qz29 346706 1000 7 qz32 rfl rfl (@BSN.floor_sqrt_eq_dec qz29 346706 1000 7 qz32 rfl rfl rfl))) (@Ns114p252 8388608 184899 524288 1613393 47185920000 1722822503259 4398046511104 4569577206887 98956046499840000 Ns114p268 (Ns114p286 rfl) rfl)) 

noncomputable def Ns114p288 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz29) (hardyZApproximantRS₀ qz29) Bool.false 24789408747689725703 36893488147419103232 136099389423031858271 83010348331692982272000 (@Eq.refl Real (hardyZApproximantRS₀ qz29)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz29) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz29) qz29 7) (@HMul.hMul Real Real Real qz5 qz647 (Zeta.RiemannSiegel.correction qz31))) Bool.false 24789408747689725703 36893488147419103232 136099389423031858271 83010348331692982272000 (BSN.hardyZApproximantRS₀_eq qz29 7 (@BSN.floor_sqrt_eq_dec qz29 346706 1000 7 qz32 rfl rfl rfl)) (@Ns114p184 24789408747689725703 36893488147419103232 136099389423031858271 83010348331692982272000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz29) qz29 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 7)) Bool.false 2215399 4194304 13611 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz29) qz29 7) (Ns114p244 (Ns114p243 rfl) rfl rfl)) (Ns114p287 rfl) rfl rfl)) 

theorem RS115to132.d39 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz29) Bool.false 24789408747689725703 36893488147419103232 136099389423031858271 83010348331692982272000 := Ns114p288 

noncomputable abbrev qz654 := (@HMul.hMul Real Real Real qz884 (Real.sqrt qz889) qz886)

noncomputable abbrev qz387 := qz654

noncomputable abbrev qz42 := qz387

noncomputable abbrev qz388 := (@HMul.hMul Real Real Real qz629 (@HMul.hMul Real Real Real qz629 qz654 qz654) qz654)

noncomputable abbrev qz43 := (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz388))

noncomputable abbrev qz44 := (@HMul.hMul Real Real Real qz339 (@HMul.hMul Real Real Real qz339 qz363 qz363) qz363)

noncomputable abbrev qz655 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz42))

noncomputable def Ns114p289 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz354 (@HAdd.hAdd Real Real Real qz354 qz655 qz43) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz44))) Bool.false 

noncomputable def Ns114p290 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz354 qz655 qz43) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz44)) 11219003 268435456 

noncomputable def Ns114p291 := @Enclosure.Real.IsNear.addLit_ff qz655 qz43 1402375 33554432 25 33554432 

noncomputable def Ns114p292 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz42) 25 4 0 1 56095 8388608 1 8388608 1402375 

noncomputable def Ns114p293 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz42) Bool.false 56095 8388608 1 8388608 56095 8388608 1 8388608 

noncomputable def Ns114p294 := @Enclosure.Real.IsNear.mulLit_ff qz19 qz8 22837233 8388608 5 8388608 460791282371 8388608000 345139 8388608000 10523197879875319443 70368744177664000 10185977897937 

noncomputable def Ns114p295 := @Enclosure.Real.IsNear.sqrt_image qz8 460791282371 8388608000 345139 8388608000 31086148 31086172 4194304 qz361 

noncomputable def Ns114p296 := @Enclosure.Real.IsNear.sqrt_image qz18 1942885 262144 3 1048576 11418614 11418619 4194304 (@Enclosure.Real.IsNear.recentre' qz18 Bool.false 62172320 8388608 24 8388608 1942885 262144 3 1048576 (Ns114p295 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz389 := (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 22837233 8388608 5 8388608 22837233 8388608 5 8388608 (Ns114p296 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns114p297 := @Ns114p294 70368744177664000 qz389 

noncomputable def Ns114p298 := Ns114p297 qz361 

noncomputable def Ns114p299 := @Enclosure.Real.IsNear.inv_image qz42 10523197879875319443 70368744177664000 10185977897937 70368744177664000 28047 28048 4194304 (Ns114p298 rfl) rfl rfl 

noncomputable abbrev qz45 := (@Inv.inv Real Real.instInv qz388)

noncomputable def Ns114p300 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz45 1 32 0 1 3 

noncomputable def Ns114p301 := @Enclosure.Real.IsNear.recentre' qz45 Bool.false 3 8388608 1 8388608 

noncomputable def Ns114p302 := nat_lit 1165314662713874168036279672830721888210726802203891231307 

noncomputable def Ns114p303 := nat_lit 348449143727040986586495598010130648530944000000000 

noncomputable def Ns114p304 := nat_lit 3383918374492615133854093520148709068038684228040693 

noncomputable abbrev qz46 := qz388

noncomputable def Ns114p305 := @Enclosure.Real.IsNear.inv_image qz46 Ns114p302 Ns114p303 Ns114p304 Ns114p303 1 2 

noncomputable def Ns114p306 := nat_lit 110737693619012418053816306921293830249 

noncomputable def Ns114p307 := nat_lit 4951760157141521099596496896000000 

noncomputable def Ns114p308 := nat_lit 214378225794200740012376240234151 

noncomputable abbrev qz390 := (@HMul.hMul Real Real Real qz629 qz654 qz654)

noncomputable abbrev qz47 := qz390

noncomputable def Ns114p309 := @Enclosure.Real.IsNear.mulLit_ff qz47 qz42 Ns114p306 Ns114p307 Ns114p308 Ns114p307 10523197879875319443 70368744177664000 10185977897937 

noncomputable def Ns114p310 := @Enclosure.Real.IsNear.mulLit_ff qz42 qz42 10523197879875319443 70368744177664000 10185977897937 70368744177664000 10523197879875319443 70368744177664000 10185977897937 70368744177664000 Ns114p306 

noncomputable def Ns114p311 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz44) 13 10 0 1 415747 8388608 1 

noncomputable def Ns114p312 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz44) Bool.false 415747 8388608 1 8388608 415747 8388608 

noncomputable def Ns114p313 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz19 qz19) qz19 521539211096289 70368744177664 228372355 70368744177664 22837233 8388608 5 8388608 11910512482442137328337 

noncomputable def Ns114p314 := @Enclosure.Real.IsNear.mulLit_ff qz19 qz19 22837233 8388608 5 8388608 22837233 8388608 5 8388608 521539211096289 70368744177664 228372355 

noncomputable def Ns114p315 := @Ns114p314 70368744177664 qz389 

noncomputable def Ns114p316 := Ns114p315 qz389 

noncomputable def Ns114p317 := @Ns114p313 590295810358705651712 7823089879236935 590295810358705651712 (Ns114p316 rfl) qz389 

noncomputable def Ns114p318 := @Enclosure.Real.IsNear.inv_image qz44 11910512482442137328337 590295810358705651712 7823089879236935 590295810358705651712 207873 207874 4194304 (Ns114p317 rfl) 

noncomputable def Ns114p319 := @Ns114p290 201 268435456 5404711 83886080 13 83886080 2391934245011456 142570391 1342177280 1213 1342177280 (@Ns114p291 3 268435456 1 268435456 376447273271296 11219003 268435456 201 268435456 (@Ns114p292 33554432 25 33554432 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns114p293 (Ns114p299 rfl rfl rfl rfl) rfl) rfl) (@Ns114p300 8388608 1 8388608 3 268435456 1 268435456 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns114p301 3 8388608 1 8388608 (@Ns114p305 4194304 (@Ns114p309 70368744177664000 Ns114p302 Ns114p303 Ns114p304 Ns114p303 (@Ns114p310 Ns114p307 Ns114p308 Ns114p307 (Ns114p298 rfl) (Ns114p298 rfl) rfl) (Ns114p298 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns114p311 8388608 5404711 83886080 13 83886080 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns114p312 1 8388608 (Ns114p318 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS115to132.d40 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 := @Ns114p289 142570391 1342177280 1213 1342177280 (BSN.hardyZErrorBoundRS₀_mk qz4 345139 1000 qz11 rfl rfl) (Ns114p319 rfl rfl) 

noncomputable def Ns114p320 := nat_lit 1516071794073270153893642240 

noncomputable abbrev qz894 := (Enclosure.sfrac Bool.false 348272 1000)

noncomputable abbrev qz656 := qz894

noncomputable abbrev qz391 := qz656

noncomputable abbrev qz48 := qz391

noncomputable abbrev qz895 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 348272 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz657 := qz895

noncomputable abbrev qz392 := qz657

noncomputable abbrev qz49 := qz392

noncomputable abbrev qz896 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 348272 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz658 := qz896

noncomputable abbrev qz393 := qz658

noncomputable abbrev qz50 := qz393

noncomputable abbrev qz659 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz49 qz9))

noncomputable def Ns114p321 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz48) qz48 7) (@HMul.hMul Real Real Real qz5 qz659 (Zeta.RiemannSiegel.correction qz50)) 86957555 33554432 54687 33554432 2622961052872307145 18446744073709551616 855027334022213171 51881467707308113920000 Ns114p320 

noncomputable def Ns114p322 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz48) qz48 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 348272 1000 63 97 67108864 33554432 1125899906842624 Bool.false 35208395869 1217 

noncomputable def Ns114p323 := Ns114p322 120242927 48 27397080 8 130587807 48 25364760 8 Bool.true 81765288 40567 Bool.true 27744307 Bool.true 46488215 3537118876014220 1 Bool.false 26960699 Bool.false Bool.false 42858342 Bool.true Bool.true 86957555 

noncomputable def Ns114p324 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz48) qz48 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 348272 1000 26 22 67108864 33554432 1125899906842624 Bool.false 35208395869 1217 

noncomputable def Ns114p325 := Ns114p324 93032624 47 33554424 8 108007536 47 30011992 8 Bool.true 56085761 23889 Bool.false 66964559 Bool.true 88488853 3537118876014220 1 Bool.false 36380418 Bool.true Bool.false 16746636 Bool.true Bool.true 81765288 

noncomputable def Ns114p326 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz48) qz48 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 348272 1000 180 90 67108864 33554432 1125899906842624 Bool.false 35208395869 1217 

noncomputable def Ns114p327 := Ns114p326 46516304 47 47453136 16 73726608 47 38745320 8 Bool.true 67108856 1271 Bool.false 33485370 Bool.false 44190511 3537118876014220 1 Bool.false 58926647 Bool.false Bool.false 53077553 Bool.true Bool.true 56085761 

noncomputable def Ns114p328 := nat_lit 1158064490867384068589599611199606417566751198958569 

noncomputable def Ns114p329 := nat_lit 2207325568259557885849173918142528189410312192000 

noncomputable def Ns114p330 := nat_lit 2459440410931610653752230543360000 

noncomputable def Ns114p331 := nat_lit 5139330328115164036511382828798443520 

noncomputable abbrev qz394 := (@Eq.refl Real qz656)

noncomputable abbrev qz51 := qz394

noncomputable def Ns114p332 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz48 348272 1000 485174543936 16000000 696544 4000 2000 Ns114p330 Ns114p331 qz51 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns114p333 := nat_lit 1517898289469697646381760002391548123633092131498975559680 

noncomputable abbrev qz660 := (Real.log (Enclosure.sfrac Bool.false 485174543936 16000000))

noncomputable abbrev qz52 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 348272 4000) qz660) (@HMul.hMul Real Real Real qz339 qz343 (@HSub.hSub Real Real Real qz342 qz344 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz345 (@Nat.cast Real Real.instNatCast 696544))))))

noncomputable abbrev qz661 := (Enclosure.sfrac Bool.false 348272 2000)

noncomputable abbrev qz395 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz52 qz661) (@HMul.hMul Real Real Real qz5 qz661 (Real.log Real.pi)))

noncomputable def Ns114p334 := @Enclosure.Real.IsNear.addLit_ft_p qz395 (Enclosure.sfrac Bool.true Ns114p330 Ns114p331) 295349700661924208409 562949953421312000 10431885809610227 576000000000000000000 Ns114p330 Ns114p331 0 1 Ns114p333 

noncomputable def Ns114p335 := nat_lit 247757286177022271005340467200 

noncomputable abbrev qz396 := (@HSub.hSub Real Real Real qz12 qz52 qz661)

noncomputable abbrev qz397 := (@HMul.hMul Real Real Real qz5 qz661 (Real.log Real.pi))

noncomputable def Ns114p336 := @Enclosure.Real.IsNear.subLit_ff_p qz396 qz397 81513480573574107909 112589990684262400 69584385971693 9000000000000000000 836087034687 4194304000 21767 2097152000 Ns114p335 295349700661924208409 562949953421312000 

noncomputable abbrev qz398 := qz661

noncomputable def Ns114p337 := @Enclosure.Real.IsNear.subLit_ff_p qz52 qz398 505597255956844125977 562949953421312000 69584385971693 9000000000000000000 348272 2000 0 1 815134805735741079090000 81513480573574107909 112589990684262400 69584385971693 9000000000000000000 

noncomputable def Ns114p338 := nat_lit 1138503806763394247395072565938487296 

noncomputable def Ns114p339 := nat_lit 12475721847767540246249472 

noncomputable def Ns114p340 := nat_lit 34351027368197562835125377615717427014877781971585406521238804322884311410500833439357055937353228085549949074706631580831353643916906739761431424864632580057384953996902400 

noncomputable def Ns114p341 := nat_lit 1078075845246687314169200253529719690688418648855307076223946988659279514085310382747376047113537150003619643272109020712679355767477364060004231632265408391792268085821440 

noncomputable def Ns114p342 := nat_lit 101828338090530905530420780020494554856212169746565840667509781206579651617900787627453933414072125811052809699029428815415691932103061347408531505254410840346460160 

noncomputable def Ns114p343 := BSN.log_dyadic_bound 223030543936 747318543936 8 7 Ns114p340 33554432 11520000 Ns114p341 Ns114p342 20656602 970349087872 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 223030543936) (BSN.artanhQ 747318543936) 0 7 Ns114p341 Ns114p340 Ns114p342 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns114p344 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 348272 4000) qz660 348272 4000 0 1 23237842782898881 2251799813685248 390625063 4500000000000000 505818123855359942727 562949953421312000 8502735746321 1125000000000000000 (Enclosure.Real.IsNear.const Bool.false 348272 4000) (BSN.isNear_log_sfrac 485174543936 16000000 23237842782898881 2251799813685248 390625063 4500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 485174543936) qz350)) Bool.false Ns114p339 Ns114p85 1000000161280000 11520000000000000000000 23237842782898881 2251799813685248 390625063 4500000000000000 (BSN.log_rat_reduce_isNear 485174543936 16000000 14 970349087872 524288000000 20656602 33554432 24973259072661432 36028797018963968 11520000 1000000000000000 rfl rfl rfl rfl (Ns114p343 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p345 := BSN.arctan_dyadic_bound_f 1000 696544 1 0 4194304 1440000 0 1 1 0 1 1 6021 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 696544) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 696544) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz399 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 696544)))

noncomputable def Ns114p346 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz399 884279719003555 562949953421312 1 2000000000000000 6021 4194304 1 1440000 3705548440865937031168 883471594063267 562949953421312 12500000009 18000000000000000 qz16 (Ns114p345 rfl) rfl rfl 

noncomputable def Ns114p347 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 348272 4000) qz660) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz399)) 505818123855359942727 562949953421312000 8502735746321 1125000000000000000 883471594063267 2251799813685248 12500000009 72000000000000000 Ns114p338 505597255956844125977 562949953421312000 69584385971693 9000000000000000000 (Ns114p344 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz399) 1 4 0 1 883471594063267 562949953421312 12500000009 18000000000000000 883471594063267 2251799813685248 12500000009 72000000000000000 qz353 Ns114p346 rfl) 

noncomputable def Ns114p348 := @Ns114p334 Ns114p328 Ns114p329 10431885809610227 576000000000000000000 (@Ns114p336 10431885809610227 576000000000000000000 (Ns114p337 (Ns114p347 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 348272 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz398 (Real.log Real.pi) 348272 2000 0 1 38410761 33554432 1 16777216 836087034687 4194304000 21767 2097152000 (Enclosure.Real.IsNear.const Bool.false 348272 2000) RS115to132.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns114p330 Ns114p331) 

noncomputable def Ns114p349 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz48) Bool.false Ns114p328 Ns114p329 10431885809610227 576000000000000000000 4401049483 8388608 153 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz48) (@HAdd.hAdd Real Real Real qz354 qz395 (Enclosure.sfrac Bool.true Ns114p330 Ns114p331)) Bool.false Ns114p328 Ns114p329 10431885809610227 576000000000000000000 Ns114p332 (Ns114p348 rfl rfl)) 

noncomputable def Ns114p350 := nat_lit 1898987113242901197357056 

noncomputable def Ns114p351 := nat_lit 139992106860207505350906767658374000952658930348753777678528364822560935819695446097920 

noncomputable def Ns114p352 := nat_lit 281279276418540397008627139887499562823904212130967732331468818595642379795483918336 

noncomputable def Ns114p353 := nat_lit 366190589614913448609598995164495003202868020284238327115228101209933315674771575341056 

noncomputable def Ns114p354 := BSN.sin_dyadic_bound_f 26986229972 17179869184 3 2 8388608 2882813 Ns114p351 Ns114p98 Ns114p352 Ns114p353 Ns114p101 Ns114p352 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26986229972) qz355 0 2 Ns114p351 Ns114p98 Ns114p352 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26986229972) qz356 0 2 Ns114p353 Ns114p101 Ns114p352 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p355 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz48) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4401049483) qz357) Bool.false 4401049483 8388608 153 8388608 Bool.true 8388607 8388608 1 1440000 (Ns114p349 rfl) (Enclosure.sfrac_false_div 4401049483 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4401049483) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns114p350) qz358) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 83 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q1 4401049483 8388608 226375608064910080 72057594037927936 83 Ns114p350 Ns114p85 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns114p350 Ns114p85 26986229972 17179869184 2882813 2880000 (Ns114p354 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p356 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz48) Bool.false Ns114p328 Ns114p329 10431885809610227 576000000000000000000 35208395869 67108864 1217 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz48) (@HAdd.hAdd Real Real Real qz354 qz395 (Enclosure.sfrac Bool.true Ns114p330 Ns114p331)) Bool.false Ns114p328 Ns114p329 10431885809610227 576000000000000000000 Ns114p332 (Ns114p348 rfl rfl)) 

noncomputable def Ns114p357 := Ns114p327 23889 BSN.abs_quadSignPos (BSN.cos_quad_nat0 180 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 58926647 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 90 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 53077553 67108864) qz51 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 1) Bool.true 8388607 8388608 893393 47185920000 67108856 67108864 1271 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz48)) Bool.true 8388607 8388608 893393 47185920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz48) qz48) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz48)) Bool.true 8388607 8388608 228708608 12079595520000 8388607 8388608 893393 47185920000 (Ns114p355 rfl rfl) rfl)) rfl) (Ns114p356 rfl) RS115to132.d7 

noncomputable def Ns114p358 := nat_lit 42841558665226500151945051425695935056820627354098684540976800000 

noncomputable def Ns114p359 := nat_lit 1580668565513393967984805786520695078632358028525792100000000 

noncomputable def Ns114p360 := nat_lit 128521514658548473667899184665514763780304617346239002038730400000 

noncomputable def Ns114p361 := BSN.cos_dyadic_bound_f 33485370 67108864 3 2 67108864 33554432 Ns114p358 Ns114p113 Ns114p359 Ns114p360 Ns114p116 Ns114p359 58926647 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 33485370) qz360 0 2 Ns114p358 Ns114p113 Ns114p359 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 33485370) (BSN.cosOddQ 67108864) 0 2 Ns114p360 Ns114p116 Ns114p359 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p362 := nat_lit 129955159424030516177009903482350029883445482502812029627130552961 

noncomputable def Ns114p363 := nat_lit 14542269495822200626630493215633034722453596547822171101962881 

noncomputable def Ns114p364 := nat_lit 389836393733099904129776449460618823580891540315340444539187733121 

noncomputable def Ns114p365 := BSN.cos_dyadic_bound_f 44190511 67108864 3 2 67108864 33554432 Ns114p362 Ns114p113 Ns114p363 Ns114p364 Ns114p116 Ns114p363 53077553 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 44190511) qz360 0 2 Ns114p362 Ns114p113 Ns114p363 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 44190511) (BSN.cosOddQ 67108864) 0 2 Ns114p364 Ns114p116 Ns114p363 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p366 := nat_lit 685590987480067407544940298633980217316743587361808173589520112001 

noncomputable def Ns114p367 := nat_lit 404352474156800155367292506766794689381534532061456277700008321 

noncomputable def Ns114p368 := nat_lit 2055964257491888622324086310888407062571467693021301608213160319361 

noncomputable def Ns114p369 := BSN.cos_dyadic_bound_f 66964559 67108864 3 2 67108864 33554432 Ns114p366 Ns114p113 Ns114p367 Ns114p368 Ns114p116 Ns114p367 36380418 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 66964559) qz360 0 2 Ns114p366 Ns114p113 Ns114p367 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 66964559) (BSN.cosOddQ 67108864) 0 2 Ns114p368 Ns114p116 Ns114p367 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p370 := nat_lit 504312862781320839879426993022200848817055097114460146779762104279358648214705620479035296638925743121 

noncomputable def Ns114p371 := nat_lit 3996645342911614855169325114413848961633120431781532997847909552396155328908156533147964360867027353600 

noncomputable def Ns114p372 := nat_lit 230495679555903643119556335445219814576818647439384735907655084340249857562857167321240502477841 

noncomputable def Ns114p373 := nat_lit 3055833305674158806853976658103093947161076202863464510492930169961168591799272431342421541249767646225 

noncomputable def Ns114p374 := nat_lit 363694726204956951820408585411660255508613959292119502804159769268050134930642244516464756838899489177600 

noncomputable def Ns114p375 := BSN.cos_dyadic_bound_f 88488853 67108864 4 3 67108864 33554432 Ns114p370 Ns114p371 Ns114p372 Ns114p373 Ns114p374 Ns114p372 16746636 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 88488853) qz360 0 3 Ns114p370 Ns114p371 Ns114p372 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 88488853) (BSN.cosOddQ 67108864) 0 3 Ns114p373 Ns114p374 Ns114p372 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p376 := Ns114p325 40567 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 26 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 36380418 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 22 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 16746636 67108864) qz51 rfl rfl (Ns114p357 RS115to132.d9 RS115to132.d11 RS115to132.d13 RS115to132.d17 (Ns114p361 rfl rfl) (Ns114p365 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns114p356 rfl) RS115to132.d19 RS115to132.d21 RS115to132.d23 RS115to132.d25 RS115to132.d17 (Ns114p369 rfl rfl) (Ns114p375 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns114p377 := nat_lit 592509783428086992020413242001 

noncomputable def Ns114p378 := BSN.sin_dyadic_bound_f 27744307 67108864 2 1 67108864 33554432 Ns114p377 Ns114p231 Ns114p377 Ns114p377 Ns114p232 Ns114p377 26960699 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 27744307) qz359 0 1 Ns114p377 Ns114p231 Ns114p377 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 27744307) (BSN.sinOddQ 67108864) 0 1 Ns114p377 Ns114p232 Ns114p377 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p379 := nat_lit 286487640140963022928990976102180800661981694787781100618992130625 

noncomputable def Ns114p380 := nat_lit 21814384703254852297555502822864666373548356105429118437890625 

noncomputable def Ns114p381 := nat_lit 750289453270145504576970799929712697035823455677160759238937090625 

noncomputable def Ns114p382 := BSN.sin_dyadic_bound_f 46488215 67108864 3 2 67108864 33554432 Ns114p379 Ns114p107 Ns114p380 Ns114p381 Ns114p110 Ns114p380 42858342 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 46488215) qz359 0 2 Ns114p379 Ns114p107 Ns114p380 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 46488215) (BSN.sinOddQ 67108864) 0 2 Ns114p381 Ns114p110 Ns114p380 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p383 := Ns114p323 54687 BSN.abs_quadSignPos (BSN.cos_quad_nat3 63 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 26960699 67108864) BSN.abs_quadSignNeg qz637 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 42858342 67108864) qz51 rfl rfl (Ns114p376 rfl rfl) (Ns114p356 rfl) RS115to132.d27 RS115to132.d29 RS115to132.d31 RS115to132.d33 RS115to132.d17 (Ns114p378 rfl rfl) (Ns114p382 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns114p384 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 7) 86957555 67108864 54687 67108864 86957555 67108864 54687 67108864 11671245464535040 86957555 33554432 54687 33554432 (Ns114p383 rfl) 

noncomputable def Ns114p385 := @Enclosure.Real.IsNear.mulLit_tf qz659 (Zeta.RiemannSiegel.correction qz50) 768591 2097152 1 4194304 3412687701095 8796093022208 2212432070723 49478023249920000 2622961052872307145 18446744073709551616 

noncomputable abbrev qz662 := (@HPow.hPow Real Real Real qz7 qz49 qz9)

noncomputable def Ns114p386 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz662 1 1 0 1 768591 2097152 1 4194304 768591 2097152 1 4194304 

noncomputable def Ns114p387 := @Enclosure.Real.IsNear.sqrt_image qz49 29060882263 524288000 21767 524288000 31226922 31226946 4194304 (@Enclosure.Real.IsNear.of_eq qz49 (@HMul.hMul Real Real Real qz5 qz48 qz3) Bool.false 29060882263 524288000 21767 524288000 (BSN.t_div_two_pi_mk qz48 348272 1000 qz51) (@Enclosure.Real.IsNear.mulLit_ff qz48 qz3 348272 1000 0 1 1335089 8388608 1 8388608 29060882263 524288000 21767 524288000 (Enclosure.Real.IsNear.const Bool.false 348272 1000) RS115to132.d36 rfl)) 

noncomputable abbrev qz897 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 348272 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz663 := qz897

noncomputable abbrev qz400 := qz663

noncomputable abbrev qz53 := qz400

noncomputable def Ns114p388 := @Enclosure.Real.IsNear.sqrt_image qz53 15613467 2097152 3 1048576 11444439 11444445 4194304 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 62453868 8388608 24 8388608 15613467 2097152 3 1048576 (Ns114p387 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns114p389 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz53) 5722221 2097152 3 4194304 1537181 1537183 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz53) Bool.false 22888884 8388608 6 8388608 5722221 2097152 3 4194304 (Ns114p388 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns114p390 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz53)) Bool.false 3074364 8388608 2 8388608 768591 2097152 1 4194304 (Ns114p389 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz54 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz393))

noncomputable abbrev qz664 := (@HMul.hMul Real Real Real qz884 qz896 qz896)

noncomputable abbrev qz401 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz664 qz658) qz642)

noncomputable abbrev qz55 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz401))

noncomputable def Ns114p391 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz50) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz54) qz55) Bool.false 3412687701095 

noncomputable def Ns114p392 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz54) qz55 2228515 2097152 89 

noncomputable abbrev qz665 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz54))

noncomputable def Ns114p393 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz54) (@Neg.neg Real Real.instNeg qz665) Bool.true 2228515 2097152 89 4194304 (BSN.inv_eq_neg_inv_neg qz54) 

noncomputable def Ns114p394 := @Enclosure.Real.IsNear.recentre' qz665 Bool.false 8914060 8388608 178 8388608 2228515 2097152 

noncomputable def Ns114p395 := @Enclosure.Real.IsNear.recentre' qz54 Bool.true 7894129 8388608 225828608 12079595520000 7894129 8388608 882143 47185920000 

noncomputable abbrev qz56 := (@HMul.hMul Real Real Real qz339 qz337 qz393)

noncomputable def Ns114p396 := @Enclosure.Real.IsNear.cos_image qz56 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 733093) (@Nat.cast Real Real.instNatCast 262144)) Bool.false 733093 262144 151 8388608 Bool.true 7894129 8388608 1 

noncomputable def Ns114p397 := nat_lit 80958226231141071724495189 

noncomputable def Ns114p398 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz50 884279719003555 140737488355328 1 500000000000000 933403 2097152 3 1048576 825389342557075247665 295147905179352825856 Ns114p397 

noncomputable def Ns114p399 := @Enclosure.Real.IsNear.subLit_ff_p qz53 qz1 15613467 2097152 3 1048576 7 1 0 1 933403 933403 2097152 3 

noncomputable def Ns114p400 := @Ns114p399 1048576 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 62453868 8388608 24 8388608 15613467 2097152 3 1048576 (Ns114p387 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns114p401 := @Enclosure.Real.IsNear.recentre' qz56 Bool.false 825389342557075247665 295147905179352825856 Ns114p397 Ns114p150 733093 262144 151 8388608 (@Ns114p398 Ns114p150 RS115to132.d35 (Ns114p400 rfl rfl) rfl) 

noncomputable def Ns114p402 := nat_lit 51837745361746160588656053795456284378641764653671841696638882615053956878684562080000 

noncomputable def Ns114p403 := nat_lit 38665328027472737803837113872032801151760281007005102534632220657556818000987504896 

noncomputable def Ns114p404 := nat_lit 135702922559195464728131071279926025027911295542748243801379097539314795072172254249216 

noncomputable def Ns114p405 := BSN.sin_dyadic_bound_f 21057907438 17179869184 3 2 8388608 2882813 Ns114p402 Ns114p98 Ns114p403 Ns114p404 Ns114p101 Ns114p403 7894129 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 21057907438) qz355 0 2 Ns114p402 Ns114p98 Ns114p403 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 21057907438) qz356 0 2 Ns114p404 Ns114p101 Ns114p403 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p406 := @Ns114p396 1440000 (Ns114p401 rfl) (Enclosure.sfrac_false_div 733093 262144) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 733093) (@Nat.cast Real Real.instNatCast 262144)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 46306828171525620760576) (@Nat.cast Real Real.instNatCast 37778931862957161709568)) 226375608064910080 72057594037927936 Bool.false 7894129 8388608 0 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q1 733093 262144 226375608064910080 72057594037927936 0 46306828171525620760576 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 7894129 8388608 46306828171525620760576 37778931862957161709568 21057907438 17179869184 2882813 2880000 (Ns114p405 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p407 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz54) 7894129 8388608 882143 47185920000 4456941 4457119 4194304 (@Enclosure.Real.IsNear.neg qz54 Bool.true 7894129 8388608 882143 47185920000 (Ns114p395 (Ns114p406 rfl rfl) rfl)) 

noncomputable def Ns114p408 := Ns114p393 (@Enclosure.Real.IsNear.neg qz665 Bool.false 2228515 2097152 89 4194304 (@Ns114p394 89 4194304 (Ns114p407 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p409 := @Enclosure.Real.IsNear.recentre' qz55 Bool.true 1531373 4194304 

noncomputable abbrev qz57 := (@HMul.hMul Real Real Real qz339 qz337 qz401)

noncomputable def Ns114p410 := @Enclosure.Real.IsNear.cos_image qz57 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 2039003)) (@Nat.cast Real Real.instNatCast 1048576)) Bool.true 2039003 1048576 

noncomputable def Ns114p411 := nat_lit 1203614980324179422090082005 

noncomputable def Ns114p412 := nat_lit 618970019642690137449562112 

noncomputable def Ns114p413 := nat_lit 3209154942740535979317648697907 

noncomputable def Ns114p414 := @Enclosure.Real.IsNear.recentre' qz57 Bool.true Ns114p411 Ns114p412 Ns114p413 

noncomputable def Ns114p415 := nat_lit 94447329657392904273920000000000000 

noncomputable abbrev qz58 := qz401

noncomputable def Ns114p416 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz58 884279719003555 140737488355328 1 500000000000000 1361124714791 

noncomputable abbrev qz402 := (@HSub.hSub Real Real Real qz634 qz664 qz658)

noncomputable abbrev qz59 := qz402

noncomputable def Ns114p417 := @Enclosure.Real.IsNear.subLit_tf qz59 qz26 1086246807847 4398046511104 2972973 549755813888 1 16 

noncomputable abbrev qz403 := qz664

noncomputable abbrev qz60 := qz403

noncomputable def Ns114p418 := @Enclosure.Real.IsNear.subLit_ff_n qz60 qz50 871241160409 4398046511104 1400109 549755813888 933403 2097152 3 1048576 

noncomputable def Ns114p419 := @Enclosure.Real.IsNear.mulLit_ff qz50 qz50 933403 2097152 3 1048576 933403 2097152 3 1048576 871241160409 4398046511104 

noncomputable def Ns114p420 := nat_lit 508488792894354356162406950213765206557298774110675496613168866502133402761261521 

noncomputable def Ns114p421 := nat_lit 846322570984149739285326836131859157750990110577656481930582364989086940895641600 

noncomputable def Ns114p422 := nat_lit 5164334652718579775353456413443299604411409507703481781401806784471347327441 

noncomputable def Ns114p423 := nat_lit 3067451113279730806966289688526174536418727459233199789582795683171114218925158865 

noncomputable def Ns114p424 := nat_lit 77015353959557626274964742087999183355340100062566739855682995214006911621503385600 

noncomputable def Ns114p425 := BSN.cos_dyadic_bound_t 2039003 1048576 4 3 4194304 1440000 Ns114p420 Ns114p421 Ns114p422 Ns114p423 Ns114p424 Ns114p422 1531373 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 2039003) (BSN.cosEvenQ 1048576) 0 3 Ns114p420 Ns114p421 Ns114p422 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 2039003) (BSN.cosOddQ 1048576) 0 3 Ns114p423 Ns114p424 Ns114p422 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p426 := @Ns114p409 210114304 6039797760000 1531373 4194304 820759 23592960000 (@Ns114p410 143 4194304 Bool.true 1531373 4194304 1 1440000 (@Ns114p414 Ns114p415 2039003 1048576 143 4194304 (@Ns114p416 4398046511104 2972973 549755813888 Ns114p411 Ns114p412 Ns114p413 Ns114p415 RS115to132.d35 (@Ns114p417 0 1 21777995436656 1361124714791 4398046511104 2972973 549755813888 (@Ns114p418 2278024665569951744 1086246807847 4398046511104 2972973 549755813888 (@Ns114p419 1400109 549755813888 (Ns114p400 rfl rfl) (Ns114p400 rfl rfl) rfl) (Ns114p400 rfl rfl) rfl rfl) qz370 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 2039003 1048576) (BSN.cos_neg_of_bound 2039003 1048576 Bool.true 1531373 4194304 1 1440000 (Ns114p425 rfl rfl)) rfl rfl) 

noncomputable def Ns114p427 := @Ns114p385 855027334022213171 51881467707308113920000 (Ns114p386 qz28 (@Enclosure.Real.IsNear.of_eq qz662 (@Inv.inv Real Real.instInv (Real.sqrt qz53)) Bool.false 768591 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz49 (BSN.t_div_two_pi_nonneg qz48 348272 1000 qz51)) Ns114p390) rfl) (@Ns114p391 8796093022208 2212432070723 49478023249920000 (BSN.correction_mk qz50 (BSN.cos_two_pi_p_ne_zero_mk qz48 348272 1000 7 qz51 rfl rfl (@BSN.floor_sqrt_eq_dec qz48 348272 1000 7 qz51 rfl rfl rfl))) (@Ns114p392 4194304 1531373 4194304 820759 23592960000 3412687701095 8796093022208 2212432070723 49478023249920000 Ns114p408 (Ns114p426 rfl) rfl)) 

noncomputable def Ns114p428 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz48) (hardyZApproximantRS₀ qz48) Bool.true 45182460369863216695 18446744073709551616 85411422879908933171 51881467707308113920000 (@Eq.refl Real (hardyZApproximantRS₀ qz48)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz48) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz48) qz48 7) (@HMul.hMul Real Real Real qz5 qz659 (Zeta.RiemannSiegel.correction qz50))) Bool.true 45182460369863216695 18446744073709551616 85411422879908933171 51881467707308113920000 (BSN.hardyZApproximantRS₀_eq qz48 7 (@BSN.floor_sqrt_eq_dec qz48 348272 1000 7 qz51 rfl rfl rfl)) (@Ns114p321 45182460369863216695 18446744073709551616 85411422879908933171 51881467707308113920000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz48) qz48 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 7)) Bool.true 86957555 33554432 54687 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz48) qz48 7) (Ns114p384 (Ns114p383 rfl) rfl rfl)) (Ns114p427 rfl) rfl rfl)) 

theorem RS115to132.d41 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz48) Bool.true 45182460369863216695 18446744073709551616 85411422879908933171 51881467707308113920000 := Ns114p428 

noncomputable def Ns114p429 := nat_lit 67026611370283279587475456 

noncomputable abbrev qz898 := (Enclosure.sfrac Bool.false 349836 1000)

noncomputable abbrev qz666 := qz898

noncomputable abbrev qz404 := qz666

noncomputable abbrev qz61 := qz404

noncomputable abbrev qz899 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 349836 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz667 := qz899

noncomputable abbrev qz405 := qz667

noncomputable abbrev qz62 := qz405

noncomputable abbrev qz900 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 349836 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz668 := qz900

noncomputable abbrev qz406 := qz668

noncomputable abbrev qz63 := qz406

noncomputable abbrev qz669 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz62 qz9))

noncomputable def Ns114p430 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz61) qz61 7) (@HMul.hMul Real Real Real qz5 qz669 (Zeta.RiemannSiegel.correction qz63)) 12167977 16777216 13733 8388608 650389311721160853 4611686018427387904 2325530220913752671 138350580552821637120000 Ns114p429 

noncomputable def Ns114p431 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 349836 1000 63 97 67108864 33554432 1125899906842624 Bool.false 35419222934 1222 

noncomputable def Ns114p432 := Ns114p431 120242927 48 27397080 8 130587807 48 25364760 8 Bool.false 36513891 40749 Bool.true 4977180 Bool.true 39900480 3537118876014220 1 Bool.false 4972618 Bool.false Bool.false 37590842 Bool.true Bool.false 24335954 

noncomputable def Ns114p433 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 349836 1000 27 22 67108864 33554432 1125899906842624 Bool.false 35419222934 1222 

noncomputable def Ns114p434 := Ns114p433 93032624 47 33554424 8 108007536 47 30011992 8 Bool.false 46499638 23997 Bool.false 26874243 Bool.true 46585574 3537118876014220 1 Bool.false 26161693 Bool.false Bool.false 51578470 Bool.true Bool.false 36513891 

noncomputable def Ns114p435 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 349836 1000 181 91 67108864 33554432 1125899906842624 Bool.false 35419222934 1222 

noncomputable def Ns114p436 := Ns114p435 46516304 47 47453136 16 73726608 47 38745320 8 Bool.false 67108856 1279 Bool.false 66146578 Bool.false 34294804 3537118876014220 1 Bool.false 55944448 Bool.true Bool.false 32821469 Bool.false Bool.false 46499638 

noncomputable def Ns114p437 := nat_lit 66485760229117889162583664092850445956541037670099 

noncomputable def Ns114p438 := nat_lit 125970686861741864561460972110340915353092096000 

noncomputable def Ns114p439 := nat_lit 2515162088283979336972824084480000 

noncomputable def Ns114p440 := nat_lit 5279370498637095005498960376684871680 

noncomputable abbrev qz407 := (@Eq.refl Real qz666)

noncomputable abbrev qz64 := qz407

noncomputable def Ns114p441 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz61 349836 1000 489541907584 16000000 699672 4000 2000 Ns114p439 Ns114p440 qz64 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns114p442 := nat_lit 6274383526620676777189079534384227429739337760436555612160 

noncomputable abbrev qz670 := (Real.log (Enclosure.sfrac Bool.false 489541907584 16000000))

noncomputable abbrev qz65 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 349836 4000) qz670) (@HMul.hMul Real Real Real qz339 qz343 (@HSub.hSub Real Real Real qz342 qz344 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz345 (@Nat.cast Real Real.instNatCast 699672))))))

noncomputable abbrev qz671 := (Enclosure.sfrac Bool.false 349836 2000)

noncomputable abbrev qz408 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz65 qz671) (@HMul.hMul Real Real Real qz5 qz671 (Real.log Real.pi)))

noncomputable def Ns114p443 := @Enclosure.Real.IsNear.addLit_ft_p qz408 (Enclosure.sfrac Bool.true Ns114p439 Ns114p440) 1188472980231634495787 2251799813685248000 41913134608474879 2304000000000000000000 Ns114p439 Ns114p440 0 1 Ns114p442 

noncomputable def Ns114p444 := nat_lit 19939267899509861968869588992000 

noncomputable abbrev qz409 := (@HSub.hSub Real Real Real qz12 qz65 qz671)

noncomputable abbrev qz410 := (@HMul.hMul Real Real Real qz5 qz671 (Real.log Real.pi))

noncomputable def Ns114p445 := @Enclosure.Real.IsNear.subLit_ff_p qz409 qz410 1639359552438638684459 2251799813685248000 69889854770959 9000000000000000000 3359366746299 16777216000 87459 8388608000 Ns114p444 1188472980231634495787 2251799813685248000 

noncomputable def Ns114p446 := nat_lit 3278719104877277368918000 

noncomputable abbrev qz411 := qz671

noncomputable def Ns114p447 := @Enclosure.Real.IsNear.subLit_ff_p qz65 qz411 2033239872248834894123 2251799813685248000 69889854770959 9000000000000000000 349836 2000 0 1 Ns114p446 1639359552438638684459 2251799813685248000 69889854770959 9000000000000000000 

noncomputable def Ns114p448 := nat_lit 4578449165507343860032815812526997504 

noncomputable def Ns114p449 := nat_lit 12486555490858360597643264 

noncomputable def Ns114p450 := nat_lit 37270809111619848204262267508515713494486374018591413409692611701419873257310396278630400220183420991348496127651659774390924826055953666433206870995256499487038379550310400 

noncomputable def Ns114p451 := nat_lit 1203792442996975297724678043798211683680842884895474909238759138953177284986675365572172280617967363494249030059322514430043483219718897894020094060587003973032432883466240 

noncomputable def Ns114p452 := nat_lit 133591351819772370910761403617732597685897179736587878739325166660060681248368802186962515902451954540597850016772636760632877445198300145739270029775154525356687360 

noncomputable def Ns114p453 := BSN.log_dyadic_bound 227397907584 751685907584 8 7 Ns114p450 33554432 11520000 Ns114p451 Ns114p452 20957296 979083815168 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 227397907584) (BSN.artanhQ 751685907584) 0 7 Ns114p451 Ns114p450 Ns114p452 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns114p454 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 349836 4000) qz670 349836 4000 0 1 23258022015650497 2251799813685248 390625063 4500000000000000 2034123347466776817123 2251799813685248000 11387892461639 1500000000000000000 (Enclosure.Real.IsNear.const Bool.false 349836 4000) (BSN.isNear_log_sfrac 489541907584 16000000 23258022015650497 2251799813685248 390625063 4500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 489541907584) qz350)) Bool.false Ns114p449 Ns114p85 1000000161280000 11520000000000000000000 23258022015650497 2251799813685248 390625063 4500000000000000 (BSN.log_rat_reduce_isNear 489541907584 16000000 14 979083815168 524288000000 20957296 33554432 24973259072661432 36028797018963968 11520000 1000000000000000 rfl rfl rfl rfl (Ns114p453 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p455 := BSN.arctan_dyadic_bound_f 1000 699672 1 0 4194304 1440000 0 1 1 0 1 1 5994 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 699672) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 699672) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz412 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 699672)))

noncomputable def Ns114p456 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz412 884279719003555 562949953421312 1 2000000000000000 5994 4194304 1 1440000 3705563640514679406592 883475217941923 562949953421312 12500000009 18000000000000000 qz16 (Ns114p455 rfl) rfl rfl 

noncomputable def Ns114p457 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 349836 4000) qz670) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz412)) 2034123347466776817123 2251799813685248000 11387892461639 1500000000000000000 883475217941923 2251799813685248 12500000009 72000000000000000 Ns114p448 2033239872248834894123 2251799813685248000 69889854770959 9000000000000000000 (Ns114p454 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz412) 1 4 0 1 883475217941923 562949953421312 12500000009 18000000000000000 883475217941923 2251799813685248 12500000009 72000000000000000 qz353 Ns114p456 rfl) 

noncomputable def Ns114p458 := @Ns114p443 Ns114p437 Ns114p438 41913134608474879 2304000000000000000000 (@Ns114p445 41913134608474879 2304000000000000000000 (Ns114p447 (Ns114p457 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 349836 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz411 (Real.log Real.pi) 349836 2000 0 1 38410761 33554432 1 16777216 3359366746299 16777216000 87459 8388608000 (Enclosure.Real.IsNear.const Bool.false 349836 2000) RS115to132.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns114p439 Ns114p440) 

noncomputable def Ns114p459 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz61) Bool.false Ns114p437 Ns114p438 41913134608474879 2304000000000000000000 2213701433 4194304 77 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz61) (@HAdd.hAdd Real Real Real qz354 qz408 (Enclosure.sfrac Bool.true Ns114p439 Ns114p440)) Bool.false Ns114p437 Ns114p438 41913134608474879 2304000000000000000000 Ns114p441 (Ns114p458 rfl rfl)) 

noncomputable def Ns114p460 := nat_lit 139983323884761517313815069768770745489937315803579599242513081904809424654265319276800 

noncomputable def Ns114p461 := nat_lit 281244053886107496643177760333145184939206377263088249210878245317184716881096458496 

noncomputable def Ns114p462 := nat_lit 366167643610940752255902894925288765031362826303330140850716649734463527410030251458816 

noncomputable def Ns114p463 := BSN.sin_dyadic_bound_f 26985807538 17179869184 3 2 8388608 2882813 Ns114p460 Ns114p98 Ns114p461 Ns114p462 Ns114p101 Ns114p461 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26985807538) qz355 0 2 Ns114p460 Ns114p98 Ns114p461 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26985807538) qz356 0 2 Ns114p462 Ns114p101 Ns114p461 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p464 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz61) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2213701433) qz366) Bool.false 2213701433 4194304 77 4194304 Bool.false 8388607 8388608 1 1440000 (Ns114p459 rfl) (Enclosure.sfrac_false_div 2213701433 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2213701433) qz366) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949478693543312806117376) qz380) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 83 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q3 2213701433 4194304 226375608064910080 72057594037927936 83 949478693543312806117376 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 949478693543312806117376 604462909807314587353088 26985807538 17179869184 2882813 2880000 (Ns114p463 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p465 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz61) Bool.false Ns114p437 Ns114p438 41913134608474879 2304000000000000000000 35419222934 67108864 1222 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz61) (@HAdd.hAdd Real Real Real qz354 qz408 (Enclosure.sfrac Bool.true Ns114p439 Ns114p440)) Bool.false Ns114p437 Ns114p438 41913134608474879 2304000000000000000000 Ns114p441 (Ns114p458 rfl rfl)) 

noncomputable def Ns114p466 := Ns114p436 23997 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 181 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 55944448 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 91 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 32821469 67108864) qz64 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 1) Bool.false 8388607 8388608 449509 23592960000 67108856 67108864 1279 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz61)) Bool.false 8388607 8388608 449509 23592960000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz61) qz61) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz61)) Bool.false 8388607 8388608 115074304 6039797760000 8388607 8388608 449509 23592960000 (Ns114p464 rfl rfl) rfl)) rfl) (Ns114p465 rfl) RS115to132.d7 

noncomputable def Ns114p467 := nat_lit 1174536168035669735770261762319965297386590891592296012137029648640 

noncomputable def Ns114p468 := nat_lit 366487403322326056035049137369418364576077503062758757735547136 

noncomputable def Ns114p469 := nat_lit 3075572793821375065783771678901311006279376781070102231893982003456 

noncomputable def Ns114p470 := BSN.sin_dyadic_bound_f 66146578 67108864 3 2 67108864 33554432 Ns114p467 Ns114p107 Ns114p468 Ns114p469 Ns114p110 Ns114p468 55944448 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 66146578) qz359 0 2 Ns114p467 Ns114p107 Ns114p468 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 66146578) (BSN.sinOddQ 67108864) 0 2 Ns114p469 Ns114p110 Ns114p468 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p471 := nat_lit 1383290201293064434774127309056 

noncomputable def Ns114p472 := BSN.sin_dyadic_bound_f 34294804 67108864 2 1 67108864 33554432 Ns114p471 Ns114p231 Ns114p471 Ns114p471 Ns114p232 Ns114p471 32821469 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 34294804) qz359 0 1 Ns114p471 Ns114p231 Ns114p471 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 34294804) (BSN.sinOddQ 67108864) 0 1 Ns114p471 Ns114p232 Ns114p471 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p473 := nat_lit 521608859369057119377137656401 

noncomputable def Ns114p474 := BSN.sin_dyadic_bound_f 26874243 67108864 2 1 67108864 33554432 Ns114p473 Ns114p231 Ns114p473 Ns114p473 Ns114p232 Ns114p473 26161693 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 26874243) qz359 0 1 Ns114p473 Ns114p231 Ns114p473 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 26874243) (BSN.sinOddQ 67108864) 0 1 Ns114p473 Ns114p232 Ns114p473 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p475 := nat_lit 160507252073105776693385561493047819675489168076945925782387302656 

noncomputable def Ns114p476 := nat_lit 22182557085801140757163882037436828799091865883429761328619776 

noncomputable def Ns114p477 := nat_lit 481477391105145727798642356715068585368869320499070917824504668416 

noncomputable def Ns114p478 := BSN.cos_dyadic_bound_f 46585574 67108864 3 2 67108864 33554432 Ns114p475 Ns114p113 Ns114p476 Ns114p477 Ns114p116 Ns114p476 51578470 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 46585574) qz360 0 2 Ns114p475 Ns114p113 Ns114p476 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 46585574) (BSN.cosOddQ 67108864) 0 2 Ns114p477 Ns114p116 Ns114p476 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p479 := Ns114p434 40749 BSN.abs_quadSignPos (BSN.cos_quad_nat3 27 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 26161693 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 22 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 51578470 67108864) qz64 rfl rfl (Ns114p466 RS115to132.d9 RS115to132.d11 RS115to132.d13 RS115to132.d17 (Ns114p470 rfl rfl) (Ns114p472 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns114p465 rfl) RS115to132.d19 RS115to132.d21 RS115to132.d23 RS115to132.d25 RS115to132.d17 (Ns114p474 rfl rfl) (Ns114p478 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns114p480 := nat_lit 613667875459787702105760000 

noncomputable def Ns114p481 := BSN.sin_dyadic_bound_f 4977180 67108864 2 1 67108864 33554432 Ns114p480 Ns114p231 Ns114p480 Ns114p480 Ns114p232 Ns114p480 4972618 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 4977180) qz359 0 1 Ns114p480 Ns114p231 Ns114p480 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 4977180) (BSN.sinOddQ 67108864) 0 1 Ns114p480 Ns114p232 Ns114p480 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p482 := nat_lit 155464689450305475739736577984105190937114389050557034072637440000 

noncomputable def Ns114p483 := nat_lit 6424287407299208430061667168057794197752760380266905600000000 

noncomputable def Ns114p484 := nat_lit 407159023523569190123756652021051025549455609710843228533555200000 

noncomputable def Ns114p485 := BSN.sin_dyadic_bound_f 39900480 67108864 3 2 67108864 33554432 Ns114p482 Ns114p107 Ns114p483 Ns114p484 Ns114p110 Ns114p483 37590842 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 39900480) qz359 0 2 Ns114p482 Ns114p107 Ns114p483 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 39900480) (BSN.sinOddQ 67108864) 0 2 Ns114p484 Ns114p110 Ns114p483 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p486 := Ns114p432 54932 BSN.abs_quadSignPos (BSN.cos_quad_nat3 63 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 4972618 67108864) BSN.abs_quadSignNeg qz637 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 37590842 67108864) qz64 rfl rfl (Ns114p479 rfl rfl) (Ns114p465 rfl) RS115to132.d27 RS115to132.d29 RS115to132.d31 RS115to132.d33 RS115to132.d17 (Ns114p481 rfl rfl) (Ns114p485 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns114p487 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 7) 24335954 67108864 54932 67108864 24335954 67108864 54932 67108864 3266316454592512 12167977 16777216 13733 8388608 (Ns114p486 rfl) 

noncomputable def Ns114p488 := @Enclosure.Real.IsNear.mulLit_tf qz669 (Zeta.RiemannSiegel.correction qz63) 1535461 4194304 1 4194304 423579180273 1099511627776 3012543254741 65970697666560000 650389311721160853 4611686018427387904 

noncomputable abbrev qz672 := (@HPow.hPow Real Real Real qz7 qz62 qz9)

noncomputable def Ns114p489 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz672 1 1 0 1 1535461 4194304 1 4194304 1535461 4194304 1 4194304 

noncomputable def Ns114p490 := @Enclosure.Real.IsNear.sqrt_image qz62 116765548851 2097152000 87459 2097152000 31296959 31296984 4194304 (@Enclosure.Real.IsNear.of_eq qz62 (@HMul.hMul Real Real Real qz5 qz61 qz3) Bool.false 116765548851 2097152000 87459 2097152000 (BSN.t_div_two_pi_mk qz61 349836 1000 qz64) (@Enclosure.Real.IsNear.mulLit_ff qz61 qz3 349836 1000 0 1 1335089 8388608 1 8388608 116765548851 2097152000 87459 2097152000 (Enclosure.Real.IsNear.const Bool.false 349836 1000) RS115to132.d36 rfl)) 

noncomputable abbrev qz901 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 349836 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz673 := qz901

noncomputable abbrev qz413 := qz673

noncomputable abbrev qz66 := qz413

noncomputable def Ns114p491 := @Enclosure.Real.IsNear.sqrt_image qz66 62593943 8388608 25 8388608 11457266 11457272 4194304 (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 62593943 8388608 25 8388608 62593943 8388608 25 8388608 (Ns114p490 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns114p492 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz66) 11457269 4194304 3 4194304 1535460 1535462 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz66) Bool.false 22914538 8388608 6 8388608 11457269 4194304 3 4194304 (Ns114p491 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns114p493 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz66)) Bool.false 3070922 8388608 2 8388608 1535461 4194304 1 4194304 (Ns114p492 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz67 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz406))

noncomputable abbrev qz674 := (@HMul.hMul Real Real Real qz884 qz900 qz900)

noncomputable abbrev qz414 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz674 qz668) qz642)

noncomputable abbrev qz68 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz414))

noncomputable def Ns114p494 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz63) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz67) qz68) Bool.false 423579180273 

noncomputable def Ns114p495 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz67) qz68 269889 262144 87 

noncomputable abbrev qz675 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz67))

noncomputable def Ns114p496 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz67) (@Neg.neg Real Real.instNeg qz675) Bool.true 269889 262144 87 4194304 (BSN.inv_eq_neg_inv_neg qz67) 

noncomputable def Ns114p497 := @Enclosure.Real.IsNear.recentre' qz675 Bool.false 8636448 8388608 174 8388608 269889 262144 

noncomputable def Ns114p498 := @Enclosure.Real.IsNear.recentre' qz67 Bool.true 8147880 8388608 117954304 6039797760000 1018485 1048576 460759 23592960000 

noncomputable abbrev qz69 := (@HMul.hMul Real Real Real qz339 qz337 qz406)

noncomputable def Ns114p499 := @Enclosure.Real.IsNear.cos_image qz69 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24339093) qz357) Bool.false 24339093 8388608 79 4194304 Bool.true 8147880 8388608 1 

noncomputable def Ns114p500 := nat_lit 674651885259375854339104879 

noncomputable def Ns114p501 := nat_lit 36028797018963968000000000000000 

noncomputable def Ns114p502 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz63 884279719003555 140737488355328 1 500000000000000 3873687 8388608 25 8388608 3425422851867723957285 1180591620717411303424 Ns114p500 

noncomputable def Ns114p503 := @Enclosure.Real.IsNear.subLit_ff_p qz66 qz1 62593943 8388608 25 8388608 7 1 0 1 3873687 3873687 8388608 25 

noncomputable def Ns114p504 := @Ns114p503 8388608 (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 62593943 8388608 25 8388608 62593943 8388608 25 8388608 (Ns114p490 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns114p505 := @Enclosure.Real.IsNear.recentre' qz69 Bool.false 3425422851867723957285 1180591620717411303424 Ns114p500 Ns114p501 24339093 8388608 79 4194304 (@Ns114p502 Ns114p501 RS115to132.d35 (Ns114p504 rfl rfl) rfl) 

noncomputable def Ns114p506 := nat_lit 1608656728472577906835456 

noncomputable def Ns114p507 := nat_lit 72018742623637314909183206060211158468306276600356261281652191775740349221811503448320 

noncomputable def Ns114p508 := nat_lit 74587943644824674254079979754253556932961849246122143415368348658095322315463803136 

noncomputable def Ns114p509 := nat_lit 188499754962672775289544648285712814039101167149772677029273715419587807916233662873856 

noncomputable def Ns114p510 := BSN.sin_dyadic_bound_f 22860387054 17179869184 3 2 8388608 2882813 Ns114p507 Ns114p98 Ns114p508 Ns114p509 Ns114p101 Ns114p508 8147880 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 22860387054) qz355 0 2 Ns114p507 Ns114p98 Ns114p508 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 22860387054) qz356 0 2 Ns114p509 Ns114p101 Ns114p508 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p511 := @Ns114p499 1440000 (Ns114p505 rfl) (Enclosure.sfrac_false_div 24339093 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24339093) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns114p506) qz358) 226375608064910080 72057594037927936 Bool.false 8147880 8388608 0 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q1 24339093 8388608 226375608064910080 72057594037927936 0 Ns114p506 Ns114p85 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8147880 8388608 Ns114p506 Ns114p85 22860387054 17179869184 2882813 2880000 (Ns114p510 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p512 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz67) 1018485 1048576 460759 23592960000 4318137 4318311 4194304 (@Enclosure.Real.IsNear.neg qz67 Bool.true 1018485 1048576 460759 23592960000 (Ns114p498 (Ns114p511 rfl rfl) rfl)) 

noncomputable def Ns114p513 := Ns114p496 (@Enclosure.Real.IsNear.neg qz675 Bool.false 269889 262144 87 4194304 (@Ns114p497 87 4194304 (Ns114p512 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p514 := @Enclosure.Real.IsNear.recentre' qz68 Bool.true 1569457 4194304 

noncomputable abbrev qz70 := (@HMul.hMul Real Real Real qz339 qz337 qz414)

noncomputable def Ns114p515 := @Enclosure.Real.IsNear.cos_image qz70 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8196999)) qz366) Bool.true 8196999 4194304 

noncomputable def Ns114p516 := nat_lit 19354616900781086672072124205 

noncomputable def Ns114p517 := nat_lit 9903520314283042199192993792 

noncomputable def Ns114p518 := nat_lit 10886187542759576174072215652063177 

noncomputable def Ns114p519 := @Enclosure.Real.IsNear.recentre' qz70 Bool.true Ns114p516 Ns114p517 Ns114p518 

noncomputable def Ns114p520 := nat_lit 302231454903657293676544000000000000000 

noncomputable abbrev qz71 := qz414

noncomputable def Ns114p521 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz71 884279719003555 140737488355328 1 500000000000000 21887437294831 

noncomputable abbrev qz415 := (@HSub.hSub Real Real Real qz634 qz674 qz668)

noncomputable abbrev qz72 := qz415

noncomputable def Ns114p522 := @Enclosure.Real.IsNear.subLit_tf qz72 qz26 17489390783727 70368744177664 403400175 70368744177664 1 16 

noncomputable abbrev qz416 := qz674

noncomputable abbrev qz73 := qz416

noncomputable def Ns114p523 := @Enclosure.Real.IsNear.subLit_ff_n qz73 qz63 15005450973969 70368744177664 193684975 70368744177664 3873687 8388608 25 8388608 

noncomputable def Ns114p524 := @Enclosure.Real.IsNear.mulLit_ff qz63 qz63 3873687 8388608 25 8388608 3873687 8388608 25 8388608 15005450973969 70368744177664 

noncomputable def Ns114p525 := nat_lit 8705300891162616421211225654657621368042700639937607741492083332070864772619046916443681 

noncomputable def Ns114p526 := nat_lit 92014990422788453123898788503496959757555632232011203029318196555455027533295636001 

noncomputable def Ns114p527 := nat_lit 52508614825333056406970284799179198709303392071451283628184610459820343868715435383311905 

noncomputable def Ns114p528 := BSN.cos_dyadic_bound_t 8196999 4194304 4 3 4194304 1440000 Ns114p525 Ns114p175 Ns114p526 Ns114p527 Ns114p178 Ns114p526 1569457 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 8196999) (BSN.cosEvenQ 4194304) 0 3 Ns114p525 Ns114p175 Ns114p526 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 8196999) (BSN.cosOddQ 4194304) 0 3 Ns114p527 Ns114p178 Ns114p526 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p529 := @Ns114p514 444708608 12079595520000 1569457 4194304 1737143 47185920000 (@Ns114p515 303 8388608 Bool.true 1569457 4194304 1 1440000 (@Ns114p519 Ns114p520 8196999 4194304 303 8388608 (@Ns114p521 70368744177664 403400175 70368744177664 Ns114p516 Ns114p517 Ns114p518 Ns114p520 RS115to132.d35 (@Ns114p522 0 1 350198996717296 21887437294831 70368744177664 403400175 70368744177664 (@Ns114p523 146711643443498582016 17489390783727 70368744177664 403400175 70368744177664 (@Ns114p524 193684975 70368744177664 (Ns114p504 rfl rfl) (Ns114p504 rfl rfl) rfl) (Ns114p504 rfl rfl) rfl rfl) qz370 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 8196999 4194304) (BSN.cos_neg_of_bound 8196999 4194304 Bool.true 1569457 4194304 1 1440000 (Ns114p528 rfl rfl)) rfl rfl) 

noncomputable def Ns114p530 := @Ns114p488 2325530220913752671 138350580552821637120000 (Ns114p489 qz28 (@Enclosure.Real.IsNear.of_eq qz672 (@Inv.inv Real Real.instInv (Real.sqrt qz66)) Bool.false 1535461 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz62 (BSN.t_div_two_pi_nonneg qz61 349836 1000 qz64)) Ns114p493) rfl) (@Ns114p494 1099511627776 3012543254741 65970697666560000 (BSN.correction_mk qz63 (BSN.cos_two_pi_p_ne_zero_mk qz61 349836 1000 7 qz64 rfl rfl (@BSN.floor_sqrt_eq_dec qz61 349836 1000 7 qz64 rfl rfl rfl))) (@Ns114p495 4194304 1569457 4194304 1737143 47185920000 423579180273 1099511627776 3012543254741 65970697666560000 Ns114p513 (Ns114p529 rfl) rfl)) 

noncomputable def Ns114p531 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz61) (hardyZApproximantRS₀ qz61) Bool.false 3995097361223893141 4611686018427387904 228819427984630872671 138350580552821637120000 (@Eq.refl Real (hardyZApproximantRS₀ qz61)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz61) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz61) qz61 7) (@HMul.hMul Real Real Real qz5 qz669 (Zeta.RiemannSiegel.correction qz63))) Bool.false 3995097361223893141 4611686018427387904 228819427984630872671 138350580552821637120000 (BSN.hardyZApproximantRS₀_eq qz61 7 (@BSN.floor_sqrt_eq_dec qz61 349836 1000 7 qz64 rfl rfl rfl)) (@Ns114p430 3995097361223893141 4611686018427387904 228819427984630872671 138350580552821637120000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz61) qz61 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 7)) Bool.false 12167977 16777216 13733 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz61) qz61 7) (Ns114p487 (Ns114p486 rfl) rfl rfl)) (Ns114p530 rfl) rfl rfl)) 

theorem RS115to132.d42 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz61) Bool.false 3995097361223893141 4611686018427387904 228819427984630872671 138350580552821637120000 := Ns114p531 

noncomputable def Ns114p532 := nat_lit 869306220712899397621383168 

noncomputable abbrev qz902 := (Enclosure.sfrac Bool.false 351398 1000)

noncomputable abbrev qz676 := qz902

noncomputable abbrev qz417 := qz676

noncomputable abbrev qz74 := qz417

noncomputable abbrev qz903 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 351398 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz677 := qz903

noncomputable abbrev qz418 := qz677

noncomputable abbrev qz75 := qz418

noncomputable abbrev qz904 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 351398 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz678 := qz904

noncomputable abbrev qz419 := qz678

noncomputable abbrev qz76 := qz419

noncomputable abbrev qz679 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz75 qz9))

noncomputable def Ns114p533 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz74) qz74 7) (@HMul.hMul Real Real Real qz5 qz679 (Zeta.RiemannSiegel.correction qz76)) 51830715 33554432 13795 8388608 2586892665907125621 18446744073709551616 1659354809511610339 103762935414616227840000 Ns114p532 

noncomputable def Ns114p534 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz74) qz74 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 351398 1000 62 97 67108864 33554432 1125899906842624 Bool.false 35630014439 1228 

noncomputable def Ns114p535 := Ns114p534 120242927 48 27397080 8 130587807 48 25364760 8 Bool.true 32566840 40934 Bool.true 87419484 Bool.true 33087129 3537118876014220 1 Bool.false 17780004 Bool.true Bool.false 31762829 Bool.true Bool.true 51830715 

noncomputable def Ns114p536 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz74) qz74 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 351398 1000 27 22 67108864 33554432 1125899906842624 Bool.false 35630014439 1228 

noncomputable def Ns114p537 := Ns114p536 93032624 47 33554424 8 108007536 47 30011992 8 Bool.true 35542840 24107 Bool.false 92348789 Bool.true 4501840 3537118876014220 1 Bool.false 65840994 Bool.false Bool.false 66957922 Bool.true Bool.true 32566840 

noncomputable def Ns114p538 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz74) qz74 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 351398 1000 182 92 67108864 33554432 1125899906842624 Bool.false 35630014439 1228 

noncomputable def Ns114p539 := Ns114p538 46516304 47 47453136 16 73726608 47 38745320 8 Bool.true 67108848 1287 Bool.false 98865259 Bool.false 24510990 3537118876014220 1 Bool.false 6538707 Bool.true Bool.false 62682180 Bool.false Bool.true 35542840 

noncomputable def Ns114p540 := nat_lit 633077343105648221492955327118025141160169165088397143 

noncomputable def Ns114p541 := nat_lit 1192396410378490925188624603710325465931436785664000 

noncomputable def Ns114p542 := nat_lit 2571815986924211858975797744640000 

noncomputable def Ns114p543 := nat_lit 5422391088261478786028531447802040320 

noncomputable abbrev qz420 := (@Eq.refl Real qz676)

noncomputable abbrev qz77 := qz420

noncomputable def Ns114p544 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz74 351398 1000 493923217616 16000000 702796 4000 2000 Ns114p542 Ns114p543 qz77 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns114p545 := nat_lit 12965423986803675576175725099377154890960264501010373488640 

noncomputable abbrev qz680 := (Real.log (Enclosure.sfrac Bool.false 493923217616 16000000))

noncomputable abbrev qz78 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 351398 4000) qz680) (@HMul.hMul Real Real Real qz339 qz343 (@HSub.hSub Real Real Real qz342 qz344 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz345 (@Nat.cast Real Real.instNatCast 702796))))))

noncomputable abbrev qz681 := (Enclosure.sfrac Bool.false 351398 2000)

noncomputable abbrev qz421 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz78 qz681) (@HMul.hMul Real Real Real qz5 qz681 (Real.log Real.pi)))

noncomputable def Ns114p546 := @Enclosure.Real.IsNear.addLit_ft_p qz421 (Enclosure.sfrac Bool.true Ns114p542 Ns114p543) 2391091929407504245027 4503599627370496000 84196977298782319 4608000000000000000000 Ns114p542 Ns114p543 0 1 Ns114p545 

noncomputable def Ns114p547 := nat_lit 80231731551052901479469809664000 

noncomputable abbrev qz422 := (@HSub.hSub Real Real Real qz12 qz78 qz681)

noncomputable abbrev qz423 := (@HMul.hMul Real Real Real qz5 qz681 (Real.log Real.pi))

noncomputable def Ns114p548 := @Enclosure.Real.IsNear.subLit_ff_p qz422 qz423 3296891445182878179619 4503599627370496000 35097466472581 4500000000000000000 6748732296939 33554432000 175699 16777216000 Ns114p547 2391091929407504245027 4503599627370496000 

noncomputable def Ns114p549 := nat_lit 6593782890365756359238000 

noncomputable abbrev qz424 := qz681

noncomputable def Ns114p550 := @Enclosure.Real.IsNear.subLit_ff_p qz78 qz424 4088169396112246956323 4503599627370496000 35097466472581 4500000000000000000 351398 2000 0 1 Ns114p549 3296891445182878179619 4503599627370496000 35097466472581 4500000000000000000 

noncomputable def Ns114p551 := nat_lit 9205739084479290525605075569925423104 

noncomputable def Ns114p552 := nat_lit 12497327020303120255156224 

noncomputable def Ns114p553 := nat_lit 40430099955895426364990723970120287808827869023667532880133181392787769137949588242681347578456006194961975415249551425288537922547191164827742607063019149829149242582630400 

noncomputable def Ns114p554 := nat_lit 1343107935158479797867058642019222114248536972768219637965105953204269186807329806147256479455931550559295601970170845948893259784600988489670007553002221997949137966858240 

noncomputable def Ns114p555 := nat_lit 174506151807945993233515653020969112407860419593992830644751668939572248139727893674678761226715007041407206880309727399659749989839063841211113960021724457452175360 

noncomputable def Ns114p556 := BSN.log_dyadic_bound 231779217616 756067217616 8 7 Ns114p553 33554432 11520000 Ns114p554 Ns114p555 21256266 987846435232 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 231779217616) (BSN.artanhQ 756067217616) 0 7 Ns114p554 Ns114p553 Ns114p555 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns114p557 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 351398 4000) qz680 351398 4000 0 1 23278085552720577 2251799813685248 390625063 4500000000000000 4089936353527452658323 4503599627370496000 68632432944037 9000000000000000000 (Enclosure.Real.IsNear.const Bool.false 351398 4000) (BSN.isNear_log_sfrac 493923217616 16000000 23278085552720577 2251799813685248 390625063 4500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 493923217616) qz350)) Bool.false Ns114p552 Ns114p85 1000000161280000 11520000000000000000000 23278085552720577 2251799813685248 390625063 4500000000000000 (BSN.log_rat_reduce_isNear 493923217616 16000000 14 987846435232 524288000000 21256266 33554432 24973259072661432 36028797018963968 11520000 1000000000000000 rfl rfl rfl rfl (Ns114p556 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p558 := BSN.arctan_dyadic_bound_f 1000 702796 1 0 4194304 1440000 0 1 1 0 1 1 5968 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 702796) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 702796) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz425 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 702796)))

noncomputable def Ns114p559 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz425 884279719003555 562949953421312 1 2000000000000000 5968 4194304 1 1440000 3705578277213468360704 883478707602851 562949953421312 12500000009 18000000000000000 qz16 (Ns114p558 rfl) rfl rfl 

noncomputable def Ns114p560 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 351398 4000) qz680) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz425)) 4089936353527452658323 4503599627370496000 68632432944037 9000000000000000000 883478707602851 2251799813685248 12500000009 72000000000000000 Ns114p551 4088169396112246956323 4503599627370496000 35097466472581 4500000000000000000 (Ns114p557 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz425) 1 4 0 1 883478707602851 562949953421312 12500000009 18000000000000000 883478707602851 2251799813685248 12500000009 72000000000000000 qz353 Ns114p559 rfl) 

noncomputable def Ns114p561 := @Ns114p546 Ns114p540 Ns114p541 84196977298782319 4608000000000000000000 (@Ns114p548 84196977298782319 4608000000000000000000 (Ns114p550 (Ns114p560 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 351398 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz424 (Real.log Real.pi) 351398 2000 0 1 38410761 33554432 1 16777216 6748732296939 33554432000 175699 16777216000 (Enclosure.Real.IsNear.const Bool.false 351398 2000) RS115to132.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns114p542 Ns114p543) 

noncomputable def Ns114p562 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz74) Bool.false Ns114p540 Ns114p541 84196977298782319 4608000000000000000000 1113437951 2097152 155 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz74) (@HAdd.hAdd Real Real Real qz354 qz421 (Enclosure.sfrac Bool.true Ns114p542 Ns114p543)) Bool.false Ns114p540 Ns114p541 84196977298782319 4608000000000000000000 Ns114p544 (Ns114p561 rfl rfl)) 

noncomputable def Ns114p563 := nat_lit 139785379791593146945658989934497859909564620489640319996568509234985335313876029276160 

noncomputable def Ns114p564 := nat_lit 280450817566894411840928549925669304422236146830274708695728353218853772856829935616 

noncomputable def Ns114p565 := nat_lit 365650502892397555809935851223805216127414195139904202843600630662607257808859494875136 

noncomputable def Ns114p566 := BSN.sin_dyadic_bound_f 26976281744 17179869184 3 2 8388608 2882813 Ns114p563 Ns114p98 Ns114p564 Ns114p565 Ns114p101 Ns114p564 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26976281744) qz355 0 2 Ns114p563 Ns114p98 Ns114p564 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26976281744) qz356 0 2 Ns114p565 Ns114p101 Ns114p564 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p567 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz74) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1113437951) qz383) Bool.false 1113437951 2097152 155 8388608 Bool.true 8388606 8388608 1 1440000 (Ns114p562 rfl) (Enclosure.sfrac_false_div 1113437951 2097152) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1113437951) qz383) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474571767229838211940352) qz384) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 84 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q1 1113437951 2097152 226375608064910080 72057594037927936 84 474571767229838211940352 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388606 8388608 474571767229838211940352 302231454903657293676544 26976281744 17179869184 2882813 2880000 (Ns114p566 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p568 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz74) Bool.false Ns114p540 Ns114p541 84196977298782319 4608000000000000000000 35630014439 67108864 1228 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz74) (@HAdd.hAdd Real Real Real qz354 qz421 (Enclosure.sfrac Bool.true Ns114p542 Ns114p543)) Bool.false Ns114p540 Ns114p541 84196977298782319 4608000000000000000000 Ns114p544 (Ns114p561 rfl rfl)) 

noncomputable def Ns114p569 := Ns114p539 24107 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 182 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 6538707 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 92 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 62682180 67108864) qz77 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 1) Bool.true 4194303 4194304 904643 47185920000 67108848 67108864 1287 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz74)) Bool.true 4194303 4194304 904643 47185920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz74) qz74) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz74)) Bool.true 8388606 8388608 231588608 12079595520000 4194303 4194304 904643 47185920000 (Ns114p567 rfl rfl) rfl)) rfl) (Ns114p568 rfl) RS115to132.d7 

noncomputable def Ns114p570 := nat_lit 786603915305120841585897133644387308192569182506311412156589008271810884413432991857726951733375980561 

noncomputable def Ns114p571 := nat_lit 872016095573522945776266898858202056263943073969489432705500781574946035524371197489279364158481 

noncomputable def Ns114p572 := nat_lit 4763164363741730645474041768723643478008199474910516707531896585000558343595744726777518398978536690705 

noncomputable def Ns114p573 := BSN.cos_dyadic_bound_f 98865259 67108864 4 3 67108864 33554432 Ns114p570 Ns114p371 Ns114p571 Ns114p572 Ns114p374 Ns114p571 6538707 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 98865259) qz360 0 3 Ns114p570 Ns114p371 Ns114p571 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 98865259) (BSN.cosOddQ 67108864) 0 3 Ns114p572 Ns114p374 Ns114p571 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p574 := nat_lit 12299199393557698994373582389197254420202753040511292470448800000 

noncomputable def Ns114p575 := nat_lit 130282721558720661644479997237485326119603739827120100000000 

noncomputable def Ns114p576 := nat_lit 36897337615229979541797458207597288289956019914054223171146400000 

noncomputable def Ns114p577 := BSN.cos_dyadic_bound_f 24510990 67108864 3 2 67108864 33554432 Ns114p574 Ns114p113 Ns114p575 Ns114p576 Ns114p116 Ns114p575 62682180 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 24510990) qz360 0 2 Ns114p574 Ns114p113 Ns114p575 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 24510990) (BSN.cosOddQ 67108864) 0 2 Ns114p576 Ns114p116 Ns114p575 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p578 := nat_lit 1554453698669082159988030440015502286893139907077284885372843522874065424031018488586773308071764607121 

noncomputable def Ns114p579 := nat_lit 51956389457850993117201226487380036501230565613159928972022824181150019275806034930923536691271355596800 

noncomputable def Ns114p580 := nat_lit 384746304586206754859526090400445440271703610828988650730763575002494765499926041579244774015121 

noncomputable def Ns114p581 := nat_lit 7766576162487643472232752816439719569859231687356250858701361402941342809689575577446933263465509339281 

noncomputable def Ns114p582 := nat_lit 1818473631024784759102042927058301277543069796460597514020798846340250674653211222582323784194497445888000 

noncomputable def Ns114p583 := BSN.sin_dyadic_bound_f 92348789 67108864 4 3 67108864 33554432 Ns114p578 Ns114p579 Ns114p580 Ns114p581 Ns114p582 Ns114p580 65840994 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 92348789) qz359 0 3 Ns114p578 Ns114p579 Ns114p580 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 92348789) (BSN.sinOddQ 67108864) 0 3 Ns114p581 Ns114p582 Ns114p580 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p584 := nat_lit 410733591462542534287360000 

noncomputable def Ns114p585 := BSN.cos_dyadic_bound_f 4501840 67108864 2 1 67108864 33554432 Ns114p584 Ns114p227 Ns114p584 Ns114p584 Ns114p228 Ns114p584 66957922 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 4501840) qz360 0 1 Ns114p584 Ns114p227 Ns114p584 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 4501840) (BSN.cosOddQ 67108864) 0 1 Ns114p584 Ns114p228 Ns114p584 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p586 := Ns114p537 40934 BSN.abs_quadSignPos (BSN.cos_quad_nat3 27 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 65840994 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 22 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66957922 67108864) qz77 rfl rfl (Ns114p569 RS115to132.d9 RS115to132.d11 RS115to132.d13 RS115to132.d17 (Ns114p573 rfl rfl) (Ns114p577 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns114p568 rfl) RS115to132.d19 RS115to132.d21 RS115to132.d23 RS115to132.d25 RS115to132.d17 (Ns114p583 rfl rfl) (Ns114p585 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns114p587 := nat_lit 480332184636661235234540975506126283550783235568469503434905406304704395549703476863918736139654004736 

noncomputable def Ns114p588 := nat_lit 199204371395142310457321188340358971616607544123920131220173625979597418385227929982695066566656 

noncomputable def Ns114p589 := nat_lit 2910690246009090782681005822637110488694993915637006077941101404518242665446411017093826331314676039680 

noncomputable def Ns114p590 := BSN.cos_dyadic_bound_f 87419484 67108864 4 3 67108864 33554432 Ns114p587 Ns114p371 Ns114p588 Ns114p589 Ns114p374 Ns114p588 17780004 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 87419484) qz360 0 3 Ns114p587 Ns114p371 Ns114p588 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 87419484) (BSN.cosOddQ 67108864) 0 3 Ns114p589 Ns114p374 Ns114p588 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p591 := nat_lit 1198495309476150994124646694881 

noncomputable def Ns114p592 := BSN.sin_dyadic_bound_f 33087129 67108864 2 1 67108864 33554432 Ns114p591 Ns114p231 Ns114p591 Ns114p591 Ns114p232 Ns114p591 31762829 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 33087129) qz359 0 1 Ns114p591 Ns114p231 Ns114p591 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 33087129) (BSN.sinOddQ 67108864) 0 1 Ns114p591 Ns114p232 Ns114p591 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p593 := Ns114p535 55180 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 62 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 17780004 67108864) BSN.abs_quadSignNeg qz637 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 31762829 67108864) qz77 rfl rfl (Ns114p586 rfl rfl) (Ns114p568 rfl) RS115to132.d27 RS115to132.d29 RS115to132.d31 RS115to132.d33 RS115to132.d17 (Ns114p590 rfl rfl) (Ns114p592 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns114p594 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 7) 51830715 67108864 55180 67108864 51830715 67108864 55180 67108864 6956600807915520 51830715 33554432 13795 8388608 (Ns114p593 rfl) 

noncomputable def Ns114p595 := @Enclosure.Real.IsNear.mulLit_tf qz679 (Zeta.RiemannSiegel.correction qz76) 3067503 8388608 1 8388608 843321967707 2199023255552 269699912933 6184752906240000 2586892665907125621 18446744073709551616 

noncomputable abbrev qz682 := (@HPow.hPow Real Real Real qz7 qz75 qz9)

noncomputable def Ns114p596 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz682 1 1 0 1 3067503 8388608 1 8388608 3067503 8388608 1 8388608 

noncomputable def Ns114p597 := @Enclosure.Real.IsNear.sqrt_image qz75 234573802211 4194304000 175699 4194304000 31366751 31366775 4194304 (@Enclosure.Real.IsNear.of_eq qz75 (@HMul.hMul Real Real Real qz5 qz74 qz3) Bool.false 234573802211 4194304000 175699 4194304000 (BSN.t_div_two_pi_mk qz74 351398 1000 qz77) (@Enclosure.Real.IsNear.mulLit_ff qz74 qz3 351398 1000 0 1 1335089 8388608 1 8388608 234573802211 4194304000 175699 4194304000 (Enclosure.Real.IsNear.const Bool.false 351398 1000) RS115to132.d36 rfl)) 

noncomputable abbrev qz905 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 351398 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz683 := qz905

noncomputable abbrev qz426 := qz683

noncomputable abbrev qz79 := qz426

noncomputable def Ns114p598 := @Enclosure.Real.IsNear.sqrt_image qz79 31366763 4194304 3 1048576 11470034 11470039 4194304 (@Enclosure.Real.IsNear.recentre' qz79 Bool.false 62733526 8388608 24 8388608 31366763 4194304 3 1048576 (Ns114p597 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns114p599 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz79) 22940073 8388608 5 8388608 1533751 1533752 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz79) Bool.false 22940073 8388608 5 8388608 22940073 8388608 5 8388608 (Ns114p598 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns114p600 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz79)) Bool.false 3067503 8388608 1 8388608 3067503 8388608 1 8388608 (Ns114p599 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz80 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz419))

noncomputable abbrev qz684 := (@HMul.hMul Real Real Real qz884 qz904 qz904)

noncomputable abbrev qz427 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz684 qz678) qz642)

noncomputable abbrev qz81 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz427))

noncomputable def Ns114p601 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz76) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz80) qz81) Bool.false 843321967707 

noncomputable def Ns114p602 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz80) qz81 8466323 8388608 161 

noncomputable abbrev qz685 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz80))

noncomputable def Ns114p603 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz80) (@Neg.neg Real Real.instNeg qz685) Bool.true 8466323 8388608 161 8388608 (BSN.inv_eq_neg_inv_neg qz80) 

noncomputable def Ns114p604 := @Enclosure.Real.IsNear.recentre' qz685 Bool.false 8466323 8388608 161 8388608 8466323 8388608 

noncomputable def Ns114p605 := @Enclosure.Real.IsNear.recentre' qz80 Bool.true 8311607 8388608 225828608 12079595520000 8311607 8388608 882143 47185920000 

noncomputable abbrev qz82 := (@HMul.hMul Real Real Real qz339 qz337 qz419)

noncomputable def Ns114p606 := @Enclosure.Real.IsNear.cos_image qz82 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 25216119) qz357) Bool.false 25216119 8388608 151 8388608 Bool.true 8311607 8388608 1 

noncomputable def Ns114p607 := nat_lit 80958226231441352215511381 

noncomputable def Ns114p608 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz76 884279719003555 140737488355328 1 500000000000000 2006635 4194304 3 1048576 1774426633942698587425 590295810358705651712 Ns114p607 

noncomputable def Ns114p609 := @Enclosure.Real.IsNear.subLit_ff_p qz79 qz1 31366763 4194304 3 1048576 7 1 0 1 2006635 2006635 4194304 3 

noncomputable def Ns114p610 := @Ns114p609 1048576 (@Enclosure.Real.IsNear.recentre' qz79 Bool.false 62733526 8388608 24 8388608 31366763 4194304 3 1048576 (Ns114p597 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns114p611 := @Enclosure.Real.IsNear.recentre' qz82 Bool.false 1774426633942698587425 590295810358705651712 Ns114p607 Ns114p150 25216119 8388608 151 8388608 (@Ns114p608 Ns114p150 RS115to132.d35 (Ns114p610 rfl rfl) rfl) 

noncomputable def Ns114p612 := nat_lit 1735049495409993478832128 

noncomputable def Ns114p613 := nat_lit 97498597732325884638692606079685920086135638359212607588767553886484998681595891892480 

noncomputable def Ns114p614 := nat_lit 136601837784820102635363557646296085802581136933267123651489373776443750173817651456 

noncomputable def Ns114p615 := nat_lit 255132305371106655792309093972511977991436778623855349294193563097536944761041154949376 

noncomputable def Ns114p616 := BSN.sin_dyadic_bound_f 24656536302 17179869184 3 2 8388608 2882813 Ns114p613 Ns114p98 Ns114p614 Ns114p615 Ns114p101 Ns114p614 8311607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 24656536302) qz355 0 2 Ns114p613 Ns114p98 Ns114p614 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 24656536302) qz356 0 2 Ns114p615 Ns114p101 Ns114p614 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p617 := @Ns114p606 1440000 (Ns114p611 rfl) (Enclosure.sfrac_false_div 25216119 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 25216119) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns114p612) qz358) 226375608064910080 72057594037927936 Bool.false 8311607 8388608 0 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q1 25216119 8388608 226375608064910080 72057594037927936 0 Ns114p612 Ns114p85 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8311607 8388608 Ns114p612 Ns114p85 24656536302 17179869184 2882813 2880000 (Ns114p616 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p618 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz80) 8311607 8388608 882143 47185920000 4233081 4233242 4194304 (@Enclosure.Real.IsNear.neg qz80 Bool.true 8311607 8388608 882143 47185920000 (Ns114p605 (Ns114p617 rfl rfl) rfl)) 

noncomputable def Ns114p619 := Ns114p603 (@Enclosure.Real.IsNear.neg qz685 Bool.false 8466323 8388608 161 8388608 (@Ns114p604 161 8388608 (Ns114p618 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p620 := @Enclosure.Real.IsNear.recentre' qz81 Bool.true 1593744 4194304 

noncomputable abbrev qz83 := (@HMul.hMul Real Real Real qz339 qz337 qz427)

noncomputable def Ns114p621 := @Enclosure.Real.IsNear.cos_image qz83 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16446445)) qz357) Bool.true 16446445 8388608 

noncomputable def Ns114p622 := nat_lit 4854133973101692114834206005 

noncomputable def Ns114p623 := nat_lit 332235802089215431877211798457477 

noncomputable def Ns114p624 := @Enclosure.Real.IsNear.recentre' qz83 Bool.true Ns114p622 Ns114p272 Ns114p623 

noncomputable def Ns114p625 := nat_lit 9444732965739290427392000000000000000 

noncomputable abbrev qz84 := qz427

noncomputable def Ns114p626 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz84 884279719003555 140737488355328 1 500000000000000 5489364811591 

noncomputable abbrev qz428 := (@HSub.hSub Real Real Real qz634 qz684 qz678)

noncomputable abbrev qz85 := qz428

noncomputable def Ns114p627 := @Enclosure.Real.IsNear.subLit_tf qz85 qz26 4389853183815 17592186044416 12311379 2199023255552 1 16 

noncomputable abbrev qz429 := qz684

noncomputable abbrev qz86 := qz429

noncomputable def Ns114p628 := @Enclosure.Real.IsNear.subLit_ff_n qz86 qz76 4026584023225 17592186044416 6019923 2199023255552 2006635 4194304 3 1048576 

noncomputable def Ns114p629 := @Enclosure.Real.IsNear.mulLit_ff qz76 qz76 2006635 4194304 3 1048576 2006635 4194304 3 1048576 4026584023225 17592186044416 

noncomputable def Ns114p630 := nat_lit 36119402537289080797922580404999601370262771803104716853980430301231537744853005729175640625 

noncomputable def Ns114p631 := nat_lit 58158844227896986633558482781719779619497718984807332131428259197799420928759449934993817600 

noncomputable def Ns114p632 := nat_lit 391619622244649888049083832862082201044223284195213154076776899088169848527617431640625 

noncomputable def Ns114p633 := nat_lit 217848855227719562000016637804878695926150948900727389663365987479379762558300045514545240625 

noncomputable def Ns114p634 := nat_lit 5292454824738625783653821933136499945374292427617467223959971586999747304517109944084437401600 

noncomputable def Ns114p635 := BSN.cos_dyadic_bound_t 16446445 8388608 4 3 4194304 1440000 Ns114p630 Ns114p631 Ns114p632 Ns114p633 Ns114p634 Ns114p632 1593744 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16446445) (BSN.cosEvenQ 8388608) 0 3 Ns114p630 Ns114p631 Ns114p632 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16446445) (BSN.cosOddQ 8388608) 0 3 Ns114p633 Ns114p634 Ns114p632 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p636 := @Ns114p620 54328576 1509949440000 99609 262144 212221 5898240000 (@Ns114p621 37 1048576 Bool.true 1593744 4194304 1 1440000 (@Ns114p624 Ns114p625 16446445 8388608 37 1048576 (@Ns114p626 17592186044416 12311379 2199023255552 Ns114p622 Ns114p272 Ns114p623 Ns114p625 RS115to132.d35 (@Ns114p627 0 1 87829836985456 5489364811591 17592186044416 12311379 2199023255552 (@Ns114p628 18412378768287989760 4389853183815 17592186044416 12311379 2199023255552 (@Ns114p629 6019923 2199023255552 (Ns114p610 rfl rfl) (Ns114p610 rfl rfl) rfl) (Ns114p610 rfl rfl) rfl rfl) qz370 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16446445 8388608) (BSN.cos_neg_of_bound 16446445 8388608 Bool.true 1593744 4194304 1 1440000 (Ns114p635 rfl rfl)) rfl rfl) 

noncomputable def Ns114p637 := @Ns114p595 1659354809511610339 103762935414616227840000 (Ns114p596 qz28 (@Enclosure.Real.IsNear.of_eq qz682 (@Inv.inv Real Real.instInv (Real.sqrt qz79)) Bool.false 3067503 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz75 (BSN.t_div_two_pi_nonneg qz74 351398 1000 qz77)) Ns114p600) rfl) (@Ns114p601 2199023255552 269699912933 6184752906240000 (BSN.correction_mk qz76 (BSN.cos_two_pi_p_ne_zero_mk qz74 351398 1000 7 qz77 rfl rfl (@BSN.floor_sqrt_eq_dec qz74 351398 1000 7 qz77 rfl rfl rfl))) (@Ns114p602 8388608 99609 262144 212221 5898240000 843321967707 2199023255552 269699912933 6184752906240000 Ns114p619 (Ns114p636 rfl) rfl)) 

noncomputable def Ns114p638 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz74) (hardyZApproximantRS₀ qz74) Bool.true 25907344243314844299 18446744073709551616 172296687492673210339 103762935414616227840000 (@Eq.refl Real (hardyZApproximantRS₀ qz74)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz74) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz74) qz74 7) (@HMul.hMul Real Real Real qz5 qz679 (Zeta.RiemannSiegel.correction qz76))) Bool.true 25907344243314844299 18446744073709551616 172296687492673210339 103762935414616227840000 (BSN.hardyZApproximantRS₀_eq qz74 7 (@BSN.floor_sqrt_eq_dec qz74 351398 1000 7 qz77 rfl rfl rfl)) (@Ns114p533 25907344243314844299 18446744073709551616 172296687492673210339 103762935414616227840000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz74) qz74 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 7)) Bool.true 51830715 33554432 13795 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz74) qz74 7) (Ns114p594 (Ns114p593 rfl) rfl rfl)) (Ns114p637 rfl) rfl rfl)) 

theorem RS115to132.d43 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz74) Bool.true 25907344243314844299 18446744073709551616 172296687492673210339 103762935414616227840000 := Ns114p638 

noncomputable def Ns114p639 := nat_lit 5912485783504185137353981952 

noncomputable abbrev qz906 := (Enclosure.sfrac Bool.false 352959 1000)

noncomputable abbrev qz686 := qz906

noncomputable abbrev qz430 := qz686

noncomputable abbrev qz87 := qz430

noncomputable abbrev qz907 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 352959 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz687 := qz907

noncomputable abbrev qz431 := qz687

noncomputable abbrev qz88 := qz431

noncomputable abbrev qz908 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 352959 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz688 := qz908

noncomputable abbrev qz432 := qz688

noncomputable abbrev qz89 := qz432

noncomputable abbrev qz689 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz88 qz9))

noncomputable def Ns114p640 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz87) qz87 7) (@HMul.hMul Real Real Real qz5 qz689 (Zeta.RiemannSiegel.correction qz89)) 37719129 16777216 55419 33554432 20630647464650657765 147573952589676412928 13923446106260435803 830103483316929822720000 Ns114p639 

noncomputable def Ns114p641 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz87) qz87 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 352959 1000 62 97 67108864 33554432 1125899906842624 Bool.false 35840903768 1233 

noncomputable def Ns114p642 := Ns114p641 120242927 48 27397080 8 130587807 48 25364760 8 Bool.false 100815170 41110 Bool.true 64229364 Bool.true 26045367 3537118876014220 1 Bool.false 38647973 Bool.true Bool.false 25396420 Bool.true Bool.false 75438258 

noncomputable def Ns114p643 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz87) qz87 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 352959 1000 28 21 67108864 33554432 1125899906842624 Bool.false 35840903768 1233 

noncomputable def Ns114p644 := Ns114p643 93032624 47 33554424 8 108007536 47 30011992 8 Bool.false 102429265 24208 Bool.false 52599835 Bool.true 67626632 3537118876014220 1 Bool.false 47528975 Bool.false Bool.false 56748229 Bool.true Bool.false 100815170 

noncomputable def Ns114p645 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz87) qz87 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 352959 1000 184 93 67108864 33554432 1125899906842624 Bool.false 35840903768 1233 

noncomputable def Ns114p646 := Ns114p645 46516304 47 47453136 16 73726608 47 38745320 8 Bool.false 67108856 1287 Bool.false 26313924 Bool.false 14898727 3537118876014220 1 Bool.false 62015674 Bool.false Bool.false 14776640 Bool.true Bool.false 102429265 

noncomputable def Ns114p647 := nat_lit 9301157783954268642520943301088097590970787213115623151 

noncomputable def Ns114p648 := nat_lit 17415580164794912606614930074290341022530191491072000 

noncomputable def Ns114p649 := nat_lit 2629448969969864925925924223520000 

noncomputable def Ns114p650 := nat_lit 5568531288814221137056903311752374080 

noncomputable abbrev qz433 := (@Eq.refl Real qz686)

noncomputable abbrev qz90 := qz433

noncomputable def Ns114p651 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz87 352959 1000 498321222724 16000000 705918 4000 2000 Ns114p649 Ns114p650 qz90 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns114p652 := nat_lit 26787334417788293690460316707133721061995867173772994674880 

noncomputable abbrev qz690 := (Real.log (Enclosure.sfrac Bool.false 498321222724 16000000))

noncomputable abbrev qz91 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 352959 4000) qz690) (@HMul.hMul Real Real Real qz339 qz343 (@HSub.hSub Real Real Real qz342 qz344 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz345 (@Nat.cast Real Real.instNatCast 705918))))))

noncomputable abbrev qz691 := (Enclosure.sfrac Bool.false 352959 2000)

noncomputable abbrev qz434 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz91 qz691) (@HMul.hMul Real Real Real qz5 qz691 (Real.log Real.pi)))

noncomputable def Ns114p653 := @Enclosure.Real.IsNear.addLit_ft_p qz434 (Enclosure.sfrac Bool.true Ns114p649 Ns114p650) 4810488926508891444511 9007199254740992000 169134896102994379 9216000000000000000000 Ns114p649 Ns114p650 0 1 Ns114p652 

noncomputable def Ns114p654 := nat_lit 322826447142591190740452245504000 

noncomputable abbrev qz435 := (@HSub.hSub Real Real Real qz12 qz91 qz691)

noncomputable abbrev qz436 := (@HMul.hMul Real Real Real qz5 qz691 (Real.log Real.pi))

noncomputable def Ns114p655 := @Enclosure.Real.IsNear.subLit_ff_p qz435 qz436 6630135545377298257183 9007199254740992000 140999631613667 18000000000000000000 13557423791799 67108864000 352959 33554432000 Ns114p654 4810488926508891444511 9007199254740992000 

noncomputable def Ns114p656 := nat_lit 13260271090754596514366000 

noncomputable abbrev qz437 := qz691

noncomputable def Ns114p657 := @Enclosure.Real.IsNear.subLit_ff_p qz91 qz437 8219721566254361154847 9007199254740992000 140999631613667 18000000000000000000 352959 2000 0 1 Ns114p656 6630135545377298257183 9007199254740992000 140999631613667 18000000000000000000 

noncomputable def Ns114p658 := nat_lit 18509167491436185322751607116247597056 

noncomputable def Ns114p659 := nat_lit 12508043930091599163293696 

noncomputable def Ns114p660 := nat_lit 43850052252515821153226294292169662344853710784505450261877573535122699449566502297626809622258855271399198480850375567346251211337031064145193095735513930153013906138726400 

noncomputable def Ns114p661 := nat_lit 1497496750730535353550123682003431145022048789650938616268408046487748391431597577036869565492660439465815067822607317336234965013516060313327983558147842256235017367715840 

noncomputable def Ns114p662 := nat_lit 227038758983454655848588274536523841679517458448045248730081147393805322625752017634896155174296438083933587397889195660444084814976128485502826208160959682062581760 

noncomputable def Ns114p663 := BSN.log_dyadic_bound 236177222724 760465222724 8 7 Ns114p660 33554432 11520000 Ns114p661 Ns114p662 21553720 996642445448 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 236177222724) (BSN.artanhQ 760465222724) 0 7 Ns114p661 Ns114p660 Ns114p662 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns114p664 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 352959 4000) qz690 352959 4000 0 1 23298047352752833 2251799813685248 390625063 4500000000000000 8223255495580287182847 9007199254740992000 45958210537139 6000000000000000000 (Enclosure.Real.IsNear.const Bool.false 352959 4000) (BSN.isNear_log_sfrac 498321222724 16000000 23298047352752833 2251799813685248 390625063 4500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 498321222724) qz350)) Bool.false Ns114p659 Ns114p85 1000000161280000 11520000000000000000000 23298047352752833 2251799813685248 390625063 4500000000000000 (BSN.log_rat_reduce_isNear 498321222724 16000000 14 996642445448 524288000000 21553720 33554432 24973259072661432 36028797018963968 11520000 1000000000000000 rfl rfl rfl rfl (Ns114p663 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p665 := BSN.arctan_dyadic_bound_f 1000 705918 1 0 4194304 1440000 0 1 1 0 1 1 5941 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 705918) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 705918) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz438 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 705918)))

noncomputable def Ns114p666 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz438 884279719003555 562949953421312 1 2000000000000000 5941 4194304 1 1440000 3705593476862210736128 883482331481507 562949953421312 12500000009 18000000000000000 qz16 (Ns114p665 rfl) rfl rfl 

noncomputable def Ns114p667 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 352959 4000) qz690) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz438)) 8223255495580287182847 9007199254740992000 45958210537139 6000000000000000000 883482331481507 2251799813685248 12500000009 72000000000000000 Ns114p658 8219721566254361154847 9007199254740992000 140999631613667 18000000000000000000 (Ns114p664 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz438) 1 4 0 1 883482331481507 562949953421312 12500000009 18000000000000000 883482331481507 2251799813685248 12500000009 72000000000000000 qz353 Ns114p666 rfl) 

noncomputable def Ns114p668 := @Ns114p653 Ns114p647 Ns114p648 169134896102994379 9216000000000000000000 (@Ns114p655 169134896102994379 9216000000000000000000 (Ns114p657 (Ns114p667 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 352959 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz437 (Real.log Real.pi) 352959 2000 0 1 38410761 33554432 1 16777216 13557423791799 67108864000 352959 33554432000 (Enclosure.Real.IsNear.const Bool.false 352959 2000) RS115to132.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns114p649 Ns114p650) 

noncomputable def Ns114p669 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz87) Bool.false Ns114p647 Ns114p648 169134896102994379 9216000000000000000000 4480112971 8388608 155 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz87) (@HAdd.hAdd Real Real Real qz354 qz434 (Enclosure.sfrac Bool.true Ns114p649 Ns114p650)) Bool.false Ns114p647 Ns114p648 169134896102994379 9216000000000000000000 Ns114p651 (Ns114p668 rfl rfl)) 

noncomputable def Ns114p670 := nat_lit 1899379135387059724746752 

noncomputable def Ns114p671 := nat_lit 140107973676498333351553434094646365952336663407325410534936002380456418869127390511360 

noncomputable def Ns114p672 := nat_lit 281744144934107697145232353906340858700773952671386045694626116439788287007584502016 

noncomputable def Ns114p673 := nat_lit 366493297679983270125357189293939739913461436810098593041326802046007154097321362145536 

noncomputable def Ns114p674 := BSN.sin_dyadic_bound_f 26991800942 17179869184 3 2 8388608 2882813 Ns114p671 Ns114p98 Ns114p672 Ns114p673 Ns114p101 Ns114p672 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26991800942) qz355 0 2 Ns114p671 Ns114p98 Ns114p672 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26991800942) qz356 0 2 Ns114p673 Ns114p101 Ns114p672 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p675 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz87) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4480112971) qz357) Bool.false 4480112971 8388608 155 8388608 Bool.false 8388607 8388608 1 1440000 (Ns114p669 rfl) (Enclosure.sfrac_false_div 4480112971 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4480112971) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns114p670) qz358) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 84 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q3 4480112971 8388608 226375608064910080 72057594037927936 84 Ns114p670 Ns114p85 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns114p670 Ns114p85 26991800942 17179869184 2882813 2880000 (Ns114p674 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p676 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz87) Bool.false Ns114p647 Ns114p648 169134896102994379 9216000000000000000000 35840903768 67108864 1233 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz87) (@HAdd.hAdd Real Real Real qz354 qz434 (Enclosure.sfrac Bool.true Ns114p649 Ns114p650)) Bool.false Ns114p647 Ns114p648 169134896102994379 9216000000000000000000 Ns114p651 (Ns114p668 rfl rfl)) 

noncomputable def Ns114p677 := Ns114p646 24208 BSN.abs_quadSignPos (BSN.cos_quad_nat0 184 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 62015674 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 93 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 14776640 67108864) qz90 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 1) Bool.false 8388607 8388608 904643 47185920000 67108856 67108864 1287 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz87)) Bool.false 8388607 8388608 904643 47185920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz87) qz87) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz87)) Bool.false 8388607 8388608 231588608 12079595520000 8388607 8388608 904643 47185920000 (Ns114p675 rfl rfl) rfl)) rfl) (Ns114p676 rfl) RS115to132.d7 

noncomputable def Ns114p678 := nat_lit 16337191721141106013288002907693070864945126436510755296976633856 

noncomputable def Ns114p679 := nat_lit 229871393306493088458152972123324242496024805407881366142976 

noncomputable def Ns114p680 := nat_lit 49011115420636705053687092417134965946350387259921450128197615616 

noncomputable def Ns114p681 := BSN.cos_dyadic_bound_f 26313924 67108864 3 2 67108864 33554432 Ns114p678 Ns114p113 Ns114p679 Ns114p680 Ns114p116 Ns114p679 62015674 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 26313924) qz360 0 2 Ns114p678 Ns114p113 Ns114p679 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 26313924) (BSN.cosOddQ 67108864) 0 2 Ns114p680 Ns114p116 Ns114p679 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p682 := nat_lit 49271598182210911534461039841 

noncomputable def Ns114p683 := BSN.sin_dyadic_bound_f 14898727 67108864 2 1 67108864 33554432 Ns114p682 Ns114p231 Ns114p682 Ns114p682 Ns114p232 Ns114p682 14776640 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 14898727) qz359 0 1 Ns114p682 Ns114p231 Ns114p682 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 14898727) (BSN.sinOddQ 67108864) 0 1 Ns114p682 Ns114p232 Ns114p682 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p684 := nat_lit 260893892165958951916449337357447723752996099584378336513273190625 

noncomputable def Ns114p685 := nat_lit 58596955829078770357256583863964142318548605054009491500390625 

noncomputable def Ns114p686 := nat_lit 782564482586218698208633498904615242974351201543026990556818790625 

noncomputable def Ns114p687 := BSN.cos_dyadic_bound_f 52599835 67108864 3 2 67108864 33554432 Ns114p684 Ns114p113 Ns114p685 Ns114p686 Ns114p116 Ns114p685 47528975 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 52599835) qz360 0 2 Ns114p684 Ns114p113 Ns114p685 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 52599835) (BSN.cosOddQ 67108864) 0 2 Ns114p686 Ns114p116 Ns114p685 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p688 := nat_lit 1283277103903245078049233062788007978838104359337218950769577820160 

noncomputable def Ns114p689 := nat_lit 437463749364833451008190610624656997028423850163486902427058176 

noncomputable def Ns114p690 := nat_lit 3360255568914289283589216189170438118961751112030546844649726672896 

noncomputable def Ns114p691 := BSN.sin_dyadic_bound_f 67626632 67108864 3 2 67108864 33554432 Ns114p688 Ns114p107 Ns114p689 Ns114p690 Ns114p110 Ns114p689 56748229 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 67626632) qz359 0 2 Ns114p688 Ns114p107 Ns114p689 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 67626632) (BSN.sinOddQ 67108864) 0 2 Ns114p690 Ns114p110 Ns114p689 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p692 := Ns114p644 41110 BSN.abs_quadSignPos (BSN.cos_quad_nat0 28 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 47528975 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 21 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 56748229 67108864) qz90 rfl rfl (Ns114p677 RS115to132.d9 RS115to132.d11 RS115to132.d13 RS115to132.d17 (Ns114p681 rfl rfl) (Ns114p683 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns114p676 rfl) RS115to132.d19 RS115to132.d21 RS115to132.d23 RS115to132.d25 RS115to132.d17 (Ns114p687 rfl rfl) (Ns114p691 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns114p693 := nat_lit 580203278366985285182156693693245035959872440350791218200890638336 

noncomputable def Ns114p694 := nat_lit 289646958973166858897800062178720036306494023949360378643808256 

noncomputable def Ns114p695 := nat_lit 1740030541183009521828674480955377667807004333004474933845384298496 

noncomputable def Ns114p696 := BSN.cos_dyadic_bound_f 64229364 67108864 3 2 67108864 33554432 Ns114p693 Ns114p113 Ns114p694 Ns114p695 Ns114p116 Ns114p694 38647973 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 64229364) qz360 0 2 Ns114p693 Ns114p113 Ns114p694 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 64229364) (BSN.cosOddQ 67108864) 0 2 Ns114p695 Ns114p116 Ns114p694 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p697 := nat_lit 460173839198981400256798466721 

noncomputable def Ns114p698 := BSN.sin_dyadic_bound_f 26045367 67108864 2 1 67108864 33554432 Ns114p697 Ns114p231 Ns114p697 Ns114p697 Ns114p232 Ns114p697 25396420 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 26045367) qz359 0 1 Ns114p697 Ns114p231 Ns114p697 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 26045367) (BSN.sinOddQ 67108864) 0 1 Ns114p697 Ns114p232 Ns114p697 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p699 := Ns114p642 55419 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 62 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 38647973 67108864) BSN.abs_quadSignNeg qz637 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 25396420 67108864) qz90 rfl rfl (Ns114p692 rfl rfl) (Ns114p676 rfl) RS115to132.d27 RS115to132.d29 RS115to132.d31 RS115to132.d33 RS115to132.d17 (Ns114p696 rfl rfl) (Ns114p698 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns114p700 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 7) 75438258 67108864 55419 67108864 75438258 67108864 55419 67108864 10125151593037824 37719129 16777216 55419 33554432 (Ns114p699 rfl) 

noncomputable def Ns114p701 := @Enclosure.Real.IsNear.mulLit_tf qz689 (Zeta.RiemannSiegel.correction qz89) 1532053 4194304 1 4194304 13466014207505 35184372088832 9038649927707 197912092999680000 20630647464650657765 147573952589676412928 

noncomputable abbrev qz692 := (@HPow.hPow Real Real Real qz7 qz88 qz9)

noncomputable def Ns114p702 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz692 1 1 0 1 1532053 4194304 1 4194304 1532053 4194304 1 4194304 

noncomputable def Ns114p703 := @Enclosure.Real.IsNear.sqrt_image qz88 471231678351 8388608000 352959 8388608000 31436343 31436368 4194304 (@Enclosure.Real.IsNear.of_eq qz88 (@HMul.hMul Real Real Real qz5 qz87 qz3) Bool.false 471231678351 8388608000 352959 8388608000 (BSN.t_div_two_pi_mk qz87 352959 1000 qz90) (@Enclosure.Real.IsNear.mulLit_ff qz87 qz3 352959 1000 0 1 1335089 8388608 1 8388608 471231678351 8388608000 352959 8388608000 (Enclosure.Real.IsNear.const Bool.false 352959 1000) RS115to132.d36 rfl)) 

noncomputable abbrev qz909 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 352959 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz693 := qz909

noncomputable abbrev qz439 := qz693

noncomputable abbrev qz92 := qz439

noncomputable def Ns114p704 := @Enclosure.Real.IsNear.sqrt_image qz92 62872711 8388608 25 8388608 11482751 11482756 4194304 (@Enclosure.Real.IsNear.recentre' qz92 Bool.false 62872711 8388608 25 8388608 62872711 8388608 25 8388608 (Ns114p703 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns114p705 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz92) 22965507 8388608 5 8388608 1532052 1532054 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz92) Bool.false 22965507 8388608 5 8388608 22965507 8388608 5 8388608 (Ns114p704 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns114p706 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz92)) Bool.false 3064106 8388608 2 8388608 1532053 4194304 1 4194304 (Ns114p705 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz93 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz432))

noncomputable abbrev qz694 := (@HMul.hMul Real Real Real qz884 qz908 qz908)

noncomputable abbrev qz440 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz694 qz688) qz642)

noncomputable abbrev qz94 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz440))

noncomputable def Ns114p707 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz89) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz93) qz94) Bool.false 13466014207505 

noncomputable def Ns114p708 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz93) qz94 8392733 8388608 165 

noncomputable abbrev qz695 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz93))

noncomputable def Ns114p709 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz93) (@Neg.neg Real Real.instNeg qz695) Bool.true 8392733 8388608 165 8388608 (BSN.inv_eq_neg_inv_neg qz93) 

noncomputable def Ns114p710 := @Enclosure.Real.IsNear.recentre' qz695 Bool.false 8392733 8388608 165 8388608 8392733 8388608 

noncomputable def Ns114p711 := @Enclosure.Real.IsNear.recentre' qz93 Bool.true 8384486 8388608 117954304 6039797760000 4192243 4194304 460759 23592960000 

noncomputable abbrev qz95 := (@HMul.hMul Real Real Real qz339 qz337 qz432)

noncomputable def Ns114p712 := @Enclosure.Real.IsNear.cos_image qz95 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6522661) qz383) Bool.false 6522661 2097152 79 4194304 Bool.true 8384486 8388608 1 

noncomputable def Ns114p713 := nat_lit 134930377052354090645089507 

noncomputable def Ns114p714 := nat_lit 7205759403792793600000000000000 

noncomputable def Ns114p715 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz89 884279719003555 140737488355328 1 500000000000000 4152455 8388608 25 8388608 3671931740574906977525 1180591620717411303424 Ns114p713 

noncomputable def Ns114p716 := @Enclosure.Real.IsNear.subLit_ff_p qz92 qz1 62872711 8388608 25 8388608 7 1 0 1 4152455 4152455 8388608 25 

noncomputable def Ns114p717 := @Ns114p716 8388608 (@Enclosure.Real.IsNear.recentre' qz92 Bool.false 62872711 8388608 25 8388608 62872711 8388608 25 8388608 (Ns114p703 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns114p718 := @Enclosure.Real.IsNear.recentre' qz95 Bool.false 3671931740574906977525 1180591620717411303424 Ns114p713 Ns114p714 6522661 2097152 79 4194304 (@Ns114p715 Ns114p714 RS115to132.d35 (Ns114p717 rfl rfl) rfl) 

noncomputable def Ns114p719 := nat_lit 129124822440959653159186226340569947441863430004606951396321450085175705690501068570880 

noncomputable def Ns114p720 := nat_lit 239378614253599174723787313144200341017603529602952418181867246745801729940097024256 

noncomputable def Ns114p721 := nat_lit 337796493398483740562601603813544966557518577630803902122833155633109835912361689170176 

noncomputable def Ns114p722 := BSN.sin_dyadic_bound_f 26447563502 17179869184 3 2 8388608 2882813 Ns114p719 Ns114p98 Ns114p720 Ns114p721 Ns114p101 Ns114p720 8384486 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26447563502) qz355 0 2 Ns114p719 Ns114p98 Ns114p720 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26447563502) qz356 0 2 Ns114p721 Ns114p101 Ns114p720 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p723 := @Ns114p712 1440000 (Ns114p718 rfl) (Enclosure.sfrac_false_div 6522661 2097152) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6522661) qz383) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 465270457565507833823232) qz384) 226375608064910080 72057594037927936 Bool.false 8384486 8388608 0 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q1 6522661 2097152 226375608064910080 72057594037927936 0 465270457565507833823232 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8384486 8388608 465270457565507833823232 302231454903657293676544 26447563502 17179869184 2882813 2880000 (Ns114p722 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p724 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz93) 4192243 4194304 460759 23592960000 4196284 4196449 4194304 (@Enclosure.Real.IsNear.neg qz93 Bool.true 4192243 4194304 460759 23592960000 (Ns114p711 (Ns114p723 rfl rfl) rfl)) 

noncomputable def Ns114p725 := Ns114p709 (@Enclosure.Real.IsNear.neg qz695 Bool.false 8392733 8388608 165 8388608 (@Ns114p710 165 8388608 (Ns114p724 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p726 := @Enclosure.Real.IsNear.recentre' qz94 Bool.true 1604485 4194304 

noncomputable abbrev qz96 := (@HMul.hMul Real Real Real qz339 qz337 qz440)

noncomputable def Ns114p727 := @Enclosure.Real.IsNear.cos_image qz96 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16469681)) qz357) Bool.true 16469681 8388608 

noncomputable def Ns114p728 := nat_lit 19443967991635224472686436045 

noncomputable def Ns114p729 := nat_lit 11262330256241863657924479858845673 

noncomputable def Ns114p730 := @Enclosure.Real.IsNear.recentre' qz96 Bool.true Ns114p728 Ns114p517 Ns114p729 

noncomputable abbrev qz97 := qz440

noncomputable def Ns114p731 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz97 884279719003555 140737488355328 1 500000000000000 21988481216719 

noncomputable abbrev qz441 := (@HSub.hSub Real Real Real qz634 qz694 qz688)

noncomputable abbrev qz98 := qz441

noncomputable def Ns114p732 := @Enclosure.Real.IsNear.subLit_tf qz98 qz26 17590434705615 70368744177664 417338575 70368744177664 1 16 

noncomputable abbrev qz442 := qz694

noncomputable abbrev qz99 := qz442

noncomputable def Ns114p733 := @Enclosure.Real.IsNear.subLit_ff_n qz99 qz89 17242882527025 70368744177664 207623375 70368744177664 4152455 8388608 25 8388608 

noncomputable def Ns114p734 := @Enclosure.Real.IsNear.mulLit_ff qz89 qz89 4152455 8388608 25 8388608 4152455 8388608 25 8388608 17242882527025 70368744177664 

noncomputable def Ns114p735 := nat_lit 36325755422069176878117643284458518662161518771571809499821196303417940755631501895302488641 

noncomputable def Ns114p736 := nat_lit 398310953130173985590698917401803599021828342462327927313005309693515349096222635434561 

noncomputable def Ns114p737 := nat_lit 219086229813475907766356170752367447276594141543409975270200735996683512035286468184007877185 

noncomputable def Ns114p738 := BSN.cos_dyadic_bound_t 16469681 8388608 4 3 4194304 1440000 Ns114p735 Ns114p631 Ns114p736 Ns114p737 Ns114p634 Ns114p736 1604485 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16469681) (BSN.cosEvenQ 8388608) 0 3 Ns114p735 Ns114p631 Ns114p736 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16469681) (BSN.cosOddQ 8388608) 0 3 Ns114p737 Ns114p634 Ns114p736 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p739 := @Ns114p726 230274304 6039797760000 1604485 4194304 899509 23592960000 (@Ns114p727 157 4194304 Bool.true 1604485 4194304 1 1440000 (@Ns114p730 Ns114p520 16469681 8388608 157 4194304 (@Ns114p731 70368744177664 417338575 70368744177664 Ns114p728 Ns114p517 Ns114p729 Ns114p520 RS115to132.d35 (@Ns114p732 0 1 351815699467504 21988481216719 70368744177664 417338575 70368744177664 (@Ns114p733 147559261294999633920 17590434705615 70368744177664 417338575 70368744177664 (@Ns114p734 207623375 70368744177664 (Ns114p717 rfl rfl) (Ns114p717 rfl rfl) rfl) (Ns114p717 rfl rfl) rfl rfl) qz370 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16469681 8388608) (BSN.cos_neg_of_bound 16469681 8388608 Bool.true 1604485 4194304 1 1440000 (Ns114p738 rfl rfl)) rfl rfl) 

noncomputable def Ns114p740 := @Ns114p701 13923446106260435803 830103483316929822720000 (Ns114p702 qz28 (@Enclosure.Real.IsNear.of_eq qz692 (@Inv.inv Real Real.instInv (Real.sqrt qz92)) Bool.false 1532053 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz88 (BSN.t_div_two_pi_nonneg qz87 352959 1000 qz90)) Ns114p706) rfl) (@Ns114p707 35184372088832 9038649927707 197912092999680000 (BSN.correction_mk qz89 (BSN.cos_two_pi_p_ne_zero_mk qz87 352959 1000 7 qz90 rfl rfl (@BSN.floor_sqrt_eq_dec qz87 352959 1000 7 qz90 rfl rfl rfl))) (@Ns114p708 8388608 1604485 4194304 899509 23592960000 13466014207505 35184372088832 9038649927707 197912092999680000 Ns114p725 (Ns114p739 rfl) rfl)) 

noncomputable def Ns114p741 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz87) (hardyZApproximantRS₀ qz87) Bool.false 352411614865314074597 147573952589676412928 1384934731349918675803 830103483316929822720000 (@Eq.refl Real (hardyZApproximantRS₀ qz87)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz87) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz87) qz87 7) (@HMul.hMul Real Real Real qz5 qz689 (Zeta.RiemannSiegel.correction qz89))) Bool.false 352411614865314074597 147573952589676412928 1384934731349918675803 830103483316929822720000 (BSN.hardyZApproximantRS₀_eq qz87 7 (@BSN.floor_sqrt_eq_dec qz87 352959 1000 7 qz90 rfl rfl rfl)) (@Ns114p640 352411614865314074597 147573952589676412928 1384934731349918675803 830103483316929822720000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz87) qz87 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 7)) Bool.false 37719129 16777216 55419 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz87) qz87 7) (Ns114p700 (Ns114p699 rfl) rfl rfl)) (Ns114p740 rfl) rfl rfl)) 

theorem RS115to132.d44 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz87) Bool.false 352411614865314074597 147573952589676412928 1384934731349918675803 830103483316929822720000 := Ns114p741 

noncomputable def Ns114p742 := nat_lit 13623126749480049665332215808 

noncomputable abbrev qz910 := (Enclosure.sfrac Bool.false 354518 1000)

noncomputable abbrev qz696 := qz910

noncomputable abbrev qz443 := qz696

noncomputable abbrev qz100 := qz443

noncomputable abbrev qz911 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 354518 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz697 := qz911

noncomputable abbrev qz444 := qz697

noncomputable abbrev qz101 := qz444

noncomputable abbrev qz912 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 354518 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz698 := qz912

noncomputable abbrev qz445 := qz698

noncomputable abbrev qz102 := qz445

noncomputable abbrev qz699 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz101 qz9))

noncomputable def Ns114p743 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz100) qz100 7) (@HMul.hMul Real Real Real qz5 qz699 (Zeta.RiemannSiegel.correction qz102)) 189315817 33554432 55657 33554432 10309068910386510915 73786976294838206464 14110267603788229507 830103483316929822720000 Ns114p742 

noncomputable def Ns114p744 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz100) qz100 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 354518 1000 62 97 67108864 33554432 1125899906842624 Bool.false 36051754146 1238 

noncomputable def Ns114p745 := Ns114p744 120242927 48 27397080 8 130587807 48 25364760 8 Bool.true 159830408 41285 Bool.true 40837710 Bool.true 18781380 3537118876014220 1 Bool.false 55062128 Bool.true Bool.false 18537166 Bool.true Bool.true 189315817 

noncomputable def Ns114p746 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz100) qz100 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 354518 1000 29 21 67108864 33554432 1125899906842624 Bool.false 36051754146 1238 

noncomputable def Ns114p747 := Ns114p746 93032624 47 33554424 8 108007536 47 30011992 8 Bool.true 142381824 24309 Bool.false 12997995 Bool.true 25160003 3537118876014220 1 Bool.false 12916879 Bool.true Bool.false 24574716 Bool.true Bool.true 159830408 

noncomputable def Ns114p748 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz100) qz100 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 354518 1000 185 94 67108864 33554432 1125899906842624 Bool.false 36051754146 1238 

noncomputable def Ns114p749 := Ns114p748 46516304 47 47453136 16 73726608 47 38745320 8 Bool.true 67108840 1287 Bool.false 59231027 Bool.false 5394966 3537118876014220 1 Bool.false 51834880 Bool.true Bool.false 66892126 Bool.true Bool.true 142381824 

noncomputable def Ns114p750 := nat_lit 675462368561906910900818522803418194128668370928331231 

noncomputable def Ns114p751 := nat_lit 1257345538451179329114487841343836845839822618624000 

noncomputable def Ns114p752 := nat_lit 2688034749521257161893815792640000 

noncomputable def Ns114p753 := nat_lit 5717745527595886092578838730986885120 

noncomputable abbrev qz446 := (@Eq.refl Real qz696)

noncomputable abbrev qz103 := qz446

noncomputable def Ns114p754 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz100 354518 1000 502733049296 16000000 709036 4000 2000 Ns114p752 Ns114p753 qz103 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns114p755 := nat_lit 13833469308147853535248763347014004615755128236612223610880 

noncomputable abbrev qz700 := (Real.log (Enclosure.sfrac Bool.false 502733049296 16000000))

noncomputable abbrev qz104 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 354518 4000) qz700) (@HMul.hMul Real Real Real qz339 qz343 (@HSub.hSub Real Real Real qz342 qz344 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz345 (@Nat.cast Real Real.instNatCast 709036))))))

noncomputable abbrev qz701 := (Enclosure.sfrac Bool.false 354518 2000)

noncomputable abbrev qz447 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz104 qz701) (@HMul.hMul Real Real Real qz5 qz701 (Real.log Real.pi)))

noncomputable def Ns114p756 := @Enclosure.Real.IsNear.addLit_ft_p qz447 (Enclosure.sfrac Bool.true Ns114p752 Ns114p753) 2419394383190860458299 4503599627370496000 84937444145976679 4608000000000000000000 Ns114p752 Ns114p753 0 1 Ns114p755 

noncomputable def Ns114p757 := nat_lit 81181404311959670269482631168000 

noncomputable abbrev qz448 := (@HSub.hSub Real Real Real qz12 qz104 qz701)

noncomputable abbrev qz449 := (@HMul.hMul Real Real Real qz5 qz701 (Real.log Real.pi))

noncomputable def Ns114p758 := @Enclosure.Real.IsNear.subLit_ff_p qz448 qz449 3333236330878821165371 4503599627370496000 35402154021721 4500000000000000000 6808653084099 33554432000 177259 16777216000 Ns114p757 2419394383190860458299 4503599627370496000 

noncomputable def Ns114p759 := nat_lit 1333294532351528466148400 

noncomputable abbrev qz450 := qz701

noncomputable def Ns114p760 := @Enclosure.Real.IsNear.subLit_ff_p qz104 qz450 826307979445377583167 900719925474099200 35402154021721 4500000000000000000 354518 2000 0 1 Ns114p759 3333236330878821165371 4503599627370496000 35402154021721 4500000000000000000 

noncomputable def Ns114p761 := nat_lit 1860680154161734975788828645881020416 

noncomputable def Ns114p762 := nat_lit 12518699915184319003361280 

noncomputable def Ns114p763 := nat_lit 47549058501501531173430274716380087328614273875349843524858682297755686434376613315741354142095014385418857027250499037649131696204111538216748979200382169987169646962278400 

noncomputable def Ns114p764 := nat_lit 1668376525865574649494721043171753433446173297317492139536993465488222326035396279782049712363321595533751086527461289447194806585575534967196710526904186187183689868247040 

noncomputable def Ns114p765 := nat_lit 294191303222349711296010037393709984772458366421735386943712958359219664166702769848602081880114139461418769035519953963564989604169210753363309700486946007610818560 

noncomputable def Ns114p766 := BSN.log_dyadic_bound 240589049296 764877049296 8 7 Ns114p763 33554432 11520000 Ns114p764 Ns114p765 21849483 1005466098592 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 240589049296) (BSN.artanhQ 764877049296) 0 7 Ns114p764 Ns114p763 Ns114p765 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns114p767 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 354518 4000) qz700 354518 4000 0 1 23317895671696065 2251799813685248 390625063 4500000000000000 826661373773834557167 900719925474099200 69241808042317 9000000000000000000 (Enclosure.Real.IsNear.const Bool.false 354518 4000) (BSN.isNear_log_sfrac 502733049296 16000000 23317895671696065 2251799813685248 390625063 4500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 502733049296) qz350)) Bool.false Ns114p762 Ns114p85 1000000161280000 11520000000000000000000 23317895671696065 2251799813685248 390625063 4500000000000000 (BSN.log_rat_reduce_isNear 502733049296 16000000 14 1005466098592 524288000000 21849483 33554432 24973259072661432 36028797018963968 11520000 1000000000000000 rfl rfl rfl rfl (Ns114p766 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p768 := BSN.arctan_dyadic_bound_f 1000 709036 1 0 4194304 1440000 0 1 1 0 1 1 5915 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 709036) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 709036) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz451 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 709036)))

noncomputable def Ns114p769 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz451 884279719003555 562949953421312 1 2000000000000000 5915 4194304 1 1440000 3705608113560999690240 883485821142435 562949953421312 12500000009 18000000000000000 qz16 (Ns114p768 rfl) rfl rfl 

noncomputable def Ns114p770 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 354518 4000) qz700) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz451)) 826661373773834557167 900719925474099200 69241808042317 9000000000000000000 883485821142435 2251799813685248 12500000009 72000000000000000 Ns114p761 826307979445377583167 900719925474099200 35402154021721 4500000000000000000 (Ns114p767 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz451) 1 4 0 1 883485821142435 562949953421312 12500000009 18000000000000000 883485821142435 2251799813685248 12500000009 72000000000000000 qz353 Ns114p769 rfl) 

noncomputable def Ns114p771 := @Ns114p756 Ns114p750 Ns114p751 84937444145976679 4608000000000000000000 (@Ns114p758 84937444145976679 4608000000000000000000 (Ns114p760 (Ns114p770 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 354518 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz450 (Real.log Real.pi) 354518 2000 0 1 38410761 33554432 1 16777216 6808653084099 33554432000 177259 16777216000 (Enclosure.Real.IsNear.const Bool.false 354518 2000) RS115to132.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns114p752 Ns114p753) 

noncomputable def Ns114p772 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz100) Bool.false Ns114p750 Ns114p751 84937444145976679 4608000000000000000000 1126617317 2097152 155 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz100) (@HAdd.hAdd Real Real Real qz354 qz447 (Enclosure.sfrac Bool.true Ns114p752 Ns114p753)) Bool.false Ns114p750 Ns114p751 84937444145976679 4608000000000000000000 Ns114p754 (Ns114p771 rfl rfl)) 

noncomputable def Ns114p773 := nat_lit 140223381103340403286776035899627557551656046735209576524584349723525319607231449506145 

noncomputable def Ns114p774 := nat_lit 282207550349387585736687867355541418375797350355954586285397936247859832387606520161 

noncomputable def Ns114p775 := nat_lit 366794804951040142993220694618544155100776450501163059662782652617212635433169100054881 

noncomputable def Ns114p776 := BSN.sin_dyadic_bound_f 26997346379 17179869184 3 2 8388608 2882813 Ns114p773 Ns114p98 Ns114p774 Ns114p775 Ns114p101 Ns114p774 8388605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26997346379) qz355 0 2 Ns114p773 Ns114p98 Ns114p774 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26997346379) qz356 0 2 Ns114p775 Ns114p101 Ns114p774 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p777 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz100) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1126617317) qz383) Bool.false 1126617317 2097152 155 8388608 Bool.true 8388605 8388608 1 1440000 (Ns114p772 rfl) (Enclosure.sfrac_false_div 1126617317 2097152) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1126617317) qz383) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474942340222209295908864) qz384) 226375608064910080 72057594037927936 Bool.false 8388605 8388608 85 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q1 1126617317 2097152 226375608064910080 72057594037927936 85 474942340222209295908864 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388605 8388608 474942340222209295908864 302231454903657293676544 26997346379 17179869184 2882813 2880000 (Ns114p776 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p778 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz100) Bool.false Ns114p750 Ns114p751 84937444145976679 4608000000000000000000 36051754146 67108864 1238 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz100) (@HAdd.hAdd Real Real Real qz354 qz447 (Enclosure.sfrac Bool.true Ns114p752 Ns114p753)) Bool.false Ns114p750 Ns114p751 84937444145976679 4608000000000000000000 Ns114p754 (Ns114p771 rfl rfl)) 

noncomputable def Ns114p779 := Ns114p749 24309 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 185 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 51834880 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 94 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66892126 67108864) qz103 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 1) Bool.true 8388605 8388608 904643 47185920000 67108840 67108864 1287 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz100)) Bool.true 8388605 8388608 904643 47185920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz100) qz100) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz100)) Bool.true 8388605 8388608 231588608 12079595520000 8388605 8388608 904643 47185920000 (Ns114p777 rfl rfl) rfl)) rfl) (Ns114p778 rfl) RS115to132.d7 

noncomputable def Ns114p780 := nat_lit 755067071752543151981304922364433397948929322387933813838578273825 

noncomputable def Ns114p781 := nat_lit 151493536196508797056683448237772659482934489223371913776680481 

noncomputable def Ns114p782 := nat_lit 1977311341245675812374849690133512029369937759938226910288257044001 

noncomputable def Ns114p783 := BSN.sin_dyadic_bound_f 59231027 67108864 3 2 67108864 33554432 Ns114p780 Ns114p107 Ns114p781 Ns114p782 Ns114p110 Ns114p781 51834880 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 59231027) qz359 0 2 Ns114p780 Ns114p107 Ns114p781 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 59231027) (BSN.sinOddQ 67108864) 0 2 Ns114p782 Ns114p110 Ns114p781 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p784 := nat_lit 847139335829840541221016336 

noncomputable def Ns114p785 := BSN.cos_dyadic_bound_f 5394966 67108864 2 1 67108864 33554432 Ns114p784 Ns114p227 Ns114p784 Ns114p784 Ns114p228 Ns114p784 66892126 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 5394966) qz360 0 1 Ns114p784 Ns114p227 Ns114p784 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 5394966) (BSN.cosOddQ 67108864) 0 1 Ns114p784 Ns114p228 Ns114p784 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p786 := nat_lit 28543384135886238354101000625 

noncomputable def Ns114p787 := BSN.sin_dyadic_bound_f 12997995 67108864 2 1 67108864 33554432 Ns114p786 Ns114p231 Ns114p786 Ns114p786 Ns114p232 Ns114p786 12916879 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 12997995) qz359 0 1 Ns114p786 Ns114p231 Ns114p786 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 12997995) (BSN.sinOddQ 67108864) 0 1 Ns114p786 Ns114p232 Ns114p786 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p788 := nat_lit 400721601378483335385117280081 

noncomputable def Ns114p789 := BSN.sin_dyadic_bound_f 25160003 67108864 2 1 67108864 33554432 Ns114p788 Ns114p231 Ns114p788 Ns114p788 Ns114p232 Ns114p788 24574716 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 25160003) qz359 0 1 Ns114p788 Ns114p231 Ns114p788 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 25160003) (BSN.sinOddQ 67108864) 0 1 Ns114p788 Ns114p232 Ns114p788 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p790 := Ns114p747 41285 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 29 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 12916879 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 21 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 24574716 67108864) qz103 rfl rfl (Ns114p779 RS115to132.d9 RS115to132.d11 RS115to132.d13 RS115to132.d17 (Ns114p783 rfl rfl) (Ns114p785 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns114p778 rfl) RS115to132.d19 RS115to132.d21 RS115to132.d23 RS115to132.d25 RS115to132.d17 (Ns114p787 rfl rfl) (Ns114p789 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns114p791 := nat_lit 94778493460827479387880836449819470504840703922688544649392800000 

noncomputable def Ns114p792 := nat_lit 7735547301686854824065199993917475510877966316357936100000000 

noncomputable def Ns114p793 := nat_lit 284320009287879064453994378949470576563500355835432918075978400000 

noncomputable def Ns114p794 := BSN.cos_dyadic_bound_f 40837710 67108864 3 2 67108864 33554432 Ns114p791 Ns114p113 Ns114p792 Ns114p793 Ns114p116 Ns114p792 55062128 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 40837710) qz360 0 2 Ns114p791 Ns114p113 Ns114p792 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 40837710) (BSN.cosOddQ 67108864) 0 2 Ns114p793 Ns114p116 Ns114p792 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p795 := nat_lit 124425673179315198155379360000 

noncomputable def Ns114p796 := BSN.sin_dyadic_bound_f 18781380 67108864 2 1 67108864 33554432 Ns114p795 Ns114p231 Ns114p795 Ns114p795 Ns114p232 Ns114p795 18537166 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 18781380) qz359 0 1 Ns114p795 Ns114p231 Ns114p795 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 18781380) (BSN.sinOddQ 67108864) 0 1 Ns114p795 Ns114p232 Ns114p795 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p797 := Ns114p745 55657 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 62 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 55062128 67108864) BSN.abs_quadSignNeg qz637 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 18537166 67108864) qz103 rfl rfl (Ns114p790 rfl rfl) (Ns114p778 rfl) RS115to132.d27 RS115to132.d29 RS115to132.d31 RS115to132.d33 RS115to132.d17 (Ns114p794 rfl rfl) (Ns114p796 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns114p798 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 7) 189315817 67108864 55657 67108864 189315817 67108864 55657 67108864 25409538832203776 189315817 33554432 55657 33554432 (Ns114p797 rfl) 

noncomputable def Ns114p799 := @Enclosure.Real.IsNear.mulLit_tf qz699 (Zeta.RiemannSiegel.correction qz102) 765183 2097152 1 4194304 13472684195005 35184372088832 4585332719273 98956046499840000 10309068910386510915 73786976294838206464 

noncomputable abbrev qz702 := (@HPow.hPow Real Real Real qz7 qz101 qz9)

noncomputable def Ns114p800 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz702 1 1 0 1 765183 2097152 1 4194304 765183 2097152 1 4194304 

noncomputable def Ns114p801 := @Enclosure.Real.IsNear.sqrt_image qz101 236656541051 4194304000 177259 4194304000 31505693 31505718 4194304 (@Enclosure.Real.IsNear.of_eq qz101 (@HMul.hMul Real Real Real qz5 qz100 qz3) Bool.false 236656541051 4194304000 177259 4194304000 (BSN.t_div_two_pi_mk qz100 354518 1000 qz103) (@Enclosure.Real.IsNear.mulLit_ff qz100 qz3 354518 1000 0 1 1335089 8388608 1 8388608 236656541051 4194304000 177259 4194304000 (Enclosure.Real.IsNear.const Bool.false 354518 1000) RS115to132.d36 rfl)) 

noncomputable abbrev qz913 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 354518 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz703 := qz913

noncomputable abbrev qz452 := qz703

noncomputable abbrev qz105 := qz452

noncomputable def Ns114p802 := @Enclosure.Real.IsNear.sqrt_image qz105 63011411 8388608 25 8388608 11495410 11495415 4194304 (@Enclosure.Real.IsNear.recentre' qz105 Bool.false 63011411 8388608 25 8388608 63011411 8388608 25 8388608 (Ns114p801 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns114p803 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz105) 22990825 8388608 5 8388608 1530365 1530367 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz105) Bool.false 22990825 8388608 5 8388608 22990825 8388608 5 8388608 (Ns114p802 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns114p804 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz105)) Bool.false 3060732 8388608 2 8388608 765183 2097152 1 4194304 (Ns114p803 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz106 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz445))

noncomputable abbrev qz704 := (@HMul.hMul Real Real Real qz884 qz912 qz912)

noncomputable abbrev qz453 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz704 qz698) qz642)

noncomputable abbrev qz107 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz453))

noncomputable def Ns114p805 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz102) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz106) qz107) Bool.false 13472684195005 

noncomputable def Ns114p806 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz106) qz107 8410729 8388608 165 

noncomputable abbrev qz705 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz106))

noncomputable def Ns114p807 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz106) (@Neg.neg Real Real.instNeg qz705) Bool.true 8410729 8388608 165 8388608 (BSN.inv_eq_neg_inv_neg qz106) 

noncomputable def Ns114p808 := @Enclosure.Real.IsNear.recentre' qz705 Bool.false 8410729 8388608 165 8388608 8410729 8388608 

noncomputable def Ns114p809 := @Enclosure.Real.IsNear.recentre' qz106 Bool.true 8366545 8388608 117954304 6039797760000 8366545 8388608 460759 23592960000 

noncomputable abbrev qz108 := (@HMul.hMul Real Real Real qz339 qz337 qz445)

noncomputable def Ns114p810 := @Enclosure.Real.IsNear.cos_image qz108 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13481061) qz366) Bool.false 13481061 4194304 79 4194304 Bool.true 8366545 8388608 1 

noncomputable def Ns114p811 := nat_lit 134930377052592375430671587 

noncomputable def Ns114p812 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz102 884279719003555 140737488355328 1 500000000000000 4291155 8388608 25 8388608 3794581337600700056025 1180591620717411303424 Ns114p811 

noncomputable def Ns114p813 := @Enclosure.Real.IsNear.subLit_ff_p qz105 qz1 63011411 8388608 25 8388608 7 1 0 1 4291155 4291155 8388608 25 

noncomputable def Ns114p814 := @Ns114p813 8388608 (@Enclosure.Real.IsNear.recentre' qz105 Bool.false 63011411 8388608 25 8388608 63011411 8388608 25 8388608 (Ns114p801 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns114p815 := @Enclosure.Real.IsNear.recentre' qz108 Bool.false 3794581337600700056025 1180591620717411303424 Ns114p811 Ns114p714 13481061 4194304 79 4194304 (@Ns114p812 Ns114p714 RS115to132.d35 (Ns114p814 rfl rfl) rfl) 

noncomputable def Ns114p816 := nat_lit 2412434799729379674379914394022174161 

noncomputable def Ns114p817 := nat_lit 2090694862362245919518973588060783891185664 

noncomputable def Ns114p818 := nat_lit 31360422935433688792784603820911758367784960 

noncomputable abbrev qz454 := (BSN.cosEvenQ 17179869184)

noncomputable abbrev qz455 := (BSN.cosOddQ 17179869184)

noncomputable def Ns114p819 := BSN.cos_dyadic_bound_f 1246275037 17179869184 2 1 8388608 2882813 Ns114p816 Ns114p817 Ns114p816 Ns114p816 Ns114p818 Ns114p816 8366545 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1246275037) qz454 0 1 Ns114p816 Ns114p817 Ns114p816 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1246275037) qz455 0 1 Ns114p816 Ns114p818 Ns114p816 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p820 := @Ns114p810 1440000 (Ns114p815 rfl) (Enclosure.sfrac_false_div 13481061 4194304) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13481061) qz366) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 43849404658916421271552) qz380) 226375608064910080 72057594037927936 Bool.false 8366545 8388608 0 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q2 13481061 4194304 226375608064910080 72057594037927936 0 43849404658916421271552 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 8366545 8388608 43849404658916421271552 604462909807314587353088 1246275037 17179869184 2882813 2880000 (Ns114p819 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p821 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz106) 8366545 8388608 460759 23592960000 4205282 4205447 4194304 (@Enclosure.Real.IsNear.neg qz106 Bool.true 8366545 8388608 460759 23592960000 (Ns114p809 (Ns114p820 rfl rfl) rfl)) 

noncomputable def Ns114p822 := Ns114p807 (@Enclosure.Real.IsNear.neg qz705 Bool.false 8410729 8388608 165 8388608 (@Ns114p808 165 8388608 (Ns114p821 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p823 := @Enclosure.Real.IsNear.recentre' qz107 Bool.true 1601845 4194304 

noncomputable abbrev qz109 := (@HMul.hMul Real Real Real qz339 qz337 qz453)

noncomputable def Ns114p824 := @Enclosure.Real.IsNear.cos_image qz109 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16463967)) qz357) Bool.true 16463967 8388608 

noncomputable def Ns114p825 := nat_lit 19437222018499611801782779045 

noncomputable def Ns114p826 := nat_lit 11449478689203518582457193717169873 

noncomputable def Ns114p827 := @Enclosure.Real.IsNear.recentre' qz109 Bool.true Ns114p825 Ns114p517 Ns114p826 

noncomputable abbrev qz110 := qz453

noncomputable def Ns114p828 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz110 884279719003555 140737488355328 1 500000000000000 21980852439319 

noncomputable abbrev qz456 := (@HSub.hSub Real Real Real qz634 qz704 qz698)

noncomputable abbrev qz111 := qz456

noncomputable def Ns114p829 := @Enclosure.Real.IsNear.subLit_tf qz111 qz26 17582805928215 70368744177664 424273575 70368744177664 1 16 

noncomputable abbrev qz457 := qz704

noncomputable abbrev qz112 := qz457

noncomputable def Ns114p830 := @Enclosure.Real.IsNear.subLit_ff_n qz112 qz102 18414011234025 70368744177664 214558375 70368744177664 4291155 8388608 25 8388608 

noncomputable def Ns114p831 := @Enclosure.Real.IsNear.mulLit_ff qz102 qz102 4291155 8388608 25 8388608 4291155 8388608 25 8388608 18414011234025 70368744177664 

noncomputable def Ns114p832 := nat_lit 36274927932604907623753334287954193399395952233872259094292656531484270436630937147122951041 

noncomputable def Ns114p833 := nat_lit 396655831163384978777629966608270286164352596703841472260552707857663089321712835928961 

noncomputable def Ns114p834 := nat_lit 218781455305265952451701792932278159797989770533377892854532152290925669061621309334876889985 

noncomputable def Ns114p835 := BSN.cos_dyadic_bound_t 16463967 8388608 4 3 4194304 1440000 Ns114p832 Ns114p631 Ns114p833 Ns114p834 Ns114p634 Ns114p833 1601845 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16463967) (BSN.cosEvenQ 8388608) 0 3 Ns114p832 Ns114p631 Ns114p833 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16463967) (BSN.cosOddQ 8388608) 0 3 Ns114p834 Ns114p634 Ns114p833 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p836 := @Ns114p823 467748608 12079595520000 1601845 4194304 1827143 47185920000 (@Ns114p824 319 8388608 Bool.true 1601845 4194304 1 1440000 (@Ns114p827 Ns114p520 16463967 8388608 319 8388608 (@Ns114p828 70368744177664 424273575 70368744177664 Ns114p825 Ns114p517 Ns114p826 Ns114p520 RS115to132.d35 (@Ns114p829 0 1 351693639029104 21980852439319 70368744177664 424273575 70368744177664 (@Ns114p830 147495266471871774720 17582805928215 70368744177664 424273575 70368744177664 (@Ns114p831 214558375 70368744177664 (Ns114p814 rfl rfl) (Ns114p814 rfl rfl) rfl) (Ns114p814 rfl rfl) rfl rfl) qz370 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16463967 8388608) (BSN.cos_neg_of_bound 16463967 8388608 Bool.true 1601845 4194304 1 1440000 (Ns114p835 rfl rfl)) rfl rfl) 

noncomputable def Ns114p837 := @Ns114p799 14110267603788229507 830103483316929822720000 (Ns114p800 qz28 (@Enclosure.Real.IsNear.of_eq qz702 (@Inv.inv Real Real.instInv (Real.sqrt qz105)) Bool.false 765183 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz101 (BSN.t_div_two_pi_nonneg qz100 354518 1000 qz103)) Ns114p804) rfl) (@Ns114p805 35184372088832 4585332719273 98956046499840000 (BSN.correction_mk qz102 (BSN.cos_two_pi_p_ne_zero_mk qz100 354518 1000 7 qz103 rfl rfl (@BSN.floor_sqrt_eq_dec qz100 354518 1000 7 qz103 rfl rfl rfl))) (@Ns114p806 8388608 1601845 4194304 1827143 47185920000 13472684195005 35184372088832 4585332719273 98956046499840000 Ns114p822 (Ns114p836 rfl) rfl)) 

noncomputable def Ns114p838 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz100) (hardyZApproximantRS₀ qz100) Bool.true 406000815316440155069 73786976294838206464 1391009437614186949507 830103483316929822720000 (@Eq.refl Real (hardyZApproximantRS₀ qz100)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz100) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz100) qz100 7) (@HMul.hMul Real Real Real qz5 qz699 (Zeta.RiemannSiegel.correction qz102))) Bool.true 406000815316440155069 73786976294838206464 1391009437614186949507 830103483316929822720000 (BSN.hardyZApproximantRS₀_eq qz100 7 (@BSN.floor_sqrt_eq_dec qz100 354518 1000 7 qz103 rfl rfl rfl)) (@Ns114p743 406000815316440155069 73786976294838206464 1391009437614186949507 830103483316929822720000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz100) qz100 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 7)) Bool.true 189315817 33554432 55657 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz100) qz100 7) (Ns114p798 (Ns114p797 rfl) rfl rfl)) (Ns114p837 rfl) rfl rfl)) 

theorem RS115to132.d45 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz100) Bool.true 406000815316440155069 73786976294838206464 1391009437614186949507 830103483316929822720000 := Ns114p838 

noncomputable abbrev qz914 := (Enclosure.sfrac Bool.false 356075 1000)

noncomputable abbrev qz706 := qz914

noncomputable abbrev qz458 := qz706

noncomputable abbrev qz113 := qz458

noncomputable abbrev qz915 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 356075 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz707 := qz915

noncomputable abbrev qz459 := qz707

noncomputable abbrev qz114 := qz459

noncomputable abbrev qz916 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 356075 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz708 := qz916

noncomputable abbrev qz460 := qz708

noncomputable abbrev qz115 := qz460

noncomputable abbrev qz709 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz114 qz9))

noncomputable def Ns114p839 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz113) qz113 7) (@HMul.hMul Real Real Real qz5 qz709 (Zeta.RiemannSiegel.correction qz115)) 94917 2097152 27955 16777216 20172802120965945 144115188075855872 3619252291469697391 207525870829232455680000 55984413620183985291264 

noncomputable def Ns114p840 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz113) qz113 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 356075 1000 62 97 67108864 33554432 1125899906842624 Bool.false 36262563574 1243 

noncomputable def Ns114p841 := Ns114p840 120242927 48 27397080 8 130587807 48 25364760 8 Bool.false 32265782 41475 Bool.true 17246519 Bool.true 11297168 3537118876014220 1 Bool.false 64904915 Bool.true Bool.false 11243885 Bool.true Bool.false 1518672 

noncomputable def Ns114p842 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz113) qz113 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 356075 1000 29 20 67108864 33554432 1125899906842624 Bool.false 36262563574 1243 

noncomputable def Ns114p843 := Ns114p842 93032624 47 33554424 8 108007536 47 30011992 8 Bool.false 55515945 24425 Bool.false 78955628 Bool.true 87932665 3537118876014220 1 Bool.false 61960194 Bool.true Bool.false 17284646 Bool.false Bool.false 32265782 

noncomputable def Ns114p844 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz113) qz113 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 356075 1000 186 94 67108864 33554432 1125899906842624 Bool.false 36262563574 1243 

noncomputable def Ns114p845 := Ns114p844 46516304 47 47453136 16 73726608 47 38745320 8 Bool.false 67108848 1303 Bool.false 92200212 Bool.false 101412066 3537118876014220 1 Bool.false 13128920 Bool.true Bool.false 3999918 Bool.true Bool.false 55515945 

noncomputable def Ns114p846 := nat_lit 14627910740793350254561249477207730876698217779 

noncomputable def Ns114p847 := nat_lit 27070961778278203580994633378216582976634880 

noncomputable def Ns114p848 := nat_lit 2747583005821882893139062500000000 

noncomputable def Ns114p849 := nat_lit 5870079114256256543794581328125000000 

noncomputable abbrev qz461 := (@Eq.refl Real qz706)

noncomputable abbrev qz116 := qz461

noncomputable def Ns114p850 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz113 356075 1000 507158622500 16000000 712150 4000 2000 Ns114p848 Ns114p849 qz116 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns114p851 := nat_lit 1142805526624480488637597615406853974742048263984375000000 

noncomputable abbrev qz710 := (Real.log (Enclosure.sfrac Bool.false 507158622500 16000000))

noncomputable abbrev qz117 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 356075 4000) qz710) (@HMul.hMul Real Real Real qz339 qz343 (@HSub.hSub Real Real Real qz342 qz344 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz345 (@Nat.cast Real Real.instNatCast 712150))))))

noncomputable abbrev qz711 := (Enclosure.sfrac Bool.false 356075 2000)

noncomputable abbrev qz462 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz117 qz711) (@HMul.hMul Real Real Real qz5 qz711 (Real.log Real.pi)))

noncomputable def Ns114p852 := @Enclosure.Real.IsNear.addLit_ft_p qz462 (Enclosure.sfrac Bool.true Ns114p848 Ns114p849) 194683324415531158019 360287970189639680 6824557246577663 368640000000000000000 Ns114p848 Ns114p849 0 1 Ns114p851 

noncomputable def Ns114p853 := nat_lit 522599069650790398850383216640 

noncomputable abbrev qz463 := (@HSub.hSub Real Real Real qz12 qz117 qz711)

noncomputable abbrev qz464 := (@HMul.hMul Real Real Real qz5 qz711 (Real.log Real.pi))

noncomputable def Ns114p854 := @Enclosure.Real.IsNear.subLit_ff_p qz463 qz464 268111758858462824963 360287970189639680 5688672772399 720000000000000000 547084468923 2684354560 14243 1342177280 Ns114p853 194683324415531158019 360287970189639680 

noncomputable abbrev qz465 := qz711

noncomputable def Ns114p855 := @Enclosure.Real.IsNear.subLit_ff_p qz117 qz465 332256528351100799491 360287970189639680 5688672772399 720000000000000000 356075 2000 0 1 536223517716925649926000 268111758858462824963 360287970189639680 5688672772399 720000000000000000 

noncomputable def Ns114p856 := nat_lit 748175188636716100177519415832608768 

noncomputable def Ns114p857 := nat_lit 12529295552042032078782464 

noncomputable def Ns114p858 := nat_lit 51548981139405740273732892601185894465382336755536762299985937780122493499295185491909099504557509697519958530213658888711417093873023986816406250000000000000000000000000000 

noncomputable def Ns114p859 := nat_lit 1857390163019815217183249253274425351692661504105592431466384556145352180703104108114386704022876355417040841757579109059726819396018981933593750000000000000000000000000000 

noncomputable def Ns114p860 := nat_lit 379713379668053492464450832002425541507461589550140322295291570213445935656631230614878024009294791456314404602997427806258201599121093750000000000000000000000000000 

noncomputable def Ns114p861 := BSN.log_dyadic_bound 245014622500 769302622500 8 7 Ns114p858 33554432 11520000 Ns114p859 Ns114p860 22143571 1014317245000 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 245014622500) (BSN.artanhQ 769302622500) 0 7 Ns114p859 Ns114p858 Ns114p860 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns114p862 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 356075 4000) qz710 356075 4000 0 1 23337631583292097 2251799813685248 390625063 4500000000000000 332397886640829337571 360287970189639680 5563672772309 720000000000000000 (Enclosure.Real.IsNear.const Bool.false 356075 4000) (BSN.isNear_log_sfrac 507158622500 16000000 23337631583292097 2251799813685248 390625063 4500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 507158622500) qz350)) Bool.false Ns114p857 Ns114p85 1000000161280000 11520000000000000000000 23337631583292097 2251799813685248 390625063 4500000000000000 (BSN.log_rat_reduce_isNear 507158622500 16000000 14 1014317245000 524288000000 22143571 33554432 24973259072661432 36028797018963968 11520000 1000000000000000 rfl rfl rfl rfl (Ns114p861 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p863 := BSN.arctan_dyadic_bound_f 1000 712150 1 0 4194304 1440000 0 1 1 0 1 1 5889 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 712150) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 712150) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz466 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 712150)))

noncomputable def Ns114p864 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz466 884279719003555 562949953421312 1 2000000000000000 5889 4194304 1 1440000 3705622750259788644352 883489310803363 562949953421312 12500000009 18000000000000000 qz16 (Ns114p863 rfl) rfl rfl 

noncomputable def Ns114p865 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 356075 4000) qz710) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz466)) 332397886640829337571 360287970189639680 5563672772309 720000000000000000 883489310803363 2251799813685248 12500000009 72000000000000000 Ns114p856 332256528351100799491 360287970189639680 5688672772399 720000000000000000 (Ns114p862 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz466) 1 4 0 1 883489310803363 562949953421312 12500000009 18000000000000000 883489310803363 2251799813685248 12500000009 72000000000000000 qz353 Ns114p864 rfl) 

noncomputable def Ns114p866 := @Ns114p852 Ns114p846 Ns114p847 6824557246577663 368640000000000000000 (@Ns114p854 6824557246577663 368640000000000000000 (Ns114p855 (Ns114p865 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 356075 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz465 (Real.log Real.pi) 356075 2000 0 1 38410761 33554432 1 16777216 547084468923 2684354560 14243 1342177280 (Enclosure.Real.IsNear.const Bool.false 356075 2000) RS115to132.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns114p848 Ns114p849) 

noncomputable def Ns114p867 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz113) Bool.false Ns114p846 Ns114p847 6824557246577663 368640000000000000000 2266410223 4194304 157 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz113) (@HAdd.hAdd Real Real Real qz354 qz462 (Enclosure.sfrac Bool.true Ns114p848 Ns114p849)) Bool.false Ns114p846 Ns114p847 6824557246577663 368640000000000000000 Ns114p850 (Ns114p866 rfl rfl)) 

noncomputable def Ns114p868 := nat_lit 140120606006437278981389685639781515331417888038240700871280537760734348352584584130625 

noncomputable def Ns114p869 := nat_lit 281794850135794629561076706846863435890087105639173598791171874430752810509437890625 

noncomputable def Ns114p870 := nat_lit 366526300259496825074826481055009046971796232405309840264834749195702074468325297090625 

noncomputable def Ns114p871 := BSN.sin_dyadic_bound_f 26992408105 17179869184 3 2 8388608 2882813 Ns114p868 Ns114p98 Ns114p869 Ns114p870 Ns114p101 Ns114p869 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26992408105) qz355 0 2 Ns114p868 Ns114p98 Ns114p869 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26992408105) qz356 0 2 Ns114p870 Ns114p101 Ns114p869 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p872 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz113) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2266410223) qz366) Bool.false 2266410223 4194304 157 8388608 Bool.false 8388606 8388608 1 1440000 (Ns114p867 rfl) (Enclosure.sfrac_false_div 2266410223 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2266410223) qz366) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949710930371427168157696) qz380) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 85 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q3 2266410223 4194304 226375608064910080 72057594037927936 85 949710930371427168157696 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388606 8388608 949710930371427168157696 604462909807314587353088 26992408105 17179869184 2882813 2880000 (Ns114p871 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p873 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz113) Bool.false Ns114p846 Ns114p847 6824557246577663 368640000000000000000 36262563574 67108864 1243 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz113) (@HAdd.hAdd Real Real Real qz354 qz462 (Enclosure.sfrac Bool.true Ns114p848 Ns114p849)) Bool.false Ns114p846 Ns114p847 6824557246577663 368640000000000000000 Ns114p850 (Ns114p866 rfl rfl)) 

noncomputable def Ns114p874 := Ns114p845 24425 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 186 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 13128920 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 94 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 3999918 67108864) qz116 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 1) Bool.false 4194303 4194304 915893 47185920000 67108848 67108864 1303 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz113)) Bool.false 4194303 4194304 915893 47185920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz113) qz113) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz113)) Bool.false 8388606 8388608 234468608 12079595520000 4194303 4194304 915893 47185920000 (Ns114p872 rfl rfl) rfl)) rfl) (Ns114p873 rfl) RS115to132.d7 

noncomputable def Ns114p875 := nat_lit 594583494762287111920402292191874628641874099547572459900489182803982319304056044112405384892080193536 

noncomputable def Ns114p876 := nat_lit 377383611043930118774416674348867632678087999860144757953603540949365912580365535728552384659456 

noncomputable def Ns114p877 := nat_lit 3602048747914530177499547769580893386186835677121285539750157178027238775683026865382144434421136097280 

noncomputable def Ns114p878 := BSN.cos_dyadic_bound_f 92200212 67108864 4 3 67108864 33554432 Ns114p875 Ns114p371 Ns114p876 Ns114p877 Ns114p374 Ns114p876 13128920 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 92200212) qz360 0 3 Ns114p875 Ns114p371 Ns114p876 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 92200212) (BSN.cosOddQ 67108864) 0 3 Ns114p877 Ns114p374 Ns114p876 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p879 := nat_lit 871103821317580788807812060747750739738369410526729827787294659838395506366704941279271512696968974336 

noncomputable def Ns114p880 := nat_lit 1183247416100687613663551811434958406500752987300217765483584311083818980961241384448698814304256 

noncomputable def Ns114p881 := nat_lit 5273788377048539163842934657113710711573332789284707946824179951730378808332952806286046407912603258880 

noncomputable def Ns114p882 := BSN.cos_dyadic_bound_f 101412066 67108864 4 3 67108864 33554432 Ns114p879 Ns114p371 Ns114p880 Ns114p881 Ns114p374 Ns114p880 3999918 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 101412066) qz360 0 3 Ns114p879 Ns114p371 Ns114p880 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 101412066) (BSN.cosOddQ 67108864) 0 3 Ns114p881 Ns114p374 Ns114p880 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p883 := nat_lit 2385112104964510986784917610475195277284364076834619832869012439040 

noncomputable def Ns114p884 := nat_lit 1510305269109502657737260333598047138971914330575277212722855936 

noncomputable def Ns114p885 := nat_lit 6244276923518970532514638177371114602281665673269739589645862240256 

noncomputable def Ns114p886 := BSN.sin_dyadic_bound_f 78955628 67108864 3 2 67108864 33554432 Ns114p883 Ns114p107 Ns114p884 Ns114p885 Ns114p110 Ns114p884 61960194 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 78955628) qz359 0 2 Ns114p883 Ns114p107 Ns114p884 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 78955628) (BSN.sinOddQ 67108864) 0 2 Ns114p885 Ns114p110 Ns114p884 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p887 := nat_lit 491730658528791756469653855945736579778930695027575294989823308714907203988769954985901517944849390625 

noncomputable def Ns114p888 := nat_lit 213699166224558299622385900249425110894726715381491756867361906318071334257079578987051025390625 

noncomputable def Ns114p889 := nat_lit 2979681565256876889093713980704269950873174781630211608534093497244077368418112643347312788722090990625 

noncomputable def Ns114p890 := BSN.cos_dyadic_bound_f 87932665 67108864 4 3 67108864 33554432 Ns114p887 Ns114p371 Ns114p888 Ns114p889 Ns114p374 Ns114p888 17284646 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 87932665) qz360 0 3 Ns114p887 Ns114p371 Ns114p888 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 87932665) (BSN.cosOddQ 67108864) 0 3 Ns114p889 Ns114p374 Ns114p888 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p891 := Ns114p843 41475 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 29 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 61960194 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 20 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 17284646 67108864) qz116 rfl rfl (Ns114p874 RS115to132.d9 RS115to132.d11 RS115to132.d13 RS115to132.d17 (Ns114p878 rfl rfl) (Ns114p882 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns114p873 rfl) RS115to132.d19 RS115to132.d21 RS115to132.d23 RS115to132.d25 RS115to132.d17 (Ns114p886 rfl rfl) (Ns114p890 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns114p892 := nat_lit 88471991798060585384208604321 

noncomputable def Ns114p893 := BSN.cos_dyadic_bound_f 17246519 67108864 2 1 67108864 33554432 Ns114p892 Ns114p227 Ns114p892 Ns114p892 Ns114p228 Ns114p892 64904915 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 17246519) qz360 0 1 Ns114p892 Ns114p227 Ns114p892 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 17246519) (BSN.cosOddQ 67108864) 0 1 Ns114p892 Ns114p228 Ns114p892 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p894 := nat_lit 16288397106371839682559410176 

noncomputable def Ns114p895 := BSN.sin_dyadic_bound_f 11297168 67108864 2 1 67108864 33554432 Ns114p894 Ns114p231 Ns114p894 Ns114p894 Ns114p232 Ns114p894 11243885 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 11297168) qz359 0 1 Ns114p894 Ns114p231 Ns114p894 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 11297168) (BSN.sinOddQ 67108864) 0 1 Ns114p894 Ns114p232 Ns114p894 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p896 := Ns114p841 55910 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 62 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 64904915 67108864) BSN.abs_quadSignNeg qz637 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 11243885 67108864) qz116 rfl rfl (Ns114p891 rfl rfl) (Ns114p873 rfl) RS115to132.d27 RS115to132.d29 RS115to132.d31 RS115to132.d33 RS115to132.d17 (Ns114p893 rfl rfl) (Ns114p895 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns114p897 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 7) 1518672 67108864 55910 67108864 1518672 67108864 55910 67108864 203832705417216 94917 2097152 27955 16777216 (Ns114p896 rfl) 

noncomputable def Ns114p898 := @Enclosure.Real.IsNear.mulLit_tf qz709 (Zeta.RiemannSiegel.correction qz115) 764345 2097152 1 4194304 26392273281 68719476736 2355119415701 49478023249920000 20172802120965945 144115188075855872 

noncomputable abbrev qz712 := (@HPow.hPow Real Real Real qz7 qz114 qz9)

noncomputable def Ns114p899 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz712 1 1 0 1 764345 2097152 1 4194304 764345 2097152 1 4194304 

noncomputable def Ns114p900 := @Enclosure.Real.IsNear.sqrt_image qz114 19015672627 335544320 14243 335544320 31574802 31574827 4194304 (@Enclosure.Real.IsNear.of_eq qz114 (@HMul.hMul Real Real Real qz5 qz113 qz3) Bool.false 19015672627 335544320 14243 335544320 (BSN.t_div_two_pi_mk qz113 356075 1000 qz116) (@Enclosure.Real.IsNear.mulLit_ff qz113 qz3 356075 1000 0 1 1335089 8388608 1 8388608 19015672627 335544320 14243 335544320 (Enclosure.Real.IsNear.const Bool.false 356075 1000) RS115to132.d36 rfl)) 

noncomputable abbrev qz917 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 356075 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz713 := qz917

noncomputable abbrev qz467 := qz713

noncomputable abbrev qz118 := qz467

noncomputable def Ns114p901 := @Enclosure.Real.IsNear.sqrt_image qz118 63149629 8388608 25 8388608 11508011 11508016 4194304 (@Enclosure.Real.IsNear.recentre' qz118 Bool.false 63149629 8388608 25 8388608 63149629 8388608 25 8388608 (Ns114p900 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns114p902 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz118) 23016027 8388608 5 8388608 1528689 1528691 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz118) Bool.false 23016027 8388608 5 8388608 23016027 8388608 5 8388608 (Ns114p901 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns114p903 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz118)) Bool.false 3057380 8388608 2 8388608 764345 2097152 1 4194304 (Ns114p902 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz119 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz460))

noncomputable abbrev qz714 := (@HMul.hMul Real Real Real qz884 qz916 qz916)

noncomputable abbrev qz468 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz714 qz708) qz642)

noncomputable abbrev qz120 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz468))

noncomputable def Ns114p904 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz115) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz119) qz120) Bool.false 26392273281 

noncomputable def Ns114p905 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz119) qz120 532521 524288 85 

noncomputable abbrev qz715 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz119))

noncomputable def Ns114p906 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz119) (@Neg.neg Real Real.instNeg qz715) Bool.true 532521 524288 85 4194304 (BSN.inv_eq_neg_inv_neg qz119) 

noncomputable def Ns114p907 := @Enclosure.Real.IsNear.recentre' qz715 Bool.false 8520336 8388608 170 8388608 532521 524288 

noncomputable def Ns114p908 := @Enclosure.Real.IsNear.recentre' qz119 Bool.true 8258917 8388608 117954304 6039797760000 8258917 8388608 460759 23592960000 

noncomputable abbrev qz121 := (@HMul.hMul Real Real Real qz339 qz337 qz460)

noncomputable def Ns114p909 := @Enclosure.Real.IsNear.cos_image qz121 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 27830571) qz357) Bool.false 27830571 8388608 79 4194304 Bool.true 8258917 8388608 1 

noncomputable def Ns114p910 := nat_lit 674651885264149160732794991 

noncomputable def Ns114p911 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz115 884279719003555 140737488355328 1 500000000000000 4429373 8388608 25 8388608 3916804711801933421015 1180591620717411303424 Ns114p910 

noncomputable def Ns114p912 := @Enclosure.Real.IsNear.subLit_ff_p qz118 qz1 63149629 8388608 25 8388608 7 1 0 1 4429373 4429373 8388608 25 

noncomputable def Ns114p913 := @Ns114p912 8388608 (@Enclosure.Real.IsNear.recentre' qz118 Bool.false 63149629 8388608 25 8388608 63149629 8388608 25 8388608 (Ns114p900 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns114p914 := @Enclosure.Real.IsNear.recentre' qz121 Bool.false 3916804711801933421015 1180591620717411303424 Ns114p910 Ns114p501 27830571 8388608 79 4194304 (@Ns114p911 Ns114p501 RS115to132.d35 (Ns114p913 rfl rfl) rfl) 

noncomputable def Ns114p915 := nat_lit 83718281600219279028604880094403788241 

noncomputable def Ns114p916 := BSN.cos_dyadic_bound_f 3024858589 17179869184 2 1 8388608 2882813 Ns114p915 Ns114p817 Ns114p915 Ns114p915 Ns114p818 Ns114p915 8258917 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 3024858589) qz454 0 1 Ns114p915 Ns114p817 Ns114p915 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 3024858589) qz455 0 1 Ns114p915 Ns114p818 Ns114p915 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p917 := @Ns114p909 1440000 (Ns114p914 rfl) (Enclosure.sfrac_false_div 27830571 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 27830571) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 212855500287121798725632) qz358) 226375608064910080 72057594037927936 Bool.false 8258917 8388608 0 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q2 27830571 8388608 226375608064910080 72057594037927936 0 212855500287121798725632 Ns114p85 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 8258917 8388608 212855500287121798725632 Ns114p85 3024858589 17179869184 2882813 2880000 (Ns114p916 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p918 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz119) 8258917 8388608 460759 23592960000 4260083 4260253 4194304 (@Enclosure.Real.IsNear.neg qz119 Bool.true 8258917 8388608 460759 23592960000 (Ns114p908 (Ns114p917 rfl rfl) rfl)) 

noncomputable def Ns114p919 := Ns114p906 (@Enclosure.Real.IsNear.neg qz715 Bool.false 532521 524288 85 4194304 (@Ns114p907 85 4194304 (Ns114p918 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p920 := @Enclosure.Real.IsNear.recentre' qz120 Bool.true 1585952 4194304 

noncomputable abbrev qz122 := (@HMul.hMul Real Real Real qz339 qz337 qz468)

noncomputable def Ns114p921 := @Enclosure.Real.IsNear.cos_image qz122 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 4107401)) qz383) Bool.true 4107401 2097152 

noncomputable def Ns114p922 := nat_lit 19396653636134738423275298245 

noncomputable def Ns114p923 := nat_lit 11635976757747486993027634183582653 

noncomputable def Ns114p924 := @Enclosure.Real.IsNear.recentre' qz122 Bool.true Ns114p922 Ns114p517 Ns114p923 

noncomputable abbrev qz123 := qz468

noncomputable def Ns114p925 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz123 884279719003555 140737488355328 1 500000000000000 21934975120759 

noncomputable abbrev qz469 := (@HSub.hSub Real Real Real qz634 qz714 qz708)

noncomputable abbrev qz124 := qz469

noncomputable def Ns114p926 := @Enclosure.Real.IsNear.subLit_tf qz124 qz26 17536928609655 70368744177664 431184475 70368744177664 1 16 

noncomputable abbrev qz470 := qz714

noncomputable abbrev qz125 := qz470

noncomputable def Ns114p927 := @Enclosure.Real.IsNear.subLit_ff_n qz125 qz115 19619345173129 70368744177664 221469275 70368744177664 4429373 8388608 25 8388608 

noncomputable def Ns114p928 := @Enclosure.Real.IsNear.mulLit_ff qz115 qz115 4429373 8388608 25 8388608 4429373 8388608 25 8388608 19619345173129 70368744177664 

noncomputable def Ns114p929 := nat_lit 2144002929710302158261411597814882631650182356550893157114285368798512902501619949281 

noncomputable def Ns114p930 := nat_lit 23057130311693037386194125205162898933906396383454488107159287139676769823448801 

noncomputable def Ns114p931 := nat_lit 12931545239412557310951683617182730259194059292028344496888362162325210806638783454945 

noncomputable def Ns114p932 := BSN.cos_dyadic_bound_t 4107401 2097152 4 3 4194304 1440000 Ns114p929 Ns114p281 Ns114p930 Ns114p931 Ns114p284 Ns114p930 1585952 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 4107401) (BSN.cosEvenQ 2097152) 0 3 Ns114p929 Ns114p281 Ns114p930 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 4107401) (BSN.cosOddQ 2097152) 0 3 Ns114p931 Ns114p284 Ns114p930 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p933 := @Ns114p920 118737152 3019898880000 49561 131072 463817 11796480000 (@Ns114p921 81 2097152 Bool.true 1585952 4194304 1 1440000 (@Ns114p924 Ns114p520 4107401 2097152 81 2097152 (@Ns114p925 70368744177664 431184475 70368744177664 Ns114p922 Ns114p517 Ns114p923 Ns114p520 RS115to132.d35 (@Ns114p926 0 1 350959601932144 21934975120759 70368744177664 431184475 70368744177664 (@Ns114p927 147110419630380810240 17536928609655 70368744177664 431184475 70368744177664 (@Ns114p928 221469275 70368744177664 (Ns114p913 rfl rfl) (Ns114p913 rfl rfl) rfl) (Ns114p913 rfl rfl) rfl rfl) qz370 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 4107401 2097152) (BSN.cos_neg_of_bound 4107401 2097152 Bool.true 1585952 4194304 1 1440000 (Ns114p932 rfl rfl)) rfl rfl) 

noncomputable def Ns114p934 := @Ns114p898 3619252291469697391 207525870829232455680000 (Ns114p899 qz28 (@Enclosure.Real.IsNear.of_eq qz712 (@Inv.inv Real Real.instInv (Real.sqrt qz118)) Bool.false 764345 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz114 (BSN.t_div_two_pi_nonneg qz113 356075 1000 qz116)) Ns114p903) rfl) (@Ns114p904 68719476736 2355119415701 49478023249920000 (BSN.correction_mk qz115 (BSN.cos_two_pi_p_ne_zero_mk qz113 356075 1000 7 qz116 rfl rfl (@BSN.floor_sqrt_eq_dec qz113 356075 1000 7 qz116 rfl rfl rfl))) (@Ns114p905 4194304 49561 131072 463817 11796480000 26392273281 68719476736 2355119415701 49478023249920000 Ns114p919 (Ns114p933 rfl) rfl)) 

noncomputable def Ns114p935 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz113) (hardyZApproximantRS₀ qz113) Bool.false 26695448694316857 144115188075855872 349408787279348097391 207525870829232455680000 (@Eq.refl Real (hardyZApproximantRS₀ qz113)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz113) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz113) qz113 7) (@HMul.hMul Real Real Real qz5 qz709 (Zeta.RiemannSiegel.correction qz115))) Bool.false 26695448694316857 144115188075855872 349408787279348097391 207525870829232455680000 (BSN.hardyZApproximantRS₀_eq qz113 7 (@BSN.floor_sqrt_eq_dec qz113 356075 1000 7 qz116 rfl rfl rfl)) (@Ns114p839 26695448694316857 144115188075855872 349408787279348097391 207525870829232455680000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz113) qz113 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 7)) Bool.false 94917 2097152 27955 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz113) qz113 7) (Ns114p897 (Ns114p896 rfl) rfl rfl)) (Ns114p934 rfl) rfl rfl)) 

theorem RS115to132.d46 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz113) Bool.false 26695448694316857 144115188075855872 349408787279348097391 207525870829232455680000 := Ns114p935 

noncomputable def Ns114p936 := nat_lit 55409310154529098143105024 

noncomputable abbrev qz918 := (Enclosure.sfrac Bool.false 357630 1000)

noncomputable abbrev qz716 := qz918

noncomputable abbrev qz471 := qz716

noncomputable abbrev qz126 := qz471

noncomputable abbrev qz919 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 357630 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz717 := qz919

noncomputable abbrev qz472 := qz717

noncomputable abbrev qz127 := qz472

noncomputable abbrev qz920 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 357630 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz718 := qz920

noncomputable abbrev qz473 := qz718

noncomputable abbrev qz128 := qz473

noncomputable abbrev qz719 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz127 qz9))

noncomputable def Ns114p937 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz126) qz126 7) (@HMul.hMul Real Real Real qz5 qz719 (Zeta.RiemannSiegel.correction qz128)) 16732221 33554432 28075 16777216 648332818997145555 4611686018427387904 5006425787619908411 276701161105643274240000 Ns114p936 

noncomputable def Ns114p938 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz126) qz126 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 357630 1000 61 97 67108864 33554432 1125899906842624 Bool.false 36473330124 1249 

noncomputable def Ns114p939 := Ns114p938 120242927 48 27397080 8 130587807 48 25364760 8 Bool.false 11892776 41652 Bool.true 98872077 Bool.true 3594657 3537118876014220 1 Bool.false 66790220 Bool.true Bool.false 3592938 Bool.true Bool.true 16732221 

noncomputable def Ns114p940 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz126) qz126 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 357630 1000 30 20 67108864 33554432 1125899906842624 Bool.false 36473330124 1249 

noncomputable def Ns114p941 := Ns114p940 93032624 47 33554424 8 108007536 47 30011992 8 Bool.false 16280221 24527 Bool.false 39642090 Bool.true 45117834 3537118876014220 1 Bool.false 55736843 Bool.true Bool.false 52505053 Bool.false Bool.false 11892776 

noncomputable def Ns114p942 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz126) qz126 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 357630 1000 188 95 67108864 33554432 1125899906842624 Bool.false 36473330124 1249 

noncomputable def Ns114p943 := Ns114p942 46516304 47 47453136 16 73726608 47 38745320 8 Bool.true 67108848 1303 Bool.false 19805195 Bool.false 92119383 3537118876014220 1 Bool.false 64207555 Bool.false Bool.false 65796228 Bool.false Bool.false 16280221 

noncomputable def Ns114p944 := nat_lit 1024215875836007119730795159426987547350539881183 

noncomputable def Ns114p945 := nat_lit 1884499267892885692222445956643498641640652800 

noncomputable def Ns114p946 := nat_lit 2808103439130756065090064000000000 

noncomputable def Ns114p947 := nat_lit 6025577694059326187670682489920000000 

noncomputable abbrev qz720 := (@Eq.refl Real qz918)

noncomputable abbrev qz474 := qz720

noncomputable abbrev qz129 := qz474

noncomputable def Ns114p948 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz126 357630 1000 511597867600 16000000 715260 4000 2000 Ns114p946 Ns114p947 qz129 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns114p949 := nat_lit 2949741722407700504824690059149724136369554857807040000000 

noncomputable abbrev qz721 := (Real.log (Enclosure.sfrac Bool.false 511597867600 16000000))

noncomputable abbrev qz130 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 357630 4000) qz721) (@HMul.hMul Real Real Real qz339 qz343 (@HSub.hSub Real Real Real qz342 qz344 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz345 (@Nat.cast Real Real.instNatCast 715260))))))

noncomputable abbrev qz722 := (Enclosure.sfrac Bool.false 357630 2000)

noncomputable abbrev qz475 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz130 qz722) (@HMul.hMul Real Real Real qz5 qz722 (Real.log Real.pi)))

noncomputable def Ns114p950 := @Enclosure.Real.IsNear.addLit_ft_p qz475 (Enclosure.sfrac Bool.true Ns114p946 Ns114p947) 489537169959753662787 900719925474099200 17135202472045903 921600000000000000000 Ns114p946 Ns114p947 0 1 Ns114p949 

noncomputable def Ns114p951 := nat_lit 3285228336177399402947464396800 

noncomputable abbrev qz476 := (@HSub.hSub Real Real Real qz12 qz130 qz722)

noncomputable abbrev qz477 := (@HMul.hMul Real Real Real qz5 qz722 (Real.log Real.pi))

noncomputable def Ns114p952 := @Enclosure.Real.IsNear.subLit_ff_p qz476 qz477 673909921555805421891 900719925474099200 7141212064147 900000000000000000 1373684045643 6710886400 35763 3355443200 Ns114p951 489537169959753662787 900719925474099200 

noncomputable def Ns114p953 := nat_lit 1347819843111610843782000 

noncomputable abbrev qz478 := qz722

noncomputable def Ns114p954 := @Enclosure.Real.IsNear.subLit_ff_p qz130 qz478 834972155029456470339 900719925474099200 7141212064147 900000000000000000 357630 2000 0 1 Ns114p953 673909921555805421891 900719925474099200 7141212064147 900000000000000000 

noncomputable def Ns114p955 := nat_lit 1880190143127700088690625233993859072 

noncomputable def Ns114p956 := nat_lit 12539831417125490692980736 

noncomputable def Ns114p957 := nat_lit 55873318813488309389308222926681390284466756596354729760158329123504089751328198436755209551697294227618821651079583640439196708601712202481664000000000000000000000000000000 

noncomputable def Ns114p958 := nat_lit 2066333481840073098776351874244371426951856423795836015121315218169575177094679226449968836334950143194880154611807243449963804682915171165798400000000000000000000000000000 

noncomputable def Ns114p959 := nat_lit 488237609332155106485428232252210915575080126394730144407249709618976185196220956151852730303143595461965661018285576014077004462266777600000000000000000000000000000 

noncomputable def Ns114p960 := BSN.log_dyadic_bound 249453867600 773741867600 8 7 Ns114p957 33554432 11520000 Ns114p958 Ns114p959 22436000 1023195735200 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 249453867600) (BSN.artanhQ 773741867600) 0 7 Ns114p958 Ns114p957 Ns114p959 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns114p961 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 357630 4000) qz721 357630 4000 0 1 23357256161282753 2251799813685248 390625063 4500000000000000 835325552095955095539 900719925474099200 4656641376023 600000000000000000 (Enclosure.Real.IsNear.const Bool.false 357630 4000) (BSN.isNear_log_sfrac 511597867600 16000000 23357256161282753 2251799813685248 390625063 4500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 511597867600) qz350)) Bool.false Ns114p956 Ns114p85 1000000161280000 11520000000000000000000 23357256161282753 2251799813685248 390625063 4500000000000000 (BSN.log_rat_reduce_isNear 511597867600 16000000 14 1023195735200 524288000000 22436000 33554432 24973259072661432 36028797018963968 11520000 1000000000000000 rfl rfl rfl rfl (Ns114p960 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p962 := BSN.arctan_dyadic_bound_f 1000 715260 1 0 4194304 1440000 0 1 1 0 1 1 5864 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 715260) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 715260) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz479 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 715260)))

noncomputable def Ns114p963 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz479 884279719003555 562949953421312 1 2000000000000000 5864 4194304 1 1440000 3705636824008624177152 883492666246563 562949953421312 12500000009 18000000000000000 qz16 (Ns114p962 rfl) rfl rfl 

noncomputable def Ns114p964 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 357630 4000) qz721) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz479)) 835325552095955095539 900719925474099200 4656641376023 600000000000000000 883492666246563 2251799813685248 12500000009 72000000000000000 Ns114p955 834972155029456470339 900719925474099200 7141212064147 900000000000000000 (Ns114p961 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz479) 1 4 0 1 883492666246563 562949953421312 12500000009 18000000000000000 883492666246563 2251799813685248 12500000009 72000000000000000 qz353 Ns114p963 rfl) 

noncomputable def Ns114p965 := @Ns114p950 Ns114p944 Ns114p945 17135202472045903 921600000000000000000 (@Ns114p952 17135202472045903 921600000000000000000 (Ns114p954 (Ns114p964 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 357630 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz478 (Real.log Real.pi) 357630 2000 0 1 38410761 33554432 1 16777216 1373684045643 6710886400 35763 3355443200 (Enclosure.Real.IsNear.const Bool.false 357630 2000) RS115to132.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns114p946 Ns114p947) 

noncomputable def Ns114p966 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz126) Bool.false Ns114p944 Ns114p945 17135202472045903 921600000000000000000 4559166265 8388608 157 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz126) (@HAdd.hAdd Real Real Real qz354 qz475 (Enclosure.sfrac Bool.true Ns114p946 Ns114p947)) Bool.false Ns114p944 Ns114p945 17135202472045903 921600000000000000000 Ns114p948 (Ns114p965 rfl rfl)) 

noncomputable def Ns114p967 := nat_lit 1898302047303972977377280 

noncomputable def Ns114p968 := nat_lit 139789800573880141569591822798948000196964771813500400967531217058018484053220434499265 

noncomputable def Ns114p969 := nat_lit 280468521120837706588263797183033457667113473752646025934240699026418420421388523201 

noncomputable def Ns114p970 := nat_lit 365662052468823776395407108801805565393922885315949147063450131163053256982514127984321 

noncomputable def Ns114p971 := BSN.sin_dyadic_bound_f 26976494599 17179869184 3 2 8388608 2882813 Ns114p968 Ns114p98 Ns114p969 Ns114p970 Ns114p101 Ns114p969 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26976494599) qz355 0 2 Ns114p968 Ns114p98 Ns114p969 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26976494599) qz356 0 2 Ns114p970 Ns114p101 Ns114p969 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p972 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz126) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4559166265) qz357) Bool.false 4559166265 8388608 157 8388608 Bool.true 8388606 8388608 1 1440000 (Ns114p966 rfl) (Enclosure.sfrac_false_div 4559166265 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4559166265) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns114p967) qz358) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 86 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q1 4559166265 8388608 226375608064910080 72057594037927936 86 Ns114p967 Ns114p85 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388606 8388608 Ns114p967 Ns114p85 26976494599 17179869184 2882813 2880000 (Ns114p971 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p973 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz126) Bool.false Ns114p944 Ns114p945 17135202472045903 921600000000000000000 36473330124 67108864 1249 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz126) (@HAdd.hAdd Real Real Real qz354 qz475 (Enclosure.sfrac Bool.true Ns114p946 Ns114p947)) Bool.false Ns114p944 Ns114p945 17135202472045903 921600000000000000000 Ns114p948 (Ns114p965 rfl rfl)) 

noncomputable def Ns114p974 := Ns114p943 24527 BSN.abs_quadSignPos (BSN.cos_quad_nat0 188 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 64207555 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 95 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 65796228 67108864) qz129 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz126) qz126 1) Bool.true 4194303 4194304 915893 47185920000 67108848 67108864 1303 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz126) qz126 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz126)) Bool.true 4194303 4194304 915893 47185920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz126) qz126) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz126)) Bool.true 8388606 8388608 234468608 12079595520000 4194303 4194304 915893 47185920000 (Ns114p972 rfl rfl) rfl)) rfl) (Ns114p973 rfl) RS115to132.d7 

noncomputable def Ns114p975 := nat_lit 153856727599176715311593400625 

noncomputable def Ns114p976 := BSN.cos_dyadic_bound_f 19805195 67108864 2 1 67108864 33554432 Ns114p975 Ns114p227 Ns114p975 Ns114p975 Ns114p228 Ns114p975 64207555 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 19805195) qz360 0 1 Ns114p975 Ns114p227 Ns114p975 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 19805195) (BSN.cosOddQ 67108864) 0 1 Ns114p975 Ns114p228 Ns114p975 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p977 := nat_lit 1539047270486398835335982718676338437430124057273694063257401543248142867477277119249481896170565592161 

noncomputable def Ns114p978 := nat_lit 373432614834532718795776031173462368833386424473753238843138318997706666016135328749694640907361 

noncomputable def Ns114p979 := nat_lit 7689656181556226812704747115928496019773848339903395858913394599948809209845541303031703895760866305121 

noncomputable def Ns114p980 := BSN.sin_dyadic_bound_f 92119383 67108864 4 3 67108864 33554432 Ns114p977 Ns114p579 Ns114p978 Ns114p979 Ns114p582 Ns114p978 65796228 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 92119383) qz359 0 3 Ns114p977 Ns114p579 Ns114p978 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 92119383) (BSN.sinOddQ 67108864) 0 3 Ns114p979 Ns114p582 Ns114p978 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p981 := nat_lit 84156270039088017579574161450779315075169069028332571095856800000 

noncomputable def Ns114p982 := nat_lit 6098911696254399878796514750401867601128284949144512100000000 

noncomputable def Ns114p983 := nat_lit 252456612293871543938964891322837141490304950515099424263370400000 

noncomputable def Ns114p984 := BSN.cos_dyadic_bound_f 39642090 67108864 3 2 67108864 33554432 Ns114p981 Ns114p113 Ns114p982 Ns114p983 Ns114p116 Ns114p982 55736843 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 39642090) qz360 0 2 Ns114p981 Ns114p113 Ns114p982 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 39642090) (BSN.cosOddQ 67108864) 0 2 Ns114p983 Ns114p116 Ns114p982 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p985 := nat_lit 141212977277608764908975187108114747391865495486990294598411346176 

noncomputable def Ns114p986 := nat_lit 17170618387122459235286886405772984168864047277836789809930496 

noncomputable def Ns114p987 := nat_lit 423604590596052049808454987551532696207258758366415210215614177536 

noncomputable def Ns114p988 := BSN.cos_dyadic_bound_f 45117834 67108864 3 2 67108864 33554432 Ns114p985 Ns114p113 Ns114p986 Ns114p987 Ns114p116 Ns114p986 52505053 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 45117834) qz360 0 2 Ns114p985 Ns114p113 Ns114p986 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 45117834) (BSN.cosOddQ 67108864) 0 2 Ns114p987 Ns114p116 Ns114p986 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p989 := Ns114p941 41652 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 30 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 55736843 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 20 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 52505053 67108864) qz129 rfl rfl (Ns114p974 RS115to132.d9 RS115to132.d11 RS115to132.d13 RS115to132.d17 (Ns114p976 rfl rfl) (Ns114p980 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns114p973 rfl) RS115to132.d19 RS115to132.d21 RS115to132.d23 RS115to132.d25 RS115to132.d17 (Ns114p984 rfl rfl) (Ns114p988 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns114p990 := nat_lit 2043191758865520863034129741259492570957860315978433743696633431926590412333127138630922008897349567921 

noncomputable def Ns114p991 := nat_lit 872738006753445196770033837913593360934743449311284206033919074879703408552976916907824605119921 

noncomputable def Ns114p992 := nat_lit 10206130761139006148281604357640159796841852059368999883452716517638050639175461841188245220737152796081 

noncomputable def Ns114p993 := BSN.sin_dyadic_bound_f 98872077 67108864 4 3 67108864 33554432 Ns114p990 Ns114p579 Ns114p991 Ns114p992 Ns114p582 Ns114p991 66790220 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 98872077) qz359 0 3 Ns114p990 Ns114p579 Ns114p991 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 98872077) (BSN.sinOddQ 67108864) 0 3 Ns114p992 Ns114p582 Ns114p991 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p994 := BSN.sin_dyadic_bound_f 3594657 67108864 1 0 67108864 33554432 0 1 1 0 1 1 3592938 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 3594657) qz359 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 3594657) (BSN.sinOddQ 67108864) 0 0 rfl) rfl rfl 

noncomputable def Ns114p995 := Ns114p939 56150 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 61 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66790220 67108864) BSN.abs_quadSignNeg qz637 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 3592938 67108864) qz129 rfl rfl (Ns114p989 rfl rfl) (Ns114p973 rfl) RS115to132.d27 RS115to132.d29 RS115to132.d31 RS115to132.d33 RS115to132.d17 (Ns114p993 rfl rfl) (Ns114p994 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns114p996 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz126) qz126 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz126) qz126 7) 16732221 67108864 56150 67108864 16732221 67108864 56150 67108864 2245760687013888 16732221 33554432 28075 16777216 (Ns114p995 rfl) 

noncomputable def Ns114p997 := @Enclosure.Real.IsNear.mulLit_tf qz719 (Zeta.RiemannSiegel.correction qz128) 763513 2097152 1 4194304 849144440235 2199023255552 9785586216379 197912092999680000 648332818997145555 4611686018427387904 

noncomputable abbrev qz723 := (@HPow.hPow Real Real Real qz7 qz127 qz9)

noncomputable def Ns114p998 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz723 1 1 0 1 763513 2097152 1 4194304 763513 2097152 1 4194304 

noncomputable def Ns114p999 := @Enclosure.Real.IsNear.sqrt_image qz127 47746787907 838860800 35763 838860800 31643671 31643696 4194304 (@Enclosure.Real.IsNear.of_eq qz127 (@HMul.hMul Real Real Real qz5 qz126 qz3) Bool.false 47746787907 838860800 35763 838860800 (BSN.t_div_two_pi_mk qz126 357630 1000 qz129) (@Enclosure.Real.IsNear.mulLit_ff qz126 qz3 357630 1000 0 1 1335089 8388608 1 8388608 47746787907 838860800 35763 838860800 (Enclosure.Real.IsNear.const Bool.false 357630 1000) RS115to132.d36 rfl)) 

noncomputable abbrev qz921 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 357630 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz724 := qz921

noncomputable abbrev qz480 := qz724

noncomputable abbrev qz131 := qz480

noncomputable def Ns114p1000 := @Enclosure.Real.IsNear.sqrt_image qz131 63287367 8388608 25 8388608 11520554 11520560 4194304 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 63287367 8388608 25 8388608 63287367 8388608 25 8388608 (Ns114p999 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns114p1001 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz131) 11520557 4194304 3 4194304 1527025 1527027 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz131) Bool.false 23041114 8388608 6 8388608 11520557 4194304 3 4194304 (Ns114p1000 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns114p1002 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz131)) Bool.false 3054052 8388608 2 8388608 763513 2097152 1 4194304 (Ns114p1001 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz132 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz473))

noncomputable abbrev qz725 := (@HMul.hMul Real Real Real qz884 qz920 qz920)

noncomputable abbrev qz481 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz725 qz718) qz642)

noncomputable abbrev qz133 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz481))

noncomputable def Ns114p1003 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz128) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz132) qz133) Bool.false 849144440235 

noncomputable def Ns114p1004 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz132) qz133 8726627 8388608 179 

noncomputable abbrev qz726 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz132))

noncomputable def Ns114p1005 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz132) (@Neg.neg Real Real.instNeg qz726) Bool.true 8726627 8388608 179 8388608 (BSN.inv_eq_neg_inv_neg qz132) 

noncomputable def Ns114p1006 := @Enclosure.Real.IsNear.recentre' qz726 Bool.false 8726627 8388608 179 8388608 8726627 8388608 

noncomputable def Ns114p1007 := @Enclosure.Real.IsNear.recentre' qz132 Bool.true 8063682 8388608 117954304 6039797760000 4031841 4194304 460759 23592960000 

noncomputable abbrev qz134 := (@HMul.hMul Real Real Real qz339 qz337 qz473)

noncomputable def Ns114p1008 := @Enclosure.Real.IsNear.cos_image qz134 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7174001) qz383) Bool.false 7174001 2097152 79 4194304 Bool.true 8063682 8388608 1 

noncomputable def Ns114p1009 := nat_lit 674651885265332321143627887 

noncomputable def Ns114p1010 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz128 884279719003555 140737488355328 1 500000000000000 4567111 8388608 25 8388608 4038603631738045079605 1180591620717411303424 Ns114p1009 

noncomputable def Ns114p1011 := @Enclosure.Real.IsNear.subLit_ff_p qz131 qz1 63287367 8388608 25 8388608 7 1 0 1 4567111 4567111 8388608 25 

noncomputable def Ns114p1012 := @Ns114p1011 8388608 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 63287367 8388608 25 8388608 63287367 8388608 25 8388608 (Ns114p999 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns114p1013 := @Enclosure.Real.IsNear.recentre' qz134 Bool.false 4038603631738045079605 1180591620717411303424 Ns114p1009 Ns114p501 7174001 2097152 79 4194304 (@Ns114p1010 Ns114p501 RS115to132.d35 (Ns114p1012 rfl rfl) rfl) 

noncomputable def Ns114p1014 := nat_lit 529632921914949816062548857377326898641 

noncomputable def Ns114p1015 := BSN.cos_dyadic_bound_f 4797265373 17179869184 2 1 8388608 2882813 Ns114p1014 Ns114p817 Ns114p1014 Ns114p1014 Ns114p818 Ns114p1014 8063682 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 4797265373) qz454 0 1 Ns114p1014 Ns114p817 Ns114p1014 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 4797265373) qz455 0 1 Ns114p1014 Ns114p818 Ns114p1014 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1016 := @Ns114p1008 1440000 (Ns114p1013 rfl) (Enclosure.sfrac_false_div 7174001 2097152) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7174001) qz383) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 84394384962293493399552) qz384) 226375608064910080 72057594037927936 Bool.false 8063682 8388608 0 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q2 7174001 2097152 226375608064910080 72057594037927936 0 84394384962293493399552 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 8063682 8388608 84394384962293493399552 302231454903657293676544 4797265373 17179869184 2882813 2880000 (Ns114p1015 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p1017 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz132) 4031841 4194304 460759 23592960000 4363224 4363403 4194304 (@Enclosure.Real.IsNear.neg qz132 Bool.true 4031841 4194304 460759 23592960000 (Ns114p1007 (Ns114p1016 rfl rfl) rfl)) 

noncomputable def Ns114p1018 := Ns114p1005 (@Enclosure.Real.IsNear.neg qz726 Bool.false 8726627 8388608 179 8388608 (@Ns114p1006 179 8388608 (Ns114p1017 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p1019 := @Enclosure.Real.IsNear.recentre' qz133 Bool.true 1556880 4194304 

noncomputable abbrev qz135 := (@HMul.hMul Real Real Real qz339 qz337 qz481)

noncomputable def Ns114p1020 := @Enclosure.Real.IsNear.cos_image qz135 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16366891)) qz357) Bool.true 16366891 8388608 

noncomputable def Ns114p1021 := nat_lit 19322614995879654612698243405 

noncomputable def Ns114p1022 := nat_lit 11821827160481313214854941884926057 

noncomputable def Ns114p1023 := @Enclosure.Real.IsNear.recentre' qz135 Bool.true Ns114p1021 Ns114p517 Ns114p1022 

noncomputable abbrev qz136 := qz481

noncomputable def Ns114p1024 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz136 884279719003555 140737488355328 1 500000000000000 21851247496271 

noncomputable abbrev qz482 := (@HSub.hSub Real Real Real qz634 qz725 qz718)

noncomputable abbrev qz137 := qz482

noncomputable def Ns114p1025 := @Enclosure.Real.IsNear.subLit_tf qz137 qz26 17453200985167 70368744177664 438071375 70368744177664 1 16 

noncomputable abbrev qz483 := qz725

noncomputable abbrev qz138 := qz483

noncomputable def Ns114p1026 := @Enclosure.Real.IsNear.subLit_ff_n qz138 qz128 20858502886321 70368744177664 228356175 70368744177664 4567111 8388608 25 8388608 

noncomputable def Ns114p1027 := @Enclosure.Real.IsNear.mulLit_ff qz128 qz128 4567111 8388608 25 8388608 4567111 8388608 25 8388608 20858502886321 70368744177664 

noncomputable def Ns114p1028 := nat_lit 35419649426850573735141616622985679632156451104525803176240437850578099272659623360953855761 

noncomputable def Ns114p1029 := nat_lit 369482847024300478476719773435110185697877031490537732130402987917787050189248909291281 

noncomputable def Ns114p1030 := nat_lit 213652254513127083505774887402118207232455641249659558540239366228024546986875810897416433425 

noncomputable def Ns114p1031 := BSN.cos_dyadic_bound_t 16366891 8388608 4 3 4194304 1440000 Ns114p1028 Ns114p631 Ns114p1029 Ns114p1030 Ns114p634 Ns114p1029 1556880 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16366891) (BSN.cosEvenQ 8388608) 0 3 Ns114p1028 Ns114p631 Ns114p1029 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16366891) (BSN.cosOddQ 8388608) 0 3 Ns114p1030 Ns114p634 Ns114p1029 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1032 := @Ns114p1019 482148608 12079595520000 97305 262144 1883393 47185920000 (@Ns114p1020 329 8388608 Bool.true 1556880 4194304 1 1440000 (@Ns114p1023 Ns114p520 16366891 8388608 329 8388608 (@Ns114p1024 70368744177664 438071375 70368744177664 Ns114p1021 Ns114p517 Ns114p1022 Ns114p520 RS115to132.d35 (@Ns114p1025 0 1 349619959940336 21851247496271 70368744177664 438071375 70368744177664 (@Ns114p1026 146408061409779777536 17453200985167 70368744177664 438071375 70368744177664 (@Ns114p1027 228356175 70368744177664 (Ns114p1012 rfl rfl) (Ns114p1012 rfl rfl) rfl) (Ns114p1012 rfl rfl) rfl rfl) qz370 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16366891 8388608) (BSN.cos_neg_of_bound 16366891 8388608 Bool.true 1556880 4194304 1 1440000 (Ns114p1031 rfl rfl)) rfl rfl) 

noncomputable def Ns114p1033 := @Ns114p997 5006425787619908411 276701161105643274240000 (Ns114p998 qz28 (@Enclosure.Real.IsNear.of_eq qz723 (@Inv.inv Real Real.instInv (Real.sqrt qz131)) Bool.false 763513 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz127 (BSN.t_div_two_pi_nonneg qz126 357630 1000 qz129)) Ns114p1002) rfl) (@Ns114p1003 2199023255552 9785586216379 197912092999680000 (BSN.correction_mk qz128 (BSN.cos_two_pi_p_ne_zero_mk qz126 357630 1000 7 qz129 rfl rfl (@BSN.floor_sqrt_eq_dec qz126 357630 1000 7 qz129 rfl rfl rfl))) (@Ns114p1004 8388608 97305 262144 1883393 47185920000 849144440235 2199023255552 9785586216379 197912092999680000 Ns114p1018 (Ns114p1032 rfl) rfl)) 

noncomputable def Ns114p1034 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz126) (hardyZApproximantRS₀ qz126) Bool.true 1651326124505075757 4611686018427387904 468038260034787908411 276701161105643274240000 (@Eq.refl Real (hardyZApproximantRS₀ qz126)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz126) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz126) qz126 7) (@HMul.hMul Real Real Real qz5 qz719 (Zeta.RiemannSiegel.correction qz128))) Bool.true 1651326124505075757 4611686018427387904 468038260034787908411 276701161105643274240000 (BSN.hardyZApproximantRS₀_eq qz126 7 (@BSN.floor_sqrt_eq_dec qz126 357630 1000 7 qz129 rfl rfl rfl)) (@Ns114p937 1651326124505075757 4611686018427387904 468038260034787908411 276701161105643274240000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz126) qz126 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz126) qz126 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz126) qz126 7)) Bool.true 16732221 33554432 28075 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz126) qz126 7) (Ns114p996 (Ns114p995 rfl) rfl rfl)) (Ns114p1033 rfl) rfl rfl)) 

theorem RS115to132.d47 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz126) Bool.true 1651326124505075757 4611686018427387904 468038260034787908411 276701161105643274240000 := Ns114p1034 

noncomputable def Ns114p1035 := nat_lit 67057580720375677957963776 

noncomputable abbrev qz922 := (Enclosure.sfrac Bool.false 359184 1000)

noncomputable abbrev qz727 := qz922

noncomputable abbrev qz484 := qz727

noncomputable abbrev qz139 := qz484

noncomputable abbrev qz923 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 359184 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz728 := qz923

noncomputable abbrev qz485 := qz728

noncomputable abbrev qz140 := qz485

noncomputable abbrev qz924 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 359184 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz729 := qz924

noncomputable abbrev qz486 := qz729

noncomputable abbrev qz141 := qz486

noncomputable abbrev qz730 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz140 qz9))

noncomputable def Ns114p1036 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz139) qz139 7) (@HMul.hMul Real Real Real qz5 qz730 (Zeta.RiemannSiegel.correction qz141)) 417297 262144 56395 33554432 20887043100591582765 147573952589676412928 15739727964133700411 830103483316929822720000 Ns114p1035 

noncomputable def Ns114p1037 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz139) qz139 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 359184 1000 61 96 67108864 33554432 1125899906842624 Bool.false 36684187884 1254 

noncomputable def Ns114p1038 := Ns114p1037 120242927 48 27397080 8 130587807 48 25364760 8 Bool.false 76386992 41834 Bool.true 74871826 Bool.true 101084707 3537118876014220 1 Bool.false 60277761 Bool.true Bool.false 4326647 Bool.false Bool.false 53414016 

noncomputable def Ns114p1039 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz139) qz139 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 359184 1000 31 20 67108864 33554432 1125899906842624 Bool.false 36684187884 1254 

noncomputable def Ns114p1040 := Ns114p1039 93032624 47 33554424 8 108007536 47 30011992 8 Bool.false 46133351 24635 Bool.false 512796 Bool.true 2103785 3537118876014220 1 Bool.false 512791 Bool.false Bool.false 67075891 Bool.false Bool.false 76386992 

noncomputable def Ns114p1041 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz139) qz139 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 359184 1000 189 96 67108864 33554432 1125899906842624 Bool.false 36684187884 1254 

noncomputable def Ns114p1042 := Ns114p1041 46516304 47 47453136 16 73726608 47 38745320 8 Bool.false 67108856 1311 Bool.false 52962262 Bool.false 82991637 3537118876014220 1 Bool.false 47633160 Bool.true Bool.false 22007833 Bool.false Bool.false 46133351 

noncomputable def Ns114p1043 := nat_lit 32265862397824653534273482248376624961820831361503 

noncomputable def Ns114p1044 := nat_lit 59026122598138159207915633386785886941111910400 

noncomputable def Ns114p1045 := nat_lit 2869645715479754386246275563520000 

noncomputable def Ns114p1046 := nat_lit 6184390552612527190605652291340206080 

noncomputable abbrev qz731 := (@Eq.refl Real qz922)

noncomputable abbrev qz487 := qz731

noncomputable abbrev qz142 := qz487

noncomputable def Ns114p1047 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz139 359184 1000 516053583424 16000000 718368 4000 2000 Ns114p1045 Ns114p1046 qz142 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns114p1048 := nat_lit 380623600458690568923986447873329888829620200739342909440 

noncomputable abbrev qz732 := (Real.log (Enclosure.sfrac Bool.false 516053583424 16000000))

noncomputable abbrev qz143 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 359184 4000) qz732) (@HMul.hMul Real Real Real qz339 qz343 (@HSub.hSub Real Real Real qz342 qz344 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz345 (@Nat.cast Real Real.instNatCast 718368))))))

noncomputable abbrev qz733 := (Enclosure.sfrac Bool.false 359184 2000)

noncomputable abbrev qz488 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz143 qz733) (@HMul.hMul Real Real Real qz5 qz733 (Real.log Real.pi)))

noncomputable def Ns114p1049 := @Enclosure.Real.IsNear.addLit_ft_p qz488 (Enclosure.sfrac Bool.true Ns114p1045 Ns114p1046) 61545906636068543143 112589990684262400 10755602726140069 576000000000000000000 Ns114p1045 Ns114p1046 0 1 Ns114p1048 

noncomputable def Ns114p1050 := nat_lit 1290711211936444173894287360000 

noncomputable abbrev qz489 := (@HSub.hSub Real Real Real qz12 qz143 qz733)

noncomputable abbrev qz490 := (@HMul.hMul Real Real Real qz5 qz733 (Real.log Real.pi))

noncomputable def Ns114p1051 := @Enclosure.Real.IsNear.subLit_ff_p qz489 qz490 423463221645509674307 562949953421312000 71715636315421 9000000000000000000 862283173689 4194304000 22449 2097152000 Ns114p1050 61545906636068543143 112589990684262400 

noncomputable abbrev qz491 := qz733

noncomputable def Ns114p1052 := @Enclosure.Real.IsNear.subLit_ff_p qz143 qz491 524564529680349939011 562949953421312000 71715636315421 9000000000000000000 359184 2000 0 1 846926443291019348614000 423463221645509674307 562949953421312000 71715636315421 9000000000000000000 

noncomputable def Ns114p1053 := nat_lit 1181214310200101737273931639950409728 

noncomputable def Ns114p1054 := nat_lit 12550314860309286714605568 

noncomputable def Ns114p1055 := nat_lit 60550452733808440876929021111394809977345064363670051461690155061750770007721239837689701828358271046241619305151374472723543716312414577498580129582281857164444304828006400 

noncomputable def Ns114p1056 := nat_lit 2297324753367322987670571140810954514929287045219692161603117690298715982488579750642373625698425126497993096277376167300783749206618311458674388371028511528061350277283840 

noncomputable def Ns114p1057 := nat_lit 625568896552046036357896393396296254988907649651862623914840167747734757754462212453490884288467264929190220436452869788362454228330961574718888662548042263308533760 

noncomputable def Ns114p1058 := BSN.log_dyadic_bound 253909583424 778197583424 8 7 Ns114p1055 33554432 11520000 Ns114p1056 Ns114p1057 22726974 1032107166848 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 253909583424) (BSN.artanhQ 778197583424) 0 7 Ns114p1056 Ns114p1055 Ns114p1057 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns114p1059 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 359184 4000) qz732 359184 4000 0 1 23376783095876289 2251799813685248 390625063 4500000000000000 524785403719326811761 562949953421312000 2923047346429 375000000000000000 (Enclosure.Real.IsNear.const Bool.false 359184 4000) (BSN.isNear_log_sfrac 516053583424 16000000 23376783095876289 2251799813685248 390625063 4500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 516053583424) qz350)) Bool.false Ns114p1054 Ns114p85 1000000161280000 11520000000000000000000 23376783095876289 2251799813685248 390625063 4500000000000000 (BSN.log_rat_reduce_isNear 516053583424 16000000 14 1032107166848 524288000000 22726974 33554432 24973259072661432 36028797018963968 11520000 1000000000000000 rfl rfl rfl rfl (Ns114p1058 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p1060 := BSN.arctan_dyadic_bound_f 1000 718368 1 0 4194304 1440000 0 1 1 0 1 1 5838 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 718368) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 718368) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz492 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 718368)))

noncomputable def Ns114p1061 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz492 884279719003555 562949953421312 1 2000000000000000 5838 4194304 1 1440000 3705651460707413131264 883496155907491 562949953421312 12500000009 18000000000000000 qz16 (Ns114p1060 rfl) rfl rfl 

noncomputable def Ns114p1062 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 359184 4000) qz732) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz492)) 524785403719326811761 562949953421312000 2923047346429 375000000000000000 883496155907491 2251799813685248 12500000009 72000000000000000 Ns114p1053 524564529680349939011 562949953421312000 71715636315421 9000000000000000000 (Ns114p1059 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz492) 1 4 0 1 883496155907491 562949953421312 12500000009 18000000000000000 883496155907491 2251799813685248 12500000009 72000000000000000 qz353 Ns114p1061 rfl) 

noncomputable def Ns114p1063 := @Ns114p1049 Ns114p1043 Ns114p1044 10755602726140069 576000000000000000000 (@Ns114p1051 10755602726140069 576000000000000000000 (Ns114p1052 (Ns114p1062 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 359184 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz491 (Real.log Real.pi) 359184 2000 0 1 38410761 33554432 1 16777216 862283173689 4194304000 22449 2097152000 (Enclosure.Real.IsNear.const Bool.false 359184 2000) RS115to132.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns114p1045 Ns114p1046) 

noncomputable def Ns114p1064 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz139) Bool.false Ns114p1043 Ns114p1044 10755602726140069 576000000000000000000 4585523485 8388608 79 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz139) (@HAdd.hAdd Real Real Real qz354 qz488 (Enclosure.sfrac Bool.true Ns114p1045 Ns114p1046)) Bool.false Ns114p1043 Ns114p1044 10755602726140069 576000000000000000000 Ns114p1047 (Ns114p1063 rfl rfl)) 

noncomputable def Ns114p1065 := nat_lit 1898825291124344451235840 

noncomputable def Ns114p1066 := nat_lit 139944299429989164911294528551520904637012123279413698796456839583859584045015548774625 

noncomputable def Ns114p1067 := nat_lit 281087579940420076254542172421459538547493646423712879066117819030210394365224503521 

noncomputable def Ns114p1068 := nat_lit 366065690044353799406121173165300958605954856970921295043660865298345236622258930927841 

noncomputable def Ns114p1069 := BSN.sin_dyadic_bound_f 26983930341 17179869184 3 2 8388608 2882813 Ns114p1066 Ns114p98 Ns114p1067 Ns114p1068 Ns114p101 Ns114p1067 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26983930341) qz355 0 2 Ns114p1066 Ns114p98 Ns114p1067 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26983930341) qz356 0 2 Ns114p1068 Ns114p101 Ns114p1067 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1070 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz139) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4585523485) qz357) Bool.false 4585523485 8388608 79 4194304 Bool.false 8388607 8388608 1 1440000 (Ns114p1064 rfl) (Enclosure.sfrac_false_div 4585523485 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4585523485) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns114p1065) qz358) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 86 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q3 4585523485 8388608 226375608064910080 72057594037927936 86 Ns114p1065 Ns114p85 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns114p1065 Ns114p85 26983930341 17179869184 2882813 2880000 (Ns114p1069 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p1071 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz139) Bool.false Ns114p1043 Ns114p1044 10755602726140069 576000000000000000000 36684187884 67108864 1254 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz139) (@HAdd.hAdd Real Real Real qz354 qz488 (Enclosure.sfrac Bool.true Ns114p1045 Ns114p1046)) Bool.false Ns114p1043 Ns114p1044 10755602726140069 576000000000000000000 Ns114p1047 (Ns114p1063 rfl rfl)) 

noncomputable abbrev qz734 := (BSN.cos_quad_nat0 96 rfl)

noncomputable def Ns114p1072 := Ns114p1042 24635 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 189 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 47633160 67108864) BSN.abs_quadSignPos qz734 (BSN.sfrac_eq_quadSignPos_mul Bool.false 22007833 67108864) qz142 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz139) qz139 1) Bool.false 8388607 8388608 460759 23592960000 67108856 67108864 1311 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz139) qz139 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz139)) Bool.false 8388607 8388608 460759 23592960000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz139) qz139) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz139)) Bool.false 8388607 8388608 117954304 6039797760000 8388607 8388608 460759 23592960000 (Ns114p1070 rfl rfl) rfl)) rfl) (Ns114p1071 rfl) RS115to132.d7 

noncomputable def Ns114p1073 := nat_lit 482639815106217326069154034113025557008849549400513816995902808320 

noncomputable def Ns114p1074 := nat_lit 61905922996492596350870520661000548318692430645058259387965696 

noncomputable def Ns114p1075 := nat_lit 1263956429974289151691787727548282457944947127351729902569307791616 

noncomputable def Ns114p1076 := BSN.sin_dyadic_bound_f 52962262 67108864 3 2 67108864 33554432 Ns114p1073 Ns114p107 Ns114p1074 Ns114p1075 Ns114p110 Ns114p1074 47633160 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 52962262) qz359 0 2 Ns114p1073 Ns114p107 Ns114p1074 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 52962262) (BSN.sinOddQ 67108864) 0 2 Ns114p1075 Ns114p110 Ns114p1074 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1077 := nat_lit 390037601838226866601276314470960951378870082260011307459951359273178587638760902619776695124932114961 

noncomputable def Ns114p1078 := nat_lit 106760837727202616373391802921454349452282120911940954712725549201116407507337820837250297444881 

noncomputable def Ns114p1079 := nat_lit 2364034420956442252732043022367626867992314508336138551171927418490675589866316689469778624202710399505 

noncomputable def Ns114p1080 := BSN.cos_dyadic_bound_f 82991637 67108864 4 3 67108864 33554432 Ns114p1077 Ns114p371 Ns114p1078 Ns114p1079 Ns114p374 Ns114p1078 22007833 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 82991637) qz360 0 3 Ns114p1077 Ns114p371 Ns114p1078 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 82991637) (BSN.cosOddQ 67108864) 0 3 Ns114p1079 Ns114p374 Ns114p1078 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1081 := BSN.sin_dyadic_bound_f 512796 67108864 1 0 67108864 33554432 0 1 1 0 1 1 512791 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 512796) qz359 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 512796) (BSN.sinOddQ 67108864) 0 0 rfl) rfl rfl 

noncomputable def Ns114p1082 := nat_lit 19588691067606738372750625 

noncomputable def Ns114p1083 := BSN.cos_dyadic_bound_f 2103785 67108864 2 1 67108864 33554432 Ns114p1082 Ns114p227 Ns114p1082 Ns114p1082 Ns114p228 Ns114p1082 67075891 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 2103785) qz360 0 1 Ns114p1082 Ns114p227 Ns114p1082 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 2103785) (BSN.cosOddQ 67108864) 0 1 Ns114p1082 Ns114p228 Ns114p1082 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1084 := Ns114p1040 41834 BSN.abs_quadSignPos (BSN.cos_quad_nat3 31 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 512791 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 20 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 67075891 67108864) qz142 rfl rfl (Ns114p1072 RS115to132.d9 RS115to132.d11 RS115to132.d13 RS115to132.d17 (Ns114p1076 rfl rfl) (Ns114p1080 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns114p1071 rfl) RS115to132.d19 RS115to132.d21 RS115to132.d23 RS115to132.d25 RS115to132.d17 (Ns114p1081 rfl rfl) (Ns114p1083 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns114p1085 := nat_lit 1928401641460506111779996702069022955147674865409053991805720674560 

noncomputable def Ns114p1086 := nat_lit 987523410332010708821141436120646753880033145153855424597278976 

noncomputable def Ns114p1087 := nat_lit 5048976880208407037323804752617531454451914117645844688803729981696 

noncomputable def Ns114p1088 := BSN.sin_dyadic_bound_f 74871826 67108864 3 2 67108864 33554432 Ns114p1085 Ns114p107 Ns114p1086 Ns114p1087 Ns114p110 Ns114p1086 60277761 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 74871826) qz359 0 2 Ns114p1085 Ns114p107 Ns114p1086 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 74871826) (BSN.sinOddQ 67108864) 0 2 Ns114p1087 Ns114p110 Ns114p1086 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1089 := nat_lit 859876221976574562179533622257517709354520499650779729076059121048930251290719352420208359521776800881 

noncomputable def Ns114p1090 := nat_lit 1138218078279329587451843475430046498625023402486257557638003718852378482524470236975058273932401 

noncomputable def Ns114p1091 := nat_lit 5205952879854032760090317510059212095585496133819817885418227725096166008906864923979846760618405368945 

noncomputable def Ns114p1092 := BSN.cos_dyadic_bound_f 101084707 67108864 4 3 67108864 33554432 Ns114p1089 Ns114p371 Ns114p1090 Ns114p1091 Ns114p374 Ns114p1090 4326647 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 101084707) qz360 0 3 Ns114p1089 Ns114p371 Ns114p1090 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 101084707) (BSN.cosOddQ 67108864) 0 3 Ns114p1091 Ns114p374 Ns114p1090 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1093 := Ns114p1038 56395 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 61 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 60277761 67108864) BSN.abs_quadSignPos qz734 (BSN.sfrac_eq_quadSignPos_mul Bool.false 4326647 67108864) qz142 rfl rfl (Ns114p1084 rfl rfl) (Ns114p1071 rfl) RS115to132.d27 RS115to132.d29 RS115to132.d31 RS115to132.d33 RS115to132.d17 (Ns114p1088 rfl rfl) (Ns114p1092 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns114p1094 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz139) qz139 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz139) qz139 7) 53414016 67108864 56395 67108864 53414016 67108864 56395 67108864 7169107870875648 417297 262144 56395 33554432 (Ns114p1093 rfl) 

noncomputable def Ns114p1095 := @Enclosure.Real.IsNear.mulLit_tf qz730 (Zeta.RiemannSiegel.correction qz141) 1525371 4194304 1 4194304 13693090468215 35184372088832 10268121042113 197912092999680000 20887043100591582765 147573952589676412928 

noncomputable abbrev qz735 := (@HPow.hPow Real Real Real qz7 qz140 qz9)

noncomputable def Ns114p1096 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz735 1 1 0 1 1525371 4194304 1 4194304 1525371 4194304 1 4194304 

noncomputable def Ns114p1097 := @Enclosure.Real.IsNear.sqrt_image qz140 29971412961 524288000 22449 524288000 31712347 31712372 4194304 (@Enclosure.Real.IsNear.of_eq qz140 (@HMul.hMul Real Real Real qz5 qz139 qz3) Bool.false 29971412961 524288000 22449 524288000 (BSN.t_div_two_pi_mk qz139 359184 1000 qz142) (@Enclosure.Real.IsNear.mulLit_ff qz139 qz3 359184 1000 0 1 1335089 8388608 1 8388608 29971412961 524288000 22449 524288000 (Enclosure.Real.IsNear.const Bool.false 359184 1000) RS115to132.d36 rfl)) 

noncomputable abbrev qz925 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 359184 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz736 := qz925

noncomputable abbrev qz493 := qz736

noncomputable abbrev qz144 := qz493

noncomputable def Ns114p1098 := @Enclosure.Real.IsNear.sqrt_image qz144 63424719 8388608 25 8388608 11533049 11533054 4194304 (@Enclosure.Real.IsNear.recentre' qz144 Bool.false 63424719 8388608 25 8388608 63424719 8388608 25 8388608 (Ns114p1097 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns114p1099 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz144) 23066103 8388608 5 8388608 1525370 1525372 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz144) Bool.false 23066103 8388608 5 8388608 23066103 8388608 5 8388608 (Ns114p1098 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns114p1100 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz144)) Bool.false 3050742 8388608 2 8388608 1525371 4194304 1 4194304 (Ns114p1099 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz145 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz486))

noncomputable abbrev qz737 := (@HMul.hMul Real Real Real qz884 qz924 qz924)

noncomputable abbrev qz494 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz737 qz729) qz642)

noncomputable abbrev qz146 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz494))

noncomputable def Ns114p1101 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz141) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz145) qz146) Bool.false 13693090468215 

noncomputable def Ns114p1102 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz145) qz146 9040641 8388608 191 

noncomputable abbrev qz738 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz145))

noncomputable def Ns114p1103 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz145) (@Neg.neg Real Real.instNeg qz738) Bool.true 9040641 8388608 191 8388608 (BSN.inv_eq_neg_inv_neg qz145) 

noncomputable def Ns114p1104 := @Enclosure.Real.IsNear.recentre' qz738 Bool.false 9040641 8388608 191 8388608 9040641 8388608 

noncomputable def Ns114p1105 := @Enclosure.Real.IsNear.recentre' qz145 Bool.true 7783601 8388608 117954304 6039797760000 7783601 8388608 460759 23592960000 

noncomputable abbrev qz147 := (@HMul.hMul Real Real Real qz339 qz337 qz486)

noncomputable def Ns114p1106 := @Enclosure.Real.IsNear.cos_image qz147 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7389753) qz383) Bool.false 7389753 2097152 79 4194304 Bool.true 7783601 8388608 1 

noncomputable def Ns114p1107 := nat_lit 674651885266512165839708271 

noncomputable def Ns114p1108 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz141 884279719003555 140737488355328 1 500000000000000 4704463 8388608 25 8388608 4160061219702621365965 1180591620717411303424 Ns114p1107 

noncomputable def Ns114p1109 := @Enclosure.Real.IsNear.subLit_ff_p qz144 qz1 63424719 8388608 25 8388608 7 1 0 1 4704463 4704463 8388608 25 

noncomputable def Ns114p1110 := @Ns114p1109 8388608 (@Enclosure.Real.IsNear.recentre' qz144 Bool.false 63424719 8388608 25 8388608 63424719 8388608 25 8388608 (Ns114p1097 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns114p1111 := @Enclosure.Real.IsNear.recentre' qz147 Bool.false 4160061219702621365965 1180591620717411303424 Ns114p1107 Ns114p501 7389753 2097152 79 4194304 (@Ns114p1108 Ns114p501 RS115to132.d35 (Ns114p1110 rfl rfl) rfl) 

noncomputable def Ns114p1112 := nat_lit 1857210197984296522371242502504165416401 

noncomputable def Ns114p1113 := BSN.cos_dyadic_bound_f 6564705757 17179869184 2 1 8388608 2882813 Ns114p1112 Ns114p817 Ns114p1112 Ns114p1112 Ns114p818 Ns114p1112 7783601 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 6564705757) qz454 0 1 Ns114p1112 Ns114p817 Ns114p1112 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 6564705757) qz455 0 1 Ns114p1112 Ns114p818 Ns114p1112 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1114 := @Ns114p1106 1440000 (Ns114p1111 rfl) (Enclosure.sfrac_false_div 7389753 2097152) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7389753) qz383) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 115487525020035549495296) qz384) 226375608064910080 72057594037927936 Bool.false 7783601 8388608 0 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q2 7389753 2097152 226375608064910080 72057594037927936 0 115487525020035549495296 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 7783601 8388608 115487525020035549495296 302231454903657293676544 6564705757 17179869184 2882813 2880000 (Ns114p1113 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p1115 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz145) 7783601 8388608 460759 23592960000 4520225 4520416 4194304 (@Enclosure.Real.IsNear.neg qz145 Bool.true 7783601 8388608 460759 23592960000 (Ns114p1105 (Ns114p1114 rfl rfl) rfl)) 

noncomputable def Ns114p1116 := Ns114p1103 (@Enclosure.Real.IsNear.neg qz738 Bool.false 9040641 8388608 191 8388608 (@Ns114p1104 191 8388608 (Ns114p1115 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p1117 := @Enclosure.Real.IsNear.recentre' qz146 Bool.true 1514615 4194304 

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz339 qz337 qz494)

noncomputable def Ns114p1118 := @Enclosure.Real.IsNear.cos_image qz148 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16276053)) qz357) Bool.true 16276053 8388608 

noncomputable def Ns114p1119 := nat_lit 19215372075264924547436099645 

noncomputable def Ns114p1120 := nat_lit 12007156731959422338670940970356313 

noncomputable def Ns114p1121 := @Enclosure.Real.IsNear.recentre' qz148 Bool.true Ns114p1119 Ns114p517 Ns114p1120 

noncomputable abbrev qz149 := qz494

noncomputable def Ns114p1122 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz149 884279719003555 140737488355328 1 500000000000000 21729970350239 

noncomputable abbrev qz495 := (@HSub.hSub Real Real Real qz634 qz737 qz729)

noncomputable abbrev qz150 := qz495

noncomputable def Ns114p1123 := @Enclosure.Real.IsNear.subLit_tf qz150 qz26 17331923839135 70368744177664 444938975 70368744177664 1 16 

noncomputable abbrev qz496 := qz737

noncomputable abbrev qz151 := qz496

noncomputable def Ns114p1124 := @Enclosure.Real.IsNear.subLit_ff_n qz151 qz141 22131972118369 70368744177664 235223775 70368744177664 4704463 8388608 25 8388608 

noncomputable def Ns114p1125 := @Enclosure.Real.IsNear.mulLit_ff qz141 qz141 4704463 8388608 25 8388608 4704463 8388608 25 8388608 22131972118369 70368744177664 

noncomputable def Ns114p1126 := nat_lit 34633302421400983620843830968028912246428614382246187287682300341705754801410194728999682321 

noncomputable def Ns114p1127 := nat_lit 345612263726894425500773880569402660494833629022521642903229650100324251355551103418641 

noncomputable def Ns114p1128 := nat_lit 208935219904601299604114141513529550153583297931329293094652081318446991129210578306127593745 

noncomputable def Ns114p1129 := BSN.cos_dyadic_bound_t 16276053 8388608 4 3 4194304 1440000 Ns114p1126 Ns114p631 Ns114p1127 Ns114p1128 Ns114p634 Ns114p1127 1514615 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16276053) (BSN.cosEvenQ 8388608) 0 3 Ns114p1126 Ns114p631 Ns114p1127 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16276053) (BSN.cosOddQ 8388608) 0 3 Ns114p1128 Ns114p634 Ns114p1127 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1130 := @Ns114p1117 244674304 6039797760000 1514615 4194304 955759 23592960000 (@Ns114p1118 167 4194304 Bool.true 1514615 4194304 1 1440000 (@Ns114p1121 Ns114p520 16276053 8388608 167 4194304 (@Ns114p1122 70368744177664 444938975 70368744177664 Ns114p1119 Ns114p517 Ns114p1120 Ns114p520 RS115to132.d35 (@Ns114p1123 0 1 347679525603824 21729970350239 70368744177664 444938975 70368744177664 (@Ns114p1124 145390714972358574080 17331923839135 70368744177664 444938975 70368744177664 (@Ns114p1125 235223775 70368744177664 (Ns114p1110 rfl rfl) (Ns114p1110 rfl rfl) rfl) (Ns114p1110 rfl rfl) rfl rfl) qz370 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16276053 8388608) (BSN.cos_neg_of_bound 16276053 8388608 Bool.true 1514615 4194304 1 1440000 (Ns114p1129 rfl rfl)) rfl rfl) 

noncomputable def Ns114p1131 := @Ns114p1095 15739727964133700411 830103483316929822720000 (Ns114p1096 qz28 (@Enclosure.Real.IsNear.of_eq qz735 (@Inv.inv Real Real.instInv (Real.sqrt qz144)) Bool.false 1525371 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz140 (BSN.t_div_two_pi_nonneg qz139 359184 1000 qz142)) Ns114p1100) rfl) (@Ns114p1101 35184372088832 10268121042113 197912092999680000 (BSN.correction_mk qz141 (BSN.cos_two_pi_p_ne_zero_mk qz139 359184 1000 7 qz142 rfl rfl (@BSN.floor_sqrt_eq_dec qz139 359184 1000 7 qz142 rfl rfl rfl))) (@Ns114p1102 8388608 1514615 4194304 955759 23592960000 13693090468215 35184372088832 10268121042113 197912092999680000 Ns114p1116 (Ns114p1130 rfl) rfl)) 

noncomputable def Ns114p1132 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz139) (hardyZApproximantRS₀ qz139) Bool.false 255804369813444816429 147573952589676412928 1410896288553752900411 830103483316929822720000 (@Eq.refl Real (hardyZApproximantRS₀ qz139)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz139) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz139) qz139 7) (@HMul.hMul Real Real Real qz5 qz730 (Zeta.RiemannSiegel.correction qz141))) Bool.false 255804369813444816429 147573952589676412928 1410896288553752900411 830103483316929822720000 (BSN.hardyZApproximantRS₀_eq qz139 7 (@BSN.floor_sqrt_eq_dec qz139 359184 1000 7 qz142 rfl rfl rfl)) (@Ns114p1036 255804369813444816429 147573952589676412928 1410896288553752900411 830103483316929822720000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz139) qz139 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz139) qz139 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz139) qz139 7)) Bool.false 417297 262144 56395 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz139) qz139 7) (Ns114p1094 (Ns114p1093 rfl) rfl rfl)) (Ns114p1131 rfl) rfl rfl)) 

theorem RS115to132.d48 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz139) Bool.false 255804369813444816429 147573952589676412928 1410896288553752900411 830103483316929822720000 := Ns114p1132 

noncomputable def Ns114p1133 := nat_lit 10325856147723824090054656 

noncomputable abbrev qz926 := (Enclosure.sfrac Bool.false 360736 1000)

noncomputable abbrev qz739 := qz926

noncomputable abbrev qz497 := qz739

noncomputable abbrev qz152 := qz497

noncomputable abbrev qz927 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 360736 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz740 := qz927

noncomputable abbrev qz498 := qz740

noncomputable abbrev qz153 := qz498

noncomputable abbrev qz928 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 360736 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz741 := qz928

noncomputable abbrev qz499 := qz741

noncomputable abbrev qz154 := qz499

noncomputable abbrev qz742 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz153 qz9))

noncomputable def Ns114p1134 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 7) (@HMul.hMul Real Real Real qz5 qz742 (Zeta.RiemannSiegel.correction qz154)) 9555327 4194304 56641 33554432 164672335178042699 1152921504606846976 8356986610985603339 415051741658464911360000 Ns114p1133 

noncomputable def Ns114p1135 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 360736 1000 61 96 67108864 33554432 1125899906842624 Bool.false 36894999479 1260 

noncomputable def Ns114p1136 := Ns114p1135 120242927 48 27397080 8 130587807 48 25364760 8 Bool.true 62350472 42017 Bool.true 50677254 Bool.true 92945388 3537118876014220 1 Bool.false 45996271 Bool.true Bool.false 12397349 Bool.false Bool.true 76442616 

noncomputable def Ns114p1137 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 360736 1000 31 19 67108864 33554432 1125899906842624 Bool.false 36894999479 1260 

noncomputable def Ns114p1138 := Ns114p1137 93032624 47 33554424 8 108007536 47 30011992 8 Bool.true 115101626 24744 Bool.false 66937758 Bool.true 64334243 3537118876014220 1 Bool.false 56377529 Bool.false Bool.false 54923196 Bool.false Bool.true 62350472 

noncomputable def Ns114p1139 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 360736 1000 190 97 67108864 33554432 1125899906842624 Bool.false 36894999479 1260 

noncomputable def Ns114p1140 := Ns114p1139 46516304 47 47453136 16 73726608 47 38745320 8 Bool.true 67108848 1319 Bool.false 86166196 Bool.false 73965180 3537118876014220 1 Bool.false 18985333 Bool.true Bool.false 59873739 Bool.true Bool.true 115101626 

noncomputable def Ns114p1141 := nat_lit 374644528164207345424738873240112470098189935369849 

noncomputable def Ns114p1142 := nat_lit 681446511542170320945781102052448660180959232000 

noncomputable def Ns114p1143 := nat_lit 2932181016049930997733338644480000 

noncomputable def Ns114p1144 := nat_lit 6346465195921904602514403891306823680 

noncomputable abbrev qz929 := (@Eq.refl Real (Enclosure.sfrac Bool.false 360736 1000))

noncomputable abbrev qz743 := qz929

noncomputable abbrev qz500 := qz743

noncomputable abbrev qz155 := qz500

noncomputable def Ns114p1145 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz152 360736 1000 520522846784 16000000 721472 4000 2000 Ns114p1143 Ns114p1144 qz155 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns114p1146 := nat_lit 491054075955389851795113735933280216807099512087968481280 

noncomputable abbrev qz744 := (Real.log (Enclosure.sfrac Bool.false 520522846784 16000000))

noncomputable abbrev qz156 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 360736 4000) qz744) (@HMul.hMul Real Real Real qz339 qz343 (@HSub.hSub Real Real Real qz342 qz344 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz345 (@Nat.cast Real Real.instNatCast 721472))))))

noncomputable abbrev qz745 := (Enclosure.sfrac Bool.false 360736 2000)

noncomputable abbrev qz501 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz156 qz745) (@HMul.hMul Real Real Real qz5 qz745 (Real.log Real.pi)))

noncomputable def Ns114p1147 := @Enclosure.Real.IsNear.addLit_ft_p qz501 (Enclosure.sfrac Bool.true Ns114p1143 Ns114p1144) 77374486972483831321 140737488355328000 1800274095828671 96000000000000000000 Ns114p1143 Ns114p1144 0 1 Ns114p1146 

noncomputable def Ns114p1148 := nat_lit 162266060103318411822497792000 

noncomputable abbrev qz502 := (@HSub.hSub Real Real Real qz12 qz156 qz745)

noncomputable abbrev qz503 := (@HMul.hMul Real Real Real qz5 qz745 (Real.log Real.pi))

noncomputable def Ns114p1149 := @Enclosure.Real.IsNear.subLit_ff_p qz502 qz503 106432927661775717913 140737488355328000 24006253788103 3000000000000000000 433004508753 2097152000 11273 1048576000 Ns114p1148 77374486972483831321 140737488355328000 

noncomputable abbrev qz504 := qz745

noncomputable def Ns114p1150 := @Enclosure.Real.IsNear.subLit_ff_p qz156 qz504 131817466961449518617 140737488355328000 24006253788103 3000000000000000000 360736 2000 0 1 212865855323551435826000 106432927661775717913 140737488355328000 24006253788103 3000000000000000000 

noncomputable def Ns114p1151 := nat_lit 593653095088506719662199956708524032 

noncomputable def Ns114p1152 := nat_lit 12560739648611535862890496 

noncomputable def Ns114p1153 := nat_lit 65604893414552299811116550048387025923827594518409130526472055020219006568411051770237091874256592966884313962550733748111179267514495045686411306681447779358149087487590400 

noncomputable def Ns114p1154 := nat_lit 2552383236173216811847196725177591252821000204718519815200211905295970743872236200920786419802257603436143422900592120434303344237966196999601053410381495442276064941834240 

noncomputable def Ns114p1155 := nat_lit 798666049403094584123162535146401013742598273610809803578013883434518131060007941864073268618451907332103442704581976633638796694051350683381625377372713073885839360 

noncomputable def Ns114p1156 := BSN.log_dyadic_bound 258378846784 782666846784 8 7 Ns114p1153 33554432 11520000 Ns114p1154 Ns114p1155 23016320 1041045693568 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 258378846784) (BSN.artanhQ 782666846784) 0 7 Ns114p1154 Ns114p1153 Ns114p1155 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns114p1157 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 360736 4000) qz744 360736 4000 0 1 23396200777239233 2251799813685248 390625063 4500000000000000 263745371361817873609 281474976710656000 4403516335199 562500000000000000 (Enclosure.Real.IsNear.const Bool.false 360736 4000) (BSN.isNear_log_sfrac 520522846784 16000000 23396200777239233 2251799813685248 390625063 4500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 520522846784) qz350)) Bool.false Ns114p1152 Ns114p85 1000000161280000 11520000000000000000000 23396200777239233 2251799813685248 390625063 4500000000000000 (BSN.log_rat_reduce_isNear 520522846784 16000000 14 1041045693568 524288000000 23016320 33554432 24973259072661432 36028797018963968 11520000 1000000000000000 rfl rfl rfl rfl (Ns114p1156 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p1158 := BSN.arctan_dyadic_bound_f 1000 721472 1 0 4194304 1440000 0 1 1 0 1 1 5813 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 721472) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 721472) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz505 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 721472)))

noncomputable def Ns114p1159 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz505 884279719003555 562949953421312 1 2000000000000000 5813 4194304 1 1440000 3705665534456248664064 883499511350691 562949953421312 12500000009 18000000000000000 qz16 (Ns114p1158 rfl) rfl rfl 

noncomputable def Ns114p1160 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 360736 4000) qz744) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz505)) 263745371361817873609 281474976710656000 4403516335199 562500000000000000 883499511350691 2251799813685248 12500000009 72000000000000000 Ns114p1151 131817466961449518617 140737488355328000 24006253788103 3000000000000000000 (Ns114p1157 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz505) 1 4 0 1 883499511350691 562949953421312 12500000009 18000000000000000 883499511350691 2251799813685248 12500000009 72000000000000000 qz353 Ns114p1159 rfl) 

noncomputable def Ns114p1161 := @Ns114p1147 Ns114p1141 Ns114p1142 1800274095828671 96000000000000000000 (@Ns114p1149 1800274095828671 96000000000000000000 (Ns114p1150 (Ns114p1160 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 360736 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz504 (Real.log Real.pi) 360736 2000 0 1 38410761 33554432 1 16777216 433004508753 2097152000 11273 1048576000 (Enclosure.Real.IsNear.const Bool.false 360736 2000) RS115to132.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns114p1143 Ns114p1144) 

noncomputable def Ns114p1162 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns114p1141 Ns114p1142 1800274095828671 96000000000000000000 2305937467 4194304 159 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz354 qz501 (Enclosure.sfrac Bool.true Ns114p1143 Ns114p1144)) Bool.false Ns114p1141 Ns114p1142 1800274095828671 96000000000000000000 Ns114p1145 (Ns114p1161 rfl rfl)) 

noncomputable def Ns114p1163 := nat_lit 139853208975013146471550183811944334700135501941610758435217817336777091405882175390625 

noncomputable def Ns114p1164 := nat_lit 280722508920140045550742670896317762955344240658907464696024913946125464019775390625 

noncomputable def Ns114p1165 := nat_lit 365827710872497061637454040897450647836522423933628040958919766973741512454611775390625 

noncomputable def Ns114p1166 := BSN.sin_dyadic_bound_f 26979547075 17179869184 3 2 8388608 2882813 Ns114p1163 Ns114p98 Ns114p1164 Ns114p1165 Ns114p101 Ns114p1164 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26979547075) qz355 0 2 Ns114p1163 Ns114p98 Ns114p1164 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26979547075) qz356 0 2 Ns114p1165 Ns114p101 Ns114p1164 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1167 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz152) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2305937467) qz366) Bool.false 2305937467 4194304 159 8388608 Bool.true 8388606 8388608 1 1440000 (Ns114p1162 rfl) (Enclosure.sfrac_false_div 2305937467 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2305937467) qz366) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949258423097165080428544) qz380) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 87 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q1 2305937467 4194304 226375608064910080 72057594037927936 87 949258423097165080428544 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388606 8388608 949258423097165080428544 604462909807314587353088 26979547075 17179869184 2882813 2880000 (Ns114p1166 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p1168 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns114p1141 Ns114p1142 1800274095828671 96000000000000000000 36894999479 67108864 1260 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz354 qz501 (Enclosure.sfrac Bool.true Ns114p1143 Ns114p1144)) Bool.false Ns114p1141 Ns114p1142 1800274095828671 96000000000000000000 Ns114p1145 (Ns114p1161 rfl rfl)) 

noncomputable def Ns114p1169 := Ns114p1140 24744 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 190 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 18985333 67108864) BSN.abs_quadSignNeg qz637 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 59873739 67108864) qz155 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) Bool.true 4194303 4194304 927143 47185920000 67108848 67108864 1319 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.true 4194303 4194304 927143 47185920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz152) qz152) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.true 8388606 8388608 237348608 12079595520000 4194303 4194304 927143 47185920000 (Ns114p1167 rfl rfl) rfl)) rfl) (Ns114p1168 rfl) RS115to132.d7 

noncomputable def Ns114p1170 := nat_lit 453330236688494162821671539605284017198595862414128259904696870742837842293296773447406343851549392896 

noncomputable def Ns114p1171 := nat_lit 167510889806460152469065124141741917952605802165585381232833856255928572988716143665545127919616 

noncomputable def Ns114p1172 := nat_lit 2747241233859258393347544962756355599449069004696093265874091356546609276894903788939713674696091238400 

noncomputable def Ns114p1173 := BSN.cos_dyadic_bound_f 86166196 67108864 4 3 67108864 33554432 Ns114p1170 Ns114p371 Ns114p1171 Ns114p1172 Ns114p374 Ns114p1171 18985333 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 86166196) qz360 0 3 Ns114p1170 Ns114p371 Ns114p1171 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 86166196) (BSN.cosOddQ 67108864) 0 3 Ns114p1172 Ns114p374 Ns114p1171 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1174 := nat_lit 1836633442779663856765541305755693609537785428723842298041507840000 

noncomputable def Ns114p1175 := nat_lit 895815448827482260941749713084160803451294034998546457600000000 

noncomputable def Ns114p1176 := nat_lit 4808780077505779891677750110777061288440993075362922657748787200000 

noncomputable def Ns114p1177 := BSN.sin_dyadic_bound_f 73965180 67108864 3 2 67108864 33554432 Ns114p1174 Ns114p107 Ns114p1175 Ns114p1176 Ns114p110 Ns114p1175 59873739 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 73965180) qz359 0 2 Ns114p1174 Ns114p107 Ns114p1175 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 73965180) (BSN.sinOddQ 67108864) 0 2 Ns114p1176 Ns114p110 Ns114p1175 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1178 := nat_lit 1231765732095309645338511636354580248166110234161668016589492814080 

noncomputable def Ns114p1179 := nat_lit 403059625223022945564463267730403535080252940179808918359081216 

noncomputable def Ns114p1180 := nat_lit 3225400535142116557784235630876146663283015918044077495676090286336 

noncomputable def Ns114p1181 := BSN.sin_dyadic_bound_f 66937758 67108864 3 2 67108864 33554432 Ns114p1178 Ns114p107 Ns114p1179 Ns114p1180 Ns114p110 Ns114p1179 56377529 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 66937758) qz359 0 2 Ns114p1178 Ns114p107 Ns114p1179 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 66937758) (BSN.sinOddQ 67108864) 0 2 Ns114p1180 Ns114p110 Ns114p1179 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1182 := nat_lit 1050972607912975171144748775160675314192436360956837940536669722785 

noncomputable def Ns114p1183 := nat_lit 293452329219483756907036709212463656116425283023230599890032801 

noncomputable def Ns114p1184 := nat_lit 2752072193143817712629825875510662786489335304428728423291455887521 

noncomputable def Ns114p1185 := BSN.sin_dyadic_bound_f 64334243 67108864 3 2 67108864 33554432 Ns114p1182 Ns114p107 Ns114p1183 Ns114p1184 Ns114p110 Ns114p1183 54923196 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 64334243) qz359 0 2 Ns114p1182 Ns114p107 Ns114p1183 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 64334243) (BSN.sinOddQ 67108864) 0 2 Ns114p1184 Ns114p110 Ns114p1183 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1186 := Ns114p1138 42017 BSN.abs_quadSignPos (BSN.cos_quad_nat3 31 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 56377529 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 19 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 54923196 67108864) qz155 rfl rfl (Ns114p1169 RS115to132.d9 RS115to132.d11 RS115to132.d13 RS115to132.d17 (Ns114p1173 rfl rfl) (Ns114p1177 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns114p1168 rfl) RS115to132.d19 RS115to132.d21 RS115to132.d23 RS115to132.d25 RS115to132.d17 (Ns114p1181 rfl rfl) (Ns114p1185 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns114p1187 := nat_lit 404576200926121586281584838192583497797356349102494895179550531840 

noncomputable def Ns114p1188 := nat_lit 43501536141708962979960275483761764101048596393962954276577536 

noncomputable def Ns114p1189 := nat_lit 1059533904700374720987897497677411641851198264207610690210946457856 

noncomputable def Ns114p1190 := BSN.sin_dyadic_bound_f 50677254 67108864 3 2 67108864 33554432 Ns114p1187 Ns114p107 Ns114p1188 Ns114p1189 Ns114p110 Ns114p1188 45996271 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 50677254) qz359 0 2 Ns114p1187 Ns114p107 Ns114p1188 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 50677254) (BSN.sinOddQ 67108864) 0 2 Ns114p1189 Ns114p110 Ns114p1188 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1191 := nat_lit 614082388510944089078963897470205653118726061397070857666202036820500446678056035943788217784583847936 

noncomputable def Ns114p1192 := nat_lit 415656079131189889417139776378127107292341985061154917299788653203436703528464274286235516665856 

noncomputable def Ns114p1193 := nat_lit 3720003328650390510730512294022775920881384222160276310185820233267487817871907271197536406921627566080 

noncomputable def Ns114p1194 := BSN.cos_dyadic_bound_f 92945388 67108864 4 3 67108864 33554432 Ns114p1191 Ns114p371 Ns114p1192 Ns114p1193 Ns114p374 Ns114p1192 12397349 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 92945388) qz360 0 3 Ns114p1191 Ns114p371 Ns114p1192 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 92945388) (BSN.cosOddQ 67108864) 0 3 Ns114p1193 Ns114p374 Ns114p1192 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1195 := Ns114p1136 56641 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 61 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 45996271 67108864) BSN.abs_quadSignPos qz734 (BSN.sfrac_eq_quadSignPos_mul Bool.false 12397349 67108864) qz155 rfl rfl (Ns114p1186 rfl rfl) (Ns114p1168 rfl) RS115to132.d27 RS115to132.d29 RS115to132.d31 RS115to132.d33 RS115to132.d17 (Ns114p1190 rfl rfl) (Ns114p1194 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns114p1196 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 7) 76442616 67108864 56641 67108864 76442616 67108864 56641 67108864 10259954241896448 9555327 4194304 56641 33554432 (Ns114p1195 rfl) 

noncomputable def Ns114p1197 := @Enclosure.Real.IsNear.mulLit_tf qz742 (Zeta.RiemannSiegel.correction qz154) 95233 262144 1 4194304 1729152029003 4398046511104 5459028928591 98956046499840000 164672335178042699 1152921504606846976 

noncomputable abbrev qz746 := (@HPow.hPow Real Real Real qz7 qz153 qz9)

noncomputable def Ns114p1198 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz746 1 1 0 1 95233 262144 1 4194304 95233 262144 1 4194304 

noncomputable def Ns114p1199 := @Enclosure.Real.IsNear.sqrt_image qz153 15050458297 262144000 11273 262144000 31780786 31780811 4194304 (@Enclosure.Real.IsNear.of_eq qz153 (@HMul.hMul Real Real Real qz5 qz152 qz3) Bool.false 15050458297 262144000 11273 262144000 (BSN.t_div_two_pi_mk qz152 360736 1000 qz155) (@Enclosure.Real.IsNear.mulLit_ff qz152 qz3 360736 1000 0 1 1335089 8388608 1 8388608 15050458297 262144000 11273 262144000 (Enclosure.Real.IsNear.const Bool.false 360736 1000) RS115to132.d36 rfl)) 

noncomputable abbrev qz930 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 360736 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz747 := qz930

noncomputable abbrev qz506 := qz747

noncomputable abbrev qz157 := qz506

noncomputable def Ns114p1200 := @Enclosure.Real.IsNear.sqrt_image qz157 63561597 8388608 25 8388608 11545487 11545492 4194304 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 63561597 8388608 25 8388608 63561597 8388608 25 8388608 (Ns114p1199 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns114p1201 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz157) 23090979 8388608 5 8388608 1523727 1523729 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz157) Bool.false 23090979 8388608 5 8388608 23090979 8388608 5 8388608 (Ns114p1200 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns114p1202 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz157)) Bool.false 3047456 8388608 2 8388608 95233 262144 1 4194304 (Ns114p1201 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz158 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz499))

noncomputable abbrev qz748 := (@HMul.hMul Real Real Real qz884 qz928 qz928)

noncomputable abbrev qz507 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz748 qz741) qz642)

noncomputable abbrev qz159 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz507))

noncomputable def Ns114p1203 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz154) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz158) qz159) Bool.false 1729152029003 

noncomputable def Ns114p1204 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz158) qz159 4740169 4194304 105 

noncomputable abbrev qz749 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz158))

noncomputable def Ns114p1205 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz158) (@Neg.neg Real Real.instNeg qz749) Bool.true 4740169 4194304 105 4194304 (BSN.inv_eq_neg_inv_neg qz158) 

noncomputable def Ns114p1206 := @Enclosure.Real.IsNear.recentre' qz749 Bool.false 9480338 8388608 210 8388608 4740169 4194304 

noncomputable def Ns114p1207 := @Enclosure.Real.IsNear.recentre' qz158 Bool.true 7422599 8388608 117954304 6039797760000 7422599 8388608 460759 23592960000 

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz339 qz337 qz499)

noncomputable def Ns114p1208 := @Enclosure.Real.IsNear.cos_image qz160 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15209521) qz366) Bool.false 15209521 4194304 79 4194304 Bool.true 7422599 8388608 1 

noncomputable def Ns114p1209 := nat_lit 674651885267687938906792047 

noncomputable def Ns114p1210 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz154 884279719003555 140737488355328 1 500000000000000 4841341 8388608 25 8388608 4281099659080389967255 1180591620717411303424 Ns114p1209 

noncomputable def Ns114p1211 := @Enclosure.Real.IsNear.subLit_ff_p qz157 qz1 63561597 8388608 25 8388608 7 1 0 1 4841341 4841341 8388608 25 

noncomputable def Ns114p1212 := @Ns114p1211 8388608 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 63561597 8388608 25 8388608 63561597 8388608 25 8388608 (Ns114p1199 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns114p1213 := @Enclosure.Real.IsNear.recentre' qz160 Bool.false 4281099659080389967255 1180591620717411303424 Ns114p1209 Ns114p501 15209521 4194304 79 4194304 (@Ns114p1210 Ns114p501 RS115to132.d35 (Ns114p1212 rfl rfl) rfl) 

noncomputable def Ns114p1214 := nat_lit 4805686914889139577990718896815714262481 

noncomputable def Ns114p1215 := BSN.cos_dyadic_bound_f 8326047197 17179869184 2 1 8388608 2882813 Ns114p1214 Ns114p817 Ns114p1214 Ns114p1214 Ns114p818 Ns114p1214 7422599 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 8326047197) qz454 0 1 Ns114p1214 Ns114p817 Ns114p1214 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 8326047197) qz455 0 1 Ns114p1214 Ns114p818 Ns114p1214 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1216 := @Ns114p1208 1440000 (Ns114p1213 rfl) (Enclosure.sfrac_false_div 15209521 4194304) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15209521) qz366) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 292946742640510261788672) qz380) 226375608064910080 72057594037927936 Bool.false 7422599 8388608 0 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q2 15209521 4194304 226375608064910080 72057594037927936 0 292946742640510261788672 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 7422599 8388608 292946742640510261788672 604462909807314587353088 8326047197 17179869184 2882813 2880000 (Ns114p1215 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p1217 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz158) 7422599 8388608 460759 23592960000 4740064 4740274 4194304 (@Enclosure.Real.IsNear.neg qz158 Bool.true 7422599 8388608 460759 23592960000 (Ns114p1207 (Ns114p1216 rfl rfl) rfl)) 

noncomputable def Ns114p1218 := Ns114p1205 (@Enclosure.Real.IsNear.neg qz749 Bool.false 4740169 4194304 105 4194304 (@Ns114p1206 105 4194304 (Ns114p1217 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p1219 := @Enclosure.Real.IsNear.recentre' qz159 Bool.true 1459148 4194304 

noncomputable abbrev qz161 := (@HMul.hMul Real Real Real qz339 qz337 qz507)

noncomputable def Ns114p1220 := @Enclosure.Real.IsNear.cos_image qz161 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16157413)) qz357) Bool.true 16157413 8388608 

noncomputable def Ns114p1221 := nat_lit 19075306877370728233097716805 

noncomputable def Ns114p1222 := nat_lit 12191846733450018281471434786355517 

noncomputable def Ns114p1223 := @Enclosure.Real.IsNear.recentre' qz161 Bool.true Ns114p1221 Ns114p517 Ns114p1222 

noncomputable abbrev qz162 := qz507

noncomputable def Ns114p1224 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz162 884279719003555 140737488355328 1 500000000000000 21571575676151 

noncomputable abbrev qz508 := (@HSub.hSub Real Real Real qz634 qz748 qz741)

noncomputable abbrev qz163 := qz508

noncomputable def Ns114p1225 := @Enclosure.Real.IsNear.subLit_tf qz163 qz26 17173529165047 70368744177664 451782875 70368744177664 1 16 

noncomputable abbrev qz509 := qz748

noncomputable abbrev qz164 := qz509

noncomputable def Ns114p1226 := @Enclosure.Real.IsNear.subLit_ff_n qz164 qz154 23438582678281 70368744177664 242067675 70368744177664 4841341 8388608 25 8388608 

noncomputable def Ns114p1227 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz154 4841341 8388608 25 8388608 4841341 8388608 25 8388608 23438582678281 70368744177664 

noncomputable def Ns114p1228 := nat_lit 33626355186656622145213941367681352789234474788123407882466305960310767096670374242780068561 

noncomputable def Ns114p1229 := nat_lit 316564283314625701707032213702803251337758692643274779666577600917199282104971548048081 

noncomputable def Ns114p1230 := nat_lit 202893163987003327912036370920889087021839193545961366818706865999743549690061617692287843025 

noncomputable def Ns114p1231 := BSN.cos_dyadic_bound_t 16157413 8388608 4 3 4194304 1440000 Ns114p1228 Ns114p631 Ns114p1229 Ns114p1230 Ns114p634 Ns114p1229 1459148 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16157413) (BSN.cosEvenQ 8388608) 0 3 Ns114p1228 Ns114p631 Ns114p1229 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16157413) (BSN.cosOddQ 8388608) 0 3 Ns114p1230 Ns114p634 Ns114p1229 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1232 := @Ns114p1219 496548608 12079595520000 364787 1048576 1939643 47185920000 (@Ns114p1220 339 8388608 Bool.true 1459148 4194304 1 1440000 (@Ns114p1223 Ns114p520 16157413 8388608 339 8388608 (@Ns114p1224 70368744177664 451782875 70368744177664 Ns114p1221 Ns114p517 Ns114p1222 Ns114p520 RS115to132.d35 (@Ns114p1225 0 1 345145210818416 21571575676151 70368744177664 451782875 70368744177664 (@Ns114p1226 144062004142146584576 17173529165047 70368744177664 451782875 70368744177664 (@Ns114p1227 242067675 70368744177664 (Ns114p1212 rfl rfl) (Ns114p1212 rfl rfl) rfl) (Ns114p1212 rfl rfl) rfl rfl) qz370 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16157413 8388608) (BSN.cos_neg_of_bound 16157413 8388608 Bool.true 1459148 4194304 1 1440000 (Ns114p1231 rfl rfl)) rfl rfl) 

noncomputable def Ns114p1233 := @Ns114p1197 8356986610985603339 415051741658464911360000 (Ns114p1198 qz28 (@Enclosure.Real.IsNear.of_eq qz746 (@Inv.inv Real Real.instInv (Real.sqrt qz157)) Bool.false 95233 262144 1 4194304 (BSN.rpow_neg_quarter_mk qz153 (BSN.t_div_two_pi_nonneg qz152 360736 1000 qz155)) Ns114p1202) rfl) (@Ns114p1203 4398046511104 5459028928591 98956046499840000 (BSN.correction_mk qz154 (BSN.cos_two_pi_p_ne_zero_mk qz152 360736 1000 7 qz155 rfl rfl (@BSN.floor_sqrt_eq_dec qz152 360736 1000 7 qz155 rfl rfl rfl))) (@Ns114p1204 4194304 364787 1048576 1939643 47185920000 1729152029003 4398046511104 5459028928591 98956046499840000 Ns114p1218 (Ns114p1232 rfl) rfl)) 

noncomputable def Ns114p1234 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (hardyZApproximantRS₀ qz152) Bool.true 2461875950747447989 1152921504606846976 708978165335665283339 415051741658464911360000 (@Eq.refl Real (hardyZApproximantRS₀ qz152)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 7) (@HMul.hMul Real Real Real qz5 qz742 (Zeta.RiemannSiegel.correction qz154))) Bool.true 2461875950747447989 1152921504606846976 708978165335665283339 415051741658464911360000 (BSN.hardyZApproximantRS₀_eq qz152 7 (@BSN.floor_sqrt_eq_dec qz152 360736 1000 7 qz155 rfl rfl rfl)) (@Ns114p1134 2461875950747447989 1152921504606846976 708978165335665283339 415051741658464911360000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 7)) Bool.true 9555327 4194304 56641 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz152) qz152 7) (Ns114p1196 (Ns114p1195 rfl) rfl rfl)) (Ns114p1233 rfl) rfl rfl)) 

theorem RS115to132.d49 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz152) Bool.true 2461875950747447989 1152921504606846976 708978165335665283339 415051741658464911360000 := Ns114p1234 

noncomputable def Ns114p1235 := nat_lit 4929994539399704253971824640 

noncomputable abbrev qz931 := (Enclosure.sfrac Bool.false 362287 1000)

noncomputable abbrev qz750 := qz931

noncomputable abbrev qz510 := qz750

noncomputable abbrev qz165 := qz510

noncomputable abbrev qz932 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 362287 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz751 := qz932

noncomputable abbrev qz511 := qz751

noncomputable abbrev qz166 := qz511

noncomputable abbrev qz933 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 362287 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz752 := qz933

noncomputable abbrev qz512 := qz752

noncomputable abbrev qz167 := qz512

noncomputable abbrev qz753 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz166 qz9))

noncomputable def Ns114p1236 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz165) qz165 7) (@HMul.hMul Real Real Real qz5 qz753 (Zeta.RiemannSiegel.correction qz167)) 64390085 16777216 56877 33554432 10659984581594889075 73786976294838206464 1200197251090705141 55340232221128654848000 Ns114p1235 

noncomputable def Ns114p1237 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz165) qz165 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 362287 1000 61 96 67108864 33554432 1125899906842624 Bool.false 37105899140 1265 

noncomputable def Ns114p1238 := Ns114p1237 120242927 48 27397080 8 130587807 48 25364760 8 Bool.false 131488606 42191 Bool.true 26274372 Bool.true 84587416 3537118876014220 1 Bool.false 25608245 Bool.true Bool.false 20494225 Bool.false Bool.false 128780170 

noncomputable def Ns114p1239 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz165) qz165 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 362287 1000 32 19 67108864 33554432 1125899906842624 Bool.false 37105899140 1265 

noncomputable def Ns114p1240 := Ns114p1239 93032624 47 33554424 8 108007536 47 30011992 8 Bool.false 91619473 24844 Bool.false 28129462 Bool.true 20954270 3537118876014220 1 Bool.false 61299280 Bool.false Bool.false 20615434 Bool.false Bool.false 131488606 

noncomputable def Ns114p1241 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz165) qz165 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 362287 1000 192 98 67108864 33554432 1125899906842624 Bool.false 37105899140 1265 

noncomputable def Ns114p1242 := Ns114p1241 46516304 47 47453136 16 73726608 47 38745320 8 Bool.false 67108840 1319 Bool.false 14090355 Bool.false 65100514 3537118876014220 1 Bool.false 65635066 Bool.false Bool.false 37932554 Bool.true Bool.false 91619473 

noncomputable def Ns114p1243 := nat_lit 202695605046854965541163733953548185955449711132368557983 

noncomputable def Ns114p1244 := nat_lit 366590545102306922272032974415208278866404891951104000 

noncomputable def Ns114p1245 := nat_lit 2995760466216227255631270499360000 

noncomputable def Ns114p1246 := nat_lit 6511956220519488920786574482505817920 

noncomputable abbrev qz754 := (@Eq.refl Real qz931)

noncomputable abbrev qz513 := qz754

noncomputable abbrev qz168 := qz513

noncomputable def Ns114p1247 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz165 362287 1000 525008481476 16000000 724574 4000 2000 Ns114p1245 Ns114p1246 qz168 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns114p1248 := nat_lit 64862593614993588973172394865135419505743907562357938554560 

noncomputable abbrev qz755 := (Real.log (Enclosure.sfrac Bool.false 525008481476 16000000))

noncomputable abbrev qz169 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 362287 4000) qz755) (@HMul.hMul Real Real Real qz339 qz343 (@HSub.hSub Real Real Real qz342 qz344 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz345 (@Nat.cast Real Real.instNatCast 724574))))))

noncomputable abbrev qz756 := (Enclosure.sfrac Bool.false 362287 2000)

noncomputable abbrev qz514 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz169 qz756) (@HMul.hMul Real Real Real qz5 qz756 (Real.log Real.pi)))

noncomputable def Ns114p1249 := @Enclosure.Real.IsNear.addLit_ft_p qz514 (Enclosure.sfrac Bool.true Ns114p1245 Ns114p1246) 9960547243458291002743 18014398509481984000 3856944643496391 204800000000000000000 Ns114p1245 Ns114p1246 0 1 Ns114p1248 

noncomputable def Ns114p1250 := nat_lit 133688202065363468115100722790400 

noncomputable abbrev qz515 := (@HSub.hSub Real Real Real qz12 qz169 qz756)

noncomputable abbrev qz516 := (@HMul.hMul Real Real Real qz5 qz756 (Real.log Real.pi))

noncomputable def Ns114p1251 := @Enclosure.Real.IsNear.subLit_ff_p qz515 qz516 2739203943644305390667 3602879701896396800 6428594836961 800000000000000000 13915719370407 67108864000 362287 33554432000 Ns114p1250 9960547243458291002743 18014398509481984000 

noncomputable def Ns114p1252 := nat_lit 27392039436443053906670000 

noncomputable abbrev qz517 := qz756

noncomputable def Ns114p1253 := @Enclosure.Real.IsNear.subLit_ff_p qz169 qz517 16959210914623876722039 18014398509481984000 6428594836961 800000000000000000 362287 2000 0 1 Ns114p1252 2739203943644305390667 3602879701896396800 6428594836961 800000000000000000 

noncomputable def Ns114p1254 := nat_lit 38188747977798869928846655454730780672 

noncomputable def Ns114p1255 := nat_lit 12571113021517853026680832 

noncomputable def Ns114p1256 := BSN.log_dyadic_bound 720481476 1049296481476 1 0 1 33554432 11520000 0 1 46079 1050016962952 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 720481476) (BSN.artanhQ 1049296481476) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns114p1257 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 362287 4000) qz755 362287 4000 0 1 46831045379928697 4503599627370496 156250027 1800000000000000 16966278937558227850039 18014398509481984000 56607353531749 7200000000000000000 (Enclosure.Real.IsNear.const Bool.false 362287 4000) (BSN.isNear_log_sfrac 525008481476 16000000 46831045379928697 4503599627370496 156250027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 525008481476) qz350)) Bool.false Ns114p1255 Ns114p85 1000000172800000 11520000000000000000000 46831045379928697 4503599627370496 156250027 1800000000000000 (BSN.log_rat_reduce_isNear 525008481476 16000000 15 1050016962952 1048576000000 46079 33554432 24973259072661432 36028797018963968 11520000 1000000000000000 rfl rfl rfl rfl (Ns114p1256 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p1258 := BSN.arctan_dyadic_bound_f 1000 724574 1 0 4194304 1440000 0 1 1 0 1 1 5788 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 724574) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 724574) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz518 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 724574)))

noncomputable def Ns114p1259 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz518 884279719003555 562949953421312 1 2000000000000000 5788 4194304 1 1440000 3705679608205084196864 883502866793891 562949953421312 12500000009 18000000000000000 qz16 (Ns114p1258 rfl) rfl rfl 

noncomputable def Ns114p1260 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 362287 4000) qz755) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz518)) 16966278937558227850039 18014398509481984000 56607353531749 7200000000000000000 883502866793891 2251799813685248 12500000009 72000000000000000 Ns114p1254 16959210914623876722039 18014398509481984000 6428594836961 800000000000000000 (Ns114p1257 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz518) 1 4 0 1 883502866793891 562949953421312 12500000009 18000000000000000 883502866793891 2251799813685248 12500000009 72000000000000000 qz353 Ns114p1259 rfl) 

noncomputable def Ns114p1261 := @Ns114p1249 Ns114p1243 Ns114p1244 3856944643496391 204800000000000000000 (@Ns114p1251 3856944643496391 204800000000000000000 (Ns114p1253 (Ns114p1260 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 362287 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz517 (Real.log Real.pi) 362287 2000 0 1 38410761 33554432 1 16777216 13915719370407 67108864000 362287 33554432000 (Enclosure.Real.IsNear.const Bool.false 362287 2000) RS115to132.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns114p1245 Ns114p1246) 

noncomputable def Ns114p1262 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz165) Bool.false Ns114p1243 Ns114p1244 3856944643496391 204800000000000000000 289889837 524288 159 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz165) (@HAdd.hAdd Real Real Real qz354 qz514 (Enclosure.sfrac Bool.true Ns114p1245 Ns114p1246)) Bool.false Ns114p1243 Ns114p1244 3856944643496391 204800000000000000000 Ns114p1247 (Ns114p1261 rfl rfl)) 

noncomputable def Ns114p1263 := nat_lit 140230956023169908053757838801944139049314446394564309905196465848619221706337961172225 

noncomputable def Ns114p1264 := nat_lit 282237979843073488320597413971026017979799616998923073222378377109395234261893438721 

noncomputable def Ns114p1265 := nat_lit 366814594759984783064465753430091083957189588796336840966487845564397035994461118455041 

noncomputable def Ns114p1266 := BSN.sin_dyadic_bound_f 26997710241 17179869184 3 2 8388608 2882813 Ns114p1263 Ns114p98 Ns114p1264 Ns114p1265 Ns114p101 Ns114p1264 8388605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26997710241) qz355 0 2 Ns114p1263 Ns114p98 Ns114p1264 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26997710241) qz356 0 2 Ns114p1265 Ns114p101 Ns114p1264 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1267 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz165) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 289889837) (@Nat.cast Real Real.instNatCast 524288)) Bool.false 289889837 524288 159 8388608 Bool.false 8388605 8388608 1 1440000 (Ns114p1262 rfl) (Enclosure.sfrac_false_div 289889837 524288) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 289889837) (@Nat.cast Real Real.instNatCast 524288)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 118737185335615185485824) (@Nat.cast Real Real.instNatCast 75557863725914323419136)) 226375608064910080 72057594037927936 Bool.false 8388605 8388608 87 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q3 289889837 524288 226375608064910080 72057594037927936 87 118737185335615185485824 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388605 8388608 118737185335615185485824 75557863725914323419136 26997710241 17179869184 2882813 2880000 (Ns114p1266 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p1268 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz165) Bool.false Ns114p1243 Ns114p1244 3856944643496391 204800000000000000000 37105899140 67108864 1265 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz165) (@HAdd.hAdd Real Real Real qz354 qz514 (Enclosure.sfrac Bool.true Ns114p1245 Ns114p1246)) Bool.false Ns114p1243 Ns114p1244 3856944643496391 204800000000000000000 Ns114p1247 (Ns114p1261 rfl rfl)) 

noncomputable def Ns114p1269 := Ns114p1242 24844 BSN.abs_quadSignPos (BSN.cos_quad_nat0 192 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 65635066 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 98 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 37932554 67108864) qz168 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz165) qz165 1) Bool.false 8388605 8388608 927143 47185920000 67108840 67108864 1319 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz165) qz165 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz165)) Bool.false 8388605 8388608 927143 47185920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz165) qz165) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz165)) Bool.false 8388605 8388608 237348608 12079595520000 8388605 8388608 927143 47185920000 (Ns114p1267 rfl rfl) rfl)) rfl) (Ns114p1268 rfl) RS115to132.d7 

noncomputable def Ns114p1270 := nat_lit 39417378750248724313877300625 

noncomputable def Ns114p1271 := BSN.cos_dyadic_bound_f 14090355 67108864 2 1 67108864 33554432 Ns114p1270 Ns114p227 Ns114p1270 Ns114p1270 Ns114p228 Ns114p1270 65635066 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 14090355) qz360 0 1 Ns114p1270 Ns114p227 Ns114p1270 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 14090355) (BSN.cosOddQ 67108864) 0 1 Ns114p1270 Ns114p228 Ns114p1270 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1272 := nat_lit 612343857325999376315169239919722142684632566285694593380762747136 

noncomputable def Ns114p1273 := nat_lit 322608154208300506694311926352966642965197105020340351565005056 

noncomputable def Ns114p1274 := nat_lit 1836386355669581527932119095906460494767967304647043099439158231296 

noncomputable def Ns114p1275 := BSN.cos_dyadic_bound_f 65100514 67108864 3 2 67108864 33554432 Ns114p1272 Ns114p113 Ns114p1273 Ns114p1274 Ns114p116 Ns114p1273 37932554 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 65100514) qz360 0 2 Ns114p1272 Ns114p113 Ns114p1273 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 65100514) (BSN.cosOddQ 67108864) 0 2 Ns114p1274 Ns114p116 Ns114p1273 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1276 := nat_lit 21334502237474406829928378191374514217465275098396788417152082176 

noncomputable def Ns114p1277 := nat_lit 392004820807884742873251591929274292297371035109529346826496 

noncomputable def Ns114p1278 := nat_lit 64002722702781604720299388070939684103811230553120146192762593536 

noncomputable def Ns114p1279 := BSN.cos_dyadic_bound_f 28129462 67108864 3 2 67108864 33554432 Ns114p1276 Ns114p113 Ns114p1277 Ns114p1278 Ns114p116 Ns114p1277 61299280 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 28129462) qz360 0 2 Ns114p1276 Ns114p113 Ns114p1277 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 28129462) (BSN.cosOddQ 67108864) 0 2 Ns114p1278 Ns114p116 Ns114p1277 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1280 := nat_lit 192792503253531891614042410000 

noncomputable def Ns114p1281 := BSN.sin_dyadic_bound_f 20954270 67108864 2 1 67108864 33554432 Ns114p1280 Ns114p231 Ns114p1280 Ns114p1280 Ns114p232 Ns114p1280 20615434 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 20954270) qz359 0 1 Ns114p1280 Ns114p231 Ns114p1280 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 20954270) (BSN.sinOddQ 67108864) 0 1 Ns114p1280 Ns114p232 Ns114p1280 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1282 := Ns114p1240 42191 BSN.abs_quadSignPos (BSN.cos_quad_nat0 32 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 61299280 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 19 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 20615434 67108864) qz168 rfl rfl (Ns114p1269 RS115to132.d9 RS115to132.d11 RS115to132.d13 RS115to132.d17 (Ns114p1271 rfl rfl) (Ns114p1275 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns114p1268 rfl) RS115to132.d19 RS115to132.d21 RS115to132.d23 RS115to132.d25 RS115to132.d17 (Ns114p1279 rfl rfl) (Ns114p1281 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns114p1283 := nat_lit 476572938503451447647263539456 

noncomputable def Ns114p1284 := BSN.sin_dyadic_bound_f 26274372 67108864 2 1 67108864 33554432 Ns114p1283 Ns114p231 Ns114p1283 Ns114p1283 Ns114p232 Ns114p1283 25608245 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 26274372) qz359 0 1 Ns114p1283 Ns114p231 Ns114p1283 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 26274372) (BSN.sinOddQ 67108864) 0 1 Ns114p1283 Ns114p232 Ns114p1283 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1285 := nat_lit 420959193867251039701716428345043439215803599547373920294855073012922765304299234163393989836103745536 

noncomputable def Ns114p1286 := nat_lit 134174225960344323905977510111915513464472954684452537803725423416775156240030182876628916371456 

noncomputable def Ns114p1287 := nat_lit 2551264311810729708427012070388199274964714287607415805644523876454326585594401123677969552585816801280 

noncomputable def Ns114p1288 := BSN.cos_dyadic_bound_f 84587416 67108864 4 3 67108864 33554432 Ns114p1285 Ns114p371 Ns114p1286 Ns114p1287 Ns114p374 Ns114p1286 20494225 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 84587416) qz360 0 3 Ns114p1285 Ns114p371 Ns114p1286 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 84587416) (BSN.cosOddQ 67108864) 0 3 Ns114p1287 Ns114p374 Ns114p1286 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1289 := Ns114p1238 56877 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 61 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 25608245 67108864) BSN.abs_quadSignPos qz734 (BSN.sfrac_eq_quadSignPos_mul Bool.false 20494225 67108864) qz168 rfl rfl (Ns114p1282 rfl rfl) (Ns114p1268 rfl) RS115to132.d27 RS115to132.d29 RS115to132.d31 RS115to132.d33 RS115to132.d17 (Ns114p1284 rfl rfl) (Ns114p1288 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns114p1290 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz165) qz165 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz165) qz165 7) 128780170 67108864 56877 67108864 128780170 67108864 56877 67108864 17284581828853760 64390085 16777216 56877 33554432 (Ns114p1289 rfl) 

noncomputable def Ns114p1291 := @Enclosure.Real.IsNear.mulLit_tf qz753 (Zeta.RiemannSiegel.correction qz167) 3044189 8388608 1 8388608 3501748604175 8796093022208 11801867882467 197912092999680000 10659984581594889075 73786976294838206464 

noncomputable abbrev qz757 := (@HPow.hPow Real Real Real qz7 qz166 qz9)

noncomputable def Ns114p1292 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz757 1 1 0 1 3044189 8388608 1 8388608 3044189 8388608 1 8388608 

noncomputable def Ns114p1293 := @Enclosure.Real.IsNear.sqrt_image qz166 483685388543 8388608000 362287 8388608000 31849034 31849059 4194304 (@Enclosure.Real.IsNear.of_eq qz166 (@HMul.hMul Real Real Real qz5 qz165 qz3) Bool.false 483685388543 8388608000 362287 8388608000 (BSN.t_div_two_pi_mk qz165 362287 1000 qz168) (@Enclosure.Real.IsNear.mulLit_ff qz165 qz3 362287 1000 0 1 1335089 8388608 1 8388608 483685388543 8388608000 362287 8388608000 (Enclosure.Real.IsNear.const Bool.false 362287 1000) RS115to132.d36 rfl)) 

noncomputable abbrev qz934 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 362287 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz758 := qz934

noncomputable abbrev qz519 := qz758

noncomputable abbrev qz170 := qz519

noncomputable def Ns114p1294 := @Enclosure.Real.IsNear.sqrt_image qz170 63698093 8388608 25 8388608 11557877 11557882 4194304 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 63698093 8388608 25 8388608 63698093 8388608 25 8388608 (Ns114p1293 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns114p1295 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz170) 23115759 8388608 5 8388608 1522094 1522095 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz170) Bool.false 23115759 8388608 5 8388608 23115759 8388608 5 8388608 (Ns114p1294 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns114p1296 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz170)) Bool.false 3044189 8388608 1 8388608 3044189 8388608 1 8388608 (Ns114p1295 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz171 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz512))

noncomputable abbrev qz759 := (@HMul.hMul Real Real Real qz884 qz933 qz933)

noncomputable abbrev qz520 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz759 qz752) qz642)

noncomputable abbrev qz172 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz520))

noncomputable def Ns114p1297 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz167) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz171) qz172) Bool.false 3501748604175 

noncomputable def Ns114p1298 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz171) qz172 2518575 2097152 119 

noncomputable abbrev qz760 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz171))

noncomputable def Ns114p1299 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz171) (@Neg.neg Real Real.instNeg qz760) Bool.true 2518575 2097152 119 4194304 (BSN.inv_eq_neg_inv_neg qz171) 

noncomputable def Ns114p1300 := @Enclosure.Real.IsNear.recentre' qz760 Bool.false 10074300 8388608 238 8388608 2518575 2097152 

noncomputable def Ns114p1301 := @Enclosure.Real.IsNear.recentre' qz171 Bool.true 6984976 8388608 117954304 6039797760000 436561 524288 460759 23592960000 

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz339 qz337 qz512)

noncomputable def Ns114p1302 := @Enclosure.Real.IsNear.cos_image qz173 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 244349) (@Nat.cast Real Real.instNatCast 65536)) Bool.false 244349 65536 79 4194304 Bool.true 6984976 8388608 1 

noncomputable def Ns114p1303 := nat_lit 674651885268860430618861679 

noncomputable def Ns114p1304 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz167 884279719003555 140737488355328 1 500000000000000 4977837 8388608 25 8388608 4401800303605499210535 1180591620717411303424 Ns114p1303 

noncomputable def Ns114p1305 := @Enclosure.Real.IsNear.subLit_ff_p qz170 qz1 63698093 8388608 25 8388608 7 1 0 1 4977837 4977837 8388608 25 

noncomputable def Ns114p1306 := @Ns114p1305 8388608 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 63698093 8388608 25 8388608 63698093 8388608 25 8388608 (Ns114p1293 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns114p1307 := @Enclosure.Real.IsNear.recentre' qz173 Bool.false 4401800303605499210535 1180591620717411303424 Ns114p1303 Ns114p501 244349 65536 79 4194304 (@Ns114p1304 Ns114p501 RS115to132.d35 (Ns114p1306 rfl rfl) rfl) 

noncomputable def Ns114p1308 := nat_lit 1512473253782079032844424976492311628306101908824912021623026320252358936320026608801 

noncomputable def Ns114p1309 := nat_lit 305970350525552328669815250324704227796179077150711974597160454533877424919820338462720 

noncomputable def Ns114p1310 := nat_lit 106791501310172781001591979636082470177451710121999190510821227267082758630671521 

noncomputable def Ns114p1311 := nat_lit 4537206178343616752971271745517662719977950823054492066488057318302542643442818483361 

noncomputable def Ns114p1312 := nat_lit 13768665773649854790141686264611690250828058471782038856872220454024484121391915230822400 

noncomputable def Ns114p1313 := BSN.cos_dyadic_bound_f 10082473437 17179869184 3 2 8388608 2882813 Ns114p1308 Ns114p1309 Ns114p1310 Ns114p1311 Ns114p1312 Ns114p1310 6984976 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 10082473437) qz454 0 2 Ns114p1308 Ns114p1309 Ns114p1310 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 10082473437) qz455 0 2 Ns114p1311 Ns114p1312 Ns114p1310 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1314 := @Ns114p1302 1440000 (Ns114p1307 rfl) (Enclosure.sfrac_false_div 244349 65536) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 244349) (@Nat.cast Real Real.instNatCast 65536)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5542898390863412461568) (@Nat.cast Real Real.instNatCast 9444732965739290427392)) 226375608064910080 72057594037927936 Bool.false 6984976 8388608 0 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q2 244349 65536 226375608064910080 72057594037927936 0 5542898390863412461568 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 6984976 8388608 5542898390863412461568 9444732965739290427392 10082473437 17179869184 2882813 2880000 (Ns114p1313 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p1315 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz171) 436561 524288 460759 23592960000 5037031 5037269 4194304 (@Enclosure.Real.IsNear.neg qz171 Bool.true 436561 524288 460759 23592960000 (Ns114p1301 (Ns114p1314 rfl rfl) rfl)) 

noncomputable def Ns114p1316 := Ns114p1299 (@Enclosure.Real.IsNear.neg qz760 Bool.false 2518575 2097152 119 4194304 (@Ns114p1300 119 4194304 (Ns114p1315 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p1317 := @Enclosure.Real.IsNear.recentre' qz172 Bool.true 1390369 4194304 

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz339 qz337 qz520)

noncomputable def Ns114p1318 := @Enclosure.Real.IsNear.cos_image qz174 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16011155)) qz357) Bool.true 16011155 8388608 

noncomputable def Ns114p1319 := nat_lit 18902636156332442702938647205 

noncomputable def Ns114p1320 := nat_lit 12376021300899984751425336498886877 

noncomputable def Ns114p1321 := @Enclosure.Real.IsNear.recentre' qz174 Bool.true Ns114p1319 Ns114p517 Ns114p1320 

noncomputable abbrev qz175 := qz520

noncomputable def Ns114p1322 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz175 884279719003555 140737488355328 1 500000000000000 21376308593431 

noncomputable abbrev qz521 := (@HSub.hSub Real Real Real qz634 qz759 qz752)

noncomputable abbrev qz176 := qz521

noncomputable def Ns114p1323 := @Enclosure.Real.IsNear.subLit_tf qz176 qz26 16978262082327 70368744177664 458607675 70368744177664 1 16 

noncomputable abbrev qz522 := qz759

noncomputable abbrev qz177 := qz522

noncomputable def Ns114p1324 := @Enclosure.Real.IsNear.subLit_ff_n qz177 qz167 24778861198569 70368744177664 248892475 70368744177664 4977837 8388608 25 8388608 

noncomputable def Ns114p1325 := @Enclosure.Real.IsNear.mulLit_ff qz167 qz167 4977837 8388608 25 8388608 4977837 8388608 25 8388608 24778861198569 70368744177664 

noncomputable def Ns114p1326 := nat_lit 32415802535673605853392147868022933834659349014904118697190293464999539115213609262095640625 

noncomputable def Ns114p1327 := nat_lit 283838917652013936770826288065908258624764911325613963750124210701871215314492431640625 

noncomputable def Ns114p1328 := nat_lit 195626849255891376300068058789940427464089361400168264549356461999365002719886808839593240625 

noncomputable def Ns114p1329 := BSN.cos_dyadic_bound_t 16011155 8388608 4 3 4194304 1440000 Ns114p1326 Ns114p631 Ns114p1327 Ns114p1328 Ns114p634 Ns114p1327 1390369 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16011155) (BSN.cosEvenQ 8388608) 0 3 Ns114p1326 Ns114p631 Ns114p1327 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16011155) (BSN.cosOddQ 8388608) 0 3 Ns114p1328 Ns114p634 Ns114p1327 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1330 := @Ns114p1317 505188608 12079595520000 1390369 4194304 1973393 47185920000 (@Ns114p1318 345 8388608 Bool.true 1390369 4194304 1 1440000 (@Ns114p1321 Ns114p520 16011155 8388608 345 8388608 (@Ns114p1322 70368744177664 458607675 70368744177664 Ns114p1319 Ns114p517 Ns114p1320 Ns114p520 RS115to132.d35 (@Ns114p1323 0 1 342020937494896 21376308593431 70368744177664 458607675 70368744177664 (@Ns114p1324 142423985129904930816 16978262082327 70368744177664 458607675 70368744177664 (@Ns114p1325 248892475 70368744177664 (Ns114p1306 rfl rfl) (Ns114p1306 rfl rfl) rfl) (Ns114p1306 rfl rfl) rfl rfl) qz370 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16011155 8388608) (BSN.cos_neg_of_bound 16011155 8388608 Bool.true 1390369 4194304 1 1440000 (Ns114p1329 rfl rfl)) rfl rfl) 

noncomputable def Ns114p1331 := @Ns114p1291 1200197251090705141 55340232221128654848000 (Ns114p1292 qz28 (@Enclosure.Real.IsNear.of_eq qz757 (@Inv.inv Real Real.instInv (Real.sqrt qz170)) Bool.false 3044189 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz166 (BSN.t_div_two_pi_nonneg qz165 362287 1000 qz168)) Ns114p1296) rfl) (@Ns114p1297 8796093022208 11801867882467 197912092999680000 (BSN.correction_mk qz167 (BSN.cos_two_pi_p_ne_zero_mk qz165 362287 1000 7 qz168 rfl rfl (@BSN.floor_sqrt_eq_dec qz165 362287 1000 7 qz168 rfl rfl rfl))) (@Ns114p1298 4194304 1390369 4194304 1973393 47185920000 3501748604175 8796093022208 11801867882467 197912092999680000 Ns114p1316 (Ns114p1330 rfl) rfl)) 

noncomputable def Ns114p1332 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz165) (hardyZApproximantRS₀ qz165) Bool.false 293850573265534892915 73786976294838206464 95005581530614033141 55340232221128654848000 (@Eq.refl Real (hardyZApproximantRS₀ qz165)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz165) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz165) qz165 7) (@HMul.hMul Real Real Real qz5 qz753 (Zeta.RiemannSiegel.correction qz167))) Bool.false 293850573265534892915 73786976294838206464 95005581530614033141 55340232221128654848000 (BSN.hardyZApproximantRS₀_eq qz165 7 (@BSN.floor_sqrt_eq_dec qz165 362287 1000 7 qz168 rfl rfl rfl)) (@Ns114p1236 293850573265534892915 73786976294838206464 95005581530614033141 55340232221128654848000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz165) qz165 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz165) qz165 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz165) qz165 7)) Bool.false 64390085 16777216 56877 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz165) qz165 7) (Ns114p1290 (Ns114p1289 rfl) rfl rfl)) (Ns114p1331 rfl) rfl rfl)) 

theorem RS115to132.d50 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz165) Bool.false 293850573265534892915 73786976294838206464 95005581530614033141 55340232221128654848000 := Ns114p1332 

noncomputable def Ns114p1333 := nat_lit 67776366990663293448749056 

noncomputable abbrev qz935 := (Enclosure.sfrac Bool.false 363836 1000)

noncomputable abbrev qz761 := qz935

noncomputable abbrev qz523 := qz761

noncomputable abbrev qz178 := qz523

noncomputable abbrev qz936 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 363836 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz762 := qz936

noncomputable abbrev qz524 := qz762

noncomputable abbrev qz179 := qz524

noncomputable abbrev qz937 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 363836 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz763 := qz937

noncomputable abbrev qz525 := qz763

noncomputable abbrev qz180 := qz525

noncomputable abbrev qz764 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz179 qz9))

noncomputable def Ns114p1334 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz178) qz178 7) (@HMul.hMul Real Real Real qz5 qz764 (Zeta.RiemannSiegel.correction qz180)) 31850423 16777216 28561 16777216 337702526115522165 2305843009213693952 2465537324859566173 103762935414616227840000 Ns114p1333 

noncomputable def Ns114p1335 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz178) qz178 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 363836 1000 61 96 67108864 33554432 1125899906842624 Bool.false 37316749029 1270 

noncomputable def Ns114p1336 := Ns114p1335 120242927 48 27397080 8 130587807 48 25364760 8 Bool.true 73773578 42373 Bool.true 1680777 Bool.true 76018040 3537118876014220 1 Bool.false 1680601 Bool.true Bool.false 28465208 Bool.false Bool.true 63700846 

noncomputable def Ns114p1337 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz178) qz178 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 363836 1000 32 18 67108864 33554432 1125899906842624 Bool.false 37316749029 1270 

noncomputable def Ns114p1338 := Ns114p1337 93032624 47 33554424 8 108007536 47 30011992 8 Bool.true 69109527 24952 Bool.false 94871817 Bool.true 82822411 3537118876014220 1 Bool.false 10499230 Bool.false Bool.false 22167630 Bool.true Bool.true 73773578 

noncomputable def Ns114p1339 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz178) qz178 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 363836 1000 193 99 67108864 33554432 1125899906842624 Bool.false 37316749029 1270 

noncomputable def Ns114p1340 := Ns114p1339 46516304 47 47453136 16 73726608 47 38745320 8 Bool.true 67108824 1327 Bool.false 47472133 Bool.false 56333531 3537118876014220 1 Bool.false 43610840 Bool.true Bool.false 49946839 Bool.false Bool.true 69109527 

noncomputable def Ns114p1341 := nat_lit 1595558509622849259715067407614409108316414551348627 

noncomputable def Ns114p1342 := nat_lit 2869384976232836427034567141599697407446089728000 

noncomputable def Ns114p1343 := nat_lit 3060353942006784336491441684480000 

noncomputable def Ns114p1344 := nat_lit 6680807509070347126188145814462791680 

noncomputable abbrev qz526 := (@Eq.refl Real qz761)

noncomputable abbrev qz181 := qz526

noncomputable def Ns114p1345 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz178 363836 1000 529507539584 16000000 727672 4000 2000 Ns114p1343 Ns114p1344 qz181 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns114p1346 := nat_lit 16730643597862887853549865220066866451619927045949379051520 

noncomputable abbrev qz765 := (Real.log (Enclosure.sfrac Bool.false 529507539584 16000000))

noncomputable abbrev qz182 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 363836 4000) qz765) (@HMul.hMul Real Real Real qz339 qz343 (@HSub.hSub Real Real Real qz342 qz344 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz345 (@Nat.cast Real Real.instNatCast 727672))))))

noncomputable abbrev qz766 := (Enclosure.sfrac Bool.false 363836 2000)

noncomputable abbrev qz527 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz182 qz766) (@HMul.hMul Real Real Real qz5 qz766 (Real.log Real.pi)))

noncomputable def Ns114p1347 := @Enclosure.Real.IsNear.addLit_ft_p qz527 (Enclosure.sfrac Bool.true Ns114p1343 Ns114p1344) 2504286698540110763239 4503599627370496000 8714887728375583 460800000000000000000 Ns114p1343 Ns114p1344 0 1 Ns114p1346 

noncomputable def Ns114p1348 := nat_lit 42014958867334322938785562624000 

noncomputable abbrev qz528 := (@HSub.hSub Real Real Real qz12 qz182 qz766)

noncomputable abbrev qz529 := (@HMul.hMul Real Real Real qz5 qz766 (Real.log Real.pi))

noncomputable def Ns114p1349 := @Enclosure.Real.IsNear.subLit_ff_p qz528 qz529 3442147678459316196583 4503599627370496000 7262423103059 900000000000000000 3493804409799 16777216000 90959 8388608000 Ns114p1348 2504286698540110763239 4503599627370496000 

noncomputable def Ns114p1350 := nat_lit 6884295356918632393166000 

noncomputable abbrev qz530 := qz766

noncomputable def Ns114p1351 := @Enclosure.Real.IsNear.subLit_ff_p qz182 qz530 4261433515471302087911 4503599627370496000 7262423103059 900000000000000000 363836 2000 0 1 Ns114p1350 3442147678459316196583 4503599627370496000 7262423103059 900000000000000000 

noncomputable def Ns114p1352 := nat_lit 9595895196170349442034178173779836928 

noncomputable def Ns114p1353 := nat_lit 12581428750651525771034624 

noncomputable def Ns114p1354 := nat_lit 3331455117741401132679168 

noncomputable def Ns114p1355 := BSN.log_dyadic_bound 5219539584 1053795539584 2 1 Ns114p1354 33554432 11520000 27243593468942893056 27243593468942893056 332398 1059015079168 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 5219539584) (BSN.artanhQ 1053795539584) 0 1 27243593468942893056 Ns114p1354 27243593468942893056 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns114p1356 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 363836 4000) qz765 363836 4000 0 1 46869474465591929 4503599627370496 156250027 1800000000000000 4263200527915776269911 4503599627370496000 14212346205893 1800000000000000000 (Enclosure.Real.IsNear.const Bool.false 363836 4000) (BSN.isNear_log_sfrac 529507539584 16000000 46869474465591929 4503599627370496 156250027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 529507539584) qz350)) Bool.false Ns114p1353 Ns114p85 1000000172800000 11520000000000000000000 46869474465591929 4503599627370496 156250027 1800000000000000 (BSN.log_rat_reduce_isNear 529507539584 16000000 15 1059015079168 1048576000000 332398 33554432 24973259072661432 36028797018963968 11520000 1000000000000000 rfl rfl rfl rfl (Ns114p1355 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p1357 := BSN.arctan_dyadic_bound_f 1000 727672 1 0 4194304 1440000 0 1 1 0 1 1 5763 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 727672) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 727672) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz531 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 727672)))

noncomputable def Ns114p1358 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz531 884279719003555 562949953421312 1 2000000000000000 5763 4194304 1 1440000 3705693681953919729664 883506222237091 562949953421312 12500000009 18000000000000000 qz16 (Ns114p1357 rfl) rfl rfl 

noncomputable def Ns114p1359 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 363836 4000) qz765) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz531)) 4263200527915776269911 4503599627370496000 14212346205893 1800000000000000000 883506222237091 2251799813685248 12500000009 72000000000000000 Ns114p1352 4261433515471302087911 4503599627370496000 7262423103059 900000000000000000 (Ns114p1356 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz531) 1 4 0 1 883506222237091 562949953421312 12500000009 18000000000000000 883506222237091 2251799813685248 12500000009 72000000000000000 qz353 Ns114p1358 rfl) 

noncomputable def Ns114p1360 := @Ns114p1347 Ns114p1341 Ns114p1342 8714887728375583 460800000000000000000 (@Ns114p1349 8714887728375583 460800000000000000000 (Ns114p1351 (Ns114p1359 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 363836 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz530 (Real.log Real.pi) 363836 2000 0 1 38410761 33554432 1 16777216 3493804409799 16777216000 90959 8388608000 (Enclosure.Real.IsNear.const Bool.false 363836 2000) RS115to132.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns114p1343 Ns114p1344) 

noncomputable def Ns114p1361 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz178) Bool.false Ns114p1341 Ns114p1342 8714887728375583 460800000000000000000 1166148407 2097152 5 262144 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz178) (@HAdd.hAdd Real Real Real qz354 qz527 (Enclosure.sfrac Bool.true Ns114p1343 Ns114p1344)) Bool.false Ns114p1341 Ns114p1342 8714887728375583 460800000000000000000 Ns114p1345 (Ns114p1360 rfl rfl)) 

noncomputable def Ns114p1362 := nat_lit 140343837272696251182251503905553798259413253367692690629215416335318480573275502961665 

noncomputable def Ns114p1363 := nat_lit 282691632921224836219424538004438891849283237950924051816043987639945067080263296001 

noncomputable def Ns114p1364 := nat_lit 367109501641855817647255822881586094378326347863465074611671542993464680916639224325121 

noncomputable def Ns114p1365 := BSN.sin_dyadic_bound_f 27003130751 17179869184 3 2 8388608 2882813 Ns114p1362 Ns114p98 Ns114p1363 Ns114p1364 Ns114p101 Ns114p1363 8388603 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 27003130751) qz355 0 2 Ns114p1362 Ns114p98 Ns114p1363 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 27003130751) qz356 0 2 Ns114p1364 Ns114p101 Ns114p1363 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1366 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz178) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1166148407) qz383) Bool.false 1166148407 2097152 5 262144 Bool.true 8388603 8388608 1 1440000 (Ns114p1361 rfl) (Enclosure.sfrac_false_div 1166148407 2097152) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1166148407) qz383) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 475044099961286949863424) qz384) 226375608064910080 72057594037927936 Bool.false 8388603 8388608 88 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q1 1166148407 2097152 226375608064910080 72057594037927936 88 475044099961286949863424 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388603 8388608 475044099961286949863424 302231454903657293676544 27003130751 17179869184 2882813 2880000 (Ns114p1365 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p1367 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz178) Bool.false Ns114p1341 Ns114p1342 8714887728375583 460800000000000000000 37316749029 67108864 1270 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz178) (@HAdd.hAdd Real Real Real qz354 qz527 (Enclosure.sfrac Bool.true Ns114p1343 Ns114p1344)) Bool.false Ns114p1341 Ns114p1342 8714887728375583 460800000000000000000 Ns114p1345 (Ns114p1360 rfl rfl)) 

noncomputable def Ns114p1368 := Ns114p1340 24952 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 193 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 43610840 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 99 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 49946839 67108864) qz181 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 1) Bool.true 8388603 8388608 29149 1474560000 67108824 67108864 1327 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz178)) Bool.true 8388603 8388608 29149 1474560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz178) qz178) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz178)) Bool.true 8388603 8388608 7462144 377487360000 8388603 8388608 29149 1474560000 (Ns114p1366 rfl rfl) rfl)) rfl) (Ns114p1367 rfl) RS115to132.d7 

noncomputable def Ns114p1369 := nat_lit 311524551010988642812219890015409143000246015271429422326007604705 

noncomputable def Ns114p1370 := nat_lit 25793481517375282133424859746684164950665996107956312064271841 

noncomputable def Ns114p1371 := nat_lit 815855872725370695003788452648386457305009914098140367300963476961 

noncomputable def Ns114p1372 := BSN.sin_dyadic_bound_f 47472133 67108864 3 2 67108864 33554432 Ns114p1369 Ns114p107 Ns114p1370 Ns114p1371 Ns114p110 Ns114p1370 43610840 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 47472133) qz359 0 2 Ns114p1369 Ns114p107 Ns114p1370 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 47472133) (BSN.sinOddQ 67108864) 0 2 Ns114p1371 Ns114p110 Ns114p1370 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1373 := nat_lit 617789517757600572516604938181446194094711057916788112867890465505 

noncomputable def Ns114p1374 := nat_lit 101422845347683609460672907171685339293442904479194785930185441 

noncomputable def Ns114p1375 := nat_lit 1617855957139343345032933748625509684460625291746240646905349966561 

noncomputable def Ns114p1376 := BSN.sin_dyadic_bound_f 56333531 67108864 3 2 67108864 33554432 Ns114p1373 Ns114p107 Ns114p1374 Ns114p1375 Ns114p110 Ns114p1374 49946839 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 56333531) qz359 0 2 Ns114p1373 Ns114p107 Ns114p1374 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 56333531) (BSN.sinOddQ 67108864) 0 2 Ns114p1375 Ns114p110 Ns114p1374 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1377 := nat_lit 666722863945416990612460530493817610811570921742609211551032913116259235798324475574947690875901142241 

noncomputable def Ns114p1378 := nat_lit 531675465570176853803507424137979580820564593413195078987233622730300990086654401347248976782561 

noncomputable def Ns114p1379 := nat_lit 4038386914122406569598285216331192640881123361245498959860573758841640993934809691568545265674408125665 

noncomputable def Ns114p1380 := BSN.cos_dyadic_bound_f 94871817 67108864 4 3 67108864 33554432 Ns114p1377 Ns114p371 Ns114p1378 Ns114p1379 Ns114p374 Ns114p1378 10499230 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 94871817) qz360 0 3 Ns114p1377 Ns114p371 Ns114p1378 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 94871817) (BSN.cosOddQ 67108864) 0 3 Ns114p1379 Ns114p374 Ns114p1378 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1381 := nat_lit 386861683182996519272578587391184540536663148020389494360995200620158621271961631011948737308823456401 

noncomputable def Ns114p1382 := nat_lit 104177618789280643296079516445493216978175078927758877734918291783074927409991478135584750373521 

noncomputable def Ns114p1383 := nat_lit 2344802715955975792549075332892266353394322352226971319443608799600196580657732613090799051979614128785 

noncomputable def Ns114p1384 := BSN.cos_dyadic_bound_f 82822411 67108864 4 3 67108864 33554432 Ns114p1381 Ns114p371 Ns114p1382 Ns114p1383 Ns114p374 Ns114p1382 22167630 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 82822411) qz360 0 3 Ns114p1381 Ns114p371 Ns114p1382 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 82822411) (BSN.cosOddQ 67108864) 0 3 Ns114p1383 Ns114p374 Ns114p1382 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1385 := Ns114p1338 42373 BSN.abs_quadSignPos (BSN.cos_quad_nat0 32 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 10499230 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 18 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 22167630 67108864) qz181 rfl rfl (Ns114p1368 RS115to132.d9 RS115to132.d11 RS115to132.d13 RS115to132.d17 (Ns114p1372 rfl rfl) (Ns114p1376 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns114p1367 rfl) RS115to132.d19 RS115to132.d21 RS115to132.d23 RS115to132.d25 RS115to132.d17 (Ns114p1380 rfl rfl) (Ns114p1384 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns114p1386 := BSN.sin_dyadic_bound_f 1680777 67108864 1 0 67108864 33554432 0 1 1 0 1 1 1680601 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 1680777) qz359 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 1680777) (BSN.sinOddQ 67108864) 0 0 rfl) rfl rfl 

noncomputable def Ns114p1387 := nat_lit 274446036069700401918199768257018279765760385888725429815083635263515746969464694234955565236224000000 

noncomputable def Ns114p1388 := nat_lit 37239171836135187635546091667965339442289561412447258609093772310538196066150383616000000000000 

noncomputable def Ns114p1389 := nat_lit 1663885683753258409776210461861032261096922973229700595498985765467584738782338730242806493321625600000 

noncomputable def Ns114p1390 := BSN.cos_dyadic_bound_f 76018040 67108864 4 3 67108864 33554432 Ns114p1387 Ns114p371 Ns114p1388 Ns114p1389 Ns114p374 Ns114p1388 28465208 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 76018040) qz360 0 3 Ns114p1387 Ns114p371 Ns114p1388 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 76018040) (BSN.cosOddQ 67108864) 0 3 Ns114p1389 Ns114p374 Ns114p1388 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1391 := Ns114p1336 57122 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 61 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 1680601 67108864) BSN.abs_quadSignPos qz734 (BSN.sfrac_eq_quadSignPos_mul Bool.false 28465208 67108864) qz181 rfl rfl (Ns114p1385 rfl rfl) (Ns114p1367 rfl) RS115to132.d27 RS115to132.d29 RS115to132.d31 RS115to132.d33 RS115to132.d17 (Ns114p1386 rfl rfl) (Ns114p1390 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns114p1392 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 7) 63700846 67108864 57122 67108864 63700846 67108864 57122 67108864 8549782821797888 31850423 16777216 28561 16777216 (Ns114p1391 rfl) 

noncomputable def Ns114p1393 := @Enclosure.Real.IsNear.mulLit_tf qz764 (Zeta.RiemannSiegel.correction qz180) 190059 524288 1 4194304 1776829963935 4398046511104 807493015763 12369505812480000 337702526115522165 2305843009213693952 

noncomputable abbrev qz767 := (@HPow.hPow Real Real Real qz7 qz179 qz9)

noncomputable def Ns114p1394 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz767 1 1 0 1 190059 524288 1 4194304 190059 524288 1 4194304 

noncomputable def Ns114p1395 := @Enclosure.Real.IsNear.sqrt_image qz179 121438360351 2097152000 90959 2097152000 31917049 31917074 4194304 (@Enclosure.Real.IsNear.of_eq qz179 (@HMul.hMul Real Real Real qz5 qz178 qz3) Bool.false 121438360351 2097152000 90959 2097152000 (BSN.t_div_two_pi_mk qz178 363836 1000 qz181) (@Enclosure.Real.IsNear.mulLit_ff qz178 qz3 363836 1000 0 1 1335089 8388608 1 8388608 121438360351 2097152000 90959 2097152000 (Enclosure.Real.IsNear.const Bool.false 363836 1000) RS115to132.d36 rfl)) 

noncomputable abbrev qz938 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 363836 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz768 := qz938

noncomputable abbrev qz532 := qz768

noncomputable abbrev qz183 := qz532

noncomputable def Ns114p1396 := @Enclosure.Real.IsNear.sqrt_image qz183 63834123 8388608 25 8388608 11570212 11570217 4194304 (@Enclosure.Real.IsNear.recentre' qz183 Bool.false 63834123 8388608 25 8388608 63834123 8388608 25 8388608 (Ns114p1395 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns114p1397 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz183) 23140429 8388608 5 8388608 1520471 1520473 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz183) Bool.false 23140429 8388608 5 8388608 23140429 8388608 5 8388608 (Ns114p1396 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns114p1398 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz183)) Bool.false 3040944 8388608 2 8388608 190059 524288 1 4194304 (Ns114p1397 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz184 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz525))

noncomputable abbrev qz769 := (@HMul.hMul Real Real Real qz884 qz937 qz937)

noncomputable abbrev qz533 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz769 qz763) qz642)

noncomputable abbrev qz185 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz533))

noncomputable def Ns114p1399 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz180) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz184) qz185) Bool.false 1776829963935 

noncomputable def Ns114p1400 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz184) qz185 5432817 4194304 139 

noncomputable abbrev qz770 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz184))

noncomputable def Ns114p1401 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz184) (@Neg.neg Real Real.instNeg qz770) Bool.true 5432817 4194304 139 4194304 (BSN.inv_eq_neg_inv_neg qz184) 

noncomputable def Ns114p1402 := @Enclosure.Real.IsNear.recentre' qz770 Bool.false 10865634 8388608 278 8388608 5432817 4194304 

noncomputable def Ns114p1403 := @Enclosure.Real.IsNear.recentre' qz184 Bool.true 6476267 8388608 237348608 12079595520000 6476267 8388608 927143 47185920000 

noncomputable abbrev qz186 := (@HMul.hMul Real Real Real qz339 qz337 qz525)

noncomputable def Ns114p1404 := @Enclosure.Real.IsNear.cos_image qz186 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 32131373) qz357) Bool.false 32131373 8388608 159 8388608 Bool.true 6476267 8388608 1 

noncomputable def Ns114p1405 := nat_lit 674651885270028919421411439 

noncomputable def Ns114p1406 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz180 884279719003555 140737488355328 1 500000000000000 5113867 8388608 25 8388608 4522088873781552797185 1180591620717411303424 Ns114p1405 

noncomputable def Ns114p1407 := @Enclosure.Real.IsNear.subLit_ff_p qz183 qz1 63834123 8388608 25 8388608 7 1 0 1 5113867 5113867 8388608 25 

noncomputable def Ns114p1408 := @Ns114p1407 8388608 (@Enclosure.Real.IsNear.recentre' qz183 Bool.false 63834123 8388608 25 8388608 63834123 8388608 25 8388608 (Ns114p1395 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns114p1409 := @Enclosure.Real.IsNear.recentre' qz186 Bool.false 4522088873781552797185 1180591620717411303424 Ns114p1405 Ns114p501 32131373 8388608 159 8388608 (@Ns114p1406 Ns114p501 RS115to132.d35 (Ns114p1408 rfl rfl) rfl) 

noncomputable def Ns114p1410 := nat_lit 2869536827715669844787503153897506233759517207927955197648483188834607848240624190625 

noncomputable def Ns114p1411 := nat_lit 384352644023464295433813088134246946669867791542633480103477705929899075875390625 

noncomputable def Ns114p1412 := nat_lit 8607841777858962605771641835516250207385211888200780325985242611091963746570121790625 

noncomputable def Ns114p1413 := BSN.cos_dyadic_bound_f 11832901085 17179869184 3 2 8388608 2882813 Ns114p1410 Ns114p1309 Ns114p1411 Ns114p1412 Ns114p1312 Ns114p1411 6476267 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 11832901085) qz454 0 2 Ns114p1410 Ns114p1309 Ns114p1411 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 11832901085) qz455 0 2 Ns114p1412 Ns114p1312 Ns114p1411 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1414 := @Ns114p1404 1440000 (Ns114p1409 rfl) (Enclosure.sfrac_false_div 32131373 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 32131373) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 832666389394138884734976) qz358) 226375608064910080 72057594037927936 Bool.false 6476267 8388608 0 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q2 32131373 8388608 226375608064910080 72057594037927936 0 832666389394138884734976 Ns114p85 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 6476267 8388608 832666389394138884734976 Ns114p85 11832901085 17179869184 2882813 2880000 (Ns114p1413 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p1415 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz184) 6476267 8388608 927143 47185920000 5432678 5432956 4194304 (@Enclosure.Real.IsNear.neg qz184 Bool.true 6476267 8388608 927143 47185920000 (Ns114p1403 (Ns114p1414 rfl rfl) rfl)) 

noncomputable def Ns114p1416 := Ns114p1401 (@Enclosure.Real.IsNear.neg qz770 Bool.false 5432817 4194304 139 4194304 (@Ns114p1402 139 4194304 (Ns114p1415 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p1417 := @Enclosure.Real.IsNear.recentre' qz185 Bool.true 1308220 4194304 

noncomputable abbrev qz187 := (@HMul.hMul Real Real Real qz339 qz337 qz533)

noncomputable def Ns114p1418 := @Enclosure.Real.IsNear.cos_image qz187 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 15837629)) qz357) Bool.true 15837629 8388608 

noncomputable def Ns114p1419 := nat_lit 18697773173619886543729378805 

noncomputable def Ns114p1420 := nat_lit 12559567092792607777983000941880417 

noncomputable def Ns114p1421 := @Enclosure.Real.IsNear.recentre' qz187 Bool.true Ns114p1419 Ns114p517 Ns114p1420 

noncomputable abbrev qz188 := qz533

noncomputable def Ns114p1422 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz188 884279719003555 140737488355328 1 500000000000000 21144636444551 

noncomputable abbrev qz534 := (@HSub.hSub Real Real Real qz634 qz769 qz763)

noncomputable abbrev qz189 := qz534

noncomputable def Ns114p1423 := @Enclosure.Real.IsNear.subLit_tf qz189 qz26 16746589933447 70368744177664 465409175 70368744177664 1 16 

noncomputable abbrev qz535 := qz769

noncomputable abbrev qz190 := qz535

noncomputable def Ns114p1424 := @Enclosure.Real.IsNear.subLit_ff_n qz190 qz180 26151635693689 70368744177664 255693975 70368744177664 5113867 8388608 25 8388608 

noncomputable def Ns114p1425 := @Enclosure.Real.IsNear.mulLit_ff qz180 qz180 5113867 8388608 25 8388608 5113867 8388608 25 8388608 26151635693689 70368744177664 

noncomputable def Ns114p1426 := nat_lit 31022819474581189191327029023155743970356861111385668346969551891120908297848827204748641521 

noncomputable def Ns114p1427 := nat_lit 249047383648971545905162776706250347702248510844013399912953761776530423188124034073841 

noncomputable def Ns114p1428 := nat_lit 187262048280471460020826574367030903606177082466475250140848915179106355295881934325642364145 

noncomputable def Ns114p1429 := BSN.cos_dyadic_bound_t 15837629 8388608 4 3 4194304 1440000 Ns114p1426 Ns114p631 Ns114p1427 Ns114p1428 Ns114p634 Ns114p1427 1308220 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 15837629) (BSN.cosEvenQ 8388608) 0 3 Ns114p1426 Ns114p631 Ns114p1427 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 15837629) (BSN.cosOddQ 8388608) 0 3 Ns114p1428 Ns114p634 Ns114p1427 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1430 := @Ns114p1417 256194304 6039797760000 327055 1048576 1000759 23592960000 (@Ns114p1418 175 4194304 Bool.true 1308220 4194304 1 1440000 (@Ns114p1421 Ns114p520 15837629 8388608 175 4194304 (@Ns114p1422 70368744177664 465409175 70368744177664 Ns114p1419 Ns114p517 Ns114p1420 Ns114p520 RS115to132.d35 (@Ns114p1423 0 1 338314183112816 21144636444551 70368744177664 465409175 70368744177664 (@Ns114p1424 140480578288432971776 16746589933447 70368744177664 465409175 70368744177664 (@Ns114p1425 255693975 70368744177664 (Ns114p1408 rfl rfl) (Ns114p1408 rfl rfl) rfl) (Ns114p1408 rfl rfl) rfl rfl) qz370 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 15837629 8388608) (BSN.cos_neg_of_bound 15837629 8388608 Bool.true 1308220 4194304 1 1440000 (Ns114p1429 rfl rfl)) rfl rfl) 

noncomputable def Ns114p1431 := @Ns114p1393 2465537324859566173 103762935414616227840000 (Ns114p1394 qz28 (@Enclosure.Real.IsNear.of_eq qz767 (@Inv.inv Real Real.instInv (Real.sqrt qz183)) Bool.false 190059 524288 1 4194304 (BSN.rpow_neg_quarter_mk qz179 (BSN.t_div_two_pi_nonneg qz178 363836 1000 qz181)) Ns114p1398) rfl) (@Ns114p1399 4398046511104 807493015763 12369505812480000 (BSN.correction_mk qz180 (BSN.cos_two_pi_p_ne_zero_mk qz178 363836 1000 7 qz181 rfl rfl (@BSN.floor_sqrt_eq_dec qz178 363836 1000 7 qz181 rfl rfl rfl))) (@Ns114p1400 4194304 327055 1048576 1000759 23592960000 1776829963935 4398046511104 807493015763 12369505812480000 Ns114p1416 (Ns114p1430 rfl) rfl)) 

noncomputable def Ns114p1432 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz178) (hardyZApproximantRS₀ qz178) Bool.true 4039786278644996491 2305843009213693952 179108265079980206173 103762935414616227840000 (@Eq.refl Real (hardyZApproximantRS₀ qz178)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz178) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz178) qz178 7) (@HMul.hMul Real Real Real qz5 qz764 (Zeta.RiemannSiegel.correction qz180))) Bool.true 4039786278644996491 2305843009213693952 179108265079980206173 103762935414616227840000 (BSN.hardyZApproximantRS₀_eq qz178 7 (@BSN.floor_sqrt_eq_dec qz178 363836 1000 7 qz181 rfl rfl rfl)) (@Ns114p1334 4039786278644996491 2305843009213693952 179108265079980206173 103762935414616227840000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz178) qz178 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 7)) Bool.true 31850423 16777216 28561 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz178) qz178 7) (Ns114p1392 (Ns114p1391 rfl) rfl rfl)) (Ns114p1431 rfl) rfl rfl)) 

theorem RS115to132.d51 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz178) Bool.true 4039786278644996491 2305843009213693952 179108265079980206173 103762935414616227840000 := Ns114p1432 

noncomputable def Ns114p1433 := nat_lit 529444121260046006005792768 

noncomputable abbrev qz939 := (Enclosure.sfrac Bool.false 365383 1000)

noncomputable abbrev qz771 := qz939

noncomputable abbrev qz536 := qz771

noncomputable abbrev qz191 := qz536

noncomputable abbrev qz940 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 365383 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz772 := qz940

noncomputable abbrev qz537 := qz772

noncomputable abbrev qz192 := qz537

noncomputable abbrev qz941 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 365383 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz773 := qz941

noncomputable abbrev qz538 := qz773

noncomputable abbrev qz193 := qz538

noncomputable abbrev qz774 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz192 qz9))

noncomputable def Ns114p1434 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz191) qz191 7) (@HMul.hMul Real Real Real qz5 qz774 (Zeta.RiemannSiegel.correction qz193)) 52409891 33554432 28679 16777216 1372343246818757745 9223372036854775808 455136361759025953 17293822569102704640000 Ns114p1433 

noncomputable def Ns114p1435 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz191) qz191 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 365383 1000 60 96 67108864 33554432 1125899906842624 Bool.false 37527547667 1275 

noncomputable def Ns114p1436 := Ns114p1435 120242927 48 27397080 8 130587807 48 25364760 8 Bool.false 29500391 42547 Bool.true 82312305 Bool.true 67238739 3537118876014220 1 Bool.false 22648458 Bool.false Bool.false 36149719 Bool.false Bool.false 52409891 

noncomputable def Ns114p1437 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz191) qz191 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 365383 1000 33 18 67108864 33554432 1125899906842624 Bool.false 37527547667 1275 

noncomputable def Ns114p1438 := Ns114p1437 93032624 47 33554424 8 108007536 47 30011992 8 Bool.false 79531835 25052 Bool.false 56334628 Bool.true 39111432 3537118876014220 1 Bool.false 49947571 Bool.true Bool.false 56030649 Bool.true Bool.false 29500391 

noncomputable def Ns114p1439 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz191) qz191 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 365383 1000 194 100 67108864 33554432 1125899906842624 Bool.false 37527547667 1275 

noncomputable def Ns114p1440 := Ns114p1439 46516304 47 47453136 16 73726608 47 38745320 8 Bool.false 67108848 1327 Bool.false 80895691 Bool.false 47662749 3537118876014220 1 Bool.false 23976814 Bool.true Bool.false 50882728 Bool.false Bool.false 79531835 

noncomputable def Ns114p1441 := nat_lit 215737199445208533487565131490862241246123095171998336647 

noncomputable def Ns114p1442 := nat_lit 385793351211606914233782313624176458213016169611264000 

noncomputable def Ns114p1443 := nat_lit 3125971282832603946724358628640000 

noncomputable def Ns114p1444 := nat_lit 6853066580198808463709211367106214720 

noncomputable abbrev qz539 := (@Eq.refl Real qz771)

noncomputable abbrev qz194 := qz539

noncomputable def Ns114p1445 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz191 365383 1000 534019946756 16000000 730766 4000 2000 Ns114p1443 Ns114p1444 qz194 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns114p1446 := nat_lit 69035903822466730716020842077075917198759390455039467727040 

noncomputable abbrev qz775 := (Real.log (Enclosure.sfrac Bool.false 534019946756 16000000))

noncomputable abbrev qz195 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 365383 4000) qz775) (@HMul.hMul Real Real Real qz339 qz343 (@HSub.hSub Real Real Real qz342 qz344 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz345 (@Nat.cast Real Real.instNatCast 730766))))))

noncomputable abbrev qz776 := (Enclosure.sfrac Bool.false 365383 2000)

noncomputable abbrev qz540 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz195 qz776) (@HMul.hMul Real Real Real qz5 qz776 (Real.log Real.pi)))

noncomputable def Ns114p1447 := @Enclosure.Real.IsNear.addLit_ft_p qz540 (Enclosure.sfrac Bool.true Ns114p1443 Ns114p1444) 10073732587748535424207 18014398509481984000 3889601130249119 204800000000000000000 Ns114p1443 Ns114p1444 0 1 Ns114p1446 

noncomputable def Ns114p1448 := nat_lit 135207350040716905996457974169600 

noncomputable abbrev qz541 := (@HSub.hSub Real Real Real qz12 qz195 qz776)

noncomputable abbrev qz542 := (@HMul.hMul Real Real Real qz5 qz776 (Real.log Real.pi))

noncomputable def Ns114p1449 := @Enclosure.Real.IsNear.subLit_ff_p qz541 qz542 2768225466143730851267 3602879701896396800 6482344846249 800000000000000000 14034639086463 67108864000 365383 33554432000 Ns114p1448 10073732587748535424207 18014398509481984000 

noncomputable def Ns114p1450 := nat_lit 27682254661437308512670000 

noncomputable abbrev qz543 := qz776

noncomputable def Ns114p1451 := @Enclosure.Real.IsNear.subLit_ff_p qz195 qz543 17132204816013682136271 18014398509481984000 6482344846249 800000000000000000 365383 2000 0 1 Ns114p1450 2768225466143730851267 3602879701896396800 6482344846249 800000000000000000 

noncomputable def Ns114p1452 := nat_lit 38578295612717117925660221973838430208 

noncomputable def Ns114p1453 := nat_lit 12591687446199517495427072 

noncomputable def Ns114p1454 := nat_lit 3360047130500701592770608 

noncomputable def Ns114p1455 := BSN.log_dyadic_bound 9731946756 1058307946756 2 1 Ns114p1454 33554432 11520000 94710787661618923536 94710787661618923536 617134 1068039893512 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 9731946756) (BSN.artanhQ 1058307946756) 0 1 94710787661618923536 Ns114p1454 94710787661618923536 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns114p1456 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 365383 4000) qz775 365383 4000 0 1 46907691084591737 4503599627370496 156250027 1800000000000000 17139272891561382640271 18014398509481984000 57091103615341 7200000000000000000 (Enclosure.Real.IsNear.const Bool.false 365383 4000) (BSN.isNear_log_sfrac 534019946756 16000000 46907691084591737 4503599627370496 156250027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 534019946756) qz350)) Bool.false Ns114p1453 Ns114p85 1000000172800000 11520000000000000000000 46907691084591737 4503599627370496 156250027 1800000000000000 (BSN.log_rat_reduce_isNear 534019946756 16000000 15 1068039893512 1048576000000 617134 33554432 24973259072661432 36028797018963968 11520000 1000000000000000 rfl rfl rfl rfl (Ns114p1455 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p1457 := BSN.arctan_dyadic_bound_f 1000 730766 1 0 4194304 1440000 0 1 1 0 1 1 5739 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 730766) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 730766) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz544 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 730766)))

noncomputable def Ns114p1458 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz544 884279719003555 562949953421312 1 2000000000000000 5739 4194304 1 1440000 3705707192752801841152 883509443462563 562949953421312 12500000009 18000000000000000 qz16 (Ns114p1457 rfl) rfl rfl 

noncomputable def Ns114p1459 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 365383 4000) qz775) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz544)) 17139272891561382640271 18014398509481984000 57091103615341 7200000000000000000 883509443462563 2251799813685248 12500000009 72000000000000000 Ns114p1452 17132204816013682136271 18014398509481984000 6482344846249 800000000000000000 (Ns114p1456 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz544) 1 4 0 1 883509443462563 562949953421312 12500000009 18000000000000000 883509443462563 2251799813685248 12500000009 72000000000000000 qz353 Ns114p1458 rfl) 

noncomputable def Ns114p1460 := @Ns114p1447 Ns114p1441 Ns114p1442 3889601130249119 204800000000000000000 (@Ns114p1449 3889601130249119 204800000000000000000 (Ns114p1451 (Ns114p1459 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 365383 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz543 (Real.log Real.pi) 365383 2000 0 1 38410761 33554432 1 16777216 14034639086463 67108864000 365383 33554432000 (Enclosure.Real.IsNear.const Bool.false 365383 2000) RS115to132.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns114p1443 Ns114p1444) 

noncomputable def Ns114p1461 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz191) Bool.false Ns114p1441 Ns114p1442 3889601130249119 204800000000000000000 2345471729 4194304 5 262144 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz191) (@HAdd.hAdd Real Real Real qz354 qz540 (Enclosure.sfrac Bool.true Ns114p1443 Ns114p1444)) Bool.false Ns114p1441 Ns114p1442 3889601130249119 204800000000000000000 Ns114p1445 (Ns114p1460 rfl rfl)) 

noncomputable def Ns114p1462 := nat_lit 140183527693971279654483751264694183403951295057703730035418091181390298991490292076705 

noncomputable def Ns114p1463 := nat_lit 282047480639872948460426113931254627451158037607100952365431400541548575449079173281 

noncomputable def Ns114p1464 := nat_lit 366690686134603080988045325318310353803999135947383986646074778445621609188890351063201 

noncomputable def Ns114p1465 := BSN.sin_dyadic_bound_f 26995431773 17179869184 3 2 8388608 2882813 Ns114p1462 Ns114p98 Ns114p1463 Ns114p1464 Ns114p101 Ns114p1463 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26995431773) qz355 0 2 Ns114p1462 Ns114p98 Ns114p1463 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26995431773) qz356 0 2 Ns114p1464 Ns114p101 Ns114p1463 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1466 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz191) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2345471729) qz366) Bool.false 2345471729 4194304 5 262144 Bool.false 8388606 8388608 1 1440000 (Ns114p1461 rfl) (Enclosure.sfrac_false_div 2345471729 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2345471729) qz366) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949817316212819349209088) qz380) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 88 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q3 2345471729 4194304 226375608064910080 72057594037927936 88 949817316212819349209088 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388606 8388608 949817316212819349209088 604462909807314587353088 26995431773 17179869184 2882813 2880000 (Ns114p1465 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p1467 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz191) Bool.false Ns114p1441 Ns114p1442 3889601130249119 204800000000000000000 37527547667 67108864 1275 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz191) (@HAdd.hAdd Real Real Real qz354 qz540 (Enclosure.sfrac Bool.true Ns114p1443 Ns114p1444)) Bool.false Ns114p1441 Ns114p1442 3889601130249119 204800000000000000000 Ns114p1445 (Ns114p1460 rfl rfl)) 

noncomputable def Ns114p1468 := Ns114p1440 25052 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 194 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 23976814 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 100 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 50882728 67108864) qz194 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz191) qz191 1) Bool.false 4194303 4194304 29149 1474560000 67108848 67108864 1327 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz191) qz191 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz191)) Bool.false 4194303 4194304 29149 1474560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz191) qz191) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz191)) Bool.false 8388606 8388608 7462144 377487360000 4194303 4194304 29149 1474560000 (Ns114p1466 rfl rfl) rfl)) rfl) (Ns114p1467 rfl) RS115to132.d7 

noncomputable def Ns114p1469 := nat_lit 352056170301034742329422042838503721365512892067800148468041845274366010434807218531158515342417090961 

noncomputable def Ns114p1470 := nat_lit 78542490564089024210948322785081546495147560942283167867735748884586702262884415374550324500881 

noncomputable def Ns114p1471 := nat_lit 2134019733067285003807198935016166569501838857797566436521723994738989799017333191834926214839829551505 

noncomputable def Ns114p1472 := BSN.cos_dyadic_bound_f 80895691 67108864 4 3 67108864 33554432 Ns114p1469 Ns114p371 Ns114p1470 Ns114p1471 Ns114p374 Ns114p1470 23976814 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 80895691) qz360 0 3 Ns114p1469 Ns114p371 Ns114p1470 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 80895691) (BSN.cosOddQ 67108864) 0 3 Ns114p1471 Ns114p374 Ns114p1470 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1473 := nat_lit 175877770217254906062090512286771440462039522246356187746644574881 

noncomputable def Ns114p1474 := nat_lit 26633773191544987709663987197589509338230064043710347582948001 

noncomputable def Ns114p1475 := nat_lit 527580043105381628210852208885919142367442106610981142544767828641 

noncomputable def Ns114p1476 := BSN.cos_dyadic_bound_f 47662749 67108864 3 2 67108864 33554432 Ns114p1473 Ns114p113 Ns114p1474 Ns114p1475 Ns114p116 Ns114p1474 50882728 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 47662749) qz360 0 2 Ns114p1473 Ns114p113 Ns114p1474 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 47662749) (BSN.cosOddQ 67108864) 0 2 Ns114p1475 Ns114p116 Ns114p1474 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1477 := nat_lit 617837648677712369577962627183162374223110941543776772173284311040 

noncomputable def Ns114p1478 := nat_lit 101438646728186450276930949168213010994564079793272370652839936 

noncomputable def Ns114p1479 := nat_lit 1617981988727877237498977563942962444757013647914035771853735264256 

noncomputable def Ns114p1480 := BSN.sin_dyadic_bound_f 56334628 67108864 3 2 67108864 33554432 Ns114p1477 Ns114p107 Ns114p1478 Ns114p1479 Ns114p110 Ns114p1478 49947571 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 56334628) qz359 0 2 Ns114p1477 Ns114p107 Ns114p1478 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 56334628) (BSN.sinOddQ 67108864) 0 2 Ns114p1479 Ns114p110 Ns114p1478 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1481 := nat_lit 79739502715024553458591668017901911817209774710013398636094816256 

noncomputable def Ns114p1482 := nat_lit 5475575072506194143854407320258154134212670023110240686309376 

noncomputable def Ns114p1483 := nat_lit 239207556994928647987487295239065219143360898789993975426911830016 

noncomputable def Ns114p1484 := BSN.cos_dyadic_bound_f 39111432 67108864 3 2 67108864 33554432 Ns114p1481 Ns114p113 Ns114p1482 Ns114p1483 Ns114p116 Ns114p1482 56030649 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 39111432) qz360 0 2 Ns114p1481 Ns114p113 Ns114p1482 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 39111432) (BSN.cosOddQ 67108864) 0 2 Ns114p1483 Ns114p116 Ns114p1482 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1485 := Ns114p1438 42547 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 33 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 49947571 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 18 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 56030649 67108864) qz194 rfl rfl (Ns114p1468 RS115to132.d9 RS115to132.d11 RS115to132.d13 RS115to132.d17 (Ns114p1472 rfl rfl) (Ns114p1476 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns114p1467 rfl) RS115to132.d19 RS115to132.d21 RS115to132.d23 RS115to132.d25 RS115to132.d17 (Ns114p1480 rfl rfl) (Ns114p1484 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns114p1486 := nat_lit 377405887536109523882178578081167895117438874363855209565232602303774449792227102239191585434041890625 

noncomputable def Ns114p1487 := nat_lit 96733557861853680886304883494636788462692055128820082139447670588996290836155533319121337890625 

noncomputable def Ns114p1488 := nat_lit 2287541641240226420637730508170364171443626734493373360677333992637998766434844662198033687528275490625 

noncomputable def Ns114p1489 := BSN.cos_dyadic_bound_f 82312305 67108864 4 3 67108864 33554432 Ns114p1486 Ns114p371 Ns114p1487 Ns114p1488 Ns114p374 Ns114p1487 22648458 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 82312305) qz360 0 3 Ns114p1486 Ns114p371 Ns114p1487 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 82312305) (BSN.cosOddQ 67108864) 0 3 Ns114p1488 Ns114p374 Ns114p1487 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1490 := nat_lit 696895256552255100387968091138377743231817287824270989762156828961 

noncomputable def Ns114p1491 := nat_lit 417788499010570439494480689256273323417993452069751246917998881 

noncomputable def Ns114p1492 := nat_lit 2089850192658744160284915312036620683048615876568673466792634489121 

noncomputable def Ns114p1493 := BSN.cos_dyadic_bound_f 67238739 67108864 3 2 67108864 33554432 Ns114p1490 Ns114p113 Ns114p1491 Ns114p1492 Ns114p116 Ns114p1491 36149719 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 67238739) qz360 0 2 Ns114p1490 Ns114p113 Ns114p1491 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 67238739) (BSN.cosOddQ 67108864) 0 2 Ns114p1492 Ns114p116 Ns114p1491 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1494 := Ns114p1436 57358 BSN.abs_quadSignPos (BSN.cos_quad_nat0 60 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 22648458 67108864) BSN.abs_quadSignPos qz734 (BSN.sfrac_eq_quadSignPos_mul Bool.false 36149719 67108864) qz194 rfl rfl (Ns114p1485 rfl rfl) (Ns114p1467 rfl) RS115to132.d27 RS115to132.d29 RS115to132.d31 RS115to132.d33 RS115to132.d17 (Ns114p1489 rfl rfl) (Ns114p1493 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns114p1495 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz191) qz191 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz191) qz191 7) 52409891 67108864 57358 67108864 52409891 67108864 57358 67108864 7034336494747648 52409891 33554432 28679 16777216 (Ns114p1494 rfl) 

noncomputable def Ns114p1496 := @Enclosure.Real.IsNear.mulLit_tf qz774 (Zeta.RiemannSiegel.correction qz193) 379715 1048576 1 4194304 3614140202043 8796093022208 3582491618701 49478023249920000 1372343246818757745 9223372036854775808 

noncomputable abbrev qz777 := (@HPow.hPow Real Real Real qz7 qz192 qz9)

noncomputable def Ns114p1497 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz777 1 1 0 1 379715 1048576 1 4194304 379715 1048576 1 4194304 

noncomputable def Ns114p1498 := @Enclosure.Real.IsNear.sqrt_image qz192 487818824087 8388608000 365383 8388608000 31984831 31984856 4194304 (@Enclosure.Real.IsNear.of_eq qz192 (@HMul.hMul Real Real Real qz5 qz191 qz3) Bool.false 487818824087 8388608000 365383 8388608000 (BSN.t_div_two_pi_mk qz191 365383 1000 qz194) (@Enclosure.Real.IsNear.mulLit_ff qz191 qz3 365383 1000 0 1 1335089 8388608 1 8388608 487818824087 8388608000 365383 8388608000 (Enclosure.Real.IsNear.const Bool.false 365383 1000) RS115to132.d36 rfl)) 

noncomputable abbrev qz942 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 365383 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz778 := qz942

noncomputable abbrev qz545 := qz778

noncomputable abbrev qz196 := qz545

noncomputable def Ns114p1499 := @Enclosure.Real.IsNear.sqrt_image qz196 63969687 8388608 25 8388608 11582491 11582496 4194304 (@Enclosure.Real.IsNear.recentre' qz196 Bool.false 63969687 8388608 25 8388608 63969687 8388608 25 8388608 (Ns114p1498 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns114p1500 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz196) 23164987 8388608 5 8388608 1518859 1518861 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz196) Bool.false 23164987 8388608 5 8388608 23164987 8388608 5 8388608 (Ns114p1499 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns114p1501 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz196)) Bool.false 3037720 8388608 2 8388608 379715 1048576 1 4194304 (Ns114p1500 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz197 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz538))

noncomputable abbrev qz779 := (@HMul.hMul Real Real Real qz884 qz941 qz941)

noncomputable abbrev qz546 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz779 qz773) qz642)

noncomputable abbrev qz198 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz546))

noncomputable def Ns114p1502 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz193) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz197) qz198) Bool.false 3614140202043 

noncomputable def Ns114p1503 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz197) qz198 2980481 2097152 83 

noncomputable abbrev qz780 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz197))

noncomputable def Ns114p1504 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz197) (@Neg.neg Real Real.instNeg qz780) Bool.true 2980481 2097152 83 2097152 (BSN.inv_eq_neg_inv_neg qz197) 

noncomputable def Ns114p1505 := @Enclosure.Real.IsNear.recentre' qz780 Bool.false 11921924 8388608 332 8388608 2980481 2097152 

noncomputable def Ns114p1506 := @Enclosure.Real.IsNear.recentre' qz197 Bool.true 5902465 8388608 117954304 6039797760000 5902465 8388608 460759 23592960000 

noncomputable abbrev qz199 := (@HMul.hMul Real Real Real qz339 qz337 qz538)

noncomputable def Ns114p1507 := @Enclosure.Real.IsNear.cos_image qz199 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 32983147) qz357) Bool.false 32983147 8388608 79 4194304 Bool.true 5902465 8388608 1 

noncomputable def Ns114p1508 := nat_lit 674651885271193405314441327 

noncomputable def Ns114p1509 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz193 884279719003555 140737488355328 1 500000000000000 5249431 8388608 25 8388608 4641965369608550727205 1180591620717411303424 Ns114p1508 

noncomputable def Ns114p1510 := @Enclosure.Real.IsNear.subLit_ff_p qz196 qz1 63969687 8388608 25 8388608 7 1 0 1 5249431 5249431 8388608 25 

noncomputable def Ns114p1511 := @Ns114p1510 8388608 (@Enclosure.Real.IsNear.recentre' qz196 Bool.false 63969687 8388608 25 8388608 63969687 8388608 25 8388608 (Ns114p1498 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns114p1512 := @Enclosure.Real.IsNear.recentre' qz199 Bool.false 4641965369608550727205 1180591620717411303424 Ns114p1508 Ns114p501 32983147 8388608 79 4194304 (@Ns114p1509 Ns114p501 RS115to132.d35 (Ns114p1511 rfl rfl) rfl) 

noncomputable def Ns114p1513 := nat_lit 4974478547209152825344097742690424066148916857188072089719232685017998147909055268001 

noncomputable def Ns114p1514 := nat_lit 1154824726649996413685605681947544862198897454171645831404709678495905313683522721 

noncomputable def Ns114p1515 := nat_lit 14921125992174158483204922016707377108722352776655872977494888635697002633099798758561 

noncomputable def Ns114p1516 := BSN.cos_dyadic_bound_f 13577334237 17179869184 3 2 8388608 2882813 Ns114p1513 Ns114p1309 Ns114p1514 Ns114p1515 Ns114p1312 Ns114p1514 5902465 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 13577334237) qz454 0 2 Ns114p1513 Ns114p1309 Ns114p1514 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 13577334237) qz455 0 2 Ns114p1515 Ns114p1312 Ns114p1514 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1517 := @Ns114p1507 1440000 (Ns114p1512 rfl) (Enclosure.sfrac_false_div 32983147 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 32983147) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 955419959602262944251904) qz358) 226375608064910080 72057594037927936 Bool.false 5902465 8388608 0 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q2 32983147 8388608 226375608064910080 72057594037927936 0 955419959602262944251904 Ns114p85 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 5902465 8388608 955419959602262944251904 Ns114p85 13577334237 17179869184 2882813 2880000 (Ns114p1516 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p1518 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz197) 5902465 8388608 460759 23592960000 5960796 5961128 4194304 (@Enclosure.Real.IsNear.neg qz197 Bool.true 5902465 8388608 460759 23592960000 (Ns114p1506 (Ns114p1517 rfl rfl) rfl)) 

noncomputable def Ns114p1519 := Ns114p1504 (@Enclosure.Real.IsNear.neg qz780 Bool.false 2980481 2097152 83 2097152 (@Ns114p1505 83 2097152 (Ns114p1518 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p1520 := @Enclosure.Real.IsNear.recentre' qz198 Bool.true 1212603 4194304 

noncomputable abbrev qz200 := (@HMul.hMul Real Real Real qz339 qz337 qz546)

noncomputable def Ns114p1521 := @Enclosure.Real.IsNear.cos_image qz200 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 15637121)) qz357) Bool.true 15637121 8388608 

noncomputable def Ns114p1522 := nat_lit 18461054256075272001298185005 

noncomputable def Ns114p1523 := nat_lit 12742484109127890628239120044465097 

noncomputable def Ns114p1524 := @Enclosure.Real.IsNear.recentre' qz200 Bool.true Ns114p1522 Ns114p517 Ns114p1523 

noncomputable abbrev qz201 := qz546

noncomputable def Ns114p1525 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz201 884279719003555 140737488355328 1 500000000000000 20876939569391 

noncomputable abbrev qz547 := (@HSub.hSub Real Real Real qz634 qz779 qz773)

noncomputable abbrev qz202 := qz547

noncomputable def Ns114p1526 := @Enclosure.Real.IsNear.subLit_tf qz202 qz26 16478893058287 70368744177664 472187375 70368744177664 1 16 

noncomputable abbrev qz548 := qz779

noncomputable abbrev qz203 := qz548

noncomputable def Ns114p1527 := @Enclosure.Real.IsNear.subLit_ff_n qz203 qz193 27556525823761 70368744177664 262472175 70368744177664 5249431 8388608 25 8388608 

noncomputable def Ns114p1528 := @Enclosure.Real.IsNear.mulLit_ff qz193 qz193 5249431 8388608 25 8388608 5249431 8388608 25 8388608 27556525823761 70368744177664 

noncomputable def Ns114p1529 := nat_lit 29470360536551029223638260693089271243678633737500855343438219264990326224464765526275243521 

noncomputable def Ns114p1530 := nat_lit 213737911265548129794612329197284679992158570742884828741837304810436640694396654435841 

noncomputable def Ns114p1531 := nat_lit 177935241662143222608701226497047686231365792582973273894278482508252715140300615505028038145 

noncomputable def Ns114p1532 := BSN.cos_dyadic_bound_t 15637121 8388608 4 3 4194304 1440000 Ns114p1529 Ns114p631 Ns114p1530 Ns114p1531 Ns114p634 Ns114p1530 1212603 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 15637121) (BSN.cosEvenQ 8388608) 0 3 Ns114p1529 Ns114p631 Ns114p1530 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 15637121) (BSN.cosOddQ 8388608) 0 3 Ns114p1531 Ns114p634 Ns114p1530 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1533 := @Ns114p1520 259074304 6039797760000 1212603 4194304 1012009 23592960000 (@Ns114p1521 177 4194304 Bool.true 1212603 4194304 1 1440000 (@Ns114p1524 Ns114p520 15637121 8388608 177 4194304 (@Ns114p1525 70368744177664 472187375 70368744177664 Ns114p1522 Ns114p517 Ns114p1523 Ns114p520 RS115to132.d35 (@Ns114p1526 0 1 334031033110256 20876939569391 70368744177664 472187375 70368744177664 (@Ns114p1527 138234974139890794496 16478893058287 70368744177664 472187375 70368744177664 (@Ns114p1528 262472175 70368744177664 (Ns114p1511 rfl rfl) (Ns114p1511 rfl rfl) rfl) (Ns114p1511 rfl rfl) rfl rfl) qz370 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 15637121 8388608) (BSN.cos_neg_of_bound 15637121 8388608 Bool.true 1212603 4194304 1 1440000 (Ns114p1532 rfl rfl)) rfl rfl) 

noncomputable def Ns114p1534 := @Ns114p1496 455136361759025953 17293822569102704640000 (Ns114p1497 qz28 (@Enclosure.Real.IsNear.of_eq qz777 (@Inv.inv Real Real.instInv (Real.sqrt qz196)) Bool.false 379715 1048576 1 4194304 (BSN.rpow_neg_quarter_mk qz192 (BSN.t_div_two_pi_nonneg qz191 365383 1000 qz194)) Ns114p1501) rfl) (@Ns114p1502 8796093022208 3582491618701 49478023249920000 (BSN.correction_mk qz193 (BSN.cos_two_pi_p_ne_zero_mk qz191 365383 1000 7 qz194 rfl rfl (@BSN.floor_sqrt_eq_dec qz191 365383 1000 7 qz194 rfl rfl rfl))) (@Ns114p1503 2097152 1212603 4194304 1012009 23592960000 3614140202043 8796093022208 3582491618701 49478023249920000 Ns114p1519 (Ns114p1533 rfl) rfl)) 

noncomputable def Ns114p1535 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz191) (hardyZApproximantRS₀ qz191) Bool.false 15778664388061940849 9223372036854775808 30017224461435185953 17293822569102704640000 (@Eq.refl Real (hardyZApproximantRS₀ qz191)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz191) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz191) qz191 7) (@HMul.hMul Real Real Real qz5 qz774 (Zeta.RiemannSiegel.correction qz193))) Bool.false 15778664388061940849 9223372036854775808 30017224461435185953 17293822569102704640000 (BSN.hardyZApproximantRS₀_eq qz191 7 (@BSN.floor_sqrt_eq_dec qz191 365383 1000 7 qz194 rfl rfl rfl)) (@Ns114p1434 15778664388061940849 9223372036854775808 30017224461435185953 17293822569102704640000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz191) qz191 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz191) qz191 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz191) qz191 7)) Bool.false 52409891 33554432 28679 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz191) qz191 7) (Ns114p1495 (Ns114p1494 rfl) rfl rfl)) (Ns114p1534 rfl) rfl rfl)) 

theorem RS115to132.d52 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz191) Bool.false 15778664388061940849 9223372036854775808 30017224461435185953 17293822569102704640000 := Ns114p1535 

noncomputable def Ns114p1536 := nat_lit 2369387214332017485669203968 

noncomputable abbrev qz943 := (Enclosure.sfrac Bool.false 366928 1000)

noncomputable abbrev qz781 := qz943

noncomputable abbrev qz549 := qz781

noncomputable abbrev qz204 := qz549

noncomputable abbrev qz944 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 366928 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz782 := qz944

noncomputable abbrev qz550 := qz782

noncomputable abbrev qz205 := qz550

noncomputable abbrev qz945 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 366928 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz783 := qz945

noncomputable abbrev qz551 := qz783

noncomputable abbrev qz206 := qz551

noncomputable abbrev qz784 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz205 qz9))

noncomputable def Ns114p1537 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz204) qz204 7) (@HMul.hMul Real Real Real qz5 qz784 (Zeta.RiemannSiegel.correction qz206)) 34652557 16777216 14401 8388608 11177074169070259905 73786976294838206464 2484534064461308639 83010348331692982272000 Ns114p1536 

noncomputable def Ns114p1538 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 366928 1000 60 96 67108864 33554432 1125899906842624 Bool.false 37738293091 1281 

noncomputable def Ns114p1539 := Ns114p1538 120242927 48 27397080 8 130587807 48 25364760 8 Bool.true 103688962 42730 Bool.true 57342203 Bool.true 58251477 3537118876014220 1 Bool.false 44065143 Bool.false Bool.false 43375326 Bool.false Bool.true 69305114 

noncomputable def Ns114p1540 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 366928 1000 34 17 67108864 33554432 1125899906842624 Bool.false 37738293091 1281 

noncomputable def Ns114p1541 := Ns114p1540 93032624 47 33554424 8 108007536 47 30011992 8 Bool.true 41388640 25161 Bool.false 17930291 Bool.true 100652008 3537118876014220 1 Bool.false 64727752 Bool.true Bool.false 66939955 Bool.true Bool.true 103688962 

noncomputable def Ns114p1542 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz204) qz204 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 366928 1000 196 101 67108864 33554432 1125899906842624 Bool.false 37738293091 1281 

noncomputable def Ns114p1543 := Ns114p1542 46516304 47 47453136 16 73726608 47 38745320 8 Bool.true 67108840 1335 Bool.false 8944711 Bool.false 39086207 3537118876014220 1 Bool.false 66513641 Bool.false Bool.false 36913553 Bool.true Bool.true 41388640 

noncomputable def Ns114p1544 := nat_lit 679050772552796085051546542818392658035548731647533 

noncomputable def Ns114p1545 := nat_lit 1207535429161083639634989005345253011527355596800 

noncomputable def Ns114p1546 := nat_lit 3192622344364001343846612336640000 

noncomputable def Ns114p1547 := nat_lit 7028781280160669933742546740367851520 

noncomputable abbrev qz552 := (@Eq.refl Real qz781)

noncomputable abbrev qz207 := qz552

noncomputable def Ns114p1548 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz204 366928 1000 538545628736 16000000 733856 4000 2000 Ns114p1546 Ns114p1547 qz207 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns114p1549 := nat_lit 890045428600400884598763084602923624740354433545054453760 

noncomputable abbrev qz785 := (Real.log (Enclosure.sfrac Bool.false 538545628736 16000000))

noncomputable abbrev qz208 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 366928 4000) qz785) (@HMul.hMul Real Real Real qz339 qz343 (@HSub.hSub Real Real Real qz342 qz344 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz345 (@Nat.cast Real Real.instNatCast 733856))))))

noncomputable abbrev qz786 := (Enclosure.sfrac Bool.false 366928 2000)

noncomputable abbrev qz553 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz208 qz786) (@HMul.hMul Real Real Real qz5 qz786 (Real.log Real.pi)))

noncomputable def Ns114p1550 := @Enclosure.Real.IsNear.addLit_ft_p qz553 (Enclosure.sfrac Bool.true Ns114p1546 Ns114p1547) 126628801215834029213 225179981368524800 732355824326807 38400000000000000000 Ns114p1546 Ns114p1547 0 1 Ns114p1549 

noncomputable def Ns114p1551 := nat_lit 2655598437273887660321013760000 

noncomputable abbrev qz554 := (@HSub.hSub Real Real Real qz12 qz208 qz786)

noncomputable abbrev qz555 := (@HMul.hMul Real Real Real qz5 qz786 (Real.log Real.pi))

noncomputable def Ns114p1552 := @Enclosure.Real.IsNear.subLit_ff_p qz554 qz555 869601815119365598993 1125899906842624000 4881875825663 600000000000000000 880873982013 4194304000 22933 2097152000 Ns114p1551 126628801215834029213 225179981368524800 

noncomputable def Ns114p1553 := nat_lit 1739203630238731197986000 

noncomputable abbrev qz556 := qz786

noncomputable def Ns114p1554 := @Enclosure.Real.IsNear.subLit_ff_p qz208 qz556 1076163915628340768529 1125899906842624000 4881875825663 600000000000000000 366928 2000 0 1 Ns114p1553 869601815119365598993 1125899906842624000 4881875825663 600000000000000000 

noncomputable def Ns114p1555 := nat_lit 2423305704706684690930367740029960192 

noncomputable def Ns114p1556 := nat_lit 12601889612564986465353728 

noncomputable def Ns114p1557 := nat_lit 3388845967116400454873088 

noncomputable def Ns114p1558 := BSN.log_dyadic_bound 14257628736 1062833628736 2 1 Ns114p1557 33554432 11520000 203279977173612957696 203279977173612957696 900301 1077091257472 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 14257628736) (BSN.artanhQ 1062833628736) 0 1 203279977173612957696 Ns114p1557 203279977173612957696 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns114p1559 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 366928 4000) qz785 366928 4000 0 1 46945697115976313 4503599627370496 156250027 1800000000000000 1076605671960684786029 1125899906842624000 3583281869191 450000000000000000 (Enclosure.Real.IsNear.const Bool.false 366928 4000) (BSN.isNear_log_sfrac 538545628736 16000000 46945697115976313 4503599627370496 156250027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 538545628736) qz350)) Bool.false Ns114p1556 Ns114p85 1000000172800000 11520000000000000000000 46945697115976313 4503599627370496 156250027 1800000000000000 (BSN.log_rat_reduce_isNear 538545628736 16000000 15 1077091257472 1048576000000 900301 33554432 24973259072661432 36028797018963968 11520000 1000000000000000 rfl rfl rfl rfl (Ns114p1558 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p1560 := BSN.arctan_dyadic_bound_f 1000 733856 1 0 4194304 1440000 0 1 1 0 1 1 5715 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 733856) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 733856) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz787 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 733856)))

noncomputable def Ns114p1561 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz787 884279719003555 562949953421312 1 2000000000000000 5715 4194304 1 1440000 3705720703551683952640 883512664688035 562949953421312 12500000009 18000000000000000 qz16 (Ns114p1560 rfl) rfl rfl 

noncomputable def Ns114p1562 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 366928 4000) qz785) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz787)) 1076605671960684786029 1125899906842624000 3583281869191 450000000000000000 883512664688035 2251799813685248 12500000009 72000000000000000 Ns114p1555 1076163915628340768529 1125899906842624000 4881875825663 600000000000000000 (Ns114p1559 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz787) 1 4 0 1 883512664688035 562949953421312 12500000009 18000000000000000 883512664688035 2251799813685248 12500000009 72000000000000000 qz353 Ns114p1561 rfl) 

noncomputable def Ns114p1563 := @Ns114p1550 Ns114p1544 Ns114p1545 732355824326807 38400000000000000000 (@Ns114p1552 732355824326807 38400000000000000000 (Ns114p1554 (Ns114p1562 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 366928 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz556 (Real.log Real.pi) 366928 2000 0 1 38410761 33554432 1 16777216 880873982013 4194304000 22933 2097152000 (Enclosure.Real.IsNear.const Bool.false 366928 2000) RS115to132.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns114p1546 Ns114p1547) 

noncomputable def Ns114p1564 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz204) Bool.false Ns114p1544 Ns114p1545 732355824326807 38400000000000000000 1179321659 2097152 161 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz204) (@HAdd.hAdd Real Real Real qz354 qz553 (Enclosure.sfrac Bool.true Ns114p1546 Ns114p1547)) Bool.false Ns114p1544 Ns114p1545 732355824326807 38400000000000000000 Ns114p1548 (Ns114p1563 rfl rfl)) 

noncomputable def Ns114p1565 := nat_lit 139740270482792780042637695765644768400230411858502020658674864126089867785589510685665 

noncomputable def Ns114p1566 := nat_lit 280270203730311906125383501406237769967877904686797951646898095419403124849934124001 

noncomputable def Ns114p1567 := nat_lit 365532651886989157025562391812507151325417371593250476470053475794794429617263110833121 

noncomputable def Ns114p1568 := BSN.sin_dyadic_bound_f 26974109499 17179869184 3 2 8388608 2882813 Ns114p1565 Ns114p98 Ns114p1566 Ns114p1567 Ns114p101 Ns114p1566 8388605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26974109499) qz355 0 2 Ns114p1565 Ns114p98 Ns114p1566 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26974109499) qz356 0 2 Ns114p1567 Ns114p101 Ns114p1566 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1569 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz204) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1179321659) qz383) Bool.false 1179321659 2097152 161 8388608 Bool.true 8388605 8388608 1 1440000 (Ns114p1564 rfl) (Enclosure.sfrac_false_div 1179321659 2097152) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1179321659) qz383) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474533552693762251030528) qz384) 226375608064910080 72057594037927936 Bool.false 8388605 8388608 89 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q1 1179321659 2097152 226375608064910080 72057594037927936 89 474533552693762251030528 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388605 8388608 474533552693762251030528 302231454903657293676544 26974109499 17179869184 2882813 2880000 (Ns114p1568 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p1570 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz204) Bool.false Ns114p1544 Ns114p1545 732355824326807 38400000000000000000 37738293091 67108864 1281 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz204) (@HAdd.hAdd Real Real Real qz354 qz553 (Enclosure.sfrac Bool.true Ns114p1546 Ns114p1547)) Bool.false Ns114p1544 Ns114p1545 732355824326807 38400000000000000000 Ns114p1548 (Ns114p1563 rfl rfl)) 

noncomputable def Ns114p1571 := Ns114p1543 25161 BSN.abs_quadSignPos (BSN.cos_quad_nat0 196 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66513641 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 101 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 36913553 67108864) qz207 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 1) Bool.true 8388605 8388608 938393 47185920000 67108840 67108864 1335 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz204)) Bool.true 8388605 8388608 938393 47185920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz204) qz204) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz204)) Bool.true 8388605 8388608 240228608 12079595520000 8388605 8388608 938393 47185920000 (Ns114p1569 rfl rfl) rfl)) rfl) (Ns114p1570 rfl) RS115to132.d7 

noncomputable def Ns114p1572 := nat_lit 6401256841462398030906937441 

noncomputable def Ns114p1573 := BSN.cos_dyadic_bound_f 8944711 67108864 2 1 67108864 33554432 Ns114p1572 Ns114p227 Ns114p1572 Ns114p1572 Ns114p228 Ns114p1572 66513641 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 8944711) qz360 0 1 Ns114p1572 Ns114p227 Ns114p1572 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 8944711) (BSN.cosOddQ 67108864) 0 1 Ns114p1572 Ns114p228 Ns114p1572 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1574 := nat_lit 143156796961776290768225089872997758803406236799836807779160669185 

noncomputable def Ns114p1575 := nat_lit 5447386895260364387464643826090816662711165380823594108697601 

noncomputable def Ns114p1576 := nat_lit 374925648654440816183962197386894745067657659255622686935911480321 

noncomputable def Ns114p1577 := BSN.sin_dyadic_bound_f 39086207 67108864 3 2 67108864 33554432 Ns114p1574 Ns114p107 Ns114p1575 Ns114p1576 Ns114p110 Ns114p1575 36913553 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 39086207) qz359 0 2 Ns114p1574 Ns114p107 Ns114p1575 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 39086207) (BSN.sinOddQ 67108864) 0 2 Ns114p1576 Ns114p110 Ns114p1575 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1578 := nat_lit 103359250648388892245074991761 

noncomputable def Ns114p1579 := BSN.cos_dyadic_bound_f 17930291 67108864 2 1 67108864 33554432 Ns114p1578 Ns114p227 Ns114p1578 Ns114p1578 Ns114p228 Ns114p1578 64727752 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 17930291) qz360 0 1 Ns114p1578 Ns114p227 Ns114p1578 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 17930291) (BSN.cosOddQ 67108864) 0 1 Ns114p1578 Ns114p228 Ns114p1578 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1580 := nat_lit 2194594458682416386665172413187409545469633954671767183283275179534118666259050016484619550728740929536 

noncomputable def Ns114p1581 := nat_lit 1081108598392957795992923486050838785605198555851045966494845178851906581870555434299187303284736 

noncomputable def Ns114p1582 := nat_lit 10961636072142533907277235855289156180489863457014948710703097744982037963397977499473802607302327402496 

noncomputable def Ns114p1583 := BSN.sin_dyadic_bound_f 100652008 67108864 4 3 67108864 33554432 Ns114p1580 Ns114p579 Ns114p1581 Ns114p1582 Ns114p582 Ns114p1581 66939955 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 100652008) qz359 0 3 Ns114p1580 Ns114p579 Ns114p1581 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 100652008) (BSN.sinOddQ 67108864) 0 3 Ns114p1582 Ns114p582 Ns114p1581 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1584 := Ns114p1541 42730 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 34 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 64727752 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 17 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66939955 67108864) qz207 rfl rfl (Ns114p1571 RS115to132.d9 RS115to132.d11 RS115to132.d13 RS115to132.d17 (Ns114p1573 rfl rfl) (Ns114p1577 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns114p1570 rfl) RS115to132.d19 RS115to132.d21 RS115to132.d23 RS115to132.d25 RS115to132.d17 (Ns114p1579 rfl rfl) (Ns114p1583 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns114p1585 := nat_lit 368522582206431593071208463562207696666032694861639437271895363041 

noncomputable def Ns114p1586 := nat_lit 116894745806807793927225373310078698220071861844441979589217761 

noncomputable def Ns114p1587 := nat_lit 1105333957127681163625770939940002932601657940861229427856507653601 

noncomputable def Ns114p1588 := BSN.cos_dyadic_bound_f 57342203 67108864 3 2 67108864 33554432 Ns114p1585 Ns114p113 Ns114p1586 Ns114p1587 Ns114p116 Ns114p1586 44065143 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 57342203) qz360 0 2 Ns114p1585 Ns114p113 Ns114p1586 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 57342203) (BSN.cosOddQ 67108864) 0 2 Ns114p1587 Ns114p116 Ns114p1586 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1589 := nat_lit 392467161414016318649992992469305693085208851368389468029102667361 

noncomputable def Ns114p1590 := nat_lit 132573137046444291917442935291025994810095331136693498110621281 

noncomputable def Ns114p1591 := nat_lit 1177136337967956067366144091537335027266006363442895017091086759521 

noncomputable def Ns114p1592 := BSN.cos_dyadic_bound_f 58251477 67108864 3 2 67108864 33554432 Ns114p1589 Ns114p113 Ns114p1590 Ns114p1591 Ns114p116 Ns114p1590 43375326 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 58251477) qz360 0 2 Ns114p1589 Ns114p113 Ns114p1590 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 58251477) (BSN.cosOddQ 67108864) 0 2 Ns114p1591 Ns114p116 Ns114p1590 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1593 := Ns114p1539 57604 BSN.abs_quadSignPos (BSN.cos_quad_nat0 60 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 44065143 67108864) BSN.abs_quadSignPos qz734 (BSN.sfrac_eq_quadSignPos_mul Bool.false 43375326 67108864) qz207 rfl rfl (Ns114p1584 rfl rfl) (Ns114p1570 rfl) RS115to132.d27 RS115to132.d29 RS115to132.d31 RS115to132.d33 RS115to132.d17 (Ns114p1588 rfl rfl) (Ns114p1592 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns114p1594 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 7) 69305114 67108864 57604 67108864 69305114 67108864 57604 67108864 9301974939860992 34652557 16777216 14401 8388608 (Ns114p1593 rfl) 

noncomputable def Ns114p1595 := @Enclosure.Real.IsNear.mulLit_tf qz784 (Zeta.RiemannSiegel.correction qz206) 1517259 4194304 1 4194304 7366622421795 17592186044416 2040064502983 24739011624960000 11177074169070259905 73786976294838206464 

noncomputable abbrev qz788 := (@HPow.hPow Real Real Real qz7 qz205 qz9)

noncomputable def Ns114p1596 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz788 1 1 0 1 1517259 4194304 1 4194304 1517259 4194304 1 4194304 

noncomputable def Ns114p1597 := @Enclosure.Real.IsNear.sqrt_image qz205 30617596037 524288000 22933 524288000 32052383 32052408 4194304 (@Enclosure.Real.IsNear.of_eq qz205 (@HMul.hMul Real Real Real qz5 qz204 qz3) Bool.false 30617596037 524288000 22933 524288000 (BSN.t_div_two_pi_mk qz204 366928 1000 qz207) (@Enclosure.Real.IsNear.mulLit_ff qz204 qz3 366928 1000 0 1 1335089 8388608 1 8388608 30617596037 524288000 22933 524288000 (Enclosure.Real.IsNear.const Bool.false 366928 1000) RS115to132.d36 rfl)) 

noncomputable abbrev qz946 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 366928 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz789 := qz946

noncomputable abbrev qz557 := qz789

noncomputable abbrev qz209 := qz557

noncomputable def Ns114p1598 := @Enclosure.Real.IsNear.sqrt_image qz209 64104791 8388608 25 8388608 11594715 11594721 4194304 (@Enclosure.Real.IsNear.recentre' qz209 Bool.false 64104791 8388608 25 8388608 64104791 8388608 25 8388608 (Ns114p1597 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns114p1599 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz209) 5797359 2097152 3 4194304 1517258 1517260 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz209) Bool.false 23189436 8388608 6 8388608 5797359 2097152 3 4194304 (Ns114p1598 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns114p1600 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz209)) Bool.false 3034518 8388608 2 8388608 1517259 4194304 1 4194304 (Ns114p1599 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz210 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz551))

noncomputable abbrev qz790 := (@HMul.hMul Real Real Real qz884 qz945 qz945)

noncomputable abbrev qz558 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz790 qz783) qz642)

noncomputable abbrev qz211 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz558))

noncomputable def Ns114p1601 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz206) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz210) qz211) Bool.false 7366622421795 

noncomputable def Ns114p1602 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz210) qz211 6676215 4194304 13 

noncomputable abbrev qz791 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz210))

noncomputable def Ns114p1603 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz210) (@Neg.neg Real Real.instNeg qz791) Bool.true 6676215 4194304 13 262144 (BSN.inv_eq_neg_inv_neg qz210) 

noncomputable def Ns114p1604 := @Enclosure.Real.IsNear.recentre' qz791 Bool.false 13352430 8388608 416 8388608 6676215 4194304 

noncomputable def Ns114p1605 := @Enclosure.Real.IsNear.recentre' qz210 Bool.true 5270108 8388608 117954304 6039797760000 1317527 2097152 460759 23592960000 

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz339 qz337 qz551)

noncomputable def Ns114p1606 := @Enclosure.Real.IsNear.cos_image qz212 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 33832031) qz357) Bool.false 33832031 8388608 79 4194304 Bool.true 5270108 8388608 1 

noncomputable def Ns114p1607 := nat_lit 134930377054470787967511779 

noncomputable def Ns114p1608 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz206 884279719003555 140737488355328 1 500000000000000 5384535 8388608 25 8388608 4761435096764807021925 1180591620717411303424 Ns114p1607 

noncomputable def Ns114p1609 := @Enclosure.Real.IsNear.subLit_ff_p qz209 qz1 64104791 8388608 25 8388608 7 1 0 1 5384535 5384535 8388608 25 

noncomputable def Ns114p1610 := @Ns114p1609 8388608 (@Enclosure.Real.IsNear.recentre' qz209 Bool.false 64104791 8388608 25 8388608 64104791 8388608 25 8388608 (Ns114p1597 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns114p1611 := @Enclosure.Real.IsNear.recentre' qz212 Bool.false 4761435096764807021925 1180591620717411303424 Ns114p1607 Ns114p714 33832031 8388608 79 4194304 (@Ns114p1608 Ns114p714 RS115to132.d35 (Ns114p1610 rfl rfl) rfl) 

noncomputable def Ns114p1612 := nat_lit 8055939902987955671782235982652021436501254361115326684312558868779344733798484853921 

noncomputable def Ns114p1613 := nat_lit 3027809397484177850394815881798317200921463035691929331073601206568993181139911841 

noncomputable def Ns114p1614 := nat_lit 24161764090168898659645918316192467675101920157274596194275529403924896215033174738081 

noncomputable def Ns114p1615 := BSN.cos_dyadic_bound_f 15315848669 17179869184 3 2 8388608 2882813 Ns114p1612 Ns114p1309 Ns114p1613 Ns114p1614 Ns114p1312 Ns114p1613 5270108 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 15315848669) qz454 0 2 Ns114p1612 Ns114p1309 Ns114p1613 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 15315848669) qz455 0 2 Ns114p1614 Ns114p1312 Ns114p1613 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1616 := @Ns114p1606 1440000 (Ns114p1611 rfl) (Enclosure.sfrac_false_div 33832031 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 33832031) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1077757036916847780298752) qz358) 226375608064910080 72057594037927936 Bool.false 5270108 8388608 0 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q2 33832031 8388608 226375608064910080 72057594037927936 0 1077757036916847780298752 Ns114p85 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 5270108 8388608 1077757036916847780298752 Ns114p85 15315848669 17179869184 2882813 2880000 (Ns114p1615 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p1617 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz210) 1317527 2097152 460759 23592960000 6676007 6676423 4194304 (@Enclosure.Real.IsNear.neg qz210 Bool.true 1317527 2097152 460759 23592960000 (Ns114p1605 (Ns114p1616 rfl rfl) rfl)) 

noncomputable def Ns114p1618 := Ns114p1603 (@Enclosure.Real.IsNear.neg qz791 Bool.false 6676215 4194304 13 262144 (@Ns114p1604 13 262144 (Ns114p1617 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p1619 := @Enclosure.Real.IsNear.recentre' qz211 Bool.true 1103413 4194304 

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz339 qz337 qz558)

noncomputable def Ns114p1620 := @Enclosure.Real.IsNear.cos_image qz213 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7704951)) qz366) Bool.true 7704951 4194304 

noncomputable def Ns114p1621 := nat_lit 18192801948447154679898275245 

noncomputable def Ns114p1622 := nat_lit 12924780445728459148622119234094153 

noncomputable def Ns114p1623 := @Enclosure.Real.IsNear.recentre' qz213 Bool.true Ns114p1621 Ns114p517 Ns114p1622 

noncomputable abbrev qz214 := qz558

noncomputable def Ns114p1624 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz214 884279719003555 140737488355328 1 500000000000000 20573582722159 

noncomputable abbrev qz559 := (@HSub.hSub Real Real Real qz634 qz790 qz783)

noncomputable abbrev qz215 := qz559

noncomputable def Ns114p1625 := @Enclosure.Real.IsNear.subLit_tf qz215 qz26 16175536211055 70368744177664 478942575 70368744177664 1 16 

noncomputable abbrev qz560 := qz790

noncomputable abbrev qz216 := qz560

noncomputable def Ns114p1626 := @Enclosure.Real.IsNear.subLit_ff_n qz216 qz206 28993217166225 70368744177664 269227375 70368744177664 5384535 8388608 25 8388608 

noncomputable def Ns114p1627 := @Enclosure.Real.IsNear.mulLit_ff qz206 qz206 5384535 8388608 25 8388608 5384535 8388608 25 8388608 28993217166225 70368744177664 

noncomputable def Ns114p1628 := nat_lit 6782990349370411765214209177113606011172159791923732308321676327898403107724265565370081 

noncomputable def Ns114p1629 := nat_lit 43776251800014674037952809114039931649746867960166918059130887707453667829205874401 

noncomputable def Ns114p1630 := nat_lit 40965216639125781525282758975263143947747164521339211827571332997318143584466143402964705 

noncomputable def Ns114p1631 := BSN.cos_dyadic_bound_t 7704951 4194304 4 3 4194304 1440000 Ns114p1628 Ns114p175 Ns114p1629 Ns114p1630 Ns114p178 Ns114p1629 1103413 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 7704951) (BSN.cosEvenQ 4194304) 0 3 Ns114p1628 Ns114p175 Ns114p1629 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 7704951) (BSN.cosOddQ 4194304) 0 3 Ns114p1630 Ns114p178 Ns114p1629 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1632 := @Ns114p1619 65848576 1509949440000 1103413 4194304 257221 5898240000 (@Ns114p1620 45 1048576 Bool.true 1103413 4194304 1 1440000 (@Ns114p1623 Ns114p520 7704951 4194304 45 1048576 (@Ns114p1624 70368744177664 478942575 70368744177664 Ns114p1621 Ns114p517 Ns114p1622 Ns114p520 RS115to132.d35 (@Ns114p1625 0 1 329177323554544 20573582722159 70368744177664 478942575 70368744177664 (@Ns114p1626 135690232464345661440 16175536211055 70368744177664 478942575 70368744177664 (@Ns114p1627 269227375 70368744177664 (Ns114p1610 rfl rfl) (Ns114p1610 rfl rfl) rfl) (Ns114p1610 rfl rfl) rfl rfl) qz370 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7704951 4194304) (BSN.cos_neg_of_bound 7704951 4194304 Bool.true 1103413 4194304 1 1440000 (Ns114p1631 rfl rfl)) rfl rfl) 

noncomputable def Ns114p1633 := @Ns114p1595 2484534064461308639 83010348331692982272000 (Ns114p1596 qz28 (@Enclosure.Real.IsNear.of_eq qz788 (@Inv.inv Real Real.instInv (Real.sqrt qz209)) Bool.false 1517259 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz205 (BSN.t_div_two_pi_nonneg qz204 366928 1000 qz207)) Ns114p1600) rfl) (@Ns114p1601 17592186044416 2040064502983 24739011624960000 (BSN.correction_mk qz206 (BSN.cos_two_pi_p_ne_zero_mk qz204 366928 1000 7 qz207 rfl rfl (@BSN.floor_sqrt_eq_dec qz204 366928 1000 7 qz207 rfl rfl rfl))) (@Ns114p1602 262144 1103413 4194304 257221 5898240000 7366622421795 17592186044416 2040064502983 24739011624960000 Ns114p1618 (Ns114p1632 rfl) rfl)) 

noncomputable def Ns114p1634 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz204) (hardyZApproximantRS₀ qz204) Bool.true 141226483245612233023 73786976294838206464 144991136628880892639 83010348331692982272000 (@Eq.refl Real (hardyZApproximantRS₀ qz204)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz204) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz204) qz204 7) (@HMul.hMul Real Real Real qz5 qz784 (Zeta.RiemannSiegel.correction qz206))) Bool.true 141226483245612233023 73786976294838206464 144991136628880892639 83010348331692982272000 (BSN.hardyZApproximantRS₀_eq qz204 7 (@BSN.floor_sqrt_eq_dec qz204 366928 1000 7 qz207 rfl rfl rfl)) (@Ns114p1537 141226483245612233023 73786976294838206464 144991136628880892639 83010348331692982272000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz204) qz204 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz204) qz204 7)) Bool.true 34652557 16777216 14401 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz204) qz204 7) (Ns114p1594 (Ns114p1593 rfl) rfl rfl)) (Ns114p1633 rfl) rfl rfl)) 

theorem RS115to132.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz204) Bool.true 141226483245612233023 73786976294838206464 144991136628880892639 83010348331692982272000 := Ns114p1634 

noncomputable def Ns114p1635 := nat_lit 1660206966633859645440000 

noncomputable def Ns114p1636 := nat_lit 5963678301762699601515642880 

noncomputable abbrev qz947 := (Enclosure.sfrac Bool.false 368472 1000)

noncomputable abbrev qz792 := qz947

noncomputable abbrev qz561 := qz792

noncomputable abbrev qz217 := qz561

noncomputable abbrev qz948 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 368472 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz793 := qz948

noncomputable abbrev qz562 := qz793

noncomputable abbrev qz218 := qz562

noncomputable abbrev qz949 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 368472 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz794 := qz949

noncomputable abbrev qz563 := qz794

noncomputable abbrev qz219 := qz563

noncomputable abbrev qz795 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz218 qz9))

noncomputable def Ns114p1637 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz217) qz217 7) (@HMul.hMul Real Real Real qz5 qz795 (Zeta.RiemannSiegel.correction qz219)) 15020705 33554432 57847 33554432 45607944926490447325 295147905179352825856 57778223601568993709 Ns114p1635 Ns114p1636 

noncomputable def Ns114p1638 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz217) qz217 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 368472 1000 60 96 67108864 33554432 1125899906842624 Bool.false 37949120173 1286 

noncomputable def Ns114p1639 := Ns114p1638 120242927 48 27397080 8 130587807 48 25364760 8 Bool.true 28173697 42911 Bool.true 32170200 Bool.true 49051969 3537118876014220 1 Bool.false 59544629 Bool.false Bool.false 49966107 Bool.false Bool.false 15020705 

noncomputable def Ns114p1640 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz217) qz217 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 368472 1000 34 17 67108864 33554432 1125899906842624 Bool.false 37949120173 1286 

noncomputable def Ns114p1641 := Ns114p1640 93032624 47 33554424 8 108007536 47 30011992 8 Bool.false 4234823 25269 Bool.false 85115002 Bool.true 56588561 3537118876014220 1 Bool.false 19991214 Bool.true Bool.false 50116808 Bool.true Bool.true 28173697 

noncomputable def Ns114p1642 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz217) qz217 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 368472 1000 197 102 67108864 33554432 1125899906842624 Bool.false 37949120173 1286 

noncomputable def Ns114p1643 := Ns114p1642 46516304 47 47453136 16 73726608 47 38745320 8 Bool.false 67108840 1343 Bool.false 42536263 Bool.false 30665049 3537118876014220 1 Bool.false 39744754 Bool.true Bool.false 60223806 Bool.true Bool.false 4234823 

noncomputable def Ns114p1644 := nat_lit 155614836089438874999940270897098610983229413872683 

noncomputable def Ns114p1645 := nat_lit 275187799447141810059285523059432662929663590400 

noncomputable def Ns114p1646 := nat_lit 3260361239160281181502497423360000 

noncomputable def Ns114p1647 := nat_lit 7208117152984126850885716579897835520 

noncomputable abbrev qz796 := (@Eq.refl Real qz947)

noncomputable abbrev qz564 := qz796

noncomputable abbrev qz220 := qz564

noncomputable def Ns114p1648 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz217 368472 1000 543087459136 16000000 736944 4000 2000 Ns114p1646 Ns114p1647 qz220 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns114p1649 := nat_lit 1835707301632343900159295406832205822491446116160827555840 

noncomputable abbrev qz797 := (Real.log (Enclosure.sfrac Bool.false 543087459136 16000000))

noncomputable abbrev qz221 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 368472 4000) qz797) (@HMul.hMul Real Real Real qz339 qz343 (@HSub.hSub Real Real Real qz342 qz344 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz345 (@Nat.cast Real Real.instNatCast 736944))))))

noncomputable abbrev qz798 := (Enclosure.sfrac Bool.false 368472 2000)

noncomputable abbrev qz565 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz221 qz798) (@HMul.hMul Real Real Real qz5 qz798 (Real.log Real.pi)))

noncomputable def Ns114p1650 := @Enclosure.Real.IsNear.addLit_ft_p qz565 (Enclosure.sfrac Bool.true Ns114p1646 Ns114p1647) 254672438170422246367 450359962737049600 4412456753935483 230400000000000000000 Ns114p1646 Ns114p1647 0 1 Ns114p1649 

noncomputable def Ns114p1651 := nat_lit 10681736261079547096260935680000 

noncomputable abbrev qz566 := (@HSub.hSub Real Real Real qz12 qz221 qz798)

noncomputable abbrev qz567 := (@HMul.hMul Real Real Real qz5 qz798 (Real.log Real.pi))

noncomputable def Ns114p1652 := @Enclosure.Real.IsNear.subLit_ff_p qz566 qz567 1748267795290360146779 2251799813685248000 14705939987411 1800000000000000000 1769161240899 8388608000 46059 4194304000 Ns114p1651 254672438170422246367 450359962737049600 

noncomputable def Ns114p1653 := nat_lit 3496535590580720293558000 

noncomputable abbrev qz568 := qz798

noncomputable def Ns114p1654 := @Enclosure.Real.IsNear.subLit_ff_p qz221 qz568 2163130385764475497307 2251799813685248000 14705939987411 1800000000000000000 368472 2000 0 1 Ns114p1653 1748267795290360146779 2251799813685248000 14705939987411 1800000000000000000 

noncomputable def Ns114p1655 := nat_lit 4870936599641344557463319909169627136 

noncomputable def Ns114p1656 := nat_lit 12612042347420945416716288 

noncomputable def Ns114p1657 := nat_lit 3417871112297360417599488 

noncomputable def Ns114p1658 := BSN.log_dyadic_bound 18799459136 1067375459136 2 1 Ns114p1657 33554432 11520000 353419663806133866496 353419663806133866496 1182096 1086174918272 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 18799459136) (BSN.artanhQ 1067375459136) 0 1 353419663806133866496 Ns114p1657 353419663806133866496 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns114p1659 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 368472 4000) qz797 368472 4000 0 1 46983519000638073 4503599627370496 156250027 1800000000000000 2164013901650389004307 2251799813685248000 2398906664531 300000000000000000 (Enclosure.Real.IsNear.const Bool.false 368472 4000) (BSN.isNear_log_sfrac 543087459136 16000000 46983519000638073 4503599627370496 156250027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 543087459136) qz350)) Bool.false Ns114p1656 Ns114p85 1000000172800000 11520000000000000000000 46983519000638073 4503599627370496 156250027 1800000000000000 (BSN.log_rat_reduce_isNear 543087459136 16000000 15 1086174918272 1048576000000 1182096 33554432 24973259072661432 36028797018963968 11520000 1000000000000000 rfl rfl rfl rfl (Ns114p1658 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p1660 := BSN.arctan_dyadic_bound_f 1000 736944 1 0 4194304 1440000 0 1 1 0 1 1 5691 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 736944) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 736944) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz799 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 736944)))

noncomputable def Ns114p1661 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz799 884279719003555 562949953421312 1 2000000000000000 5691 4194304 1 1440000 3705734214350566064128 883515885913507 562949953421312 12500000009 18000000000000000 qz16 (Ns114p1660 rfl) rfl rfl 

noncomputable def Ns114p1662 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 368472 4000) qz797) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz799)) 2164013901650389004307 2251799813685248000 2398906664531 300000000000000000 883515885913507 2251799813685248 12500000009 72000000000000000 Ns114p1655 2163130385764475497307 2251799813685248000 14705939987411 1800000000000000000 (Ns114p1659 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz799) 1 4 0 1 883515885913507 562949953421312 12500000009 18000000000000000 883515885913507 2251799813685248 12500000009 72000000000000000 qz353 Ns114p1661 rfl) 

noncomputable def Ns114p1663 := @Ns114p1650 Ns114p1644 Ns114p1645 4412456753935483 230400000000000000000 (@Ns114p1652 4412456753935483 230400000000000000000 (Ns114p1654 (Ns114p1662 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 368472 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz568 (Real.log Real.pi) 368472 2000 0 1 38410761 33554432 1 16777216 1769161240899 8388608000 46059 4194304000 (Enclosure.Real.IsNear.const Bool.false 368472 2000) RS115to132.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns114p1646 Ns114p1647) 

noncomputable def Ns114p1664 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz217) Bool.false Ns114p1644 Ns114p1645 4412456753935483 230400000000000000000 4743640021 8388608 81 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz217) (@HAdd.hAdd Real Real Real qz354 qz565 (Enclosure.sfrac Bool.true Ns114p1646 Ns114p1647)) Bool.false Ns114p1644 Ns114p1645 4412456753935483 230400000000000000000 Ns114p1648 (Ns114p1663 rfl rfl)) 

noncomputable def Ns114p1665 := nat_lit 1898104772849149570711552 

noncomputable def Ns114p1666 := nat_lit 139731584443607933677781743643168750986575367708049417880963443202570092834864448903105 

noncomputable def Ns114p1667 := nat_lit 280235432221028062806001137416292878530362827824979227569299045866716528063000582081 

noncomputable def Ns114p1668 := nat_lit 365509959033472447530599612462006064113886327990317556653125390884851749712542984280001 

noncomputable def Ns114p1669 := BSN.sin_dyadic_bound_f 26973691161 17179869184 3 2 8388608 2882813 Ns114p1666 Ns114p98 Ns114p1667 Ns114p1668 Ns114p101 Ns114p1667 8388605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26973691161) qz355 0 2 Ns114p1666 Ns114p98 Ns114p1667 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26973691161) qz356 0 2 Ns114p1668 Ns114p101 Ns114p1667 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1670 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz217) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4743640021) qz357) Bool.false 4743640021 8388608 81 4194304 Bool.false 8388605 8388608 1 1440000 (Ns114p1664 rfl) (Enclosure.sfrac_false_div 4743640021 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4743640021) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns114p1665) qz358) 226375608064910080 72057594037927936 Bool.false 8388605 8388608 89 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q3 4743640021 8388608 226375608064910080 72057594037927936 89 Ns114p1665 Ns114p85 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388605 8388608 Ns114p1665 Ns114p85 26973691161 17179869184 2882813 2880000 (Ns114p1669 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p1671 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz217) Bool.false Ns114p1644 Ns114p1645 4412456753935483 230400000000000000000 37949120173 67108864 1286 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz217) (@HAdd.hAdd Real Real Real qz354 qz565 (Enclosure.sfrac Bool.true Ns114p1646 Ns114p1647)) Bool.false Ns114p1644 Ns114p1645 4412456753935483 230400000000000000000 Ns114p1648 (Ns114p1663 rfl rfl)) 

noncomputable def Ns114p1672 := Ns114p1643 25269 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 197 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 39744754 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 102 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 60223806 67108864) qz220 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz217) qz217 1) Bool.false 8388605 8388608 472009 23592960000 67108840 67108864 1343 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz217) qz217 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz217)) Bool.false 8388605 8388608 472009 23592960000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz217) qz217) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz217)) Bool.false 8388605 8388608 120834304 6039797760000 8388605 8388608 472009 23592960000 (Ns114p1670 rfl rfl) rfl)) rfl) (Ns114p1671 rfl) RS115to132.d7 

noncomputable def Ns114p1673 := nat_lit 200799138773592644238884473052460416780039966377405469201017470145 

noncomputable def Ns114p1674 := nat_lit 10717035278143873531198003642651220636559410756215517621910721 

noncomputable def Ns114p1675 := nat_lit 525885154921339930544694537417212989590502625275789975164610280641 

noncomputable def Ns114p1676 := BSN.sin_dyadic_bound_f 42536263 67108864 3 2 67108864 33554432 Ns114p1673 Ns114p107 Ns114p1674 Ns114p1675 Ns114p110 Ns114p1674 39744754 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 42536263) qz359 0 2 Ns114p1673 Ns114p107 Ns114p1674 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 42536263) (BSN.sinOddQ 67108864) 0 2 Ns114p1675 Ns114p110 Ns114p1674 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1677 := nat_lit 30131083760904002187961805318899383927599001273759963781988780481 

noncomputable def Ns114p1678 := nat_lit 781896562649992175703288685380454420223251779424606547249601 

noncomputable def Ns114p1679 := nat_lit 90391687489586706579534009379327390873956557317721042132871842241 

noncomputable def Ns114p1680 := BSN.cos_dyadic_bound_f 30665049 67108864 3 2 67108864 33554432 Ns114p1677 Ns114p113 Ns114p1678 Ns114p1679 Ns114p116 Ns114p1678 60223806 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 30665049) qz360 0 2 Ns114p1677 Ns114p113 Ns114p1678 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 30665049) (BSN.cosOddQ 67108864) 0 2 Ns114p1679 Ns114p116 Ns114p1678 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1681 := nat_lit 431576545989075784493700325640824803514025084934149933298935653354779288140524592463967531755992190976 

noncomputable def Ns114p1682 := nat_lit 144568396579341375363216071932365585111651864004643602588215208467884173610812447923090186244096 

noncomputable def Ns114p1683 := nat_lit 2615545934553386224267096716564314167654801351048706852706007268060136913841774801067855940797988802560 

noncomputable def Ns114p1684 := BSN.cos_dyadic_bound_f 85115002 67108864 4 3 67108864 33554432 Ns114p1681 Ns114p371 Ns114p1682 Ns114p1683 Ns114p374 Ns114p1682 19991214 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 85115002) qz360 0 3 Ns114p1681 Ns114p371 Ns114p1682 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 85115002) (BSN.cosOddQ 67108864) 0 3 Ns114p1683 Ns114p374 Ns114p1682 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1685 := nat_lit 629054887974718501780478862529102295485013539082469645113887876225 

noncomputable def Ns114p1686 := nat_lit 105154824435174238747758868913516739919400783204061367090865281 

noncomputable def Ns114p1687 := nat_lit 1647354455932320079705186363693217461072308810614613923561083036801 

noncomputable def Ns114p1688 := BSN.sin_dyadic_bound_f 56588561 67108864 3 2 67108864 33554432 Ns114p1685 Ns114p107 Ns114p1686 Ns114p1687 Ns114p110 Ns114p1686 50116808 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 56588561) qz359 0 2 Ns114p1685 Ns114p107 Ns114p1686 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 56588561) (BSN.sinOddQ 67108864) 0 2 Ns114p1687 Ns114p110 Ns114p1686 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1689 := Ns114p1641 42911 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 34 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 19991214 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 17 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 50116808 67108864) qz220 rfl rfl (Ns114p1672 RS115to132.d9 RS115to132.d11 RS115to132.d13 RS115to132.d17 (Ns114p1676 rfl rfl) (Ns114p1680 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns114p1671 rfl) RS115to132.d19 RS115to132.d21 RS115to132.d23 RS115to132.d25 RS115to132.d17 (Ns114p1684 rfl rfl) (Ns114p1688 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns114p1690 := nat_lit 36497030065636268642162696725896929714840887267347038208000000000 

noncomputable def Ns114p1691 := nat_lit 1147176091270146443283741553613945769003010560000000000000000 

noncomputable def Ns114p1692 := nat_lit 109488795844726265633601522694583561252984655780921114624000000000 

noncomputable def Ns114p1693 := BSN.cos_dyadic_bound_f 32170200 67108864 3 2 67108864 33554432 Ns114p1690 Ns114p113 Ns114p1691 Ns114p1692 Ns114p116 Ns114p1691 59544629 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 32170200) qz360 0 2 Ns114p1690 Ns114p113 Ns114p1691 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 32170200) (BSN.cosOddQ 67108864) 0 2 Ns114p1692 Ns114p116 Ns114p1691 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1694 := nat_lit 197300593769203601420039100256181338298376406081408133775782545921 

noncomputable def Ns114p1695 := nat_lit 33515952094206514699263933640646731204048570557610849780861441 

noncomputable def Ns114p1696 := nat_lit 591834749403422391230718772901262721432721121103109179627785914881 

noncomputable def Ns114p1697 := BSN.cos_dyadic_bound_f 49051969 67108864 3 2 67108864 33554432 Ns114p1694 Ns114p113 Ns114p1695 Ns114p1696 Ns114p116 Ns114p1695 49966107 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 49051969) qz360 0 2 Ns114p1694 Ns114p113 Ns114p1695 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 49051969) (BSN.cosOddQ 67108864) 0 2 Ns114p1696 Ns114p116 Ns114p1695 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1698 := Ns114p1639 57847 BSN.abs_quadSignPos (BSN.cos_quad_nat0 60 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 59544629 67108864) BSN.abs_quadSignPos qz734 (BSN.sfrac_eq_quadSignPos_mul Bool.false 49966107 67108864) qz220 rfl rfl (Ns114p1689 rfl rfl) (Ns114p1671 rfl) RS115to132.d27 RS115to132.d29 RS115to132.d31 RS115to132.d33 RS115to132.d17 (Ns114p1693 rfl rfl) (Ns114p1697 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns114p1699 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz217) qz217 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz217) qz217 7) 15020705 67108864 57847 67108864 15020705 67108864 57847 67108864 2016044898058240 15020705 33554432 57847 33554432 (Ns114p1698 rfl) 

noncomputable def Ns114p1700 := @Enclosure.Real.IsNear.mulLit_tf qz795 (Zeta.RiemannSiegel.correction qz219) 3031333 8388608 1 8388608 15045508008025 35184372088832 9516205178813 98956046499840000 45607944926490447325 295147905179352825856 

noncomputable abbrev qz800 := (@HPow.hPow Real Real Real qz7 qz218 qz9)

noncomputable def Ns114p1701 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz800 1 1 0 1 3031333 8388608 1 8388608 3031333 8388608 1 8388608 

noncomputable def Ns114p1702 := @Enclosure.Real.IsNear.sqrt_image qz218 61492864251 1048576000 46059 1048576000 32119749 32119774 4194304 (@Enclosure.Real.IsNear.of_eq qz218 (@HMul.hMul Real Real Real qz5 qz217 qz3) Bool.false 61492864251 1048576000 46059 1048576000 (BSN.t_div_two_pi_mk qz217 368472 1000 qz220) (@Enclosure.Real.IsNear.mulLit_ff qz217 qz3 368472 1000 0 1 1335089 8388608 1 8388608 61492864251 1048576000 46059 1048576000 (Enclosure.Real.IsNear.const Bool.false 368472 1000) RS115to132.d36 rfl)) 

noncomputable abbrev qz950 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 368472 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz801 := qz950

noncomputable abbrev qz569 := qz801

noncomputable abbrev qz222 := qz569

noncomputable def Ns114p1703 := @Enclosure.Real.IsNear.sqrt_image qz222 64239523 8388608 25 8388608 11606894 11606899 4194304 (@Enclosure.Real.IsNear.recentre' qz222 Bool.false 64239523 8388608 25 8388608 64239523 8388608 25 8388608 (Ns114p1702 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns114p1704 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz222) 23213793 8388608 5 8388608 1515666 1515667 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz222) Bool.false 23213793 8388608 5 8388608 23213793 8388608 5 8388608 (Ns114p1703 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns114p1705 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz222)) Bool.false 3031333 8388608 1 8388608 3031333 8388608 1 8388608 (Ns114p1704 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz223 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz563))

noncomputable abbrev qz802 := (@HMul.hMul Real Real Real qz884 qz949 qz949)

noncomputable abbrev qz570 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz802 qz794) qz642)

noncomputable abbrev qz224 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz570))

noncomputable def Ns114p1706 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz219) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz223) qz224) Bool.false 15045508008025 

noncomputable def Ns114p1707 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz223) qz224 15344965 8388608 549 

noncomputable abbrev qz803 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz223))

noncomputable def Ns114p1708 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz223) (@Neg.neg Real Real.instNeg qz803) Bool.true 15344965 8388608 549 8388608 (BSN.inv_eq_neg_inv_neg qz223) 

noncomputable def Ns114p1709 := @Enclosure.Real.IsNear.recentre' qz803 Bool.false 15344965 8388608 549 8388608 15344965 8388608 

noncomputable def Ns114p1710 := @Enclosure.Real.IsNear.recentre' qz223 Bool.true 4585787 8388608 117954304 6039797760000 4585787 8388608 460759 23592960000 

noncomputable abbrev qz225 := (@HMul.hMul Real Real Real qz339 qz337 qz563)

noncomputable def Ns114p1711 := @Enclosure.Real.IsNear.cos_image qz225 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 34678577) qz357) Bool.false 34678577 8388608 79 4194304 Bool.true 4585787 8388608 1 

noncomputable def Ns114p1712 := nat_lit 674651885273511278905008239 

noncomputable def Ns114p1713 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz219 884279719003555 140737488355328 1 500000000000000 5519267 8388608 25 8388608 4880575871865593994185 1180591620717411303424 Ns114p1712 

noncomputable def Ns114p1714 := @Enclosure.Real.IsNear.subLit_ff_p qz222 qz1 64239523 8388608 25 8388608 7 1 0 1 5519267 5519267 8388608 25 

noncomputable def Ns114p1715 := @Ns114p1714 8388608 (@Enclosure.Real.IsNear.recentre' qz222 Bool.false 64239523 8388608 25 8388608 64239523 8388608 25 8388608 (Ns114p1702 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns114p1716 := @Enclosure.Real.IsNear.recentre' qz225 Bool.false 4880575871865593994185 1180591620717411303424 Ns114p1712 Ns114p501 34678577 8388608 79 4194304 (@Ns114p1713 Ns114p501 RS115to132.d35 (Ns114p1715 rfl rfl) rfl) 

noncomputable def Ns114p1717 := nat_lit 12373529354164615906999800652485455315149942162801547991029172399115360798535162086561 

noncomputable def Ns114p1718 := nat_lit 7140168097921441643859293693374166313027632661028371527158045915627486245468062881 

noncomputable def Ns114p1719 := nat_lit 37106307726298004837711683370069617612823771223082587230033201105514827423114550133921 

noncomputable def Ns114p1720 := BSN.cos_dyadic_bound_f 17049574877 17179869184 3 2 8388608 2882813 Ns114p1717 Ns114p1309 Ns114p1718 Ns114p1719 Ns114p1312 Ns114p1718 4585787 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 17049574877) qz454 0 2 Ns114p1717 Ns114p1309 Ns114p1718 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 17049574877) qz455 0 2 Ns114p1719 Ns114p1312 Ns114p1718 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1721 := @Ns114p1711 1440000 (Ns114p1716 rfl) (Enclosure.sfrac_false_div 34678577 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 34678577) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1199757172921711265316864) qz358) 226375608064910080 72057594037927936 Bool.false 4585787 8388608 0 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q2 34678577 8388608 226375608064910080 72057594037927936 0 1199757172921711265316864 Ns114p85 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 4585787 8388608 1199757172921711265316864 Ns114p85 17049574877 17179869184 2882813 2880000 (Ns114p1720 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p1722 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz223) 4585787 8388608 460759 23592960000 7672208 7672757 4194304 (@Enclosure.Real.IsNear.neg qz223 Bool.true 4585787 8388608 460759 23592960000 (Ns114p1710 (Ns114p1721 rfl rfl) rfl)) 

noncomputable def Ns114p1723 := Ns114p1708 (@Enclosure.Real.IsNear.neg qz803 Bool.false 15344965 8388608 549 8388608 (@Ns114p1709 549 8388608 (Ns114p1722 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p1724 := @Enclosure.Real.IsNear.recentre' qz224 Bool.true 980485 4194304 

noncomputable abbrev qz226 := (@HMul.hMul Real Real Real qz339 qz337 qz570)

noncomputable def Ns114p1725 := @Enclosure.Real.IsNear.cos_image qz226 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7578039)) qz366) Bool.true 7578039 4194304 

noncomputable def Ns114p1726 := nat_lit 17893139785758305891991756805 

noncomputable def Ns114p1727 := nat_lit 13106574841326114332956996311853617 

noncomputable def Ns114p1728 := @Enclosure.Real.IsNear.recentre' qz226 Bool.true Ns114p1726 Ns114p517 Ns114p1727 

noncomputable abbrev qz227 := qz570

noncomputable def Ns114p1729 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz227 884279719003555 140737488355328 1 500000000000000 20234705604151 

noncomputable abbrev qz571 := (@HSub.hSub Real Real Real qz634 qz802 qz794)

noncomputable abbrev qz228 := qz571

noncomputable def Ns114p1730 := @Enclosure.Real.IsNear.subLit_tf qz228 qz26 15836659093047 70368744177664 485679175 70368744177664 1 16 

noncomputable abbrev qz572 := qz802

noncomputable abbrev qz229 := qz572

noncomputable def Ns114p1731 := @Enclosure.Real.IsNear.subLit_ff_n qz229 qz219 30462308217289 70368744177664 275963975 70368744177664 5519267 8388608 25 8388608 

noncomputable def Ns114p1732 := @Enclosure.Real.IsNear.mulLit_ff qz219 qz219 5519267 8388608 25 8388608 5519267 8388608 25 8388608 30462308217289 70368744177664 

noncomputable def Ns114p1733 := nat_lit 6344255809219537139778848778115071049292790308453577972386503891801461693767789877087201 

noncomputable def Ns114p1734 := nat_lit 35865924690268505933765216480898731551992298244160310334019399531843364921233329121 

noncomputable def Ns114p1735 := nat_lit 38326581329069392388556182377106019241381356708691126070312097577866867295257535269784545 

noncomputable def Ns114p1736 := BSN.cos_dyadic_bound_t 7578039 4194304 4 3 4194304 1440000 Ns114p1733 Ns114p175 Ns114p1734 Ns114p1735 Ns114p178 Ns114p1734 980485 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 7578039) (BSN.cosEvenQ 4194304) 0 3 Ns114p1733 Ns114p175 Ns114p1734 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 7578039) (BSN.cosOddQ 4194304) 0 3 Ns114p1735 Ns114p178 Ns114p1734 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1737 := @Ns114p1724 533988608 12079595520000 980485 4194304 2085893 47185920000 (@Ns114p1725 365 8388608 Bool.true 980485 4194304 1 1440000 (@Ns114p1728 Ns114p520 7578039 4194304 365 8388608 (@Ns114p1729 70368744177664 485679175 70368744177664 Ns114p1726 Ns114p517 Ns114p1727 Ns114p520 RS115to132.d35 (@Ns114p1730 0 1 323755289666416 20234705604151 70368744177664 485679175 70368744177664 (@Ns114p1731 132847525161206808576 15836659093047 70368744177664 485679175 70368744177664 (@Ns114p1732 275963975 70368744177664 (Ns114p1715 rfl rfl) (Ns114p1715 rfl rfl) rfl) (Ns114p1715 rfl rfl) rfl rfl) qz370 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7578039 4194304) (BSN.cos_neg_of_bound 7578039 4194304 Bool.true 980485 4194304 1 1440000 (Ns114p1736 rfl rfl)) rfl rfl) 

noncomputable def Ns114p1738 := @Ns114p1700 57778223601568993709 Ns114p1635 (Ns114p1701 qz28 (@Enclosure.Real.IsNear.of_eq qz800 (@Inv.inv Real Real.instInv (Real.sqrt qz222)) Bool.false 3031333 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz218 (BSN.t_div_two_pi_nonneg qz217 368472 1000 qz220)) Ns114p1705) rfl) (@Ns114p1706 35184372088832 9516205178813 98956046499840000 (BSN.correction_mk qz219 (BSN.cos_two_pi_p_ne_zero_mk qz217 368472 1000 7 qz220 rfl rfl (@BSN.floor_sqrt_eq_dec qz217 368472 1000 7 qz220 rfl rfl rfl))) (@Ns114p1707 8388608 980485 4194304 2085893 47185920000 15045508008025 35184372088832 9516205178813 98956046499840000 Ns114p1723 (Ns114p1737 rfl) rfl)) 

noncomputable def Ns114p1739 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz217) (hardyZApproximantRS₀ qz217) Bool.false 177731463365635263965 295147905179352825856 2919933434539691233709 Ns114p1635 (@Eq.refl Real (hardyZApproximantRS₀ qz217)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz217) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz217) qz217 7) (@HMul.hMul Real Real Real qz5 qz795 (Zeta.RiemannSiegel.correction qz219))) Bool.false 177731463365635263965 295147905179352825856 2919933434539691233709 Ns114p1635 (BSN.hardyZApproximantRS₀_eq qz217 7 (@BSN.floor_sqrt_eq_dec qz217 368472 1000 7 qz220 rfl rfl rfl)) (@Ns114p1637 177731463365635263965 295147905179352825856 2919933434539691233709 Ns114p1635 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz217) qz217 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz217) qz217 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz217) qz217 7)) Bool.false 15020705 33554432 57847 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz217) qz217 7) (Ns114p1699 (Ns114p1698 rfl) rfl rfl)) (Ns114p1738 rfl) rfl rfl)) 

theorem RS115to132.d54 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz217) Bool.false 177731463365635263965 295147905179352825856 2919933434539691233709 Ns114p1635 := Ns114p1739 

noncomputable def Ns114p1740 := nat_lit 2656267863257018752040960 

noncomputable abbrev qz951 := (Enclosure.sfrac Bool.false 370015 1000)

noncomputable abbrev qz804 := qz951

noncomputable abbrev qz573 := qz804

noncomputable abbrev qz230 := qz573

noncomputable abbrev qz952 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 370015 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz805 := qz952

noncomputable abbrev qz574 := qz805

noncomputable abbrev qz231 := qz574

noncomputable abbrev qz953 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 370015 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz806 := qz953

noncomputable abbrev qz575 := qz806

noncomputable abbrev qz232 := qz575

noncomputable abbrev qz807 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz231 qz9))

noncomputable def Ns114p1741 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz230) qz230 7) (@HMul.hMul Real Real Real qz5 qz807 (Zeta.RiemannSiegel.correction qz232)) 619219 2097152 58085 33554432 1456746743217543921 9223372036854775808 19368609559008511 461168601842738790400 Ns114p1740 

noncomputable def Ns114p1742 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz230) qz230 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 370015 1000 60 96 67108864 33554432 1125899906842624 Bool.false 38160027532 1292 

noncomputable def Ns114p1743 := Ns114p1742 120242927 48 27397080 8 130587807 48 25364760 8 Bool.true 58230797 43086 Bool.true 6797677 Bool.true 39641596 3537118876014220 1 Bool.false 66764878 Bool.false Bool.false 55737118 Bool.false Bool.true 9907504 

noncomputable def Ns114p1744 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz230) qz230 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 370015 1000 35 17 67108864 33554432 1125899906842624 Bool.false 38160027532 1292 

noncomputable def Ns114p1745 := Ns114p1744 93032624 47 33554424 8 108007536 47 30011992 8 Bool.true 74392494 25369 Bool.false 47058665 Bool.true 12336830 3537118876014220 1 Bool.false 43295753 Bool.false Bool.false 12267460 Bool.true Bool.true 58230797 

noncomputable def Ns114p1746 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz230) qz230 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 370015 1000 198 103 67108864 33554432 1125899906842624 Bool.false 38160027532 1292 

noncomputable def Ns114p1747 := Ns114p1746 46516304 47 47453136 16 73726608 47 38745320 8 Bool.true 67108848 1343 Bool.false 76254608 Bool.false 22397895 3537118876014220 1 Bool.false 28250799 Bool.true Bool.false 21984379 Bool.false Bool.true 74392494 

noncomputable def Ns114p1748 := nat_lit 605688591074497738293114752728529243568538422830287 

noncomputable def Ns114p1749 := nat_lit 1065174107910544357992318396694055173938437160960 

noncomputable def Ns114p1750 := nat_lit 3329200089045665479981364500000000 

noncomputable def Ns114p1751 := nat_lit 7391130123980296492915964522805000000 

noncomputable abbrev qz808 := (@Eq.refl Real qz951)

noncomputable abbrev qz576 := qz808

noncomputable abbrev qz233 := qz576

noncomputable def Ns114p1752 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz230 370015 1000 547645400900 16000000 740030 4000 2000 Ns114p1750 Ns114p1751 qz233 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns114p1753 := nat_lit 3028442955372488691465573763642646217842692114151435000000 

noncomputable abbrev qz809 := (Real.log (Enclosure.sfrac Bool.false 547645400900 16000000))

noncomputable abbrev qz234 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 370015 4000) qz809) (@HMul.hMul Real Real Real qz339 qz343 (@HSub.hSub Real Real Real qz342 qz344 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz345 (@Nat.cast Real Real.instNatCast 740030))))))

noncomputable abbrev qz810 := (Enclosure.sfrac Bool.false 370015 2000)

noncomputable abbrev qz577 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz234 qz810) (@HMul.hMul Real Real Real qz5 qz810 (Real.log Real.pi)))

noncomputable def Ns114p1754 := @Enclosure.Real.IsNear.addLit_ft_p qz577 (Enclosure.sfrac Bool.true Ns114p1750 Ns114p1751) 409740500236665416767 720575940379279360 2363075570908897 122880000000000000000 Ns114p1750 Ns114p1751 0 1 Ns114p1753 

noncomputable def Ns114p1755 := nat_lit 27497219505674347267319922688000 

noncomputable abbrev qz578 := (@HSub.hSub Real Real Real qz12 qz234 qz810)

noncomputable abbrev qz579 := (@HMul.hMul Real Real Real qz5 qz810 (Real.log Real.pi))

noncomputable def Ns114p1756 := @Enclosure.Real.IsNear.subLit_ff_p qz578 qz579 2811733384295069293883 3602879701896396800 3937656916087 480000000000000000 2842511546283 13421772800 74003 6710886400 Ns114p1755 409740500236665416767 720575940379279360 

noncomputable def Ns114p1757 := nat_lit 5623466768590138587766000 

noncomputable abbrev qz580 := qz810

noncomputable def Ns114p1758 := @Enclosure.Real.IsNear.subLit_ff_p qz234 qz580 3478293150743666924859 3602879701896396800 3937656916087 480000000000000000 370015 2000 0 1 Ns114p1757 2811733384295069293883 3602879701896396800 3937656916087 480000000000000000 

noncomputable def Ns114p1759 := nat_lit 7832419868787263417292577524292780032 

noncomputable def Ns114p1760 := nat_lit 12622146083112958577082368 

noncomputable def Ns114p1761 := nat_lit 3447123647895120362430000 

noncomputable def Ns114p1762 := BSN.log_dyadic_bound 23357400900 1071933400900 2 1 Ns114p1761 33554432 11520000 545568176803320810000 545568176803320810000 1462531 1095290801800 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 23357400900) (BSN.artanhQ 1071933400900) 0 1 545568176803320810000 Ns114p1761 545568176803320810000 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns114p1763 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 370015 4000) qz809 370015 4000 0 1 47021158349189753 4503599627370496 156250027 1800000000000000 3479706781315089291259 3602879701896396800 11562970748081 1440000000000000000 (Enclosure.Real.IsNear.const Bool.false 370015 4000) (BSN.isNear_log_sfrac 547645400900 16000000 47021158349189753 4503599627370496 156250027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 547645400900) qz350)) Bool.false Ns114p1760 Ns114p85 1000000172800000 11520000000000000000000 47021158349189753 4503599627370496 156250027 1800000000000000 (BSN.log_rat_reduce_isNear 547645400900 16000000 15 1095290801800 1048576000000 1462531 33554432 24973259072661432 36028797018963968 11520000 1000000000000000 rfl rfl rfl rfl (Ns114p1762 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p1764 := BSN.arctan_dyadic_bound_f 1000 740030 1 0 4194304 1440000 0 1 1 0 1 1 5667 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 740030) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 740030) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz811 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 740030)))

noncomputable def Ns114p1765 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz811 884279719003555 562949953421312 1 2000000000000000 5667 4194304 1 1440000 3705747725149448175616 883519107138979 562949953421312 12500000009 18000000000000000 qz16 (Ns114p1764 rfl) rfl rfl 

noncomputable def Ns114p1766 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 370015 4000) qz809) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz811)) 3479706781315089291259 3602879701896396800 11562970748081 1440000000000000000 883519107138979 2251799813685248 12500000009 72000000000000000 Ns114p1759 3478293150743666924859 3602879701896396800 3937656916087 480000000000000000 (Ns114p1763 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz811) 1 4 0 1 883519107138979 562949953421312 12500000009 18000000000000000 883519107138979 2251799813685248 12500000009 72000000000000000 qz353 Ns114p1765 rfl) 

noncomputable def Ns114p1767 := @Ns114p1754 Ns114p1748 Ns114p1749 2363075570908897 122880000000000000000 (@Ns114p1756 2363075570908897 122880000000000000000 (Ns114p1758 (Ns114p1766 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 370015 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz580 (Real.log Real.pi) 370015 2000 0 1 38410761 33554432 1 16777216 2842511546283 13421772800 74003 6710886400 (Enclosure.Real.IsNear.const Bool.false 370015 2000) RS115to132.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns114p1750 Ns114p1751) 

noncomputable def Ns114p1768 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz230) Bool.false Ns114p1748 Ns114p1749 2363075570908897 122880000000000000000 4770003441 8388608 81 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz230) (@HAdd.hAdd Real Real Real qz354 qz577 (Enclosure.sfrac Bool.true Ns114p1750 Ns114p1751)) Bool.false Ns114p1748 Ns114p1749 2363075570908897 122880000000000000000 Ns114p1752 (Ns114p1767 rfl rfl)) 

noncomputable def Ns114p1769 := nat_lit 1899521530835591350976512 

noncomputable def Ns114p1770 := nat_lit 140150078207099128407169532528430335348321765240559262322120918386610040731349581889345 

noncomputable def Ns114p1771 := nat_lit 281913166952193860396968633218262843720588212422118056479177905259213784774656458561 

noncomputable def Ns114p1772 := nat_lit 366603297795908451006706064549249881308152242333733686371255164880225665311518508777281 

noncomputable def Ns114p1773 := BSN.sin_dyadic_bound_f 26993824503 17179869184 3 2 8388608 2882813 Ns114p1770 Ns114p98 Ns114p1771 Ns114p1772 Ns114p101 Ns114p1771 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26993824503) qz355 0 2 Ns114p1770 Ns114p98 Ns114p1771 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26993824503) qz356 0 2 Ns114p1772 Ns114p101 Ns114p1771 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1774 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz230) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4770003441) qz357) Bool.false 4770003441 8388608 81 4194304 Bool.true 8388606 8388608 1 1440000 (Ns114p1768 rfl) (Enclosure.sfrac_false_div 4770003441 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4770003441) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns114p1769) qz358) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 90 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q1 4770003441 8388608 226375608064910080 72057594037927936 90 Ns114p1769 Ns114p85 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388606 8388608 Ns114p1769 Ns114p85 26993824503 17179869184 2882813 2880000 (Ns114p1773 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p1775 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz230) Bool.false Ns114p1748 Ns114p1749 2363075570908897 122880000000000000000 38160027532 67108864 1292 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz230) (@HAdd.hAdd Real Real Real qz354 qz577 (Enclosure.sfrac Bool.true Ns114p1750 Ns114p1751)) Bool.false Ns114p1748 Ns114p1749 2363075570908897 122880000000000000000 Ns114p1752 (Ns114p1767 rfl rfl)) 

noncomputable def Ns114p1776 := Ns114p1747 25369 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 198 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 28250799 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 103 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 21984379 67108864) qz233 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz230) qz230 1) Bool.true 4194303 4194304 472009 23592960000 67108848 67108864 1343 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz230) qz230 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz230)) Bool.true 4194303 4194304 472009 23592960000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz230) qz230) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz230)) Bool.true 8388606 8388608 120834304 6039797760000 4194303 4194304 472009 23592960000 (Ns114p1774 rfl rfl) rfl)) rfl) (Ns114p1775 rfl) RS115to132.d7 

noncomputable def Ns114p1777 := nat_lit 277881722108019478936882732200127311665276989488417812996571678508811860712510206315891152589019938816 

noncomputable def Ns114p1778 := nat_lit 38653881794037424490386008619573977045029253430508666392401800110059840356616320812008274395136 

noncomputable def Ns114p1779 := nat_lit 1684701486398149247549792638730157480112547165769289696474566774550763280815438686085087155275106877440 

noncomputable def Ns114p1780 := BSN.cos_dyadic_bound_f 76254608 67108864 4 3 67108864 33554432 Ns114p1777 Ns114p371 Ns114p1778 Ns114p1779 Ns114p374 Ns114p1778 28250799 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 76254608) qz360 0 3 Ns114p1777 Ns114p371 Ns114p1778 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 76254608) (BSN.cosOddQ 67108864) 0 3 Ns114p1779 Ns114p374 Ns114p1778 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1781 := nat_lit 251668474988950916870782550625 

noncomputable def Ns114p1782 := BSN.sin_dyadic_bound_f 22397895 67108864 2 1 67108864 33554432 Ns114p1781 Ns114p231 Ns114p1781 Ns114p1781 Ns114p232 Ns114p1781 21984379 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 22397895) qz359 0 1 Ns114p1781 Ns114p231 Ns114p1781 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 22397895) (BSN.sinOddQ 67108864) 0 1 Ns114p1781 Ns114p232 Ns114p1781 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1783 := nat_lit 300811523876392088450676331494456184750680360064109702968812930625 

noncomputable def Ns114p1784 := nat_lit 24050096353342868008783950837155238596669534584728572437890625 

noncomputable def Ns114p1785 := nat_lit 787800767139311962251185694184125089675006335207150137705801090625 

noncomputable def Ns114p1786 := BSN.sin_dyadic_bound_f 47058665 67108864 3 2 67108864 33554432 Ns114p1783 Ns114p107 Ns114p1784 Ns114p1785 Ns114p110 Ns114p1784 43295753 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 47058665) qz359 0 2 Ns114p1783 Ns114p107 Ns114p1784 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 47058665) (BSN.sinOddQ 67108864) 0 2 Ns114p1785 Ns114p110 Ns114p1784 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1787 := nat_lit 23164040789138678578711210000 

noncomputable def Ns114p1788 := BSN.sin_dyadic_bound_f 12336830 67108864 2 1 67108864 33554432 Ns114p1787 Ns114p231 Ns114p1787 Ns114p1787 Ns114p232 Ns114p1787 12267460 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 12336830) qz359 0 1 Ns114p1787 Ns114p231 Ns114p1787 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 12336830) (BSN.sinOddQ 67108864) 0 1 Ns114p1787 Ns114p232 Ns114p1787 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1789 := Ns114p1745 43086 BSN.abs_quadSignPos (BSN.cos_quad_nat3 35 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 43295753 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 17 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 12267460 67108864) qz233 rfl rfl (Ns114p1776 RS115to132.d9 RS115to132.d11 RS115to132.d13 RS115to132.d17 (Ns114p1780 rfl rfl) (Ns114p1782 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns114p1775 rfl) RS115to132.d19 RS115to132.d21 RS115to132.d23 RS115to132.d25 RS115to132.d17 (Ns114p1786 rfl rfl) (Ns114p1788 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns114p1790 := nat_lit 2135217394672576594704276241 

noncomputable def Ns114p1791 := BSN.cos_dyadic_bound_f 6797677 67108864 2 1 67108864 33554432 Ns114p1790 Ns114p227 Ns114p1790 Ns114p1790 Ns114p228 Ns114p1790 66764878 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 6797677) qz360 0 1 Ns114p1790 Ns114p227 Ns114p1790 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 6797677) (BSN.cosOddQ 67108864) 0 1 Ns114p1790 Ns114p228 Ns114p1790 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1792 := nat_lit 84152074959266050197005978162670906003885363449248830730618863616 

noncomputable def Ns114p1793 := nat_lit 6098303709950054482270218920768984752684326380917568097550336 

noncomputable def Ns114p1794 := nat_lit 252444028270378250482053394050171180042150721694984657055661490176 

noncomputable def Ns114p1795 := BSN.cos_dyadic_bound_f 39641596 67108864 3 2 67108864 33554432 Ns114p1792 Ns114p113 Ns114p1793 Ns114p1794 Ns114p116 Ns114p1793 55737118 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 39641596) qz360 0 2 Ns114p1792 Ns114p113 Ns114p1793 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 39641596) (BSN.cosOddQ 67108864) 0 2 Ns114p1794 Ns114p116 Ns114p1793 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1796 := Ns114p1743 58085 BSN.abs_quadSignPos (BSN.cos_quad_nat0 60 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66764878 67108864) BSN.abs_quadSignPos qz734 (BSN.sfrac_eq_quadSignPos_mul Bool.false 55737118 67108864) qz233 rfl rfl (Ns114p1789 rfl rfl) (Ns114p1775 rfl) RS115to132.d27 RS115to132.d29 RS115to132.d31 RS115to132.d33 RS115to132.d17 (Ns114p1791 rfl rfl) (Ns114p1795 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns114p1797 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz230) qz230 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz230) qz230 7) 9907504 67108864 58085 67108864 9907504 67108864 58085 67108864 1329762677030912 619219 2097152 58085 33554432 (Ns114p1796 rfl) 

noncomputable def Ns114p1798 := @Enclosure.Real.IsNear.mulLit_tf qz807 (Zeta.RiemannSiegel.correction qz232) 378521 1048576 1 4194304 3848522917401 8796093022208 382815423623 3298534883328000 1456746743217543921 9223372036854775808 

noncomputable abbrev qz812 := (@HPow.hPow Real Real Real qz7 qz231 qz9)

noncomputable def Ns114p1799 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz812 1 1 0 1 378521 1048576 1 4194304 378521 1048576 1 4194304 

noncomputable def Ns114p1800 := @Enclosure.Real.IsNear.sqrt_image qz231 98800591267 1677721600 74003 1677721600 32186930 32186955 4194304 (@Enclosure.Real.IsNear.of_eq qz231 (@HMul.hMul Real Real Real qz5 qz230 qz3) Bool.false 98800591267 1677721600 74003 1677721600 (BSN.t_div_two_pi_mk qz230 370015 1000 qz233) (@Enclosure.Real.IsNear.mulLit_ff qz230 qz3 370015 1000 0 1 1335089 8388608 1 8388608 98800591267 1677721600 74003 1677721600 (Enclosure.Real.IsNear.const Bool.false 370015 1000) RS115to132.d36 rfl)) 

noncomputable abbrev qz954 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 370015 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz813 := qz954

noncomputable abbrev qz581 := qz813

noncomputable abbrev qz235 := qz581

noncomputable def Ns114p1801 := @Enclosure.Real.IsNear.sqrt_image qz235 64373885 8388608 25 8388608 11619026 11619031 4194304 (@Enclosure.Real.IsNear.recentre' qz235 Bool.false 64373885 8388608 25 8388608 64373885 8388608 25 8388608 (Ns114p1800 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns114p1802 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz235) 23238057 8388608 5 8388608 1514083 1514085 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz235) Bool.false 23238057 8388608 5 8388608 23238057 8388608 5 8388608 (Ns114p1801 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns114p1803 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz235)) Bool.false 3028168 8388608 2 8388608 378521 1048576 1 4194304 (Ns114p1802 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz236 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz575))

noncomputable abbrev qz814 := (@HMul.hMul Real Real Real qz884 qz953 qz953)

noncomputable abbrev qz582 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz814 qz806) qz642)

noncomputable abbrev qz237 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz582))

noncomputable def Ns114p1804 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz232) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz236) qz237) Bool.false 3848522917401 

noncomputable def Ns114p1805 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz236) qz237 4561261 2097152 97 

noncomputable abbrev qz815 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz236))

noncomputable def Ns114p1806 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz236) (@Neg.neg Real Real.instNeg qz815) Bool.true 4561261 2097152 97 1048576 (BSN.inv_eq_neg_inv_neg qz236) 

noncomputable def Ns114p1807 := @Enclosure.Real.IsNear.recentre' qz815 Bool.false 18245044 8388608 776 8388608 4561261 2097152 

noncomputable def Ns114p1808 := @Enclosure.Real.IsNear.recentre' qz236 Bool.true 3856869 8388608 117954304 6039797760000 3856869 8388608 460759 23592960000 

noncomputable abbrev qz238 := (@HMul.hMul Real Real Real qz339 qz337 qz575)

noncomputable def Ns114p1809 := @Enclosure.Real.IsNear.cos_image qz238 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17761399) qz366) Bool.false 17761399 4194304 79 4194304 Bool.true 3856869 8388608 1 

noncomputable def Ns114p1810 := nat_lit 674651885274665439696658543 

noncomputable def Ns114p1811 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz232 884279719003555 140737488355328 1 500000000000000 5653629 8388608 25 8388608 4999389463470349651095 1180591620717411303424 Ns114p1810 

noncomputable def Ns114p1812 := @Enclosure.Real.IsNear.subLit_ff_p qz235 qz1 64373885 8388608 25 8388608 7 1 0 1 5653629 5653629 8388608 25 

noncomputable def Ns114p1813 := @Ns114p1812 8388608 (@Enclosure.Real.IsNear.recentre' qz235 Bool.false 64373885 8388608 25 8388608 64373885 8388608 25 8388608 (Ns114p1800 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns114p1814 := @Enclosure.Real.IsNear.recentre' qz238 Bool.false 4999389463470349651095 1180591620717411303424 Ns114p1810 Ns114p501 17761399 4194304 79 4194304 (@Ns114p1811 Ns114p501 RS115to132.d35 (Ns114p1813 rfl rfl) rfl) 

noncomputable def Ns114p1815 := nat_lit 18213977511325220604790693411986238826020263134497308765418064247426266977936112190625 

noncomputable def Ns114p1816 := nat_lit 15463026256087838041323554424804396013026703657791504715239898612981662307875390625 

noncomputable def Ns114p1817 := nat_lit 54611006481463486138289433127109107686034735996176343286823712945052837609192585790625 

noncomputable def Ns114p1818 := BSN.cos_dyadic_bound_f 18778539485 17179869184 3 2 8388608 2882813 Ns114p1815 Ns114p1309 Ns114p1816 Ns114p1817 Ns114p1312 Ns114p1816 3856869 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 18778539485) qz454 0 2 Ns114p1815 Ns114p1309 Ns114p1816 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 18778539485) qz455 0 2 Ns114p1817 Ns114p1312 Ns114p1816 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1819 := @Ns114p1809 1440000 (Ns114p1814 rfl) (Enclosure.sfrac_false_div 17761399 4194304) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17761399) qz366) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 660711120557149192716288) qz380) 226375608064910080 72057594037927936 Bool.false 3856869 8388608 0 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q2 17761399 4194304 226375608064910080 72057594037927936 0 660711120557149192716288 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 3856869 8388608 660711120557149192716288 604462909807314587353088 18778539485 17179869184 2882813 2880000 (Ns114p1818 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p1820 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz236) 3856869 8388608 460759 23592960000 9122134 9122910 4194304 (@Enclosure.Real.IsNear.neg qz236 Bool.true 3856869 8388608 460759 23592960000 (Ns114p1808 (Ns114p1819 rfl rfl) rfl)) 

noncomputable def Ns114p1821 := Ns114p1806 (@Enclosure.Real.IsNear.neg qz815 Bool.false 4561261 2097152 97 1048576 (@Ns114p1807 97 1048576 (Ns114p1820 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p1822 := @Enclosure.Real.IsNear.recentre' qz237 Bool.true 843741 4194304 

noncomputable abbrev qz239 := (@HMul.hMul Real Real Real qz339 qz337 qz582)

noncomputable def Ns114p1823 := @Enclosure.Real.IsNear.cos_image qz239 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7437935)) qz366) Bool.true 7437935 4194304 

noncomputable def Ns114p1824 := nat_lit 17562328528416283973525126725 

noncomputable def Ns114p1825 := nat_lit 2657573998905679923737420901486553 

noncomputable def Ns114p1826 := @Enclosure.Real.IsNear.recentre' qz239 Bool.true Ns114p1824 Ns114p517 Ns114p1825 

noncomputable def Ns114p1827 := nat_lit 60446290980731458735308800000000000000 

noncomputable abbrev qz240 := qz582

noncomputable def Ns114p1828 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz240 884279719003555 140737488355328 1 500000000000000 19860603099895 

noncomputable abbrev qz583 := (@HSub.hSub Real Real Real qz634 qz814 qz806)

noncomputable abbrev qz241 := qz583

noncomputable def Ns114p1829 := @Enclosure.Real.IsNear.subLit_tf qz241 qz26 15462556588791 70368744177664 492397275 70368744177664 1 16 

noncomputable abbrev qz584 := qz814

noncomputable abbrev qz242 := qz584

noncomputable def Ns114p1830 := @Enclosure.Real.IsNear.subLit_ff_n qz242 qz232 31963520869641 70368744177664 282682075 70368744177664 5653629 8388608 25 8388608 

noncomputable def Ns114p1831 := @Enclosure.Real.IsNear.mulLit_ff qz232 qz232 5653629 8388608 25 8388608 5653629 8388608 25 8388608 31963520869641 70368744177664 

noncomputable def Ns114p1832 := nat_lit 5885259129485917057438843237938955874980748944075628733354459150432143332367768191890625 

noncomputable def Ns114p1833 := nat_lit 28670056245862672594971013820083635455421514679474888549351398033945231465087890625 

noncomputable def Ns114p1834 := nat_lit 35564465625700381106262682037118270226370284959793341617244443945764953840152949785490625 

noncomputable def Ns114p1835 := BSN.cos_dyadic_bound_t 7437935 4194304 4 3 4194304 1440000 Ns114p1832 Ns114p175 Ns114p1833 Ns114p1834 Ns114p178 Ns114p1833 843741 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 7437935) (BSN.cosEvenQ 4194304) 0 3 Ns114p1832 Ns114p175 Ns114p1833 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 7437935) (BSN.cosOddQ 4194304) 0 3 Ns114p1834 Ns114p178 Ns114p1833 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1836 := @Ns114p1822 270594304 6039797760000 843741 4194304 1057009 23592960000 (@Ns114p1823 185 4194304 Bool.true 843741 4194304 1 1440000 (@Ns114p1826 Ns114p1827 7437935 4194304 185 4194304 (@Ns114p1828 70368744177664 492397275 70368744177664 Ns114p1824 Ns114p517 Ns114p1825 Ns114p1827 RS115to132.d35 (@Ns114p1829 0 1 317769649598320 19860603099895 70368744177664 492397275 70368744177664 (@Ns114p1830 129709325901184892928 15462556588791 70368744177664 492397275 70368744177664 (@Ns114p1831 282682075 70368744177664 (Ns114p1813 rfl rfl) (Ns114p1813 rfl rfl) rfl) (Ns114p1813 rfl rfl) rfl rfl) qz370 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7437935 4194304) (BSN.cos_neg_of_bound 7437935 4194304 Bool.true 843741 4194304 1 1440000 (Ns114p1835 rfl rfl)) rfl rfl) 

noncomputable def Ns114p1837 := @Ns114p1798 19368609559008511 461168601842738790400 (Ns114p1799 qz28 (@Enclosure.Real.IsNear.of_eq qz812 (@Inv.inv Real Real.instInv (Real.sqrt qz235)) Bool.false 378521 1048576 1 4194304 (BSN.rpow_neg_quarter_mk qz231 (BSN.t_div_two_pi_nonneg qz230 370015 1000 qz233)) Ns114p1803) rfl) (@Ns114p1804 8796093022208 382815423623 3298534883328000 (BSN.correction_mk qz232 (BSN.cos_two_pi_p_ne_zero_mk qz230 370015 1000 7 qz233 rfl rfl (@BSN.floor_sqrt_eq_dec qz230 370015 1000 7 qz233 rfl rfl rfl))) (@Ns114p1805 1048576 843741 4194304 1057009 23592960000 3848522917401 8796093022208 382815423623 3298534883328000 Ns114p1821 (Ns114p1836 rfl) rfl)) 

noncomputable def Ns114p1838 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz230) (hardyZApproximantRS₀ qz230) Bool.true 1266607219341763855 9223372036854775808 817682770801120511 461168601842738790400 (@Eq.refl Real (hardyZApproximantRS₀ qz230)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz230) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz230) qz230 7) (@HMul.hMul Real Real Real qz5 qz807 (Zeta.RiemannSiegel.correction qz232))) Bool.true 1266607219341763855 9223372036854775808 817682770801120511 461168601842738790400 (BSN.hardyZApproximantRS₀_eq qz230 7 (@BSN.floor_sqrt_eq_dec qz230 370015 1000 7 qz233 rfl rfl rfl)) (@Ns114p1741 1266607219341763855 9223372036854775808 817682770801120511 461168601842738790400 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz230) qz230 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz230) qz230 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz230) qz230 7)) Bool.true 619219 2097152 58085 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz230) qz230 7) (Ns114p1797 (Ns114p1796 rfl) rfl rfl)) (Ns114p1837 rfl) rfl rfl)) 

theorem RS115to132.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz230) Bool.true 1266607219341763855 9223372036854775808 817682770801120511 461168601842738790400 := Ns114p1838 

noncomputable def Ns114p1839 := nat_lit 18303046454151134952030208 

noncomputable abbrev qz955 := (Enclosure.sfrac Bool.false 371556 1000)

noncomputable abbrev qz816 := qz955

noncomputable abbrev qz585 := qz816

noncomputable abbrev qz243 := qz585

noncomputable abbrev qz956 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 371556 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz817 := qz956

noncomputable abbrev qz586 := qz817

noncomputable abbrev qz244 := qz586

noncomputable abbrev qz957 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 371556 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz818 := qz957

noncomputable abbrev qz587 := qz818

noncomputable abbrev qz245 := qz587

noncomputable abbrev qz819 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz244 qz9))

noncomputable def Ns114p1840 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz243) qz243 7) (@HMul.hMul Real Real Real qz5 qz819 (Zeta.RiemannSiegel.correction qz245)) 62144777 8388608 7291 4194304 46614885756598765 288230376151711744 2449095940924342643 46116860184273879040000 Ns114p1839 

noncomputable def Ns114p1841 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz243) qz243 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 371556 1000 59 96 67108864 33554432 1125899906842624 Bool.false 38370877237 1297 

noncomputable def Ns114p1842 := Ns114p1841 120242927 48 27397080 8 130587807 48 25364760 8 Bool.false 199377588 43267 Bool.true 86656680 Bool.true 30027702 3537118876014220 1 Bool.false 64504396 Bool.false Bool.false 60502289 Bool.false Bool.false 248579108 

noncomputable def Ns114p1843 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz243) qz243 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 371556 1000 36 16 67108864 33554432 1125899906842624 Bool.false 38370877237 1297 

noncomputable def Ns114p1844 := Ns114p1843 93032624 47 33554424 8 108007536 47 30011992 8 Bool.false 152329517 25477 Bool.false 9130739 Bool.true 73341095 3537118876014220 1 Bool.false 66488663 Bool.false Bool.false 30866123 Bool.false Bool.false 199377588 

noncomputable def Ns114p1845 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz243) qz243 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 371556 1000 200 104 67108864 33554432 1125899906842624 Bool.false 38370877237 1297 

noncomputable def Ns114p1846 := Ns114p1845 46516304 47 47453136 16 73726608 47 38745320 8 Bool.false 67108840 1351 Bool.false 4593974 Bool.false 14220540 3537118876014220 1 Bool.false 66951683 Bool.false Bool.false 65607809 Bool.false Bool.false 152329517 

noncomputable def Ns114p1847 := nat_lit 206766279276688357737914831761549588229400097256197 

noncomputable def Ns114p1848 := nat_lit 361624521375652580683931915818069073416159232000 

noncomputable def Ns114p1849 := nat_lit 3399105340196863723797048852480000 

noncomputable def Ns114p1850 := nat_lit 7577754306562415385049272427248353280 

noncomputable abbrev qz958 := (@Eq.refl Real (Enclosure.sfrac Bool.false 371556 1000))

noncomputable abbrev qz820 := qz958

noncomputable abbrev qz588 := qz820

noncomputable abbrev qz246 := qz588

noncomputable def Ns114p1851 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz243 371556 1000 552216444544 16000000 743112 4000 2000 Ns114p1849 Ns114p1850 qz246 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns114p1852 := nat_lit 19512914225294949426305260436627875892450829274246262292480 

noncomputable abbrev qz821 := (Real.log (Enclosure.sfrac Bool.false 552216444544 16000000))

noncomputable abbrev qz247 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 371556 4000) qz821) (@HMul.hMul Real Real Real qz339 qz343 (@HSub.hSub Real Real Real qz342 qz344 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz345 (@Nat.cast Real Real.instNatCast 743112))))))

noncomputable abbrev qz822 := (Enclosure.sfrac Bool.false 371556 2000)

noncomputable abbrev qz589 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz247 qz822) (@HMul.hMul Real Real Real qz5 qz822 (Real.log Real.pi)))

noncomputable def Ns114p1853 := @Enclosure.Real.IsNear.addLit_ft_p qz589 (Enclosure.sfrac Bool.true Ns114p1849 Ns114p1850) 2575028002241520228641 4503599627370496000 8898105808121993 460800000000000000000 Ns114p1849 Ns114p1850 0 1 Ns114p1852 

noncomputable def Ns114p1854 := nat_lit 8640360199930893808855888691200 

noncomputable abbrev qz590 := (@HSub.hSub Real Real Real qz12 qz247 qz822)

noncomputable abbrev qz591 := (@HMul.hMul Real Real Real qz5 qz822 (Real.log Real.pi))

noncomputable def Ns114p1855 := @Enclosure.Real.IsNear.subLit_ff_p qz590 qz591 706557769147861150573 900719925474099200 3706602189557 450000000000000000 3567937178529 16777216000 92889 8388608000 Ns114p1854 2575028002241520228641 4503599627370496000 

noncomputable def Ns114p1856 := nat_lit 7065577691478611505730000 

noncomputable abbrev qz592 := qz822

noncomputable def Ns114p1857 := @Enclosure.Real.IsNear.subLit_ff_p qz247 qz592 4369458577312941758753 4503599627370496000 3706602189557 450000000000000000 371556 2000 0 1 Ns114p1856 706557769147861150573 900719925474099200 3706602189557 450000000000000000 

noncomputable def Ns114p1858 := nat_lit 9839146010298691046026435227490975744 

noncomputable def Ns114p1859 := nat_lit 12632194802831923779469312 

noncomputable def Ns114p1860 := nat_lit 20144410737315543809954730174367241603806333501440 

noncomputable def Ns114p1861 := nat_lit 4521374781540902414394253558044954109063200768 

noncomputable def Ns114p1862 := nat_lit 1825190708561111038168794949843713458700288 

noncomputable def Ns114p1863 := BSN.log_dyadic_bound 27928444544 1076504444544 3 2 Ns114p1860 33554432 11520000 Ns114p1861 Ns114p1862 1741439 1104432889088 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 27928444544) (BSN.artanhQ 1076504444544) 0 2 Ns114p1861 Ns114p1860 Ns114p1862 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns114p1864 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 371556 4000) qz821 371556 4000 0 1 47058592747270777 4503599627370496 156250027 1800000000000000 4371225621701235204753 4503599627370496000 1612656528667 200000000000000000 (Enclosure.Real.IsNear.const Bool.false 371556 4000) (BSN.isNear_log_sfrac 552216444544 16000000 47058592747270777 4503599627370496 156250027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 552216444544) qz350)) Bool.false Ns114p1859 Ns114p85 1000000172800000 11520000000000000000000 47058592747270777 4503599627370496 156250027 1800000000000000 (BSN.log_rat_reduce_isNear 552216444544 16000000 15 1104432889088 1048576000000 1741439 33554432 24973259072661432 36028797018963968 11520000 1000000000000000 rfl rfl rfl rfl (Ns114p1863 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p1865 := BSN.arctan_dyadic_bound_f 1000 743112 1 0 4194304 1440000 0 1 1 0 1 1 5644 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 743112) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 743112) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz823 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 743112)))

noncomputable def Ns114p1866 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz823 884279719003555 562949953421312 1 2000000000000000 5644 4194304 1 1440000 3705760672998376865792 883522194146723 562949953421312 12500000009 18000000000000000 qz16 (Ns114p1865 rfl) rfl rfl 

noncomputable def Ns114p1867 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 371556 4000) qz821) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz823)) 4371225621701235204753 4503599627370496000 1612656528667 200000000000000000 883522194146723 2251799813685248 12500000009 72000000000000000 Ns114p1858 4369458577312941758753 4503599627370496000 3706602189557 450000000000000000 (Ns114p1864 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz823) 1 4 0 1 883522194146723 562949953421312 12500000009 18000000000000000 883522194146723 2251799813685248 12500000009 72000000000000000 qz353 Ns114p1866 rfl) 

noncomputable def Ns114p1868 := @Ns114p1853 Ns114p1847 Ns114p1848 8898105808121993 460800000000000000000 (@Ns114p1855 8898105808121993 460800000000000000000 (Ns114p1857 (Ns114p1867 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 371556 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz592 (Real.log Real.pi) 371556 2000 0 1 38410761 33554432 1 16777216 3567937178529 16777216000 92889 8388608000 (Enclosure.Real.IsNear.const Bool.false 371556 2000) RS115to132.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns114p1849 Ns114p1850) 

noncomputable def Ns114p1869 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz243) Bool.false Ns114p1847 Ns114p1848 8898105808121993 460800000000000000000 2398179827 4194304 163 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz243) (@HAdd.hAdd Real Real Real qz354 qz589 (Enclosure.sfrac Bool.true Ns114p1849 Ns114p1850)) Bool.false Ns114p1847 Ns114p1848 8898105808121993 460800000000000000000 Ns114p1851 (Ns114p1868 rfl rfl)) 

noncomputable def Ns114p1870 := nat_lit 140261929665249447474866826704625292791746028041319720811019917657518217536454610646625 

noncomputable def Ns114p1871 := nat_lit 282362422218212693387781883459757703053428886601140899287375512674985212119118247521 

noncomputable def Ns114p1872 := nat_lit 366895514725395256168690042129369492459153093339435516858586890653931069871093026911841 

noncomputable def Ns114p1873 := BSN.sin_dyadic_bound_f 26999197909 17179869184 3 2 8388608 2882813 Ns114p1870 Ns114p98 Ns114p1871 Ns114p1872 Ns114p101 Ns114p1871 8388605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26999197909) qz355 0 2 Ns114p1870 Ns114p98 Ns114p1871 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26999197909) qz356 0 2 Ns114p1872 Ns114p101 Ns114p1871 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1874 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz243) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2398179827) qz366) Bool.false 2398179827 4194304 163 8388608 Bool.false 8388605 8388608 1 1440000 (Ns114p1869 rfl) (Enclosure.sfrac_false_div 2398179827 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2398179827) qz366) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949949825330785218985984) qz380) 226375608064910080 72057594037927936 Bool.false 8388605 8388608 90 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q3 2398179827 4194304 226375608064910080 72057594037927936 90 949949825330785218985984 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388605 8388608 949949825330785218985984 604462909807314587353088 26999197909 17179869184 2882813 2880000 (Ns114p1873 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p1875 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz243) Bool.false Ns114p1847 Ns114p1848 8898105808121993 460800000000000000000 38370877237 67108864 1297 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz243) (@HAdd.hAdd Real Real Real qz354 qz589 (Enclosure.sfrac Bool.true Ns114p1849 Ns114p1850)) Bool.false Ns114p1847 Ns114p1848 8898105808121993 460800000000000000000 Ns114p1851 (Ns114p1868 rfl rfl)) 

noncomputable def Ns114p1876 := Ns114p1846 25477 BSN.abs_quadSignPos (BSN.cos_quad_nat0 200 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66951683 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 104 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 65607809 67108864) qz246 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 1) Bool.false 8388605 8388608 949643 47185920000 67108840 67108864 1351 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz243)) Bool.false 8388605 8388608 949643 47185920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz243) qz243) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz243)) Bool.false 8388605 8388608 243108608 12079595520000 8388605 8388608 949643 47185920000 (Ns114p1874 rfl rfl) rfl)) rfl) (Ns114p1875 rfl) RS115to132.d7 

noncomputable def Ns114p1877 := nat_lit 445404019288372155839880976 

noncomputable def Ns114p1878 := BSN.cos_dyadic_bound_f 4593974 67108864 2 1 67108864 33554432 Ns114p1877 Ns114p227 Ns114p1877 Ns114p1877 Ns114p228 Ns114p1877 66951683 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 4593974) qz360 0 1 Ns114p1877 Ns114p227 Ns114p1877 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 4593974) (BSN.cosOddQ 67108864) 0 1 Ns114p1877 Ns114p228 Ns114p1877 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1879 := nat_lit 40894448255800453277350560000 

noncomputable def Ns114p1880 := BSN.cos_dyadic_bound_f 14220540 67108864 2 1 67108864 33554432 Ns114p1879 Ns114p227 Ns114p1879 Ns114p1879 Ns114p228 Ns114p1879 65607809 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 14220540) qz360 0 1 Ns114p1879 Ns114p227 Ns114p1879 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 14220540) (BSN.cosOddQ 67108864) 0 1 Ns114p1879 Ns114p228 Ns114p1879 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1881 := nat_lit 6950622710119592674110026641 

noncomputable def Ns114p1882 := BSN.cos_dyadic_bound_f 9130739 67108864 2 1 67108864 33554432 Ns114p1881 Ns114p227 Ns114p1881 Ns114p1881 Ns114p228 Ns114p1881 66488663 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 9130739) qz360 0 1 Ns114p1881 Ns114p227 Ns114p1881 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 9130739) (BSN.cosOddQ 67108864) 0 1 Ns114p1881 Ns114p228 Ns114p1881 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1883 := nat_lit 986704240230790600978548790479535820078366333623801169250240690625 

noncomputable def Ns114p1884 := nat_lit 837103424035766999542860523188108009464570275096335891187890625 

noncomputable def Ns114p1885 := nat_lit 2958438513844300268936560650392231244216169860321210835968346290625 

noncomputable def Ns114p1886 := BSN.cos_dyadic_bound_f 73341095 67108864 3 2 67108864 33554432 Ns114p1883 Ns114p113 Ns114p1884 Ns114p1885 Ns114p116 Ns114p1884 30866123 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 73341095) qz360 0 2 Ns114p1883 Ns114p113 Ns114p1884 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 73341095) (BSN.cosOddQ 67108864) 0 2 Ns114p1885 Ns114p116 Ns114p1884 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1887 := Ns114p1844 43267 BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66488663 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 16 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 30866123 67108864) qz246 rfl rfl (Ns114p1876 RS115to132.d9 RS115to132.d11 RS115to132.d13 RS115to132.d17 (Ns114p1878 rfl rfl) (Ns114p1880 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns114p1875 rfl) RS115to132.d19 RS115to132.d21 RS115to132.d23 RS115to132.d25 RS115to132.d17 (Ns114p1882 rfl rfl) (Ns114p1886 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns114p1888 := nat_lit 3461853059791920711915287751955351615010566847082943997898915840000 

noncomputable def Ns114p1889 := nat_lit 3179921288997620425268581400143514848467978184130828697600000000 

noncomputable def Ns114p1890 := nat_lit 9061609569749034288613414028092355205749203111014355795653427200000 

noncomputable def Ns114p1891 := BSN.sin_dyadic_bound_f 86656680 67108864 3 2 67108864 33554432 Ns114p1888 Ns114p107 Ns114p1889 Ns114p1890 Ns114p110 Ns114p1889 64504396 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 86656680) qz359 0 2 Ns114p1888 Ns114p107 Ns114p1889 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 86656680) (BSN.sinOddQ 67108864) 0 2 Ns114p1890 Ns114p110 Ns114p1889 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1892 := nat_lit 27703049720445979414271513305799599769691954357159617597579387136 

noncomputable def Ns114p1893 := nat_lit 660962435067244030476471836048271040203316137886709668045056 

noncomputable def Ns114p1894 := nat_lit 83107827236467803754753586973726702766995456439203079373402071296 

noncomputable def Ns114p1895 := BSN.cos_dyadic_bound_f 30027702 67108864 3 2 67108864 33554432 Ns114p1892 Ns114p113 Ns114p1893 Ns114p1894 Ns114p116 Ns114p1893 60502289 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 30027702) qz360 0 2 Ns114p1892 Ns114p113 Ns114p1893 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 30027702) (BSN.cosOddQ 67108864) 0 2 Ns114p1894 Ns114p116 Ns114p1893 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1896 := Ns114p1842 58328 BSN.abs_quadSignPos (BSN.cos_quad_nat3 59 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 64504396 67108864) BSN.abs_quadSignPos qz734 (BSN.sfrac_eq_quadSignPos_mul Bool.false 60502289 67108864) qz246 rfl rfl (Ns114p1887 rfl rfl) (Ns114p1875 rfl) RS115to132.d27 RS115to132.d29 RS115to132.d31 RS115to132.d33 RS115to132.d17 (Ns114p1891 rfl rfl) (Ns114p1895 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns114p1897 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 7) 248579108 67108864 58328 67108864 248579108 67108864 58328 67108864 33363723104026624 62144777 8388608 7291 4194304 (Ns114p1896 rfl) 

noncomputable def Ns114p1898 := @Enclosure.Real.IsNear.mulLit_tf qz819 (Zeta.RiemannSiegel.correction qz245) 23633 65536 1 4194304 1972448938205 4398046511104 14543665652599 98956046499840000 46614885756598765 288230376151711744 

noncomputable abbrev qz824 := (@HPow.hPow Real Real Real qz7 qz244 qz9)

noncomputable def Ns114p1899 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz824 1 1 0 1 23633 65536 1 4194304 23633 65536 1 4194304 

noncomputable def Ns114p1900 := @Enclosure.Real.IsNear.sqrt_image qz244 124015082121 2097152000 92889 2097152000 32253885 32253910 4194304 (@Enclosure.Real.IsNear.of_eq qz244 (@HMul.hMul Real Real Real qz5 qz243 qz3) Bool.false 124015082121 2097152000 92889 2097152000 (BSN.t_div_two_pi_mk qz243 371556 1000 qz246) (@Enclosure.Real.IsNear.mulLit_ff qz243 qz3 371556 1000 0 1 1335089 8388608 1 8388608 124015082121 2097152000 92889 2097152000 (Enclosure.Real.IsNear.const Bool.false 371556 1000) RS115to132.d36 rfl)) 

noncomputable abbrev qz959 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 371556 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz825 := qz959

noncomputable abbrev qz593 := qz825

noncomputable abbrev qz248 := qz593

noncomputable def Ns114p1901 := @Enclosure.Real.IsNear.sqrt_image qz248 64507795 8388608 25 8388608 11631104 11631110 4194304 (@Enclosure.Real.IsNear.recentre' qz248 Bool.false 64507795 8388608 25 8388608 64507795 8388608 25 8388608 (Ns114p1900 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns114p1902 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz248) 11631107 4194304 3 4194304 1512511 1512513 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz248) Bool.false 23262214 8388608 6 8388608 11631107 4194304 3 4194304 (Ns114p1901 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns114p1903 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz248)) Bool.false 3025024 8388608 2 8388608 23633 65536 1 4194304 (Ns114p1902 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz249 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz587))

noncomputable abbrev qz826 := (@HMul.hMul Real Real Real qz884 qz957 qz957)

noncomputable abbrev qz594 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz826 qz818) qz642)

noncomputable abbrev qz250 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz594))

noncomputable def Ns114p1904 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz245) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz249) qz250) Bool.false 1972448938205 

noncomputable def Ns114p1905 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz249) qz250 22761565 8388608 1207 

noncomputable abbrev qz827 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz249))

noncomputable def Ns114p1906 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz249) (@Neg.neg Real Real.instNeg qz827) Bool.true 22761565 8388608 1207 8388608 (BSN.inv_eq_neg_inv_neg qz249) 

noncomputable def Ns114p1907 := @Enclosure.Real.IsNear.recentre' qz827 Bool.false 22761565 8388608 1207 8388608 22761565 8388608 

noncomputable def Ns114p1908 := @Enclosure.Real.IsNear.recentre' qz249 Bool.true 3091560 8388608 117954304 6039797760000 386445 1048576 460759 23592960000 

noncomputable abbrev qz251 := (@HMul.hMul Real Real Real qz339 qz337 qz587)

noncomputable def Ns114p1909 := @Enclosure.Real.IsNear.cos_image qz251 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9091045) qz383) Bool.false 9091045 2097152 79 4194304 Bool.true 3091560 8388608 1 

noncomputable def Ns114p1910 := nat_lit 674651885275815717837873263 

noncomputable def Ns114p1911 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz245 884279719003555 140737488355328 1 500000000000000 5787539 8388608 25 8388608 5117803360642115701145 1180591620717411303424 Ns114p1910 

noncomputable def Ns114p1912 := @Enclosure.Real.IsNear.subLit_ff_p qz248 qz1 64507795 8388608 25 8388608 7 1 0 1 5787539 5787539 8388608 25 

noncomputable def Ns114p1913 := @Ns114p1912 8388608 (@Enclosure.Real.IsNear.recentre' qz248 Bool.false 64507795 8388608 25 8388608 64507795 8388608 25 8388608 (Ns114p1900 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns114p1914 := @Enclosure.Real.IsNear.recentre' qz251 Bool.false 5117803360642115701145 1180591620717411303424 Ns114p1910 Ns114p501 9091045 2097152 79 4194304 (@Ns114p1911 Ns114p501 RS115to132.d35 (Ns114p1913 rfl rfl) rfl) 

noncomputable def Ns114p1915 := nat_lit 25886377449587549640182294486849077284686948658269940012562347759828233114055948436641 

noncomputable def Ns114p1916 := nat_lit 31211688852803363280164619150468363522601860508365936525395491924434105935275033761 

noncomputable def Ns114p1917 := nat_lit 77596708971057042193986554222246295127015642253793088164636252295635831130297295242401 

noncomputable def Ns114p1918 := BSN.cos_dyadic_bound_f 20501689821 17179869184 3 2 8388608 2882813 Ns114p1915 Ns114p1309 Ns114p1916 Ns114p1917 Ns114p1312 Ns114p1916 3091560 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 20501689821) qz454 0 2 Ns114p1915 Ns114p1309 Ns114p1916 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 20501689821) qz455 0 2 Ns114p1917 Ns114p1312 Ns114p1916 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1919 := @Ns114p1909 1440000 (Ns114p1914 rfl) (Enclosure.sfrac_false_div 9091045 2097152) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9091045) qz383) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 360669541571984537681920) qz384) 226375608064910080 72057594037927936 Bool.false 3091560 8388608 0 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q2 9091045 2097152 226375608064910080 72057594037927936 0 360669541571984537681920 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 3091560 8388608 360669541571984537681920 302231454903657293676544 20501689821 17179869184 2882813 2880000 (Ns114p1918 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p1920 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz249) 386445 1048576 460759 23592960000 11380179 11381386 4194304 (@Enclosure.Real.IsNear.neg qz249 Bool.true 386445 1048576 460759 23592960000 (Ns114p1908 (Ns114p1919 rfl rfl) rfl)) 

noncomputable def Ns114p1921 := Ns114p1906 (@Enclosure.Real.IsNear.neg qz827 Bool.false 22761565 8388608 1207 8388608 (@Ns114p1907 1207 8388608 (Ns114p1920 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p1922 := @Enclosure.Real.IsNear.recentre' qz250 Bool.true 693256 4194304 

noncomputable abbrev qz252 := (@HMul.hMul Real Real Real qz339 qz337 qz594)

noncomputable def Ns114p1923 := @Enclosure.Real.IsNear.cos_image qz252 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 14569697)) qz357) Bool.true 14569697 8388608 

noncomputable def Ns114p1924 := nat_lit 17200863002465637799784498725 

noncomputable def Ns114p1925 := nat_lit 2693711052485228546397888384059613 

noncomputable def Ns114p1926 := @Enclosure.Real.IsNear.recentre' qz252 Bool.true Ns114p1924 Ns114p517 Ns114p1925 

noncomputable abbrev qz253 := qz594

noncomputable def Ns114p1927 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz253 884279719003555 140737488355328 1 500000000000000 19451834790295 

noncomputable abbrev qz595 := (@HSub.hSub Real Real Real qz634 qz826 qz818)

noncomputable abbrev qz254 := qz595

noncomputable def Ns114p1928 := @Enclosure.Real.IsNear.subLit_tf qz254 qz26 15053788279191 70368744177664 499092775 70368744177664 1 16 

noncomputable abbrev qz596 := qz826

noncomputable abbrev qz255 := qz596

noncomputable def Ns114p1929 := @Enclosure.Real.IsNear.subLit_ff_n qz255 qz245 33495607676521 70368744177664 289377575 70368744177664 5787539 8388608 25 8388608 

noncomputable def Ns114p1930 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz245 5787539 8388608 25 8388608 5787539 8388608 25 8388608 33495607676521 70368744177664 

noncomputable def Ns114p1931 := nat_lit 22171490140215088437923468665377301321587428489728956090623410777736421583216284300489544321 

noncomputable def Ns114p1932 := nat_lit 91496870552454268072443403455335572669618753517311296996735414636523836512278499840641 

noncomputable def Ns114p1933 := nat_lit 134023474332109611826663306624675781201341538664534278126396633844207353729287348773072687745 

noncomputable def Ns114p1934 := BSN.cos_dyadic_bound_t 14569697 8388608 4 3 4194304 1440000 Ns114p1931 Ns114p631 Ns114p1932 Ns114p1933 Ns114p634 Ns114p1932 693256 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 14569697) (BSN.cosEvenQ 8388608) 0 3 Ns114p1931 Ns114p631 Ns114p1932 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 14569697) (BSN.cosOddQ 8388608) 0 3 Ns114p1933 Ns114p634 Ns114p1932 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1935 := @Ns114p1922 548388608 12079595520000 86657 524288 2142143 47185920000 (@Ns114p1923 375 8388608 Bool.true 693256 4194304 1 1440000 (@Ns114p1926 Ns114p1827 14569697 8388608 375 8388608 (@Ns114p1927 70368744177664 499092775 70368744177664 Ns114p1924 Ns114p517 Ns114p1925 Ns114p1827 RS115to132.d35 (@Ns114p1928 0 1 311229356644720 19451834790295 70368744177664 499092775 70368744177664 (@Ns114p1929 126280328789127856128 15053788279191 70368744177664 499092775 70368744177664 (@Ns114p1930 289377575 70368744177664 (Ns114p1913 rfl rfl) (Ns114p1913 rfl rfl) rfl) (Ns114p1913 rfl rfl) rfl rfl) qz370 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 14569697 8388608) (BSN.cos_neg_of_bound 14569697 8388608 Bool.true 693256 4194304 1 1440000 (Ns114p1934 rfl rfl)) rfl rfl) 

noncomputable def Ns114p1936 := @Ns114p1898 2449095940924342643 46116860184273879040000 (Ns114p1899 qz28 (@Enclosure.Real.IsNear.of_eq qz824 (@Inv.inv Real Real.instInv (Real.sqrt qz248)) Bool.false 23633 65536 1 4194304 (BSN.rpow_neg_quarter_mk qz244 (BSN.t_div_two_pi_nonneg qz243 371556 1000 qz246)) Ns114p1903) rfl) (@Ns114p1904 4398046511104 14543665652599 98956046499840000 (BSN.correction_mk qz245 (BSN.cos_two_pi_p_ne_zero_mk qz243 371556 1000 7 qz246 rfl rfl (@BSN.floor_sqrt_eq_dec qz243 371556 1000 7 qz246 rfl rfl rfl))) (@Ns114p1905 8388608 86657 524288 2142143 47185920000 1972448938205 4398046511104 14543665652599 98956046499840000 Ns114p1921 (Ns114p1935 rfl) rfl)) 

noncomputable def Ns114p1937 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz243) (hardyZApproximantRS₀ qz243) Bool.false 2181893164414302701 288230376151711744 82614488722072502643 46116860184273879040000 (@Eq.refl Real (hardyZApproximantRS₀ qz243)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz243) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz243) qz243 7) (@HMul.hMul Real Real Real qz5 qz819 (Zeta.RiemannSiegel.correction qz245))) Bool.false 2181893164414302701 288230376151711744 82614488722072502643 46116860184273879040000 (BSN.hardyZApproximantRS₀_eq qz243 7 (@BSN.floor_sqrt_eq_dec qz243 371556 1000 7 qz246 rfl rfl rfl)) (@Ns114p1840 2181893164414302701 288230376151711744 82614488722072502643 46116860184273879040000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz243) qz243 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 7)) Bool.false 62144777 8388608 7291 4194304 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz243) qz243 7) (Ns114p1897 (Ns114p1896 rfl) rfl rfl)) (Ns114p1936 rfl) rfl rfl)) 

theorem RS115to132.d56 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz243) Bool.false 2181893164414302701 288230376151711744 82614488722072502643 46116860184273879040000 := Ns114p1937 

noncomputable def Ns114p1938 := nat_lit 17278883932877718361735168 

noncomputable abbrev qz960 := (Enclosure.sfrac Bool.false 373095 1000)

noncomputable abbrev qz828 := qz960

noncomputable abbrev qz597 := qz828

noncomputable abbrev qz256 := qz597

noncomputable abbrev qz961 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 373095 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz829 := qz961

noncomputable abbrev qz598 := qz829

noncomputable abbrev qz257 := qz598

noncomputable abbrev qz830 := (@HSub.hSub Real Real Real qz888 (Real.sqrt qz961) qz883)

noncomputable abbrev qz599 := qz830

noncomputable abbrev qz258 := qz599

noncomputable abbrev qz831 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz257 qz9))

noncomputable def Ns114p1939 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz256) qz256 7) (@HMul.hMul Real Real Real qz5 qz831 (Zeta.RiemannSiegel.correction qz258)) 2328307 8388608 29281 16777216 3060197761195748643 18446744073709551616 83266607449173907 1106804644422573096960 Ns114p1938 

noncomputable def Ns114p1940 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz256) qz256 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 373095 1000 59 96 67108864 33554432 1125899906842624 Bool.false 38581667152 1302 

noncomputable def Ns114p1941 := Ns114p1940 120242927 48 27397080 8 130587807 48 25364760 8 Bool.true 55129033 43439 Bool.true 60920630 Bool.true 20212422 3537118876014220 1 Bool.false 52891467 Bool.false Bool.false 64087929 Bool.false Bool.true 9313228 

noncomputable def Ns114p1942 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz256) qz256 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 373095 1000 36 16 67108864 33554432 1125899906842624 Bool.false 38581667152 1302 

noncomputable def Ns114p1943 := Ns114p1942 93032624 47 33554424 8 108007536 47 30011992 8 Bool.true 96327495 25576 Bool.false 76743446 Bool.true 28774778 3537118876014220 1 Bool.false 27806641 Bool.false Bool.false 61033810 Bool.false Bool.true 55129033 

noncomputable def Ns114p1944 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz256) qz256 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 373095 1000 201 105 67108864 33554432 1125899906842624 Bool.false 38581667152 1302 

noncomputable def Ns114p1945 := Ns114p1944 46516304 47 47453136 16 73726608 47 38745320 8 Bool.true 67108856 1351 Bool.false 38380940 Bool.false 6130848 3537118876014220 1 Bool.false 36322537 Bool.true Bool.false 6122323 Bool.true Bool.true 96327495 

noncomputable def Ns114p1946 := nat_lit 357560677684819689863039775516995480785803905044747 

noncomputable def Ns114p1947 := nat_lit 621940228646779777606471840471529508349725900800 

noncomputable def Ns114p1948 := nat_lit 3470086957049960043955648500000000 

noncomputable def Ns114p1949 := nat_lit 7768039070073254335283339472645000000 

noncomputable def Ns114p1950 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz256 373095 1000 556800516100 16000000 746190 4000 2000 Ns114p1948 Ns114p1949 (@Eq.refl Real qz256) rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns114p1951 := nat_lit 16090230495816886043836789898264796635361175727013615000000 

noncomputable abbrev qz832 := (Real.log (Enclosure.sfrac Bool.false 556800516100 16000000))

noncomputable abbrev qz259 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 373095 4000) qz832) (@HMul.hMul Real Real Real qz339 qz343 (@HSub.hSub Real Real Real qz342 qz344 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz345 (@Nat.cast Real Real.instNatCast 746190))))))

noncomputable abbrev qz833 := (Enclosure.sfrac Bool.false 373095 2000)

noncomputable abbrev qz600 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz259 qz833) (@HMul.hMul Real Real Real qz5 qz833 (Real.log Real.pi)))

noncomputable def Ns114p1952 := @Enclosure.Real.IsNear.addLit_ft_p qz600 (Enclosure.sfrac Bool.true Ns114p1948 Ns114p1949) 2071339092527377420387 3602879701896396800 7147704607609483 368640000000000000000 Ns114p1948 Ns114p1949 0 1 Ns114p1951 

noncomputable def Ns114p1953 := nat_lit 27801042691660637516284402073600 

noncomputable abbrev qz601 := (@HSub.hSub Real Real Real qz12 qz259 qz833)

noncomputable abbrev qz602 := (@HMul.hMul Real Real Real qz5 qz833 (Real.log Real.pi))

noncomputable def Ns114p1954 := @Enclosure.Real.IsNear.subLit_ff_p qz601 qz602 2840721434688034312291 3602879701896396800 11909220764893 1440000000000000000 2866172575059 13421772800 74619 6710886400 Ns114p1953 2071339092527377420387 3602879701896396800 

noncomputable def Ns114p1955 := nat_lit 5681442869376068624582000 

noncomputable abbrev qz603 := qz833

noncomputable def Ns114p1956 := @Enclosure.Real.IsNear.subLit_ff_p qz259 qz603 3512829635877552394339 3602879701896396800 11909220764893 1440000000000000000 373095 2000 0 1 Ns114p1955 2840721434688034312291 3602879701896396800 11909220764893 1440000000000000000 

noncomputable def Ns114p1957 := nat_lit 7910189119577090054796083481723011072 

noncomputable def Ns114p1958 := nat_lit 12642188938923405251444736 

noncomputable def Ns114p1959 := nat_lit 20489731873828145353326236380493814957361500000000 

noncomputable def Ns114p1960 := nat_lit 6180580743489299895035220424868478592800000000 

noncomputable def Ns114p1961 := nat_lit 3352151017569073924209733908719472300000000 

noncomputable def Ns114p1962 := BSN.log_dyadic_bound 32512516100 1081088516100 3 2 Ns114p1959 33554432 11520000 Ns114p1960 Ns114p1961 2018832 1113601032200 1048576000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 32512516100) (BSN.artanhQ 1081088516100) 0 2 Ns114p1960 Ns114p1959 Ns114p1961 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns114p1963 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 373095 4000) qz832 373095 4000 0 1 47095823805493881 4503599627370496 156250027 1800000000000000 3514243276542147906339 3602879701896396800 1295468973857 160000000000000000 (Enclosure.Real.IsNear.const Bool.false 373095 4000) (BSN.isNear_log_sfrac 556800516100 16000000 47095823805493881 4503599627370496 156250027 1800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 556800516100) qz350)) Bool.false Ns114p1958 Ns114p85 1000000172800000 11520000000000000000000 47095823805493881 4503599627370496 156250027 1800000000000000 (BSN.log_rat_reduce_isNear 556800516100 16000000 15 1113601032200 1048576000000 2018832 33554432 24973259072661432 36028797018963968 11520000 1000000000000000 rfl rfl rfl rfl (Ns114p1962 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p1964 := BSN.arctan_dyadic_bound_f 1000 746190 1 0 4194304 1440000 0 1 1 0 1 1 5620 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 746190) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 746190) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz834 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz15 (@Nat.cast Real Real.instNatCast 746190)))

noncomputable def Ns114p1965 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz834 884279719003555 562949953421312 1 2000000000000000 5620 4194304 1 1440000 3705774183797258977280 883525415372195 562949953421312 12500000009 18000000000000000 qz16 (Ns114p1964 rfl) rfl rfl 

noncomputable def Ns114p1966 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 373095 4000) qz832) (@HMul.hMul Real Real Real qz5 qz17 (@HSub.hSub Real Real Real qz12 qz14 qz834)) 3514243276542147906339 3602879701896396800 1295468973857 160000000000000000 883525415372195 2251799813685248 12500000009 72000000000000000 Ns114p1957 3512829635877552394339 3602879701896396800 11909220764893 1440000000000000000 (Ns114p1963 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 (@HSub.hSub Real Real Real qz12 qz14 qz834) 1 4 0 1 883525415372195 562949953421312 12500000009 18000000000000000 883525415372195 2251799813685248 12500000009 72000000000000000 qz353 Ns114p1965 rfl) 

noncomputable def Ns114p1967 := @Ns114p1952 Ns114p1946 Ns114p1947 7147704607609483 368640000000000000000 (@Ns114p1954 7147704607609483 368640000000000000000 (Ns114p1956 (Ns114p1966 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 373095 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz603 (Real.log Real.pi) 373095 2000 0 1 38410761 33554432 1 16777216 2866172575059 13421772800 74619 6710886400 (Enclosure.Real.IsNear.const Bool.false 373095 2000) RS115to132.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns114p1948 Ns114p1949) 

noncomputable def Ns114p1968 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz256) Bool.false Ns114p1946 Ns114p1947 7147704607609483 368640000000000000000 2411354197 4194304 163 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz256) (@HAdd.hAdd Real Real Real qz354 qz600 (Enclosure.sfrac Bool.true Ns114p1948 Ns114p1949)) Bool.false Ns114p1946 Ns114p1947 7147704607609483 368640000000000000000 Ns114p1950 (Ns114p1967 rfl rfl)) 

noncomputable def Ns114p1969 := nat_lit 140055254885267937781768871233927963401961700176946024109004076504479165525412590240000 

noncomputable def Ns114p1970 := nat_lit 281532584809092880696067310867764720379739214732363347771812883843378594608100000000 

noncomputable def Ns114p1971 := nat_lit 366355567181248924764458172823644475553094398877672903436713455699794249127667479200000 

noncomputable def Ns114p1972 := BSN.sin_dyadic_bound_f 26989266610 17179869184 3 2 8388608 2882813 Ns114p1969 Ns114p98 Ns114p1970 Ns114p1971 Ns114p101 Ns114p1970 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26989266610) qz355 0 2 Ns114p1969 Ns114p98 Ns114p1970 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26989266610) qz356 0 2 Ns114p1971 Ns114p101 Ns114p1970 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1973 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz256) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2411354197) qz366) Bool.false 2411354197 4194304 163 8388608 Bool.true 8388607 8388608 1 1440000 (Ns114p1968 rfl) (Enclosure.sfrac_false_div 2411354197 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2411354197) qz366) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949600398843529327017984) qz380) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 91 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q1 2411354197 4194304 226375608064910080 72057594037927936 91 949600398843529327017984 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 949600398843529327017984 604462909807314587353088 26989266610 17179869184 2882813 2880000 (Ns114p1972 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p1974 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz256) Bool.false Ns114p1946 Ns114p1947 7147704607609483 368640000000000000000 38581667152 67108864 1302 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz256) (@HAdd.hAdd Real Real Real qz354 qz600 (Enclosure.sfrac Bool.true Ns114p1948 Ns114p1949)) Bool.false Ns114p1946 Ns114p1947 7147704607609483 368640000000000000000 Ns114p1950 (Ns114p1967 rfl rfl)) 

noncomputable def Ns114p1975 := Ns114p1945 25576 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 201 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 36322537 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 105 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 6122323 67108864) (@Eq.refl Real qz256) rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 1) Bool.true 8388607 8388608 949643 47185920000 67108856 67108864 1351 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz256)) Bool.true 8388607 8388608 949643 47185920000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz256) qz256) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz256)) Bool.true 8388607 8388608 243108608 12079595520000 8388607 8388608 949643 47185920000 (Ns114p1973 rfl rfl) rfl)) rfl) (Ns114p1974 rfl) RS115to132.d7 

noncomputable def Ns114p1976 := nat_lit 133100328998971534320701618928981234141179261329722239721840640000 

noncomputable def Ns114p1977 := nat_lit 4708958421738896010637903967848469715764648105926681600000000 

noncomputable def Ns114p1978 := nat_lit 348588475731290250722582254874241001418786827385672460834611200000 

noncomputable def Ns114p1979 := BSN.sin_dyadic_bound_f 38380940 67108864 3 2 67108864 33554432 Ns114p1976 Ns114p107 Ns114p1977 Ns114p1978 Ns114p110 Ns114p1977 36322537 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 38380940) qz359 0 2 Ns114p1976 Ns114p107 Ns114p1977 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 38380940) (BSN.sinOddQ 67108864) 0 2 Ns114p1978 Ns114p110 Ns114p1977 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1980 := nat_lit 1412804910733771403418402816 

noncomputable def Ns114p1981 := BSN.sin_dyadic_bound_f 6130848 67108864 2 1 67108864 33554432 Ns114p1980 Ns114p231 Ns114p1980 Ns114p1980 Ns114p232 Ns114p1980 6122323 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 6130848) qz359 0 1 Ns114p1980 Ns114p231 Ns114p1980 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 6130848) (BSN.sinOddQ 67108864) 0 1 Ns114p1980 Ns114p232 Ns114p1980 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1982 := nat_lit 285083409909816420984493674642363484407992003596573190415208212995030249272075825051241327833148624896 

noncomputable def Ns114p1983 := nat_lit 41734532822397148196467882545841016190616879002329763256637883710629083875095741415777366511616 

noncomputable def Ns114p1984 := nat_lit 1728333275231566367433232054351955805650445868953893499802733065703549281634090865996743033948713062400 

noncomputable def Ns114p1985 := BSN.cos_dyadic_bound_f 76743446 67108864 4 3 67108864 33554432 Ns114p1982 Ns114p371 Ns114p1983 Ns114p1984 Ns114p374 Ns114p1983 27806641 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 76743446) qz360 0 3 Ns114p1982 Ns114p371 Ns114p1983 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 76743446) (BSN.cosOddQ 67108864) 0 3 Ns114p1984 Ns114p374 Ns114p1983 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1986 := nat_lit 23360680801639240816945385928135814922034460716398497753122447616 

noncomputable def Ns114p1987 := nat_lit 469997830828904927625993158109599358301124449847787539374336 

noncomputable def Ns114p1988 := nat_lit 70081102409256064640980905798091225567386779900295797684288594176 

noncomputable def Ns114p1989 := BSN.cos_dyadic_bound_f 28774778 67108864 3 2 67108864 33554432 Ns114p1986 Ns114p113 Ns114p1987 Ns114p1988 Ns114p116 Ns114p1987 61033810 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 28774778) qz360 0 2 Ns114p1986 Ns114p113 Ns114p1987 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 28774778) (BSN.cosOddQ 67108864) 0 2 Ns114p1988 Ns114p116 Ns114p1987 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1990 := Ns114p1943 43439 BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 27806641 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 16 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 61033810 67108864) (@Eq.refl Real qz256) rfl rfl (Ns114p1975 RS115to132.d9 RS115to132.d11 RS115to132.d13 RS115to132.d17 (Ns114p1979 rfl rfl) (Ns114p1981 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns114p1974 rfl) RS115to132.d19 RS115to132.d21 RS115to132.d23 RS115to132.d25 RS115to132.d17 (Ns114p1985 rfl rfl) (Ns114p1989 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns114p1991 := nat_lit 844999396777001580996883335158062383021270452459963779224430240000 

noncomputable def Ns114p1992 := nat_lit 189720861008431779501825787706765867695328941355117952100000000 

noncomputable def Ns114p1993 := nat_lit 2212786491117180965444072445567209572698487319109139706998679200000 

noncomputable def Ns114p1994 := BSN.sin_dyadic_bound_f 60920630 67108864 3 2 67108864 33554432 Ns114p1991 Ns114p107 Ns114p1992 Ns114p1993 Ns114p110 Ns114p1992 52891467 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 60920630) qz359 0 2 Ns114p1991 Ns114p107 Ns114p1992 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 60920630) (BSN.sinOddQ 67108864) 0 2 Ns114p1993 Ns114p110 Ns114p1992 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1995 := nat_lit 166906568301931548703757815056 

noncomputable def Ns114p1996 := BSN.cos_dyadic_bound_f 20212422 67108864 2 1 67108864 33554432 Ns114p1995 Ns114p227 Ns114p1995 Ns114p1995 Ns114p228 Ns114p1995 64087929 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 20212422) qz360 0 1 Ns114p1995 Ns114p227 Ns114p1995 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 20212422) (BSN.cosOddQ 67108864) 0 1 Ns114p1995 Ns114p228 Ns114p1995 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p1997 := Ns114p1941 58562 BSN.abs_quadSignPos (BSN.cos_quad_nat3 59 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 52891467 67108864) BSN.abs_quadSignPos qz734 (BSN.sfrac_eq_quadSignPos_mul Bool.false 64087929 67108864) (@Eq.refl Real qz256) rfl rfl (Ns114p1990 rfl rfl) (Ns114p1974 rfl) RS115to132.d27 RS115to132.d29 RS115to132.d31 RS115to132.d33 RS115to132.d17 (Ns114p1994 rfl rfl) (Ns114p1996 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns114p1998 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 7) 9313228 67108864 58562 67108864 9313228 67108864 58562 67108864 1250000302505984 2328307 8388608 29281 16777216 (Ns114p1997 rfl) 

noncomputable def Ns114p1999 := @Enclosure.Real.IsNear.mulLit_tf qz831 (Zeta.RiemannSiegel.correction qz258) 3021899 8388608 1 8388608 1012673739657 2199023255552 8260284624719 39582418599936000 3060197761195748643 18446744073709551616 

noncomputable abbrev qz835 := (@HPow.hPow Real Real Real qz7 qz257 qz9)

noncomputable def Ns114p2000 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz835 1 1 0 1 3021899 8388608 1 8388608 3021899 8388608 1 8388608 

noncomputable def Ns114p2001 := @Enclosure.Real.IsNear.sqrt_image qz257 99623006091 1677721600 74619 1677721600 32320614 32320640 4194304 (@Enclosure.Real.IsNear.of_eq qz257 (@HMul.hMul Real Real Real qz5 qz256 qz3) Bool.false 99623006091 1677721600 74619 1677721600 (BSN.t_div_two_pi_mk qz256 373095 1000 (@Eq.refl Real qz256)) (@Enclosure.Real.IsNear.mulLit_ff qz256 qz3 373095 1000 0 1 1335089 8388608 1 8388608 99623006091 1677721600 74619 1677721600 (Enclosure.Real.IsNear.const Bool.false 373095 1000) RS115to132.d36 rfl)) 

noncomputable abbrev qz836 := (Real.sqrt qz961)

noncomputable abbrev qz604 := qz836

noncomputable abbrev qz260 := qz604

noncomputable def Ns114p2002 := @Enclosure.Real.IsNear.sqrt_image qz260 32320627 4194304 13 4194304 11643130 11643135 4194304 (@Enclosure.Real.IsNear.recentre' qz260 Bool.false 64641254 8388608 26 8388608 32320627 4194304 13 4194304 (Ns114p2001 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns114p2003 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz260) 23286265 8388608 5 8388608 1510949 1510950 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz260) Bool.false 23286265 8388608 5 8388608 23286265 8388608 5 8388608 (Ns114p2002 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns114p2004 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz260)) Bool.false 3021899 8388608 1 8388608 3021899 8388608 1 8388608 (Ns114p2003 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz261 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz599))

noncomputable abbrev qz605 := (@HSub.hSub Real Real Real qz634 (@HMul.hMul Real Real Real qz629 qz830 qz830) qz830)

noncomputable abbrev qz262 := (@HMul.hMul Real Real Real qz339 qz337 (@HSub.hSub Real Real Real qz342 qz605 qz368))

noncomputable def Ns114p2005 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz258) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz261) (Real.cos qz262)) Bool.false 1012673739657 

noncomputable def Ns114p2006 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz261) (Real.cos qz262) 30623053 8388608 2277 

noncomputable abbrev qz837 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz261))

noncomputable def Ns114p2007 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz261) (@Neg.neg Real Real.instNeg qz837) Bool.true 30623053 8388608 2277 8388608 (BSN.inv_eq_neg_inv_neg qz261) 

noncomputable def Ns114p2008 := @Enclosure.Real.IsNear.recentre' qz837 Bool.false 30623053 8388608 2277 8388608 30623053 8388608 

noncomputable def Ns114p2009 := @Enclosure.Real.IsNear.recentre' qz261 Bool.true 2297901 8388608 245988608 12079595520000 2297901 8388608 960893 47185920000 

noncomputable abbrev qz263 := (@HMul.hMul Real Real Real qz339 qz337 qz599)

noncomputable def Ns114p2010 := @Enclosure.Real.IsNear.cos_image qz263 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 37202727) qz357) Bool.false 37202727 8388608 165 8388608 Bool.true 2297901 8388608 1 

noncomputable def Ns114p2011 := nat_lit 350818980343003083686877979 

noncomputable def Ns114p2012 := nat_lit 18014398509481984000000000000000 

noncomputable def Ns114p2013 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz258 884279719003555 140737488355328 1 500000000000000 2960499 4194304 13 4194304 2617909223830305573945 590295810358705651712 Ns114p2011 

noncomputable def Ns114p2014 := @Enclosure.Real.IsNear.subLit_ff_p qz260 qz1 32320627 4194304 13 4194304 7 1 0 1 2960499 2960499 4194304 13 

noncomputable def Ns114p2015 := @Ns114p2014 4194304 (@Enclosure.Real.IsNear.recentre' qz260 Bool.false 64641254 8388608 26 8388608 32320627 4194304 13 4194304 (Ns114p2001 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns114p2016 := @Enclosure.Real.IsNear.recentre' qz263 Bool.false 2617909223830305573945 590295810358705651712 Ns114p2011 Ns114p2012 37202727 8388608 165 8388608 (@Ns114p2013 Ns114p2012 RS115to132.d35 (Ns114p2015 rfl rfl) rfl) 

noncomputable def Ns114p2017 := nat_lit 1563525524903382864625664 

noncomputable def Ns114p2018 := nat_lit 35728275426465517507506852521938412088185372929146393240982452187188346453276530099361 

noncomputable def Ns114p2019 := nat_lit 59402045519426627052901993851546268844836786758785100114411450593534958072083563681 

noncomputable def Ns114p2020 := nat_lit 107066022188357699268414753578112143726866445213921609522718533660377969443685423170721 

noncomputable def Ns114p2021 := BSN.cos_dyadic_bound_f 22219034077 17179869184 3 2 8388608 2882813 Ns114p2018 Ns114p1309 Ns114p2019 Ns114p2020 Ns114p1312 Ns114p2019 2297901 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 22219034077) qz454 0 2 Ns114p2018 Ns114p1309 Ns114p2019 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 22219034077) qz455 0 2 Ns114p2020 Ns114p1312 Ns114p2019 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p2022 := @Ns114p2010 1440000 (Ns114p2016 rfl) (Enclosure.sfrac_false_div 37202727 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 37202727) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns114p2017) qz358) 226375608064910080 72057594037927936 Bool.false 2297901 8388608 0 1000000000000000 2880000 1440000 (BSN.sin_reduce_arg_pos_rat_q2 37202727 8388608 226375608064910080 72057594037927936 0 Ns114p2017 Ns114p85 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 2297901 8388608 Ns114p2017 Ns114p85 22219034077 17179869184 2882813 2880000 (Ns114p2021 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns114p2023 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz261) 2297901 8388608 960893 47185920000 15310388 15312665 4194304 (@Enclosure.Real.IsNear.neg qz261 Bool.true 2297901 8388608 960893 47185920000 (Ns114p2009 (Ns114p2022 rfl rfl) rfl)) 

noncomputable def Ns114p2024 := Ns114p2007 (@Enclosure.Real.IsNear.neg qz837 Bool.false 30623053 8388608 2277 8388608 (@Ns114p2008 2277 8388608 (Ns114p2023 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns114p2025 := @Enclosure.Real.IsNear.recentre' (Real.cos qz262) Bool.true 529104 4194304 

noncomputable def Ns114p2026 := @Enclosure.Real.IsNear.cos_image qz262 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 3559457)) qz383) Bool.true 3559457 2097152 

noncomputable def Ns114p2027 := nat_lit 4202265323158852807441954405 

noncomputable def Ns114p2028 := nat_lit 3548644493931867794591018292609697 

noncomputable def Ns114p2029 := @Enclosure.Real.IsNear.recentre' qz262 Bool.true Ns114p2027 Ns114p272 Ns114p2028 

noncomputable def Ns114p2030 := nat_lit 75557863725914323419136000000000000000 

noncomputable abbrev qz264 := (@HSub.hSub Real Real Real qz342 qz605 qz368)

noncomputable def Ns114p2031 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz264 884279719003555 140737488355328 1 500000000000000 4752190096471 

noncomputable abbrev qz265 := qz605

noncomputable def Ns114p2032 := @Enclosure.Real.IsNear.subLit_tf qz265 qz26 3652678468695 17592186044416 131499095 17592186044416 1 16 

noncomputable abbrev qz606 := (@HMul.hMul Real Real Real qz629 qz830 qz830)

noncomputable abbrev qz266 := qz606

noncomputable def Ns114p2033 := @Enclosure.Real.IsNear.subLit_ff_n qz266 qz258 8764554329001 17592186044416 76973143 17592186044416 2960499 4194304 13 4194304 

noncomputable def Ns114p2034 := @Enclosure.Real.IsNear.mulLit_ff qz258 qz258 2960499 4194304 13 4194304 2960499 4194304 13 4194304 8764554329001 17592186044416 

noncomputable def Ns114p2035 := nat_lit 1204596283195567395319882937927065641881680899931034712889665909732067765657848170881 

noncomputable def Ns114p2036 := nat_lit 4136233138477036082050166925596237078380023207519674850940076428835298024278401 

noncomputable def Ns114p2037 := nat_lit 7283915397827055834128163621897652953431146738296286119088395844013668692711192054145 

noncomputable def Ns114p2038 := BSN.cos_dyadic_bound_t 3559457 2097152 4 3 4194304 1440000 Ns114p2035 Ns114p281 Ns114p2036 Ns114p2037 Ns114p284 Ns114p2036 529104 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 3559457) (BSN.cosEvenQ 2097152) 0 3 Ns114p2035 Ns114p281 Ns114p2036 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 3559457) (BSN.cosOddQ 2097152) 0 3 Ns114p2037 Ns114p284 Ns114p2036 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns114p2039 := @Ns114p2025 577188608 12079595520000 33069 262144 2254643 47185920000 (@Ns114p2026 395 8388608 Bool.true 529104 4194304 1 1440000 (@Ns114p2029 Ns114p2030 3559457 2097152 395 8388608 (@Ns114p2031 17592186044416 131499095 17592186044416 Ns114p2027 Ns114p272 Ns114p2028 Ns114p2030 RS115to132.d35 (@Ns114p2032 0 1 76035041543536 4752190096471 17592186044416 131499095 17592186044416 (@Ns114p2033 15320443911961313280 3652678468695 17592186044416 131499095 17592186044416 (@Ns114p2034 76973143 17592186044416 (Ns114p2015 rfl rfl) (Ns114p2015 rfl rfl) rfl) (Ns114p2015 rfl rfl) rfl rfl) qz370 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 3559457 2097152) (BSN.cos_neg_of_bound 3559457 2097152 Bool.true 529104 4194304 1 1440000 (Ns114p2038 rfl rfl)) rfl rfl) 

noncomputable def Ns114p2040 := @Ns114p1999 83266607449173907 1106804644422573096960 (Ns114p2000 qz28 (@Enclosure.Real.IsNear.of_eq qz835 (@Inv.inv Real Real.instInv (Real.sqrt qz260)) Bool.false 3021899 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz257 (BSN.t_div_two_pi_nonneg qz256 373095 1000 (@Eq.refl Real qz256))) Ns114p2004) rfl) (@Ns114p2005 2199023255552 8260284624719 39582418599936000 (BSN.correction_mk qz258 (BSN.cos_two_pi_p_ne_zero_mk qz256 373095 1000 7 (@Eq.refl Real qz256) rfl rfl (@BSN.floor_sqrt_eq_dec qz256 373095 1000 7 (@Eq.refl Real qz256) rfl rfl rfl))) (@Ns114p2006 8388608 33069 262144 2254643 47185920000 1012673739657 2199023255552 8260284624719 39582418599936000 Ns114p2024 (Ns114p2039 rfl) rfl)) 

noncomputable def Ns114p2041 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz256) (hardyZApproximantRS₀ qz256) Bool.true 2059803477868761821 18446744073709551616 2014954605823717267 1106804644422573096960 (@Eq.refl Real (hardyZApproximantRS₀ qz256)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz256) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz256) qz256 7) (@HMul.hMul Real Real Real qz5 qz831 (Zeta.RiemannSiegel.correction qz258))) Bool.true 2059803477868761821 18446744073709551616 2014954605823717267 1106804644422573096960 (BSN.hardyZApproximantRS₀_eq qz256 7 (@BSN.floor_sqrt_eq_dec qz256 373095 1000 7 (@Eq.refl Real qz256) rfl rfl rfl)) (@Ns114p1939 2059803477868761821 18446744073709551616 2014954605823717267 1106804644422573096960 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz256) qz256 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz256) qz256 7)) Bool.true 2328307 8388608 29281 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz256) qz256 7) (Ns114p1998 (Ns114p1997 rfl) rfl rfl)) (Ns114p2040 rfl) rfl rfl)) 

theorem RS115to132.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz256) Bool.true 2059803477868761821 18446744073709551616 2014954605823717267 1106804644422573096960 := Ns114p2041 

noncomputable def RS115to132.d58 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz267 := (RS115to132.d3 qz338 qz371 (@Enclosure.dec_le_dec qz338 qz371 345139 1000 346706 1000 (@Eq.refl Real qz338) qz374 rfl rfl rfl))

noncomputable abbrev qz838 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz267)

noncomputable def Ns114p2042 := @Enclosure.Real.IsNear.of_eq qz838 (hardyZApproximantRS₀ qz4) Bool.true 155282229166106583 72057594037927936 37656588456128324923 23058430092136939520000 

noncomputable abbrev qz268 := (@Enclosure.dec_le_dec qz338 qz371 345139 1000 346706 1000 (@Eq.refl Real qz338) qz374 rfl rfl rfl)

noncomputable def Ns114p2043 := @Enclosure.Real.IsNear.neg_val qz838 155282229166106583 72057594037927936 37656588456128324923 23058430092136939520000 (Ns114p2042 (RS115to132.d4 qz4 qz29 qz268) RS115to132.d37) rfl 

noncomputable abbrev qz839 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz267)

noncomputable def Ns114p2044 := @Enclosure.Real.IsNear.of_eq qz839 (hardyZApproximantRS₀ qz29) Bool.false 24789408747689725703 36893488147419103232 136099389423031858271 83010348331692982272000 

noncomputable def Ns114p2045 := @Enclosure.Real.IsNear.pos_val qz839 24789408747689725703 36893488147419103232 136099389423031858271 83010348331692982272000 (Ns114p2044 (RS115to132.d38 qz4 qz29 qz268) RS115to132.d39) rfl 

noncomputable def Ns114p2046 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz838 qz4 qz4 345139 1000 345139 1000 

noncomputable def Ns114p2047 := @Enclosure.norm_gt_of_isNear qz838 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 155282229166106583 72057594037927936 37656588456128324923 

noncomputable def Ns114p2048 := @Ns114p2047 23058430092136939520000 142570391 1342177280 1213 1342177280 (Ns114p2042 (RS115to132.d4 qz4 qz29 qz268) RS115to132.d37) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2049 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz839 qz4 qz29 345139 1000 346706 1000 

noncomputable def Ns114p2050 := @Enclosure.norm_gt_of_isNear qz839 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 24789408747689725703 36893488147419103232 136099389423031858271 

noncomputable def Ns114p2051 := @Ns114p2050 83010348331692982272000 142570391 1342177280 1213 1342177280 (Ns114p2044 (RS115to132.d38 qz4 qz29 qz268) RS115to132.d39) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2052 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz267 (@BSN.thirtyTwoPi_le_dec qz4 345139 1000 qz11 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz838 qz839 (Ns114p2043 rfl rfl) (Ns114p2045 rfl rfl)) (Ns114p2046 qz11 qz11 rfl rfl rfl rfl (Ns114p2048 rfl)) (Ns114p2049 qz11 qz32 rfl rfl rfl rfl (Ns114p2051 rfl)) 

noncomputable abbrev qz269 := (RS115to132.d3 qz371 qz391 (@Enclosure.dec_le_dec qz371 qz391 346706 1000 348272 1000 qz374 qz394 rfl rfl rfl))

noncomputable abbrev qz840 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz269)

noncomputable def Ns114p2053 := @Enclosure.Real.IsNear.of_eq qz840 (hardyZApproximantRS₀ qz29) Bool.false 24789408747689725703 36893488147419103232 136099389423031858271 83010348331692982272000 

noncomputable abbrev qz270 := (@Enclosure.dec_le_dec qz371 qz391 346706 1000 348272 1000 qz374 qz394 rfl rfl rfl)

noncomputable def Ns114p2054 := @Enclosure.Real.IsNear.pos_val qz840 24789408747689725703 36893488147419103232 136099389423031858271 83010348331692982272000 (Ns114p2053 (RS115to132.d4 qz29 qz48 qz270) RS115to132.d39) rfl 

noncomputable abbrev qz841 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz269)

noncomputable def Ns114p2055 := @Enclosure.Real.IsNear.of_eq qz841 (hardyZApproximantRS₀ qz48) Bool.true 45182460369863216695 18446744073709551616 85411422879908933171 51881467707308113920000 

noncomputable def Ns114p2056 := @Enclosure.Real.IsNear.neg_val qz841 45182460369863216695 18446744073709551616 85411422879908933171 51881467707308113920000 (Ns114p2055 (RS115to132.d38 qz29 qz48 qz270) RS115to132.d41) rfl 

noncomputable def Ns114p2057 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz840 qz4 qz29 345139 1000 346706 1000 

noncomputable def Ns114p2058 := @Enclosure.norm_gt_of_isNear qz840 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 24789408747689725703 36893488147419103232 136099389423031858271 

noncomputable def Ns114p2059 := @Ns114p2058 83010348331692982272000 142570391 1342177280 1213 1342177280 (Ns114p2053 (RS115to132.d4 qz29 qz48 qz270) RS115to132.d39) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2060 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz841 qz4 qz48 345139 1000 348272 1000 

noncomputable def Ns114p2061 := @Enclosure.norm_gt_of_isNear qz841 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 45182460369863216695 18446744073709551616 85411422879908933171 

noncomputable def Ns114p2062 := @Ns114p2061 51881467707308113920000 142570391 1342177280 1213 1342177280 (Ns114p2055 (RS115to132.d38 qz29 qz48 qz270) RS115to132.d41) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2063 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz269 (@BSN.thirtyTwoPi_le_dec qz29 346706 1000 qz32 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz840 qz841 (Ns114p2054 rfl rfl) (Ns114p2056 rfl rfl)) (Ns114p2057 qz11 qz32 rfl rfl rfl rfl (Ns114p2059 rfl)) (Ns114p2060 qz11 qz51 rfl rfl rfl rfl (Ns114p2062 rfl)) 

noncomputable abbrev qz271 := (RS115to132.d3 qz391 qz404 (@Enclosure.dec_le_dec qz391 qz404 348272 1000 349836 1000 qz394 qz407 rfl rfl rfl))

noncomputable abbrev qz842 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz271)

noncomputable def Ns114p2064 := @Enclosure.Real.IsNear.of_eq qz842 (hardyZApproximantRS₀ qz48) Bool.true 45182460369863216695 18446744073709551616 85411422879908933171 51881467707308113920000 

noncomputable abbrev qz272 := (@Enclosure.dec_le_dec qz391 qz404 348272 1000 349836 1000 qz394 qz407 rfl rfl rfl)

noncomputable def Ns114p2065 := @Enclosure.Real.IsNear.neg_val qz842 45182460369863216695 18446744073709551616 85411422879908933171 51881467707308113920000 (Ns114p2064 (RS115to132.d4 qz48 qz61 qz272) RS115to132.d41) rfl 

noncomputable abbrev qz843 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz271)

noncomputable def Ns114p2066 := @Enclosure.Real.IsNear.of_eq qz843 (hardyZApproximantRS₀ qz61) Bool.false 3995097361223893141 4611686018427387904 228819427984630872671 138350580552821637120000 

noncomputable def Ns114p2067 := @Enclosure.Real.IsNear.pos_val qz843 3995097361223893141 4611686018427387904 228819427984630872671 138350580552821637120000 (Ns114p2066 (RS115to132.d38 qz48 qz61 qz272) RS115to132.d42) rfl 

noncomputable def Ns114p2068 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz842 qz4 qz48 345139 1000 348272 1000 

noncomputable def Ns114p2069 := @Enclosure.norm_gt_of_isNear qz842 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 45182460369863216695 18446744073709551616 85411422879908933171 

noncomputable def Ns114p2070 := @Ns114p2069 51881467707308113920000 142570391 1342177280 1213 1342177280 (Ns114p2064 (RS115to132.d4 qz48 qz61 qz272) RS115to132.d41) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2071 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz843 qz4 qz61 345139 1000 349836 1000 

noncomputable def Ns114p2072 := @Enclosure.norm_gt_of_isNear qz843 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 3995097361223893141 4611686018427387904 228819427984630872671 

noncomputable def Ns114p2073 := @Ns114p2072 138350580552821637120000 142570391 1342177280 1213 1342177280 (Ns114p2066 (RS115to132.d38 qz48 qz61 qz272) RS115to132.d42) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2074 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz271 (@BSN.thirtyTwoPi_le_dec qz48 348272 1000 qz51 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz842 qz843 (Ns114p2065 rfl rfl) (Ns114p2067 rfl rfl)) (Ns114p2068 qz11 qz51 rfl rfl rfl rfl (Ns114p2070 rfl)) (Ns114p2071 qz11 qz64 rfl rfl rfl rfl (Ns114p2073 rfl)) 

noncomputable abbrev qz273 := (RS115to132.d3 qz404 qz417 (@Enclosure.dec_le_dec qz404 qz417 349836 1000 351398 1000 qz407 qz420 rfl rfl rfl))

noncomputable abbrev qz844 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz273)

noncomputable def Ns114p2075 := @Enclosure.Real.IsNear.of_eq qz844 (hardyZApproximantRS₀ qz61) Bool.false 3995097361223893141 4611686018427387904 228819427984630872671 138350580552821637120000 

noncomputable abbrev qz274 := (@Enclosure.dec_le_dec qz404 qz417 349836 1000 351398 1000 qz407 qz420 rfl rfl rfl)

noncomputable def Ns114p2076 := @Enclosure.Real.IsNear.pos_val qz844 3995097361223893141 4611686018427387904 228819427984630872671 138350580552821637120000 (Ns114p2075 (RS115to132.d4 qz61 qz74 qz274) RS115to132.d42) rfl 

noncomputable abbrev qz845 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz273)

noncomputable def Ns114p2077 := @Enclosure.Real.IsNear.of_eq qz845 (hardyZApproximantRS₀ qz74) Bool.true 25907344243314844299 18446744073709551616 172296687492673210339 103762935414616227840000 

noncomputable def Ns114p2078 := @Enclosure.Real.IsNear.neg_val qz845 25907344243314844299 18446744073709551616 172296687492673210339 103762935414616227840000 (Ns114p2077 (RS115to132.d38 qz61 qz74 qz274) RS115to132.d43) rfl 

noncomputable def Ns114p2079 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz844 qz4 qz61 345139 1000 349836 1000 

noncomputable def Ns114p2080 := @Enclosure.norm_gt_of_isNear qz844 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 3995097361223893141 4611686018427387904 228819427984630872671 

noncomputable def Ns114p2081 := @Ns114p2080 138350580552821637120000 142570391 1342177280 1213 1342177280 (Ns114p2075 (RS115to132.d4 qz61 qz74 qz274) RS115to132.d42) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2082 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz845 qz4 qz74 345139 1000 351398 1000 

noncomputable def Ns114p2083 := @Enclosure.norm_gt_of_isNear qz845 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 25907344243314844299 18446744073709551616 172296687492673210339 

noncomputable def Ns114p2084 := @Ns114p2083 103762935414616227840000 142570391 1342177280 1213 1342177280 (Ns114p2077 (RS115to132.d38 qz61 qz74 qz274) RS115to132.d43) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2085 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz273 (@BSN.thirtyTwoPi_le_dec qz61 349836 1000 qz64 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz844 qz845 (Ns114p2076 rfl rfl) (Ns114p2078 rfl rfl)) (Ns114p2079 qz11 qz64 rfl rfl rfl rfl (Ns114p2081 rfl)) (Ns114p2082 qz11 qz77 rfl rfl rfl rfl (Ns114p2084 rfl)) 

noncomputable abbrev qz275 := (RS115to132.d3 qz417 qz430 (@Enclosure.dec_le_dec qz417 qz430 351398 1000 352959 1000 qz420 qz433 rfl rfl rfl))

noncomputable abbrev qz846 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz275)

noncomputable def Ns114p2086 := @Enclosure.Real.IsNear.of_eq qz846 (hardyZApproximantRS₀ qz74) Bool.true 25907344243314844299 18446744073709551616 172296687492673210339 103762935414616227840000 

noncomputable abbrev qz276 := (@Enclosure.dec_le_dec qz417 qz430 351398 1000 352959 1000 qz420 qz433 rfl rfl rfl)

noncomputable def Ns114p2087 := @Enclosure.Real.IsNear.neg_val qz846 25907344243314844299 18446744073709551616 172296687492673210339 103762935414616227840000 (Ns114p2086 (RS115to132.d4 qz74 qz87 qz276) RS115to132.d43) rfl 

noncomputable abbrev qz847 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz275)

noncomputable def Ns114p2088 := @Enclosure.Real.IsNear.of_eq qz847 (hardyZApproximantRS₀ qz87) Bool.false 352411614865314074597 147573952589676412928 1384934731349918675803 830103483316929822720000 

noncomputable def Ns114p2089 := @Enclosure.Real.IsNear.pos_val qz847 352411614865314074597 147573952589676412928 1384934731349918675803 830103483316929822720000 (Ns114p2088 (RS115to132.d38 qz74 qz87 qz276) RS115to132.d44) rfl 

noncomputable def Ns114p2090 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz846 qz4 qz74 345139 1000 351398 1000 

noncomputable def Ns114p2091 := @Enclosure.norm_gt_of_isNear qz846 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 25907344243314844299 18446744073709551616 172296687492673210339 

noncomputable def Ns114p2092 := @Ns114p2091 103762935414616227840000 142570391 1342177280 1213 1342177280 (Ns114p2086 (RS115to132.d4 qz74 qz87 qz276) RS115to132.d43) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2093 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz847 qz4 qz87 345139 1000 352959 1000 

noncomputable def Ns114p2094 := @Enclosure.norm_gt_of_isNear qz847 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 352411614865314074597 147573952589676412928 1384934731349918675803 

noncomputable def Ns114p2095 := @Ns114p2094 830103483316929822720000 142570391 1342177280 1213 1342177280 (Ns114p2088 (RS115to132.d38 qz74 qz87 qz276) RS115to132.d44) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2096 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz275 (@BSN.thirtyTwoPi_le_dec qz74 351398 1000 qz77 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz846 qz847 (Ns114p2087 rfl rfl) (Ns114p2089 rfl rfl)) (Ns114p2090 qz11 qz77 rfl rfl rfl rfl (Ns114p2092 rfl)) (Ns114p2093 qz11 qz90 rfl rfl rfl rfl (Ns114p2095 rfl)) 

noncomputable abbrev qz277 := (RS115to132.d3 qz430 qz443 (@Enclosure.dec_le_dec qz430 qz443 352959 1000 354518 1000 qz433 qz446 rfl rfl rfl))

noncomputable abbrev qz848 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz277)

noncomputable def Ns114p2097 := @Enclosure.Real.IsNear.of_eq qz848 (hardyZApproximantRS₀ qz87) Bool.false 352411614865314074597 147573952589676412928 1384934731349918675803 830103483316929822720000 

noncomputable abbrev qz278 := (@Enclosure.dec_le_dec qz430 qz443 352959 1000 354518 1000 qz433 qz446 rfl rfl rfl)

noncomputable def Ns114p2098 := @Enclosure.Real.IsNear.pos_val qz848 352411614865314074597 147573952589676412928 1384934731349918675803 830103483316929822720000 (Ns114p2097 (RS115to132.d4 qz87 qz100 qz278) RS115to132.d44) rfl 

noncomputable abbrev qz849 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz277)

noncomputable def Ns114p2099 := @Enclosure.Real.IsNear.of_eq qz849 (hardyZApproximantRS₀ qz100) Bool.true 406000815316440155069 73786976294838206464 1391009437614186949507 830103483316929822720000 

noncomputable def Ns114p2100 := @Enclosure.Real.IsNear.neg_val qz849 406000815316440155069 73786976294838206464 1391009437614186949507 830103483316929822720000 (Ns114p2099 (RS115to132.d38 qz87 qz100 qz278) RS115to132.d45) rfl 

noncomputable def Ns114p2101 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz848 qz4 qz87 345139 1000 352959 1000 

noncomputable def Ns114p2102 := @Enclosure.norm_gt_of_isNear qz848 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 352411614865314074597 147573952589676412928 1384934731349918675803 

noncomputable def Ns114p2103 := @Ns114p2102 830103483316929822720000 142570391 1342177280 1213 1342177280 (Ns114p2097 (RS115to132.d4 qz87 qz100 qz278) RS115to132.d44) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2104 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz849 qz4 qz100 345139 1000 354518 1000 

noncomputable def Ns114p2105 := @Enclosure.norm_gt_of_isNear qz849 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 406000815316440155069 73786976294838206464 1391009437614186949507 

noncomputable def Ns114p2106 := @Ns114p2105 830103483316929822720000 142570391 1342177280 1213 1342177280 (Ns114p2099 (RS115to132.d38 qz87 qz100 qz278) RS115to132.d45) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2107 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz277 (@BSN.thirtyTwoPi_le_dec qz87 352959 1000 qz90 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz848 qz849 (Ns114p2098 rfl rfl) (Ns114p2100 rfl rfl)) (Ns114p2101 qz11 qz90 rfl rfl rfl rfl (Ns114p2103 rfl)) (Ns114p2104 qz11 qz103 rfl rfl rfl rfl (Ns114p2106 rfl)) 

noncomputable abbrev qz607 := (@Enclosure.dec_le_dec qz696 qz706 354518 1000 356075 1000 (@Eq.refl Real qz696) (@Eq.refl Real qz706) rfl rfl rfl)

noncomputable abbrev qz279 := (RS115to132.d3 qz443 qz458 qz607)

noncomputable abbrev qz850 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz279)

noncomputable def Ns114p2108 := @Enclosure.Real.IsNear.of_eq qz850 (hardyZApproximantRS₀ qz100) Bool.true 406000815316440155069 73786976294838206464 1391009437614186949507 830103483316929822720000 

noncomputable abbrev qz280 := qz607

noncomputable def Ns114p2109 := @Enclosure.Real.IsNear.neg_val qz850 406000815316440155069 73786976294838206464 1391009437614186949507 830103483316929822720000 (Ns114p2108 (RS115to132.d4 qz100 qz113 qz280) RS115to132.d45) rfl 

noncomputable abbrev qz851 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz279)

noncomputable def Ns114p2110 := @Enclosure.Real.IsNear.of_eq qz851 (hardyZApproximantRS₀ qz113) Bool.false 26695448694316857 144115188075855872 349408787279348097391 207525870829232455680000 

noncomputable def Ns114p2111 := @Enclosure.Real.IsNear.pos_val qz851 26695448694316857 144115188075855872 349408787279348097391 207525870829232455680000 (Ns114p2110 (RS115to132.d38 qz100 qz113 qz280) RS115to132.d46) rfl 

noncomputable def Ns114p2112 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz850 qz4 qz100 345139 1000 354518 1000 

noncomputable def Ns114p2113 := @Enclosure.norm_gt_of_isNear qz850 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 406000815316440155069 73786976294838206464 1391009437614186949507 

noncomputable def Ns114p2114 := @Ns114p2113 830103483316929822720000 142570391 1342177280 1213 1342177280 (Ns114p2108 (RS115to132.d4 qz100 qz113 qz280) RS115to132.d45) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2115 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz851 qz4 qz113 345139 1000 356075 1000 

noncomputable def Ns114p2116 := @Enclosure.norm_gt_of_isNear qz851 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 26695448694316857 144115188075855872 349408787279348097391 

noncomputable def Ns114p2117 := @Ns114p2116 207525870829232455680000 142570391 1342177280 1213 1342177280 (Ns114p2110 (RS115to132.d38 qz100 qz113 qz280) RS115to132.d46) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2118 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz279 (@BSN.thirtyTwoPi_le_dec qz100 354518 1000 qz103 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz850 qz851 (Ns114p2109 rfl rfl) (Ns114p2111 rfl rfl)) (Ns114p2112 qz11 qz103 rfl rfl rfl rfl (Ns114p2114 rfl)) (Ns114p2115 qz11 qz116 rfl rfl rfl rfl (Ns114p2117 rfl)) 

noncomputable abbrev qz608 := (@Enclosure.dec_le_dec qz706 qz716 356075 1000 357630 1000 (@Eq.refl Real qz706) qz720 rfl rfl rfl)

noncomputable abbrev qz281 := (RS115to132.d3 qz458 qz471 qz608)

noncomputable abbrev qz852 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz281)

noncomputable def Ns114p2119 := @Enclosure.Real.IsNear.of_eq qz852 (hardyZApproximantRS₀ qz113) Bool.false 26695448694316857 144115188075855872 349408787279348097391 207525870829232455680000 

noncomputable abbrev qz282 := qz608

noncomputable def Ns114p2120 := @Enclosure.Real.IsNear.pos_val qz852 26695448694316857 144115188075855872 349408787279348097391 207525870829232455680000 (Ns114p2119 (RS115to132.d4 qz113 qz126 qz282) RS115to132.d46) rfl 

noncomputable abbrev qz853 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz281)

noncomputable def Ns114p2121 := @Enclosure.Real.IsNear.of_eq qz853 (hardyZApproximantRS₀ qz126) Bool.true 1651326124505075757 4611686018427387904 468038260034787908411 276701161105643274240000 

noncomputable def Ns114p2122 := @Enclosure.Real.IsNear.neg_val qz853 1651326124505075757 4611686018427387904 468038260034787908411 276701161105643274240000 (Ns114p2121 (RS115to132.d38 qz113 qz126 qz282) RS115to132.d47) rfl 

noncomputable def Ns114p2123 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz852 qz4 qz113 345139 1000 356075 1000 

noncomputable def Ns114p2124 := @Enclosure.norm_gt_of_isNear qz852 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 26695448694316857 144115188075855872 349408787279348097391 

noncomputable def Ns114p2125 := @Ns114p2124 207525870829232455680000 142570391 1342177280 1213 1342177280 (Ns114p2119 (RS115to132.d4 qz113 qz126 qz282) RS115to132.d46) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2126 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz853 qz4 qz126 345139 1000 357630 1000 

noncomputable def Ns114p2127 := @Enclosure.norm_gt_of_isNear qz853 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1651326124505075757 4611686018427387904 468038260034787908411 

noncomputable def Ns114p2128 := @Ns114p2127 276701161105643274240000 142570391 1342177280 1213 1342177280 (Ns114p2121 (RS115to132.d38 qz113 qz126 qz282) RS115to132.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2129 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz281 (@BSN.thirtyTwoPi_le_dec qz113 356075 1000 qz116 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz852 qz853 (Ns114p2120 rfl rfl) (Ns114p2122 rfl rfl)) (Ns114p2123 qz11 qz116 rfl rfl rfl rfl (Ns114p2125 rfl)) (Ns114p2126 qz11 qz129 rfl rfl rfl rfl (Ns114p2128 rfl)) 

noncomputable abbrev qz609 := (@Enclosure.dec_le_dec qz716 qz727 357630 1000 359184 1000 qz720 qz731 rfl rfl rfl)

noncomputable abbrev qz283 := (RS115to132.d3 qz471 qz484 qz609)

noncomputable abbrev qz854 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz283)

noncomputable def Ns114p2130 := @Enclosure.Real.IsNear.of_eq qz854 (hardyZApproximantRS₀ qz126) Bool.true 1651326124505075757 4611686018427387904 468038260034787908411 276701161105643274240000 

noncomputable abbrev qz284 := qz609

noncomputable def Ns114p2131 := @Enclosure.Real.IsNear.neg_val qz854 1651326124505075757 4611686018427387904 468038260034787908411 276701161105643274240000 (Ns114p2130 (RS115to132.d4 qz126 qz139 qz284) RS115to132.d47) rfl 

noncomputable abbrev qz855 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz283)

noncomputable def Ns114p2132 := @Enclosure.Real.IsNear.of_eq qz855 (hardyZApproximantRS₀ qz139) Bool.false 255804369813444816429 147573952589676412928 1410896288553752900411 830103483316929822720000 

noncomputable def Ns114p2133 := @Enclosure.Real.IsNear.pos_val qz855 255804369813444816429 147573952589676412928 1410896288553752900411 830103483316929822720000 (Ns114p2132 (RS115to132.d38 qz126 qz139 qz284) RS115to132.d48) rfl 

noncomputable def Ns114p2134 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz854 qz4 qz126 345139 1000 357630 1000 

noncomputable def Ns114p2135 := @Enclosure.norm_gt_of_isNear qz854 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1651326124505075757 4611686018427387904 468038260034787908411 

noncomputable def Ns114p2136 := @Ns114p2135 276701161105643274240000 142570391 1342177280 1213 1342177280 (Ns114p2130 (RS115to132.d4 qz126 qz139 qz284) RS115to132.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2137 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz855 qz4 qz139 345139 1000 359184 1000 

noncomputable def Ns114p2138 := @Enclosure.norm_gt_of_isNear qz855 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 255804369813444816429 147573952589676412928 1410896288553752900411 

noncomputable def Ns114p2139 := @Ns114p2138 830103483316929822720000 142570391 1342177280 1213 1342177280 (Ns114p2132 (RS115to132.d38 qz126 qz139 qz284) RS115to132.d48) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2140 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz283 (@BSN.thirtyTwoPi_le_dec qz126 357630 1000 qz129 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz854 qz855 (Ns114p2131 rfl rfl) (Ns114p2133 rfl rfl)) (Ns114p2134 qz11 qz129 rfl rfl rfl rfl (Ns114p2136 rfl)) (Ns114p2137 qz11 qz142 rfl rfl rfl rfl (Ns114p2139 rfl)) 

noncomputable abbrev qz856 := (@Enclosure.dec_le_dec qz922 qz926 359184 1000 360736 1000 (@Eq.refl Real qz922) qz929 rfl rfl rfl)

noncomputable abbrev qz610 := qz856

noncomputable abbrev qz285 := (RS115to132.d3 qz484 qz497 qz610)

noncomputable abbrev qz857 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz285)

noncomputable def Ns114p2141 := @Enclosure.Real.IsNear.of_eq qz857 (hardyZApproximantRS₀ qz139) Bool.false 255804369813444816429 147573952589676412928 1410896288553752900411 830103483316929822720000 

noncomputable abbrev qz286 := qz610

noncomputable def Ns114p2142 := @Enclosure.Real.IsNear.pos_val qz857 255804369813444816429 147573952589676412928 1410896288553752900411 830103483316929822720000 (Ns114p2141 (RS115to132.d4 qz139 qz152 qz286) RS115to132.d48) rfl 

noncomputable abbrev qz858 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz285)

noncomputable def Ns114p2143 := @Enclosure.Real.IsNear.of_eq qz858 (hardyZApproximantRS₀ qz152) Bool.true 2461875950747447989 1152921504606846976 708978165335665283339 415051741658464911360000 

noncomputable def Ns114p2144 := @Enclosure.Real.IsNear.neg_val qz858 2461875950747447989 1152921504606846976 708978165335665283339 415051741658464911360000 (Ns114p2143 (RS115to132.d38 qz139 qz152 qz286) RS115to132.d49) rfl 

noncomputable def Ns114p2145 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz857 qz4 qz139 345139 1000 359184 1000 

noncomputable def Ns114p2146 := @Enclosure.norm_gt_of_isNear qz857 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 255804369813444816429 147573952589676412928 1410896288553752900411 

noncomputable def Ns114p2147 := @Ns114p2146 830103483316929822720000 142570391 1342177280 1213 1342177280 (Ns114p2141 (RS115to132.d4 qz139 qz152 qz286) RS115to132.d48) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2148 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz858 qz4 qz152 345139 1000 360736 1000 

noncomputable def Ns114p2149 := @Enclosure.norm_gt_of_isNear qz858 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2461875950747447989 1152921504606846976 708978165335665283339 

noncomputable def Ns114p2150 := @Ns114p2149 415051741658464911360000 142570391 1342177280 1213 1342177280 (Ns114p2143 (RS115to132.d38 qz139 qz152 qz286) RS115to132.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2151 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz285 (@BSN.thirtyTwoPi_le_dec qz139 359184 1000 qz142 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz857 qz858 (Ns114p2142 rfl rfl) (Ns114p2144 rfl rfl)) (Ns114p2145 qz11 qz142 rfl rfl rfl rfl (Ns114p2147 rfl)) (Ns114p2148 qz11 qz155 rfl rfl rfl rfl (Ns114p2150 rfl)) 

noncomputable abbrev qz859 := (@Enclosure.dec_le_dec qz926 qz931 360736 1000 362287 1000 qz929 (@Eq.refl Real qz931) rfl rfl rfl)

noncomputable abbrev qz611 := qz859

noncomputable abbrev qz287 := (RS115to132.d3 qz497 qz510 qz611)

noncomputable abbrev qz860 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz287)

noncomputable def Ns114p2152 := @Enclosure.Real.IsNear.of_eq qz860 (hardyZApproximantRS₀ qz152) Bool.true 2461875950747447989 1152921504606846976 708978165335665283339 415051741658464911360000 

noncomputable abbrev qz288 := qz611

noncomputable def Ns114p2153 := @Enclosure.Real.IsNear.neg_val qz860 2461875950747447989 1152921504606846976 708978165335665283339 415051741658464911360000 (Ns114p2152 (RS115to132.d4 qz152 qz165 qz288) RS115to132.d49) rfl 

noncomputable abbrev qz861 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz287)

noncomputable def Ns114p2154 := @Enclosure.Real.IsNear.of_eq qz861 (hardyZApproximantRS₀ qz165) Bool.false 293850573265534892915 73786976294838206464 95005581530614033141 55340232221128654848000 

noncomputable def Ns114p2155 := @Enclosure.Real.IsNear.pos_val qz861 293850573265534892915 73786976294838206464 95005581530614033141 55340232221128654848000 (Ns114p2154 (RS115to132.d38 qz152 qz165 qz288) RS115to132.d50) rfl 

noncomputable def Ns114p2156 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz860 qz4 qz152 345139 1000 360736 1000 

noncomputable def Ns114p2157 := @Enclosure.norm_gt_of_isNear qz860 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2461875950747447989 1152921504606846976 708978165335665283339 

noncomputable def Ns114p2158 := @Ns114p2157 415051741658464911360000 142570391 1342177280 1213 1342177280 (Ns114p2152 (RS115to132.d4 qz152 qz165 qz288) RS115to132.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2159 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz861 qz4 qz165 345139 1000 362287 1000 

noncomputable def Ns114p2160 := @Enclosure.norm_gt_of_isNear qz861 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 293850573265534892915 73786976294838206464 95005581530614033141 

noncomputable def Ns114p2161 := @Ns114p2160 55340232221128654848000 142570391 1342177280 1213 1342177280 (Ns114p2154 (RS115to132.d38 qz152 qz165 qz288) RS115to132.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2162 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz287 (@BSN.thirtyTwoPi_le_dec qz152 360736 1000 qz155 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz860 qz861 (Ns114p2153 rfl rfl) (Ns114p2155 rfl rfl)) (Ns114p2156 qz11 qz155 rfl rfl rfl rfl (Ns114p2158 rfl)) (Ns114p2159 qz11 qz168 rfl rfl rfl rfl (Ns114p2161 rfl)) 

noncomputable abbrev qz289 := (RS115to132.d3 qz510 qz523 (@Enclosure.dec_le_dec qz510 qz523 362287 1000 363836 1000 qz513 qz526 rfl rfl rfl))

noncomputable abbrev qz862 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz289)

noncomputable def Ns114p2163 := @Enclosure.Real.IsNear.of_eq qz862 (hardyZApproximantRS₀ qz165) Bool.false 293850573265534892915 73786976294838206464 95005581530614033141 55340232221128654848000 

noncomputable abbrev qz290 := (@Enclosure.dec_le_dec qz510 qz523 362287 1000 363836 1000 qz513 qz526 rfl rfl rfl)

noncomputable def Ns114p2164 := @Enclosure.Real.IsNear.pos_val qz862 293850573265534892915 73786976294838206464 95005581530614033141 55340232221128654848000 (Ns114p2163 (RS115to132.d4 qz165 qz178 qz290) RS115to132.d50) rfl 

noncomputable abbrev qz863 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz289)

noncomputable def Ns114p2165 := @Enclosure.Real.IsNear.of_eq qz863 (hardyZApproximantRS₀ qz178) Bool.true 4039786278644996491 2305843009213693952 179108265079980206173 103762935414616227840000 

noncomputable def Ns114p2166 := @Enclosure.Real.IsNear.neg_val qz863 4039786278644996491 2305843009213693952 179108265079980206173 103762935414616227840000 (Ns114p2165 (RS115to132.d38 qz165 qz178 qz290) RS115to132.d51) rfl 

noncomputable def Ns114p2167 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz862 qz4 qz165 345139 1000 362287 1000 

noncomputable def Ns114p2168 := @Enclosure.norm_gt_of_isNear qz862 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 293850573265534892915 73786976294838206464 95005581530614033141 

noncomputable def Ns114p2169 := @Ns114p2168 55340232221128654848000 142570391 1342177280 1213 1342177280 (Ns114p2163 (RS115to132.d4 qz165 qz178 qz290) RS115to132.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2170 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz863 qz4 qz178 345139 1000 363836 1000 

noncomputable def Ns114p2171 := @Enclosure.norm_gt_of_isNear qz863 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 4039786278644996491 2305843009213693952 179108265079980206173 

noncomputable def Ns114p2172 := @Ns114p2171 103762935414616227840000 142570391 1342177280 1213 1342177280 (Ns114p2165 (RS115to132.d38 qz165 qz178 qz290) RS115to132.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2173 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz289 (@BSN.thirtyTwoPi_le_dec qz165 362287 1000 qz168 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz862 qz863 (Ns114p2164 rfl rfl) (Ns114p2166 rfl rfl)) (Ns114p2167 qz11 qz168 rfl rfl rfl rfl (Ns114p2169 rfl)) (Ns114p2170 qz11 qz181 rfl rfl rfl rfl (Ns114p2172 rfl)) 

noncomputable abbrev qz291 := (RS115to132.d3 qz523 qz536 (@Enclosure.dec_le_dec qz523 qz536 363836 1000 365383 1000 qz526 qz539 rfl rfl rfl))

noncomputable abbrev qz864 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz291)

noncomputable def Ns114p2174 := @Enclosure.Real.IsNear.of_eq qz864 (hardyZApproximantRS₀ qz178) Bool.true 4039786278644996491 2305843009213693952 179108265079980206173 103762935414616227840000 

noncomputable abbrev qz292 := (@Enclosure.dec_le_dec qz523 qz536 363836 1000 365383 1000 qz526 qz539 rfl rfl rfl)

noncomputable def Ns114p2175 := @Enclosure.Real.IsNear.neg_val qz864 4039786278644996491 2305843009213693952 179108265079980206173 103762935414616227840000 (Ns114p2174 (RS115to132.d4 qz178 qz191 qz292) RS115to132.d51) rfl 

noncomputable abbrev qz865 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz291)

noncomputable def Ns114p2176 := @Enclosure.Real.IsNear.of_eq qz865 (hardyZApproximantRS₀ qz191) Bool.false 15778664388061940849 9223372036854775808 30017224461435185953 17293822569102704640000 

noncomputable def Ns114p2177 := @Enclosure.Real.IsNear.pos_val qz865 15778664388061940849 9223372036854775808 30017224461435185953 17293822569102704640000 (Ns114p2176 (RS115to132.d38 qz178 qz191 qz292) RS115to132.d52) rfl 

noncomputable def Ns114p2178 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz864 qz4 qz178 345139 1000 363836 1000 

noncomputable def Ns114p2179 := @Enclosure.norm_gt_of_isNear qz864 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 4039786278644996491 2305843009213693952 179108265079980206173 

noncomputable def Ns114p2180 := @Ns114p2179 103762935414616227840000 142570391 1342177280 1213 1342177280 (Ns114p2174 (RS115to132.d4 qz178 qz191 qz292) RS115to132.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2181 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz865 qz4 qz191 345139 1000 365383 1000 

noncomputable def Ns114p2182 := @Enclosure.norm_gt_of_isNear qz865 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 15778664388061940849 9223372036854775808 30017224461435185953 

noncomputable def Ns114p2183 := @Ns114p2182 17293822569102704640000 142570391 1342177280 1213 1342177280 (Ns114p2176 (RS115to132.d38 qz178 qz191 qz292) RS115to132.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2184 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz291 (@BSN.thirtyTwoPi_le_dec qz178 363836 1000 qz181 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz864 qz865 (Ns114p2175 rfl rfl) (Ns114p2177 rfl rfl)) (Ns114p2178 qz11 qz181 rfl rfl rfl rfl (Ns114p2180 rfl)) (Ns114p2181 qz11 qz194 rfl rfl rfl rfl (Ns114p2183 rfl)) 

noncomputable abbrev qz612 := (@Enclosure.dec_le_dec qz771 qz781 365383 1000 366928 1000 (@Eq.refl Real qz771) (@Eq.refl Real qz781) rfl rfl rfl)

noncomputable abbrev qz293 := (RS115to132.d3 qz536 qz549 qz612)

noncomputable abbrev qz866 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz293)

noncomputable def Ns114p2185 := @Enclosure.Real.IsNear.of_eq qz866 (hardyZApproximantRS₀ qz191) Bool.false 15778664388061940849 9223372036854775808 30017224461435185953 17293822569102704640000 

noncomputable abbrev qz294 := qz612

noncomputable def Ns114p2186 := @Enclosure.Real.IsNear.pos_val qz866 15778664388061940849 9223372036854775808 30017224461435185953 17293822569102704640000 (Ns114p2185 (RS115to132.d4 qz191 qz204 qz294) RS115to132.d52) rfl 

noncomputable abbrev qz867 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz293)

noncomputable def Ns114p2187 := @Enclosure.Real.IsNear.of_eq qz867 (hardyZApproximantRS₀ qz204) Bool.true 141226483245612233023 73786976294838206464 144991136628880892639 83010348331692982272000 

noncomputable def Ns114p2188 := @Enclosure.Real.IsNear.neg_val qz867 141226483245612233023 73786976294838206464 144991136628880892639 83010348331692982272000 (Ns114p2187 (RS115to132.d38 qz191 qz204 qz294) RS115to132.d53) rfl 

noncomputable def Ns114p2189 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz866 qz4 qz191 345139 1000 365383 1000 

noncomputable def Ns114p2190 := @Enclosure.norm_gt_of_isNear qz866 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 15778664388061940849 9223372036854775808 30017224461435185953 

noncomputable def Ns114p2191 := @Ns114p2190 17293822569102704640000 142570391 1342177280 1213 1342177280 (Ns114p2185 (RS115to132.d4 qz191 qz204 qz294) RS115to132.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2192 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz867 qz4 qz204 345139 1000 366928 1000 

noncomputable def Ns114p2193 := @Enclosure.norm_gt_of_isNear qz867 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 141226483245612233023 73786976294838206464 144991136628880892639 

noncomputable def Ns114p2194 := @Ns114p2193 83010348331692982272000 142570391 1342177280 1213 1342177280 (Ns114p2187 (RS115to132.d38 qz191 qz204 qz294) RS115to132.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2195 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz293 (@BSN.thirtyTwoPi_le_dec qz191 365383 1000 qz194 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz866 qz867 (Ns114p2186 rfl rfl) (Ns114p2188 rfl rfl)) (Ns114p2189 qz11 qz194 rfl rfl rfl rfl (Ns114p2191 rfl)) (Ns114p2192 qz11 qz207 rfl rfl rfl rfl (Ns114p2194 rfl)) 

noncomputable abbrev qz613 := (@Enclosure.dec_le_dec qz781 qz792 366928 1000 368472 1000 (@Eq.refl Real qz781) qz796 rfl rfl rfl)

noncomputable abbrev qz295 := (RS115to132.d3 qz549 qz561 qz613)

noncomputable abbrev qz868 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz295)

noncomputable def Ns114p2196 := @Enclosure.Real.IsNear.of_eq qz868 (hardyZApproximantRS₀ qz204) Bool.true 141226483245612233023 73786976294838206464 144991136628880892639 83010348331692982272000 

noncomputable abbrev qz296 := qz613

noncomputable def Ns114p2197 := @Enclosure.Real.IsNear.neg_val qz868 141226483245612233023 73786976294838206464 144991136628880892639 83010348331692982272000 (Ns114p2196 (RS115to132.d4 qz204 qz217 qz296) RS115to132.d53) rfl 

noncomputable abbrev qz869 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz295)

noncomputable def Ns114p2198 := @Enclosure.Real.IsNear.of_eq qz869 (hardyZApproximantRS₀ qz217) Bool.false 177731463365635263965 295147905179352825856 2919933434539691233709 Ns114p1635 

noncomputable def Ns114p2199 := @Enclosure.Real.IsNear.pos_val qz869 177731463365635263965 295147905179352825856 2919933434539691233709 Ns114p1635 (Ns114p2198 (RS115to132.d38 qz204 qz217 qz296) RS115to132.d54) rfl 

noncomputable def Ns114p2200 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz868 qz4 qz204 345139 1000 366928 1000 

noncomputable def Ns114p2201 := @Enclosure.norm_gt_of_isNear qz868 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 141226483245612233023 73786976294838206464 144991136628880892639 

noncomputable def Ns114p2202 := @Ns114p2201 83010348331692982272000 142570391 1342177280 1213 1342177280 (Ns114p2196 (RS115to132.d4 qz204 qz217 qz296) RS115to132.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2203 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz869 qz4 qz217 345139 1000 368472 1000 

noncomputable def Ns114p2204 := @Enclosure.norm_gt_of_isNear qz869 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 177731463365635263965 295147905179352825856 2919933434539691233709 

noncomputable def Ns114p2205 := @Ns114p2204 Ns114p1635 142570391 1342177280 1213 1342177280 (Ns114p2198 (RS115to132.d38 qz204 qz217 qz296) RS115to132.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2206 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz295 (@BSN.thirtyTwoPi_le_dec qz204 366928 1000 qz207 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz868 qz869 (Ns114p2197 rfl rfl) (Ns114p2199 rfl rfl)) (Ns114p2200 qz11 qz207 rfl rfl rfl rfl (Ns114p2202 rfl)) (Ns114p2203 qz11 qz220 rfl rfl rfl rfl (Ns114p2205 rfl)) 

noncomputable abbrev qz614 := (@Enclosure.dec_le_dec qz792 qz804 368472 1000 370015 1000 qz796 qz808 rfl rfl rfl)

noncomputable abbrev qz297 := (RS115to132.d3 qz561 qz573 qz614)

noncomputable abbrev qz870 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz297)

noncomputable def Ns114p2207 := @Enclosure.Real.IsNear.of_eq qz870 (hardyZApproximantRS₀ qz217) Bool.false 177731463365635263965 295147905179352825856 2919933434539691233709 Ns114p1635 

noncomputable abbrev qz298 := qz614

noncomputable def Ns114p2208 := @Enclosure.Real.IsNear.pos_val qz870 177731463365635263965 295147905179352825856 2919933434539691233709 Ns114p1635 (Ns114p2207 (RS115to132.d4 qz217 qz230 qz298) RS115to132.d54) rfl 

noncomputable abbrev qz871 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz297)

noncomputable def Ns114p2209 := @Enclosure.Real.IsNear.of_eq qz871 (hardyZApproximantRS₀ qz230) Bool.true 1266607219341763855 9223372036854775808 817682770801120511 461168601842738790400 

noncomputable def Ns114p2210 := @Enclosure.Real.IsNear.neg_val qz871 1266607219341763855 9223372036854775808 817682770801120511 461168601842738790400 (Ns114p2209 (RS115to132.d38 qz217 qz230 qz298) RS115to132.d55) rfl 

noncomputable def Ns114p2211 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz870 qz4 qz217 345139 1000 368472 1000 

noncomputable def Ns114p2212 := @Enclosure.norm_gt_of_isNear qz870 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 177731463365635263965 295147905179352825856 2919933434539691233709 

noncomputable def Ns114p2213 := @Ns114p2212 Ns114p1635 142570391 1342177280 1213 1342177280 (Ns114p2207 (RS115to132.d4 qz217 qz230 qz298) RS115to132.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2214 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz871 qz4 qz230 345139 1000 370015 1000 

noncomputable def Ns114p2215 := @Enclosure.norm_gt_of_isNear qz871 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1266607219341763855 9223372036854775808 817682770801120511 

noncomputable def Ns114p2216 := @Ns114p2215 461168601842738790400 142570391 1342177280 1213 1342177280 (Ns114p2209 (RS115to132.d38 qz217 qz230 qz298) RS115to132.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2217 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz297 (@BSN.thirtyTwoPi_le_dec qz217 368472 1000 qz220 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz870 qz871 (Ns114p2208 rfl rfl) (Ns114p2210 rfl rfl)) (Ns114p2211 qz11 qz220 rfl rfl rfl rfl (Ns114p2213 rfl)) (Ns114p2214 qz11 qz233 rfl rfl rfl rfl (Ns114p2216 rfl)) 

noncomputable abbrev qz872 := (@Enclosure.dec_le_dec qz951 qz955 370015 1000 371556 1000 (@Eq.refl Real qz951) qz958 rfl rfl rfl)

noncomputable abbrev qz615 := qz872

noncomputable abbrev qz299 := (RS115to132.d3 qz573 qz585 qz615)

noncomputable abbrev qz873 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz299)

noncomputable def Ns114p2218 := @Enclosure.Real.IsNear.of_eq qz873 (hardyZApproximantRS₀ qz230) Bool.true 1266607219341763855 9223372036854775808 817682770801120511 461168601842738790400 

noncomputable abbrev qz300 := qz615

noncomputable def Ns114p2219 := @Enclosure.Real.IsNear.neg_val qz873 1266607219341763855 9223372036854775808 817682770801120511 461168601842738790400 (Ns114p2218 (RS115to132.d4 qz230 qz243 qz300) RS115to132.d55) rfl 

noncomputable abbrev qz874 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz299)

noncomputable def Ns114p2220 := @Enclosure.Real.IsNear.of_eq qz874 (hardyZApproximantRS₀ qz243) Bool.false 2181893164414302701 288230376151711744 82614488722072502643 46116860184273879040000 

noncomputable def Ns114p2221 := @Enclosure.Real.IsNear.pos_val qz874 2181893164414302701 288230376151711744 82614488722072502643 46116860184273879040000 (Ns114p2220 (RS115to132.d38 qz230 qz243 qz300) RS115to132.d56) rfl 

noncomputable def Ns114p2222 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz873 qz4 qz230 345139 1000 370015 1000 

noncomputable def Ns114p2223 := @Enclosure.norm_gt_of_isNear qz873 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1266607219341763855 9223372036854775808 817682770801120511 

noncomputable def Ns114p2224 := @Ns114p2223 461168601842738790400 142570391 1342177280 1213 1342177280 (Ns114p2218 (RS115to132.d4 qz230 qz243 qz300) RS115to132.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2225 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz874 qz4 qz243 345139 1000 371556 1000 

noncomputable def Ns114p2226 := @Enclosure.norm_gt_of_isNear qz874 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2181893164414302701 288230376151711744 82614488722072502643 

noncomputable def Ns114p2227 := @Ns114p2226 46116860184273879040000 142570391 1342177280 1213 1342177280 (Ns114p2220 (RS115to132.d38 qz230 qz243 qz300) RS115to132.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2228 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz299 (@BSN.thirtyTwoPi_le_dec qz230 370015 1000 qz233 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz873 qz874 (Ns114p2219 rfl rfl) (Ns114p2221 rfl rfl)) (Ns114p2222 qz11 qz233 rfl rfl rfl rfl (Ns114p2224 rfl)) (Ns114p2225 qz11 qz246 rfl rfl rfl rfl (Ns114p2227 rfl)) 

noncomputable abbrev qz962 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 371556 1000) (Enclosure.sfrac Bool.false 373095 1000) 371556 1000 373095 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 371556 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 373095 1000)) rfl rfl rfl)

noncomputable abbrev qz875 := qz962

noncomputable abbrev qz616 := qz875

noncomputable abbrev qz301 := (RS115to132.d3 qz585 qz597 qz616)

noncomputable abbrev qz876 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz301)

noncomputable def Ns114p2229 := @Enclosure.Real.IsNear.of_eq qz876 (hardyZApproximantRS₀ qz243) Bool.false 2181893164414302701 288230376151711744 82614488722072502643 46116860184273879040000 

noncomputable abbrev qz302 := qz616

noncomputable def Ns114p2230 := @Enclosure.Real.IsNear.pos_val qz876 2181893164414302701 288230376151711744 82614488722072502643 46116860184273879040000 (Ns114p2229 (RS115to132.d4 qz243 qz256 qz302) RS115to132.d56) rfl 

noncomputable abbrev qz877 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz301)

noncomputable def Ns114p2231 := @Enclosure.Real.IsNear.of_eq qz877 (hardyZApproximantRS₀ qz256) Bool.true 2059803477868761821 18446744073709551616 2014954605823717267 1106804644422573096960 

noncomputable def Ns114p2232 := @Enclosure.Real.IsNear.neg_val qz877 2059803477868761821 18446744073709551616 2014954605823717267 1106804644422573096960 (Ns114p2231 (RS115to132.d38 qz243 qz256 qz302) RS115to132.d57) rfl 

noncomputable def Ns114p2233 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz876 qz4 qz243 345139 1000 371556 1000 

noncomputable def Ns114p2234 := @Enclosure.norm_gt_of_isNear qz876 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2181893164414302701 288230376151711744 82614488722072502643 

noncomputable def Ns114p2235 := @Ns114p2234 46116860184273879040000 142570391 1342177280 1213 1342177280 (Ns114p2229 (RS115to132.d4 qz243 qz256 qz302) RS115to132.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2236 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz877 qz4 qz256 345139 1000 373095 1000 

noncomputable def Ns114p2237 := @Enclosure.norm_gt_of_isNear qz877 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2059803477868761821 18446744073709551616 2014954605823717267 

noncomputable def Ns114p2238 := @Ns114p2237 1106804644422573096960 142570391 1342177280 1213 1342177280 (Ns114p2231 (RS115to132.d38 qz243 qz256 qz302) RS115to132.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 142570391 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS115to132.d40) rfl rfl rfl rfl 

noncomputable def Ns114p2239 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz301 (@BSN.thirtyTwoPi_le_dec qz243 371556 1000 qz246 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz876 qz877 (Ns114p2230 rfl rfl) (Ns114p2232 rfl rfl)) (Ns114p2233 qz11 qz246 rfl rfl rfl rfl (Ns114p2235 rfl)) (Ns114p2236 qz11 (@Eq.refl Real qz256) rfl rfl rfl rfl (Ns114p2238 rfl)) 

noncomputable def Ns114p2240 := @List.cons RS115to132.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz299 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz299) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz299) Ns114p2228)) (@List.cons RS115to132.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz301 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz301) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz301) Ns114p2239)) (@List.nil RS115to132.d0)) 

noncomputable def Ns114p2241 := @List.cons RS115to132.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz295 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz295) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz295) Ns114p2206)) (@List.cons RS115to132.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz297 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz297) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz297) Ns114p2217)) Ns114p2240) 

noncomputable def Ns114p2242 := @List.cons RS115to132.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz291 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz291) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz291) Ns114p2184)) (@List.cons RS115to132.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz293 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz293) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz293) Ns114p2195)) Ns114p2241) 

noncomputable def Ns114p2243 := @List.cons RS115to132.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz287 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz287) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz287) Ns114p2162)) (@List.cons RS115to132.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz289 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz289) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz289) Ns114p2173)) Ns114p2242) 

noncomputable def Ns114p2244 := @List.cons RS115to132.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz283 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz283) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz283) Ns114p2140)) (@List.cons RS115to132.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz285 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz285) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz285) Ns114p2151)) Ns114p2243) 

noncomputable def Ns114p2245 := @List.cons RS115to132.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz279 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz279) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz279) Ns114p2118)) (@List.cons RS115to132.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz281 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz281) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz281) Ns114p2129)) Ns114p2244) 

noncomputable def Ns114p2246 := @List.cons RS115to132.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz275 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz275) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz275) Ns114p2096)) (@List.cons RS115to132.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz277 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz277) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz277) Ns114p2107)) Ns114p2245) 

noncomputable def Ns114p2247 := @List.cons RS115to132.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz271 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz271) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz271) Ns114p2074)) (@List.cons RS115to132.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz273 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz273) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz273) Ns114p2085)) Ns114p2246) 

noncomputable def Ns114p2248 := @List.cons RS115to132.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz267 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz267) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz267) Ns114p2052)) (@List.cons RS115to132.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz269 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz269) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz269) Ns114p2063)) Ns114p2247) 

noncomputable abbrev qz878 := (RS115to132.d2 qz951 qz955 (@Enclosure.dec_le_dec qz951 qz955 370015 1000 371556 1000 (@Eq.refl Real qz951) qz958 rfl rfl rfl))

noncomputable abbrev qz879 := (@List.cons RS115to132.d1 (RS115to132.d2 qz955 qz960 qz962) (@List.nil RS115to132.d1))

noncomputable abbrev qz617 := (@List.cons RS115to132.d1 (RS115to132.d2 qz792 qz804 (@Enclosure.dec_le_dec qz792 qz804 368472 1000 370015 1000 qz796 qz808 rfl rfl rfl)) (@List.cons RS115to132.d1 qz878 qz879))

noncomputable abbrev qz303 := (@List.cons RS115to132.d1 (RS115to132.d2 qz536 qz549 qz612) (@List.cons RS115to132.d1 (RS115to132.d2 qz549 qz561 qz613) qz617))

noncomputable def Ns114p2249 := @List.cons RS115to132.d1 (RS115to132.d2 qz165 qz178 qz290) (@List.cons RS115to132.d1 (RS115to132.d2 qz178 qz191 qz292) qz303) 

noncomputable abbrev qz880 := (RS115to132.d2 qz922 qz926 (@Enclosure.dec_le_dec qz922 qz926 359184 1000 360736 1000 (@Eq.refl Real qz922) qz929 rfl rfl rfl))

noncomputable abbrev qz881 := (RS115to132.d2 qz926 qz931 (@Enclosure.dec_le_dec qz926 qz931 360736 1000 362287 1000 qz929 (@Eq.refl Real qz931) rfl rfl rfl))

noncomputable abbrev qz618 := (@List.cons RS115to132.d1 (RS115to132.d2 qz716 qz727 (@Enclosure.dec_le_dec qz716 qz727 357630 1000 359184 1000 qz720 qz731 rfl rfl rfl)) (@List.cons RS115to132.d1 qz880 (@List.cons RS115to132.d1 qz881 Ns114p2249)))

noncomputable abbrev qz304 := (@List.cons RS115to132.d1 (RS115to132.d2 qz443 qz458 qz607) (@List.cons RS115to132.d1 (RS115to132.d2 qz458 qz471 qz608) qz618))

noncomputable def Ns114p2250 := @List.cons RS115to132.d1 (RS115to132.d2 qz74 qz87 qz276) (@List.cons RS115to132.d1 (RS115to132.d2 qz87 qz100 qz278) qz304) 

noncomputable def Ns114p2251 := @List.IsChain.cons_cons RS115to132.d1 RS115to132.d58 (RS115to132.d2 qz61 qz74 qz274) (RS115to132.d2 qz74 qz87 qz276) (@List.cons RS115to132.d1 (RS115to132.d2 qz87 qz100 qz278) qz304) 

noncomputable def Ns114p2252 := @List.IsChain.cons_cons RS115to132.d1 RS115to132.d58 (RS115to132.d2 qz74 qz87 qz276) (RS115to132.d2 qz87 qz100 qz278) qz304 (@Enclosure.dec_le_dec qz87 qz87 352959 1000 352959 1000 qz90 qz90 rfl rfl rfl) 

noncomputable abbrev qz619 := qz881

noncomputable abbrev qz305 := qz619

noncomputable def Ns114p2253 := @List.IsChain.cons_cons RS115to132.d1 RS115to132.d58 qz305 (RS115to132.d2 qz165 qz178 qz290) (@List.cons RS115to132.d1 (RS115to132.d2 qz178 qz191 qz292) qz303) 

noncomputable def Ns114p2254 := @List.IsChain.cons_cons RS115to132.d1 RS115to132.d58 (RS115to132.d2 qz165 qz178 qz290) (RS115to132.d2 qz178 qz191 qz292) qz303 (@Enclosure.dec_le_dec qz178 qz178 363836 1000 363836 1000 qz181 qz181 rfl rfl rfl) 

noncomputable abbrev qz306 := qz617

noncomputable abbrev qz620 := (@List.cons RS115to132.d1 qz878 qz879)

noncomputable abbrev qz307 := qz620

noncomputable abbrev qz621 := qz878

noncomputable abbrev qz308 := qz621

noncomputable abbrev qz622 := qz879

noncomputable abbrev qz309 := qz622

noncomputable abbrev qz882 := (RS115to132.d2 qz955 qz960 qz962)

noncomputable abbrev qz623 := qz882

noncomputable abbrev qz310 := qz623

noncomputable def Ns114p2255 := @List.IsChain.cons_cons RS115to132.d1 RS115to132.d58 (RS115to132.d2 qz191 qz204 qz294) (RS115to132.d2 qz204 qz217 qz296) qz306 (@Enclosure.dec_le_dec qz204 qz204 366928 1000 366928 1000 qz207 qz207 rfl rfl rfl) (@List.IsChain.cons_cons RS115to132.d1 RS115to132.d58 (RS115to132.d2 qz204 qz217 qz296) (RS115to132.d2 qz217 qz230 qz298) qz307 (@Enclosure.dec_le_dec qz217 qz217 368472 1000 368472 1000 qz220 qz220 rfl rfl rfl) (@List.IsChain.cons_cons RS115to132.d1 RS115to132.d58 (RS115to132.d2 qz217 qz230 qz298) qz308 qz309 (@Enclosure.dec_le_dec qz230 qz230 370015 1000 370015 1000 qz233 qz233 rfl rfl rfl) (@List.IsChain.cons_cons RS115to132.d1 RS115to132.d58 qz308 qz310 (@List.nil RS115to132.d1) (@Enclosure.dec_le_dec qz243 qz243 371556 1000 371556 1000 qz246 qz246 rfl rfl rfl) (@List.IsChain.singleton RS115to132.d1 RS115to132.d58 qz310)))) 

noncomputable abbrev qz311 := (@List.cons RS115to132.d1 (RS115to132.d2 qz549 qz561 qz613) qz617)

noncomputable def Ns114p2256 := @List.IsChain.cons_cons RS115to132.d1 RS115to132.d58 (RS115to132.d2 qz178 qz191 qz292) (RS115to132.d2 qz191 qz204 qz294) qz311 (@Enclosure.dec_le_dec qz191 qz191 365383 1000 365383 1000 qz194 qz194 rfl rfl rfl) Ns114p2255 

noncomputable abbrev qz312 := qz618

noncomputable abbrev qz624 := (@List.cons RS115to132.d1 qz880 (@List.cons RS115to132.d1 qz881 Ns114p2249))

noncomputable abbrev qz313 := qz624

noncomputable abbrev qz625 := qz880

noncomputable abbrev qz314 := qz625

noncomputable def Ns114p2257 := @List.IsChain.cons_cons RS115to132.d1 RS115to132.d58 (RS115to132.d2 qz100 qz113 qz280) (RS115to132.d2 qz113 qz126 qz282) qz312 (@Enclosure.dec_le_dec qz113 qz113 356075 1000 356075 1000 qz116 qz116 rfl rfl rfl) (@List.IsChain.cons_cons RS115to132.d1 RS115to132.d58 (RS115to132.d2 qz113 qz126 qz282) (RS115to132.d2 qz126 qz139 qz284) qz313 (@Enclosure.dec_le_dec qz126 qz126 357630 1000 357630 1000 qz129 qz129 rfl rfl rfl) (@List.IsChain.cons_cons RS115to132.d1 RS115to132.d58 (RS115to132.d2 qz126 qz139 qz284) qz314 (@List.cons RS115to132.d1 qz305 Ns114p2249) (@Enclosure.dec_le_dec qz139 qz139 359184 1000 359184 1000 qz142 qz142 rfl rfl rfl) (@List.IsChain.cons_cons RS115to132.d1 RS115to132.d58 qz314 qz305 Ns114p2249 (@Enclosure.dec_le_dec qz152 qz152 360736 1000 360736 1000 qz155 qz155 rfl rfl rfl) (Ns114p2253 (@Enclosure.dec_le_dec qz165 qz165 362287 1000 362287 1000 qz168 qz168 rfl rfl rfl) (Ns114p2254 Ns114p2256))))) 

noncomputable abbrev qz315 := (@List.cons RS115to132.d1 (RS115to132.d2 qz458 qz471 qz608) qz618)

noncomputable def Ns114p2258 := @List.IsChain.cons_cons RS115to132.d1 RS115to132.d58 (RS115to132.d2 qz87 qz100 qz278) (RS115to132.d2 qz100 qz113 qz280) qz315 (@Enclosure.dec_le_dec qz100 qz100 354518 1000 354518 1000 qz103 qz103 rfl rfl rfl) Ns114p2257 

noncomputable def Ns114p2259 := Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns114p2248 (@List.IsChain.cons_cons RS115to132.d1 RS115to132.d58 (RS115to132.d2 qz4 qz29 qz268) (RS115to132.d2 qz29 qz48 qz270) (@List.cons RS115to132.d1 (RS115to132.d2 qz48 qz61 qz272) (@List.cons RS115to132.d1 (RS115to132.d2 qz61 qz74 qz274) Ns114p2250)) (@Enclosure.dec_le_dec qz29 qz29 346706 1000 346706 1000 qz32 qz32 rfl rfl rfl) (@List.IsChain.cons_cons RS115to132.d1 RS115to132.d58 (RS115to132.d2 qz29 qz48 qz270) (RS115to132.d2 qz48 qz61 qz272) (@List.cons RS115to132.d1 (RS115to132.d2 qz61 qz74 qz274) Ns114p2250) (@Enclosure.dec_le_dec qz48 qz48 348272 1000 348272 1000 qz51 qz51 rfl rfl rfl) (@List.IsChain.cons_cons RS115to132.d1 RS115to132.d58 (RS115to132.d2 qz48 qz61 qz272) (RS115to132.d2 qz61 qz74 qz274) Ns114p2250 (@Enclosure.dec_le_dec qz61 qz61 349836 1000 349836 1000 qz64 qz64 rfl rfl rfl) (Ns114p2251 (@Enclosure.dec_le_dec qz74 qz74 351398 1000 351398 1000 qz77 qz77 rfl rfl rfl) (Ns114p2252 Ns114p2258))))) 

noncomputable abbrev qz626 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz627 := (Zeta.Certificates.CertifiedZeroIntervals.intervals Ns114p2259)

theorem RS115to132.d59 : Zeta.Certificates.BatchSpec 18 345139 1000 373095 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz626 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 18) (And (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz626 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz626 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz256)))) Ns114p2259 (@And.intro (@Eq Nat (@List.length qz626 qz627) 18) (And (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz626 qz627)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz626 qz627)) (@Option.some Real qz256))) (@Eq.refl Nat 18) (@And.intro (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz626 qz627)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz626 qz627)) (@Option.some Real qz256)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz256))))

theorem solution : Zeta.Certificates.BatchSpec 18 345139 1000 373095 1000 := RS115to132.d59
#print axioms solution
#check solution
