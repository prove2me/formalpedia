-- Prove2me | solution 1 for RHHeight1000.rs_main_0097_0114
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T21:54:10.892421+00:00
-- url     : https://prove2.me/submissions/3ecffda3-98c8-48a2-9e72-8d67db6fce1d

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

noncomputable def RS097to114.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS097to114.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS097to114.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS097to114.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS097to114.d2 a b h 

theorem RS097to114.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS097to114.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS097to114.d3 a b h)) 

noncomputable def Ns96p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns96p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns96p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns96p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns96p0 Ns96p1 Ns96p2 Ns96p1 76821522 67108864 1 19360000 76821522 67108864 1 19360000 38410761 33554432 2 33554432 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns96p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns96p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns96p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns96p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns96p8 := nat_lit 4564579050430662680769181008104061220617401457132102377181523838895616693352443067851710738206186456870068891932464934433532008760270543541307416978974983178670584632435273151991067990877911260800542253584783113678675870571765297427794279500566373840368605043192397583789219721854001914445657820861544585749419999617014263230075963405112904900127091763553068379337562290951837345169106631254289648555755847509739637528572205479767112592191328488981867735095152085893116377698979776390335134938272744697179058821035388170748994050345731998297589980525805272027148669105172128531226596705145339433394591280230580530674088894892093599627198529211479716891686479023042798211193766875 

noncomputable def Ns96p9 := nat_lit 487897090127139370915718269131278067469793404735814825511781216300711748025172292443098109798278438646340651351778930478625246708087138935333656000353278407183834741097045313633566773106147391845370902603761794798142555380136213880615811008223525988937457841388015247818375543397617608528881621312159551521324412657167692163397240217814307445909713899850058291308690066733028125556419716734774904437710284132364898181426902860503703874999414246848733477446908396851600224567407637334679631394476122651438668110771117818686943497967108192010818356995023330089079080278635386063923383437486637555787861728490935630579993241432729945572572039527546968749899721199864050991936636425 

noncomputable def Ns96p10 := nat_lit 6037312065319767048564142443281100833094517501602298457411621838401909436348967513970575877459259771623941548258204445821942291045664120860093665600098153114527011142424471743215189638406506367790367599859596104992621477169994698594142049192256667252266301439715334971326182286325870243632349119406725171166047972624848379242642987691741446913322611634487665631123884299676351857591585933871955560195724863436092564725843702568563820604138142931407752731605404492259322164906548421338089777140624840599546449293504664341809058329304227251421882253537858630692969727217927909816425536009981778974686700833928275616694615814871054602955126209568752228017149733267081250625 

noncomputable def Ns96p11 := BSN.log_dyadic_bound Ns96p6 Ns96p7 14 13 Ns96p8 67108864 19360000 Ns96p9 Ns96p10 76821522 Ns96p4 Ns96p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP Ns96p6) (BSN.artanhQ Ns96p7) 0 13 Ns96p9 Ns96p8 Ns96p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns96p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns96p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns96p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns96p15 := nat_lit 4564579050430719991598727864173574027249459620864950728835381976489772818715667160654947079996042508112007609792086902604246591277951902079645511578729044446029890641532783292129843149875777032317116470385319181253925715321425403083930304095443896121595862314424397722115177325385869596477930511910402142030838288588290691454497602943515837117442179176528567975378491450565217634156690207739385924001994080445739653712153122146143735369275124802705327973995316801123426696765469161725178407791303143690561306079033018690304653273985689879967765287476386100315971524212560669782530460797364817008851488910076252022325883262600059844010859170953904690437223359663042798211193766875 

noncomputable def Ns96p16 := nat_lit 487897090127146028016094362581487656757614504303373888298359177917068925336311225982425876767220472971199663852495703606478044548245204650969304786130313739004418091807374551157966311600460925549125369213480618028519005676490156484647720769146106466452899814849266557198964140238149260938822380107756357944282785296375303842904282420173433118269847736574242174913483374429734863225743639963757643848706968740179283875896315642693907130861939137742544595612595383386022728925244773380688186919137495322289344312028838765525860232491884325012249877491080249836360703014994786844727995613684463741175252463635603207543937219860925630575346787413234983278028650172664050991936636425 

noncomputable def Ns96p17 := nat_lit 6037312065319913640506765330482094651728996212510072186683329349665034025528265882310343281188309943135362157762326025787898903072857099500666458772539172249805276355211909724494669715550462680374559205875381267976760313571991112548079805305194151041203595124480241065931717334103047325628819416103687949050116922196393250525830281764599302835242983634853487222885409728030646963007168165596579721200854339637057218394652367706804217404799249814690071011337988816707639904852988452679974011323771101001271418584434659185032723127441286381829860978672625319259709832419206399165424340759332155638209605427889981579187342651500575472600628768480466654897149733267081250625 

noncomputable def Ns96p18 := BSN.log_dyadic_bound Ns96p13 Ns96p14 14 13 Ns96p15 67108864 19360000 Ns96p16 Ns96p17 76821522 Ns96p12 Ns96p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP Ns96p13) (BSN.artanhQ Ns96p14) 0 13 Ns96p16 Ns96p15 Ns96p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns96p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 38410761 33554432 2 33554432 38410761 33554432 1 16777216 (Ns96p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns96p0 Ns96p1 76821522 67108864 1 19360000 Bool.false (BSN.logfrac_isNear Ns96p4 Ns96p5 1 Ns96p0 Ns96p1 76821522 67108864 19360000 rfl rfl rfl (Ns96p11 rfl))) (BSN.isNear_log_sfrac Ns96p2 Ns96p1 76821522 67108864 1 19360000 Bool.false (BSN.logfrac_isNear Ns96p12 Ns96p5 1 Ns96p2 Ns96p1 76821522 67108864 19360000 rfl rfl rfl (Ns96p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS097to114.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 16777216 := Ns96p19 

noncomputable def Ns96p20 := BSN.log_dyadic_bound 1 3 7 6 71816279535 4194304 1210000 2852596872 10395 2907269 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1) (BSN.artanhQ 3) 0 6 2852596872 71816279535 10395 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz316 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz0 := qz316

theorem RS097to114.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 2907269 4194304 1 1210000 := BSN.isNear_log_sfrac 2 1 2907269 4194304 1 1210000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 2907269 4194304 1210000 rfl rfl rfl (Ns96p20 rfl)) 

theorem RS097to114.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 46516304 67108864 56 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 2907269 4194304 1 1210000 46516304 67108864 56 67108864 RS097to114.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz319 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def Ns96p21 := @Enclosure.Real.IsNear.inv_image qz317 11863283 8388608 1 8388608 2965820 2965822 4194304 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 11863283 8388608 1 8388608 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 11863283 8388608 1 8388608 11863283 8388608 1 8388608 (BSN.sqrt_enclosure 2 1 5931641 5931642 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS097to114.d8 : Enclosure.Real.IsNear qz320 Bool.false 2965821 4194304 1 4194304 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 5931642 8388608 2 8388608 2965821 4194304 1 4194304 (Ns96p21 rfl rfl) rfl 

theorem RS097to114.d9 : Enclosure.Real.IsNear qz320 Bool.false 47453136 67108864 16 67108864 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 2965821 4194304 1 4194304 47453136 67108864 16 67108864 RS097to114.d8 rfl 

noncomputable def Ns96p22 := BSN.log_dyadic_bound 1 2 12 11 1326382131865190400 4194304 1210000 130797573554866995 13749310575 4607913 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 1) (BSN.artanhQ 2) 0 11 130797573554866995 1326382131865190400 13749310575 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS097to114.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 4607913 4194304 1 1210000 := BSN.isNear_log_sfrac 3 1 4607913 4194304 1 1210000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 4607913 4194304 1210000 rfl rfl rfl (Ns96p22 rfl)) 

theorem RS097to114.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 73726608 67108864 56 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 4607913 4194304 1 1210000 73726608 67108864 56 67108864 RS097to114.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns96p23 := @Enclosure.Real.IsNear.inv_image qz321 14529495 8388608 1 8388608 2421582 2421583 4194304 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 14529495 8388608 1 8388608 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 14529495 8388608 1 8388608 14529495 8388608 1 8388608 (BSN.sqrt_enclosure 3 1 7264747 7264748 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS097to114.d12 : Enclosure.Real.IsNear qz323 Bool.false 4843165 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 4843165 8388608 1 8388608 4843165 8388608 1 8388608 (Ns96p23 rfl rfl) rfl 

theorem RS097to114.d13 : Enclosure.Real.IsNear qz323 Bool.false 38745320 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 4843165 8388608 1 8388608 38745320 67108864 8 67108864 RS097to114.d12 rfl 

noncomputable def Ns96p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns96p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns96p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns96p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns96p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns96p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns96p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns96p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns96p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns96p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns96p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns96p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns96p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns96p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns96p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns96p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns96p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns96p25 Ns96p26 Ns96p27 Ns96p28 200200021673987500790625 Ns96p29 Ns96p30 Ns96p31 Ns96p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns96p32 Ns96p33 151412625 Ns96p34 Ns96p35 1322214852783825 Ns96p27 Ns96p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns96p32 Ns96p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns96p34 Ns96p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns96p36 Ns96p37 1267389585 Ns96p38 Ns96p39 1927077560082675 Ns96p29 Ns96p30 Ns96p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns96p36 Ns96p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns96p38 Ns96p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS097to114.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns96p24 Ns96p25 1 Ns96p26 := Ns96p40 rfl rfl rfl 

noncomputable def Ns96p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns96p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns96p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns96p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns96p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns96p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns96p25 Ns96p26 Ns96p42 Ns96p43 9945 Ns96p44 Ns96p45 65835 Ns96p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns96p42 Ns96p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns96p44 Ns96p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS097to114.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns96p41 Ns96p25 1 Ns96p26 := Ns96p46 rfl 

noncomputable def Ns96p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns96p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS097to114.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns96p47 Ns96p25 1 Ns96p48 := BSN.pi_combine Ns96p24 Ns96p41 Ns96p25 Ns96p26 Ns96p48 Ns96p47 rfl rfl rfl rfl RS097to114.d14 RS097to114.d15 

theorem RS097to114.d17 : Enclosure.Real.IsNear Real.pi Bool.false 3537118876014220 1125899906842624 1 1125899906842624 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns96p47 Ns96p25 1 Ns96p48 3537118876014220 1125899906842624 1 1125899906842624 RS097to114.d16 rfl 

noncomputable def Ns96p49 := nat_lit 178719669545544893480837345123291015625 

noncomputable def Ns96p50 := nat_lit 27745388228251122714770036239987464375 

noncomputable def Ns96p51 := nat_lit 1274524447665412456340166714375 

noncomputable def Ns96p52 := BSN.log_dyadic_bound 3 5 16 15 Ns96p49 4194304 1210000 Ns96p50 Ns96p51 5814539 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP 3) (BSN.artanhQ 5) 0 15 Ns96p50 Ns96p49 Ns96p51 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS097to114.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 5814539 4194304 1 1210000 := BSN.isNear_log_sfrac 4 1 5814539 4194304 1 1210000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 5814539 4194304 1210000 rfl rfl rfl (Ns96p52 rfl)) 

theorem RS097to114.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 93032624 67108864 56 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 5814539 4194304 1 1210000 93032624 67108864 56 67108864 RS097to114.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns96p53 := @Enclosure.Real.IsNear.inv_image qz325 16777217 8388608 1 8388608 2097151 2097152 4194304 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 16777217 8388608 1 8388608 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 16777217 8388608 1 8388608 16777217 8388608 1 8388608 (BSN.sqrt_enclosure 4 1 8388608 8388609 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS097to114.d20 : Enclosure.Real.IsNear qz327 Bool.false 4194303 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 4194303 8388608 1 8388608 4194303 8388608 1 8388608 (Ns96p53 rfl rfl) rfl 

theorem RS097to114.d21 : Enclosure.Real.IsNear qz327 Bool.false 33554424 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 4194303 8388608 1 8388608 33554424 67108864 8 67108864 RS097to114.d20 rfl 

noncomputable def Ns96p54 := nat_lit 432044237847189949652629901200995702590625 

noncomputable def Ns96p55 := nat_lit 89467042677079332529401996239971435345500 

noncomputable def Ns96p56 := nat_lit 2254217236409302326906244300800000 

noncomputable def Ns96p57 := nat_lit 1703271991756449094855875 

noncomputable def Ns96p58 := BSN.log_dyadic_bound 2 3 20 19 Ns96p54 4194304 1210000 Ns96p55 Ns96p56 6750471 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 19 9 52520441922763380 253655458399017675 9033331507200 1156268355358836200013540 Ns96p57 249544393960587264000 Ns96p55 Ns96p54 Ns96p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 2) (BSN.artanhQ 3) 0 9 52520441922763380 253655458399017675 9033331507200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 9 19 1156268355358836200013540 Ns96p57 249544393960587264000 rfl rfl rfl rfl)) rfl rfl 

theorem RS097to114.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 6750471 4194304 1 1210000 := BSN.isNear_log_sfrac 5 1 6750471 4194304 1 1210000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 6750471 4194304 1210000 rfl rfl rfl (Ns96p58 rfl rfl)) 

theorem RS097to114.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 108007536 67108864 56 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 6750471 4194304 1 1210000 108007536 67108864 56 67108864 RS097to114.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns96p59 := @Enclosure.Real.IsNear.inv_image qz328 18757497 8388608 1 8388608 1875749 1875750 4194304 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 18757497 8388608 1 8388608 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 18757497 8388608 1 8388608 18757497 8388608 1 8388608 (BSN.sqrt_enclosure 5 1 9378748 9378749 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS097to114.d24 : Enclosure.Real.IsNear qz329 Bool.false 3751499 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 3751499 8388608 1 8388608 3751499 8388608 1 8388608 (Ns96p59 rfl rfl) rfl 

theorem RS097to114.d25 : Enclosure.Real.IsNear qz329 Bool.false 30011992 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 3751499 8388608 1 8388608 30011992 67108864 8 67108864 RS097to114.d24 rfl 

noncomputable def Ns96p60 := BSN.log_dyadic_bound 2 10 5 4 94500000000 4194304 1210000 1291130880 26880 1700643 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 10) 0 4 1291130880 94500000000 26880 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) (@Nat.cast Real Real.instNatCast 1))

theorem RS097to114.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683142479095 2251799813685248 50000000121 60500000000000000 := BSN.isNear_log_sfrac 6 1 4034683142479095 2251799813685248 50000000121 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 270763002291722209198080 151115727451828646838272 1000000002420000 1210000000000000000000 4034683142479095 2251799813685248 50000000121 60500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 1700643 4194304 24973259072661432 36028797018963968 1210000 1000000000000000 rfl rfl rfl rfl (Ns96p60 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS097to114.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 120242927 67108864 57 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683142479095 2251799813685248 50000000121 60500000000000000 120242927 67108864 57 67108864 RS097to114.d26 rfl 

noncomputable abbrev qz331 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns96p61 := @Enclosure.Real.IsNear.inv_image qz331 20547809 8388608 1 8388608 1712317 1712318 4194304 (@Enclosure.Real.IsNear.of_eq qz331 (Real.sqrt qz330) Bool.false 20547809 8388608 1 8388608 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 20547809 8388608 1 8388608 20547809 8388608 1 8388608 (BSN.sqrt_enclosure 6 1 10273904 10273905 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS097to114.d28 : Enclosure.Real.IsNear qz332 Bool.false 3424635 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 3424635 8388608 1 8388608 3424635 8388608 1 8388608 (Ns96p61 rfl rfl) rfl 

theorem RS097to114.d29 : Enclosure.Real.IsNear qz332 Bool.false 27397080 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 3424635 8388608 1 8388608 27397080 67108864 8 67108864 RS097to114.d28 rfl 

noncomputable def Ns96p62 := BSN.log_dyadic_bound 3 11 6 5 269619528727395 4194304 1210000 6999933372849 55801305 2347198 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 3) (BSN.artanhQ 11) 0 5 6999933372849 269619528727395 55801305 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz862 := (Enclosure.sfrac Bool.false 7 1)

noncomputable abbrev qz629 := qz862

noncomputable abbrev qz333 := qz629

noncomputable abbrev qz1 := qz333

noncomputable abbrev qz334 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) (@Nat.cast Real Real.instNatCast 1))

theorem RS097to114.d30 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 4381799714987255 2251799813685248 50000000121 60500000000000000 := BSN.isNear_log_sfrac 7 1 4381799714987255 2251799813685248 50000000121 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz334) Bool.false 294057601148318457528320 151115727451828646838272 1000000002420000 1210000000000000000000 4381799714987255 2251799813685248 50000000121 60500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 2347198 4194304 24973259072661432 36028797018963968 1210000 1000000000000000 rfl rfl rfl rfl (Ns96p62 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS097to114.d31 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 130587807 67108864 57 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 4381799714987255 2251799813685248 50000000121 60500000000000000 130587807 67108864 57 67108864 RS097to114.d30 rfl 

noncomputable abbrev qz335 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns96p63 := @Enclosure.Real.IsNear.inv_image qz335 22194171 8388608 1 8388608 1585297 1585298 4194304 (@Enclosure.Real.IsNear.of_eq qz335 (Real.sqrt qz334) Bool.false 22194171 8388608 1 8388608 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz334) Bool.false 22194171 8388608 1 8388608 22194171 8388608 1 8388608 (BSN.sqrt_enclosure 7 1 11097085 11097086 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz336 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS097to114.d32 : Enclosure.Real.IsNear qz336 Bool.false 3170595 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz336 Bool.false 3170595 8388608 1 8388608 3170595 8388608 1 8388608 (Ns96p63 rfl rfl) rfl 

theorem RS097to114.d33 : Enclosure.Real.IsNear qz336 Bool.false 25364760 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz336 Bool.false 3170595 8388608 1 8388608 25364760 67108864 8 67108864 RS097to114.d32 rfl 

theorem RS097to114.d34 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz863 := (@instHMul Real Real.instMul)

noncomputable abbrev qz630 := qz863

noncomputable abbrev qz337 := (@HMul.hMul Real Real Real qz630 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz2 := qz337

theorem RS097to114.d35 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS097to114.d34 rfl 

noncomputable abbrev qz3 := (@Inv.inv Real Real.instInv qz337)

theorem RS097to114.d36 : Enclosure.Real.IsNear qz3 Bool.false 1335089 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 1335089 8388608 1 8388608 1335089 8388608 1 8388608 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 667544 667545 4194304 RS097to114.d35 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns96p64 := nat_lit 1395035020574284840960000 

noncomputable def Ns96p65 := nat_lit 642054934871550060337823744 

noncomputable abbrev qz864 := (Enclosure.sfrac Bool.false 316604 1000)

noncomputable abbrev qz631 := qz864

noncomputable abbrev qz338 := qz631

noncomputable abbrev qz4 := qz338

noncomputable abbrev qz339 := qz630

noncomputable abbrev qz5 := qz339

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 7)

noncomputable abbrev qz7 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz865 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 316604 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz632 := qz865

noncomputable abbrev qz340 := qz632

noncomputable abbrev qz8 := qz340

noncomputable abbrev qz9 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz866 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 316604 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz633 := qz866

noncomputable abbrev qz341 := qz633

noncomputable abbrev qz10 := qz341

noncomputable abbrev qz634 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz8 qz9))

noncomputable def Ns96p66 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 7) (@HMul.hMul Real Real Real qz5 qz634 (Zeta.RiemannSiegel.correction qz10)) 74104393 16777216 29345 16777216 2469864567085905675 9223372036854775808 22518808741393429899 Ns96p64 Ns96p65 

noncomputable def Ns96p67 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 316604 1000 67 98 67108864 33554432 1125899906842624 Bool.false 30991782316 1196 

noncomputable def Ns96p68 := Ns96p67 120242927 57 27397080 8 130587807 57 25364760 8 Bool.true 130235406 43542 Bool.true 14847420 Bool.true 22232738 3537118876014220 1 Bool.false 14726588 Bool.false Bool.false 63459642 Bool.true Bool.true 148208786 

noncomputable def Ns96p69 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 316604 1000 14 30 67108864 33554432 1125899906842624 Bool.false 30991782316 1196 

noncomputable def Ns96p70 := Ns96p69 93032624 56 33554424 8 108007536 56 30011992 8 Bool.true 85325646 25595 Bool.false 61480428 Bool.true 41404899 3537118876014220 1 Bool.false 40862236 Bool.true Bool.false 54735925 Bool.true Bool.true 130235406 

noncomputable def Ns96p71 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 316604 1000 154 72 67108864 33554432 1125899906842624 Bool.false 30991782316 1196 

noncomputable def Ns96p72 := Ns96p71 46516304 56 47453136 16 73726608 56 38745320 8 Bool.true 67108848 1256 Bool.false 30723416 Bool.false 59809607 3537118876014220 1 Bool.false 60198031 Bool.true Bool.false 42174816 Bool.false Bool.true 85325646 

noncomputable def Ns96p73 := nat_lit 287667403440821817776032675259388517534759638112067 

noncomputable def Ns96p74 := nat_lit 622908113442758028455857613920960258982805504000 

noncomputable def Ns96p75 := nat_lit 1526954051811337955778007531520000 

noncomputable def Ns96p76 := nat_lit 2900641939801899848765961890672148480 

noncomputable abbrev qz11 := (@Eq.refl Real qz338)

noncomputable def Ns96p77 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 316604 1000 400953371264 16000000 633208 4000 2000 Ns96p75 Ns96p76 qz11 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns96p78 := nat_lit 3016411352303631783963212384927885741625281222929987665920 

noncomputable abbrev qz867 := (@instHSub Real Real.instSub)

noncomputable abbrev qz635 := qz867

noncomputable abbrev qz342 := qz635

noncomputable abbrev qz12 := qz342

noncomputable abbrev qz343 := (Real.log (Enclosure.sfrac Bool.false 400953371264 16000000))

noncomputable abbrev qz344 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz345 := (@HMul.hMul Real Real Real qz630 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz346 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz347 := (Enclosure.sfrac Bool.false 316604 2000)

noncomputable abbrev qz13 := (@HSub.hSub Real Real Real qz342 (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 316604 4000) qz343) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 633208)))))) qz347)

noncomputable abbrev qz348 := (@HSub.hSub Real Real Real qz12 qz13 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 316604 2000) (Real.log Real.pi)))

noncomputable def Ns96p79 := @Enclosure.Real.IsNear.addLit_ft_p qz348 (Enclosure.sfrac Bool.true Ns96p75 Ns96p76) 1039912837674989988279 2251799813685248000 551958350295608139 30976000000000000000000 Ns96p75 Ns96p76 0 1 Ns96p78 

noncomputable def Ns96p80 := nat_lit 17446842298846244831194251264000 

noncomputable abbrev qz349 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 316604 2000) (Real.log Real.pi))

noncomputable def Ns96p81 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz349 1447968304542397442487 2251799813685248000 1014387634096919 121000000000000000000 3040250143911 16777216000 79151 8388608000 Ns96p80 1039912837674989988279 2251799813685248000 

noncomputable def Ns96p82 := nat_lit 2895936609084794884974000 

noncomputable abbrev qz14 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 316604 4000) qz343) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 633208))))))

noncomputable def Ns96p83 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz347 1804432718648399571383 2251799813685248000 1014387634096919 121000000000000000000 316604 2000 0 1 Ns96p82 1447968304542397442487 2251799813685248000 1014387634096919 121000000000000000000 

noncomputable def Ns96p84 := nat_lit 4063221259660031679177898060870057984 

noncomputable def Ns96p85 := nat_lit 12245223763757437231824896 

noncomputable def Ns96p86 := nat_lit 1208925819614629174706176 

noncomputable def Ns96p87 := nat_lit 170843144345348883781708170383944782762278530799733430375706175257913986070368765749755159076483952020796598307931050475520 

noncomputable def Ns96p88 := nat_lit 2563249506432439787519923222500507323681419183412570678395522290026633622182006010133710389021864237553059443715975675904 

noncomputable def Ns96p89 := nat_lit 2509687683920446640020025064909199916801971229266741600230144767474527634555474457147556409718412079222550240952320 

noncomputable def Ns96p90 := BSN.log_dyadic_bound 138809371264 663097371264 6 5 Ns96p87 33554432 9680000 Ns96p88 Ns96p89 14258995 801906742528 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 138809371264) (BSN.artanhQ 663097371264) 0 5 Ns96p88 Ns96p87 Ns96p89 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz350 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns96p91 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 316604 4000) qz343 316604 4000 0 1 22808506644810433 2251799813685248 6250000847 60500000000000000 1805316109443390582383 2251799813685248000 494693817040897 60500000000000000000 (Enclosure.Real.IsNear.const Bool.false 316604 4000) (BSN.isNear_log_sfrac 400953371264 16000000 22808506644810433 2251799813685248 6250000847 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 400953371264) qz350)) Bool.false Ns96p85 Ns96p86 1000000135520000 9680000000000000000000 22808506644810433 2251799813685248 6250000847 60500000000000000 (BSN.log_rat_reduce_isNear 400953371264 16000000 14 801906742528 524288000000 14258995 33554432 24973259072661432 36028797018963968 9680000 1000000000000000 rfl rfl rfl rfl (Ns96p90 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p92 := BSN.arctan_dyadic_bound_f 1000 633208 1 0 4194304 1210000 0 1 1 0 1 1 6623 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 633208) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 633208) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz15 := qz345

noncomputable abbrev qz16 := qz346

noncomputable abbrev qz351 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz17 := (@Enclosure.Real.IsNear.mulLit_ff qz351 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz352 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 633208)))

noncomputable def Ns96p93 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz352 884279719003555 562949953421312 1 2000000000000000 6623 4194304 1 1210000 3705209544993977401344 883390794991011 562949953421312 200000000121 242000000000000000 qz17 (Ns96p92 rfl) rfl rfl 

noncomputable abbrev qz18 := qz344

noncomputable abbrev qz353 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns96p94 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 316604 4000) qz343) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz352)) 1805316109443390582383 2251799813685248000 494693817040897 60500000000000000000 883390794991011 2251799813685248 200000000121 968000000000000000 Ns96p84 1804432718648399571383 2251799813685248000 1014387634096919 121000000000000000000 (Ns96p91 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz352) 1 4 0 1 883390794991011 562949953421312 200000000121 242000000000000000 883390794991011 2251799813685248 200000000121 968000000000000000 qz353 Ns96p93 rfl) 

noncomputable def Ns96p95 := @Ns96p79 Ns96p73 Ns96p74 551958350295608139 30976000000000000000000 (@Ns96p81 551958350295608139 30976000000000000000000 (Ns96p83 (Ns96p94 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 316604 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz347 (Real.log Real.pi) 316604 2000 0 1 38410761 33554432 1 16777216 3040250143911 16777216000 79151 8388608000 (Enclosure.Real.IsNear.const Bool.false 316604 2000) RS097to114.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns96p75 Ns96p76) 

noncomputable abbrev qz354 := (@instHAdd Real Real.instAdd)

noncomputable def Ns96p96 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns96p73 Ns96p74 551958350295608139 30976000000000000000000 3873972789 8388608 75 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz354 qz348 (Enclosure.sfrac Bool.true Ns96p75 Ns96p76)) Bool.false Ns96p73 Ns96p74 551958350295608139 30976000000000000000000 Ns96p77 (Ns96p95 rfl rfl)) 

noncomputable def Ns96p97 := nat_lit 1898279699759335617855488 

noncomputable def Ns96p98 := nat_lit 139783204860565253061567234157026390937453994421535725933430534823414593031712976011520 

noncomputable def Ns96p99 := nat_lit 2753733154729970958028337252922338050165611694356407771374444090804896824278383046164480 

noncomputable def Ns96p100 := nat_lit 280442107998464744792493705031379996642444752367967317098465153252207591090797281536 

noncomputable def Ns96p101 := nat_lit 365644820745673386526821575841208789603529836743045430359872933337010836126053646336256 

noncomputable def Ns96p102 := nat_lit 50485107836716134230519516303576197586369547729867475808531474998089775111770355846348800 

noncomputable abbrev qz355 := (BSN.sinEvenQ 17179869184)

noncomputable abbrev qz356 := (BSN.sinOddQ 17179869184)

noncomputable def Ns96p103 := BSN.sin_dyadic_bound_f 26976177022 17179869184 3 2 8388608 2422364 Ns96p98 Ns96p99 Ns96p100 Ns96p101 Ns96p102 Ns96p100 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26976177022) qz355 0 2 Ns96p98 Ns96p99 Ns96p100 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26976177022) qz356 0 2 Ns96p101 Ns96p102 Ns96p100 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz357 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable abbrev qz358 := (@Nat.cast Real Real.instNatCast Ns96p86)

noncomputable def Ns96p104 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3873972789) qz357) Bool.false 3873972789 8388608 75 4194304 Bool.true 8388606 8388608 1 1210000 (Ns96p96 rfl) (Enclosure.sfrac_false_div 3873972789 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3873972789) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns96p97) qz358) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 73 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q1 3873972789 8388608 226375608064910080 72057594037927936 73 Ns96p97 Ns96p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388606 8388608 Ns96p97 Ns96p86 26976177022 17179869184 2422364 2420000 (Ns96p103 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p105 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns96p73 Ns96p74 551958350295608139 30976000000000000000000 30991782316 67108864 1196 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz354 qz348 (Enclosure.sfrac Bool.true Ns96p75 Ns96p76)) Bool.false Ns96p73 Ns96p74 551958350295608139 30976000000000000000000 Ns96p77 (Ns96p95 rfl rfl)) 

noncomputable def Ns96p106 := Ns96p72 25595 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 154 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 60198031 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 72 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 42174816 67108864) qz11 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 4194303 4194304 5934019 317194240000 67108848 67108864 1256 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 4194303 4194304 5934019 317194240000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 8388606 8388608 94944304 5075107840000 4194303 4194304 5934019 317194240000 (Ns96p104 rfl rfl) rfl)) rfl) (Ns96p105 rfl) RS097to114.d7 

noncomputable def Ns96p107 := nat_lit 30361148227655690457002939210457229077449211802771819139669426176 

noncomputable def Ns96p108 := nat_lit 16586685937797756904922089360178093090225977525586485022553978961920 

noncomputable def Ns96p109 := nat_lit 793882101278021606939078973667190458565214552707466312810496 

noncomputable def Ns96p110 := nat_lit 91081856918764515327794939473424352851430504979210042486382657536 

noncomputable def Ns96p111 := nat_lit 746400867200899060721494021208014189060168988651391826014929053286400 

noncomputable abbrev qz359 := (BSN.cosEvenQ 67108864)

noncomputable def Ns96p112 := BSN.cos_dyadic_bound_f 30723416 67108864 3 2 67108864 33554432 Ns96p107 Ns96p108 Ns96p109 Ns96p110 Ns96p111 Ns96p109 60198031 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 30723416) qz359 0 2 Ns96p107 Ns96p108 Ns96p109 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 30723416) (BSN.cosOddQ 67108864) 0 2 Ns96p110 Ns96p111 Ns96p109 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p113 := nat_lit 436189984717913523807486674784483540890446358832854298795386662081 

noncomputable def Ns96p114 := nat_lit 163744827444297110925540873705127806473701269482169725948587201 

noncomputable def Ns96p115 := nat_lit 1308242464498851977200608942606040367058391673959598556934262811841 

noncomputable def Ns96p116 := BSN.cos_dyadic_bound_f 59809607 67108864 3 2 67108864 33554432 Ns96p113 Ns96p108 Ns96p114 Ns96p115 Ns96p111 Ns96p114 42174816 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 59809607) qz359 0 2 Ns96p113 Ns96p108 Ns96p114 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 59809607) (BSN.cosOddQ 67108864) 0 2 Ns96p115 Ns96p111 Ns96p114 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p117 := nat_lit 487033033351100339671933160628105332107229573143724591020224086016 

noncomputable def Ns96p118 := nat_lit 204124464143672413041596830700102958355106540383592356197236736 

noncomputable def Ns96p119 := nat_lit 1460690851125013674189716288222915790404978506350406588348277784576 

noncomputable def Ns96p120 := BSN.cos_dyadic_bound_f 61480428 67108864 3 2 67108864 33554432 Ns96p117 Ns96p108 Ns96p118 Ns96p119 Ns96p111 Ns96p118 40862236 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 61480428) qz359 0 2 Ns96p117 Ns96p108 Ns96p118 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 61480428) (BSN.cosOddQ 67108864) 0 2 Ns96p119 Ns96p111 Ns96p118 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p121 := nat_lit 100155131863313404762532078073628749492739046796822733654307499681 

noncomputable def Ns96p122 := nat_lit 8638012670599695485143343581308408368371967259779467157040801 

noncomputable def Ns96p123 := nat_lit 300448119564599014896625947533723631661480396455948642028608417441 

noncomputable def Ns96p124 := BSN.cos_dyadic_bound_f 41404899 67108864 3 2 67108864 33554432 Ns96p121 Ns96p108 Ns96p122 Ns96p123 Ns96p111 Ns96p122 54735925 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 41404899) qz359 0 2 Ns96p121 Ns96p108 Ns96p122 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 41404899) (BSN.cosOddQ 67108864) 0 2 Ns96p123 Ns96p111 Ns96p122 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p125 := Ns96p70 43542 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 14 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 40862236 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 30 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 54735925 67108864) qz11 rfl rfl (Ns96p106 RS097to114.d9 RS097to114.d11 RS097to114.d13 RS097to114.d17 (Ns96p112 rfl rfl) (Ns96p116 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns96p105 rfl) RS097to114.d19 RS097to114.d21 RS097to114.d23 RS097to114.d25 RS097to114.d17 (Ns96p120 rfl rfl) (Ns96p124 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns96p126 := nat_lit 48596386298375751694860960000 

noncomputable def Ns96p127 := nat_lit 2433889152438200450873670154321920 

noncomputable def Ns96p128 := nat_lit 17037224067067403156115691080253440 

noncomputable abbrev qz360 := (BSN.sinEvenQ 67108864)

noncomputable def Ns96p129 := BSN.sin_dyadic_bound_f 14847420 67108864 2 1 67108864 33554432 Ns96p126 Ns96p127 Ns96p126 Ns96p126 Ns96p128 Ns96p126 14726588 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 14847420) qz360 0 1 Ns96p126 Ns96p127 Ns96p126 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 14847420) (BSN.sinOddQ 67108864) 0 1 Ns96p126 Ns96p128 Ns96p126 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p130 := nat_lit 244327190121050829823577502736 

noncomputable def Ns96p131 := nat_lit 486777830487640090174734030864384 

noncomputable def Ns96p132 := nat_lit 7301667457314601352621010462965760 

noncomputable def Ns96p133 := BSN.cos_dyadic_bound_f 22232738 67108864 2 1 67108864 33554432 Ns96p130 Ns96p131 Ns96p130 Ns96p130 Ns96p132 Ns96p130 63459642 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 22232738) qz359 0 1 Ns96p130 Ns96p131 Ns96p130 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 22232738) (BSN.cosOddQ 67108864) 0 1 Ns96p130 Ns96p132 Ns96p130 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz636 := (BSN.cos_quad_nat2 98 rfl)

noncomputable def Ns96p134 := Ns96p68 58690 BSN.abs_quadSignPos (BSN.cos_quad_nat3 67 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 14726588 67108864) BSN.abs_quadSignNeg qz636 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 63459642 67108864) qz11 rfl rfl (Ns96p125 rfl rfl) (Ns96p105 rfl) RS097to114.d27 RS097to114.d29 RS097to114.d31 RS097to114.d33 RS097to114.d17 (Ns96p129 rfl rfl) (Ns96p133 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns96p135 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 7) 148208786 67108864 58690 67108864 148208786 67108864 58690 67108864 19892246526558208 74104393 16777216 29345 16777216 (Ns96p134 rfl) 

noncomputable def Ns96p136 := @Enclosure.Real.IsNear.mulLit_tf qz634 (Zeta.RiemannSiegel.correction qz10) 1574257 4194304 1 4194304 1568908105275 2199023255552 28307318610381 665204534804480000 2469864567085905675 9223372036854775808 

noncomputable abbrev qz637 := (@HPow.hPow Real Real Real qz7 qz8 qz9)

noncomputable def Ns96p137 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz637 1 1 0 1 1574257 4194304 1 4194304 1574257 4194304 1 4194304 

noncomputable abbrev qz361 := (@Enclosure.Real.IsNear.of_eq qz8 (@HMul.hMul Real Real Real qz5 qz4 qz3) Bool.false 105673629439 2097152000 79151 2097152000 (BSN.t_div_two_pi_mk qz4 316604 1000 qz11) (@Enclosure.Real.IsNear.mulLit_ff qz4 qz3 316604 1000 0 1 1335089 8388608 1 8388608 105673629439 2097152000 79151 2097152000 (Enclosure.Real.IsNear.const Bool.false 316604 1000) RS097to114.d36 rfl))

noncomputable def Ns96p138 := @Enclosure.Real.IsNear.sqrt_image qz8 105673629439 2097152000 79151 2097152000 29773377 29773400 4194304 qz361 

noncomputable abbrev qz868 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 316604 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz638 := qz868

noncomputable abbrev qz362 := qz638

noncomputable abbrev qz19 := qz362

noncomputable def Ns96p139 := @Enclosure.Real.IsNear.sqrt_image qz19 59546777 8388608 23 8388608 11174909 11174914 4194304 (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 59546777 8388608 23 8388608 59546777 8388608 23 8388608 (Ns96p138 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz639 := (Real.sqrt qz868)

noncomputable abbrev qz363 := qz639

noncomputable abbrev qz20 := qz363

noncomputable def Ns96p140 := @Enclosure.Real.IsNear.inv_image qz20 22349823 8388608 5 8388608 1574256 1574258 4194304 (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 22349823 8388608 5 8388608 22349823 8388608 5 8388608 (Ns96p139 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns96p141 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz20) Bool.false 3148514 8388608 2 8388608 1574257 4194304 1 4194304 (Ns96p140 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz21 := (@HMul.hMul Real Real Real qz339 qz337 qz341)

noncomputable abbrev qz640 := (@HMul.hMul Real Real Real qz863 qz866 qz866)

noncomputable abbrev qz641 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz364 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz640 qz633) qz641)

noncomputable abbrev qz22 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz364))

noncomputable def Ns96p142 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz10) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz21)) qz22) Bool.false 1568908105275 

noncomputable def Ns96p143 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz21)) qz22 2575041 2097152 29 

noncomputable def Ns96p144 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz21)) Bool.false 10300164 8388608 232 8388608 2575041 2097152 29 

noncomputable def Ns96p145 := @Enclosure.Real.IsNear.recentre' (Real.cos qz21) Bool.false 3415904 4194304 92524304 5075107840000 106747 131072 5782769 317194240000 

noncomputable def Ns96p146 := @Enclosure.Real.IsNear.cos_image qz21 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 162287) (@Nat.cast Real Real.instNatCast 262144)) Bool.false 162287 262144 73 4194304 Bool.false 3415904 4194304 1 

noncomputable def Ns96p147 := nat_lit 620679734415112806797800673 

noncomputable def Ns96p148 := nat_lit 36028797018963968000000000000000 

noncomputable def Ns96p149 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz10 884279719003555 140737488355328 1 500000000000000 826521 8388608 23 8388608 730875757630537282155 1180591620717411303424 Ns96p147 

noncomputable def Ns96p150 := @Enclosure.Real.IsNear.subLit_ff_p qz19 qz1 59546777 8388608 23 8388608 7 1 0 1 826521 826521 8388608 23 

noncomputable abbrev qz365 := (Enclosure.Real.IsNear.const Bool.false 7 1)

noncomputable def Ns96p151 := @Ns96p150 8388608 (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 59546777 8388608 23 8388608 59546777 8388608 23 8388608 (Ns96p138 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns96p152 := @Enclosure.Real.IsNear.recentre' qz21 Bool.false 730875757630537282155 1180591620717411303424 Ns96p147 Ns96p148 162287 262144 73 4194304 (@Ns96p149 Ns96p148 RS097to114.d35 (Ns96p151 rfl rfl) rfl) 

noncomputable def Ns96p153 := nat_lit 5503536700918758713426248343089642737173712001 

noncomputable def Ns96p154 := nat_lit 899166046404754725066720160753181935921130373120 

noncomputable def Ns96p155 := nat_lit 481138219246040638072070706077751426337921 

noncomputable def Ns96p156 := nat_lit 16509647826317784059002600887856772708668460161 

noncomputable def Ns96p157 := nat_lit 40462472088213962628002407233893187116450866790400 

noncomputable def Ns96p158 := BSN.cos_dyadic_bound_f 162287 262144 3 2 4194304 1210000 Ns96p153 Ns96p154 Ns96p155 Ns96p156 Ns96p157 Ns96p155 3415904 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 162287) (BSN.cosEvenQ 262144) 0 2 Ns96p153 Ns96p154 Ns96p155 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 162287) (BSN.cosOddQ 262144) 0 2 Ns96p156 Ns96p157 Ns96p155 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p159 := @Enclosure.Real.IsNear.inv_image (Real.cos qz21) 106747 131072 5782769 317194240000 5149966 5150198 4194304 (Ns96p145 (@Ns96p146 1210000 (Ns96p152 rfl) (Enclosure.sfrac_false_div 162287 262144) (Ns96p158 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns96p160 := @Enclosure.Real.IsNear.recentre' qz22 Bool.false 2437100 4194304 

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz339 qz337 qz364)

noncomputable def Ns96p161 := @Enclosure.Real.IsNear.cos_image qz23 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 996963)) (@Nat.cast Real Real.instNatCast 1048576)) Bool.true 996963 1048576 

noncomputable def Ns96p162 := nat_lit 9416049398396647339522632205 

noncomputable def Ns96p163 := nat_lit 9903520314283042199192993792 

noncomputable def Ns96p164 := nat_lit 1246532586148716705408826203674069 

noncomputable def Ns96p165 := @Enclosure.Real.IsNear.recentre' qz23 Bool.true Ns96p162 Ns96p163 Ns96p164 

noncomputable def Ns96p166 := nat_lit 60446290980731458735308800000000000000 

noncomputable abbrev qz24 := qz364

noncomputable def Ns96p167 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz24 884279719003555 140737488355328 1 500000000000000 10648270220431 

noncomputable abbrev qz366 := (@HSub.hSub Real Real Real qz635 qz640 qz633)

noncomputable abbrev qz25 := qz366

noncomputable abbrev qz367 := qz641

noncomputable abbrev qz26 := qz367

noncomputable def Ns96p168 := @Enclosure.Real.IsNear.subLit_tf qz25 qz26 6250223709327 70368744177664 230958479 70368744177664 1 16 

noncomputable abbrev qz368 := qz640

noncomputable abbrev qz27 := qz368

noncomputable def Ns96p169 := @Enclosure.Real.IsNear.subLit_ff_n qz27 qz10 683136963441 70368744177664 38020495 70368744177664 826521 8388608 23 8388608 

noncomputable def Ns96p170 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz10 826521 8388608 23 8388608 826521 8388608 23 8388608 683136963441 70368744177664 

noncomputable def Ns96p171 := nat_lit 2007410974132698900360774172356256471689081433930401 

noncomputable def Ns96p172 := nat_lit 58927746017182005661972572455120531352527200132792320 

noncomputable def Ns96p173 := nat_lit 975960691635678766340042064251656754187534645921 

noncomputable def Ns96p174 := nat_lit 6020281001014825343549642432940266101558869232499361 

noncomputable def Ns96p175 := nat_lit 2651748570773190254788765760480423910863724005975654400 

noncomputable def Ns96p176 := BSN.cos_dyadic_bound_f 996963 1048576 3 2 4194304 1210000 Ns96p171 Ns96p172 Ns96p173 Ns96p174 Ns96p175 Ns96p173 2437100 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 996963) (BSN.cosEvenQ 1048576) 0 2 Ns96p171 Ns96p172 Ns96p173 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 996963) (BSN.cosOddQ 1048576) 0 2 Ns96p174 Ns96p175 Ns96p173 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz369 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns96p177 := @Ns96p160 109464304 5075107840000 609275 1048576 6841519 317194240000 (@Ns96p161 87 4194304 Bool.false 2437100 4194304 1 1210000 (@Ns96p165 Ns96p166 996963 1048576 87 4194304 (@Ns96p167 70368744177664 230958479 70368744177664 Ns96p162 Ns96p163 Ns96p164 Ns96p166 RS097to114.d35 (@Ns96p168 0 1 170372323526896 10648270220431 70368744177664 230958479 70368744177664 (@Ns96p169 52430676609850146816 6250223709327 70368744177664 230958479 70368744177664 (@Ns96p170 38020495 70368744177664 (Ns96p151 rfl rfl) (Ns96p151 rfl rfl) rfl) (Ns96p151 rfl rfl) rfl rfl) qz369 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 996963 1048576) (BSN.cos_neg_of_bound 996963 1048576 Bool.false 2437100 4194304 1 1210000 (Ns96p176 rfl rfl)) rfl rfl) 

noncomputable abbrev qz28 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 7) (Enclosure.sfrac Bool.true 1 1) Bool.true 1 1 0 1 (BSN.neg_one_pow_odd_mk 7 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1))

noncomputable def Ns96p178 := @Ns96p136 22518808741393429899 Ns96p64 (Ns96p137 qz28 (@Enclosure.Real.IsNear.of_eq qz637 (@Inv.inv Real Real.instInv qz20) Bool.false 1574257 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz8 (BSN.t_div_two_pi_nonneg qz4 316604 1000 qz11)) Ns96p141) rfl) (@Ns96p142 2199023255552 28307318610381 665204534804480000 (BSN.correction_mk qz10 (BSN.cos_two_pi_p_ne_zero_mk qz4 316604 1000 7 qz11 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 316604 1000 7 qz11 rfl rfl rfl))) (@Ns96p143 1048576 609275 1048576 6841519 317194240000 1568908105275 2199023255552 28307318610381 665204534804480000 (@Ns96p144 1048576 (Ns96p159 rfl rfl rfl rfl rfl) rfl) (Ns96p177 rfl) rfl)) 

noncomputable def Ns96p179 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 38269456319305304309 9223372036854775808 2462572192971076629899 Ns96p64 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 7) (@HMul.hMul Real Real Real qz5 qz634 (Zeta.RiemannSiegel.correction qz10))) Bool.true 38269456319305304309 9223372036854775808 2462572192971076629899 Ns96p64 (BSN.hardyZApproximantRS₀_eq qz4 7 (@BSN.floor_sqrt_eq_dec qz4 316604 1000 7 qz11 rfl rfl rfl)) (@Ns96p66 38269456319305304309 9223372036854775808 2462572192971076629899 Ns96p64 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 7)) Bool.true 74104393 16777216 29345 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 7) (Ns96p135 (Ns96p134 rfl) rfl rfl)) (Ns96p178 rfl) rfl rfl)) 

theorem RS097to114.d37 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 38269456319305304309 9223372036854775808 2462572192971076629899 Ns96p64 := Ns96p179 

theorem RS097to114.d38 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS097to114.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS097to114.d3 a b h)) 

noncomputable def Ns96p180 := nat_lit 5580140082297139363840000 

noncomputable def Ns96p181 := nat_lit 48037631356616520029437952 

noncomputable abbrev qz869 := (Enclosure.sfrac Bool.false 318206 1000)

noncomputable abbrev qz642 := qz869

noncomputable abbrev qz370 := qz642

noncomputable abbrev qz29 := qz370

noncomputable abbrev qz870 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 318206 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz643 := qz870

noncomputable abbrev qz371 := qz643

noncomputable abbrev qz30 := qz371

noncomputable abbrev qz871 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 318206 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz644 := qz871

noncomputable abbrev qz372 := qz644

noncomputable abbrev qz31 := qz372

noncomputable abbrev qz645 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz30 qz9))

noncomputable def Ns96p182 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz29) qz29 7) (@HMul.hMul Real Real Real qz5 qz645 (Zeta.RiemannSiegel.correction qz31)) 33096677 33554432 3687 2097152 294439813860943725 1152921504606846976 98109867869265626391 Ns96p180 Ns96p181 

noncomputable def Ns96p183 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz29) qz29 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 318206 1000 66 98 67108864 33554432 1125899906842624 Bool.false 31202622360 1203 

noncomputable def Ns96p184 := Ns96p183 120242927 57 27397080 8 130587807 57 25364760 8 Bool.false 58648964 43766 Bool.true 102050902 Bool.true 20594361 3537118876014220 1 Bool.false 3362047 Bool.true Bool.false 63973587 Bool.true Bool.false 33096677 

noncomputable def Ns96p185 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz29) qz29 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 318206 1000 15 30 67108864 33554432 1125899906842624 Bool.false 31202622360 1203 

noncomputable def Ns96p186 := Ns96p185 93032624 56 33554424 8 108007536 56 30011992 8 Bool.false 79789211 25727 Bool.false 17867851 Bool.true 3592928 3537118876014220 1 Bool.false 17657489 Bool.false Bool.false 67012706 Bool.true Bool.false 58648964 

noncomputable def Ns96p187 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz29) qz29 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 318206 1000 155 73 67108864 33554432 1125899906842624 Bool.false 31202622360 1203 

noncomputable def Ns96p188 := Ns96p187 46516304 56 47453136 16 73726608 56 38745320 8 Bool.false 67108848 1264 Bool.false 61629984 Bool.false 47125268 3537118876014220 1 Bool.false 53325105 Bool.false Bool.false 43346620 Bool.true Bool.false 79789211 

noncomputable def Ns96p189 := nat_lit 305694004008774042150837428258731801824920512062810827 

noncomputable def Ns96p190 := nat_lit 657469654431117522429200979568537405906753683456000 

noncomputable def Ns96p191 := nat_lit 1565978428791987571153829012480000 

noncomputable def Ns96p192 := nat_lit 2989825836407897088198301296727265280 

noncomputable abbrev qz373 := (@Eq.refl Real qz642)

noncomputable abbrev qz32 := qz373

noncomputable def Ns96p193 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz29 318206 1000 405021233744 16000000 636412 4000 2000 Ns96p191 Ns96p192 qz32 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns96p194 := nat_lit 6260613202099692383249150530738827301374372087046365736960 

noncomputable abbrev qz374 := (Real.log (Enclosure.sfrac Bool.false 405021233744 16000000))

noncomputable abbrev qz375 := (Enclosure.sfrac Bool.false 318206 2000)

noncomputable abbrev qz33 := (@HSub.hSub Real Real Real qz342 (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 318206 4000) qz374) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 636412)))))) qz375)

noncomputable abbrev qz376 := (@HSub.hSub Real Real Real qz12 qz33 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 318206 2000) (Real.log Real.pi)))

noncomputable def Ns96p195 := @Enclosure.Real.IsNear.addLit_ft_p qz376 (Enclosure.sfrac Bool.true Ns96p191 Ns96p192) 2093974899274177821007 4503599627370496000 1109437695128034267 61952000000000000000000 Ns96p191 Ns96p192 0 1 Ns96p194 

noncomputable def Ns96p196 := nat_lit 70262138367402249050887553024000 

noncomputable abbrev qz377 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 318206 2000) (Real.log Real.pi))

noncomputable def Ns96p197 := @Enclosure.Real.IsNear.subLit_ff_p qz33 qz377 2914215312471801706831 4503599627370496000 509696942387683 60500000000000000000 6111267307383 33554432000 159103 16777216000 Ns96p196 2093974899274177821007 4503599627370496000 

noncomputable def Ns96p198 := nat_lit 5828430624943603413662000 

noncomputable abbrev qz34 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 318206 4000) qz374) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 636412))))))

noncomputable def Ns96p199 := @Enclosure.Real.IsNear.subLit_ff_p qz34 qz375 3630751523985329731919 4503599627370496000 509696942387683 60500000000000000000 318206 2000 0 1 Ns96p198 2914215312471801706831 4503599627370496000 509696942387683 60500000000000000000 

noncomputable def Ns96p200 := nat_lit 8175725605247595725386443559285030912 

noncomputable def Ns96p201 := nat_lit 12257427077595730517426176 

noncomputable def Ns96p202 := nat_lit 181617863816190509377065811978554609945472167239594575433137851929121596294833245157739105628182172998662389205843857899520 

noncomputable def Ns96p203 := nat_lit 2855490771149040010473349784044315565077967635548511092894356363932966331240145478169769558631888219022294318038546120704 

noncomputable def Ns96p204 := nat_lit 3350133708754248544558677203066837993133727893109681786912714023187786536884414518539664683375427157927492132536320 

noncomputable def Ns96p205 := BSN.log_dyadic_bound 142877233744 667165233744 6 5 Ns96p202 33554432 9680000 Ns96p203 Ns96p204 14597705 810042467488 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 142877233744) (BSN.artanhQ 667165233744) 0 5 Ns96p203 Ns96p202 Ns96p204 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns96p206 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 318206 4000) qz374 318206 4000 0 1 22831237088135873 2251799813685248 6250000847 60500000000000000 3632518314433681801919 4503599627370496000 994393884760241 121000000000000000000 (Enclosure.Real.IsNear.const Bool.false 318206 4000) (BSN.isNear_log_sfrac 405021233744 16000000 22831237088135873 2251799813685248 6250000847 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 405021233744) qz350)) Bool.false Ns96p201 Ns96p86 1000000135520000 9680000000000000000000 22831237088135873 2251799813685248 6250000847 60500000000000000 (BSN.log_rat_reduce_isNear 405021233744 16000000 14 810042467488 524288000000 14597705 33554432 24973259072661432 36028797018963968 9680000 1000000000000000 rfl rfl rfl rfl (Ns96p205 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p207 := BSN.arctan_dyadic_bound_f 1000 636412 1 0 4194304 1210000 0 1 1 0 1 1 6590 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 636412) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 636412) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz378 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 636412)))

noncomputable def Ns96p208 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz378 884279719003555 562949953421312 1 2000000000000000 6590 4194304 1 1210000 3705228122342440304640 883395224176035 562949953421312 200000000121 242000000000000000 qz17 (Ns96p207 rfl) rfl rfl 

noncomputable def Ns96p209 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 318206 4000) qz374) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz378)) 3632518314433681801919 4503599627370496000 994393884760241 121000000000000000000 883395224176035 2251799813685248 200000000121 968000000000000000 Ns96p200 3630751523985329731919 4503599627370496000 509696942387683 60500000000000000000 (Ns96p206 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz378) 1 4 0 1 883395224176035 562949953421312 200000000121 242000000000000000 883395224176035 2251799813685248 200000000121 968000000000000000 qz353 Ns96p208 rfl) 

noncomputable def Ns96p210 := @Ns96p195 Ns96p189 Ns96p190 1109437695128034267 61952000000000000000000 (@Ns96p197 1109437695128034267 61952000000000000000000 (Ns96p199 (Ns96p209 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 318206 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz375 (Real.log Real.pi) 318206 2000 0 1 38410761 33554432 1 16777216 6111267307383 33554432000 159103 16777216000 (Enclosure.Real.IsNear.const Bool.false 318206 2000) RS097to114.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns96p191 Ns96p192) 

noncomputable def Ns96p211 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz29) Bool.false Ns96p189 Ns96p190 1109437695128034267 61952000000000000000000 3900327795 8388608 151 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz29) (@HAdd.hAdd Real Real Real qz354 qz376 (Enclosure.sfrac Bool.true Ns96p191 Ns96p192)) Bool.false Ns96p189 Ns96p190 1109437695128034267 61952000000000000000000 Ns96p193 (Ns96p210 rfl rfl)) 

noncomputable def Ns96p212 := nat_lit 1898483872553307146813440 

noncomputable def Ns96p213 := nat_lit 139843473799249184849970331442773384430021548485758595576535643035522654236052683816960 

noncomputable def Ns96p214 := nat_lit 280683506397493159805631572747583996987692513529995503204562332538438639012733321216 

noncomputable def Ns96p215 := nat_lit 365802277130532876157856035994243727988266839107462043314309773697497098536022127476736 

noncomputable def Ns96p216 := BSN.sin_dyadic_bound_f 26979078492 17179869184 3 2 8388608 2422364 Ns96p213 Ns96p99 Ns96p214 Ns96p215 Ns96p102 Ns96p214 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26979078492) qz355 0 2 Ns96p213 Ns96p99 Ns96p214 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26979078492) qz356 0 2 Ns96p215 Ns96p102 Ns96p214 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p217 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz29) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3900327795) qz357) Bool.false 3900327795 8388608 151 8388608 Bool.false 8388606 8388608 1 1210000 (Ns96p211 rfl) (Enclosure.sfrac_false_div 3900327795 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3900327795) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns96p212) qz358) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 73 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q3 3900327795 8388608 226375608064910080 72057594037927936 73 Ns96p212 Ns96p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388606 8388608 Ns96p212 Ns96p86 26979078492 17179869184 2422364 2420000 (Ns96p216 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p218 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz29) Bool.false Ns96p189 Ns96p190 1109437695128034267 61952000000000000000000 31202622360 67108864 1203 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz29) (@HAdd.hAdd Real Real Real qz354 qz376 (Enclosure.sfrac Bool.true Ns96p191 Ns96p192)) Bool.false Ns96p189 Ns96p190 1109437695128034267 61952000000000000000000 Ns96p193 (Ns96p210 rfl rfl)) 

noncomputable def Ns96p219 := Ns96p188 25727 BSN.abs_quadSignPos (BSN.cos_quad_nat3 155 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 53325105 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 73 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 43346620 67108864) qz32 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 1) Bool.false 4194303 4194304 11943663 634388480000 67108848 67108864 1264 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz29)) Bool.false 4194303 4194304 11943663 634388480000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz29) qz29) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz29)) Bool.false 8388606 8388608 191098608 10150215680000 4194303 4194304 11943663 634388480000 (Ns96p217 rfl rfl) rfl)) rfl) (Ns96p218 rfl) RS097to114.d7 

noncomputable def Ns96p220 := nat_lit 885057928290315735194041434744734120707871666917904196610157445120 

noncomputable def Ns96p221 := nat_lit 149280173440179812144298804241602837812033797730278365202985810657280 

noncomputable def Ns96p222 := nat_lit 208130841363820772222994371369150131455393437544592718268727296 

noncomputable def Ns96p223 := nat_lit 2317671886064809310924604623920658358783974204933724507673215369216 

noncomputable def Ns96p224 := nat_lit 2736803179736629889312144744429385359887286291721770028721406528716800 

noncomputable def Ns96p225 := BSN.sin_dyadic_bound_f 61629984 67108864 3 2 67108864 33554432 Ns96p220 Ns96p221 Ns96p222 Ns96p223 Ns96p224 Ns96p222 53325105 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 61629984) qz360 0 2 Ns96p220 Ns96p221 Ns96p222 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 61629984) (BSN.sinOddQ 67108864) 0 2 Ns96p223 Ns96p224 Ns96p222 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p226 := nat_lit 302518256368201374624406512980440379134091238654762211342049935360 

noncomputable def Ns96p227 := nat_lit 24323757462977016463271224860638416025928049772431052416024576 

noncomputable def Ns96p228 := nat_lit 792270337737968304084886047251379006963339836777126617525266743296 

noncomputable def Ns96p229 := BSN.sin_dyadic_bound_f 47125268 67108864 3 2 67108864 33554432 Ns96p226 Ns96p221 Ns96p227 Ns96p228 Ns96p224 Ns96p227 43346620 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 47125268) qz360 0 2 Ns96p226 Ns96p221 Ns96p227 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 47125268) (BSN.sinOddQ 67108864) 0 2 Ns96p228 Ns96p224 Ns96p227 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p230 := nat_lit 101927011042208374572105956401 

noncomputable def Ns96p231 := BSN.sin_dyadic_bound_f 17867851 67108864 2 1 67108864 33554432 Ns96p230 Ns96p127 Ns96p230 Ns96p230 Ns96p128 Ns96p230 17657489 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 17867851) qz360 0 1 Ns96p230 Ns96p127 Ns96p230 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 17867851) (BSN.sinOddQ 67108864) 0 1 Ns96p230 Ns96p128 Ns96p230 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p232 := nat_lit 166645679006506542202617856 

noncomputable def Ns96p233 := BSN.cos_dyadic_bound_f 3592928 67108864 2 1 67108864 33554432 Ns96p232 Ns96p131 Ns96p232 Ns96p232 Ns96p132 Ns96p232 67012706 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 3592928) qz359 0 1 Ns96p232 Ns96p131 Ns96p232 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 3592928) (BSN.cosOddQ 67108864) 0 1 Ns96p232 Ns96p132 Ns96p232 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p234 := Ns96p186 43766 BSN.abs_quadSignPos (BSN.cos_quad_nat3 15 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 17657489 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 30 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 67012706 67108864) qz32 rfl rfl (Ns96p219 RS097to114.d9 RS097to114.d11 RS097to114.d13 RS097to114.d17 (Ns96p225 rfl rfl) (Ns96p229 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns96p218 rfl) RS097to114.d19 RS097to114.d21 RS097to114.d23 RS097to114.d25 RS097to114.d17 (Ns96p231 rfl rfl) (Ns96p233 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns96p235 := nat_lit 893332227115210101501315814033750623830535944342503756447292617792718446346989917137733460222089957376 

noncomputable def Ns96p236 := nat_lit 3996645342911614855169325114413848961633120431781532997847909552396155328908156533147964360867027353600 

noncomputable def Ns96p237 := nat_lit 1275857503608429992617201506528463837534954763549746063251914755227168830006000062964334265962496 

noncomputable def Ns96p238 := nat_lit 5408078552578333642253874676370976868342089293836514287037592403978579741345440595006135921308339343360 

noncomputable def Ns96p239 := nat_lit 363694726204956951820408585411660255508613959292119502804159769268050134930642244516464756838899489177600 

noncomputable def Ns96p240 := BSN.cos_dyadic_bound_f 102050902 67108864 4 3 67108864 33554432 Ns96p235 Ns96p236 Ns96p237 Ns96p238 Ns96p239 Ns96p237 3362047 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 102050902) qz359 0 3 Ns96p235 Ns96p236 Ns96p237 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 102050902) (BSN.cosOddQ 67108864) 0 3 Ns96p238 Ns96p239 Ns96p237 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p241 := nat_lit 179884310147142804166612819041 

noncomputable def Ns96p242 := BSN.cos_dyadic_bound_f 20594361 67108864 2 1 67108864 33554432 Ns96p241 Ns96p131 Ns96p241 Ns96p241 Ns96p132 Ns96p241 63973587 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 20594361) qz359 0 1 Ns96p241 Ns96p131 Ns96p241 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 20594361) (BSN.cosOddQ 67108864) 0 1 Ns96p241 Ns96p132 Ns96p241 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p243 := Ns96p184 58992 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 66 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 3362047 67108864) BSN.abs_quadSignNeg qz636 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 63973587 67108864) qz32 rfl rfl (Ns96p234 rfl rfl) (Ns96p218 rfl) RS097to114.d27 RS097to114.d29 RS097to114.d31 RS097to114.d33 RS097to114.d17 (Ns96p240 rfl rfl) (Ns96p242 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns96p244 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 7) 33096677 67108864 58992 67108864 33096677 67108864 58992 67108864 4442160791289856 33096677 33554432 3687 2097152 (Ns96p243 rfl) 

noncomputable def Ns96p245 := @Enclosure.Real.IsNear.mulLit_tf qz645 (Zeta.RiemannSiegel.correction qz31) 98267 262144 1 4194304 2996324441175 4398046511104 61823538104267 1330409069608960000 294439813860943725 1152921504606846976 

noncomputable abbrev qz646 := (@HPow.hPow Real Real Real qz7 qz30 qz9)

noncomputable def Ns96p246 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz646 1 1 0 1 98267 262144 1 4194304 98267 262144 1 4194304 

noncomputable def Ns96p247 := @Enclosure.Real.IsNear.sqrt_image qz30 212416665167 4194304000 159103 4194304000 29848608 29848631 4194304 (@Enclosure.Real.IsNear.of_eq qz30 (@HMul.hMul Real Real Real qz5 qz29 qz3) Bool.false 212416665167 4194304000 159103 4194304000 (BSN.t_div_two_pi_mk qz29 318206 1000 qz32) (@Enclosure.Real.IsNear.mulLit_ff qz29 qz3 318206 1000 0 1 1335089 8388608 1 8388608 212416665167 4194304000 159103 4194304000 (Enclosure.Real.IsNear.const Bool.false 318206 1000) RS097to114.d36 rfl)) 

noncomputable abbrev qz872 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 318206 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz647 := qz872

noncomputable abbrev qz379 := qz647

noncomputable abbrev qz35 := qz379

noncomputable def Ns96p248 := @Enclosure.Real.IsNear.sqrt_image qz35 59697239 8388608 23 8388608 11189018 11189023 4194304 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 59697239 8388608 23 8388608 59697239 8388608 23 8388608 (Ns96p247 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns96p249 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz35) 22378041 8388608 5 8388608 1572271 1572273 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz35) Bool.false 22378041 8388608 5 8388608 22378041 8388608 5 8388608 (Ns96p248 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns96p250 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz35)) Bool.false 3144544 8388608 2 8388608 98267 262144 1 4194304 (Ns96p249 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz36 := (@HMul.hMul Real Real Real qz339 qz337 qz372)

noncomputable abbrev qz648 := (@HMul.hMul Real Real Real qz863 qz871 qz871)

noncomputable abbrev qz380 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz648 qz644) qz641)

noncomputable abbrev qz37 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz380))

noncomputable def Ns96p251 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz31) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz36)) qz37) Bool.false 2996324441175 

noncomputable def Ns96p252 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz36)) qz37 1409395 1048576 69 

noncomputable def Ns96p253 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz36)) Bool.false 11275160 8388608 276 8388608 1409395 1048576 69 

noncomputable def Ns96p254 := @Enclosure.Real.IsNear.recentre' (Real.cos qz36) Bool.false 3120521 4194304 183838608 10150215680000 3120521 4194304 11489913 634388480000 

noncomputable def Ns96p255 := @Enclosure.Real.IsNear.cos_image qz36 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6138565) qz357) Bool.false 6138565 8388608 145 8388608 Bool.false 3120521 4194304 1 

noncomputable def Ns96p256 := nat_lit 620679734416405265536382177 

noncomputable def Ns96p257 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz31 884279719003555 140737488355328 1 500000000000000 976983 8388608 23 8388608 863926252711250174565 1180591620717411303424 Ns96p256 

noncomputable def Ns96p258 := @Enclosure.Real.IsNear.subLit_ff_p qz35 qz1 59697239 8388608 23 8388608 7 1 0 1 976983 976983 8388608 23 

noncomputable def Ns96p259 := @Ns96p258 8388608 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 59697239 8388608 23 8388608 59697239 8388608 23 8388608 (Ns96p247 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns96p260 := @Enclosure.Real.IsNear.recentre' qz36 Bool.false 863926252711250174565 1180591620717411303424 Ns96p256 Ns96p148 6138565 8388608 145 8388608 (@Ns96p257 Ns96p148 RS097to114.d35 (Ns96p259 rfl rfl) rfl) 

noncomputable def Ns96p261 := nat_lit 11814366521682564378288842084868361264296317108840069190625 

noncomputable def Ns96p262 := nat_lit 988643523323402220304136834155207460536120982503085435781120 

noncomputable def Ns96p263 := nat_lit 2016205851642409587452434571367432175546893507000390625 

noncomputable def Ns96p264 := nat_lit 35439067153344408315691621385462348928537857539506206790625 

noncomputable def Ns96p265 := nat_lit 44488958549553099913686157536984335724125444212638844610150400 

noncomputable def Ns96p266 := BSN.cos_dyadic_bound_f 6138565 8388608 3 2 4194304 1210000 Ns96p261 Ns96p262 Ns96p263 Ns96p264 Ns96p265 Ns96p263 3120521 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 6138565) (BSN.cosEvenQ 8388608) 0 2 Ns96p261 Ns96p262 Ns96p263 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 6138565) (BSN.cosOddQ 8388608) 0 2 Ns96p264 Ns96p265 Ns96p263 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p267 := @Enclosure.Real.IsNear.inv_image (Real.cos qz36) 3120521 4194304 11489913 634388480000 5637442 5637718 4194304 (Ns96p254 (@Ns96p255 1210000 (Ns96p260 rfl) (Enclosure.sfrac_false_div 6138565 8388608) (Ns96p266 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns96p268 := @Enclosure.Real.IsNear.recentre' qz37 Bool.false 2125965 4194304 

noncomputable abbrev qz38 := (@HMul.hMul Real Real Real qz339 qz337 qz380)

noncomputable def Ns96p269 := @Enclosure.Real.IsNear.cos_image qz38 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8717833)) qz357) Bool.true 8717833 8388608 

noncomputable def Ns96p270 := nat_lit 10292200745754630130183292845 

noncomputable def Ns96p271 := nat_lit 1283888071829818283989615631574689 

noncomputable def Ns96p272 := @Enclosure.Real.IsNear.recentre' qz38 Bool.true Ns96p270 Ns96p163 Ns96p271 

noncomputable abbrev qz39 := qz380

noncomputable def Ns96p273 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz39 884279719003555 140737488355328 1 500000000000000 11639078138479 

noncomputable abbrev qz381 := (@HSub.hSub Real Real Real qz635 qz648 qz644)

noncomputable abbrev qz40 := qz381

noncomputable def Ns96p274 := @Enclosure.Real.IsNear.subLit_tf qz40 qz26 7241031627375 70368744177664 237879731 70368744177664 1 16 

noncomputable abbrev qz382 := qz648

noncomputable abbrev qz41 := qz382

noncomputable def Ns96p275 := @Enclosure.Real.IsNear.subLit_ff_n qz41 qz31 954495782289 70368744177664 44941747 70368744177664 976983 8388608 23 8388608 

noncomputable def Ns96p276 := @Enclosure.Real.IsNear.mulLit_ff qz31 qz31 976983 8388608 23 8388608 976983 8388608 23 8388608 954495782289 70368744177664 

noncomputable def Ns96p277 := nat_lit 48084433391423929568407579831839211654083000276363569497921 

noncomputable def Ns96p278 := nat_lit 33363251005317784675723020620295685150320006509286623041 

noncomputable def Ns96p279 := nat_lit 144186573672261153135871293454277043591948360816072135247681 

noncomputable def Ns96p280 := BSN.cos_dyadic_bound_f 8717833 8388608 3 2 4194304 1210000 Ns96p277 Ns96p262 Ns96p278 Ns96p279 Ns96p265 Ns96p278 2125965 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 8717833) (BSN.cosEvenQ 8388608) 0 2 Ns96p277 Ns96p262 Ns96p278 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 8717833) (BSN.cosOddQ 8388608) 0 2 Ns96p279 Ns96p265 Ns96p278 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p281 := @Ns96p268 224978608 10150215680000 2125965 4194304 14061163 634388480000 (@Ns96p269 179 8388608 Bool.false 2125965 4194304 1 1210000 (@Ns96p272 Ns96p166 8717833 8388608 179 8388608 (@Ns96p273 70368744177664 237879731 70368744177664 Ns96p270 Ns96p163 Ns96p271 Ns96p166 RS097to114.d35 (@Ns96p274 0 1 186225250215664 11639078138479 70368744177664 237879731 70368744177664 (@Ns96p275 60742175837650944000 7241031627375 70368744177664 237879731 70368744177664 (@Ns96p276 44941747 70368744177664 (Ns96p259 rfl rfl) (Ns96p259 rfl rfl) rfl) (Ns96p259 rfl rfl) rfl rfl) qz369 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 8717833 8388608) (BSN.cos_neg_of_bound 8717833 8388608 Bool.false 2125965 4194304 1 1210000 (Ns96p280 rfl rfl)) rfl rfl) 

noncomputable def Ns96p282 := @Ns96p245 98109867869265626391 Ns96p180 (Ns96p246 qz28 (@Enclosure.Real.IsNear.of_eq qz646 (@Inv.inv Real Real.instInv (Real.sqrt qz35)) Bool.false 98267 262144 1 4194304 (BSN.rpow_neg_quarter_mk qz30 (BSN.t_div_two_pi_nonneg qz29 318206 1000 qz32)) Ns96p250) rfl) (@Ns96p251 4398046511104 61823538104267 1330409069608960000 (BSN.correction_mk qz31 (BSN.cos_two_pi_p_ne_zero_mk qz29 318206 1000 7 qz32 rfl rfl (@BSN.floor_sqrt_eq_dec qz29 318206 1000 7 qz32 rfl rfl rfl))) (@Ns96p252 2097152 2125965 4194304 14061163 634388480000 2996324441175 4398046511104 61823538104267 1330409069608960000 (@Ns96p253 2097152 (Ns96p267 rfl rfl rfl rfl rfl) rfl) (Ns96p281 rfl) rfl)) 

noncomputable def Ns96p283 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz29) (hardyZApproximantRS₀ qz29) Bool.false 1431632976431146861 1152921504606846976 9908546347165736666391 Ns96p180 (@Eq.refl Real (hardyZApproximantRS₀ qz29)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz29) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz29) qz29 7) (@HMul.hMul Real Real Real qz5 qz645 (Zeta.RiemannSiegel.correction qz31))) Bool.false 1431632976431146861 1152921504606846976 9908546347165736666391 Ns96p180 (BSN.hardyZApproximantRS₀_eq qz29 7 (@BSN.floor_sqrt_eq_dec qz29 318206 1000 7 qz32 rfl rfl rfl)) (@Ns96p182 1431632976431146861 1152921504606846976 9908546347165736666391 Ns96p180 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz29) qz29 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 7)) Bool.false 33096677 33554432 3687 2097152 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz29) qz29 7) (Ns96p244 (Ns96p243 rfl) rfl rfl)) (Ns96p282 rfl) rfl rfl)) 

theorem RS097to114.d39 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz29) Bool.false 1431632976431146861 1152921504606846976 9908546347165736666391 Ns96p180 := Ns96p283 

noncomputable abbrev qz649 := (@HMul.hMul Real Real Real qz863 (Real.sqrt qz868) qz865)

noncomputable abbrev qz383 := qz649

noncomputable abbrev qz42 := qz383

noncomputable abbrev qz384 := (@HMul.hMul Real Real Real qz630 (@HMul.hMul Real Real Real qz630 qz649 qz649) qz649)

noncomputable abbrev qz43 := (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz384))

noncomputable abbrev qz44 := (@HMul.hMul Real Real Real qz339 (@HMul.hMul Real Real Real qz339 qz363 qz363) qz363)

noncomputable abbrev qz385 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz42))

noncomputable def Ns96p284 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz354 (@HAdd.hAdd Real Real Real qz354 qz385 qz43) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz44))) Bool.false 

noncomputable def Ns96p285 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz354 qz385 qz43) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz44)) 12496803 268435456 

noncomputable def Ns96p286 := @Enclosure.Real.IsNear.addLit_ff qz385 qz43 390525 8388608 25 16777216 

noncomputable def Ns96p287 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz42) 25 4 0 1 15621 2097152 1 4194304 390525 

noncomputable def Ns96p288 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz42) Bool.false 62484 8388608 2 8388608 15621 2097152 1 4194304 

noncomputable def Ns96p289 := @Enclosure.Real.IsNear.mulLit_ff qz20 qz8 22349823 8388608 5 8388608 105673629439 2097152000 79151 2097152000 2361786913729239297 17592186044416000 2297379383223 

noncomputable def Ns96p290 := @Enclosure.Real.IsNear.sqrt_image qz8 105673629439 2097152000 79151 2097152000 29773377 29773400 4194304 qz361 

noncomputable def Ns96p291 := @Enclosure.Real.IsNear.sqrt_image qz19 59546777 8388608 23 8388608 11174909 11174914 4194304 (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 59546777 8388608 23 8388608 59546777 8388608 23 8388608 (Ns96p290 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz386 := (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 22349823 8388608 5 8388608 22349823 8388608 5 8388608 (Ns96p291 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns96p292 := @Ns96p289 17592186044416000 qz386 

noncomputable def Ns96p293 := Ns96p292 qz361 

noncomputable def Ns96p294 := @Enclosure.Real.IsNear.inv_image qz42 2361786913729239297 17592186044416000 2297379383223 17592186044416000 31241 31243 4194304 (Ns96p293 rfl) rfl rfl 

noncomputable abbrev qz45 := (@Inv.inv Real Real.instInv qz384)

noncomputable def Ns96p295 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz45 1 32 0 1 3 

noncomputable def Ns96p296 := @Enclosure.Real.IsNear.recentre' qz45 Bool.false 3 8388608 1 8388608 

noncomputable def Ns96p297 := nat_lit 13174135796694421792247209424515308981850233883166051073 

noncomputable def Ns96p298 := nat_lit 5444517870735015415413993718908291383296000000000 

noncomputable def Ns96p299 := nat_lit 38444641939275915055692770794577145947938180956927 

noncomputable abbrev qz46 := qz384

noncomputable def Ns96p300 := @Enclosure.Real.IsNear.inv_image qz46 Ns96p297 Ns96p298 Ns96p299 Ns96p298 1 2 

noncomputable def Ns96p301 := nat_lit 5578037425862685225731630274289054209 

noncomputable def Ns96p302 := nat_lit 309485009821345068724781056000000 

noncomputable def Ns96p303 := nat_lit 10851846404286895432017562096191 

noncomputable abbrev qz387 := (@HMul.hMul Real Real Real qz630 qz649 qz649)

noncomputable abbrev qz47 := qz387

noncomputable def Ns96p304 := @Enclosure.Real.IsNear.mulLit_ff qz47 qz42 Ns96p301 Ns96p302 Ns96p303 Ns96p302 2361786913729239297 17592186044416000 2297379383223 

noncomputable def Ns96p305 := @Enclosure.Real.IsNear.mulLit_ff qz42 qz42 2361786913729239297 17592186044416000 2297379383223 17592186044416000 2361786913729239297 17592186044416000 2297379383223 17592186044416000 Ns96p301 

noncomputable def Ns96p306 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz44) 13 10 0 1 443545 8388608 1 

noncomputable def Ns96p307 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz44) Bool.false 443545 8388608 1 8388608 443545 8388608 

noncomputable def Ns96p308 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz20 qz20) qz20 499514588131329 70368744177664 223498255 70368744177664 22349823 8388608 5 8388608 11164062630653103904767 

noncomputable def Ns96p309 := @Enclosure.Real.IsNear.mulLit_ff qz20 qz20 22349823 8388608 5 8388608 22349823 8388608 5 8388608 499514588131329 70368744177664 223498255 

noncomputable def Ns96p310 := @Ns96p309 70368744177664 qz386 

noncomputable def Ns96p311 := Ns96p310 qz386 

noncomputable def Ns96p312 := @Ns96p308 590295810358705651712 7492720498206785 590295810358705651712 (Ns96p311 rfl) qz386 

noncomputable def Ns96p313 := @Enclosure.Real.IsNear.inv_image qz44 11164062630653103904767 590295810358705651712 7492720498206785 590295810358705651712 221772 221773 4194304 (Ns96p312 rfl) 

noncomputable def Ns96p314 := @Ns96p285 401 268435456 1153217 16777216 13 83886080 519225894502400 30948275 268435456 2213 1342177280 (@Ns96p286 3 268435456 1 268435456 104830781620224 12496803 268435456 401 268435456 (@Ns96p287 8388608 25 16777216 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns96p288 (Ns96p294 rfl rfl rfl rfl) rfl) rfl) (@Ns96p295 8388608 1 8388608 3 268435456 1 268435456 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns96p296 3 8388608 1 8388608 (@Ns96p300 4194304 (@Ns96p304 17592186044416000 Ns96p297 Ns96p298 Ns96p299 Ns96p298 (@Ns96p305 Ns96p302 Ns96p303 Ns96p302 (Ns96p293 rfl) (Ns96p293 rfl) rfl) (Ns96p293 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns96p306 8388608 1153217 16777216 13 83886080 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns96p307 1 8388608 (Ns96p313 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS097to114.d40 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 := @Ns96p284 30948275 268435456 2213 1342177280 (BSN.hardyZErrorBoundRS₀_mk qz4 316604 1000 qz11 rfl rfl) (Ns96p314 rfl rfl) 

noncomputable def Ns96p315 := nat_lit 8248806325105840891495448576 

noncomputable abbrev qz873 := (Enclosure.sfrac Bool.false 319806 1000)

noncomputable abbrev qz650 := qz873

noncomputable abbrev qz388 := qz650

noncomputable abbrev qz48 := qz388

noncomputable abbrev qz874 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 319806 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz651 := qz874

noncomputable abbrev qz389 := qz651

noncomputable abbrev qz49 := qz389

noncomputable abbrev qz875 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 319806 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz652 := qz875

noncomputable abbrev qz390 := qz652

noncomputable abbrev qz50 := qz390

noncomputable abbrev qz653 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz49 qz9))

noncomputable def Ns96p316 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz48) qz48 7) (@HMul.hMul Real Real Real qz5 qz653 (Zeta.RiemannSiegel.correction qz50)) 119972213 33554432 59289 33554432 17988100992573476283 73786976294838206464 13727847636776350773 697517510287142420480000 Ns96p315 

noncomputable def Ns96p317 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz48) qz48 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 319806 1000 66 98 67108864 33554432 1125899906842624 Bool.false 31413469401 1209 

noncomputable def Ns96p318 := Ns96p317 120242927 57 27397080 8 130587807 57 25364760 8 Bool.true 86832026 43987 Bool.true 83592544 Bool.true 18687811 3537118876014220 1 Bool.false 21439283 Bool.true Bool.false 64523636 Bool.true Bool.true 119972213 

noncomputable def Ns96p319 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz48) qz48 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 319806 1000 15 29 67108864 33554432 1125899906842624 Bool.false 31413469401 1209 

noncomputable def Ns96p320 := Ns96p319 93032624 56 33554424 8 108007536 56 30011992 8 Bool.true 91838105 25858 Bool.false 79862694 Bool.true 70972302 3537118876014220 1 Bool.false 62302955 Bool.false Bool.false 58462880 Bool.true Bool.true 86832026 

noncomputable def Ns96p321 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz48) qz48 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 319806 1000 156 74 67108864 33554432 1125899906842624 Bool.false 31413469401 1209 

noncomputable def Ns96p322 := Ns96p321 46516304 56 47453136 16 73726608 56 38745320 8 Bool.true 67108856 1272 Bool.false 92636581 Bool.false 34595380 3537118876014220 1 Bool.false 12700709 Bool.false Bool.false 58387446 Bool.true Bool.true 91838105 

noncomputable def Ns96p323 := nat_lit 35240222887434789683503802181977316267702487654219923 

noncomputable def Ns96p324 := nat_lit 75283990279934355597519539963033912273256054784000 

noncomputable def Ns96p325 := nat_lit 1605746425547059614842645652480000 

noncomputable def Ns96p326 := nat_lit 3081167562956621624733433507878113280 

noncomputable abbrev qz391 := (@Eq.refl Real qz650)

noncomputable abbrev qz51 := qz391

noncomputable def Ns96p327 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz48 319806 1000 409104510544 16000000 639612 4000 2000 Ns96p325 Ns96p326 qz51 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns96p328 := nat_lit 6495477882611980434463420818182058934462922524425816207360 

noncomputable abbrev qz392 := (Real.log (Enclosure.sfrac Bool.false 409104510544 16000000))

noncomputable abbrev qz393 := (Enclosure.sfrac Bool.false 319806 2000)

noncomputable abbrev qz52 := (@HSub.hSub Real Real Real qz342 (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 319806 4000) qz392) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 639612)))))) qz393)

noncomputable abbrev qz394 := (@HSub.hSub Real Real Real qz12 qz52 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 319806 2000) (Real.log Real.pi)))

noncomputable def Ns96p329 := @Enclosure.Real.IsNear.addLit_ft_p qz394 (Enclosure.sfrac Bool.true Ns96p325 Ns96p326) 2108124592879349093487 4503599627370496000 1114951797037465467 61952000000000000000000 Ns96p325 Ns96p326 0 1 Ns96p328 

noncomputable def Ns96p330 := nat_lit 70736923299297803361671184384000 

noncomputable abbrev qz395 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 319806 2000) (Real.log Real.pi))

noncomputable def Ns96p331 := @Enclosure.Real.IsNear.subLit_ff_p qz52 qz395 2932489330134709785711 4503599627370496000 512196942726483 60500000000000000000 6141995916183 33554432000 159903 16777216000 Ns96p330 2108124592879349093487 4503599627370496000 

noncomputable def Ns96p332 := nat_lit 5864978660269419571422000 

noncomputable abbrev qz53 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 319806 4000) qz392) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 639612))))))

noncomputable def Ns96p333 := @Enclosure.Real.IsNear.subLit_ff_p qz53 qz393 3652628421350134207599 4503599627370496000 512196942726483 60500000000000000000 319806 2000 0 1 Ns96p332 2932489330134709785711 4503599627370496000 512196942726483 60500000000000000000 

noncomputable def Ns96p334 := nat_lit 8224987998657673736669668144475799552 

noncomputable def Ns96p335 := nat_lit 12269554010384343599415296 

noncomputable def Ns96p336 := nat_lit 193044682834911147710976254805148466868399415715599301000122888402117992630529091978139661746341132824334139602717135339520 

noncomputable def Ns96p337 := nat_lit 3176265396931795261061922016828574073378303294756632264445730888248802427979273170843325442606383396197280624119019208704 

noncomputable def Ns96p338 := nat_lit 4440565996382995377767401842090872398819688468196872515168912706766927518206042241095452980874895728055033339576320 

noncomputable def Ns96p339 := BSN.log_dyadic_bound 146960510544 671248510544 6 5 Ns96p336 33554432 9680000 Ns96p337 Ns96p338 14934295 818209021088 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 146960510544) (BSN.artanhQ 671248510544) 0 5 Ns96p337 Ns96p336 Ns96p338 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns96p340 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 319806 4000) qz392 319806 4000 0 1 22853825260669633 2251799813685248 6250000847 60500000000000000 3654395220656856325599 4503599627370496000 999393885437841 121000000000000000000 (Enclosure.Real.IsNear.const Bool.false 319806 4000) (BSN.isNear_log_sfrac 409104510544 16000000 22853825260669633 2251799813685248 6250000847 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 409104510544) qz350)) Bool.false Ns96p335 Ns96p86 1000000135520000 9680000000000000000000 22853825260669633 2251799813685248 6250000847 60500000000000000 (BSN.log_rat_reduce_isNear 409104510544 16000000 14 818209021088 524288000000 14934295 33554432 24973259072661432 36028797018963968 9680000 1000000000000000 rfl rfl rfl rfl (Ns96p339 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p341 := BSN.arctan_dyadic_bound_f 1000 639612 1 0 4194304 1210000 0 1 1 0 1 1 6557 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 639612) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 639612) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz396 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 639612)))

noncomputable def Ns96p342 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz396 884279719003555 562949953421312 1 2000000000000000 6557 4194304 1 1210000 3705246699690903207936 883399653361059 562949953421312 200000000121 242000000000000000 qz17 (Ns96p341 rfl) rfl rfl 

noncomputable def Ns96p343 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 319806 4000) qz392) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz396)) 3654395220656856325599 4503599627370496000 999393885437841 121000000000000000000 883399653361059 2251799813685248 200000000121 968000000000000000 Ns96p334 3652628421350134207599 4503599627370496000 512196942726483 60500000000000000000 (Ns96p340 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz396) 1 4 0 1 883399653361059 562949953421312 200000000121 242000000000000000 883399653361059 2251799813685248 200000000121 968000000000000000 qz353 Ns96p342 rfl) 

noncomputable def Ns96p344 := @Ns96p329 Ns96p323 Ns96p324 1114951797037465467 61952000000000000000000 (@Ns96p331 1114951797037465467 61952000000000000000000 (Ns96p333 (Ns96p343 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 319806 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz393 (Real.log Real.pi) 319806 2000 0 1 38410761 33554432 1 16777216 6141995916183 33554432000 159903 16777216000 (Enclosure.Real.IsNear.const Bool.false 319806 2000) RS097to114.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns96p325 Ns96p326) 

noncomputable def Ns96p345 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz48) Bool.false Ns96p323 Ns96p324 1114951797037465467 61952000000000000000000 3926683675 8388608 19 1048576 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz48) (@HAdd.hAdd Real Real Real qz354 qz394 (Enclosure.sfrac Bool.true Ns96p325 Ns96p326)) Bool.false Ns96p323 Ns96p324 1114951797037465467 61952000000000000000000 Ns96p327 (Ns96p344 rfl rfl)) 

noncomputable def Ns96p346 := nat_lit 1898814002021656973803520 

noncomputable def Ns96p347 := nat_lit 139940964722789448875161116961629207650155420430720507539021128772762963388869986271425 

noncomputable def Ns96p348 := nat_lit 281074210982120512500294973422073122014744319164580374447965105839151982933260157121 

noncomputable def Ns96p349 := nat_lit 366056977932382266224231019228250282600478419849430103900711012804925324712767542837441 

noncomputable def Ns96p350 := BSN.sin_dyadic_bound_f 26983769913 17179869184 3 2 8388608 2422364 Ns96p347 Ns96p99 Ns96p348 Ns96p349 Ns96p102 Ns96p348 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26983769913) qz355 0 2 Ns96p347 Ns96p99 Ns96p348 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26983769913) qz356 0 2 Ns96p349 Ns96p102 Ns96p348 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p351 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz48) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3926683675) qz357) Bool.false 3926683675 8388608 19 1048576 Bool.true 8388607 8388608 1 1210000 (Ns96p345 rfl) (Enclosure.sfrac_false_div 3926683675 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3926683675) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns96p346) qz358) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 74 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q1 3926683675 8388608 226375608064910080 72057594037927936 74 Ns96p346 Ns96p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns96p346 Ns96p86 26983769913 17179869184 2422364 2420000 (Ns96p350 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p352 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz48) Bool.false Ns96p323 Ns96p324 1114951797037465467 61952000000000000000000 31413469401 67108864 1209 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz48) (@HAdd.hAdd Real Real Real qz354 qz394 (Enclosure.sfrac Bool.true Ns96p325 Ns96p326)) Bool.false Ns96p323 Ns96p324 1114951797037465467 61952000000000000000000 Ns96p327 (Ns96p344 rfl rfl)) 

noncomputable def Ns96p353 := Ns96p322 25858 BSN.abs_quadSignPos (BSN.cos_quad_nat0 156 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 12700709 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 74 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 58387446 67108864) qz51 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 1) Bool.true 8388607 8388608 1502411 79298560000 67108856 67108864 1272 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz48)) Bool.true 8388607 8388608 1502411 79298560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz48) qz48) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz48)) Bool.true 8388607 8388608 24038576 1268776960000 8388607 8388608 1502411 79298560000 (Ns96p351 rfl rfl) rfl)) rfl) (Ns96p352 rfl) RS097to114.d7 

noncomputable def Ns96p354 := nat_lit 605944400104482683153809352282772939820307144101572490573961356729158139187614616844388493738794457041 

noncomputable def Ns96p355 := nat_lit 399383588279954589042953604927601832953380372464323207848920455263875846623746552829300407441361 

noncomputable def Ns96p356 := nat_lit 3670775548544065351765920752743007423063968890065441747930433387028977007958467488414545234422212237265 

noncomputable def Ns96p357 := BSN.cos_dyadic_bound_f 92636581 67108864 4 3 67108864 33554432 Ns96p354 Ns96p236 Ns96p355 Ns96p356 Ns96p239 Ns96p355 12700709 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 92636581) qz359 0 3 Ns96p354 Ns96p236 Ns96p355 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 92636581) (BSN.cosOddQ 67108864) 0 3 Ns96p356 Ns96p239 Ns96p355 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p358 := nat_lit 48811202682362424253706009815938019663403601500109417623756800000 

noncomputable def Ns96p359 := nat_lit 2051846380424553984854272952663358917644751157633049600000000 

noncomputable def Ns96p360 := nat_lit 146429504354326423653148320901908732272375514998012986772070400000 

noncomputable def Ns96p361 := BSN.cos_dyadic_bound_f 34595380 67108864 3 2 67108864 33554432 Ns96p358 Ns96p108 Ns96p359 Ns96p360 Ns96p111 Ns96p359 58387446 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 34595380) qz359 0 2 Ns96p358 Ns96p108 Ns96p359 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 34595380) (BSN.cosOddQ 67108864) 0 2 Ns96p360 Ns96p111 Ns96p359 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p362 := nat_lit 2496692800024471230860054062988038343629654589158070248877669556480 

noncomputable def Ns96p363 := nat_lit 1654823382968174498890398041502559396389151299752924018810102016 

noncomputable def Ns96p364 := nat_lit 6536278095539285703063842853853858184769227202833441155792013435136 

noncomputable def Ns96p365 := BSN.sin_dyadic_bound_f 79862694 67108864 3 2 67108864 33554432 Ns96p362 Ns96p221 Ns96p363 Ns96p364 Ns96p224 Ns96p363 62302955 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 79862694) qz360 0 2 Ns96p362 Ns96p221 Ns96p363 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 79862694) (BSN.sinOddQ 67108864) 0 2 Ns96p364 Ns96p224 Ns96p363 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p366 := nat_lit 1556813256205186296487739250763535519676172107291180240134345376000 

noncomputable def Ns96p367 := nat_lit 643740947719133337306562633346004840529725481537303618923315456 

noncomputable def Ns96p368 := nat_lit 4076325804717275989207487412498128067505307392125840232587885854976 

noncomputable def Ns96p369 := BSN.sin_dyadic_bound_f 70972302 67108864 3 2 67108864 33554432 Ns96p366 Ns96p221 Ns96p367 Ns96p368 Ns96p224 Ns96p367 58462880 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 70972302) qz360 0 2 Ns96p366 Ns96p221 Ns96p367 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 70972302) (BSN.sinOddQ 67108864) 0 2 Ns96p368 Ns96p224 Ns96p367 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p370 := Ns96p320 43987 BSN.abs_quadSignPos (BSN.cos_quad_nat3 15 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 62302955 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 29 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 58462880 67108864) qz51 rfl rfl (Ns96p353 RS097to114.d9 RS097to114.d11 RS097to114.d13 RS097to114.d17 (Ns96p357 rfl rfl) (Ns96p361 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns96p352 rfl) RS097to114.d19 RS097to114.d21 RS097to114.d23 RS097to114.d25 RS097to114.d17 (Ns96p365 rfl rfl) (Ns96p369 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns96p371 := nat_lit 401473614329282235144888511333184543922794456057403479458013459834050116030745405061232905984111804416 

noncomputable def Ns96p372 := nat_lit 116415420058198100113518800908016442424721722776810185795415139701902462231486035262038381428736 

noncomputable def Ns96p373 := nat_lit 2433282543741260531057755078617150612162280608926546867360056332042749841940570413561624880956980592640 

noncomputable def Ns96p374 := BSN.cos_dyadic_bound_f 83592544 67108864 4 3 67108864 33554432 Ns96p371 Ns96p236 Ns96p372 Ns96p373 Ns96p239 Ns96p372 21439283 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 83592544) qz359 0 3 Ns96p371 Ns96p236 Ns96p372 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 83592544) (BSN.cosOddQ 67108864) 0 3 Ns96p373 Ns96p239 Ns96p372 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p375 := nat_lit 121964582307366407592559701841 

noncomputable def Ns96p376 := BSN.cos_dyadic_bound_f 18687811 67108864 2 1 67108864 33554432 Ns96p375 Ns96p131 Ns96p375 Ns96p375 Ns96p132 Ns96p375 64523636 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 18687811) qz359 0 1 Ns96p375 Ns96p131 Ns96p375 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 18687811) (BSN.cosOddQ 67108864) 0 1 Ns96p375 Ns96p132 Ns96p375 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p377 := Ns96p318 59289 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 66 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 21439283 67108864) BSN.abs_quadSignNeg qz636 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 64523636 67108864) qz51 rfl rfl (Ns96p370 rfl rfl) (Ns96p352 rfl) RS097to114.d27 RS097to114.d29 RS097to114.d31 RS097to114.d33 RS097to114.d17 (Ns96p374 rfl rfl) (Ns96p376 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns96p378 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 7) 119972213 67108864 59289 67108864 119972213 67108864 59289 67108864 16102397851992064 119972213 33554432 59289 33554432 (Ns96p377 rfl) 

noncomputable def Ns96p379 := @Enclosure.Real.IsNear.mulLit_tf qz653 (Zeta.RiemannSiegel.correction qz50) 785151 2097152 1 4194304 22910371371333 35184372088832 138771285129981 2660818139217920000 17988100992573476283 73786976294838206464 

noncomputable abbrev qz654 := (@HPow.hPow Real Real Real qz7 qz49 qz9)

noncomputable def Ns96p380 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz654 1 1 0 1 785151 2097152 1 4194304 785151 2097152 1 4194304 

noncomputable def Ns96p381 := @Enclosure.Real.IsNear.sqrt_image qz49 213484736367 4194304000 159903 4194304000 29923556 29923579 4194304 (@Enclosure.Real.IsNear.of_eq qz49 (@HMul.hMul Real Real Real qz5 qz48 qz3) Bool.false 213484736367 4194304000 159903 4194304000 (BSN.t_div_two_pi_mk qz48 319806 1000 qz51) (@Enclosure.Real.IsNear.mulLit_ff qz48 qz3 319806 1000 0 1 1335089 8388608 1 8388608 213484736367 4194304000 159903 4194304000 (Enclosure.Real.IsNear.const Bool.false 319806 1000) RS097to114.d36 rfl)) 

noncomputable abbrev qz876 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 319806 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz655 := qz876

noncomputable abbrev qz397 := qz655

noncomputable abbrev qz54 := qz397

noncomputable def Ns96p382 := @Enclosure.Real.IsNear.sqrt_image qz54 59847135 8388608 23 8388608 11203057 11203062 4194304 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 59847135 8388608 23 8388608 59847135 8388608 23 8388608 (Ns96p381 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns96p383 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz54) 22406119 8388608 5 8388608 1570301 1570303 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz54) Bool.false 22406119 8388608 5 8388608 22406119 8388608 5 8388608 (Ns96p382 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns96p384 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz54)) Bool.false 3140604 8388608 2 8388608 785151 2097152 1 4194304 (Ns96p383 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz55 := (@HMul.hMul Real Real Real qz339 qz337 qz390)

noncomputable abbrev qz656 := (@HMul.hMul Real Real Real qz863 qz875 qz875)

noncomputable abbrev qz398 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz656 qz652) qz641)

noncomputable abbrev qz56 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz398))

noncomputable def Ns96p385 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz50) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz55)) qz56) Bool.false 22910371371333 

noncomputable def Ns96p386 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz55)) qz56 12625027 8388608 347 

noncomputable def Ns96p387 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz55)) Bool.false 12625027 8388608 347 8388608 12625027 8388608 347 

noncomputable def Ns96p388 := @Enclosure.Real.IsNear.recentre' (Real.cos qz55) Bool.false 2786875 4194304 92524304 5075107840000 2786875 4194304 5782769 317194240000 

noncomputable def Ns96p389 := @Enclosure.Real.IsNear.cos_image qz55 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7080389) qz357) Bool.false 7080389 8388608 73 4194304 Bool.false 2786875 4194304 1 

noncomputable def Ns96p390 := nat_lit 620679734417692862371984609 

noncomputable def Ns96p391 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz50 884279719003555 140737488355328 1 500000000000000 1126879 8388608 23 8388608 996476245471007054845 1180591620717411303424 Ns96p390 

noncomputable def Ns96p392 := @Enclosure.Real.IsNear.subLit_ff_p qz54 qz1 59847135 8388608 23 8388608 7 1 0 1 1126879 1126879 8388608 23 

noncomputable def Ns96p393 := @Ns96p392 8388608 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 59847135 8388608 23 8388608 59847135 8388608 23 8388608 (Ns96p381 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns96p394 := @Enclosure.Real.IsNear.recentre' qz55 Bool.false 996476245471007054845 1180591620717411303424 Ns96p390 Ns96p148 7080389 8388608 73 4194304 (@Ns96p391 Ns96p148 RS097to114.d35 (Ns96p393 rfl rfl) rfl) 

noncomputable def Ns96p395 := nat_lit 20913587648411074121209346189274843070840222264603117448161 

noncomputable def Ns96p396 := nat_lit 6316215652355318006633109721612002702187814329211251681 

noncomputable def Ns96p397 := nat_lit 62728130513928511727614772348381305207116291165150929841121 

noncomputable def Ns96p398 := BSN.cos_dyadic_bound_f 7080389 8388608 3 2 4194304 1210000 Ns96p395 Ns96p262 Ns96p396 Ns96p397 Ns96p265 Ns96p396 2786875 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 7080389) (BSN.cosEvenQ 8388608) 0 2 Ns96p395 Ns96p262 Ns96p396 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 7080389) (BSN.cosOddQ 8388608) 0 2 Ns96p397 Ns96p265 Ns96p396 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p399 := @Enclosure.Real.IsNear.inv_image (Real.cos qz55) 2786875 4194304 5782769 317194240000 6312340 6312687 4194304 (Ns96p388 (@Ns96p389 1210000 (Ns96p394 rfl) (Enclosure.sfrac_false_div 7080389 8388608) (Ns96p398 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns96p400 := @Enclosure.Real.IsNear.recentre' qz56 Bool.false 1814679 4194304 

noncomputable abbrev qz57 := (@HMul.hMul Real Real Real qz339 qz337 qz398)

noncomputable def Ns96p401 := @Enclosure.Real.IsNear.cos_image qz57 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 1177931)) (@Nat.cast Real Real.instNatCast 1048576)) Bool.true 1177931 1048576 

noncomputable def Ns96p402 := nat_lit 11125243782551541144495501725 

noncomputable def Ns96p403 := nat_lit 6605515178094830685937451543937589 

noncomputable def Ns96p404 := @Enclosure.Real.IsNear.recentre' qz57 Bool.true Ns96p402 Ns96p163 Ns96p403 

noncomputable def Ns96p405 := nat_lit 302231454903657293676544000000000000000 

noncomputable abbrev qz58 := qz398

noncomputable def Ns96p406 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz58 884279719003555 140737488355328 1 500000000000000 12581136424895 

noncomputable abbrev qz399 := (@HSub.hSub Real Real Real qz635 qz656 qz652)

noncomputable abbrev qz59 := qz399

noncomputable def Ns96p407 := @Enclosure.Real.IsNear.subLit_tf qz59 qz26 8183089913791 70368744177664 244774947 70368744177664 1 16 

noncomputable abbrev qz400 := qz656

noncomputable abbrev qz60 := qz400

noncomputable def Ns96p408 := @Enclosure.Real.IsNear.subLit_ff_n qz60 qz50 1269856280641 70368744177664 51836963 70368744177664 1126879 8388608 23 8388608 

noncomputable def Ns96p409 := @Enclosure.Real.IsNear.mulLit_ff qz50 qz50 1126879 8388608 23 8388608 1126879 8388608 23 8388608 1269856280641 70368744177664 

noncomputable def Ns96p410 := nat_lit 3913810740663520905159109829395540981178724620269921 

noncomputable def Ns96p411 := nat_lit 3706455678547648840390001530499419400701287692641 

noncomputable def Ns96p412 := nat_lit 11734019310633467417796549485125624104734771285424481 

noncomputable def Ns96p413 := BSN.cos_dyadic_bound_f 1177931 1048576 3 2 4194304 1210000 Ns96p410 Ns96p172 Ns96p411 Ns96p412 Ns96p175 Ns96p411 1814679 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1177931) (BSN.cosEvenQ 1048576) 0 2 Ns96p410 Ns96p172 Ns96p411 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1177931) (BSN.cosOddQ 1048576) 0 2 Ns96p412 Ns96p175 Ns96p411 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p414 := @Ns96p400 28878576 1268776960000 1814679 4194304 1804911 79298560000 (@Ns96p401 23 1048576 Bool.false 1814679 4194304 1 1210000 (@Ns96p404 Ns96p405 1177931 1048576 23 1048576 (@Ns96p406 70368744177664 244774947 70368744177664 Ns96p402 Ns96p163 Ns96p403 Ns96p405 RS097to114.d35 (@Ns96p407 0 1 201298182798320 12581136424895 70368744177664 244774947 70368744177664 (@Ns96p408 68644733515546492928 8183089913791 70368744177664 244774947 70368744177664 (@Ns96p409 51836963 70368744177664 (Ns96p393 rfl rfl) (Ns96p393 rfl rfl) rfl) (Ns96p393 rfl rfl) rfl rfl) qz369 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 1177931 1048576) (BSN.cos_neg_of_bound 1177931 1048576 Bool.false 1814679 4194304 1 1210000 (Ns96p413 rfl rfl)) rfl rfl) 

noncomputable def Ns96p415 := @Ns96p379 13727847636776350773 697517510287142420480000 (Ns96p380 qz28 (@Enclosure.Real.IsNear.of_eq qz654 (@Inv.inv Real Real.instInv (Real.sqrt qz54)) Bool.false 785151 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz49 (BSN.t_div_two_pi_nonneg qz48 319806 1000 qz51)) Ns96p384) rfl) (@Ns96p385 35184372088832 138771285129981 2660818139217920000 (BSN.correction_mk qz50 (BSN.cos_two_pi_p_ne_zero_mk qz48 319806 1000 7 qz51 rfl rfl (@BSN.floor_sqrt_eq_dec qz48 319806 1000 7 qz51 rfl rfl rfl))) (@Ns96p386 8388608 1814679 4194304 1804911 79298560000 22910371371333 35184372088832 138771285129981 2660818139217920000 (@Ns96p387 8388608 (Ns96p399 rfl rfl rfl rfl rfl) rfl) (Ns96p414 rfl) rfl)) 

noncomputable def Ns96p416 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz48) (hardyZApproximantRS₀ qz48) Bool.true 245833585414464500293 73786976294838206464 1246206337137489310773 697517510287142420480000 (@Eq.refl Real (hardyZApproximantRS₀ qz48)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz48) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz48) qz48 7) (@HMul.hMul Real Real Real qz5 qz653 (Zeta.RiemannSiegel.correction qz50))) Bool.true 245833585414464500293 73786976294838206464 1246206337137489310773 697517510287142420480000 (BSN.hardyZApproximantRS₀_eq qz48 7 (@BSN.floor_sqrt_eq_dec qz48 319806 1000 7 qz51 rfl rfl rfl)) (@Ns96p316 245833585414464500293 73786976294838206464 1246206337137489310773 697517510287142420480000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz48) qz48 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 7)) Bool.true 119972213 33554432 59289 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz48) qz48 7) (Ns96p378 (Ns96p377 rfl) rfl rfl)) (Ns96p415 rfl) rfl rfl)) 

theorem RS097to114.d41 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz48) Bool.true 245833585414464500293 73786976294838206464 1246206337137489310773 697517510287142420480000 := Ns96p416 

noncomputable def Ns96p417 := nat_lit 18777459223479755751817216 

noncomputable abbrev qz877 := (Enclosure.sfrac Bool.false 321404 1000)

noncomputable abbrev qz657 := qz877

noncomputable abbrev qz401 := qz657

noncomputable abbrev qz61 := qz401

noncomputable abbrev qz878 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 321404 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz658 := qz878

noncomputable abbrev qz402 := qz658

noncomputable abbrev qz62 := qz402

noncomputable abbrev qz879 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 321404 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz659 := qz879

noncomputable abbrev qz403 := qz659

noncomputable abbrev qz63 := qz403

noncomputable abbrev qz660 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz62 qz9))

noncomputable def Ns96p418 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz61) qz61 7) (@HMul.hMul Real Real Real qz5 qz660 (Zeta.RiemannSiegel.correction qz63)) 8470065 33554432 931 524288 268582676039992643 1152921504606846976 1193928232497267263 50728546202701266944000 Ns96p417 

noncomputable def Ns96p419 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 321404 1000 66 98 67108864 33554432 1125899906842624 Bool.false 31624320877 1214 

noncomputable def Ns96p420 := Ns96p419 120242927 57 27397080 8 130587807 57 25364760 8 Bool.false 48627536 44206 Bool.true 64889266 Bool.true 16515651 3537118876014220 1 Bool.false 38106630 Bool.true Bool.false 65086830 Bool.true Bool.false 8470065 

noncomputable def Ns96p421 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 321404 1000 16 29 67108864 33554432 1125899906842624 Bool.false 31624320877 1214 

noncomputable def Ns96p422 := Ns96p421 93032624 56 33554424 8 108007536 56 30011992 8 Bool.false 34008315 25987 Bool.false 36633679 Bool.true 32716868 3537118876014220 1 Bool.false 57355831 Bool.false Bool.false 31436184 Bool.true Bool.false 48627536 

noncomputable def Ns96p423 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 321404 1000 158 75 67108864 33554432 1125899906842624 Bool.false 31624320877 1214 

noncomputable def Ns96p424 := Ns96p423 46516304 56 47453136 16 73726608 56 38745320 8 Bool.false 67108856 1280 Bool.false 18326289 Bool.false 22217379 3537118876014220 1 Bool.false 64622077 Bool.true Bool.false 21813745 Bool.false Bool.false 34008315 

noncomputable def Ns96p425 := nat_lit 321273194582877105061512020879473168974735150423491 

noncomputable def Ns96p426 := nat_lit 681762596764774274969163785061602487177314304000 

noncomputable def Ns96p427 := nat_lit 1646267054835795853478236651520000 

noncomputable def Ns96p428 := nat_lit 3174704484477519406793470424886804480 

noncomputable abbrev qz404 := (@Eq.refl Real qz657)

noncomputable abbrev qz64 := qz404

noncomputable def Ns96p429 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz61 321404 1000 413203124864 16000000 642808 4000 2000 Ns96p427 Ns96p428 qz64 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns96p430 := nat_lit 3368793612829349433169800288057144576308518850904624988160 

noncomputable abbrev qz405 := (Enclosure.sfrac Bool.false 321404 2000)

noncomputable abbrev qz661 := (Real.log (Enclosure.sfrac Bool.false 413203124864 16000000))

noncomputable abbrev qz65 := (@HSub.hSub Real Real Real qz342 (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 321404 4000) qz661) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 642808)))))) qz405)

noncomputable abbrev qz406 := (@HSub.hSub Real Real Real qz12 qz65 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 321404 2000) (Real.log Real.pi)))

noncomputable def Ns96p431 := @Enclosure.Real.IsNear.addLit_ft_p qz406 (Enclosure.sfrac Bool.true Ns96p427 Ns96p428) 1061137292105353368167 2251799813685248000 560229503159754939 30976000000000000000000 Ns96p427 Ns96p428 0 1 Ns96p430 

noncomputable def Ns96p432 := nat_lit 712117182212264328562611322880 

noncomputable abbrev qz407 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 321404 2000) (Real.log Real.pi))

noncomputable def Ns96p433 := @Enclosure.Real.IsNear.subLit_ff_p qz65 qz407 59015169802374641279 90071992547409920 1029387636129719 121000000000000000000 3086343057111 16777216000 80351 8388608000 Ns96p432 1061137292105353368167 2251799813685248000 

noncomputable def Ns96p434 := nat_lit 2950758490118732063950000 

noncomputable abbrev qz66 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 321404 4000) qz661) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 642808))))))

noncomputable def Ns96p435 := @Enclosure.Real.IsNear.subLit_ff_p qz66 qz405 1837247978718212756071 2251799813685248000 1029387636129719 121000000000000000000 321404 2000 0 1 Ns96p434 59015169802374641279 90071992547409920 1029387636129719 121000000000000000000 

noncomputable def Ns96p436 := nat_lit 4137114656171269966735590269395140608 

noncomputable def Ns96p437 := nat_lit 12281605354756810894999552 

noncomputable def Ns96p438 := nat_lit 205161113076857474420929458291977860311430222253328385106033854886973968793342849851221236248072775350418955463684542955520 

noncomputable def Ns96p439 := nat_lit 3528004078662965677804783865050109114463583534313683588297915799648525120339687333248476197762070600225593826680613371904 

noncomputable def Ns96p440 := nat_lit 5846574015503156084415363683019466108045891797409287493980242161380038241307995659268412826659093406428942376632320 

noncomputable def Ns96p441 := BSN.log_dyadic_bound 151059124864 675347124864 6 5 Ns96p438 33554432 9680000 Ns96p439 Ns96p440 15268787 826406249728 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 151059124864) (BSN.artanhQ 675347124864) 0 5 Ns96p439 Ns96p438 Ns96p440 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns96p442 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 321404 4000) qz661 321404 4000 0 1 22876272638806721 2251799813685248 6250000847 60500000000000000 1838131382800758839071 2251799813685248000 502193818057297 60500000000000000000 (Enclosure.Real.IsNear.const Bool.false 321404 4000) (BSN.isNear_log_sfrac 413203124864 16000000 22876272638806721 2251799813685248 6250000847 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 413203124864) qz350)) Bool.false Ns96p437 Ns96p86 1000000135520000 9680000000000000000000 22876272638806721 2251799813685248 6250000847 60500000000000000 (BSN.log_rat_reduce_isNear 413203124864 16000000 14 826406249728 524288000000 15268787 33554432 24973259072661432 36028797018963968 9680000 1000000000000000 rfl rfl rfl rfl (Ns96p441 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p443 := BSN.arctan_dyadic_bound_f 1000 642808 1 0 4194304 1210000 0 1 1 0 1 1 6524 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 642808) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 642808) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz408 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 642808)))

noncomputable def Ns96p444 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz408 884279719003555 562949953421312 1 2000000000000000 6524 4194304 1 1210000 3705265277039366111232 883404082546083 562949953421312 200000000121 242000000000000000 qz17 (Ns96p443 rfl) rfl rfl 

noncomputable def Ns96p445 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 321404 4000) qz661) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz408)) 1838131382800758839071 2251799813685248000 502193818057297 60500000000000000000 883404082546083 2251799813685248 200000000121 968000000000000000 Ns96p436 1837247978718212756071 2251799813685248000 1029387636129719 121000000000000000000 (Ns96p442 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz408) 1 4 0 1 883404082546083 562949953421312 200000000121 242000000000000000 883404082546083 2251799813685248 200000000121 968000000000000000 qz353 Ns96p444 rfl) 

noncomputable def Ns96p446 := @Ns96p431 Ns96p425 Ns96p426 560229503159754939 30976000000000000000000 (@Ns96p433 560229503159754939 30976000000000000000000 (Ns96p435 (Ns96p445 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 321404 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz405 (Real.log Real.pi) 321404 2000 0 1 38410761 33554432 1 16777216 3086343057111 16777216000 80351 8388608000 (Enclosure.Real.IsNear.const Bool.false 321404 2000) RS097to114.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns96p427 Ns96p428) 

noncomputable def Ns96p447 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz61) Bool.false Ns96p425 Ns96p426 560229503159754939 30976000000000000000000 3953040109 8388608 153 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz61) (@HAdd.hAdd Real Real Real qz354 qz406 (Enclosure.sfrac Bool.true Ns96p427 Ns96p428)) Bool.false Ns96p425 Ns96p426 560229503159754939 30976000000000000000000 Ns96p429 (Ns96p446 rfl rfl)) 

noncomputable def Ns96p448 := nat_lit 1899223971304200824946688 

noncomputable def Ns96p449 := nat_lit 140062104443783505660370139752765838435070591670496804287405539924379076296074028951105 

noncomputable def Ns96p450 := nat_lit 281560067564251655372906569335378143284821524286843931106447940591088992913445398081 

noncomputable def Ns96p451 := nat_lit 366373462005281345477984707764034202717009457621503406769032641231464389072619735656001 

noncomputable def Ns96p452 := BSN.sin_dyadic_bound_f 26989595927 17179869184 3 2 8388608 2422364 Ns96p449 Ns96p99 Ns96p450 Ns96p451 Ns96p102 Ns96p450 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26989595927) qz355 0 2 Ns96p449 Ns96p99 Ns96p450 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26989595927) qz356 0 2 Ns96p451 Ns96p102 Ns96p450 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p453 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz61) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3953040109) qz357) Bool.false 3953040109 8388608 153 8388608 Bool.false 8388607 8388608 1 1210000 (Ns96p447 rfl) (Enclosure.sfrac_false_div 3953040109 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3953040109) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns96p448) qz358) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 74 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q3 3953040109 8388608 226375608064910080 72057594037927936 74 Ns96p448 Ns96p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns96p448 Ns96p86 26989595927 17179869184 2422364 2420000 (Ns96p452 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p454 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz61) Bool.false Ns96p425 Ns96p426 560229503159754939 30976000000000000000000 31624320877 67108864 1214 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz61) (@HAdd.hAdd Real Real Real qz354 qz406 (Enclosure.sfrac Bool.true Ns96p427 Ns96p428)) Bool.false Ns96p425 Ns96p426 560229503159754939 30976000000000000000000 Ns96p429 (Ns96p446 rfl rfl)) 

noncomputable def Ns96p455 := Ns96p424 25987 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 158 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 64622077 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 75 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 21813745 67108864) qz64 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 1) Bool.false 8388607 8388608 12094913 634388480000 67108856 67108864 1280 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz61)) Bool.false 8388607 8388608 12094913 634388480000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz61) qz61) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz61)) Bool.false 8388607 8388608 193518608 10150215680000 8388607 8388608 12094913 634388480000 (Ns96p453 rfl rfl) rfl)) rfl) (Ns96p454 rfl) RS097to114.d7 

noncomputable def Ns96p456 := nat_lit 112797149287417014046109733441 

noncomputable def Ns96p457 := BSN.cos_dyadic_bound_f 18326289 67108864 2 1 67108864 33554432 Ns96p456 Ns96p131 Ns96p456 Ns96p456 Ns96p132 Ns96p456 64622077 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 18326289) qz359 0 1 Ns96p456 Ns96p131 Ns96p456 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 18326289) (BSN.cosOddQ 67108864) 0 1 Ns96p456 Ns96p132 Ns96p456 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p458 := nat_lit 243652737072697658571425788881 

noncomputable def Ns96p459 := BSN.sin_dyadic_bound_f 22217379 67108864 2 1 67108864 33554432 Ns96p458 Ns96p127 Ns96p458 Ns96p458 Ns96p128 Ns96p458 21813745 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 22217379) qz360 0 1 Ns96p458 Ns96p127 Ns96p458 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 22217379) (BSN.sinOddQ 67108864) 0 1 Ns96p458 Ns96p128 Ns96p458 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p460 := nat_lit 61372515984522822697084474575688610479899120831558244239381191041 

noncomputable def Ns96p461 := nat_lit 3243726919247649351731675517775012722205097856456812337125761 

noncomputable def Ns96p462 := nat_lit 184111060499729972792549960376030281414252952298961819093469321601 

noncomputable def Ns96p463 := BSN.cos_dyadic_bound_f 36633679 67108864 3 2 67108864 33554432 Ns96p460 Ns96p108 Ns96p461 Ns96p462 Ns96p111 Ns96p461 57355831 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 36633679) qz359 0 2 Ns96p460 Ns96p108 Ns96p461 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 36633679) (BSN.cosOddQ 67108864) 0 2 Ns96p462 Ns96p111 Ns96p461 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p464 := nat_lit 1145742141505230746736507371776 

noncomputable def Ns96p465 := BSN.sin_dyadic_bound_f 32716868 67108864 2 1 67108864 33554432 Ns96p464 Ns96p127 Ns96p464 Ns96p464 Ns96p128 Ns96p464 31436184 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 32716868) qz360 0 1 Ns96p464 Ns96p127 Ns96p464 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 32716868) (BSN.sinOddQ 67108864) 0 1 Ns96p464 Ns96p128 Ns96p464 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p466 := Ns96p422 44206 BSN.abs_quadSignPos (BSN.cos_quad_nat0 16 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 57355831 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 29 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 31436184 67108864) qz64 rfl rfl (Ns96p455 RS097to114.d9 RS097to114.d11 RS097to114.d13 RS097to114.d17 (Ns96p457 rfl rfl) (Ns96p459 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns96p454 rfl) RS097to114.d19 RS097to114.d21 RS097to114.d23 RS097to114.d25 RS097to114.d17 (Ns96p463 rfl rfl) (Ns96p465 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns96p467 := nat_lit 604430243214408278106903208039314709163775445879894765169319198976 

noncomputable def Ns96p468 := nat_lit 314327872485921721455534819737709226667423018583371621972951296 

noncomputable def Ns96p469 := nat_lit 1812662073898252990877798554478468709037991491602517552264011694336 

noncomputable def Ns96p470 := BSN.cos_dyadic_bound_f 64889266 67108864 3 2 67108864 33554432 Ns96p467 Ns96p108 Ns96p468 Ns96p469 Ns96p111 Ns96p468 38106630 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 64889266) qz359 0 2 Ns96p467 Ns96p108 Ns96p468 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 64889266) (BSN.cosOddQ 67108864) 0 2 Ns96p469 Ns96p111 Ns96p468 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p471 := nat_lit 74401687878622883868390347601 

noncomputable def Ns96p472 := BSN.cos_dyadic_bound_f 16515651 67108864 2 1 67108864 33554432 Ns96p471 Ns96p131 Ns96p471 Ns96p471 Ns96p132 Ns96p471 65086830 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 16515651) qz359 0 1 Ns96p471 Ns96p131 Ns96p471 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 16515651) (BSN.cosOddQ 67108864) 0 1 Ns96p471 Ns96p132 Ns96p471 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p473 := Ns96p420 59584 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 66 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 38106630 67108864) BSN.abs_quadSignNeg qz636 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 65086830 67108864) qz64 rfl rfl (Ns96p466 rfl rfl) (Ns96p454 rfl) RS097to114.d27 RS097to114.d29 RS097to114.d31 RS097to114.d33 RS097to114.d17 (Ns96p470 rfl rfl) (Ns96p472 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns96p474 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 7) 8470065 67108864 59584 67108864 8470065 67108864 59584 67108864 1136832880312320 8470065 33554432 931 524288 (Ns96p473 rfl) 

noncomputable def Ns96p475 := @Enclosure.Real.IsNear.mulLit_tf qz660 (Zeta.RiemannSiegel.correction qz63) 3136693 8388608 1 8388608 85626064151 137438953472 8347494235919 133040906960896000 268582676039992643 1152921504606846976 

noncomputable abbrev qz662 := (@HPow.hPow Real Real Real qz7 qz62 qz9)

noncomputable def Ns96p476 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz662 1 1 0 1 3136693 8388608 1 8388608 3136693 8388608 1 8388608 

noncomputable def Ns96p477 := @Enclosure.Real.IsNear.sqrt_image qz62 107275736239 2097152000 80351 2097152000 29998223 29998247 4194304 (@Enclosure.Real.IsNear.of_eq qz62 (@HMul.hMul Real Real Real qz5 qz61 qz3) Bool.false 107275736239 2097152000 80351 2097152000 (BSN.t_div_two_pi_mk qz61 321404 1000 qz64) (@Enclosure.Real.IsNear.mulLit_ff qz61 qz3 321404 1000 0 1 1335089 8388608 1 8388608 107275736239 2097152000 80351 2097152000 (Enclosure.Real.IsNear.const Bool.false 321404 1000) RS097to114.d36 rfl)) 

noncomputable abbrev qz880 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 321404 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz663 := qz880

noncomputable abbrev qz409 := qz663

noncomputable abbrev qz67 := qz409

noncomputable def Ns96p478 := @Enclosure.Real.IsNear.sqrt_image qz67 29998235 4194304 3 1048576 11217025 11217031 4194304 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 59996470 8388608 24 8388608 29998235 4194304 3 1048576 (Ns96p477 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns96p479 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz67) 2804257 1048576 3 4194304 1568346 1568347 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz67) Bool.false 22434056 8388608 6 8388608 2804257 1048576 3 4194304 (Ns96p478 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns96p480 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz67)) Bool.false 3136693 8388608 1 8388608 3136693 8388608 1 8388608 (Ns96p479 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz68 := (@HMul.hMul Real Real Real qz339 qz337 qz403)

noncomputable abbrev qz664 := (@HMul.hMul Real Real Real qz863 qz879 qz879)

noncomputable abbrev qz410 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz664 qz659) qz641)

noncomputable abbrev qz69 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz410))

noncomputable def Ns96p481 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz63) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz68)) qz69) Bool.false 85626064151 

noncomputable def Ns96p482 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz68)) qz69 1817693 1048576 119 

noncomputable def Ns96p483 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz68)) Bool.false 14541544 8388608 476 8388608 1817693 1048576 119 

noncomputable def Ns96p484 := @Enclosure.Real.IsNear.recentre' (Real.cos qz68) Bool.false 2419576 4194304 191098608 10150215680000 302447 524288 11943663 634388480000 

noncomputable def Ns96p485 := @Enclosure.Real.IsNear.cos_image qz68 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8018689) qz357) Bool.false 8018689 8388608 151 8388608 Bool.false 2419576 4194304 1 

noncomputable def Ns96p486 := nat_lit 80958226228502460713681237 

noncomputable def Ns96p487 := nat_lit 4503599627370496000000000000000 

noncomputable def Ns96p488 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz63 884279719003555 140737488355328 1 500000000000000 638107 4194304 3 1048576 564265078654201470385 590295810358705651712 Ns96p486 

noncomputable def Ns96p489 := @Enclosure.Real.IsNear.subLit_ff_p qz67 qz1 29998235 4194304 3 1048576 7 1 0 1 638107 638107 4194304 3 

noncomputable def Ns96p490 := @Ns96p489 1048576 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 59996470 8388608 24 8388608 29998235 4194304 3 1048576 (Ns96p477 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns96p491 := @Enclosure.Real.IsNear.recentre' qz68 Bool.false 564265078654201470385 590295810358705651712 Ns96p486 Ns96p487 8018689 8388608 151 8388608 (@Ns96p488 Ns96p487 RS097to114.d35 (Ns96p490 rfl rfl) rfl) 

noncomputable def Ns96p492 := nat_lit 34411067658286713236337593076441868180639563208183472117761 

noncomputable def Ns96p493 := nat_lit 17093341120183794674570938090442434964910098175472097281 

noncomputable def Ns96p494 := nat_lit 103199016292619772119663637353144719671988869428199472158721 

noncomputable def Ns96p495 := BSN.cos_dyadic_bound_f 8018689 8388608 3 2 4194304 1210000 Ns96p492 Ns96p262 Ns96p493 Ns96p494 Ns96p265 Ns96p493 2419576 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 8018689) (BSN.cosEvenQ 8388608) 0 2 Ns96p492 Ns96p262 Ns96p493 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 8018689) (BSN.cosOddQ 8388608) 0 2 Ns96p494 Ns96p265 Ns96p493 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p496 := @Enclosure.Real.IsNear.inv_image (Real.cos qz68) 302447 524288 11943663 634388480000 7270534 7271010 4194304 (Ns96p484 (@Ns96p485 1210000 (Ns96p491 rfl) (Enclosure.sfrac_false_div 8018689 8388608) (Ns96p495 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns96p497 := @Enclosure.Real.IsNear.recentre' qz69 Bool.false 1507424 4194304 

noncomputable abbrev qz70 := (@HMul.hMul Real Real Real qz339 qz337 qz410)

noncomputable def Ns96p498 := @Enclosure.Real.IsNear.cos_image qz70 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 10092951)) qz357) Bool.true 10092951 8388608 

noncomputable def Ns96p499 := nat_lit 2978913613165737945159469525 

noncomputable def Ns96p500 := nat_lit 2475880078570760549798248448 

noncomputable def Ns96p501 := nat_lit 44288440532954749252903581889457 

noncomputable def Ns96p502 := @Enclosure.Real.IsNear.recentre' qz70 Bool.true Ns96p499 Ns96p500 Ns96p501 

noncomputable def Ns96p503 := nat_lit 1888946593147858085478400000000000000 

noncomputable abbrev qz71 := qz410

noncomputable def Ns96p504 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz71 884279719003555 140737488355328 1 500000000000000 3368745826855 

noncomputable abbrev qz411 := (@HSub.hSub Real Real Real qz635 qz664 qz659)

noncomputable abbrev qz72 := qz411

noncomputable def Ns96p505 := @Enclosure.Real.IsNear.subLit_tf qz72 qz26 2269234199079 17592186044416 8205795 2199023255552 1 16 

noncomputable abbrev qz412 := qz664

noncomputable abbrev qz73 := qz412

noncomputable def Ns96p506 := @Enclosure.Real.IsNear.subLit_ff_n qz73 qz63 407180543449 17592186044416 1914339 2199023255552 638107 4194304 3 1048576 

noncomputable def Ns96p507 := @Enclosure.Real.IsNear.mulLit_ff qz63 qz63 638107 4194304 3 1048576 638107 4194304 3 1048576 407180543449 17592186044416 

noncomputable def Ns96p508 := nat_lit 86433667469987279311433207281422554023659533881739900002881 

noncomputable def Ns96p509 := nat_lit 107682546802062865765564135203607398949412257551382913601 

noncomputable def Ns96p510 := nat_lit 259085637316357712202768493573860447273079777130116934181441 

noncomputable def Ns96p511 := BSN.cos_dyadic_bound_f 10092951 8388608 3 2 4194304 1210000 Ns96p508 Ns96p262 Ns96p509 Ns96p510 Ns96p265 Ns96p509 1507424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 10092951) (BSN.cosEvenQ 8388608) 0 2 Ns96p508 Ns96p262 Ns96p509 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 10092951) (BSN.cosOddQ 8388608) 0 2 Ns96p510 Ns96p265 Ns96p509 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p512 := @Ns96p497 123984304 5075107840000 47107 131072 7749019 317194240000 (@Ns96p498 99 4194304 Bool.false 1507424 4194304 1 1210000 (@Ns96p502 Ns96p503 10092951 8388608 99 4194304 (@Ns96p504 17592186044416 8205795 2199023255552 Ns96p499 Ns96p500 Ns96p501 Ns96p503 RS097to114.d35 (@Ns96p505 0 1 53899933229680 3368745826855 17592186044416 8205795 2199023255552 (@Ns96p506 9517858078133846016 2269234199079 17592186044416 8205795 2199023255552 (@Ns96p507 1914339 2199023255552 (Ns96p490 rfl rfl) (Ns96p490 rfl rfl) rfl) (Ns96p490 rfl rfl) rfl rfl) qz369 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 10092951 8388608) (BSN.cos_neg_of_bound 10092951 8388608 Bool.false 1507424 4194304 1 1210000 (Ns96p511 rfl rfl)) rfl rfl) 

noncomputable def Ns96p513 := @Ns96p475 1193928232497267263 50728546202701266944000 (Ns96p476 qz28 (@Enclosure.Real.IsNear.of_eq qz662 (@Inv.inv Real Real.instInv (Real.sqrt qz67)) Bool.false 3136693 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz62 (BSN.t_div_two_pi_nonneg qz61 321404 1000 qz64)) Ns96p480) rfl) (@Ns96p481 137438953472 8347494235919 133040906960896000 (BSN.correction_mk qz63 (BSN.cos_two_pi_p_ne_zero_mk qz61 321404 1000 7 qz64 rfl rfl (@BSN.floor_sqrt_eq_dec qz61 321404 1000 7 qz64 rfl rfl rfl))) (@Ns96p482 2097152 47107 131072 7749019 317194240000 85626064151 137438953472 8347494235919 133040906960896000 (@Ns96p483 2097152 (Ns96p496 rfl rfl rfl rfl rfl) rfl) (Ns96p512 rfl) rfl)) 

noncomputable def Ns96p514 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz61) (hardyZApproximantRS₀ qz61) Bool.false 559611893399946563 1152921504606846976 91274716872929395263 50728546202701266944000 (@Eq.refl Real (hardyZApproximantRS₀ qz61)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz61) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz61) qz61 7) (@HMul.hMul Real Real Real qz5 qz660 (Zeta.RiemannSiegel.correction qz63))) Bool.false 559611893399946563 1152921504606846976 91274716872929395263 50728546202701266944000 (BSN.hardyZApproximantRS₀_eq qz61 7 (@BSN.floor_sqrt_eq_dec qz61 321404 1000 7 qz64 rfl rfl rfl)) (@Ns96p418 559611893399946563 1152921504606846976 91274716872929395263 50728546202701266944000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz61) qz61 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 7)) Bool.false 8470065 33554432 931 524288 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz61) qz61 7) (Ns96p474 (Ns96p473 rfl) rfl rfl)) (Ns96p513 rfl) rfl rfl)) 

theorem RS097to114.d42 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz61) Bool.false 559611893399946563 1152921504606846976 91274716872929395263 50728546202701266944000 := Ns96p514 

noncomputable def Ns96p515 := nat_lit 2232056032918855745536000 

noncomputable def Ns96p516 := nat_lit 4375384154867602824439529472 

noncomputable abbrev qz881 := (Enclosure.sfrac Bool.false 323000 1000)

noncomputable abbrev qz665 := qz881

noncomputable abbrev qz413 := qz665

noncomputable abbrev qz74 := qz413

noncomputable abbrev qz882 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 323000 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz666 := qz882

noncomputable abbrev qz414 := qz666

noncomputable abbrev qz75 := qz414

noncomputable abbrev qz883 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 323000 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz667 := qz883

noncomputable abbrev qz415 := qz667

noncomputable abbrev qz76 := qz415

noncomputable abbrev qz668 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz75 qz9))

noncomputable def Ns96p517 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz74) qz74 7) (@HMul.hMul Real Real Real qz5 qz668 (Zeta.RiemannSiegel.correction qz76)) 37127523 33554432 14969 8388608 32891963842705421421 147573952589676412928 62942323171320413063 Ns96p515 Ns96p516 

noncomputable def Ns96p518 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz74) qz74 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 323000 1000 66 98 67108864 33554432 1125899906842624 Bool.false 31835174634 1221 

noncomputable def Ns96p519 := Ns96p518 120242927 57 27397080 8 130587807 57 25364760 8 Bool.false 8904632 44421 Bool.true 45943220 Bool.true 14080034 3537118876014220 1 Bool.false 51987050 Bool.true Bool.false 65637216 Bool.true Bool.true 37127523 

noncomputable def Ns96p520 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz74) qz74 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 323000 1000 16 28 67108864 33554432 1125899906842624 Bool.false 31835174634 1221 

noncomputable def Ns96p521 := Ns96p520 93032624 56 33554424 8 108007536 56 30011992 8 Bool.false 3134614 26111 Bool.false 99007368 Bool.true 99657496 3537118876014220 1 Bool.false 6397260 Bool.false Bool.false 5749802 Bool.false Bool.false 8904632 

noncomputable def Ns96p522 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz74) qz74 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 323000 1000 159 76 67108864 33554432 1125899906842624 Bool.false 31835174634 1221 

noncomputable def Ns96p523 := Ns96p522 46516304 56 47453136 16 73726608 56 38745320 8 Bool.true 67108848 1280 Bool.false 49525668 Bool.false 9989112 3537118876014220 1 Bool.false 45150991 Bool.false Bool.false 66366799 Bool.false Bool.false 3134614 

noncomputable def Ns96p524 := nat_lit 13974229238117173139578755310095739487 

noncomputable def Ns96p525 := nat_lit 29457813886727285915239995219640320 

noncomputable def Ns96p526 := nat_lit 1687549363231994000000000000000000 

noncomputable def Ns96p527 := nat_lit 3270474323216730585000000000000000000 

noncomputable abbrev qz416 := (@Eq.refl Real qz665)

noncomputable abbrev qz77 := qz416

noncomputable def Ns96p528 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz74 323000 1000 417317000000 16000000 646000 4000 2000 Ns96p526 Ns96p527 qz77 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns96p529 := nat_lit 13974229238117173139578755310095739487000000000000000000 

noncomputable abbrev qz417 := (Enclosure.sfrac Bool.false 323000 2000)

noncomputable abbrev qz669 := (Real.log (Enclosure.sfrac Bool.false 417317000000 16000000))

noncomputable abbrev qz78 := (@HSub.hSub Real Real Real qz342 (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 323000 4000) qz669) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 646000)))))) qz417)

noncomputable abbrev qz418 := (@HSub.hSub Real Real Real qz12 qz78 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 323000 2000) (Real.log Real.pi)))

noncomputable def Ns96p530 := @Enclosure.Real.IsNear.addLit_ft_p qz418 (Enclosure.sfrac Bool.true Ns96p526 Ns96p527) 4272849457648679671 9007199254740992 450383729189667 24780800000000000000 Ns96p526 Ns96p527 0 1 Ns96p529 

noncomputable def Ns96p531 := nat_lit 286746073145819003820703744 

noncomputable abbrev qz419 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 323000 2000) (Real.log Real.pi))

noncomputable def Ns96p532 := @Enclosure.Real.IsNear.subLit_ff_p qz78 qz419 5938045295959915255 9007199254740992 1655000218889 193600000000000000 12406675803 67108864 323 33554432 Ns96p531 4272849457648679671 9007199254740992 

noncomputable abbrev qz79 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 323000 4000) qz669) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 646000))))))

noncomputable def Ns96p533 := @Enclosure.Real.IsNear.subLit_ff_p qz79 qz417 7392707975600585463 9007199254740992 1655000218889 193600000000000000 323000 2000 0 1 11876090591919830510000 5938045295959915255 9007199254740992 1655000218889 193600000000000000 

noncomputable def Ns96p534 := nat_lit 16646898442086845263138268406349824 

noncomputable def Ns96p535 := nat_lit 12293581975404260859314176 

noncomputable def Ns96p536 := nat_lit 218006696122628865083452787404071717337695439729002381335467395000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns96p537 := nat_lit 3913321445051367222630006641710147686843697880171109382121889000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns96p538 := nat_lit 7648801210601203173303566690509816882453254434751763305000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns96p539 := BSN.log_dyadic_bound 155173000000 679461000000 6 5 Ns96p536 33554432 9680000 Ns96p537 Ns96p538 15601205 834634000000 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 155173000000) (BSN.artanhQ 679461000000) 0 5 Ns96p537 Ns96p536 Ns96p538 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns96p540 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 323000 4000) qz669 323000 4000 0 1 22898580833159873 2251799813685248 6250000847 60500000000000000 7396241609110638979 9007199254740992 2018750273581 242000000000000000 (Enclosure.Real.IsNear.const Bool.false 323000 4000) (BSN.isNear_log_sfrac 417317000000 16000000 22898580833159873 2251799813685248 6250000847 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 417317000000) qz350)) Bool.false Ns96p535 Ns96p86 1000000135520000 9680000000000000000000 22898580833159873 2251799813685248 6250000847 60500000000000000 (BSN.log_rat_reduce_isNear 417317000000 16000000 14 834634000000 524288000000 15601205 33554432 24973259072661432 36028797018963968 9680000 1000000000000000 rfl rfl rfl rfl (Ns96p539 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p541 := BSN.arctan_dyadic_bound_f 1000 646000 1 0 4194304 1210000 0 1 1 0 1 1 6492 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 646000) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 646000) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz420 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 646000)))

noncomputable def Ns96p542 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz420 884279719003555 562949953421312 1 2000000000000000 6492 4194304 1 1210000 3705283291437875593216 883408377513379 562949953421312 200000000121 242000000000000000 qz17 (Ns96p541 rfl) rfl rfl 

noncomputable def Ns96p543 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 323000 4000) qz669) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz420)) 7396241609110638979 9007199254740992 2018750273581 242000000000000000 883408377513379 2251799813685248 200000000121 968000000000000000 Ns96p534 7392707975600585463 9007199254740992 1655000218889 193600000000000000 (Ns96p540 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz420) 1 4 0 1 883408377513379 562949953421312 200000000121 242000000000000000 883408377513379 2251799813685248 200000000121 968000000000000000 qz353 Ns96p542 rfl) 

noncomputable def Ns96p544 := @Ns96p530 Ns96p524 Ns96p525 450383729189667 24780800000000000000 (@Ns96p532 450383729189667 24780800000000000000 (Ns96p533 (Ns96p543 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 323000 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz417 (Real.log Real.pi) 323000 2000 0 1 38410761 33554432 1 16777216 12406675803 67108864 323 33554432 (Enclosure.Real.IsNear.const Bool.false 323000 2000) RS097to114.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns96p526 Ns96p527) 

noncomputable def Ns96p545 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz74) Bool.false Ns96p524 Ns96p525 450383729189667 24780800000000000000 3979396829 8388608 153 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz74) (@HAdd.hAdd Real Real Real qz354 qz418 (Enclosure.sfrac Bool.true Ns96p526 Ns96p527)) Bool.false Ns96p524 Ns96p525 450383729189667 24780800000000000000 Ns96p528 (Ns96p544 rfl rfl)) 

noncomputable def Ns96p546 := nat_lit 1899675157530534370869248 

noncomputable def Ns96p547 := nat_lit 140195514339122775635619528752497501212096352920595994293925696897870749381570584351585 

noncomputable def Ns96p548 := nat_lit 282095619790456359422183359970300168930819603731584866961606501315791498625467519841 

noncomputable def Ns96p549 := nat_lit 366722001789470340178034278435636779091507216385995514318534224206578776430148392555361 

noncomputable def Ns96p550 := BSN.sin_dyadic_bound_f 26996007669 17179869184 3 2 8388608 2422364 Ns96p547 Ns96p99 Ns96p548 Ns96p549 Ns96p102 Ns96p548 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26996007669) qz355 0 2 Ns96p547 Ns96p99 Ns96p548 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26996007669) qz356 0 2 Ns96p549 Ns96p102 Ns96p548 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p551 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz74) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3979396829) qz357) Bool.false 3979396829 8388608 153 8388608 Bool.true 8388606 8388608 1 1210000 (Ns96p545 rfl) (Enclosure.sfrac_false_div 3979396829 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3979396829) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns96p546) qz358) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 75 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q1 3979396829 8388608 226375608064910080 72057594037927936 75 Ns96p546 Ns96p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388606 8388608 Ns96p546 Ns96p86 26996007669 17179869184 2422364 2420000 (Ns96p550 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p552 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz74) Bool.false Ns96p524 Ns96p525 450383729189667 24780800000000000000 31835174634 67108864 1221 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz74) (@HAdd.hAdd Real Real Real qz354 qz418 (Enclosure.sfrac Bool.true Ns96p526 Ns96p527)) Bool.false Ns96p524 Ns96p525 450383729189667 24780800000000000000 Ns96p528 (Ns96p544 rfl rfl)) 

noncomputable def Ns96p553 := Ns96p523 26111 BSN.abs_quadSignPos (BSN.cos_quad_nat3 159 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 45150991 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 76 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66366799 67108864) qz77 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 1) Bool.true 4194303 4194304 12094913 634388480000 67108848 67108864 1280 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz74)) Bool.true 4194303 4194304 12094913 634388480000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz74) qz74) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz74)) Bool.true 8388606 8388608 193518608 10150215680000 4194303 4194304 12094913 634388480000 (Ns96p551 rfl rfl) rfl)) rfl) (Ns96p552 rfl) RS097to114.d7 

noncomputable def Ns96p554 := nat_lit 369033082840960294038387976502009380294254912042136910707791298560 

noncomputable def Ns96p555 := nat_lit 36194512868309504754078848228106548827091824698276284664446976 

noncomputable def Ns96p556 := nat_lit 966456616324537792807128572703369537786852335251323271202377629696 

noncomputable def Ns96p557 := BSN.sin_dyadic_bound_f 49525668 67108864 3 2 67108864 33554432 Ns96p554 Ns96p221 Ns96p555 Ns96p556 Ns96p224 Ns96p555 45150991 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 49525668) qz360 0 2 Ns96p554 Ns96p221 Ns96p555 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 49525668) (BSN.sinOddQ 67108864) 0 2 Ns96p556 Ns96p224 Ns96p555 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p558 := nat_lit 9956519077510191874404519936 

noncomputable def Ns96p559 := BSN.cos_dyadic_bound_f 9989112 67108864 2 1 67108864 33554432 Ns96p558 Ns96p131 Ns96p558 Ns96p558 Ns96p132 Ns96p558 66366799 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 9989112) qz359 0 1 Ns96p558 Ns96p131 Ns96p558 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 9989112) (BSN.cosOddQ 67108864) 0 1 Ns96p558 Ns96p132 Ns96p558 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p560 := nat_lit 791149091860576810889566826566292723528022299349837486624522737126218975204464163049849660142105133056 

noncomputable def Ns96p561 := nat_lit 887176818104798468451030373601146521137983394550804928657330094248260935869730624926792418328576 

noncomputable def Ns96p562 := nat_lit 4790635556857572588828931265871045624141661229367920021562958797108266000145560276950120464801249361920 

noncomputable def Ns96p563 := BSN.cos_dyadic_bound_f 99007368 67108864 4 3 67108864 33554432 Ns96p560 Ns96p236 Ns96p561 Ns96p562 Ns96p239 Ns96p561 6397260 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 99007368) qz359 0 3 Ns96p560 Ns96p236 Ns96p561 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 99007368) (BSN.cosOddQ 67108864) 0 3 Ns96p562 Ns96p239 Ns96p561 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p564 := nat_lit 812195492468656070463677676750190644697574721038653126011803727476705403566150367369933709670399082496 

noncomputable def Ns96p565 := nat_lit 959664987745592923055047826631595923618333104478395092743617422621854947733730876546288206217216 

noncomputable def Ns96p566 := nat_lit 4917833011475741918321830782888601537506187337687816414562338484352192848757926865904128145852307865600 

noncomputable def Ns96p567 := BSN.cos_dyadic_bound_f 99657496 67108864 4 3 67108864 33554432 Ns96p564 Ns96p236 Ns96p565 Ns96p566 Ns96p239 Ns96p565 5749802 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 99657496) qz359 0 3 Ns96p564 Ns96p236 Ns96p565 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 99657496) (BSN.cosOddQ 67108864) 0 3 Ns96p566 Ns96p239 Ns96p565 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p568 := Ns96p521 44421 BSN.abs_quadSignPos (BSN.cos_quad_nat0 16 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 6397260 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 28 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 5749802 67108864) qz77 rfl rfl (Ns96p553 RS097to114.d9 RS097to114.d11 RS097to114.d13 RS097to114.d17 (Ns96p557 rfl rfl) (Ns96p559 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns96p552 rfl) RS097to114.d19 RS097to114.d21 RS097to114.d23 RS097to114.d25 RS097to114.d17 (Ns96p563 rfl rfl) (Ns96p567 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns96p569 := nat_lit 151834804115217493140402358824327400451239401476329403199692800000 

noncomputable def Ns96p570 := nat_lit 19850499566558070297224329959773870319105948876546073600000000 

noncomputable def Ns96p571 := nat_lit 455464711346519363280612627813062653613079992531235117451878400000 

noncomputable def Ns96p572 := BSN.cos_dyadic_bound_f 45943220 67108864 3 2 67108864 33554432 Ns96p569 Ns96p108 Ns96p570 Ns96p571 Ns96p111 Ns96p570 51987050 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 45943220) qz359 0 2 Ns96p569 Ns96p108 Ns96p570 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 45943220) (BSN.cosOddQ 67108864) 0 2 Ns96p571 Ns96p111 Ns96p570 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p573 := nat_lit 39302014732401471244002616336 

noncomputable def Ns96p574 := BSN.cos_dyadic_bound_f 14080034 67108864 2 1 67108864 33554432 Ns96p573 Ns96p131 Ns96p573 Ns96p573 Ns96p132 Ns96p573 65637216 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 14080034) qz359 0 1 Ns96p573 Ns96p131 Ns96p573 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 14080034) (BSN.cosOddQ 67108864) 0 1 Ns96p573 Ns96p132 Ns96p573 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p575 := Ns96p519 59876 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 66 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 51987050 67108864) BSN.abs_quadSignNeg qz636 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 65637216 67108864) qz77 rfl rfl (Ns96p568 rfl rfl) (Ns96p552 rfl) RS097to114.d27 RS097to114.d29 RS097to114.d31 RS097to114.d33 RS097to114.d17 (Ns96p572 rfl rfl) (Ns96p574 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns96p576 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 7) 37127523 67108864 59876 67108864 37127523 67108864 59876 67108864 4983171783327744 37127523 33554432 14969 8388608 (Ns96p575 rfl) 

noncomputable def Ns96p577 := @Enclosure.Real.IsNear.mulLit_tf qz668 (Zeta.RiemannSiegel.correction qz76) 3132811 8388608 1 8388608 10499185505511 17592186044416 20040628990999 266081813921792000 32891963842705421421 147573952589676412928 

noncomputable abbrev qz670 := (@HPow.hPow Real Real Real qz7 qz75 qz9)

noncomputable def Ns96p578 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz670 1 1 0 1 3132811 8388608 1 8388608 3132811 8388608 1 8388608 

noncomputable def Ns96p579 := @Enclosure.Real.IsNear.sqrt_image qz75 431233747 8388608 323 8388608 30072612 30072636 4194304 (@Enclosure.Real.IsNear.of_eq qz75 (@HMul.hMul Real Real Real qz5 qz74 qz3) Bool.false 431233747 8388608 323 8388608 (BSN.t_div_two_pi_mk qz74 323000 1000 qz77) (@Enclosure.Real.IsNear.mulLit_ff qz74 qz3 323000 1000 0 1 1335089 8388608 1 8388608 431233747 8388608 323 8388608 (Enclosure.Real.IsNear.const Bool.false 323000 1000) RS097to114.d36 rfl)) 

noncomputable abbrev qz884 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 323000 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz671 := qz884

noncomputable abbrev qz421 := qz671

noncomputable abbrev qz80 := qz421

noncomputable def Ns96p580 := @Enclosure.Real.IsNear.sqrt_image qz80 1879539 262144 3 1048576 11230925 11230930 4194304 (@Enclosure.Real.IsNear.recentre' qz80 Bool.false 60145248 8388608 24 8388608 1879539 262144 3 1048576 (Ns96p579 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns96p581 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz80) 22461855 8388608 5 8388608 1566405 1566406 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz80) Bool.false 22461855 8388608 5 8388608 22461855 8388608 5 8388608 (Ns96p580 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns96p582 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz80)) Bool.false 3132811 8388608 1 8388608 3132811 8388608 1 8388608 (Ns96p581 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz81 := (@HMul.hMul Real Real Real qz339 qz337 qz415)

noncomputable abbrev qz672 := (@HMul.hMul Real Real Real qz863 qz883 qz883)

noncomputable abbrev qz422 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz672 qz667) qz641)

noncomputable abbrev qz82 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz422))

noncomputable def Ns96p583 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz76) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz81)) qz82) Bool.false 10499185505511 

noncomputable def Ns96p584 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz81)) qz82 17387277 8388608 683 

noncomputable def Ns96p585 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz81)) Bool.false 17387277 8388608 683 8388608 17387277 8388608 683 

noncomputable def Ns96p586 := @Enclosure.Real.IsNear.recentre' (Real.cos qz81) Bool.false 2023570 4194304 24038576 1268776960000 1011785 2097152 1502411 79298560000 

noncomputable abbrev qz423 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable def Ns96p587 := @Enclosure.Real.IsNear.cos_image qz81 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 559593) qz423) Bool.false 559593 524288 19 1048576 Bool.false 2023570 4194304 1 

noncomputable def Ns96p588 := nat_lit 80958226228662209874772309 

noncomputable def Ns96p589 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz76 884279719003555 140737488355328 1 500000000000000 44531 262144 3 1048576 39377860166947307705 36893488147419103232 Ns96p588 

noncomputable def Ns96p590 := @Enclosure.Real.IsNear.subLit_ff_p qz80 qz1 1879539 262144 3 1048576 7 1 0 1 44531 44531 262144 3 

noncomputable def Ns96p591 := @Ns96p590 1048576 (@Enclosure.Real.IsNear.recentre' qz80 Bool.false 60145248 8388608 24 8388608 1879539 262144 3 1048576 (Ns96p579 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns96p592 := @Enclosure.Real.IsNear.recentre' qz81 Bool.false 39377860166947307705 36893488147419103232 Ns96p588 Ns96p487 559593 524288 19 1048576 (@Ns96p589 Ns96p487 RS097to114.d35 (Ns96p591 rfl rfl) rfl) 

noncomputable def Ns96p593 := nat_lit 12456998419067966497031750076521034893037799906881 

noncomputable def Ns96p594 := nat_lit 230186507879617209617080361152814575595809375518720 

noncomputable def Ns96p595 := nat_lit 9615639787129621208056517317422011969067982401 

noncomputable def Ns96p596 := nat_lit 37351763977629640248679137194928260655175263755841 

noncomputable def Ns96p597 := nat_lit 10358392854582774432768616251876655901811421898342400 

noncomputable def Ns96p598 := BSN.cos_dyadic_bound_f 559593 524288 3 2 4194304 1210000 Ns96p593 Ns96p594 Ns96p595 Ns96p596 Ns96p597 Ns96p595 2023570 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 559593) (BSN.cosEvenQ 524288) 0 2 Ns96p593 Ns96p594 Ns96p595 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 559593) (BSN.cosOddQ 524288) 0 2 Ns96p596 Ns96p597 Ns96p595 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p599 := @Enclosure.Real.IsNear.inv_image (Real.cos qz81) 1011785 2097152 1502411 79298560000 8693297 8693980 4194304 (Ns96p586 (@Ns96p587 1210000 (Ns96p592 rfl) (Enclosure.sfrac_false_div 559593 524288) (Ns96p598 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns96p600 := @Enclosure.Real.IsNear.recentre' qz82 Bool.false 1207686 4194304 

noncomputable abbrev qz83 := (@HMul.hMul Real Real Real qz339 qz337 qz422)

noncomputable def Ns96p601 := @Enclosure.Real.IsNear.cos_image qz83 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 10726737)) qz357) Bool.true 10726737 8388608 

noncomputable def Ns96p602 := nat_lit 12367086758146242904345445 

noncomputable def Ns96p603 := nat_lit 9671406556917033397649408 

noncomputable def Ns96p604 := nat_lit 22746460415581101818118352357451 

noncomputable def Ns96p605 := @Enclosure.Real.IsNear.recentre' qz83 Bool.true Ns96p602 Ns96p603 Ns96p604 

noncomputable def Ns96p606 := nat_lit 944473296573929042739200000000000000 

noncomputable abbrev qz84 := qz422

noncomputable def Ns96p607 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz84 884279719003555 140737488355328 1 500000000000000 13985491799 

noncomputable abbrev qz424 := (@HSub.hSub Real Real Real qz635 qz672 qz667)

noncomputable abbrev qz85 := qz424

noncomputable def Ns96p608 := @Enclosure.Real.IsNear.subLit_tf qz85 qz26 9690524503 68719476736 4214481 1099511627776 1 16 

noncomputable abbrev qz425 := qz672

noncomputable abbrev qz86 := qz425

noncomputable def Ns96p609 := @Enclosure.Real.IsNear.subLit_ff_n qz86 qz76 1983009961 68719476736 1068753 1099511627776 44531 262144 3 1048576 

noncomputable def Ns96p610 := @Enclosure.Real.IsNear.mulLit_ff qz76 qz76 44531 262144 3 1048576 44531 262144 3 1048576 1983009961 68719476736 

noncomputable def Ns96p611 := nat_lit 110313848421923440861586189308162459427523593332609789404801 

noncomputable def Ns96p612 := nat_lit 175283509962196458590866225820671641395817322742212142721 

noncomputable def Ns96p613 := nat_lit 330590978245845929667576835472846034999779145352344943928961 

noncomputable def Ns96p614 := BSN.cos_dyadic_bound_f 10726737 8388608 3 2 4194304 1210000 Ns96p611 Ns96p262 Ns96p612 Ns96p613 Ns96p265 Ns96p612 1207686 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 10726737) (BSN.cosEvenQ 8388608) 0 2 Ns96p611 Ns96p262 Ns96p612 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 10726737) (BSN.cosOddQ 8388608) 0 2 Ns96p613 Ns96p265 Ns96p612 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p615 := @Ns96p600 254018608 10150215680000 603843 2097152 15876163 634388480000 (@Ns96p601 203 8388608 Bool.false 1207686 4194304 1 1210000 (@Ns96p605 Ns96p606 10726737 8388608 203 8388608 (@Ns96p607 68719476736 4214481 1099511627776 Ns96p602 Ns96p603 Ns96p604 Ns96p606 RS097to114.d35 (@Ns96p608 0 1 223767868784 13985491799 68719476736 4214481 1099511627776 (@Ns96p609 2540312855314432 9690524503 68719476736 4214481 1099511627776 (@Ns96p610 1068753 1099511627776 (Ns96p591 rfl rfl) (Ns96p591 rfl rfl) rfl) (Ns96p591 rfl rfl) rfl rfl) qz369 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 10726737 8388608) (BSN.cos_neg_of_bound 10726737 8388608 Bool.false 1207686 4194304 1 1210000 (Ns96p614 rfl rfl)) rfl rfl) 

noncomputable def Ns96p616 := @Ns96p577 62942323171320413063 Ns96p515 (Ns96p578 qz28 (@Enclosure.Real.IsNear.of_eq qz670 (@Inv.inv Real Real.instInv (Real.sqrt qz80)) Bool.false 3132811 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz75 (BSN.t_div_two_pi_nonneg qz74 323000 1000 qz77)) Ns96p582) rfl) (@Ns96p583 17592186044416 20040628990999 266081813921792000 (BSN.correction_mk qz76 (BSN.cos_two_pi_p_ne_zero_mk qz74 323000 1000 7 qz77 rfl rfl (@BSN.floor_sqrt_eq_dec qz74 323000 1000 7 qz77 rfl rfl rfl))) (@Ns96p584 8388608 603843 2097152 15876163 634388480000 10499185505511 17592186044416 20040628990999 266081813921792000 (@Ns96p585 8388608 (Ns96p599 rfl rfl rfl rfl rfl) rfl) (Ns96p615 rfl) rfl)) 

noncomputable def Ns96p617 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz74) (hardyZApproximantRS₀ qz74) Bool.true 130396609153378093971 147573952589676412928 4045920995766624861063 Ns96p515 (@Eq.refl Real (hardyZApproximantRS₀ qz74)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz74) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz74) qz74 7) (@HMul.hMul Real Real Real qz5 qz668 (Zeta.RiemannSiegel.correction qz76))) Bool.true 130396609153378093971 147573952589676412928 4045920995766624861063 Ns96p515 (BSN.hardyZApproximantRS₀_eq qz74 7 (@BSN.floor_sqrt_eq_dec qz74 323000 1000 7 qz77 rfl rfl rfl)) (@Ns96p517 130396609153378093971 147573952589676412928 4045920995766624861063 Ns96p515 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz74) qz74 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 7)) Bool.true 37127523 33554432 14969 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz74) qz74 7) (Ns96p576 (Ns96p575 rfl) rfl rfl)) (Ns96p616 rfl) rfl rfl)) 

theorem RS097to114.d43 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz74) Bool.true 130396609153378093971 147573952589676412928 4045920995766624861063 Ns96p515 := Ns96p617 

noncomputable def Ns96p618 := nat_lit 1320069955989125715168591872 

noncomputable abbrev qz885 := (Enclosure.sfrac Bool.false 324594 1000)

noncomputable abbrev qz673 := qz885

noncomputable abbrev qz426 := qz673

noncomputable abbrev qz87 := qz426

noncomputable abbrev qz886 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 324594 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz674 := qz886

noncomputable abbrev qz427 := qz674

noncomputable abbrev qz88 := qz427

noncomputable abbrev qz887 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 324594 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz675 := qz887

noncomputable abbrev qz428 := qz675

noncomputable abbrev qz89 := qz428

noncomputable abbrev qz676 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz88 qz9))

noncomputable def Ns96p619 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz87) qz87 7) (@HMul.hMul Real Real Real qz5 qz676 (Zeta.RiemannSiegel.correction qz89)) 28615471 33554432 15045 8388608 7878107303911764675 36893488147419103232 19125174964549354353 558014008229713936384000 Ns96p618 

noncomputable def Ns96p620 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz87) qz87 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 324594 1000 66 98 67108864 33554432 1125899906842624 Bool.false 32046028278 1227 

noncomputable def Ns96p621 := Ns96p620 120242927 57 27397080 8 130587807 57 25364760 8 Bool.false 78864350 44649 Bool.true 26756802 Bool.true 11383354 3537118876014220 1 Bool.false 61845084 Bool.true Bool.false 66145724 Bool.true Bool.false 28615471 

noncomputable def Ns96p622 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz87) qz87 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 324594 1000 17 28 67108864 33554432 1125899906842624 Bool.false 32046028278 1227 

noncomputable def Ns96p623 := Ns96p622 93032624 56 33554424 8 108007536 56 30011992 8 Bool.false 85321827 26249 Bool.false 56152653 Bool.true 60967864 3537118876014220 1 Bool.false 49825852 Bool.true Bool.false 41267632 Bool.false Bool.false 78864350 

noncomputable def Ns96p624 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz87) qz87 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 324594 1000 160 76 67108864 33554432 1125899906842624 Bool.false 32046028278 1227 

noncomputable def Ns96p625 := Ns96p624 46516304 56 47453136 16 73726608 56 38745320 8 Bool.false 67108824 1296 Bool.false 80817966 Bool.false 103322543 3537118876014220 1 Bool.false 24049393 Bool.false Bool.false 2091475 Bool.false Bool.false 85321827 

noncomputable def Ns96p626 := nat_lit 39302496987811863808414422165474976223906731488668309 

noncomputable def Ns96p627 := nat_lit 82304924100349461093902128530435817836258525184000 

noncomputable def Ns96p628 := nat_lit 1729602430500930453994080107520000 

noncomputable def Ns96p629 := nat_lit 3368515157959087218137570547578081280 

noncomputable abbrev qz429 := (@Eq.refl Real qz673)

noncomputable abbrev qz90 := qz429

noncomputable def Ns96p630 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz87 324594 1000 421446059344 16000000 649188 4000 2000 Ns96p628 Ns96p629 qz90 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns96p631 := nat_lit 7244236244793482737166946293540347617590488747991342714880 

noncomputable abbrev qz430 := (Enclosure.sfrac Bool.false 324594 2000)

noncomputable abbrev qz677 := (Real.log (Enclosure.sfrac Bool.false 421446059344 16000000))

noncomputable abbrev qz91 := (@HSub.hSub Real Real Real qz342 (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 324594 4000) qz677) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 649188)))))) qz430)

noncomputable abbrev qz431 := (@HSub.hSub Real Real Real qz12 qz91 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 324594 2000) (Real.log Real.pi)))

noncomputable def Ns96p632 := @Enclosure.Real.IsNear.addLit_ft_p qz431 (Enclosure.sfrac Bool.true Ns96p628 Ns96p629) 2150574865935731746121 4503599627370496000 1131452747001438333 61952000000000000000000 Ns96p628 Ns96p629 0 1 Ns96p631 

noncomputable def Ns96p633 := nat_lit 72161318099949627245458358272000 

noncomputable abbrev qz432 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 324594 2000) (Real.log Real.pi))

noncomputable def Ns96p634 := @Enclosure.Real.IsNear.subLit_ff_p qz91 qz432 2987281642933869831497 4503599627370496000 259839096870171 30250000000000000000 6233951278017 33554432000 162297 16777216000 Ns96p633 2150574865935731746121 4503599627370496000 

noncomputable def Ns96p635 := nat_lit 5974563285867739662994000 

noncomputable abbrev qz92 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 324594 4000) qz677) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 649188))))))

noncomputable def Ns96p636 := @Enclosure.Real.IsNear.subLit_ff_p qz92 qz430 3718202351657219220809 4503599627370496000 259839096870171 30250000000000000000 324594 2000 0 1 Ns96p635 2987281642933869831497 4503599627370496000 259839096870171 30250000000000000000 

noncomputable def Ns96p637 := nat_lit 8372647362705777206586118065337925632 

noncomputable def Ns96p638 := nat_lit 12305484664960227909566464 

noncomputable def Ns96p639 := nat_lit 231623105536553494181775867575533142787453626580173309450995309739220592725478764512529042505332208995623660525972902379520 

noncomputable def Ns96p640 := nat_lit 4335028514450423923103809499887051758044659929623647259865220435617437711072251131442168606942215367390023978980374216704 

noncomputable def Ns96p641 := nat_lit 9945937124021628985378176938020290539709157335160412236427087420622447253045920501451132811759362579289627500216320 

noncomputable def Ns96p642 := BSN.log_dyadic_bound 159302059344 683590059344 6 5 Ns96p639 33554432 9680000 Ns96p640 Ns96p641 15931571 842892118688 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 159302059344) (BSN.artanhQ 683590059344) 0 5 Ns96p640 Ns96p639 Ns96p641 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns96p643 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 324594 4000) qz677 324594 4000 0 1 22920751320124097 2251799813685248 6250000847 60500000000000000 3719969177002180570809 4503599627370496000 1014356387465559 121000000000000000000 (Enclosure.Real.IsNear.const Bool.false 324594 4000) (BSN.isNear_log_sfrac 421446059344 16000000 22920751320124097 2251799813685248 6250000847 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 421446059344) qz350)) Bool.false Ns96p638 Ns96p86 1000000135520000 9680000000000000000000 22920751320124097 2251799813685248 6250000847 60500000000000000 (BSN.log_rat_reduce_isNear 421446059344 16000000 14 842892118688 524288000000 15931571 33554432 24973259072661432 36028797018963968 9680000 1000000000000000 rfl rfl rfl rfl (Ns96p642 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p644 := BSN.arctan_dyadic_bound_f 1000 649188 1 0 4194304 1210000 0 1 1 0 1 1 6460 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 649188) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 649188) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz433 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 649188)))

noncomputable def Ns96p645 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz433 884279719003555 562949953421312 1 2000000000000000 6460 4194304 1 1210000 3705301305836385075200 883412672480675 562949953421312 200000000121 242000000000000000 qz17 (Ns96p644 rfl) rfl rfl 

noncomputable def Ns96p646 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 324594 4000) qz677) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz433)) 3719969177002180570809 4503599627370496000 1014356387465559 121000000000000000000 883412672480675 2251799813685248 200000000121 968000000000000000 Ns96p637 3718202351657219220809 4503599627370496000 259839096870171 30250000000000000000 (Ns96p643 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz433) 1 4 0 1 883412672480675 562949953421312 200000000121 242000000000000000 883412672480675 2251799813685248 200000000121 968000000000000000 qz353 Ns96p645 rfl) 

noncomputable def Ns96p647 := @Ns96p632 Ns96p626 Ns96p627 1131452747001438333 61952000000000000000000 (@Ns96p634 1131452747001438333 61952000000000000000000 (Ns96p636 (Ns96p646 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 324594 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz430 (Real.log Real.pi) 324594 2000 0 1 38410761 33554432 1 16777216 6233951278017 33554432000 162297 16777216000 (Enclosure.Real.IsNear.const Bool.false 324594 2000) RS097to114.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns96p628 Ns96p629) 

noncomputable def Ns96p648 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz87) Bool.false Ns96p626 Ns96p627 1131452747001438333 61952000000000000000000 2002876767 4194304 155 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz87) (@HAdd.hAdd Real Real Real qz354 qz431 (Enclosure.sfrac Bool.true Ns96p628 Ns96p629)) Bool.false Ns96p626 Ns96p627 1131452747001438333 61952000000000000000000 Ns96p630 (Ns96p647 rfl rfl)) 

noncomputable def Ns96p649 := nat_lit 140328379954283964812950989379486522209544538014667362106444996277463021489919242485025 

noncomputable def Ns96p650 := nat_lit 282629490800087617845396577190625920656478710352145500432288061434082872343902764321 

noncomputable def Ns96p651 := nat_lit 367069118799924527890740996773679878105839491174034855659037000055795588775517411556641 

noncomputable def Ns96p652 := BSN.sin_dyadic_bound_f 27002388691 17179869184 3 2 8388608 2422364 Ns96p649 Ns96p99 Ns96p650 Ns96p651 Ns96p102 Ns96p650 8388603 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 27002388691) qz355 0 2 Ns96p649 Ns96p99 Ns96p650 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 27002388691) qz356 0 2 Ns96p651 Ns96p102 Ns96p650 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz434 := (@Nat.cast Real Real.instNatCast 4194304)

noncomputable abbrev qz678 := (@Nat.cast Real Real.instNatCast 604462909807314587353088)

noncomputable def Ns96p653 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz87) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2002876767) qz434) Bool.false 2002876767 4194304 155 8388608 Bool.false 8388603 8388608 1 1210000 (Ns96p648 rfl) (Enclosure.sfrac_false_div 2002876767 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2002876767) qz434) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 950062091014523389476864) qz678) 226375608064910080 72057594037927936 Bool.false 8388603 8388608 75 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q3 2002876767 4194304 226375608064910080 72057594037927936 75 950062091014523389476864 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388603 8388608 950062091014523389476864 604462909807314587353088 27002388691 17179869184 2422364 2420000 (Ns96p652 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p654 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz87) Bool.false Ns96p626 Ns96p627 1131452747001438333 61952000000000000000000 32046028278 67108864 1227 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz87) (@HAdd.hAdd Real Real Real qz354 qz431 (Enclosure.sfrac Bool.true Ns96p628 Ns96p629)) Bool.false Ns96p626 Ns96p627 1131452747001438333 61952000000000000000000 Ns96p630 (Ns96p647 rfl rfl)) 

noncomputable def Ns96p655 := Ns96p625 26249 BSN.abs_quadSignPos (BSN.cos_quad_nat0 160 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 24049393 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 76 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 2091475 67108864) qz90 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 1) Bool.false 8388603 8388608 12246163 634388480000 67108824 67108864 1296 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz87)) Bool.false 8388603 8388608 12246163 634388480000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz87) qz87) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz87)) Bool.false 8388603 8388608 195938608 10150215680000 8388603 8388608 12246163 634388480000 (Ns96p653 rfl rfl) rfl)) rfl) (Ns96p654 rfl) RS097to114.d7 

noncomputable def Ns96p656 := nat_lit 350703399439444507904106386242021988022091217378931673845766769995466959981459628268011919219778523136 

noncomputable def Ns96p657 := nat_lit 77641692288879569264184877226743735226729121351817794971296730605601807367143412144899955757056 

noncomputable def Ns96p658 := nat_lit 2125826619621425193359680844746964105548798512160347507692841512559790094553473131981560779169273876480 

noncomputable def Ns96p659 := BSN.cos_dyadic_bound_f 80817966 67108864 4 3 67108864 33554432 Ns96p656 Ns96p236 Ns96p657 Ns96p658 Ns96p239 Ns96p657 24049393 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 80817966) qz359 0 3 Ns96p656 Ns96p236 Ns96p657 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 80817966) (BSN.cosOddQ 67108864) 0 3 Ns96p658 Ns96p239 Ns96p657 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p660 := nat_lit 938849531061616988806703373574451499934931297858168023343657763601824731965515615669778346970125714881 

noncomputable def Ns96p661 := nat_lit 1480270346249193897908746877448665024394109278104523410393099682013645740537262087548123703166401 

noncomputable def Ns96p662 := nat_lit 5683021932966059936806878352664317280279888943304965657274051552710649443835687599146708780562468586945 

noncomputable def Ns96p663 := BSN.cos_dyadic_bound_f 103322543 67108864 4 3 67108864 33554432 Ns96p660 Ns96p236 Ns96p661 Ns96p662 Ns96p239 Ns96p661 2091475 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 103322543) qz359 0 3 Ns96p660 Ns96p236 Ns96p661 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 103322543) (BSN.cosOddQ 67108864) 0 3 Ns96p662 Ns96p239 Ns96p661 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p664 := nat_lit 609891875674211600678416365358209199920725390894042059932594104865 

noncomputable def Ns96p665 := nat_lit 98846714531131643999090113439678783926645729509371328644540961 

noncomputable def Ns96p666 := nat_lit 1597175827323218074353187191944978900808875740208047365291369589281 

noncomputable def Ns96p667 := BSN.sin_dyadic_bound_f 56152653 67108864 3 2 67108864 33554432 Ns96p664 Ns96p221 Ns96p665 Ns96p666 Ns96p224 Ns96p665 49825852 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 56152653) qz360 0 2 Ns96p664 Ns96p221 Ns96p665 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 56152653) (BSN.sinOddQ 67108864) 0 2 Ns96p666 Ns96p224 Ns96p665 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p668 := nat_lit 470986885502275943375985947171482678921432783638438506627476750336 

noncomputable def Ns96p669 := nat_lit 190900839733390670199932506183220292448729424651361132275040256 

noncomputable def Ns96p670 := nat_lit 1412578854827361048787557976502081596179400892066012797617880170496 

noncomputable def Ns96p671 := BSN.cos_dyadic_bound_f 60967864 67108864 3 2 67108864 33554432 Ns96p668 Ns96p108 Ns96p669 Ns96p670 Ns96p111 Ns96p669 41267632 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 60967864) qz359 0 2 Ns96p668 Ns96p108 Ns96p669 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 60967864) (BSN.cosOddQ 67108864) 0 2 Ns96p670 Ns96p111 Ns96p669 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p672 := Ns96p623 44649 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 17 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 49825852 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 28 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 41267632 67108864) qz90 rfl rfl (Ns96p655 RS097to114.d9 RS097to114.d11 RS097to114.d13 RS097to114.d17 (Ns96p659 rfl rfl) (Ns96p663 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns96p654 rfl) RS097to114.d19 RS097to114.d21 RS097to114.d23 RS097to114.d25 RS097to114.d17 (Ns96p667 rfl rfl) (Ns96p671 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns96p673 := nat_lit 17465144491048519860151506532266307526086389793495632500579041536 

noncomputable def Ns96p674 := nat_lit 262708206219072025035603277633792974639841333452174005043456 

noncomputable def Ns96p675 := nat_lit 52394908056733121436404448390243654992309889697819993153727037696 

noncomputable def Ns96p676 := BSN.cos_dyadic_bound_f 26756802 67108864 3 2 67108864 33554432 Ns96p673 Ns96p108 Ns96p674 Ns96p675 Ns96p111 Ns96p674 61845084 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 26756802) qz359 0 2 Ns96p673 Ns96p108 Ns96p674 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 26756802) (BSN.cosOddQ 67108864) 0 2 Ns96p675 Ns96p111 Ns96p674 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p677 := nat_lit 16791170327219071460439747856 

noncomputable def Ns96p678 := BSN.cos_dyadic_bound_f 11383354 67108864 2 1 67108864 33554432 Ns96p677 Ns96p131 Ns96p677 Ns96p677 Ns96p132 Ns96p677 66145724 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 11383354) qz359 0 1 Ns96p677 Ns96p131 Ns96p677 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 11383354) (BSN.cosOddQ 67108864) 0 1 Ns96p677 Ns96p132 Ns96p677 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p679 := Ns96p621 60180 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 66 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 61845084 67108864) BSN.abs_quadSignNeg qz636 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66145724 67108864) qz90 rfl rfl (Ns96p672 rfl rfl) (Ns96p654 rfl) RS097to114.d27 RS097to114.d29 RS097to114.d31 RS097to114.d33 RS097to114.d17 (Ns96p676 rfl rfl) (Ns96p678 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns96p680 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 7) 28615471 67108864 60180 67108864 28615471 67108864 60180 67108864 3840703503269888 28615471 33554432 15045 8388608 (Ns96p679 rfl) 

noncomputable def Ns96p681 := @Enclosure.Real.IsNear.mulLit_tf qz676 (Zeta.RiemannSiegel.correction qz89) 1564479 4194304 1 4194304 5035610771325 8796093022208 243518758330347 2660818139217920000 7878107303911764675 36893488147419103232 

noncomputable abbrev qz679 := (@HPow.hPow Real Real Real qz7 qz88 qz9)

noncomputable def Ns96p682 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz679 1 1 0 1 1564479 4194304 1 4194304 1564479 4194304 1 4194304 

noncomputable def Ns96p683 := @Enclosure.Real.IsNear.sqrt_image qz88 216680939433 4194304000 162297 4194304000 30146725 30146748 4194304 (@Enclosure.Real.IsNear.of_eq qz88 (@HMul.hMul Real Real Real qz5 qz87 qz3) Bool.false 216680939433 4194304000 162297 4194304000 (BSN.t_div_two_pi_mk qz87 324594 1000 qz90) (@Enclosure.Real.IsNear.mulLit_ff qz87 qz3 324594 1000 0 1 1335089 8388608 1 8388608 216680939433 4194304000 162297 4194304000 (Enclosure.Real.IsNear.const Bool.false 324594 1000) RS097to114.d36 rfl)) 

noncomputable abbrev qz888 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 324594 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz680 := qz888

noncomputable abbrev qz435 := qz680

noncomputable abbrev qz93 := qz435

noncomputable def Ns96p684 := @Enclosure.Real.IsNear.sqrt_image qz93 60293473 8388608 23 8388608 11244755 11244760 4194304 (@Enclosure.Real.IsNear.recentre' qz93 Bool.false 60293473 8388608 23 8388608 60293473 8388608 23 8388608 (Ns96p683 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns96p685 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz93) 22489515 8388608 5 8388608 1564478 1564480 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz93) Bool.false 22489515 8388608 5 8388608 22489515 8388608 5 8388608 (Ns96p684 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns96p686 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz93)) Bool.false 3128958 8388608 2 8388608 1564479 4194304 1 4194304 (Ns96p685 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz94 := (@HMul.hMul Real Real Real qz339 qz337 qz428)

noncomputable abbrev qz681 := (@HMul.hMul Real Real Real qz863 qz887 qz887)

noncomputable abbrev qz436 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz681 qz675) qz641)

noncomputable abbrev qz95 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz436))

noncomputable def Ns96p687 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz89) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz94)) qz95) Bool.false 5035610771325 

noncomputable def Ns96p688 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz94)) qz95 21934491 8388608 1047 

noncomputable def Ns96p689 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz94)) Bool.false 21934491 8388608 1047 8388608 21934491 8388608 1047 

noncomputable def Ns96p690 := @Enclosure.Real.IsNear.recentre' (Real.cos qz94) Bool.false 1604066 4194304 92524304 5075107840000 802033 2097152 5782769 317194240000 

noncomputable def Ns96p691 := @Enclosure.Real.IsNear.cos_image qz94 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9884813) qz357) Bool.false 9884813 8388608 73 4194304 Bool.false 1604066 4194304 1 

noncomputable def Ns96p692 := nat_lit 124135946884305375319581741 

noncomputable def Ns96p693 := nat_lit 7205759403792793600000000000000 

noncomputable def Ns96p694 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz89 884279719003555 140737488355328 1 500000000000000 1573217 8388608 23 8388608 1391163886691615786435 1180591620717411303424 Ns96p692 

noncomputable def Ns96p695 := @Enclosure.Real.IsNear.subLit_ff_p qz93 qz1 60293473 8388608 23 8388608 7 1 0 1 1573217 1573217 8388608 23 

noncomputable def Ns96p696 := @Ns96p695 8388608 (@Enclosure.Real.IsNear.recentre' qz93 Bool.false 60293473 8388608 23 8388608 60293473 8388608 23 8388608 (Ns96p683 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns96p697 := @Enclosure.Real.IsNear.recentre' qz94 Bool.false 1391163886691615786435 1180591620717411303424 Ns96p692 Ns96p693 9884813 8388608 73 4194304 (@Ns96p694 Ns96p693 RS097to114.d35 (Ns96p696 rfl rfl) rfl) 

noncomputable def Ns96p698 := nat_lit 79513494605249890158601789233058837088656375056223493997601 

noncomputable def Ns96p699 := nat_lit 91148108843558252904014503941740821006958483296196543521 

noncomputable def Ns96p700 := nat_lit 238358187598062553969997338691293029623955208202078088905761 

noncomputable def Ns96p701 := BSN.cos_dyadic_bound_f 9884813 8388608 3 2 4194304 1210000 Ns96p698 Ns96p262 Ns96p699 Ns96p700 Ns96p265 Ns96p699 1604066 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 9884813) (BSN.cosEvenQ 8388608) 0 2 Ns96p698 Ns96p262 Ns96p699 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 9884813) (BSN.cosOddQ 8388608) 0 2 Ns96p700 Ns96p265 Ns96p699 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p702 := @Enclosure.Real.IsNear.inv_image (Real.cos qz94) 802033 2097152 5782769 317194240000 10966722 10967769 4194304 (Ns96p690 (@Ns96p691 1210000 (Ns96p697 rfl) (Enclosure.sfrac_false_div 9884813 8388608) (Ns96p701 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns96p703 := @Enclosure.Real.IsNear.recentre' qz95 Bool.false 918300 4194304 

noncomputable abbrev qz96 := (@HMul.hMul Real Real Real qz339 qz337 qz436)

noncomputable def Ns96p704 := @Enclosure.Real.IsNear.cos_image qz96 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 5662597)) qz434) Bool.true 5662597 4194304 

noncomputable def Ns96p705 := nat_lit 13370429165886668561449995805 

noncomputable def Ns96p706 := nat_lit 7159581080709047975246774969193657 

noncomputable def Ns96p707 := @Enclosure.Real.IsNear.recentre' qz96 Bool.true Ns96p705 Ns96p163 Ns96p706 

noncomputable abbrev qz97 := qz436

noncomputable def Ns96p708 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz97 884279719003555 140737488355328 1 500000000000000 15120135493951 

noncomputable abbrev qz437 := (@HSub.hSub Real Real Real qz635 qz681 qz675)

noncomputable abbrev qz98 := qz437

noncomputable def Ns96p709 := @Enclosure.Real.IsNear.subLit_tf qz98 qz26 10722088982847 70368744177664 265306495 70368744177664 1 16 

noncomputable abbrev qz438 := qz681

noncomputable abbrev qz99 := qz438

noncomputable def Ns96p710 := @Enclosure.Real.IsNear.subLit_ff_n qz99 qz89 2475011729089 70368744177664 72368511 70368744177664 1573217 8388608 23 8388608 

noncomputable def Ns96p711 := @Enclosure.Real.IsNear.mulLit_ff qz89 qz89 1573217 8388608 23 8388608 1573217 8388608 23 8388608 2475011729089 70368744177664 

noncomputable def Ns96p712 := nat_lit 535635659490166293907710015601561661320091645629033513441 

noncomputable def Ns96p713 := nat_lit 3861888762982039923063034508418779142719222587902677483520 

noncomputable def Ns96p714 := nat_lit 1057122304501218921916704101150505846622484371488276961 

noncomputable def Ns96p715 := nat_lit 1604792733861496443879296638602383972267029968144123986401 

noncomputable def Ns96p716 := nat_lit 173784994334191796537836552878845061422365016455620486758400 

noncomputable def Ns96p717 := BSN.cos_dyadic_bound_f 5662597 4194304 3 2 4194304 1210000 Ns96p712 Ns96p713 Ns96p714 Ns96p715 Ns96p716 Ns96p714 918300 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 5662597) (BSN.cosEvenQ 4194304) 0 2 Ns96p712 Ns96p713 Ns96p714 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 5662597) (BSN.cosOddQ 4194304) 0 2 Ns96p715 Ns96p716 Ns96p714 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p718 := @Ns96p703 249178608 10150215680000 229575 1048576 15573663 634388480000 (@Ns96p704 199 8388608 Bool.false 918300 4194304 1 1210000 (@Ns96p707 Ns96p405 5662597 4194304 199 8388608 (@Ns96p708 70368744177664 265306495 70368744177664 Ns96p705 Ns96p163 Ns96p706 Ns96p405 RS097to114.d35 (@Ns96p709 0 1 241922167903216 15120135493951 70368744177664 265306495 70368744177664 (@Ns96p710 89943401418222206976 10722088982847 70368744177664 265306495 70368744177664 (@Ns96p711 72368511 70368744177664 (Ns96p696 rfl rfl) (Ns96p696 rfl rfl) rfl) (Ns96p696 rfl rfl) rfl rfl) qz369 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 5662597 4194304) (BSN.cos_neg_of_bound 5662597 4194304 Bool.false 918300 4194304 1 1210000 (Ns96p717 rfl rfl)) rfl rfl) 

noncomputable def Ns96p719 := @Ns96p681 19125174964549354353 558014008229713936384000 (Ns96p682 qz28 (@Enclosure.Real.IsNear.of_eq qz679 (@Inv.inv Real Real.instInv (Real.sqrt qz93)) Bool.false 1564479 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz88 (BSN.t_div_two_pi_nonneg qz87 324594 1000 qz90)) Ns96p686) rfl) (@Ns96p687 8796093022208 243518758330347 2660818139217920000 (BSN.correction_mk qz89 (BSN.cos_two_pi_p_ne_zero_mk qz87 324594 1000 7 qz90 rfl rfl (@BSN.floor_sqrt_eq_dec qz87 324594 1000 7 qz90 rfl rfl rfl))) (@Ns96p688 8388608 229575 1048576 15573663 634388480000 5035610771325 8796093022208 243518758330347 2660818139217920000 (@Ns96p689 8388608 (Ns96p702 rfl rfl rfl rfl rfl) rfl) (Ns96p718 rfl) rfl)) 

noncomputable def Ns96p720 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz87) (hardyZApproximantRS₀ qz87) Bool.false 39341150402698687171 36893488147419103232 1019925397577889514353 558014008229713936384000 (@Eq.refl Real (hardyZApproximantRS₀ qz87)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz87) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz87) qz87 7) (@HMul.hMul Real Real Real qz5 qz676 (Zeta.RiemannSiegel.correction qz89))) Bool.false 39341150402698687171 36893488147419103232 1019925397577889514353 558014008229713936384000 (BSN.hardyZApproximantRS₀_eq qz87 7 (@BSN.floor_sqrt_eq_dec qz87 324594 1000 7 qz90 rfl rfl rfl)) (@Ns96p619 39341150402698687171 36893488147419103232 1019925397577889514353 558014008229713936384000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz87) qz87 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 7)) Bool.false 28615471 33554432 15045 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz87) qz87 7) (Ns96p680 (Ns96p679 rfl) rfl rfl)) (Ns96p719 rfl) rfl rfl)) 

theorem RS097to114.d44 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz87) Bool.false 39341150402698687171 36893488147419103232 1019925397577889514353 558014008229713936384000 := Ns96p720 

noncomputable def Ns96p721 := nat_lit 3730416449133341323911233536 

noncomputable abbrev qz889 := (Enclosure.sfrac Bool.false 326185 1000)

noncomputable abbrev qz682 := qz889

noncomputable abbrev qz439 := qz682

noncomputable abbrev qz100 := qz439

noncomputable abbrev qz890 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 326185 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz683 := qz890

noncomputable abbrev qz440 := qz683

noncomputable abbrev qz101 := qz440

noncomputable abbrev qz891 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 326185 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz684 := qz891

noncomputable abbrev qz441 := qz684

noncomputable abbrev qz102 := qz441

noncomputable abbrev qz685 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz101 qz9))

noncomputable def Ns96p722 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz100) qz100 7) (@HMul.hMul Real Real Real qz5 qz685 (Zeta.RiemannSiegel.correction qz102)) 209101321 33554432 15117 8388608 3779593253977515975 18446744073709551616 264505987508318049741 Ns96p180 Ns96p721 

noncomputable def Ns96p723 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz100) qz100 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 326185 1000 66 98 67108864 33554432 1125899906842624 Bool.false 32256746934 1233 

noncomputable def Ns96p724 := Ns96p723 120242927 57 27397080 8 130587807 57 25364760 8 Bool.true 156703252 44861 Bool.true 7344643 Bool.true 8429899 3537118876014220 1 Bool.false 66707352 Bool.true Bool.false 66580097 Bool.true Bool.true 209101321 

noncomputable def Ns96p725 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz100) qz100 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 326185 1000 18 28 67108864 33554432 1125899906842624 Bool.false 32256746934 1233 

noncomputable def Ns96p726 := Ns96p725 93032624 56 33554424 8 108007536 56 30011992 8 Bool.true 152220523 26371 Bool.false 13442047 Bool.true 22089198 3537118876014220 1 Bool.false 65767123 Bool.true Bool.false 63506186 Bool.false Bool.true 156703252 

noncomputable def Ns96p727 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz100) qz100 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 326185 1000 162 77 67108864 33554432 1125899906842624 Bool.false 32256746934 1233 

noncomputable def Ns96p728 := Ns96p727 46516304 56 47453136 16 73726608 56 38745320 8 Bool.true 67108840 1296 Bool.false 6700468 Bool.false 91327809 3537118876014220 1 Bool.false 66774638 Bool.true Bool.false 65635859 Bool.true Bool.true 152220523 

noncomputable def Ns96p729 := nat_lit 600716974713592359261625061709460827101325736656661 

noncomputable def Ns96p730 := nat_lit 1249767493290507582712565329937985535497102950400 

noncomputable def Ns96p731 := nat_lit 1772408200114293603558935500000000 

noncomputable def Ns96p732 := nat_lit 3468801616197968403533706066405000000 

noncomputable abbrev qz442 := (@Eq.refl Real qz682)

noncomputable abbrev qz103 := qz442

noncomputable def Ns96p733 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz100 326185 1000 425587616900 16000000 652370 4000 2000 Ns96p731 Ns96p732 qz103 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns96p734 := nat_lit 3003584873567961796308125308547304135506628683283305000000 

noncomputable abbrev qz443 := (Enclosure.sfrac Bool.false 326185 2000)

noncomputable abbrev qz686 := (Real.log (Enclosure.sfrac Bool.false 425587616900 16000000))

noncomputable abbrev qz104 := (@HSub.hSub Real Real Real qz342 (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 326185 4000) qz686) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 652370)))))) qz443)

noncomputable abbrev qz444 := (@HSub.hSub Real Real Real qz12 qz104 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 326185 2000) (Real.log Real.pi)))

noncomputable def Ns96p735 := @Enclosure.Real.IsNear.addLit_ft_p qz444 (Enclosure.sfrac Bool.true Ns96p731 Ns96p732) 865886377713019228981 1801439850948198400 454774332835051593 24780800000000000000000 Ns96p731 Ns96p732 0 1 Ns96p734 

noncomputable def Ns96p736 := nat_lit 11621730232279127693414157516800 

noncomputable abbrev qz445 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 326185 2000) (Real.log Real.pi))

noncomputable def Ns96p737 := @Enclosure.Real.IsNear.subLit_ff_p qz104 qz445 1202209538406239277877 1801439850948198400 417731305261789 48400000000000000000 2505802815357 13421772800 65237 6710886400 Ns96p736 865886377713019228981 1801439850948198400 

noncomputable def Ns96p738 := nat_lit 2404419076812478555754000 

noncomputable abbrev qz105 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 326185 4000) qz686) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 652370))))))

noncomputable def Ns96p739 := @Enclosure.Real.IsNear.subLit_ff_p qz105 qz443 1496010867297008325429 1801439850948198400 417731305261789 48400000000000000000 326185 2000 0 1 Ns96p738 1202209538406239277877 1801439850948198400 417731305261789 48400000000000000000 

noncomputable def Ns96p740 := nat_lit 3368716992250509617454005705760571392 

noncomputable def Ns96p741 := nat_lit 12317306794126060556386304 

noncomputable def Ns96p742 := nat_lit 246044917713904823714431114731398385748024219680908305062633074060852943251063432261369257219193413639500000000000000000000 

noncomputable def Ns96p743 := nat_lit 4795843031560157611621885601148879991826114336594647379289035950224895876714451157654241652952645432900000000000000000000 

noncomputable def Ns96p744 := nat_lit 12856165434415683818729522224427675320761402286183292578044984728849376876165572105380167546694500000000000000000000 

noncomputable def Ns96p745 := BSN.log_dyadic_bound 163443616900 687731616900 6 5 Ns96p742 33554432 9680000 Ns96p743 Ns96p744 16259701 851175233800 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 163443616900) (BSN.artanhQ 687731616900) 0 5 Ns96p743 Ns96p742 Ns96p744 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns96p746 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 326185 4000) qz686 326185 4000 0 1 22942771751668417 2251799813685248 6250000847 60500000000000000 1496717600763592519829 1801439850948198400 407731305255739 48400000000000000000 (Enclosure.Real.IsNear.const Bool.false 326185 4000) (BSN.isNear_log_sfrac 425587616900 16000000 22942771751668417 2251799813685248 6250000847 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 425587616900) qz350)) Bool.false Ns96p741 Ns96p86 1000000135520000 9680000000000000000000 22942771751668417 2251799813685248 6250000847 60500000000000000 (BSN.log_rat_reduce_isNear 425587616900 16000000 14 851175233800 524288000000 16259701 33554432 24973259072661432 36028797018963968 9680000 1000000000000000 rfl rfl rfl rfl (Ns96p745 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p747 := BSN.arctan_dyadic_bound_f 1000 652370 1 0 4194304 1210000 0 1 1 0 1 1 6429 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 652370) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 652370) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz446 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 652370)))

noncomputable def Ns96p748 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz446 884279719003555 562949953421312 1 2000000000000000 6429 4194304 1 1210000 3705318757284941135872 883416833230243 562949953421312 200000000121 242000000000000000 qz17 (Ns96p747 rfl) rfl rfl 

noncomputable def Ns96p749 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 326185 4000) qz686) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz446)) 1496717600763592519829 1801439850948198400 407731305255739 48400000000000000000 883416833230243 2251799813685248 200000000121 968000000000000000 Ns96p740 1496010867297008325429 1801439850948198400 417731305261789 48400000000000000000 (Ns96p746 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz446) 1 4 0 1 883416833230243 562949953421312 200000000121 242000000000000000 883416833230243 2251799813685248 200000000121 968000000000000000 qz353 Ns96p748 rfl) 

noncomputable def Ns96p750 := @Ns96p735 Ns96p729 Ns96p730 454774332835051593 24780800000000000000000 (@Ns96p737 454774332835051593 24780800000000000000000 (Ns96p739 (Ns96p749 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 326185 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz443 (Real.log Real.pi) 326185 2000 0 1 38410761 33554432 1 16777216 2505802815357 13421772800 65237 6710886400 (Enclosure.Real.IsNear.const Bool.false 326185 2000) RS097to114.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns96p731 Ns96p732) 

noncomputable def Ns96p751 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz100) Bool.false Ns96p729 Ns96p730 454774332835051593 24780800000000000000000 2016046683 4194304 155 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz100) (@HAdd.hAdd Real Real Real qz354 qz444 (Enclosure.sfrac Bool.true Ns96p731 Ns96p732)) Bool.false Ns96p729 Ns96p730 454774332835051593 24780800000000000000000 Ns96p733 (Ns96p750 rfl rfl)) 

noncomputable def Ns96p752 := nat_lit 139742436356372012942250168428906997410499554849182572644165067867553504966252807025025 

noncomputable def Ns96p753 := nat_lit 280278874379666362075703322831136738949892183204220266291405472659312817202482344321 

noncomputable def Ns96p754 := nat_lit 365538310374835812167294540505410771831103770594099905065484330792620292255191427936641 

noncomputable def Ns96p755 := BSN.sin_dyadic_bound_f 26974213809 17179869184 3 2 8388608 2422364 Ns96p752 Ns96p99 Ns96p753 Ns96p754 Ns96p102 Ns96p753 8388605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26974213809) qz355 0 2 Ns96p752 Ns96p99 Ns96p753 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26974213809) qz356 0 2 Ns96p754 Ns96p102 Ns96p753 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p756 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz100) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2016046683) qz434) Bool.false 2016046683 4194304 155 8388608 Bool.true 8388605 8388608 1 1210000 (Ns96p751 rfl) (Enclosure.sfrac_false_div 2016046683 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2016046683) qz434) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949070775479577635454976) qz678) 226375608064910080 72057594037927936 Bool.false 8388605 8388608 76 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q1 2016046683 4194304 226375608064910080 72057594037927936 76 949070775479577635454976 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388605 8388608 949070775479577635454976 604462909807314587353088 26974213809 17179869184 2422364 2420000 (Ns96p755 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p757 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz100) Bool.false Ns96p729 Ns96p730 454774332835051593 24780800000000000000000 32256746934 67108864 1233 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz100) (@HAdd.hAdd Real Real Real qz354 qz444 (Enclosure.sfrac Bool.true Ns96p731 Ns96p732)) Bool.false Ns96p729 Ns96p730 454774332835051593 24780800000000000000000 Ns96p733 (Ns96p750 rfl rfl)) 

noncomputable def Ns96p758 := Ns96p728 26371 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 162 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66774638 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 77 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 65635859 67108864) qz103 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 1) Bool.true 8388605 8388608 12246163 634388480000 67108840 67108864 1296 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz100)) Bool.true 8388605 8388608 12246163 634388480000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz100) qz100) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz100)) Bool.true 8388605 8388608 195938608 10150215680000 8388605 8388608 12246163 634388480000 (Ns96p756 rfl rfl) rfl)) rfl) (Ns96p757 rfl) RS097to114.d7 

noncomputable def Ns96p759 := nat_lit 2015675187330671294589112576 

noncomputable def Ns96p760 := BSN.cos_dyadic_bound_f 6700468 67108864 2 1 67108864 33554432 Ns96p759 Ns96p131 Ns96p759 Ns96p759 Ns96p132 Ns96p759 66774638 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 6700468) qz359 0 1 Ns96p759 Ns96p131 Ns96p759 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 6700468) (BSN.cosOddQ 67108864) 0 1 Ns96p759 Ns96p132 Ns96p759 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p761 := nat_lit 1486766420667490297989782271582354580171106275194182302202115210341817061728312402649519446160524558081 

noncomputable def Ns96p762 := nat_lit 51956389457850993117201226487380036501230565613159928972022824181150019275806034930923536691271355596800 

noncomputable def Ns96p763 := nat_lit 336694844094542470934753225135987877199488704366117710384563428431803277463842543441693118938881 

noncomputable def Ns96p764 := nat_lit 7428624238547076713340889722663804555948536805650750703615345028661602257960509932273923832470374301441 

noncomputable def Ns96p765 := nat_lit 1818473631024784759102042927058301277543069796460597514020798846340250674653211222582323784194497445888000 

noncomputable def Ns96p766 := BSN.sin_dyadic_bound_f 91327809 67108864 4 3 67108864 33554432 Ns96p761 Ns96p762 Ns96p763 Ns96p764 Ns96p765 Ns96p763 65635859 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 91327809) qz360 0 3 Ns96p761 Ns96p762 Ns96p763 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 91327809) (BSN.sinOddQ 67108864) 0 3 Ns96p764 Ns96p765 Ns96p763 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p767 := nat_lit 32648380125978146848815943681 

noncomputable def Ns96p768 := BSN.cos_dyadic_bound_f 13442047 67108864 2 1 67108864 33554432 Ns96p767 Ns96p131 Ns96p767 Ns96p767 Ns96p132 Ns96p767 65767123 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 13442047) qz359 0 1 Ns96p767 Ns96p131 Ns96p767 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 13442047) (BSN.cosOddQ 67108864) 0 1 Ns96p767 Ns96p132 Ns96p767 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p769 := nat_lit 238078288777967190696748505616 

noncomputable def Ns96p770 := BSN.cos_dyadic_bound_f 22089198 67108864 2 1 67108864 33554432 Ns96p769 Ns96p131 Ns96p769 Ns96p769 Ns96p132 Ns96p769 63506186 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 22089198) qz359 0 1 Ns96p769 Ns96p131 Ns96p769 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 22089198) (BSN.cosOddQ 67108864) 0 1 Ns96p769 Ns96p132 Ns96p769 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p771 := Ns96p726 44861 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 18 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 65767123 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 28 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 63506186 67108864) qz103 rfl rfl (Ns96p758 RS097to114.d9 RS097to114.d11 RS097to114.d13 RS097to114.d17 (Ns96p760 rfl rfl) (Ns96p766 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns96p757 rfl) RS097to114.d19 RS097to114.d21 RS097to114.d23 RS097to114.d25 RS097to114.d17 (Ns96p768 rfl rfl) (Ns96p770 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns96p772 := nat_lit 2909931486723227470364907601 

noncomputable def Ns96p773 := BSN.cos_dyadic_bound_f 7344643 67108864 2 1 67108864 33554432 Ns96p772 Ns96p131 Ns96p772 Ns96p772 Ns96p132 Ns96p772 66707352 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 7344643) qz359 0 1 Ns96p772 Ns96p131 Ns96p772 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 7344643) (BSN.cosOddQ 67108864) 0 1 Ns96p772 Ns96p132 Ns96p772 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p774 := nat_lit 5049977989208335527754340401 

noncomputable def Ns96p775 := BSN.cos_dyadic_bound_f 8429899 67108864 2 1 67108864 33554432 Ns96p774 Ns96p131 Ns96p774 Ns96p774 Ns96p132 Ns96p774 66580097 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 8429899) qz359 0 1 Ns96p774 Ns96p131 Ns96p774 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 8429899) (BSN.cosOddQ 67108864) 0 1 Ns96p774 Ns96p132 Ns96p774 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p776 := Ns96p724 60468 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 66 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66707352 67108864) BSN.abs_quadSignNeg qz636 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66580097 67108864) qz103 rfl rfl (Ns96p771 rfl rfl) (Ns96p757 rfl) RS097to114.d27 RS097to114.d29 RS097to114.d31 RS097to114.d33 RS097to114.d17 (Ns96p773 rfl rfl) (Ns96p775 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns96p777 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 7) 209101321 67108864 60468 67108864 209101321 67108864 60468 67108864 28065104226418688 209101321 33554432 15117 8388608 (Ns96p776 rfl) 

noncomputable def Ns96p778 := @Enclosure.Real.IsNear.mulLit_tf qz685 (Zeta.RiemannSiegel.correction qz102) 195321 524288 1 4194304 19350675318975 35184372088832 337616182194603 2660818139217920000 3779593253977515975 18446744073709551616 

noncomputable abbrev qz687 := (@HPow.hPow Real Real Real qz7 qz101 qz9)

noncomputable def Ns96p779 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz687 1 1 0 1 195321 524288 1 4194304 195321 524288 1 4194304 

noncomputable def Ns96p780 := @Enclosure.Real.IsNear.sqrt_image qz101 87097201093 1677721600 65237 1677721600 30220517 30220540 4194304 (@Enclosure.Real.IsNear.of_eq qz101 (@HMul.hMul Real Real Real qz5 qz100 qz3) Bool.false 87097201093 1677721600 65237 1677721600 (BSN.t_div_two_pi_mk qz100 326185 1000 qz103) (@Enclosure.Real.IsNear.mulLit_ff qz100 qz3 326185 1000 0 1 1335089 8388608 1 8388608 87097201093 1677721600 65237 1677721600 (Enclosure.Real.IsNear.const Bool.false 326185 1000) RS097to114.d36 rfl)) 

noncomputable abbrev qz892 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 326185 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz688 := qz892

noncomputable abbrev qz447 := qz688

noncomputable abbrev qz106 := qz447

noncomputable def Ns96p781 := @Enclosure.Real.IsNear.sqrt_image qz106 60441057 8388608 23 8388608 11258509 11258514 4194304 (@Enclosure.Real.IsNear.recentre' qz106 Bool.false 60441057 8388608 23 8388608 60441057 8388608 23 8388608 (Ns96p780 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns96p782 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz106) 22517023 8388608 5 8388608 1562567 1562569 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz106) Bool.false 22517023 8388608 5 8388608 22517023 8388608 5 8388608 (Ns96p781 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns96p783 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz106)) Bool.false 3125136 8388608 2 8388608 195321 524288 1 4194304 (Ns96p782 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz107 := (@HMul.hMul Real Real Real qz339 qz337 qz441)

noncomputable abbrev qz689 := (@HMul.hMul Real Real Real qz863 qz891 qz891)

noncomputable abbrev qz448 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz689 qz684) qz641)

noncomputable abbrev qz108 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz448))

noncomputable def Ns96p784 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz102) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz107)) qz108) Bool.false 19350675318975 

noncomputable def Ns96p785 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz107)) qz108 30156035 8388608 1977 

noncomputable def Ns96p786 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz107)) Bool.false 30156035 8388608 1977 8388608 30156035 8388608 1977 

noncomputable def Ns96p787 := @Enclosure.Real.IsNear.recentre' (Real.cos qz107) Bool.false 1166744 4194304 92524304 5075107840000 145843 524288 5782769 317194240000 

noncomputable def Ns96p788 := @Enclosure.Real.IsNear.cos_image qz107 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10812111) qz357) Bool.false 10812111 8388608 73 4194304 Bool.false 1166744 4194304 1 

noncomputable def Ns96p789 := nat_lit 620679734422794613504734433 

noncomputable def Ns96p790 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz102 884279719003555 140737488355328 1 500000000000000 1720801 8388608 23 8388608 1521669424741036447555 1180591620717411303424 Ns96p789 

noncomputable def Ns96p791 := @Enclosure.Real.IsNear.subLit_ff_p qz106 qz1 60441057 8388608 23 8388608 7 1 0 1 1720801 1720801 8388608 23 

noncomputable def Ns96p792 := @Ns96p791 8388608 (@Enclosure.Real.IsNear.recentre' qz106 Bool.false 60441057 8388608 23 8388608 60441057 8388608 23 8388608 (Ns96p780 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns96p793 := @Enclosure.Real.IsNear.recentre' qz107 Bool.false 1521669424741036447555 1180591620717411303424 Ns96p789 Ns96p148 10812111 8388608 73 4194304 (@Ns96p790 Ns96p148 RS097to114.d35 (Ns96p792 rfl rfl) rfl) 

noncomputable def Ns96p794 := nat_lit 113873775480450908479767986987261093002584793566138774988161 

noncomputable def Ns96p795 := nat_lit 186760042915697798313586245446360812719082235765131191681 

noncomputable def Ns96p796 := nat_lit 341247806355521329842676788470890557382316216226886062581121 

noncomputable def Ns96p797 := BSN.cos_dyadic_bound_f 10812111 8388608 3 2 4194304 1210000 Ns96p794 Ns96p262 Ns96p795 Ns96p796 Ns96p265 Ns96p795 1166744 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 10812111) (BSN.cosEvenQ 8388608) 0 2 Ns96p794 Ns96p262 Ns96p795 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 10812111) (BSN.cosOddQ 8388608) 0 2 Ns96p796 Ns96p265 Ns96p795 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p798 := @Enclosure.Real.IsNear.inv_image (Real.cos qz107) 145843 524288 5782769 317194240000 15077029 15079006 4194304 (Ns96p787 (@Ns96p788 1210000 (Ns96p793 rfl) (Enclosure.sfrac_false_div 10812111 8388608) (Ns96p797 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns96p799 := @Enclosure.Real.IsNear.recentre' qz108 Bool.false 641685 4194304 

noncomputable abbrev qz109 := (@HMul.hMul Real Real Real qz339 qz337 qz448)

noncomputable def Ns96p800 := @Enclosure.Real.IsNear.cos_image qz109 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 5944181)) qz434) Bool.true 5944181 4194304 

noncomputable def Ns96p801 := nat_lit 14035301374977866567385336605 

noncomputable def Ns96p802 := nat_lit 1468557175312250193923976093757733 

noncomputable def Ns96p803 := @Enclosure.Real.IsNear.recentre' qz109 Bool.true Ns96p801 Ns96p163 Ns96p802 

noncomputable abbrev qz110 := qz448

noncomputable def Ns96p804 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz110 884279719003555 140737488355328 1 500000000000000 15872015464511 

noncomputable abbrev qz449 := (@HSub.hSub Real Real Real qz635 qz689 qz684)

noncomputable abbrev qz111 := qz449

noncomputable def Ns96p805 := @Enclosure.Real.IsNear.subLit_tf qz111 qz26 11473968953407 70368744177664 272095359 70368744177664 1 16 

noncomputable abbrev qz450 := qz689

noncomputable abbrev qz112 := qz450

noncomputable def Ns96p806 := @Enclosure.Real.IsNear.subLit_ff_n qz112 qz102 2961156081601 70368744177664 79157375 70368744177664 1720801 8388608 23 8388608 

noncomputable def Ns96p807 := @Enclosure.Real.IsNear.mulLit_ff qz102 qz102 1720801 8388608 23 8388608 1720801 8388608 23 8388608 2961156081601 70368744177664 

noncomputable def Ns96p808 := nat_lit 650666664193112179354803153813124952213021560560878356321 

noncomputable def Ns96p809 := nat_lit 1558605489744523444165041809342668240498646287655372641 

noncomputable def Ns96p810 := nat_lit 1948882781599847491176079377820689520158067389107324323681 

noncomputable def Ns96p811 := BSN.cos_dyadic_bound_f 5944181 4194304 3 2 4194304 1210000 Ns96p808 Ns96p713 Ns96p809 Ns96p810 Ns96p716 Ns96p809 641685 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 5944181) (BSN.cosEvenQ 4194304) 0 2 Ns96p808 Ns96p713 Ns96p809 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 5944181) (BSN.cosOddQ 4194304) 0 2 Ns96p810 Ns96p716 Ns96p809 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p812 := @Ns96p799 256438608 10150215680000 641685 4194304 16027413 634388480000 (@Ns96p800 205 8388608 Bool.false 641685 4194304 1 1210000 (@Ns96p803 Ns96p166 5944181 4194304 205 8388608 (@Ns96p804 70368744177664 272095359 70368744177664 Ns96p801 Ns96p163 Ns96p802 Ns96p166 RS097to114.d35 (@Ns96p805 0 1 253952247432176 15872015464511 70368744177664 272095359 70368744177664 (@Ns96p806 96250627754301587456 11473968953407 70368744177664 272095359 70368744177664 (@Ns96p807 79157375 70368744177664 (Ns96p792 rfl rfl) (Ns96p792 rfl rfl) rfl) (Ns96p792 rfl rfl) rfl rfl) qz369 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 5944181 4194304) (BSN.cos_neg_of_bound 5944181 4194304 Bool.false 641685 4194304 1 1210000 (Ns96p811 rfl rfl)) rfl rfl) 

noncomputable def Ns96p813 := @Ns96p778 264505987508318049741 Ns96p180 (Ns96p779 qz28 (@Enclosure.Real.IsNear.of_eq qz687 (@Inv.inv Real Real.instInv (Real.sqrt qz106)) Bool.false 195321 524288 1 4194304 (BSN.rpow_neg_quarter_mk qz101 (BSN.t_div_two_pi_nonneg qz100 326185 1000 qz103)) Ns96p783) rfl) (@Ns96p784 35184372088832 337616182194603 2660818139217920000 (BSN.correction_mk qz102 (BSN.cos_two_pi_p_ne_zero_mk qz100 326185 1000 7 qz103 rfl rfl (@BSN.floor_sqrt_eq_dec qz100 326185 1000 7 qz103 rfl rfl rfl))) (@Ns96p785 8388608 641685 4194304 16027413 634388480000 19350675318975 35184372088832 337616182194603 2660818139217920000 (@Ns96p786 8388608 (Ns96p798 rfl rfl rfl rfl rfl) rfl) (Ns96p812 rfl) rfl)) 

noncomputable def Ns96p814 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz100) (hardyZApproximantRS₀ qz100) Bool.true 111175073657433430073 18446744073709551616 10320402940147642209741 Ns96p180 (@Eq.refl Real (hardyZApproximantRS₀ qz100)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz100) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz100) qz100 7) (@HMul.hMul Real Real Real qz5 qz685 (Zeta.RiemannSiegel.correction qz102))) Bool.true 111175073657433430073 18446744073709551616 10320402940147642209741 Ns96p180 (BSN.hardyZApproximantRS₀_eq qz100 7 (@BSN.floor_sqrt_eq_dec qz100 326185 1000 7 qz103 rfl rfl rfl)) (@Ns96p722 111175073657433430073 18446744073709551616 10320402940147642209741 Ns96p180 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz100) qz100 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 7)) Bool.true 209101321 33554432 15117 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz100) qz100 7) (Ns96p777 (Ns96p776 rfl) rfl rfl)) (Ns96p813 rfl) rfl rfl)) 

theorem RS097to114.d45 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz100) Bool.true 111175073657433430073 18446744073709551616 10320402940147642209741 Ns96p180 := Ns96p814 

noncomputable def Ns96p815 := nat_lit 109419029267705918740496384 

noncomputable abbrev qz893 := (Enclosure.sfrac Bool.false 327775 1000)

noncomputable abbrev qz690 := qz893

noncomputable abbrev qz451 := qz690

noncomputable abbrev qz113 := qz451

noncomputable abbrev qz894 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 327775 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz691 := qz894

noncomputable abbrev qz452 := qz691

noncomputable abbrev qz114 := qz452

noncomputable abbrev qz895 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 327775 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz692 := qz895

noncomputable abbrev qz453 := qz692

noncomputable abbrev qz115 := qz453

noncomputable abbrev qz693 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz114 qz9))

noncomputable def Ns96p816 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz113) qz113 7) (@HMul.hMul Real Real Real qz5 qz693 (Zeta.RiemannSiegel.correction qz115)) 40845667 33554432 60765 33554432 454048322411937825 2305843009213693952 5394097033725178533 69751751028714242048000 Ns96p815 

noncomputable def Ns96p817 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz113) qz113 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 327775 1000 65 98 67108864 33554432 1125899906842624 Bool.false 32467593346 1239 

noncomputable def Ns96p818 := Ns96p817 120242927 57 27397080 8 130587807 57 25364760 8 Bool.false 93070824 45082 Bool.true 93098842 Bool.true 5218100 3537118876014220 1 Bool.false 65981988 Bool.true Bool.false 66906097 Bool.true Bool.false 40845667 

noncomputable def Ns96p819 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz113) qz113 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 327775 1000 18 27 67108864 33554432 1125899906842624 Bool.false 32467593346 1239 

noncomputable def Ns96p820 := Ns96p819 93032624 56 33554424 8 108007536 56 30011992 8 Bool.false 78094063 26502 Bool.false 76366587 Bool.true 88389125 3537118876014220 1 Bool.false 28149187 Bool.true Bool.false 64960807 Bool.false Bool.false 93070824 

noncomputable def Ns96p821 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz113) qz113 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 327775 1000 163 78 67108864 33554432 1125899906842624 Bool.false 32467593346 1239 

noncomputable def Ns96p822 := Ns96p821 46516304 56 47453136 16 73726608 56 38745320 8 Bool.false 67108848 1304 Bool.false 38171600 Bool.false 79534557 3537118876014220 1 Bool.false 36146334 Bool.false Bool.false 25243089 Bool.true Bool.false 78094063 

noncomputable def Ns96p823 := nat_lit 7968570468986902669036100198996991173751707951 

noncomputable def Ns96p824 := nat_lit 16470629842087827238733113098189307977400320 

noncomputable def Ns96p825 := nat_lit 1816029620430209577957812500000000 

noncomputable def Ns96p826 := nat_lit 3571498531399240625244863203125000000 

noncomputable abbrev qz454 := (@Eq.refl Real qz690)

noncomputable abbrev qz116 := qz454

noncomputable def Ns96p827 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz113 327775 1000 429746802500 16000000 655550 4000 2000 Ns96p825 Ns96p826 qz116 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns96p828 := nat_lit 622544567889601771018445328046639935449352183671875000000 

noncomputable abbrev qz694 := (Real.log (Enclosure.sfrac Bool.false 429746802500 16000000))

noncomputable abbrev qz117 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 327775 4000) qz694) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 655550))))))

noncomputable abbrev qz695 := (Enclosure.sfrac Bool.false 327775 2000)

noncomputable abbrev qz455 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz117 qz695) (@HMul.hMul Real Real Real qz5 qz695 (Real.log Real.pi)))

noncomputable def Ns96p829 := @Enclosure.Real.IsNear.addLit_ft_p qz455 (Enclosure.sfrac Bool.true Ns96p825 Ns96p826) 174309247703743822999 360287970189639680 755316013791819 40960000000000000000 Ns96p825 Ns96p826 0 1 Ns96p828 

noncomputable def Ns96p830 := nat_lit 467907823923714260339198525440 

noncomputable abbrev qz456 := (@HSub.hSub Real Real Real qz12 qz117 qz695)

noncomputable abbrev qz457 := (@HMul.hMul Real Real Real qz5 qz695 (Real.log Real.pi))

noncomputable def Ns96p831 := @Enclosure.Real.IsNear.subLit_ff_p qz456 qz457 241901763604977908887 360287970189639680 693750091787 80000000000000000 503603487471 2684354560 13111 1342177280 Ns96p830 174309247703743822999 360287970189639680 

noncomputable abbrev qz458 := qz695

noncomputable def Ns96p832 := @Enclosure.Real.IsNear.subLit_ff_p qz117 qz458 300948458319432481943 360287970189639680 693750091787 80000000000000000 327775 2000 0 1 483803527209955817774000 241901763604977908887 360287970189639680 693750091787 80000000000000000 

noncomputable def Ns96p833 := nat_lit 677675682372560686271847746045476864 

noncomputable def Ns96p834 := nat_lit 12329064035428462049099776 

noncomputable def Ns96p835 := nat_lit 261336498593913290007490959223734646075418633215253844146333768968884600591025819576591444015502929687500000000000000000000 

noncomputable def Ns96p836 := nat_lit 5299586669472471981526808331910141993182032409225025647816093638053408657952424759471216201782226562500000000000000000000 

noncomputable def Ns96p837 := nat_lit 16528923543420733027487979472744780604328428703527651502463876428568187810870599222183227539062500000000000000000000 

noncomputable def Ns96p838 := BSN.log_dyadic_bound 167602802500 691890802500 6 5 Ns96p835 33554432 9680000 Ns96p836 Ns96p837 16586030 859493605000 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 167602802500) (BSN.artanhQ 691890802500) 0 5 Ns96p836 Ns96p835 Ns96p837 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns96p839 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 327775 4000) qz694 327775 4000 0 1 22964671320148673 2251799813685248 6250000847 60500000000000000 301089805678469251703 360287970189639680 81943761105017 9680000000000000000 (Enclosure.Real.IsNear.const Bool.false 327775 4000) (BSN.isNear_log_sfrac 429746802500 16000000 22964671320148673 2251799813685248 6250000847 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 429746802500) qz350)) Bool.false Ns96p834 Ns96p86 1000000135520000 9680000000000000000000 22964671320148673 2251799813685248 6250000847 60500000000000000 (BSN.log_rat_reduce_isNear 429746802500 16000000 14 859493605000 524288000000 16586030 33554432 24973259072661432 36028797018963968 9680000 1000000000000000 rfl rfl rfl rfl (Ns96p838 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p840 := BSN.arctan_dyadic_bound_f 1000 655550 1 0 4194304 1210000 0 1 1 0 1 1 6398 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 655550) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 655550) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz459 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 655550)))

noncomputable def Ns96p841 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz459 884279719003555 562949953421312 1 2000000000000000 6398 4194304 1 1210000 3705336208733497196544 883420993979811 562949953421312 200000000121 242000000000000000 qz17 (Ns96p840 rfl) rfl rfl 

noncomputable def Ns96p842 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 327775 4000) qz694) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz459)) 301089805678469251703 360287970189639680 81943761105017 9680000000000000000 883420993979811 2251799813685248 200000000121 968000000000000000 Ns96p833 300948458319432481943 360287970189639680 693750091787 80000000000000000 (Ns96p839 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz459) 1 4 0 1 883420993979811 562949953421312 200000000121 242000000000000000 883420993979811 2251799813685248 200000000121 968000000000000000 qz353 Ns96p841 rfl) 

noncomputable def Ns96p843 := @Ns96p829 Ns96p823 Ns96p824 755316013791819 40960000000000000000 (@Ns96p831 755316013791819 40960000000000000000 (Ns96p832 (Ns96p842 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 327775 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz458 (Real.log Real.pi) 327775 2000 0 1 38410761 33554432 1 16777216 503603487471 2684354560 13111 1342177280 (Enclosure.Real.IsNear.const Bool.false 327775 2000) RS097to114.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns96p825 Ns96p826) 

noncomputable def Ns96p844 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz113) Bool.false Ns96p823 Ns96p824 755316013791819 40960000000000000000 253653073 524288 39 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz113) (@HAdd.hAdd Real Real Real qz354 qz455 (Enclosure.sfrac Bool.true Ns96p825 Ns96p826)) Bool.false Ns96p823 Ns96p824 755316013791819 40960000000000000000 Ns96p827 (Ns96p843 rfl rfl)) 

noncomputable def Ns96p845 := nat_lit 139836555671711259992554541172491912005667805287727927152838594101201358437775988324225 

noncomputable def Ns96p846 := nat_lit 280655791596710712381954342390646158069254077673758168739638907928985461635355342721 

noncomputable def Ns96p847 := nat_lit 365784203096658625493786348421227294806541650104006105508046426318880438494384632199041 

noncomputable def Ns96p848 := BSN.sin_dyadic_bound_f 26978745487 17179869184 3 2 8388608 2422364 Ns96p845 Ns96p99 Ns96p846 Ns96p847 Ns96p102 Ns96p846 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26978745487) qz355 0 2 Ns96p845 Ns96p99 Ns96p846 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26978745487) qz356 0 2 Ns96p847 Ns96p102 Ns96p846 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p849 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz113) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 253653073) qz423) Bool.false 253653073 524288 39 2097152 Bool.false 8388606 8388608 1 1210000 (Ns96p844 rfl) (Enclosure.sfrac_false_div 253653073 524288) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 253653073) qz423) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 118653777465177198821376) (@Nat.cast Real Real.instNatCast 75557863725914323419136)) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 76 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q3 253653073 524288 226375608064910080 72057594037927936 76 118653777465177198821376 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388606 8388608 118653777465177198821376 75557863725914323419136 26978745487 17179869184 2422364 2420000 (Ns96p848 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p850 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz113) Bool.false Ns96p823 Ns96p824 755316013791819 40960000000000000000 32467593346 67108864 1239 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz113) (@HAdd.hAdd Real Real Real qz354 qz455 (Enclosure.sfrac Bool.true Ns96p825 Ns96p826)) Bool.false Ns96p823 Ns96p824 755316013791819 40960000000000000000 Ns96p827 (Ns96p843 rfl rfl)) 

noncomputable def Ns96p851 := Ns96p822 26502 BSN.abs_quadSignPos (BSN.cos_quad_nat3 163 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 36146334 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 78 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 25243089 67108864) qz116 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 1) Bool.false 4194303 4194304 3080447 158597120000 67108848 67108864 1304 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz113)) Bool.false 4194303 4194304 3080447 158597120000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz113) qz113) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz113)) Bool.false 8388606 8388608 49287152 2537553920000 4194303 4194304 3080447 158597120000 (Ns96p849 rfl rfl) rfl)) rfl) (Ns96p850 rfl) RS097to114.d7 

noncomputable def Ns96p852 := nat_lit 130220040300809784408040696822230677477883172217917171302400000000 

noncomputable def Ns96p853 := nat_lit 4507366926575674591072738974324835956661288960000000000000000 

noncomputable def Ns96p854 := nat_lit 341045188860430217595530564385598105564811808960038305792000000000 

noncomputable def Ns96p855 := BSN.sin_dyadic_bound_f 38171600 67108864 3 2 67108864 33554432 Ns96p852 Ns96p221 Ns96p853 Ns96p854 Ns96p224 Ns96p853 36146334 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 38171600) qz360 0 2 Ns96p852 Ns96p221 Ns96p853 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 38171600) (BSN.sinOddQ 67108864) 0 2 Ns96p854 Ns96p224 Ns96p853 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p856 := nat_lit 328925907742495688800360853819295497001831978355600800250905147341762929840042378982999813260114490481 

noncomputable def Ns96p857 := nat_lit 64072312263510029306743226845799815238522979234935742017201611306147780844815763904865324070001 

noncomputable def Ns96p858 := nat_lit 1993923094638979315490967423145333461739787910214897957708396097043181009252840781271586149263658284145 

noncomputable def Ns96p859 := BSN.cos_dyadic_bound_f 79534557 67108864 4 3 67108864 33554432 Ns96p856 Ns96p236 Ns96p857 Ns96p858 Ns96p239 Ns96p857 25243089 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 79534557) qz359 0 3 Ns96p856 Ns96p236 Ns96p857 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 79534557) (BSN.cosOddQ 67108864) 0 3 Ns96p858 Ns96p239 Ns96p857 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p860 := nat_lit 279519216941623775978179354052314072305560170930647616603569134965230381363703483740020150574515566161 

noncomputable def Ns96p861 := nat_lit 39340563553581743455384440278609752146287840972661403355894984988761673986293368053780102592081 

noncomputable def Ns96p862 := nat_lit 1694622462449252753272396536489213474306350811831502818540254936560295479661628629557257614734860301905 

noncomputable def Ns96p863 := BSN.cos_dyadic_bound_f 76366587 67108864 4 3 67108864 33554432 Ns96p860 Ns96p236 Ns96p861 Ns96p862 Ns96p239 Ns96p861 28149187 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 76366587) qz359 0 3 Ns96p860 Ns96p236 Ns96p861 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 76366587) (BSN.cosOddQ 67108864) 0 3 Ns96p862 Ns96p239 Ns96p861 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p864 := nat_lit 3747387926317384128908112932857562609308279023054916870910400390625 

noncomputable def Ns96p865 := nat_lit 3725552409918505142088941715613816576991201419889926910400390625 

noncomputable def Ns96p866 := nat_lit 9808555579310423710243580347087384464206554543797341446910400390625 

noncomputable def Ns96p867 := BSN.sin_dyadic_bound_f 88389125 67108864 3 2 67108864 33554432 Ns96p864 Ns96p221 Ns96p865 Ns96p866 Ns96p224 Ns96p865 64960807 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 88389125) qz360 0 2 Ns96p864 Ns96p221 Ns96p865 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 88389125) (BSN.sinOddQ 67108864) 0 2 Ns96p866 Ns96p224 Ns96p865 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p868 := Ns96p820 45082 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 18 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 28149187 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 27 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 64960807 67108864) qz116 rfl rfl (Ns96p851 RS097to114.d9 RS097to114.d11 RS097to114.d13 RS097to114.d17 (Ns96p855 rfl rfl) (Ns96p859 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns96p850 rfl) RS097to114.d19 RS097to114.d21 RS097to114.d23 RS097to114.d25 RS097to114.d17 (Ns96p863 rfl rfl) (Ns96p867 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns96p869 := nat_lit 1605635681809713243891412520099697740475065071447261603623455585029692414240285045926853655029253083136 

noncomputable def Ns96p870 := nat_lit 423966311782236416639409371988284735682062997541797053381170773219577510189897737418480662286336 

noncomputable def Ns96p871 := nat_lit 8022105474636978774708295202417921200405274375925926079398254999300536604674376601383935884082929668096 

noncomputable def Ns96p872 := BSN.sin_dyadic_bound_f 93098842 67108864 4 3 67108864 33554432 Ns96p869 Ns96p762 Ns96p870 Ns96p871 Ns96p765 Ns96p870 65981988 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 93098842) qz360 0 3 Ns96p869 Ns96p762 Ns96p870 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 93098842) (BSN.sinOddQ 67108864) 0 3 Ns96p871 Ns96p765 Ns96p870 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p873 := nat_lit 741394894092341112100000000 

noncomputable def Ns96p874 := BSN.cos_dyadic_bound_f 5218100 67108864 2 1 67108864 33554432 Ns96p873 Ns96p131 Ns96p873 Ns96p873 Ns96p132 Ns96p873 66906097 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 5218100) qz359 0 1 Ns96p873 Ns96p131 Ns96p873 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 5218100) (BSN.cosOddQ 67108864) 0 1 Ns96p873 Ns96p132 Ns96p873 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p875 := Ns96p818 60765 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 65 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 65981988 67108864) BSN.abs_quadSignNeg qz636 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66906097 67108864) qz116 rfl rfl (Ns96p868 rfl rfl) (Ns96p850 rfl) RS097to114.d27 RS097to114.d29 RS097to114.d31 RS097to114.d33 RS097to114.d17 (Ns96p872 rfl rfl) (Ns96p874 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns96p876 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 7) 40845667 67108864 60765 67108864 40845667 67108864 60765 67108864 5482212623384576 40845667 33554432 60765 33554432 (Ns96p875 rfl) 

noncomputable def Ns96p877 := @Enclosure.Real.IsNear.mulLit_tf qz693 (Zeta.RiemannSiegel.correction qz115) 1560669 4194304 1 4194304 290931851925 549755813888 34506310400049 166301133701120000 454048322411937825 2305843009213693952 

noncomputable abbrev qz696 := (@HPow.hPow Real Real Real qz7 qz114 qz9)

noncomputable def Ns96p878 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz696 1 1 0 1 1560669 4194304 1 4194304 1560669 4194304 1 4194304 

noncomputable def Ns96p879 := @Enclosure.Real.IsNear.sqrt_image qz114 17504351879 335544320 13111 335544320 30294083 30294106 4194304 (@Enclosure.Real.IsNear.of_eq qz114 (@HMul.hMul Real Real Real qz5 qz113 qz3) Bool.false 17504351879 335544320 13111 335544320 (BSN.t_div_two_pi_mk qz113 327775 1000 qz116) (@Enclosure.Real.IsNear.mulLit_ff qz113 qz3 327775 1000 0 1 1335089 8388608 1 8388608 17504351879 335544320 13111 335544320 (Enclosure.Real.IsNear.const Bool.false 327775 1000) RS097to114.d36 rfl)) 

noncomputable abbrev qz896 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 327775 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz697 := qz896

noncomputable abbrev qz460 := qz697

noncomputable abbrev qz118 := qz460

noncomputable def Ns96p880 := @Enclosure.Real.IsNear.sqrt_image qz118 60588189 8388608 23 8388608 11272204 11272209 4194304 (@Enclosure.Real.IsNear.recentre' qz118 Bool.false 60588189 8388608 23 8388608 60588189 8388608 23 8388608 (Ns96p879 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns96p881 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz118) 22544413 8388608 5 8388608 1560668 1560670 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz118) Bool.false 22544413 8388608 5 8388608 22544413 8388608 5 8388608 (Ns96p880 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns96p882 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz118)) Bool.false 3121338 8388608 2 8388608 1560669 4194304 1 4194304 (Ns96p881 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz119 := (@HMul.hMul Real Real Real qz339 qz337 qz453)

noncomputable abbrev qz698 := (@HMul.hMul Real Real Real qz863 qz895 qz895)

noncomputable abbrev qz461 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz698 qz692) qz641)

noncomputable abbrev qz120 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz461))

noncomputable def Ns96p883 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz115) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz119)) qz120) Bool.false 290931851925 

noncomputable def Ns96p884 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz119)) qz120 767195 131072 2603 

noncomputable def Ns96p885 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz119)) Bool.false 49100480 8388608 5206 8388608 767195 131072 2603 

noncomputable def Ns96p886 := @Enclosure.Real.IsNear.recentre' (Real.cos qz119) Bool.false 716579 4194304 183838608 10150215680000 716579 4194304 11489913 634388480000 

noncomputable def Ns96p887 := @Enclosure.Real.IsNear.cos_image qz119 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11736569) qz357) Bool.false 11736569 8388608 145 8388608 Bool.false 716579 4194304 1 

noncomputable def Ns96p888 := nat_lit 620679734424058467761124577 

noncomputable def Ns96p889 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz115 884279719003555 140737488355328 1 500000000000000 1867933 8388608 23 8388608 1651775268357467501815 1180591620717411303424 Ns96p888 

noncomputable def Ns96p890 := @Enclosure.Real.IsNear.subLit_ff_p qz118 qz1 60588189 8388608 23 8388608 7 1 0 1 1867933 1867933 8388608 23 

noncomputable def Ns96p891 := @Ns96p890 8388608 (@Enclosure.Real.IsNear.recentre' qz118 Bool.false 60588189 8388608 23 8388608 60588189 8388608 23 8388608 (Ns96p879 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns96p892 := @Enclosure.Real.IsNear.recentre' qz119 Bool.false 1651775268357467501815 1180591620717411303424 Ns96p888 Ns96p148 11736569 8388608 145 8388608 (@Ns96p889 Ns96p148 RS097to114.d35 (Ns96p891 rfl rfl) rfl) 

noncomputable def Ns96p893 := nat_lit 158205995782404226729658576406449665083331345067465988515521 

noncomputable def Ns96p894 := nat_lit 360022174631916122992321712068642387131476548125803816641 

noncomputable def Ns96p895 := nat_lit 473897942997948847942991085795211710475731082106146357913281 

noncomputable def Ns96p896 := BSN.cos_dyadic_bound_f 11736569 8388608 3 2 4194304 1210000 Ns96p893 Ns96p262 Ns96p894 Ns96p895 Ns96p265 Ns96p894 716579 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 11736569) (BSN.cosEvenQ 8388608) 0 2 Ns96p893 Ns96p262 Ns96p894 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 11736569) (BSN.cosOddQ 8388608) 0 2 Ns96p895 Ns96p265 Ns96p894 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p897 := @Enclosure.Real.IsNear.inv_image (Real.cos qz119) 716579 4194304 11489913 634388480000 24547637 24552843 4194304 (Ns96p886 (@Ns96p887 1210000 (Ns96p892 rfl) (Enclosure.sfrac_false_div 11736569 8388608) (Ns96p896 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns96p898 := @Enclosure.Real.IsNear.recentre' qz120 Bool.false 379215 4194304 

noncomputable abbrev qz121 := (@HMul.hMul Real Real Real qz339 qz337 qz461)

noncomputable def Ns96p899 := @Enclosure.Real.IsNear.cos_image qz121 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 12417327)) qz357) Bool.true 12417327 8388608 

noncomputable def Ns96p900 := nat_lit 14659793031000439957520499845 

noncomputable def Ns96p901 := nat_lit 1505085915586631372323354639130429 

noncomputable def Ns96p902 := @Enclosure.Real.IsNear.recentre' qz121 Bool.true Ns96p900 Ns96p163 Ns96p901 

noncomputable abbrev qz122 := qz461

noncomputable def Ns96p903 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz122 884279719003555 140737488355328 1 500000000000000 16578230525879 

noncomputable abbrev qz462 := (@HSub.hSub Real Real Real qz635 qz698 qz692)

noncomputable abbrev qz123 := qz462

noncomputable def Ns96p904 := @Enclosure.Real.IsNear.subLit_tf qz123 qz26 12180184014775 70368744177664 278863431 70368744177664 1 16 

noncomputable abbrev qz463 := qz698

noncomputable abbrev qz124 := qz463

noncomputable def Ns96p905 := @Enclosure.Real.IsNear.subLit_ff_n qz124 qz115 3489173692489 70368744177664 85925447 70368744177664 1867933 8388608 23 8388608 

noncomputable def Ns96p906 := @Enclosure.Real.IsNear.mulLit_ff qz115 qz115 1867933 8388608 23 8388608 1867933 8388608 23 8388608 3489173692489 70368744177664 

noncomputable def Ns96p907 := nat_lit 11668023285168981306091412029416575024542151166786962922718931582814369075892553573288715201 

noncomputable def Ns96p908 := nat_lit 58158844227896986633558482781719779619497718984807332131428259197799420928759449934993817600 

noncomputable def Ns96p909 := nat_lit 13438086016789667856645831632239045952328256852386122333921696437524255782627233833921 

noncomputable def Ns96p910 := nat_lit 70651459174887216101034285353327837936279510716756511082873253409373568681751358431805907905 

noncomputable def Ns96p911 := nat_lit 5292454824738625783653821933136499945374292427617467223959971586999747304517109944084437401600 

noncomputable def Ns96p912 := BSN.cos_dyadic_bound_f 12417327 8388608 4 3 4194304 1210000 Ns96p907 Ns96p908 Ns96p909 Ns96p910 Ns96p911 Ns96p909 379215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 12417327) (BSN.cosEvenQ 8388608) 0 3 Ns96p907 Ns96p908 Ns96p909 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 12417327) (BSN.cosOddQ 8388608) 0 3 Ns96p910 Ns96p911 Ns96p909 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p913 := @Ns96p898 131244304 5075107840000 379215 4194304 8202769 317194240000 (@Ns96p899 105 4194304 Bool.false 379215 4194304 1 1210000 (@Ns96p902 Ns96p166 12417327 8388608 105 4194304 (@Ns96p903 70368744177664 278863431 70368744177664 Ns96p900 Ns96p163 Ns96p901 Ns96p166 RS097to114.d35 (@Ns96p904 0 1 265251688414064 16578230525879 70368744177664 278863431 70368744177664 (@Ns96p905 102174789067813683200 12180184014775 70368744177664 278863431 70368744177664 (@Ns96p906 85925447 70368744177664 (Ns96p891 rfl rfl) (Ns96p891 rfl rfl) rfl) (Ns96p891 rfl rfl) rfl rfl) qz369 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 12417327 8388608) (BSN.cos_neg_of_bound 12417327 8388608 Bool.false 379215 4194304 1 1210000 (Ns96p912 rfl rfl)) rfl rfl) 

noncomputable def Ns96p914 := @Ns96p877 5394097033725178533 69751751028714242048000 (Ns96p878 qz28 (@Enclosure.Real.IsNear.of_eq qz696 (@Inv.inv Real Real.instInv (Real.sqrt qz118)) Bool.false 1560669 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz114 (BSN.t_div_two_pi_nonneg qz113 327775 1000 qz116)) Ns96p882) rfl) (@Ns96p883 549755813888 34506310400049 166301133701120000 (BSN.correction_mk qz115 (BSN.cos_two_pi_p_ne_zero_mk qz113 327775 1000 7 qz116 rfl rfl (@BSN.floor_sqrt_eq_dec qz113 327775 1000 7 qz116 rfl rfl rfl))) (@Ns96p884 4194304 379215 4194304 8202769 317194240000 290931851925 549755813888 34506310400049 166301133701120000 (@Ns96p885 4194304 (Ns96p897 rfl rfl rfl rfl rfl) rfl) (Ns96p913 rfl) rfl)) 

noncomputable def Ns96p915 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz113) (hardyZApproximantRS₀ qz113) Bool.false 3260941185584840737 2305843009213693952 131710201900582138533 69751751028714242048000 (@Eq.refl Real (hardyZApproximantRS₀ qz113)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz113) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz113) qz113 7) (@HMul.hMul Real Real Real qz5 qz693 (Zeta.RiemannSiegel.correction qz115))) Bool.false 3260941185584840737 2305843009213693952 131710201900582138533 69751751028714242048000 (BSN.hardyZApproximantRS₀_eq qz113 7 (@BSN.floor_sqrt_eq_dec qz113 327775 1000 7 qz116 rfl rfl rfl)) (@Ns96p816 3260941185584840737 2305843009213693952 131710201900582138533 69751751028714242048000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz113) qz113 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 7)) Bool.false 40845667 33554432 60765 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz113) qz113 7) (Ns96p876 (Ns96p875 rfl) rfl rfl)) (Ns96p914 rfl) rfl rfl)) 

theorem RS097to114.d46 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz113) Bool.false 3260941185584840737 2305843009213693952 131710201900582138533 69751751028714242048000 := Ns96p915 

noncomputable def Ns96p916 := nat_lit 316486797000630775865933824 

noncomputable abbrev qz897 := (Enclosure.sfrac Bool.false 329363 1000)

noncomputable abbrev qz699 := qz897

noncomputable abbrev qz464 := qz699

noncomputable abbrev qz125 := qz464

noncomputable abbrev qz898 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 329363 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz700 := qz898

noncomputable abbrev qz465 := qz700

noncomputable abbrev qz126 := qz465

noncomputable abbrev qz899 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 329363 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz701 := qz899

noncomputable abbrev qz466 := qz701

noncomputable abbrev qz127 := qz466

noncomputable abbrev qz702 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz126 qz9))

noncomputable def Ns96p917 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz125) qz125 7) (@HMul.hMul Real Real Real qz5 qz702 (Zeta.RiemannSiegel.correction qz127)) 5879431 8388608 61049 33554432 13987855771005882645 73786976294838206464 113460135079457600877 507285462027012669440000 Ns96p916 

noncomputable def Ns96p918 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz125) qz125 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 329363 1000 65 98 67108864 33554432 1125899906842624 Bool.false 32678432801 1244 

noncomputable def Ns96p919 := Ns96p918 120242927 57 27397080 8 130587807 57 25364760 8 Bool.false 26140038 45291 Bool.true 73205155 Bool.true 1752083 3537118876014220 1 Bool.false 59526631 Bool.true Bool.false 67085993 Bool.true Bool.true 23517724 

noncomputable def Ns96p920 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz125) qz125 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 329363 1000 19 27 67108864 33554432 1125899906842624 Bool.false 32678432801 1244 

noncomputable def Ns96p921 := Ns96p920 93032624 56 33554424 8 108007536 56 30011992 8 Bool.true 10205843 26622 Bool.false 34055878 Bool.true 49065637 3537118876014220 1 Bool.false 32612860 Bool.false Bool.false 44809591 Bool.false Bool.false 26140038 

noncomputable def Ns96p922 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz125) qz125 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 329363 1000 164 79 67108864 33554432 1125899906842624 Bool.false 32678432801 1244 

noncomputable def Ns96p923 := Ns96p922 46516304 56 47453136 16 73726608 56 38745320 8 Bool.true 67108856 1304 Bool.false 69728807 Bool.false 67881802 3537118876014220 1 Bool.false 34027399 Bool.false Bool.false 56884027 Bool.false Bool.true 10205843 

noncomputable def Ns96p924 := nat_lit 50392450048236099130646852526274869725755800527327647171 

noncomputable def Ns96p925 := nat_lit 103486605292648759739132950853445860248892737585152000 

noncomputable def Ns96p926 := nat_lit 1860449224650342022042939060640000 

noncomputable def Ns96p927 := nat_lit 3676582781958215652875770404273433920 

noncomputable abbrev qz703 := (@Eq.refl Real qz897)

noncomputable abbrev qz467 := qz703

noncomputable abbrev qz128 := qz467

noncomputable def Ns96p928 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz125 329363 1000 433920943076 16000000 658726 4000 2000 Ns96p926 Ns96p927 qz128 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns96p929 := nat_lit 16125584015435551721806992808407958312241856168744847094720 

noncomputable abbrev qz704 := (Real.log (Enclosure.sfrac Bool.false 433920943076 16000000))

noncomputable abbrev qz129 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 329363 4000) qz704) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 658726))))))

noncomputable abbrev qz705 := (Enclosure.sfrac Bool.false 329363 2000)

noncomputable abbrev qz468 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz129 qz705) (@HMul.hMul Real Real Real qz5 qz705 (Real.log Real.pi)))

noncomputable def Ns96p930 := @Enclosure.Real.IsNear.addLit_ft_p qz468 (Enclosure.sfrac Bool.true Ns96p926 Ns96p927) 4386029563105234837491 9007199254740992000 2295776434010473407 123904000000000000000000 Ns96p926 Ns96p927 0 1 Ns96p929 

noncomputable def Ns96p931 := nat_lit 58868292290081724479449124044800 

noncomputable abbrev qz469 := (@HSub.hSub Real Real Real qz12 qz129 qz705)

noncomputable abbrev qz470 := (@HMul.hMul Real Real Real qz5 qz705 (Real.log Real.pi))

noncomputable def Ns96p932 := @Enclosure.Real.IsNear.subLit_ff_p qz469 qz470 1216805848778138909079 1801439850948198400 2108519029000711 242000000000000000000 12651083475243 67108864000 329363 33554432000 Ns96p931 4386029563105234837491 9007199254740992000 

noncomputable def Ns96p933 := nat_lit 12168058487781389090790000 

noncomputable abbrev qz471 := qz705

noncomputable def Ns96p934 := @Enclosure.Real.IsNear.subLit_ff_p qz129 qz471 7567348327960323219443 9007199254740992000 2108519029000711 242000000000000000000 329363 2000 0 1 Ns96p933 1216805848778138909079 1801439850948198400 2108519029000711 242000000000000000000 

noncomputable def Ns96p935 := nat_lit 17040153554992428803999460929635876864 

noncomputable def Ns96p936 := nat_lit 12340749687511186860408832 

noncomputable def Ns96p937 := nat_lit 277537777888863629503733686021358296320457175193846000046993046305613252166596957587001027231129574409397313995083764203520 

noncomputable def Ns96p938 := nat_lit 5849465170558548660329217302668828611639017189532946292949502007989851554234427898747093846232773725536667481995035541504 

noncomputable def Ns96p939 := nat_lit 21138808609271276569518597138662436606390435675559549112807963907875306823456234368403283408617677671452478742200320 

noncomputable def Ns96p940 := BSN.log_dyadic_bound 171776943076 696064943076 6 5 Ns96p937 33554432 9680000 Ns96p938 Ns96p939 16910372 867841886152 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 171776943076) (BSN.artanhQ 696064943076) 0 5 Ns96p938 Ns96p937 Ns96p939 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns96p941 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 329363 4000) qz704 329363 4000 0 1 22986437543316161 2251799813685248 6250000847 60500000000000000 7570882028579240735443 9007199254740992000 2058519028970461 242000000000000000000 (Enclosure.Real.IsNear.const Bool.false 329363 4000) (BSN.isNear_log_sfrac 433920943076 16000000 22986437543316161 2251799813685248 6250000847 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 433920943076) qz350)) Bool.false Ns96p936 Ns96p86 1000000135520000 9680000000000000000000 22986437543316161 2251799813685248 6250000847 60500000000000000 (BSN.log_rat_reduce_isNear 433920943076 16000000 14 867841886152 524288000000 16910372 33554432 24973259072661432 36028797018963968 9680000 1000000000000000 rfl rfl rfl rfl (Ns96p940 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p942 := BSN.arctan_dyadic_bound_f 1000 658726 1 0 4194304 1210000 0 1 1 0 1 1 6367 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 658726) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 658726) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz472 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 658726)))

noncomputable def Ns96p943 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz472 884279719003555 562949953421312 1 2000000000000000 6367 4194304 1 1210000 3705353660182053257216 883425154729379 562949953421312 200000000121 242000000000000000 qz17 (Ns96p942 rfl) rfl rfl 

noncomputable def Ns96p944 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 329363 4000) qz704) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz472)) 7570882028579240735443 9007199254740992000 2058519028970461 242000000000000000000 883425154729379 2251799813685248 200000000121 968000000000000000 Ns96p935 7567348327960323219443 9007199254740992000 2108519029000711 242000000000000000000 (Ns96p941 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz472) 1 4 0 1 883425154729379 562949953421312 200000000121 242000000000000000 883425154729379 2251799813685248 200000000121 968000000000000000 qz353 Ns96p943 rfl) 

noncomputable def Ns96p945 := @Ns96p930 Ns96p924 Ns96p925 2295776434010473407 123904000000000000000000 (@Ns96p932 2295776434010473407 123904000000000000000000 (Ns96p934 (Ns96p944 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 329363 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz471 (Real.log Real.pi) 329363 2000 0 1 38410761 33554432 1 16777216 12651083475243 67108864000 329363 33554432000 (Enclosure.Real.IsNear.const Bool.false 329363 2000) RS097to114.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns96p926 Ns96p927) 

noncomputable def Ns96p946 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz125) Bool.false Ns96p924 Ns96p925 2295776434010473407 123904000000000000000000 1021201025 2097152 39 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz125) (@HAdd.hAdd Real Real Real qz354 qz468 (Enclosure.sfrac Bool.true Ns96p926 Ns96p927)) Bool.false Ns96p924 Ns96p925 2295776434010473407 123904000000000000000000 Ns96p928 (Ns96p945 rfl rfl)) 

noncomputable def Ns96p947 := nat_lit 139893692512624737661299730748025935862145887861253656854435531886217542522131425230625 

noncomputable def Ns96p948 := nat_lit 280884729092292821210022670834088203167900613450612740721344514354170926392125390625 

noncomputable def Ns96p949 := nat_lit 365933476543105838830968781920622260643348343405315728276639454297805858439042672590625 

noncomputable def Ns96p950 := BSN.sin_dyadic_bound_f 26981495405 17179869184 3 2 8388608 2422364 Ns96p947 Ns96p99 Ns96p948 Ns96p949 Ns96p102 Ns96p948 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26981495405) qz355 0 2 Ns96p947 Ns96p99 Ns96p948 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26981495405) qz356 0 2 Ns96p949 Ns96p102 Ns96p948 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz706 := (@Nat.cast Real Real.instNatCast 2097152)

noncomputable def Ns96p951 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz125) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1021201025) qz706) Bool.false 1021201025 2097152 39 2097152 Bool.true 8388607 8388608 1 1210000 (Ns96p946 rfl) (Enclosure.sfrac_false_div 1021201025 2097152) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1021201025) qz706) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474663486928222274191360) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 77 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q1 1021201025 2097152 226375608064910080 72057594037927936 77 474663486928222274191360 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 474663486928222274191360 302231454903657293676544 26981495405 17179869184 2422364 2420000 (Ns96p950 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p952 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz125) Bool.false Ns96p924 Ns96p925 2295776434010473407 123904000000000000000000 32678432801 67108864 1244 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz125) (@HAdd.hAdd Real Real Real qz354 qz468 (Enclosure.sfrac Bool.true Ns96p926 Ns96p927)) Bool.false Ns96p924 Ns96p925 2295776434010473407 123904000000000000000000 Ns96p928 (Ns96p945 rfl rfl)) 

noncomputable def Ns96p953 := Ns96p923 26622 BSN.abs_quadSignPos (BSN.cos_quad_nat0 164 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 34027399 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 79 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 56884027 67108864) qz128 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz125) qz125 1) Bool.true 8388607 8388608 3080447 158597120000 67108856 67108864 1304 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz125) qz125 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz125)) Bool.true 8388607 8388608 3080447 158597120000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz125) qz125) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz125)) Bool.true 8388607 8388608 49287152 2537553920000 8388607 8388608 3080447 158597120000 (Ns96p951 rfl rfl) rfl)) rfl) (Ns96p952 rfl) RS097to114.d7 

noncomputable def Ns96p954 := nat_lit 806081528680868537087114559367165267902088916388311525319393938881 

noncomputable def Ns96p955 := nat_lit 558853376104080736103323571491193193821234954852349190614552001 

noncomputable def Ns96p956 := nat_lit 2417126879290397449789137030958513417318624279255229877576952712641 

noncomputable def Ns96p957 := BSN.cos_dyadic_bound_f 69728807 67108864 3 2 67108864 33554432 Ns96p954 Ns96p108 Ns96p955 Ns96p956 Ns96p111 Ns96p955 34027399 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 69728807) qz359 0 2 Ns96p954 Ns96p108 Ns96p955 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 69728807) (BSN.cosOddQ 67108864) 0 2 Ns96p956 Ns96p111 Ns96p955 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p958 := nat_lit 1302762077323853800662075848601196843543012551382190471715694240000 

noncomputable def Ns96p959 := nat_lit 450844629963885417388918297894252514597497184348327601717043456 

noncomputable def Ns96p960 := nat_lit 3411265977875866044391568973854162943303303591512030133614514462976 

noncomputable def Ns96p961 := BSN.sin_dyadic_bound_f 67881802 67108864 3 2 67108864 33554432 Ns96p958 Ns96p221 Ns96p959 Ns96p960 Ns96p224 Ns96p959 56884027 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 67881802) qz360 0 2 Ns96p958 Ns96p221 Ns96p959 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 67881802) (BSN.sinOddQ 67108864) 0 2 Ns96p960 Ns96p224 Ns96p959 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p962 := nat_lit 1345142596011498785719487581456 

noncomputable def Ns96p963 := BSN.sin_dyadic_bound_f 34055878 67108864 2 1 67108864 33554432 Ns96p962 Ns96p127 Ns96p962 Ns96p962 Ns96p128 Ns96p962 32612860 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 34055878) qz360 0 1 Ns96p962 Ns96p127 Ns96p962 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 34055878) (BSN.sinOddQ 67108864) 0 1 Ns96p962 Ns96p128 Ns96p962 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p964 := nat_lit 355510259657610753752357524698173721477322090162736439607827166945 

noncomputable def Ns96p965 := nat_lit 33590736947971268215914919274094393898463325047144333765572321 

noncomputable def Ns96p966 := nat_lit 931043914100588592060015369102106451040960343138042917670593558241 

noncomputable def Ns96p967 := BSN.sin_dyadic_bound_f 49065637 67108864 3 2 67108864 33554432 Ns96p964 Ns96p221 Ns96p965 Ns96p966 Ns96p224 Ns96p965 44809591 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 49065637) qz360 0 2 Ns96p964 Ns96p221 Ns96p965 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 49065637) (BSN.sinOddQ 67108864) 0 2 Ns96p966 Ns96p224 Ns96p965 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p968 := Ns96p921 45291 BSN.abs_quadSignPos (BSN.cos_quad_nat3 19 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 32612860 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 27 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 44809591 67108864) qz128 rfl rfl (Ns96p953 RS097to114.d9 RS097to114.d11 RS097to114.d13 RS097to114.d17 (Ns96p957 rfl rfl) (Ns96p961 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns96p952 rfl) RS097to114.d19 RS097to114.d21 RS097to114.d23 RS097to114.d25 RS097to114.d17 (Ns96p963 rfl rfl) (Ns96p967 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns96p969 := nat_lit 1762265336972440782128736078956308752528411110736169855954250430625 

noncomputable def Ns96p970 := nat_lit 824770874556424775994290560970789647911104928219293845875390625 

noncomputable def Ns96p971 := nat_lit 4614121491607110694033175164929713073382553977282375527939238590625 

noncomputable def Ns96p972 := BSN.sin_dyadic_bound_f 73205155 67108864 3 2 67108864 33554432 Ns96p969 Ns96p221 Ns96p970 Ns96p971 Ns96p224 Ns96p970 59526631 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 73205155) qz360 0 2 Ns96p969 Ns96p221 Ns96p970 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 73205155) (BSN.sinOddQ 67108864) 0 2 Ns96p971 Ns96p224 Ns96p970 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p973 := nat_lit 9423640352869541466754321 

noncomputable def Ns96p974 := BSN.cos_dyadic_bound_f 1752083 67108864 2 1 67108864 33554432 Ns96p973 Ns96p131 Ns96p973 Ns96p973 Ns96p132 Ns96p973 67085993 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1752083) qz359 0 1 Ns96p973 Ns96p131 Ns96p973 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1752083) (BSN.cosOddQ 67108864) 0 1 Ns96p973 Ns96p132 Ns96p973 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p975 := Ns96p919 61049 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 65 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 59526631 67108864) BSN.abs_quadSignNeg qz636 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 67085993 67108864) qz128 rfl rfl (Ns96p968 rfl rfl) (Ns96p952 rfl) RS097to114.d27 RS097to114.d29 RS097to114.d31 RS097to114.d33 RS097to114.d17 (Ns96p972 rfl rfl) (Ns96p974 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns96p976 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz125) qz125 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz125) qz125 7) 23517724 67108864 61049 67108864 23517724 67108864 61049 67108864 3156495483011072 5879431 8388608 61049 33554432 (Ns96p975 rfl) 

noncomputable def Ns96p977 := @Enclosure.Real.IsNear.mulLit_tf qz702 (Zeta.RiemannSiegel.correction qz127) 1558785 4194304 1 4194304 8973563237397 17592186044416 72747921672507 120946279055360000 13987855771005882645 73786976294838206464 

noncomputable abbrev qz707 := (@HPow.hPow Real Real Real qz7 qz126 qz9)

noncomputable def Ns96p978 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz707 1 1 0 1 1558785 4194304 1 4194304 1558785 4194304 1 4194304 

noncomputable def Ns96p979 := @Enclosure.Real.IsNear.sqrt_image qz126 439728918307 8388608000 329363 8388608000 30367378 30367402 4194304 (@Enclosure.Real.IsNear.of_eq qz126 (@HMul.hMul Real Real Real qz5 qz125 qz3) Bool.false 439728918307 8388608000 329363 8388608000 (BSN.t_div_two_pi_mk qz125 329363 1000 qz128) (@Enclosure.Real.IsNear.mulLit_ff qz125 qz3 329363 1000 0 1 1335089 8388608 1 8388608 439728918307 8388608000 329363 8388608000 (Enclosure.Real.IsNear.const Bool.false 329363 1000) RS097to114.d36 rfl)) 

noncomputable abbrev qz900 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 329363 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz708 := qz900

noncomputable abbrev qz473 := qz708

noncomputable abbrev qz130 := qz473

noncomputable def Ns96p980 := @Enclosure.Real.IsNear.sqrt_image qz130 15183695 2097152 3 1048576 11285832 11285837 4194304 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 60734780 8388608 24 8388608 15183695 2097152 3 1048576 (Ns96p979 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns96p981 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz130) 22571669 8388608 5 8388608 1558784 1558786 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz130) Bool.false 22571669 8388608 5 8388608 22571669 8388608 5 8388608 (Ns96p980 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns96p982 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz130)) Bool.false 3117570 8388608 2 8388608 1558785 4194304 1 4194304 (Ns96p981 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz131 := (@HMul.hMul Real Real Real qz339 qz337 qz466)

noncomputable abbrev qz709 := (@HMul.hMul Real Real Real qz863 qz899 qz899)

noncomputable abbrev qz474 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz709 qz701) qz641)

noncomputable abbrev qz132 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz474))

noncomputable def Ns96p983 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz127) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz131)) qz132) Bool.false 8973563237397 

noncomputable def Ns96p984 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz131)) qz132 135628119 8388608 41547 

noncomputable def Ns96p985 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz131)) Bool.false 135628119 8388608 41547 8388608 135628119 8388608 41547 

noncomputable def Ns96p986 := @Enclosure.Real.IsNear.recentre' (Real.cos qz131) Bool.false 259418 4194304 24038576 1268776960000 129709 2097152 1502411 79298560000 

noncomputable def Ns96p987 := @Enclosure.Real.IsNear.cos_image qz131 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12657627) qz357) Bool.false 12657627 8388608 19 1048576 Bool.false 259418 4194304 1 

noncomputable def Ns96p988 := nat_lit 80958226229295215039758677 

noncomputable def Ns96p989 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz127 884279719003555 140737488355328 1 500000000000000 503631 2097152 3 1048576 445350679161479408205 295147905179352825856 Ns96p988 

noncomputable def Ns96p990 := @Enclosure.Real.IsNear.subLit_ff_p qz130 qz1 15183695 2097152 3 1048576 7 1 0 1 503631 503631 2097152 3 

noncomputable def Ns96p991 := @Ns96p990 1048576 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 60734780 8388608 24 8388608 15183695 2097152 3 1048576 (Ns96p979 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns96p992 := @Enclosure.Real.IsNear.recentre' qz131 Bool.false 445350679161479408205 295147905179352825856 Ns96p988 Ns96p487 12657627 8388608 19 1048576 (@Ns96p989 Ns96p487 RS097to114.d35 (Ns96p991 rfl rfl) rfl) 

noncomputable def Ns96p993 := nat_lit 12600642195644788190002967749752221065180938449868825318108458973016213539314134084811714001 

noncomputable def Ns96p994 := nat_lit 16913267696715730386013814540318212121980244411238957738928005533246349196217843936721 

noncomputable def Ns96p995 := nat_lit 76287043792246476700958826789943777912788147424712830111746288967606795380568226358902615505 

noncomputable def Ns96p996 := BSN.cos_dyadic_bound_f 12657627 8388608 4 3 4194304 1210000 Ns96p993 Ns96p908 Ns96p994 Ns96p995 Ns96p911 Ns96p994 259418 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 12657627) (BSN.cosEvenQ 8388608) 0 3 Ns96p993 Ns96p908 Ns96p994 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 12657627) (BSN.cosOddQ 8388608) 0 3 Ns96p995 Ns96p911 Ns96p994 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p997 := @Enclosure.Real.IsNear.inv_image (Real.cos qz131) 129709 2097152 1502411 79298560000 67793286 67834833 4194304 (Ns96p986 (@Ns96p987 1210000 (Ns96p992 rfl) (Enclosure.sfrac_false_div 12657627 8388608) (Ns96p996 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns96p998 := @Enclosure.Real.IsNear.recentre' qz132 Bool.false 132326 4194304 

noncomputable abbrev qz133 := (@HMul.hMul Real Real Real qz339 qz337 qz474)

noncomputable def Ns96p999 := @Enclosure.Real.IsNear.cos_image qz133 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 12912097)) qz357) Bool.true 12912097 8388608 

noncomputable def Ns96p1000 := nat_lit 952744617920805487737425725 

noncomputable def Ns96p1001 := nat_lit 618970019642690137449562112 

noncomputable def Ns96p1002 := nat_lit 12566416833433052484429835462457 

noncomputable def Ns96p1003 := @Enclosure.Real.IsNear.recentre' qz133 Bool.true Ns96p1000 Ns96p1001 Ns96p1002 

noncomputable def Ns96p1004 := nat_lit 472236648286964521369600000000000000 

noncomputable abbrev qz134 := qz474

noncomputable def Ns96p1005 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz134 884279719003555 140737488355328 1 500000000000000 1077424481695 

noncomputable abbrev qz475 := (@HSub.hSub Real Real Real qz635 qz709 qz701)

noncomputable abbrev qz135 := qz475

noncomputable def Ns96p1006 := @Enclosure.Real.IsNear.subLit_tf qz135 qz26 802546574751 4398046511104 2328315 549755813888 1 16 

noncomputable abbrev qz476 := qz709

noncomputable abbrev qz136 := qz476

noncomputable def Ns96p1007 := @Enclosure.Real.IsNear.subLit_ff_n qz136 qz127 253644184161 4398046511104 755451 549755813888 503631 2097152 3 1048576 

noncomputable def Ns96p1008 := @Enclosure.Real.IsNear.mulLit_ff qz127 qz127 503631 2097152 3 1048576 503631 2097152 3 1048576 253644184161 4398046511104 

noncomputable def Ns96p1009 := nat_lit 13648390073234700141340810147775333838335211410712205653586277973769645996912297126637358721 

noncomputable def Ns96p1010 := nat_lit 21476393834848308910745400212099662401985715073771259822881023715038452500329713127041 

noncomputable def Ns96p1011 := nat_lit 82616297358229223113297296854513565121781141585242729949814283533289052681636614097080700545 

noncomputable def Ns96p1012 := BSN.cos_dyadic_bound_f 12912097 8388608 4 3 4194304 1210000 Ns96p1009 Ns96p908 Ns96p1010 Ns96p1011 Ns96p911 Ns96p1010 132326 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 12912097) (BSN.cosEvenQ 8388608) 0 3 Ns96p1009 Ns96p908 Ns96p1010 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 12912097) (BSN.cosOddQ 8388608) 0 3 Ns96p1011 Ns96p911 Ns96p1010 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1013 := @Ns96p998 8732144 317194240000 66163 2097152 545759 19824640000 (@Ns96p999 7 262144 Bool.false 132326 4194304 1 1210000 (@Ns96p1003 Ns96p1004 12912097 8388608 7 262144 (@Ns96p1005 4398046511104 2328315 549755813888 Ns96p1000 Ns96p1001 Ns96p1002 Ns96p1004 RS097to114.d35 (@Ns96p1006 0 1 17238791707120 1077424481695 4398046511104 2328315 549755813888 (@Ns96p1007 1683062154332209152 802546574751 4398046511104 2328315 549755813888 (@Ns96p1008 755451 549755813888 (Ns96p991 rfl rfl) (Ns96p991 rfl rfl) rfl) (Ns96p991 rfl rfl) rfl rfl) qz369 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 12912097 8388608) (BSN.cos_neg_of_bound 12912097 8388608 Bool.false 132326 4194304 1 1210000 (Ns96p1012 rfl rfl)) rfl rfl) 

noncomputable def Ns96p1014 := @Ns96p977 113460135079457600877 507285462027012669440000 (Ns96p978 qz28 (@Enclosure.Real.IsNear.of_eq qz707 (@Inv.inv Real Real.instInv (Real.sqrt qz130)) Bool.false 1558785 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz126 (BSN.t_div_two_pi_nonneg qz125 329363 1000 qz128)) Ns96p982) rfl) (@Ns96p983 17592186044416 72747921672507 120946279055360000 (BSN.correction_mk qz127 (BSN.cos_two_pi_p_ne_zero_mk qz125 329363 1000 7 qz128 rfl rfl (@BSN.floor_sqrt_eq_dec qz125 329363 1000 7 qz128 rfl rfl rfl))) (@Ns96p984 8388608 66163 2097152 545759 19824640000 8973563237397 17592186044416 72747921672507 120946279055360000 (@Ns96p985 8388608 (Ns96p997 rfl rfl rfl rfl rfl) rfl) (Ns96p1013 rfl) rfl)) 

noncomputable def Ns96p1015 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz125) (hardyZApproximantRS₀ qz125) Bool.true 37728166222647521003 73786976294838206464 1036416308835791680877 507285462027012669440000 (@Eq.refl Real (hardyZApproximantRS₀ qz125)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz125) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz125) qz125 7) (@HMul.hMul Real Real Real qz5 qz702 (Zeta.RiemannSiegel.correction qz127))) Bool.true 37728166222647521003 73786976294838206464 1036416308835791680877 507285462027012669440000 (BSN.hardyZApproximantRS₀_eq qz125 7 (@BSN.floor_sqrt_eq_dec qz125 329363 1000 7 qz128 rfl rfl rfl)) (@Ns96p917 37728166222647521003 73786976294838206464 1036416308835791680877 507285462027012669440000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz125) qz125 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz125) qz125 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz125) qz125 7)) Bool.true 5879431 8388608 61049 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz125) qz125 7) (Ns96p976 (Ns96p975 rfl) rfl rfl)) (Ns96p1014 rfl) rfl rfl)) 

theorem RS097to114.d47 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz125) Bool.true 37728166222647521003 73786976294838206464 1036416308835791680877 507285462027012669440000 := Ns96p1015 

noncomputable def Ns96p1016 := nat_lit 820281738237208194283732992 

noncomputable abbrev qz901 := (Enclosure.sfrac Bool.false 330949 1000)

noncomputable abbrev qz710 := qz901

noncomputable abbrev qz477 := qz710

noncomputable abbrev qz137 := qz477

noncomputable abbrev qz902 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 330949 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz711 := qz902

noncomputable abbrev qz478 := qz711

noncomputable abbrev qz138 := qz478

noncomputable abbrev qz903 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 330949 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz712 := qz903

noncomputable abbrev qz479 := qz712

noncomputable abbrev qz139 := qz479

noncomputable abbrev qz713 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz138 qz9))

noncomputable def Ns96p1017 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz137) qz137 7) (@HMul.hMul Real Real Real qz5 qz713 (Zeta.RiemannSiegel.correction qz139)) 38332327 33554432 15337 8388608 3372881183578418455 18446744073709551616 14863185126810042687 50728546202701266944000 Ns96p1016 

noncomputable def Ns96p1018 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz137) qz137 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 330949 1000 65 97 67108864 33554432 1125899906842624 Bool.false 32889263233 1251 

noncomputable def Ns96p1019 := Ns96p1018 120242927 57 27397080 8 130587807 57 25364760 8 Bool.false 83166190 45513 Bool.true 53080005 Bool.true 103448270 3537118876014220 1 Bool.false 47716027 Bool.true Bool.false 67080065 Bool.true Bool.false 38332327 

noncomputable def Ns96p1020 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz137) qz137 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 330949 1000 19 27 67108864 33554432 1125899906842624 Bool.false 32889263233 1251 

noncomputable def Ns96p1021 := Ns96p1020 93032624 56 33554424 8 108007536 56 30011992 8 Bool.false 45604633 26753 Bool.false 97336568 Bool.true 9535157 3537118876014220 1 Bool.false 66623295 Bool.false Bool.false 9503106 Bool.false Bool.false 83166190 

noncomputable def Ns96p1022 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz137) qz137 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 330949 1000 165 80 67108864 33554432 1125899906842624 Bool.false 32889263233 1251 

noncomputable def Ns96p1023 := Ns96p1022 46516304 56 47453136 16 73726608 56 38745320 8 Bool.false 67108856 1312 Bool.false 101370024 Bool.false 56367476 3537118876014220 1 Bool.false 66987034 Bool.true Bool.false 44795627 Bool.false Bool.false 45604633 

noncomputable def Ns96p1024 := nat_lit 10440130940092507670485761830119641440447671015468378657 

noncomputable def Ns96p1025 := nat_lit 21302554649013637064932670882031579849126414227865600 

noncomputable def Ns96p1026 := nat_lit 1905676218968079779843358279520000 

noncomputable def Ns96p1027 := nat_lit 3784093864747297620164920119029186880 

noncomputable abbrev qz714 := (@Eq.refl Real qz901)

noncomputable abbrev qz480 := qz714

noncomputable abbrev qz140 := qz480

noncomputable def Ns96p1028 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz137 330949 1000 438109962404 16000000 661898 4000 2000 Ns96p1026 Ns96p1027 qz140 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns96p1029 := nat_lit 3340841900829602454555443785638285260943254724949881170240 

noncomputable abbrev qz715 := (Real.log (Enclosure.sfrac Bool.false 438109962404 16000000))

noncomputable abbrev qz141 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 330949 4000) qz715) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 661898))))))

noncomputable abbrev qz716 := (Enclosure.sfrac Bool.false 330949 2000)

noncomputable abbrev qz481 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz141 qz716) (@HMul.hMul Real Real Real qz5 qz716 (Real.log Real.pi)))

noncomputable def Ns96p1030 := @Enclosure.Real.IsNear.addLit_ft_p qz481 (Enclosure.sfrac Bool.true Ns96p1026 Ns96p1027) 882865344571411280673 1801439850948198400 2306708141045920761 123904000000000000000000 Ns96p1026 Ns96p1027 0 1 Ns96p1029 

noncomputable def Ns96p1031 := nat_lit 296240451695779889613750927360000 

noncomputable abbrev qz482 := (@HSub.hSub Real Real Real qz12 qz141 qz716)

noncomputable abbrev qz483 := (@HMul.hMul Real Real Real qz5 qz716 (Real.log Real.pi))

noncomputable def Ns96p1032 := @Enclosure.Real.IsNear.subLit_ff_p qz482 qz483 6120502876086979329957 9007199254740992000 2118431530344053 242000000000000000000 12712002942189 67108864000 330949 33554432000 Ns96p1031 882865344571411280673 1801439850948198400 

noncomputable def Ns96p1033 := nat_lit 12241005752173958659914000 

noncomputable abbrev qz484 := qz716

noncomputable def Ns96p1034 := @Enclosure.Real.IsNear.subLit_ff_p qz141 qz484 7610964669165617610661 9007199254740992000 2118431530344053 242000000000000000000 330949 2000 0 1 Ns96p1033 6120502876086979329957 9007199254740992000 2118431530344053 242000000000000000000 

noncomputable def Ns96p1035 := nat_lit 17138368823992142919332347742863228928 

noncomputable def Ns96p1036 := nat_lit 12352364543007769407520768 

noncomputable def Ns96p1037 := nat_lit 1878601849619465514474112749651555840794479478821431084579017793850177087503916552881053675728518646786872958480362269750368733410985699824537436160 

noncomputable def Ns96p1038 := nat_lit 41111324357965735069956499904689942877785812058333657011868339837292137666504907496338339929165143173765582612181879762648903739701060896871677952 

noncomputable def Ns96p1039 := nat_lit 9161540865593645900651016875433301702325853862057175237247923625642394888094075030697151345842103619702052717976895973046026053846638264320 

noncomputable def Ns96p1040 := BSN.log_dyadic_bound 175965962404 700253962404 7 6 Ns96p1037 33554432 9680000 Ns96p1038 Ns96p1039 17232749 876219924808 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 175965962404) (BSN.artanhQ 700253962404) 0 6 Ns96p1038 Ns96p1037 Ns96p1039 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns96p1041 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 330949 4000) qz715 330949 4000 0 1 23008071897565889 2251799813685248 6250000847 60500000000000000 7614498386427533398661 9007199254740992000 2068431530313803 242000000000000000000 (Enclosure.Real.IsNear.const Bool.false 330949 4000) (BSN.isNear_log_sfrac 438109962404 16000000 23008071897565889 2251799813685248 6250000847 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 438109962404) qz350)) Bool.false Ns96p1036 Ns96p86 1000000135520000 9680000000000000000000 23008071897565889 2251799813685248 6250000847 60500000000000000 (BSN.log_rat_reduce_isNear 438109962404 16000000 14 876219924808 524288000000 17232749 33554432 24973259072661432 36028797018963968 9680000 1000000000000000 rfl rfl rfl rfl (Ns96p1040 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p1042 := BSN.arctan_dyadic_bound_f 1000 661898 1 0 4194304 1210000 0 1 1 0 1 1 6336 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 661898) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 661898) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz485 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 661898)))

noncomputable def Ns96p1043 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz485 884279719003555 562949953421312 1 2000000000000000 6336 4194304 1 1210000 3705371111630609317888 883429315478947 562949953421312 200000000121 242000000000000000 qz17 (Ns96p1042 rfl) rfl rfl 

noncomputable def Ns96p1044 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 330949 4000) qz715) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz485)) 7614498386427533398661 9007199254740992000 2068431530313803 242000000000000000000 883429315478947 2251799813685248 200000000121 968000000000000000 Ns96p1035 7610964669165617610661 9007199254740992000 2118431530344053 242000000000000000000 (Ns96p1041 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz485) 1 4 0 1 883429315478947 562949953421312 200000000121 242000000000000000 883429315478947 2251799813685248 200000000121 968000000000000000 qz353 Ns96p1043 rfl) 

noncomputable def Ns96p1045 := @Ns96p1030 Ns96p1024 Ns96p1025 2306708141045920761 123904000000000000000000 (@Ns96p1032 2306708141045920761 123904000000000000000000 (Ns96p1034 (Ns96p1044 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 330949 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz484 (Real.log Real.pi) 330949 2000 0 1 38410761 33554432 1 16777216 12712002942189 67108864000 330949 33554432000 (Enclosure.Real.IsNear.const Bool.false 330949 2000) RS097to114.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns96p1026 Ns96p1027) 

noncomputable def Ns96p1046 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz137) Bool.false Ns96p1024 Ns96p1025 2306708141045920761 123904000000000000000000 256947369 524288 157 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz137) (@HAdd.hAdd Real Real Real qz354 qz481 (Enclosure.sfrac Bool.true Ns96p1026 Ns96p1027)) Bool.false Ns96p1024 Ns96p1025 2306708141045920761 123904000000000000000000 Ns96p1028 (Ns96p1045 rfl rfl)) 

noncomputable def Ns96p1047 := nat_lit 139902831613155197555522690722571704028018990808689227831917212748938433234335170158945 

noncomputable def Ns96p1048 := nat_lit 280921356520382672780294592881659711117841399878745693471971031171749769170246033761 

noncomputable def Ns96p1049 := nat_lit 365957352981040135937105617789688918636335137470572865579876175530084492177935523504481 

noncomputable def Ns96p1050 := BSN.sin_dyadic_bound_f 26981935179 17179869184 3 2 8388608 2422364 Ns96p1047 Ns96p99 Ns96p1048 Ns96p1049 Ns96p102 Ns96p1048 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26981935179) qz355 0 2 Ns96p1047 Ns96p99 Ns96p1048 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26981935179) qz356 0 2 Ns96p1049 Ns96p102 Ns96p1048 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1051 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz137) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 256947369) qz423) Bool.false 256947369 524288 157 8388608 Bool.false 8388607 8388608 1 1210000 (Ns96p1046 rfl) (Enclosure.sfrac_false_div 256947369 524288) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 256947369) qz423) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 118667805878174590435328) (@Nat.cast Real Real.instNatCast 75557863725914323419136)) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 77 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q3 256947369 524288 226375608064910080 72057594037927936 77 118667805878174590435328 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 118667805878174590435328 75557863725914323419136 26981935179 17179869184 2422364 2420000 (Ns96p1050 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p1052 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz137) Bool.false Ns96p1024 Ns96p1025 2306708141045920761 123904000000000000000000 32889263233 67108864 1251 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz137) (@HAdd.hAdd Real Real Real qz354 qz481 (Enclosure.sfrac Bool.true Ns96p1026 Ns96p1027)) Bool.false Ns96p1024 Ns96p1025 2306708141045920761 123904000000000000000000 Ns96p1028 (Ns96p1045 rfl rfl)) 

noncomputable def Ns96p1053 := Ns96p1023 26753 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 165 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66987034 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 80 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 44795627 67108864) qz140 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz137) qz137 1) Bool.false 8388607 8388608 12397413 634388480000 67108856 67108864 1312 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz137) qz137 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz137)) Bool.false 8388607 8388608 12397413 634388480000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz137) qz137) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz137)) Bool.false 8388607 8388608 198358608 10150215680000 8388607 8388608 12397413 634388480000 (Ns96p1051 rfl rfl) rfl)) rfl) (Ns96p1052 rfl) RS097to114.d7 

noncomputable def Ns96p1054 := nat_lit 2257998445485714192719114833678315000049929995024052547784147262127706117942467344792128427568111026176 

noncomputable def Ns96p1055 := nat_lit 1177374408711431664566991836821405241905857407931093840655686004167222108012303780079025390616576 

noncomputable def Ns96p1056 := nat_lit 11277992539842041004672632723058882610203705739938713431093020531190772931760773665297589081895323303936 

noncomputable def Ns96p1057 := BSN.sin_dyadic_bound_f 101370024 67108864 4 3 67108864 33554432 Ns96p1054 Ns96p762 Ns96p1055 Ns96p1056 Ns96p765 Ns96p1055 66987034 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 101370024) qz360 0 3 Ns96p1054 Ns96p762 Ns96p1055 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 101370024) (BSN.sinOddQ 67108864) 0 3 Ns96p1056 Ns96p765 Ns96p1055 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1058 := nat_lit 344089827768739053535286094523739270593051584572880458696380973056 

noncomputable def Ns96p1059 := nat_lit 101912794129256687784580993066696402582104588633793633336754176 

noncomputable def Ns96p1060 := nat_lit 1032065657717958647230289121585084418973990544541373788822469410816 

noncomputable def Ns96p1061 := BSN.cos_dyadic_bound_f 56367476 67108864 3 2 67108864 33554432 Ns96p1058 Ns96p108 Ns96p1059 Ns96p1060 Ns96p111 Ns96p1059 44795627 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 56367476) qz359 0 2 Ns96p1058 Ns96p108 Ns96p1059 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 56367476) (BSN.cosOddQ 67108864) 0 2 Ns96p1060 Ns96p111 Ns96p1059 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1062 := nat_lit 1919011553981399016503417687017780860252690686750719753010484634175824937272357660001999213756705406976 

noncomputable def Ns96p1063 := nat_lit 723289819165593604401484607995829120972829093957216170182954322292493293513168470235825754341376 

noncomputable def Ns96p1064 := nat_lit 9586386629323745575662649992585506286605435315133333379113360469658240866548927825487635824875443060736 

noncomputable def Ns96p1065 := BSN.sin_dyadic_bound_f 97336568 67108864 4 3 67108864 33554432 Ns96p1062 Ns96p762 Ns96p1063 Ns96p1064 Ns96p765 Ns96p1063 66623295 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 97336568) qz360 0 3 Ns96p1062 Ns96p762 Ns96p1063 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 97336568) (BSN.sinOddQ 67108864) 0 3 Ns96p1064 Ns96p765 Ns96p1063 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1066 := nat_lit 8266304386233712278476593201 

noncomputable def Ns96p1067 := BSN.sin_dyadic_bound_f 9535157 67108864 2 1 67108864 33554432 Ns96p1066 Ns96p127 Ns96p1066 Ns96p1066 Ns96p128 Ns96p1066 9503106 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 9535157) qz360 0 1 Ns96p1066 Ns96p127 Ns96p1066 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 9535157) (BSN.sinOddQ 67108864) 0 1 Ns96p1066 Ns96p128 Ns96p1066 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1068 := Ns96p1021 45513 BSN.abs_quadSignPos (BSN.cos_quad_nat3 19 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66623295 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 27 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 9503106 67108864) qz140 rfl rfl (Ns96p1053 RS097to114.d9 RS097to114.d11 RS097to114.d13 RS097to114.d17 (Ns96p1057 rfl rfl) (Ns96p1061 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns96p1052 rfl) RS097to114.d19 RS097to114.d21 RS097to114.d23 RS097to114.d25 RS097to114.d17 (Ns96p1065 rfl rfl) (Ns96p1067 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns96p1069 := nat_lit 486946626867323424947724831389493953060447264550409269416930630625 

noncomputable def Ns96p1070 := nat_lit 63015536894719921177266434768484116329824402250333175000390625 

noncomputable def Ns96p1071 := nat_lit 1275234378545160375943087555601906617065208834314095166189579590625 

noncomputable def Ns96p1072 := BSN.sin_dyadic_bound_f 53080005 67108864 3 2 67108864 33554432 Ns96p1069 Ns96p221 Ns96p1070 Ns96p1071 Ns96p224 Ns96p1070 47716027 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 53080005) qz360 0 2 Ns96p1069 Ns96p221 Ns96p1070 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 53080005) (BSN.sinOddQ 67108864) 0 2 Ns96p1071 Ns96p224 Ns96p1070 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1073 := nat_lit 2449297411707561642224840603499730616952378970763306383838696767435167724522874703924079190236326400000 

noncomputable def Ns96p1074 := nat_lit 1502030621234986212386548536682314503190074066346409396637034541982033049076700323921000000000000 

noncomputable def Ns96p1075 := nat_lit 12232371638190266738755966549770487990967711488600132577423518102413718185144092776676031066797632000000 

noncomputable def Ns96p1076 := BSN.sin_dyadic_bound_f 103448270 67108864 4 3 67108864 33554432 Ns96p1073 Ns96p762 Ns96p1074 Ns96p1075 Ns96p765 Ns96p1074 67080065 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 103448270) qz360 0 3 Ns96p1073 Ns96p762 Ns96p1074 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 103448270) (BSN.sinOddQ 67108864) 0 3 Ns96p1075 Ns96p765 Ns96p1074 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz486 := (BSN.cos_quad_nat1 97 rfl)

noncomputable def Ns96p1077 := Ns96p1019 61348 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 65 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 47716027 67108864) BSN.abs_quadSignNeg qz486 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 67080065 67108864) qz140 rfl rfl (Ns96p1068 rfl rfl) (Ns96p1052 rfl) RS097to114.d27 RS097to114.d29 RS097to114.d31 RS097to114.d33 RS097to114.d17 (Ns96p1072 rfl rfl) (Ns96p1076 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns96p1078 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz137) qz137 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz137) qz137 7) 38332327 67108864 61348 67108864 38332327 67108864 61348 67108864 5144877838893056 38332327 33554432 15337 8388608 (Ns96p1077 rfl) 

noncomputable def Ns96p1079 := @Enclosure.Real.IsNear.mulLit_tf qz713 (Zeta.RiemannSiegel.correction qz139) 778457 2097152 1 4194304 4332777768815 8796093022208 23856837973457 30236569763840000 3372881183578418455 18446744073709551616 

noncomputable abbrev qz717 := (@HPow.hPow Real Real Real qz7 qz138 qz9)

noncomputable def Ns96p1080 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz717 1 1 0 1 778457 2097152 1 4194304 778457 2097152 1 4194304 

noncomputable def Ns96p1081 := @Enclosure.Real.IsNear.sqrt_image qz138 441846369461 8388608000 330949 8388608000 30440405 30440429 4194304 (@Enclosure.Real.IsNear.of_eq qz138 (@HMul.hMul Real Real Real qz5 qz137 qz3) Bool.false 441846369461 8388608000 330949 8388608000 (BSN.t_div_two_pi_mk qz137 330949 1000 qz140) (@Enclosure.Real.IsNear.mulLit_ff qz137 qz3 330949 1000 0 1 1335089 8388608 1 8388608 441846369461 8388608000 330949 8388608000 (Enclosure.Real.IsNear.const Bool.false 330949 1000) RS097to114.d36 rfl)) 

noncomputable abbrev qz904 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 330949 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz718 := qz904

noncomputable abbrev qz487 := qz718

noncomputable abbrev qz142 := qz487

noncomputable def Ns96p1082 := @Enclosure.Real.IsNear.sqrt_image qz142 30440417 4194304 3 1048576 11299394 11299399 4194304 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 60880834 8388608 24 8388608 30440417 4194304 3 1048576 (Ns96p1081 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns96p1083 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz142) 22598793 8388608 5 8388608 1556913 1556915 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz142) Bool.false 22598793 8388608 5 8388608 22598793 8388608 5 8388608 (Ns96p1082 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns96p1084 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz142)) Bool.false 3113828 8388608 2 8388608 778457 2097152 1 4194304 (Ns96p1083 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz143 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz479))

noncomputable abbrev qz719 := (@HMul.hMul Real Real Real qz863 qz903 qz903)

noncomputable abbrev qz488 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz719 qz712) qz641)

noncomputable abbrev qz144 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz488))

noncomputable def Ns96p1085 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz139) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz143) qz144) Bool.false 4332777768815 

noncomputable def Ns96p1086 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz143) qz144 88321295 4194304 35237 

noncomputable abbrev qz720 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz143))

noncomputable def Ns96p1087 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz143) (@Neg.neg Real Real.instNeg qz720) Bool.true 88321295 4194304 35237 4194304 (BSN.inv_eq_neg_inv_neg qz143) 

noncomputable def Ns96p1088 := @Enclosure.Real.IsNear.recentre' qz720 Bool.false 176642590 8388608 70474 8388608 88321295 4194304 

noncomputable def Ns96p1089 := @Enclosure.Real.IsNear.recentre' qz143 Bool.true 199184 4194304 24038576 1268776960000 12449 262144 1502411 79298560000 

noncomputable abbrev qz145 := (@HMul.hMul Real Real Real qz339 qz337 qz479)

noncomputable def Ns96p1090 := @Enclosure.Real.IsNear.cos_image qz145 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13575311) qz357) Bool.false 13575311 8388608 19 1048576 Bool.true 199184 4194304 1 

noncomputable def Ns96p1091 := nat_lit 80958226229452039328121173 

noncomputable def Ns96p1092 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz139 884279719003555 140737488355328 1 500000000000000 1080289 4194304 3 1048576 955277653362631427395 590295810358705651712 Ns96p1091 

noncomputable def Ns96p1093 := @Enclosure.Real.IsNear.subLit_ff_p qz142 qz1 30440417 4194304 3 1048576 7 1 0 1 1080289 1080289 4194304 3 

noncomputable def Ns96p1094 := @Ns96p1093 1048576 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 60880834 8388608 24 8388608 30440417 4194304 3 1048576 (Ns96p1081 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns96p1095 := @Enclosure.Real.IsNear.recentre' qz145 Bool.false 955277653362631427395 590295810358705651712 Ns96p1091 Ns96p487 13575311 8388608 19 1048576 (@Ns96p1092 Ns96p487 RS097to114.d35 (Ns96p1094 rfl rfl) rfl) 

noncomputable def Ns96p1096 := nat_lit 16688392648020607494357130666980041431663834512986911063426599078737283672421625409560865601 

noncomputable def Ns96p1097 := nat_lit 39173957945043886713480561023741962179236336484327629657579080592123839498204964416321 

noncomputable def Ns96p1098 := nat_lit 100968285885241689408015244034341115800661126523793933407003903345711615695870024623636048705 

noncomputable def Ns96p1099 := BSN.cos_dyadic_bound_t 13575311 8388608 4 3 4194304 1210000 Ns96p1096 Ns96p908 Ns96p1097 Ns96p1098 Ns96p911 Ns96p1097 199184 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 13575311) (BSN.cosEvenQ 8388608) 0 3 Ns96p1096 Ns96p908 Ns96p1097 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 13575311) (BSN.cosOddQ 8388608) 0 3 Ns96p1098 Ns96p911 Ns96p1097 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1100 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz143) 12449 262144 1502411 79298560000 88286058 88356532 4194304 (@Enclosure.Real.IsNear.neg qz143 Bool.true 12449 262144 1502411 79298560000 (Ns96p1089 (@Ns96p1090 1210000 (Ns96p1095 rfl) (Enclosure.sfrac_false_div 13575311 8388608) (Ns96p1099 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns96p1101 := Ns96p1087 (@Enclosure.Real.IsNear.neg qz720 Bool.false 88321295 4194304 35237 4194304 (@Ns96p1088 35237 4194304 (Ns96p1100 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p1102 := @Enclosure.Real.IsNear.recentre' qz144 Bool.true 98114 4194304 

noncomputable abbrev qz146 := (@HMul.hMul Real Real Real qz339 qz337 qz488)

noncomputable def Ns96p1103 := @Enclosure.Real.IsNear.cos_image qz146 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 835815)) qz423) Bool.true 835815 524288 

noncomputable def Ns96p1104 := nat_lit 3947024774986937343160184605 

noncomputable def Ns96p1105 := nat_lit 257240473055515023230950858476211 

noncomputable def Ns96p1106 := @Enclosure.Real.IsNear.recentre' qz146 Bool.true Ns96p1104 Ns96p500 Ns96p1105 

noncomputable def Ns96p1107 := nat_lit 9444732965739290427392000000000000000 

noncomputable abbrev qz147 := qz488

noncomputable def Ns96p1108 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz147 884279719003555 140737488355328 1 500000000000000 4463547778111 

noncomputable abbrev qz489 := (@HSub.hSub Real Real Real qz635 qz719 qz712)

noncomputable abbrev qz148 := qz489

noncomputable def Ns96p1109 := @Enclosure.Real.IsNear.subLit_tf qz148 qz26 3364036150335 17592186044416 9532341 2199023255552 1 16 

noncomputable abbrev qz490 := qz719

noncomputable abbrev qz149 := qz490

noncomputable def Ns96p1110 := @Enclosure.Real.IsNear.subLit_ff_n qz149 qz139 1167024323521 17592186044416 3240885 2199023255552 1080289 4194304 3 1048576 

noncomputable def Ns96p1111 := @Enclosure.Real.IsNear.mulLit_ff qz139 qz139 1080289 4194304 3 1048576 1080289 4194304 3 1048576 1167024323521 17592186044416 

noncomputable def Ns96p1112 := nat_lit 55820420099172218794709474691458960441676228688095220433968690249900919390625 

noncomputable def Ns96p1113 := nat_lit 206621721431677182442706747102504677185300319965248164533833585202413803929600 

noncomputable def Ns96p1114 := nat_lit 116230988575345922365530167594941891028951015924455968106921894775390625 

noncomputable def Ns96p1115 := nat_lit 337778651139837401718800344343256902306671411182109431953298080032767248990625 

noncomputable def Ns96p1116 := nat_lit 18802576650282623602286313986327925623862329116837582972578856253419656157593600 

noncomputable def Ns96p1117 := BSN.cos_dyadic_bound_t 835815 524288 4 3 4194304 1210000 Ns96p1112 Ns96p1113 Ns96p1114 Ns96p1115 Ns96p1116 Ns96p1114 98114 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 835815) (BSN.cosEvenQ 524288) 0 3 Ns96p1112 Ns96p1113 Ns96p1114 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 835815) (BSN.cosOddQ 524288) 0 3 Ns96p1115 Ns96p1116 Ns96p1114 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1118 := @Ns96p1102 285478608 10150215680000 49057 2097152 17842413 634388480000 (@Ns96p1103 229 8388608 Bool.true 98114 4194304 1 1210000 (@Ns96p1106 Ns96p1107 835815 524288 229 8388608 (@Ns96p1108 17592186044416 9532341 2199023255552 Ns96p1104 Ns96p500 Ns96p1105 Ns96p1107 RS097to114.d35 (@Ns96p1109 0 1 71416764449776 4463547778111 17592186044416 9532341 2199023255552 (@Ns96p1110 14109790281494691840 3364036150335 17592186044416 9532341 2199023255552 (@Ns96p1111 3240885 2199023255552 (Ns96p1094 rfl rfl) (Ns96p1094 rfl rfl) rfl) (Ns96p1094 rfl rfl) rfl rfl) qz369 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 835815 524288) (BSN.cos_neg_of_bound 835815 524288 Bool.true 98114 4194304 1 1210000 (Ns96p1117 rfl rfl)) rfl rfl) 

noncomputable def Ns96p1119 := @Ns96p1079 14863185126810042687 50728546202701266944000 (Ns96p1080 qz28 (@Enclosure.Real.IsNear.of_eq qz717 (@Inv.inv Real Real.instInv (Real.sqrt qz142)) Bool.false 778457 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz138 (BSN.t_div_two_pi_nonneg qz137 330949 1000 qz140)) Ns96p1084) rfl) (@Ns96p1085 8796093022208 23856837973457 30236569763840000 (BSN.correction_mk qz139 (BSN.cos_two_pi_p_ne_zero_mk qz137 330949 1000 7 qz140 rfl rfl (@BSN.floor_sqrt_eq_dec qz137 330949 1000 7 qz140 rfl rfl rfl))) (@Ns96p1086 4194304 49057 2097152 17842413 634388480000 4332777768815 8796093022208 23856837973457 30236569763840000 Ns96p1101 (Ns96p1118 rfl) rfl)) 

noncomputable def Ns96p1120 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz137) (hardyZApproximantRS₀ qz137) Bool.false 24446300811684375831 18446744073709551616 107610839220412858687 50728546202701266944000 (@Eq.refl Real (hardyZApproximantRS₀ qz137)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz137) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz137) qz137 7) (@HMul.hMul Real Real Real qz5 qz713 (Zeta.RiemannSiegel.correction qz139))) Bool.false 24446300811684375831 18446744073709551616 107610839220412858687 50728546202701266944000 (BSN.hardyZApproximantRS₀_eq qz137 7 (@BSN.floor_sqrt_eq_dec qz137 330949 1000 7 qz140 rfl rfl rfl)) (@Ns96p1017 24446300811684375831 18446744073709551616 107610839220412858687 50728546202701266944000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz137) qz137 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz137) qz137 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz137) qz137 7)) Bool.false 38332327 33554432 15337 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz137) qz137 7) (Ns96p1078 (Ns96p1077 rfl) rfl rfl)) (Ns96p1119 rfl) rfl rfl)) 

theorem RS097to114.d48 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz137) Bool.false 24446300811684375831 18446744073709551616 107610839220412858687 50728546202701266944000 := Ns96p1120 

noncomputable def Ns96p1121 := nat_lit 872750339061680072579612672 

noncomputable abbrev qz905 := (Enclosure.sfrac Bool.false 332533 1000)

noncomputable abbrev qz721 := qz905

noncomputable abbrev qz491 := qz721

noncomputable abbrev qz150 := qz491

noncomputable abbrev qz906 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 332533 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz722 := qz906

noncomputable abbrev qz492 := qz722

noncomputable abbrev qz151 := qz492

noncomputable abbrev qz907 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 332533 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz723 := qz907

noncomputable abbrev qz493 := qz723

noncomputable abbrev qz152 := qz493

noncomputable abbrev qz724 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz151 qz9))

noncomputable def Ns96p1122 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz150) qz150 7) (@HMul.hMul Real Real Real qz5 qz724 (Zeta.RiemannSiegel.correction qz152)) 100552867 33554432 61641 33554432 1629774649491825627 9223372036854775808 503363619173893684941 Ns96p180 Ns96p1121 

noncomputable def Ns96p1123 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz150) qz150 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 332533 1000 65 97 67108864 33554432 1125899906842624 Bool.false 33100082330 1256 

noncomputable def Ns96p1124 := Ns96p1123 120242927 57 27397080 8 130587807 57 25364760 8 Bool.true 62450249 45731 Bool.true 32725704 Bool.true 99480259 3537118876014220 1 Bool.false 31443991 Bool.true Bool.false 66846673 Bool.true Bool.true 100552867 

noncomputable def Ns96p1125 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz150) qz150 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 332533 1000 20 26 67108864 33554432 1125899906842624 Bool.false 33100082330 1256 

noncomputable def Ns96p1126 := Ns96p1125 93032624 56 33554424 8 108007536 56 30011992 8 Bool.true 72159537 26882 Bool.false 55377632 Bool.true 75214354 3537118876014220 1 Bool.false 45527769 Bool.false Bool.false 29190956 Bool.true Bool.true 62450249 

noncomputable def Ns96p1127 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz150) qz150 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 332533 1000 167 81 67108864 33554432 1125899906842624 Bool.false 33100082330 1256 

noncomputable def Ns96p1128 := Ns96p1127 46516304 56 47453136 16 73726608 56 38745320 8 Bool.true 67108848 1320 Bool.false 27678581 Bool.false 44989269 3537118876014220 1 Bool.false 26900498 Bool.false Bool.false 41694299 Bool.true Bool.true 72159537 

noncomputable def Ns96p1129 := nat_lit 54062100365402201322197079428688859964457753913280308469 

noncomputable def Ns96p1130 := nat_lit 109608372110226380855739734923742826276829614047232000 

noncomputable def Ns96p1131 := nat_lit 1951719839608062904458590988640000 

noncomputable def Ns96p1132 := nat_lit 3894071629070565906820168852808550720 

noncomputable abbrev qz908 := (@Eq.refl Real (Enclosure.sfrac Bool.false 332533 1000))

noncomputable abbrev qz725 := qz908

noncomputable abbrev qz494 := qz725

noncomputable abbrev qz153 := qz494

noncomputable def Ns96p1133 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz150 332533 1000 442313784356 16000000 665066 4000 2000 Ns96p1131 Ns96p1132 qz153 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns96p1134 := nat_lit 17299872116928704423103065417180435188626481252249698710080 

noncomputable abbrev qz726 := (Real.log (Enclosure.sfrac Bool.false 442313784356 16000000))

noncomputable abbrev qz154 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 332533 4000) qz726) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 665066))))))

noncomputable abbrev qz727 := (Enclosure.sfrac Bool.false 332533 2000)

noncomputable abbrev qz495 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz154 qz727) (@HMul.hMul Real Real Real qz5 qz727 (Real.log Real.pi)))

noncomputable def Ns96p1135 := @Enclosure.Real.IsNear.addLit_ft_p qz495 (Enclosure.sfrac Bool.true Ns96p1131 Ns96p1132) 4442622361465732434389 9007199254740992000 2317626062826594537 123904000000000000000000 Ns96p1131 Ns96p1132 0 1 Ns96p1134 

noncomputable def Ns96p1136 := nat_lit 298139339858962678599800324096000 

noncomputable abbrev qz496 := (@HSub.hSub Real Real Real qz12 qz154 qz727)

noncomputable abbrev qz497 := (@HMul.hMul Real Real Real qz5 qz727 (Real.log Real.pi))

noncomputable def Ns96p1137 := @Enclosure.Real.IsNear.subLit_ff_p qz496 qz497 6156964676329974237653 9007199254740992000 2128331531685701 242000000000000000000 12772845587613 67108864000 332533 33554432000 Ns96p1136 4442622361465732434389 9007199254740992000 

noncomputable def Ns96p1138 := nat_lit 12313929352659948475306000 

noncomputable abbrev qz498 := qz727

noncomputable def Ns96p1139 := @Enclosure.Real.IsNear.subLit_ff_p qz154 qz498 7654560171218367384021 9007199254740992000 2128331531685701 242000000000000000000 332533 2000 0 1 Ns96p1138 6156964676329974237653 9007199254740992000 2128331531685701 242000000000000000000 

noncomputable def Ns96p1140 := nat_lit 17236537167392039705710830801238622208 

noncomputable def Ns96p1141 := nat_lit 12363909322494150069714944 

noncomputable def Ns96p1142 := nat_lit 2018494247403574295607417102958829308720594857548899132733694655040045440727576176778282828588374110705061134236874316183758275495889959591985807360 

noncomputable def Ns96p1143 := nat_lit 45823230217369859023180116768853820429647168522668475404655446455739926214660741886892322823347758085664636621970659363586955830445717539983982592 

noncomputable def Ns96p1144 := nat_lit 12162083998281947909293927356772290421452397713588674990861717059093119781658071032927388449433377320864260583320066687826174358923740446720 

noncomputable def Ns96p1145 := BSN.log_dyadic_bound 180169784356 704457784356 7 6 Ns96p1142 33554432 9680000 Ns96p1143 Ns96p1144 17553181 884627568712 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 180169784356) (BSN.artanhQ 704457784356) 0 6 Ns96p1143 Ns96p1142 Ns96p1144 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns96p1146 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 332533 4000) qz726 332533 4000 0 1 23029575725075137 2251799813685248 6250000847 60500000000000000 7658093904586410532021 9007199254740992000 2078331531655451 242000000000000000000 (Enclosure.Real.IsNear.const Bool.false 332533 4000) (BSN.isNear_log_sfrac 442313784356 16000000 23029575725075137 2251799813685248 6250000847 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 442313784356) qz350)) Bool.false Ns96p1141 Ns96p86 1000000135520000 9680000000000000000000 23029575725075137 2251799813685248 6250000847 60500000000000000 (BSN.log_rat_reduce_isNear 442313784356 16000000 14 884627568712 524288000000 17553181 33554432 24973259072661432 36028797018963968 9680000 1000000000000000 rfl rfl rfl rfl (Ns96p1145 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p1147 := BSN.arctan_dyadic_bound_f 1000 665066 1 0 4194304 1210000 0 1 1 0 1 1 6306 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 665066) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 665066) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz499 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 665066)))

noncomputable def Ns96p1148 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz499 884279719003555 562949953421312 1 2000000000000000 6306 4194304 1 1210000 3705388000129211957248 883433342010787 562949953421312 200000000121 242000000000000000 qz17 (Ns96p1147 rfl) rfl rfl 

noncomputable def Ns96p1149 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 332533 4000) qz726) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz499)) 7658093904586410532021 9007199254740992000 2078331531655451 242000000000000000000 883433342010787 2251799813685248 200000000121 968000000000000000 Ns96p1140 7654560171218367384021 9007199254740992000 2128331531685701 242000000000000000000 (Ns96p1146 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz499) 1 4 0 1 883433342010787 562949953421312 200000000121 242000000000000000 883433342010787 2251799813685248 200000000121 968000000000000000 qz353 Ns96p1148 rfl) 

noncomputable def Ns96p1150 := @Ns96p1135 Ns96p1129 Ns96p1130 2317626062826594537 123904000000000000000000 (@Ns96p1137 2317626062826594537 123904000000000000000000 (Ns96p1139 (Ns96p1149 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 332533 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz498 (Real.log Real.pi) 332533 2000 0 1 38410761 33554432 1 16777216 12772845587613 67108864000 332533 33554432000 (Enclosure.Real.IsNear.const Bool.false 332533 2000) RS097to114.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns96p1131 Ns96p1132) 

noncomputable def Ns96p1151 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz150) Bool.false Ns96p1129 Ns96p1130 2317626062826594537 123904000000000000000000 4137510291 8388608 79 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz150) (@HAdd.hAdd Real Real Real qz354 qz495 (Enclosure.sfrac Bool.true Ns96p1131 Ns96p1132)) Bool.false Ns96p1129 Ns96p1130 2317626062826594537 123904000000000000000000 Ns96p1133 (Ns96p1150 rfl rfl)) 

noncomputable def Ns96p1152 := nat_lit 1898511629167194309394432 

noncomputable def Ns96p1153 := nat_lit 139851668666522222716223351841224702269005422741686472625061316124568946435991317442625 

noncomputable def Ns96p1154 := nat_lit 280716337725303416868836960733520326265086801225158857915707236110156903643336339521 

noncomputable def Ns96p1155 := nat_lit 365823686722669615867559233076305663509632633311957171105201825753502224726459477323841 

noncomputable def Ns96p1156 := BSN.sin_dyadic_bound_f 26979472937 17179869184 3 2 8388608 2422364 Ns96p1153 Ns96p99 Ns96p1154 Ns96p1155 Ns96p102 Ns96p1154 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26979472937) qz355 0 2 Ns96p1153 Ns96p99 Ns96p1154 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26979472937) qz356 0 2 Ns96p1155 Ns96p102 Ns96p1154 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1157 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz150) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4137510291) qz357) Bool.false 4137510291 8388608 79 4194304 Bool.true 8388606 8388608 1 1210000 (Ns96p1151 rfl) (Enclosure.sfrac_false_div 4137510291 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4137510291) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns96p1152) qz358) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 78 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q1 4137510291 8388608 226375608064910080 72057594037927936 78 Ns96p1152 Ns96p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388606 8388608 Ns96p1152 Ns96p86 26979472937 17179869184 2422364 2420000 (Ns96p1156 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p1158 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz150) Bool.false Ns96p1129 Ns96p1130 2317626062826594537 123904000000000000000000 33100082330 67108864 1256 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz150) (@HAdd.hAdd Real Real Real qz354 qz495 (Enclosure.sfrac Bool.true Ns96p1131 Ns96p1132)) Bool.false Ns96p1129 Ns96p1130 2317626062826594537 123904000000000000000000 Ns96p1133 (Ns96p1150 rfl rfl)) 

noncomputable def Ns96p1159 := Ns96p1128 26882 BSN.abs_quadSignPos (BSN.cos_quad_nat3 167 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 26900498 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 81 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 41694299 67108864) qz153 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 1) Bool.true 4194303 4194304 6236519 317194240000 67108848 67108864 1320 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz150)) Bool.true 4194303 4194304 6236519 317194240000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz150) qz150) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz150)) Bool.true 8388606 8388608 99784304 5075107840000 4194303 4194304 6236519 317194240000 (Ns96p1157 rfl rfl) rfl)) rfl) (Ns96p1158 rfl) RS097to114.d7 

noncomputable def Ns96p1160 := nat_lit 586915103121923215261335420721 

noncomputable def Ns96p1161 := BSN.sin_dyadic_bound_f 27678581 67108864 2 1 67108864 33554432 Ns96p1160 Ns96p127 Ns96p1160 Ns96p1160 Ns96p128 Ns96p1160 26900498 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 27678581) qz360 0 1 Ns96p1160 Ns96p127 Ns96p1160 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 27678581) (BSN.sinOddQ 67108864) 0 1 Ns96p1160 Ns96p128 Ns96p1160 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1162 := nat_lit 251284724988161925806597676374480226732099965270865976829209246305 

noncomputable def Ns96p1163 := nat_lit 16783073376662594702339599425851954770828450943088431562259041 

noncomputable def Ns96p1164 := nat_lit 658099488088290447197285364486473023990632853455503034234923416161 

noncomputable def Ns96p1165 := BSN.sin_dyadic_bound_f 44989269 67108864 3 2 67108864 33554432 Ns96p1162 Ns96p221 Ns96p1163 Ns96p1164 Ns96p224 Ns96p1163 41694299 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 44989269) qz360 0 2 Ns96p1162 Ns96p221 Ns96p1163 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 44989269) (BSN.sinOddQ 67108864) 0 2 Ns96p1164 Ns96p224 Ns96p1163 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1166 := nat_lit 320542930649549014383365468825949218310406827817241855955677741056 

noncomputable def Ns96p1167 := nat_lit 88445358720770411573390981191139493467172953581233208532402176 

noncomputable def Ns96p1168 := nat_lit 961451901231205502326949624515465375944286137544563101449968418816 

noncomputable def Ns96p1169 := BSN.cos_dyadic_bound_f 55377632 67108864 3 2 67108864 33554432 Ns96p1166 Ns96p108 Ns96p1167 Ns96p1168 Ns96p111 Ns96p1167 45527769 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 55377632) qz359 0 2 Ns96p1166 Ns96p108 Ns96p1167 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 55377632) (BSN.cosOddQ 67108864) 0 2 Ns96p1168 Ns96p111 Ns96p1167 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1170 := nat_lit 263011965481789111988291147880643526794462891637938297198711271867162242914967191467870845266817847296 

noncomputable def Ns96p1171 := nat_lit 32779985531432681707705325698714564593336773011368675447929297030819695046714758904712755286016 

noncomputable def Ns96p1172 := nat_lit 1594607596596036989715703107674974930237609990771695627467852072138525060807879305517593176094907699200 

noncomputable def Ns96p1173 := BSN.cos_dyadic_bound_f 75214354 67108864 4 3 67108864 33554432 Ns96p1170 Ns96p236 Ns96p1171 Ns96p1172 Ns96p239 Ns96p1171 29190956 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 75214354) qz359 0 3 Ns96p1170 Ns96p236 Ns96p1171 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 75214354) (BSN.cosOddQ 67108864) 0 3 Ns96p1172 Ns96p239 Ns96p1171 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1174 := Ns96p1126 45731 BSN.abs_quadSignPos (BSN.cos_quad_nat0 20 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 45527769 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 26 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 29190956 67108864) qz153 rfl rfl (Ns96p1159 RS097to114.d9 RS097to114.d11 RS097to114.d13 RS097to114.d17 (Ns96p1161 rfl rfl) (Ns96p1165 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns96p1158 rfl) RS097to114.d19 RS097to114.d21 RS097to114.d23 RS097to114.d25 RS097to114.d17 (Ns96p1169 rfl rfl) (Ns96p1173 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns96p1175 := nat_lit 1146980387117969545404252819456 

noncomputable def Ns96p1176 := BSN.sin_dyadic_bound_f 32725704 67108864 2 1 67108864 33554432 Ns96p1175 Ns96p127 Ns96p1175 Ns96p1175 Ns96p128 Ns96p1175 31443991 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 32725704) qz360 0 1 Ns96p1175 Ns96p127 Ns96p1175 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 32725704) (BSN.sinOddQ 67108864) 0 1 Ns96p1175 Ns96p128 Ns96p1175 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1177 := nat_lit 2094010784655772725376718849204324180574408892103479727079249592297596206966524479769248736530291709681 

noncomputable def Ns96p1178 := nat_lit 939383413324765145013947933993717822421256942428457471030638602112451281607160221016742373578481 

noncomputable def Ns96p1179 := nat_lit 10459731624063469032975188523738525647305192713200330266589257526949874978409458387160465167974669965041 

noncomputable def Ns96p1180 := BSN.sin_dyadic_bound_f 99480259 67108864 4 3 67108864 33554432 Ns96p1177 Ns96p762 Ns96p1178 Ns96p1179 Ns96p765 Ns96p1178 66846673 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 99480259) qz360 0 3 Ns96p1177 Ns96p762 Ns96p1178 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 99480259) (BSN.sinOddQ 67108864) 0 3 Ns96p1179 Ns96p765 Ns96p1178 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1181 := Ns96p1124 61641 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 65 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 31443991 67108864) BSN.abs_quadSignNeg qz486 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66846673 67108864) qz153 rfl rfl (Ns96p1174 rfl rfl) (Ns96p1158 rfl) RS097to114.d27 RS097to114.d29 RS097to114.d31 RS097to114.d33 RS097to114.d17 (Ns96p1176 rfl rfl) (Ns96p1180 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns96p1182 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 7) 100552867 67108864 61641 67108864 100552867 67108864 61641 67108864 13495977352626176 100552867 33554432 61641 33554432 (Ns96p1181 rfl) 

noncomputable def Ns96p1183 := @Enclosure.Real.IsNear.mulLit_tf qz724 (Zeta.RiemannSiegel.correction qz152) 97191 262144 1 4194304 16768781569197 35184372088832 646573790698101 2660818139217920000 1629774649491825627 9223372036854775808 

noncomputable abbrev qz728 := (@HPow.hPow Real Real Real qz7 qz151 qz9)

noncomputable def Ns96p1184 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz728 1 1 0 1 97191 262144 1 4194304 97191 262144 1 4194304 

noncomputable def Ns96p1185 := @Enclosure.Real.IsNear.sqrt_image qz151 443961150437 8388608000 332533 8388608000 30513166 30513190 4194304 (@Enclosure.Real.IsNear.of_eq qz151 (@HMul.hMul Real Real Real qz5 qz150 qz3) Bool.false 443961150437 8388608000 332533 8388608000 (BSN.t_div_two_pi_mk qz150 332533 1000 qz153) (@Enclosure.Real.IsNear.mulLit_ff qz150 qz3 332533 1000 0 1 1335089 8388608 1 8388608 443961150437 8388608000 332533 8388608000 (Enclosure.Real.IsNear.const Bool.false 332533 1000) RS097to114.d36 rfl)) 

noncomputable abbrev qz909 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 332533 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz729 := qz909

noncomputable abbrev qz500 := qz729

noncomputable abbrev qz155 := qz500

noncomputable def Ns96p1186 := @Enclosure.Real.IsNear.sqrt_image qz155 15256589 2097152 3 1048576 11312890 11312896 4194304 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 61026356 8388608 24 8388608 15256589 2097152 3 1048576 (Ns96p1185 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns96p1187 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz155) 11312893 4194304 3 4194304 1555055 1555057 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz155) Bool.false 22625786 8388608 6 8388608 11312893 4194304 3 4194304 (Ns96p1186 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns96p1188 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz155)) Bool.false 3110112 8388608 2 8388608 97191 262144 1 4194304 (Ns96p1187 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz156 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz493))

noncomputable abbrev qz730 := (@HMul.hMul Real Real Real qz863 qz907 qz907)

noncomputable abbrev qz501 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz730 qz723) qz641)

noncomputable abbrev qz157 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz501))

noncomputable def Ns96p1189 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz152) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz156) qz157) Bool.false 16768781569197 

noncomputable def Ns96p1190 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz156) qz157 53819061 8388608 6543 

noncomputable abbrev qz731 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz156))

noncomputable def Ns96p1191 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz156) (@Neg.neg Real Real.instNeg qz731) Bool.true 53819061 8388608 6543 8388608 (BSN.inv_eq_neg_inv_neg qz156) 

noncomputable def Ns96p1192 := @Enclosure.Real.IsNear.recentre' qz731 Bool.false 53819061 8388608 6543 8388608 53819061 8388608 

noncomputable def Ns96p1193 := @Enclosure.Real.IsNear.recentre' qz156 Bool.true 653753 4194304 24038576 1268776960000 653753 4194304 1502411 79298560000 

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz339 qz337 qz493)

noncomputable def Ns96p1194 := @Enclosure.Real.IsNear.cos_image qz158 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 14489653) qz357) Bool.false 14489653 8388608 19 1048576 Bool.true 653753 4194304 1 

noncomputable def Ns96p1195 := nat_lit 80958226229608292385833301 

noncomputable def Ns96p1196 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz152 884279719003555 140737488355328 1 500000000000000 576525 2097152 3 1048576 509809364998524546375 295147905179352825856 Ns96p1195 

noncomputable def Ns96p1197 := @Enclosure.Real.IsNear.subLit_ff_p qz155 qz1 15256589 2097152 3 1048576 7 1 0 1 576525 576525 2097152 3 

noncomputable def Ns96p1198 := @Ns96p1197 1048576 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 61026356 8388608 24 8388608 15256589 2097152 3 1048576 (Ns96p1185 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns96p1199 := @Enclosure.Real.IsNear.recentre' qz158 Bool.false 509809364998524546375 295147905179352825856 Ns96p1195 Ns96p487 14489653 8388608 19 1048576 (@Ns96p1196 Ns96p487 RS097to114.d35 (Ns96p1198 rfl rfl) rfl) 

noncomputable def Ns96p1200 := nat_lit 21685711103950039141338216462262126747581203514283449853357110666226216371994160336072760721 

noncomputable def Ns96p1201 := nat_lit 85643778717106992838827544132946952831432488527929936755740667897197393093853122289041 

noncomputable def Ns96p1202 := nat_lit 131097273483465108665997626004367712100416281310625123855562979016570665916782997498647174545 

noncomputable def Ns96p1203 := BSN.cos_dyadic_bound_t 14489653 8388608 4 3 4194304 1210000 Ns96p1200 Ns96p908 Ns96p1201 Ns96p1202 Ns96p911 Ns96p1201 653753 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 14489653) (BSN.cosEvenQ 8388608) 0 3 Ns96p1200 Ns96p908 Ns96p1201 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 14489653) (BSN.cosOddQ 8388608) 0 3 Ns96p1202 Ns96p911 Ns96p1201 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1204 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz156) 653753 4194304 1502411 79298560000 26906259 26912802 4194304 (@Enclosure.Real.IsNear.neg qz156 Bool.true 653753 4194304 1502411 79298560000 (Ns96p1193 (@Ns96p1194 1210000 (Ns96p1199 rfl) (Enclosure.sfrac_false_div 14489653 8388608) (Ns96p1203 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns96p1205 := Ns96p1191 (@Enclosure.Real.IsNear.neg qz731 Bool.false 53819061 8388608 6543 8388608 (@Ns96p1192 6543 8388608 (Ns96p1204 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p1206 := @Enclosure.Real.IsNear.recentre' qz157 Bool.true 311577 4194304 

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz339 qz337 qz501)

noncomputable def Ns96p1207 := @Enclosure.Real.IsNear.cos_image qz159 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 6900261)) qz434) Bool.true 6900261 4194304 

noncomputable def Ns96p1208 := nat_lit 1018298843582337045075763045 

noncomputable def Ns96p1209 := nat_lit 8222846079818143374803116801301 

noncomputable def Ns96p1210 := @Enclosure.Real.IsNear.recentre' qz159 Bool.true Ns96p1208 Ns96p1001 Ns96p1209 

noncomputable def Ns96p1211 := nat_lit 295147905179352825856000000000000000 

noncomputable abbrev qz160 := qz501

noncomputable def Ns96p1212 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz160 884279719003555 140737488355328 1 500000000000000 1151557388119 

noncomputable abbrev qz502 := (@HSub.hSub Real Real Real qz635 qz730 qz723)

noncomputable abbrev qz161 := qz502

noncomputable def Ns96p1213 := @Enclosure.Real.IsNear.subLit_tf qz161 qz26 876679481175 4398046511104 304707 68719476736 1 16 

noncomputable abbrev qz503 := qz730

noncomputable abbrev qz162 := qz503

noncomputable def Ns96p1214 := @Enclosure.Real.IsNear.subLit_ff_n qz162 qz152 332381075625 4398046511104 108099 68719476736 576525 2097152 3 1048576 

noncomputable def Ns96p1215 := @Enclosure.Real.IsNear.mulLit_ff qz152 qz152 576525 2097152 3 1048576 576525 2097152 3 1048576 332381075625 4398046511104 

noncomputable def Ns96p1216 := nat_lit 4352689802818477836618634146875996084952086297362969930436923708056683223095843040654801 

noncomputable def Ns96p1217 := nat_lit 14198936579076412752333613960380805571166435299025227571149477343212749250185412581785600 

noncomputable def Ns96p1218 := nat_lit 11651617443782019121203380523791636085604259003058876739469274915000545493116384721 

noncomputable def Ns96p1219 := nat_lit 26329833463341708127558670151405468252452006012073152188606411194917340411478616013665745 

noncomputable def Ns96p1220 := nat_lit 1292103228695953560462358870394653306976145612211295708974602438232360181766872544942489600 

noncomputable def Ns96p1221 := BSN.cos_dyadic_bound_t 6900261 4194304 4 3 4194304 1210000 Ns96p1216 Ns96p1217 Ns96p1218 Ns96p1219 Ns96p1220 Ns96p1218 311577 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 6900261) (BSN.cosEvenQ 4194304) 0 3 Ns96p1216 Ns96p1217 Ns96p1218 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 6900261) (BSN.cosOddQ 4194304) 0 3 Ns96p1219 Ns96p1220 Ns96p1218 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1222 := @Ns96p1206 292738608 10150215680000 311577 4194304 18296163 634388480000 (@Ns96p1207 235 8388608 Bool.true 311577 4194304 1 1210000 (@Ns96p1210 Ns96p1211 6900261 4194304 235 8388608 (@Ns96p1212 4398046511104 304707 68719476736 Ns96p1208 Ns96p1001 Ns96p1209 Ns96p1211 RS097to114.d35 (@Ns96p1213 0 1 18424918209904 1151557388119 4398046511104 304707 68719476736 (@Ns96p1214 1838530127305113600 876679481175 4398046511104 304707 68719476736 (@Ns96p1215 108099 68719476736 (Ns96p1198 rfl rfl) (Ns96p1198 rfl rfl) rfl) (Ns96p1198 rfl rfl) rfl rfl) qz369 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 6900261 4194304) (BSN.cos_neg_of_bound 6900261 4194304 Bool.true 311577 4194304 1 1210000 (Ns96p1221 rfl rfl)) rfl rfl) 

noncomputable def Ns96p1223 := @Ns96p1183 503363619173893684941 Ns96p180 (Ns96p1184 qz28 (@Enclosure.Real.IsNear.of_eq qz728 (@Inv.inv Real Real.instInv (Real.sqrt qz155)) Bool.false 97191 262144 1 4194304 (BSN.rpow_neg_quarter_mk qz151 (BSN.t_div_two_pi_nonneg qz150 332533 1000 qz153)) Ns96p1188) rfl) (@Ns96p1189 35184372088832 646573790698101 2660818139217920000 (BSN.correction_mk qz152 (BSN.cos_two_pi_p_ne_zero_mk qz150 332533 1000 7 qz153 rfl rfl (@BSN.floor_sqrt_eq_dec qz150 332533 1000 7 qz153 rfl rfl rfl))) (@Ns96p1190 8388608 311577 4194304 18296163 634388480000 16768781569197 35184372088832 646573790698101 2660818139217920000 Ns96p1205 (Ns96p1222 rfl) rfl)) 

noncomputable def Ns96p1224 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz150) (hardyZApproximantRS₀ qz150) Bool.true 26009986968686582821 9223372036854775808 10754331801644631604941 Ns96p180 (@Eq.refl Real (hardyZApproximantRS₀ qz150)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz150) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz150) qz150 7) (@HMul.hMul Real Real Real qz5 qz724 (Zeta.RiemannSiegel.correction qz152))) Bool.true 26009986968686582821 9223372036854775808 10754331801644631604941 Ns96p180 (BSN.hardyZApproximantRS₀_eq qz150 7 (@BSN.floor_sqrt_eq_dec qz150 332533 1000 7 qz153 rfl rfl rfl)) (@Ns96p1122 26009986968686582821 9223372036854775808 10754331801644631604941 Ns96p180 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz150) qz150 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz150) qz150 7)) Bool.true 100552867 33554432 61641 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz150) qz150 7) (Ns96p1182 (Ns96p1181 rfl) rfl rfl)) (Ns96p1223 rfl) rfl rfl)) 

theorem RS097to114.d49 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz150) Bool.true 26009986968686582821 9223372036854775808 10754331801644631604941 Ns96p180 := Ns96p1224 

noncomputable def Ns96p1225 := nat_lit 114149524572244328822341632 

noncomputable abbrev qz910 := (Enclosure.sfrac Bool.false 334115 1000)

noncomputable abbrev qz732 := qz910

noncomputable abbrev qz504 := qz732

noncomputable abbrev qz163 := qz504

noncomputable abbrev qz911 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 334115 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz733 := qz911

noncomputable abbrev qz505 := qz733

noncomputable abbrev qz164 := qz505

noncomputable abbrev qz912 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 334115 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz734 := qz912

noncomputable abbrev qz506 := qz734

noncomputable abbrev qz165 := qz506

noncomputable abbrev qz735 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz164 qz9))

noncomputable def Ns96p1226 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz163) qz163 7) (@HMul.hMul Real Real Real qz5 qz735 (Zeta.RiemannSiegel.correction qz165)) 446427 33554432 61935 33554432 3156495092977595175 18446744073709551616 301861541990081690451 Ns96p180 Ns96p1225 

noncomputable def Ns96p1227 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz163) qz163 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 334115 1000 65 97 67108864 33554432 1125899906842624 Bool.false 33310888014 1262 

noncomputable def Ns96p1228 := Ns96p1227 120242927 57 27397080 8 130587807 57 25364760 8 Bool.false 30452517 45950 Bool.true 12144331 Bool.true 95264486 3537118876014220 1 Bool.false 12078155 Bool.true Bool.false 66342768 Bool.true Bool.false 446427 

noncomputable def Ns96p1229 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz163) qz163 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 334115 1000 21 26 67108864 33554432 1125899906842624 Bool.false 33310888014 1262 

noncomputable def Ns96p1230 := Ns96p1229 93032624 56 33554424 8 108007536 56 30011992 8 Bool.false 63161956 27011 Bool.false 13591347 Bool.true 35276592 3537118876014220 1 Bool.false 13498624 Bool.true Bool.false 58048620 Bool.true Bool.false 30452517 

noncomputable def Ns96p1231 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz163) qz163 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 334115 1000 168 82 67108864 33554432 1125899906842624 Bool.false 33310888014 1262 

noncomputable def Ns96p1232 := Ns96p1231 46516304 56 47453136 16 73726608 56 38745320 8 Bool.false 67108840 1328 Bool.false 59481115 Bool.false 33745102 3537118876014220 1 Bool.false 42429826 Bool.false Bool.false 58801919 Bool.true Bool.false 63161956 

noncomputable def Ns96p1233 := nat_lit 143303674859478595241634155034584450814717138682387 

noncomputable def Ns96p1234 := nat_lit 288702805604515169759176190544846952072929607680 

noncomputable def Ns96p1235 := nat_lit 1998589352185611354341514500000000 

noncomputable def Ns96p1236 := nat_lit 4006556275700167837327761313005000000 

noncomputable abbrev qz913 := (@Eq.refl Real (Enclosure.sfrac Bool.false 334115 1000))

noncomputable abbrev qz736 := qz913

noncomputable abbrev qz507 := qz736

noncomputable abbrev qz166 := qz507

noncomputable def Ns96p1237 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz163 334115 1000 446532332900 16000000 668230 4000 2000 Ns96p1235 Ns96p1236 qz166 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns96p1238 := nat_lit 716518374297392976208170775172922254073585693411935000000 

noncomputable abbrev qz737 := (Real.log (Enclosure.sfrac Bool.false 446532332900 16000000))

noncomputable abbrev qz167 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 334115 4000) qz737) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 668230))))))

noncomputable abbrev qz738 := (Enclosure.sfrac Bool.false 334115 2000)

noncomputable abbrev qz508 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz167 qz738) (@HMul.hMul Real Real Real qz5 qz738 (Real.log Real.pi)))

noncomputable def Ns96p1239 := @Enclosure.Real.IsNear.addLit_ft_p qz508 (Enclosure.sfrac Bool.true Ns96p1235 Ns96p1236) 178836647998879848187 360287970189639680 465706039870498947 24780800000000000000000 Ns96p1235 Ns96p1236 0 1 Ns96p1238 

noncomputable def Ns96p1240 := nat_lit 12001524288772699884322029568000 

noncomputable abbrev qz509 := (@HSub.hSub Real Real Real qz12 qz167 qz738)

noncomputable abbrev qz510 := (@HMul.hMul Real Real Real qz5 qz738 (Real.log Real.pi))

noncomputable def Ns96p1241 := @Enclosure.Real.IsNear.subLit_ff_p qz509 qz510 1238682873132082508519 1801439850948198400 427643806605131 48400000000000000000 2566722282303 13421772800 66823 6710886400 Ns96p1240 178836647998879848187 360287970189639680 

noncomputable def Ns96p1242 := nat_lit 2477365746264165017038000 

noncomputable abbrev qz511 := qz738

noncomputable def Ns96p1243 := @Enclosure.Real.IsNear.subLit_ff_p qz167 qz511 1539626911031861162727 1801439850948198400 427643806605131 48400000000000000000 334115 2000 0 1 Ns96p1242 1238682873132082508519 1801439850948198400 427643806605131 48400000000000000000 

noncomputable def Ns96p1244 := nat_lit 3466931591406338864801381968087351296 

noncomputable def Ns96p1245 := nat_lit 12375384782575066245234688 

noncomputable def Ns96p1246 := nat_lit 2168417964421864005947125120081297970213182090960798126140123154852871217188512758933250801960654043505253201444650069389535000000000000000000000000 

noncomputable def Ns96p1247 := nat_lit 51020977059165249461545867707256302356642518597028950119938367404386537091193712783941919029091162644236534404526269384752000000000000000000000000 

noncomputable def Ns96p1248 := nat_lit 16055570686572910459110977735276836911132200082027911911391094371757838791932615651200070529938808890706031338999195000000000000000000000000 

noncomputable def Ns96p1249 := BSN.log_dyadic_bound 184388332900 708676332900 7 6 Ns96p1246 33554432 9680000 Ns96p1247 Ns96p1248 17871689 893064665800 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 184388332900) (BSN.artanhQ 708676332900) 0 6 Ns96p1247 Ns96p1246 Ns96p1248 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns96p1250 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 334115 4000) qz737 334115 4000 0 1 23050950435130049 2251799813685248 6250000847 60500000000000000 1540333660926695264327 1801439850948198400 417643806599081 48400000000000000000 (Enclosure.Real.IsNear.const Bool.false 334115 4000) (BSN.isNear_log_sfrac 446532332900 16000000 23050950435130049 2251799813685248 6250000847 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 446532332900) qz350)) Bool.false Ns96p1245 Ns96p86 1000000135520000 9680000000000000000000 23050950435130049 2251799813685248 6250000847 60500000000000000 (BSN.log_rat_reduce_isNear 446532332900 16000000 14 893064665800 524288000000 17871689 33554432 24973259072661432 36028797018963968 9680000 1000000000000000 rfl rfl rfl rfl (Ns96p1249 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p1251 := BSN.arctan_dyadic_bound_f 1000 668230 1 0 4194304 1210000 0 1 1 0 1 1 6276 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 668230) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 668230) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz512 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 668230)))

noncomputable def Ns96p1252 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz512 884279719003555 562949953421312 1 2000000000000000 6276 4194304 1 1210000 3705404888627814596608 883437368542627 562949953421312 200000000121 242000000000000000 qz17 (Ns96p1251 rfl) rfl rfl 

noncomputable def Ns96p1253 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 334115 4000) qz737) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz512)) 1540333660926695264327 1801439850948198400 417643806599081 48400000000000000000 883437368542627 2251799813685248 200000000121 968000000000000000 Ns96p1244 1539626911031861162727 1801439850948198400 427643806605131 48400000000000000000 (Ns96p1250 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz512) 1 4 0 1 883437368542627 562949953421312 200000000121 242000000000000000 883437368542627 2251799813685248 200000000121 968000000000000000 qz353 Ns96p1252 rfl) 

noncomputable def Ns96p1254 := @Ns96p1239 Ns96p1233 Ns96p1234 465706039870498947 24780800000000000000000 (@Ns96p1241 465706039870498947 24780800000000000000000 (Ns96p1243 (Ns96p1253 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 334115 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz511 (Real.log Real.pi) 334115 2000 0 1 38410761 33554432 1 16777216 2566722282303 13421772800 66823 6710886400 (Enclosure.Real.IsNear.const Bool.false 334115 2000) RS097to114.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns96p1235 Ns96p1236) 

noncomputable def Ns96p1255 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz163) Bool.false Ns96p1233 Ns96p1234 465706039870498947 24780800000000000000000 4163861001 8388608 159 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz163) (@HAdd.hAdd Real Real Real qz354 qz508 (Enclosure.sfrac Bool.true Ns96p1235 Ns96p1236)) Bool.false Ns96p1233 Ns96p1234 465706039870498947 24780800000000000000000 Ns96p1237 (Ns96p1254 rfl rfl)) 

noncomputable def Ns96p1256 := nat_lit 1898096683113191961526272 

noncomputable def Ns96p1257 := nat_lit 139729197534780443360146683633984034024395613385049023842505438361407620726613517276865 

noncomputable def Ns96p1258 := nat_lit 280225877445599563650815125188910799354010305700627387893306279470407447137223710401 

noncomputable def Ns96p1259 := nat_lit 365503723075227333316378089791080900198272494561136903816639366494067870798146564003521 

noncomputable def Ns96p1260 := BSN.sin_dyadic_bound_f 26973576199 17179869184 3 2 8388608 2422364 Ns96p1257 Ns96p99 Ns96p1258 Ns96p1259 Ns96p102 Ns96p1258 8388605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26973576199) qz355 0 2 Ns96p1257 Ns96p99 Ns96p1258 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26973576199) qz356 0 2 Ns96p1259 Ns96p102 Ns96p1258 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1261 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz163) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4163861001) qz357) Bool.false 4163861001 8388608 159 8388608 Bool.false 8388605 8388608 1 1210000 (Ns96p1255 rfl) (Enclosure.sfrac_false_div 4163861001 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4163861001) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns96p1256) qz358) 226375608064910080 72057594037927936 Bool.false 8388605 8388608 78 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q3 4163861001 8388608 226375608064910080 72057594037927936 78 Ns96p1256 Ns96p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388605 8388608 Ns96p1256 Ns96p86 26973576199 17179869184 2422364 2420000 (Ns96p1260 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p1262 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz163) Bool.false Ns96p1233 Ns96p1234 465706039870498947 24780800000000000000000 33310888014 67108864 1262 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz163) (@HAdd.hAdd Real Real Real qz354 qz508 (Enclosure.sfrac Bool.true Ns96p1235 Ns96p1236)) Bool.false Ns96p1233 Ns96p1234 465706039870498947 24780800000000000000000 Ns96p1237 (Ns96p1254 rfl rfl)) 

noncomputable def Ns96p1263 := Ns96p1232 27011 BSN.abs_quadSignPos (BSN.cos_quad_nat0 168 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 42429826 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 82 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 58801919 67108864) qz166 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz163) qz163 1) Bool.false 8388605 8388608 12548663 634388480000 67108840 67108864 1328 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz163) qz163 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz163)) Bool.false 8388605 8388608 12548663 634388480000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz163) qz163) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz163)) Bool.false 8388605 8388608 200778608 10150215680000 8388605 8388608 12548663 634388480000 (Ns96p1261 rfl rfl) rfl)) rfl) (Ns96p1262 rfl) RS097to114.d7 

noncomputable def Ns96p1264 := nat_lit 426682416666379646978779692147568546603132647045495768182009190625 

noncomputable def Ns96p1265 := nat_lit 156686943111400163068103897775138241817658067466779795500390625 

noncomputable def Ns96p1266 := nat_lit 1279733876112916140610202868647155363325762625001553744955026790625 

noncomputable def Ns96p1267 := BSN.cos_dyadic_bound_f 59481115 67108864 3 2 67108864 33554432 Ns96p1264 Ns96p108 Ns96p1265 Ns96p1266 Ns96p111 Ns96p1265 42429826 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 59481115) qz359 0 2 Ns96p1264 Ns96p108 Ns96p1265 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 59481115) (BSN.cosOddQ 67108864) 0 2 Ns96p1266 Ns96p111 Ns96p1265 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1268 := nat_lit 44186371383415213976907899059479386251347105578567678647633428736 

noncomputable def Ns96p1269 := nat_lit 1681457759165309040064436545928934690482698362625138572902656 

noncomputable def Ns96p1270 := nat_lit 132555751234727311312643568305346300884660351338977785665754480896 

noncomputable def Ns96p1271 := BSN.cos_dyadic_bound_f 33745102 67108864 3 2 67108864 33554432 Ns96p1268 Ns96p108 Ns96p1269 Ns96p1270 Ns96p111 Ns96p1269 58801919 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 33745102) qz359 0 2 Ns96p1268 Ns96p108 Ns96p1269 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 33745102) (BSN.cosOddQ 67108864) 0 2 Ns96p1270 Ns96p111 Ns96p1269 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1272 := nat_lit 34123219694312616614534299281 

noncomputable def Ns96p1273 := BSN.sin_dyadic_bound_f 13591347 67108864 2 1 67108864 33554432 Ns96p1272 Ns96p127 Ns96p1272 Ns96p1272 Ns96p128 Ns96p1272 13498624 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 13591347) qz360 0 1 Ns96p1272 Ns96p127 Ns96p1272 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 13591347) (BSN.sinOddQ 67108864) 0 1 Ns96p1272 Ns96p128 Ns96p1272 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1274 := nat_lit 52770967549343431759536505679575047001504120476432149695583748096 

noncomputable def Ns96p1275 := nat_lit 2398241850810750824292158737849969293082420005609662752751616 

noncomputable def Ns96p1276 := nat_lit 158308106164328673776960932721249441065926196589285229761245741056 

noncomputable def Ns96p1277 := BSN.cos_dyadic_bound_f 35276592 67108864 3 2 67108864 33554432 Ns96p1274 Ns96p108 Ns96p1275 Ns96p1276 Ns96p111 Ns96p1275 58048620 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 35276592) qz359 0 2 Ns96p1274 Ns96p108 Ns96p1275 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 35276592) (BSN.cosOddQ 67108864) 0 2 Ns96p1276 Ns96p111 Ns96p1275 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1278 := Ns96p1230 45950 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 21 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 13498624 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 26 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 58048620 67108864) qz166 rfl rfl (Ns96p1263 RS097to114.d9 RS097to114.d11 RS097to114.d13 RS097to114.d17 (Ns96p1267 rfl rfl) (Ns96p1271 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns96p1262 rfl) RS097to114.d19 RS097to114.d21 RS097to114.d23 RS097to114.d25 RS097to114.d17 (Ns96p1273 rfl rfl) (Ns96p1277 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns96p1279 := nat_lit 21751758985867796459009628721 

noncomputable def Ns96p1280 := BSN.sin_dyadic_bound_f 12144331 67108864 2 1 67108864 33554432 Ns96p1279 Ns96p127 Ns96p1279 Ns96p1279 Ns96p128 Ns96p1279 12078155 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 12144331) qz360 0 1 Ns96p1279 Ns96p127 Ns96p1279 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 12144331) (BSN.sinOddQ 67108864) 0 1 Ns96p1279 Ns96p128 Ns96p1279 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1281 := nat_lit 1760537237304618360994949145076502370589182811658587695878192303408306325992298856127506725223666487296 

noncomputable def Ns96p1282 := nat_lit 558691858600514749315773051210863868799421911220250302276697528424434253658373134759458902839296 

noncomputable def Ns96p1283 := nat_lit 8795386498984097718224422970768127803595650609327972822158212339696065676611499507546753692043616915456 

noncomputable def Ns96p1284 := BSN.sin_dyadic_bound_f 95264486 67108864 4 3 67108864 33554432 Ns96p1281 Ns96p762 Ns96p1282 Ns96p1283 Ns96p765 Ns96p1282 66342768 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 95264486) qz360 0 3 Ns96p1281 Ns96p762 Ns96p1282 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 95264486) (BSN.sinOddQ 67108864) 0 3 Ns96p1283 Ns96p765 Ns96p1282 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1285 := Ns96p1228 61935 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 65 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 12078155 67108864) BSN.abs_quadSignNeg qz486 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66342768 67108864) qz166 rfl rfl (Ns96p1278 rfl rfl) (Ns96p1262 rfl) RS097to114.d27 RS097to114.d29 RS097to114.d31 RS097to114.d33 RS097to114.d17 (Ns96p1280 rfl rfl) (Ns96p1284 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns96p1286 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz163) qz163 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz163) qz163 7) 446427 67108864 61935 67108864 446427 67108864 61935 67108864 59918417657856 446427 33554432 61935 33554432 (Ns96p1285 rfl) 

noncomputable def Ns96p1287 := @Enclosure.Real.IsNear.mulLit_tf qz735 (Zeta.RiemannSiegel.correction qz165) 388303 1048576 1 4194304 8128948509225 17592186044416 96975363410901 665204534804480000 3156495092977595175 18446744073709551616 

noncomputable abbrev qz739 := (@HPow.hPow Real Real Real qz7 qz164 qz9)

noncomputable def Ns96p1288 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz739 1 1 0 1 388303 1048576 1 4194304 388303 1048576 1 4194304 

noncomputable def Ns96p1289 := @Enclosure.Real.IsNear.sqrt_image qz164 89214652247 1677721600 66823 1677721600 30585662 30585686 4194304 (@Enclosure.Real.IsNear.of_eq qz164 (@HMul.hMul Real Real Real qz5 qz163 qz3) Bool.false 89214652247 1677721600 66823 1677721600 (BSN.t_div_two_pi_mk qz163 334115 1000 qz166) (@Enclosure.Real.IsNear.mulLit_ff qz163 qz3 334115 1000 0 1 1335089 8388608 1 8388608 89214652247 1677721600 66823 1677721600 (Enclosure.Real.IsNear.const Bool.false 334115 1000) RS097to114.d36 rfl)) 

noncomputable abbrev qz914 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 334115 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz740 := qz914

noncomputable abbrev qz513 := qz740

noncomputable abbrev qz168 := qz513

noncomputable def Ns96p1290 := @Enclosure.Real.IsNear.sqrt_image qz168 15292837 2097152 3 1048576 11326321 11326327 4194304 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 61171348 8388608 24 8388608 15292837 2097152 3 1048576 (Ns96p1289 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns96p1291 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz168) 2831581 1048576 3 4194304 1553211 1553213 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz168) Bool.false 22652648 8388608 6 8388608 2831581 1048576 3 4194304 (Ns96p1290 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns96p1292 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz168)) Bool.false 3106424 8388608 2 8388608 388303 1048576 1 4194304 (Ns96p1291 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz169 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz506))

noncomputable abbrev qz741 := (@HMul.hMul Real Real Real qz863 qz912 qz912)

noncomputable abbrev qz514 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz741 qz734) qz641)

noncomputable abbrev qz170 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz514))

noncomputable def Ns96p1293 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz165) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz169) qz170) Bool.false 8128948509225 

noncomputable def Ns96p1294 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz169) qz170 16008075 4194304 579 

noncomputable abbrev qz742 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz169))

noncomputable def Ns96p1295 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz169) (@Neg.neg Real Real.instNeg qz742) Bool.true 16008075 4194304 579 2097152 (BSN.inv_eq_neg_inv_neg qz169) 

noncomputable def Ns96p1296 := @Enclosure.Real.IsNear.recentre' qz742 Bool.false 32016150 8388608 2316 8388608 16008075 4194304 

noncomputable def Ns96p1297 := @Enclosure.Real.IsNear.recentre' qz169 Bool.true 1098957 4194304 24038576 1268776960000 1098957 4194304 1502411 79298560000 

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz339 qz337 qz506)

noncomputable def Ns96p1298 := @Enclosure.Real.IsNear.cos_image qz171 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15400665) qz357) Bool.false 15400665 8388608 19 1048576 Bool.true 1098957 4194304 1 

noncomputable def Ns96p1299 := nat_lit 80958226229763976360378709 

noncomputable def Ns96p1300 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz165 884279719003555 140737488355328 1 500000000000000 612773 2097152 3 1048576 541862736252965408015 295147905179352825856 Ns96p1299 

noncomputable def Ns96p1301 := @Enclosure.Real.IsNear.subLit_ff_p qz168 qz1 15292837 2097152 3 1048576 7 1 0 1 612773 612773 2097152 3 

noncomputable def Ns96p1302 := @Ns96p1301 1048576 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 61171348 8388608 24 8388608 15292837 2097152 3 1048576 (Ns96p1289 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns96p1303 := @Enclosure.Real.IsNear.recentre' qz171 Bool.false 541862736252965408015 295147905179352825856 Ns96p1299 Ns96p487 15400665 8388608 19 1048576 (@Ns96p1300 Ns96p487 RS097to114.d35 (Ns96p1302 rfl rfl) rfl) 

noncomputable def Ns96p1304 := nat_lit 27716125432858050649259839566302325398887334136069754139851661125670085649506262434539390625 

noncomputable def Ns96p1305 := nat_lit 178022005265273624931839278888706577828773476822660014794809984381676860797207275390625 

noncomputable def Ns96p1306 := nat_lit 167390669064181144814609626207373911205456537358387585972524655020344497185056033823876990625 

noncomputable def Ns96p1307 := BSN.cos_dyadic_bound_t 15400665 8388608 4 3 4194304 1210000 Ns96p1304 Ns96p908 Ns96p1305 Ns96p1306 Ns96p911 Ns96p1305 1098957 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 15400665) (BSN.cosEvenQ 8388608) 0 3 Ns96p1304 Ns96p908 Ns96p1305 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 15400665) (BSN.cosOddQ 8388608) 0 3 Ns96p1306 Ns96p911 Ns96p1305 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1308 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz169) 1098957 4194304 1502411 79298560000 16006917 16009233 4194304 (@Enclosure.Real.IsNear.neg qz169 Bool.true 1098957 4194304 1502411 79298560000 (Ns96p1297 (@Ns96p1298 1210000 (Ns96p1303 rfl) (Enclosure.sfrac_false_div 15400665 8388608) (Ns96p1307 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns96p1309 := Ns96p1295 (@Enclosure.Real.IsNear.neg qz742 Bool.false 16008075 4194304 579 2097152 (@Ns96p1296 579 2097152 (Ns96p1308 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p1310 := @Enclosure.Real.IsNear.recentre' qz170 Bool.true 507803 4194304 

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz339 qz337 qz514)

noncomputable def Ns96p1311 := @Enclosure.Real.IsNear.cos_image qz172 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7097449)) qz434) Bool.true 7097449 4194304 

noncomputable def Ns96p1312 := nat_lit 1047398624889166199079083605 

noncomputable def Ns96p1313 := nat_lit 3362502776536051220883505909637 

noncomputable def Ns96p1314 := @Enclosure.Real.IsNear.recentre' qz172 Bool.true Ns96p1312 Ns96p1001 Ns96p1313 

noncomputable def Ns96p1315 := nat_lit 118059162071741130342400000000000000 

noncomputable abbrev qz173 := qz514

noncomputable def Ns96p1316 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz173 884279719003555 140737488355328 1 500000000000000 1184465279911 

noncomputable abbrev qz515 := (@HSub.hSub Real Real Real qz635 qz741 qz734)

noncomputable abbrev qz174 := qz515

noncomputable def Ns96p1317 := @Enclosure.Real.IsNear.subLit_tf qz174 qz26 909587372967 4398046511104 623007 137438953472 1 16 

noncomputable abbrev qz516 := qz741

noncomputable abbrev qz175 := qz516

noncomputable def Ns96p1318 := @Enclosure.Real.IsNear.subLit_ff_n qz175 qz165 375490749529 4398046511104 229791 137438953472 612773 2097152 3 1048576 

noncomputable def Ns96p1319 := @Enclosure.Real.IsNear.mulLit_ff qz165 qz165 612773 2097152 3 1048576 612773 2097152 3 1048576 375490749529 4398046511104 

noncomputable def Ns96p1320 := nat_lit 4874498440744394870596838831516987670442966508373905187739592515332835284499431571325281 

noncomputable def Ns96p1321 := nat_lit 16339071230516941548928399145854900034090040452369852809037420970386641441480245601 

noncomputable def Ns96p1322 := nat_lit 29476125658360260551071052976668307764344083271208425169028150415892737783102349418955105 

noncomputable def Ns96p1323 := BSN.cos_dyadic_bound_t 7097449 4194304 4 3 4194304 1210000 Ns96p1320 Ns96p1217 Ns96p1321 Ns96p1322 Ns96p1220 Ns96p1321 507803 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 7097449) (BSN.cosEvenQ 4194304) 0 3 Ns96p1320 Ns96p1217 Ns96p1321 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 7097449) (BSN.cosOddQ 4194304) 0 3 Ns96p1322 Ns96p1220 Ns96p1321 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1324 := @Ns96p1310 18674288 634388480000 507803 4194304 1167143 39649280000 (@Ns96p1311 15 524288 Bool.true 507803 4194304 1 1210000 (@Ns96p1314 Ns96p1315 7097449 4194304 15 524288 (@Ns96p1316 4398046511104 623007 137438953472 Ns96p1312 Ns96p1001 Ns96p1313 Ns96p1315 RS097to114.d35 (@Ns96p1317 0 1 18951444478576 1184465279911 4398046511104 623007 137438953472 (@Ns96p1318 1907542978392489984 909587372967 4398046511104 623007 137438953472 (@Ns96p1319 229791 137438953472 (Ns96p1302 rfl rfl) (Ns96p1302 rfl rfl) rfl) (Ns96p1302 rfl rfl) rfl rfl) qz369 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7097449 4194304) (BSN.cos_neg_of_bound 7097449 4194304 Bool.true 507803 4194304 1 1210000 (Ns96p1323 rfl rfl)) rfl rfl) 

noncomputable def Ns96p1325 := @Ns96p1287 301861541990081690451 Ns96p180 (Ns96p1288 qz28 (@Enclosure.Real.IsNear.of_eq qz739 (@Inv.inv Real Real.instInv (Real.sqrt qz168)) Bool.false 388303 1048576 1 4194304 (BSN.rpow_neg_quarter_mk qz164 (BSN.t_div_two_pi_nonneg qz163 334115 1000 qz166)) Ns96p1292) rfl) (@Ns96p1293 17592186044416 96975363410901 665204534804480000 (BSN.correction_mk qz165 (BSN.cos_two_pi_p_ne_zero_mk qz163 334115 1000 7 qz166 rfl rfl (@BSN.floor_sqrt_eq_dec qz163 334115 1000 7 qz166 rfl rfl rfl))) (@Ns96p1294 2097152 507803 4194304 1167143 39649280000 8128948509225 17592186044416 96975363410901 665204534804480000 Ns96p1309 (Ns96p1324 rfl) rfl)) 

noncomputable def Ns96p1326 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz163) (hardyZApproximantRS₀ qz163) Bool.false 3401920931704173351 18446744073709551616 10601722257768948890451 Ns96p180 (@Eq.refl Real (hardyZApproximantRS₀ qz163)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz163) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz163) qz163 7) (@HMul.hMul Real Real Real qz5 qz735 (Zeta.RiemannSiegel.correction qz165))) Bool.false 3401920931704173351 18446744073709551616 10601722257768948890451 Ns96p180 (BSN.hardyZApproximantRS₀_eq qz163 7 (@BSN.floor_sqrt_eq_dec qz163 334115 1000 7 qz166 rfl rfl rfl)) (@Ns96p1226 3401920931704173351 18446744073709551616 10601722257768948890451 Ns96p180 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz163) qz163 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz163) qz163 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz163) qz163 7)) Bool.false 446427 33554432 61935 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz163) qz163 7) (Ns96p1286 (Ns96p1285 rfl) rfl rfl)) (Ns96p1325 rfl) rfl rfl)) 

theorem RS097to114.d50 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz163) Bool.false 3401920931704173351 18446744073709551616 10601722257768948890451 Ns96p180 := Ns96p1326 

noncomputable def Ns96p1327 := nat_lit 102009600475472756675182592 

noncomputable abbrev qz915 := (Enclosure.sfrac Bool.false 335696 1000)

noncomputable abbrev qz743 := qz915

noncomputable abbrev qz517 := qz743

noncomputable abbrev qz176 := qz517

noncomputable abbrev qz916 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 335696 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz744 := qz916

noncomputable abbrev qz518 := qz744

noncomputable abbrev qz177 := qz518

noncomputable abbrev qz917 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 335696 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz745 := qz917

noncomputable abbrev qz519 := qz745

noncomputable abbrev qz178 := qz519

noncomputable abbrev qz746 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz177 qz9))

noncomputable def Ns96p1328 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz176) qz176 7) (@HMul.hMul Real Real Real qz5 qz746 (Zeta.RiemannSiegel.correction qz178)) 182530379 33554432 31115 16777216 95725033315904605 576460752303423488 10936592518038532793 279007004114856968192000 Ns96p1327 

noncomputable def Ns96p1329 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz176) qz176 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 335696 1000 64 97 67108864 33554432 1125899906842624 Bool.false 33521811461 1268 

noncomputable def Ns96p1330 := Ns96p1329 120242927 57 27397080 8 130587807 57 25364760 8 Bool.true 161296386 46169 Bool.true 96739308 Bool.true 90800362 3537118876014220 1 Bool.false 8650908 Bool.false Bool.false 65523930 Bool.true Bool.true 182530379 

noncomputable def Ns96p1331 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz176) qz176 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 335696 1000 21 25 67108864 33554432 1125899906842624 Bool.false 33521811461 1268 

noncomputable def Ns96p1332 := Ns96p1331 93032624 56 33554424 8 108007536 56 30011992 8 Bool.true 100684801 27141 Bool.false 77430216 Bool.true 100527417 3537118876014220 1 Bool.false 61358281 Bool.true Bool.false 66931006 Bool.true Bool.true 161296386 

noncomputable def Ns96p1333 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz176) qz176 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 335696 1000 169 83 67108864 33554432 1125899906842624 Bool.false 33521811461 1268 

noncomputable def Ns96p1334 := Ns96p1333 46516304 56 47453136 16 73726608 56 38745320 8 Bool.true 67108840 1336 Bool.false 91447929 Bool.false 22692425 3537118876014220 1 Bool.false 65660783 Bool.true Bool.false 22262444 Bool.false Bool.true 100684801 

noncomputable def Ns96p1335 := nat_lit 884259694342606548199142051278383485524047404487223 

noncomputable def Ns96p1336 := nat_lit 1770240359357565923238543433756578938678673408000 

noncomputable def Ns96p1337 := nat_lit 2046324529647357634596269588480000 

noncomputable def Ns96p1338 := nat_lit 4121662022912795476705169849462292480 

noncomputable abbrev qz520 := (@Eq.refl Real qz743)

noncomputable abbrev qz179 := qz520

noncomputable def Ns96p1339 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz176 335696 1000 450768217664 16000000 671392 4000 2000 Ns96p1337 Ns96p1338 qz179 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns96p1340 := nat_lit 1159016866568741254855579469451602802146079414009492930560 

noncomputable abbrev qz747 := (Real.log (Enclosure.sfrac Bool.false 450768217664 16000000))

noncomputable abbrev qz180 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 335696 4000) qz747) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 671392))))))

noncomputable abbrev qz748 := (Enclosure.sfrac Bool.false 335696 2000)

noncomputable abbrev qz521 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz180 qz748) (@HMul.hMul Real Real Real qz5 qz748 (Real.log Real.pi)))

noncomputable def Ns96p1341 := @Enclosure.Real.IsNear.addLit_ft_p qz521 (Enclosure.sfrac Bool.true Ns96p1337 Ns96p1338) 281201615295947315847 562949953421312000 146214215203188009 7744000000000000000000 Ns96p1337 Ns96p1338 0 1 Ns96p1340 

noncomputable def Ns96p1342 := nat_lit 235889011968450602129267097600 

noncomputable abbrev qz522 := (@HSub.hSub Real Real Real qz12 qz180 qz748)

noncomputable abbrev qz523 := (@HMul.hMul Real Real Real qz5 qz748 (Real.log Real.pi))

noncomputable def Ns96p1343 := @Enclosure.Real.IsNear.subLit_ff_p qz522 qz523 77873433823033446939 112589990684262400 1074050142182381 121000000000000000000 805896176541 4194304000 20981 2097152000 Ns96p1342 281201615295947315847 562949953421312000 

noncomputable abbrev qz524 := qz748

noncomputable def Ns96p1344 := @Enclosure.Real.IsNear.subLit_ff_p qz180 qz524 483857192897027611271 562949953421312000 1074050142182381 121000000000000000000 335696 2000 0 1 778734338230334469390000 77873433823033446939 112589990684262400 1074050142182381 121000000000000000000 

noncomputable def Ns96p1345 := nat_lit 1089549536815793877034176868891230208 

noncomputable def Ns96p1346 := nat_lit 12386798813557065087188992 

noncomputable def Ns96p1347 := nat_lit 2329166509729339729969308076171446877692810073173035645079702651647518479424823453953975922087284861897272510675272031502481954539248008345639976960 

noncomputable def Ns96p1348 := nat_lit 56753899757753324330126774048739784181660857432465593088426958236810919535958298427703849581725376187940445149160969985993763518006369377910259712 

noncomputable def Ns96p1349 := nat_lit 21085985901698436507812734725790181340085626755049092139331177549505764981674549356559543527116014207212722622802487993496538721594292305920 

noncomputable def Ns96p1350 := BSN.log_dyadic_bound 188624217664 712912217664 7 6 Ns96p1347 33554432 9680000 Ns96p1348 Ns96p1349 18188492 901536435328 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 188624217664) (BSN.artanhQ 712912217664) 0 6 Ns96p1348 Ns96p1347 Ns96p1349 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns96p1351 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 335696 4000) qz747 335696 4000 0 1 23072210724571841 2251799813685248 6250000847 60500000000000000 484078053212241796021 562949953421312000 131131267770907 15125000000000000000 (Enclosure.Real.IsNear.const Bool.false 335696 4000) (BSN.isNear_log_sfrac 450768217664 16000000 23072210724571841 2251799813685248 6250000847 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 450768217664) qz350)) Bool.false Ns96p1346 Ns96p86 1000000135520000 9680000000000000000000 23072210724571841 2251799813685248 6250000847 60500000000000000 (BSN.log_rat_reduce_isNear 450768217664 16000000 14 901536435328 524288000000 18188492 33554432 24973259072661432 36028797018963968 9680000 1000000000000000 rfl rfl rfl rfl (Ns96p1350 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p1352 := BSN.arctan_dyadic_bound_f 1000 671392 1 0 4194304 1210000 0 1 1 0 1 1 6247 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 671392) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 671392) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz525 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 671392)))

noncomputable def Ns96p1353 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz525 884279719003555 562949953421312 1 2000000000000000 6247 4194304 1 1210000 3705421214176463814656 883441260856739 562949953421312 200000000121 242000000000000000 qz17 (Ns96p1352 rfl) rfl rfl 

noncomputable def Ns96p1354 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 335696 4000) qz747) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz525)) 484078053212241796021 562949953421312000 131131267770907 15125000000000000000 883441260856739 2251799813685248 200000000121 968000000000000000 Ns96p1345 483857192897027611271 562949953421312000 1074050142182381 121000000000000000000 (Ns96p1351 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz525) 1 4 0 1 883441260856739 562949953421312 200000000121 242000000000000000 883441260856739 2251799813685248 200000000121 968000000000000000 qz353 Ns96p1353 rfl) 

noncomputable def Ns96p1355 := @Ns96p1341 Ns96p1335 Ns96p1336 146214215203188009 7744000000000000000000 (@Ns96p1343 146214215203188009 7744000000000000000000 (Ns96p1344 (Ns96p1354 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 335696 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz524 (Real.log Real.pi) 335696 2000 0 1 38410761 33554432 1 16777216 805896176541 4194304000 20981 2097152000 (Enclosure.Real.IsNear.const Bool.false 335696 2000) RS097to114.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns96p1337 Ns96p1338) 

noncomputable def Ns96p1356 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz176) Bool.false Ns96p1335 Ns96p1336 146214215203188009 7744000000000000000000 2046009 4096 5 262144 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz176) (@HAdd.hAdd Real Real Real qz354 qz521 (Enclosure.sfrac Bool.true Ns96p1337 Ns96p1338)) Bool.false Ns96p1335 Ns96p1336 146214215203188009 7744000000000000000000 Ns96p1339 (Ns96p1355 rfl rfl)) 

noncomputable def Ns96p1357 := nat_lit 140233409045658613216302761775272822423672578332992515270103884580052074948411626997985 

noncomputable def Ns96p1358 := nat_lit 282247834321659906321170499018435999642986004464197114469690267367486732049899964641 

noncomputable def Ns96p1359 := nat_lit 366821003387823204289606290508256114729244299245847887522083056324398551108235375528161 

noncomputable def Ns96p1360 := BSN.sin_dyadic_bound_f 26997828069 17179869184 3 2 8388608 2422364 Ns96p1357 Ns96p99 Ns96p1358 Ns96p1359 Ns96p102 Ns96p1358 8388605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26997828069) qz355 0 2 Ns96p1357 Ns96p99 Ns96p1358 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26997828069) qz356 0 2 Ns96p1359 Ns96p102 Ns96p1358 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1361 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz176) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2046009) (@Nat.cast Real Real.instNatCast 4096)) Bool.false 2046009 4096 5 262144 Bool.true 8388605 8388608 1 1210000 (Ns96p1356 rfl) (Enclosure.sfrac_false_div 2046009 4096) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2046009) (@Nat.cast Real Real.instNatCast 4096)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 927638308956471820288) (@Nat.cast Real Real.instNatCast 590295810358705651712)) 226375608064910080 72057594037927936 Bool.false 8388605 8388608 79 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q1 2046009 4096 226375608064910080 72057594037927936 79 927638308956471820288 590295810358705651712 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388605 8388608 927638308956471820288 590295810358705651712 26997828069 17179869184 2422364 2420000 (Ns96p1360 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p1362 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz176) Bool.false Ns96p1335 Ns96p1336 146214215203188009 7744000000000000000000 33521811461 67108864 1268 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz176) (@HAdd.hAdd Real Real Real qz354 qz521 (Enclosure.sfrac Bool.true Ns96p1337 Ns96p1338)) Bool.false Ns96p1335 Ns96p1336 146214215203188009 7744000000000000000000 Ns96p1339 (Ns96p1355 rfl rfl)) 

noncomputable def Ns96p1363 := Ns96p1334 27141 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 169 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 65660783 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 83 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 22262444 67108864) qz179 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz176) qz176 1) Bool.true 8388605 8388608 394509 19824640000 67108840 67108864 1336 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz176) qz176 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz176)) Bool.true 8388605 8388608 394509 19824640000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz176) qz176) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz176)) Bool.true 8388605 8388608 6312144 317194240000 8388605 8388608 394509 19824640000 (Ns96p1361 rfl rfl) rfl)) rfl) (Ns96p1362 rfl) RS097to114.d7 

noncomputable def Ns96p1364 := nat_lit 1494612745710028240435710062995715224780194379514219796882644986610677813085664980173213075028621956641 

noncomputable def Ns96p1365 := nat_lit 342047558396283257534587769162856245025425475632273878622657231568654954498743411942209246238241 

noncomputable def Ns96p1366 := nat_lit 7467800806009361685458696730632528541681934878781087307005387907050472251704356504473785128684990535201 

noncomputable def Ns96p1367 := BSN.sin_dyadic_bound_f 91447929 67108864 4 3 67108864 33554432 Ns96p1364 Ns96p762 Ns96p1365 Ns96p1366 Ns96p765 Ns96p1365 65660783 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 91447929) qz360 0 3 Ns96p1364 Ns96p762 Ns96p1365 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 91447929) (BSN.sinOddQ 67108864) 0 3 Ns96p1366 Ns96p765 Ns96p1365 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1368 := nat_lit 265169539851609862354875390625 

noncomputable def Ns96p1369 := BSN.sin_dyadic_bound_f 22692425 67108864 2 1 67108864 33554432 Ns96p1368 Ns96p127 Ns96p1368 Ns96p1368 Ns96p128 Ns96p1368 22262444 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 22692425) qz360 0 1 Ns96p1368 Ns96p127 Ns96p1368 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 22692425) (BSN.sinOddQ 67108864) 0 1 Ns96p1368 Ns96p128 Ns96p1368 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1370 := nat_lit 2205960167197535460729369075005074226377024768256835447865391185920 

noncomputable def Ns96p1371 := nat_lit 1292063226624197806743036544463745152023695745606174872642256896 

noncomputable def Ns96p1372 := nat_lit 5775422811721867981651715994417491195979407457084539985091746594816 

noncomputable def Ns96p1373 := BSN.sin_dyadic_bound_f 77430216 67108864 3 2 67108864 33554432 Ns96p1370 Ns96p221 Ns96p1371 Ns96p1372 Ns96p224 Ns96p1371 61358281 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 77430216) qz360 0 2 Ns96p1370 Ns96p221 Ns96p1371 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 77430216) (BSN.sinOddQ 67108864) 0 2 Ns96p1372 Ns96p224 Ns96p1371 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1374 := nat_lit 2183730357827690808247863086229241255494477922263689611855795125535989467556578974877850383036078300961 

noncomputable def Ns96p1375 := nat_lit 1065158616036175907333301653015678131314802762425114690744327476930330634027719049540005366800161 

noncomputable def Ns96p1376 := nat_lit 10907427363227469686948905120413733161994180014423796453831830354620096093412097051246419677139023109921 

noncomputable def Ns96p1377 := BSN.sin_dyadic_bound_f 100527417 67108864 4 3 67108864 33554432 Ns96p1374 Ns96p762 Ns96p1375 Ns96p1376 Ns96p765 Ns96p1375 66931006 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 100527417) qz360 0 3 Ns96p1374 Ns96p762 Ns96p1375 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 100527417) (BSN.sinOddQ 67108864) 0 3 Ns96p1376 Ns96p765 Ns96p1375 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1378 := Ns96p1332 46169 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 21 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 61358281 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 25 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66931006 67108864) qz179 rfl rfl (Ns96p1363 RS097to114.d9 RS097to114.d11 RS097to114.d13 RS097to114.d17 (Ns96p1367 rfl rfl) (Ns96p1369 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns96p1362 rfl) RS097to114.d19 RS097to114.d21 RS097to114.d23 RS097to114.d25 RS097to114.d17 (Ns96p1373 rfl rfl) (Ns96p1377 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns96p1379 := nat_lit 720928117391059632451184926917364067411445072927854035669845971342331267864863422855888178319370223616 

noncomputable def Ns96p1380 := nat_lit 671793376117130646478922646587657331154723698740013835474451168112146199150431001408829114023936 

noncomputable def Ns96p1381 := nat_lit 4366152046366238272583062930465873984345358462859468951999247178050118998437899694711927394786124759040 

noncomputable def Ns96p1382 := BSN.cos_dyadic_bound_f 96739308 67108864 4 3 67108864 33554432 Ns96p1379 Ns96p236 Ns96p1380 Ns96p1381 Ns96p239 Ns96p1380 8650908 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 96739308) qz359 0 3 Ns96p1379 Ns96p236 Ns96p1380 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 96739308) (BSN.cosOddQ 67108864) 0 3 Ns96p1381 Ns96p239 Ns96p1380 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1383 := nat_lit 1452678921664803910163913714266959227832935967648883359337602283031854291334462115877592287293144109056 

noncomputable def Ns96p1384 := nat_lit 314087721813967101086184301299701030755213016511189703528305563864702362640817030643575933177856 

noncomputable def Ns96p1385 := nat_lit 7258422581566624682082791364065929592798539338758728715645395754537547378238372023847594435521855164416 

noncomputable def Ns96p1386 := BSN.sin_dyadic_bound_f 90800362 67108864 4 3 67108864 33554432 Ns96p1383 Ns96p762 Ns96p1384 Ns96p1385 Ns96p765 Ns96p1384 65523930 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 90800362) qz360 0 3 Ns96p1383 Ns96p762 Ns96p1384 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 90800362) (BSN.sinOddQ 67108864) 0 3 Ns96p1385 Ns96p765 Ns96p1384 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1387 := Ns96p1330 62230 BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 8650908 67108864) BSN.abs_quadSignNeg qz486 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 65523930 67108864) qz179 rfl rfl (Ns96p1378 rfl rfl) (Ns96p1362 rfl) RS097to114.d27 RS097to114.d29 RS097to114.d31 RS097to114.d33 RS097to114.d17 (Ns96p1382 rfl rfl) (Ns96p1386 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns96p1388 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz176) qz176 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz176) qz176 7) 182530379 67108864 62230 67108864 182530379 67108864 62230 67108864 24498812760358912 182530379 33554432 31115 16777216 (Ns96p1387 rfl) 

noncomputable def Ns96p1389 := @Enclosure.Real.IsNear.mulLit_tf qz746 (Zeta.RiemannSiegel.correction qz178) 387845 1048576 1 4194304 246812601209 549755813888 7030335032653 66520453480448000 95725033315904605 576460752303423488 

noncomputable abbrev qz749 := (@HPow.hPow Real Real Real qz7 qz177 qz9)

noncomputable def Ns96p1390 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz749 1 1 0 1 387845 1048576 1 4194304 387845 1048576 1 4194304 

noncomputable def Ns96p1391 := @Enclosure.Real.IsNear.sqrt_image qz177 28011502309 524288000 20981 524288000 30657940 30657964 4194304 (@Enclosure.Real.IsNear.of_eq qz177 (@HMul.hMul Real Real Real qz5 qz176 qz3) Bool.false 28011502309 524288000 20981 524288000 (BSN.t_div_two_pi_mk qz176 335696 1000 qz179) (@Enclosure.Real.IsNear.mulLit_ff qz176 qz3 335696 1000 0 1 1335089 8388608 1 8388608 28011502309 524288000 20981 524288000 (Enclosure.Real.IsNear.const Bool.false 335696 1000) RS097to114.d36 rfl)) 

noncomputable abbrev qz918 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 335696 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz750 := qz918

noncomputable abbrev qz526 := qz750

noncomputable abbrev qz181 := qz526

noncomputable def Ns96p1392 := @Enclosure.Real.IsNear.sqrt_image qz181 958061 131072 3 1048576 11339696 11339702 4194304 (@Enclosure.Real.IsNear.recentre' qz181 Bool.false 61315904 8388608 24 8388608 958061 131072 3 1048576 (Ns96p1391 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns96p1393 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz181) 11339699 4194304 3 4194304 1551379 1551381 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz181) Bool.false 22679398 8388608 6 8388608 11339699 4194304 3 4194304 (Ns96p1392 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns96p1394 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz181)) Bool.false 3102760 8388608 2 8388608 387845 1048576 1 4194304 (Ns96p1393 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz182 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz519))

noncomputable abbrev qz751 := (@HMul.hMul Real Real Real qz863 qz917 qz917)

noncomputable abbrev qz527 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz751 qz745) qz641)

noncomputable abbrev qz183 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz527))

noncomputable def Ns96p1395 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz178) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz182) qz183) Bool.false 246812601209 

noncomputable def Ns96p1396 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz182) qz183 5749321 2097152 299 

noncomputable abbrev qz752 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz182))

noncomputable def Ns96p1397 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz182) (@Neg.neg Real Real.instNeg qz752) Bool.true 5749321 2097152 299 2097152 (BSN.inv_eq_neg_inv_neg qz182) 

noncomputable def Ns96p1398 := @Enclosure.Real.IsNear.recentre' qz752 Bool.false 22997284 8388608 1196 8388608 5749321 2097152 

noncomputable def Ns96p1399 := @Enclosure.Real.IsNear.recentre' qz182 Bool.true 1529936 4194304 24038576 1268776960000 95621 262144 1502411 79298560000 

noncomputable abbrev qz184 := (@HMul.hMul Real Real Real qz339 qz337 qz519)

noncomputable def Ns96p1400 := @Enclosure.Real.IsNear.cos_image qz184 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16308937) qz357) Bool.false 16308937 8388608 19 1048576 Bool.true 1529936 4194304 1 

noncomputable def Ns96p1401 := nat_lit 80958226229919192183488853 

noncomputable def Ns96p1402 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz178 884279719003555 140737488355328 1 500000000000000 40557 131072 3 1048576 35863732563627180135 18446744073709551616 Ns96p1401 

noncomputable def Ns96p1403 := @Enclosure.Real.IsNear.subLit_ff_p qz181 qz1 958061 131072 3 1048576 7 1 0 1 40557 40557 131072 3 

noncomputable def Ns96p1404 := @Ns96p1403 1048576 (@Enclosure.Real.IsNear.recentre' qz181 Bool.false 61315904 8388608 24 8388608 958061 131072 3 1048576 (Ns96p1391 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns96p1405 := @Enclosure.Real.IsNear.recentre' qz184 Bool.false 35863732563627180135 18446744073709551616 Ns96p1401 Ns96p487 16308937 8388608 19 1048576 (@Ns96p1402 Ns96p487 RS097to114.d35 (Ns96p1404 rfl rfl) rfl) 

noncomputable def Ns96p1406 := nat_lit 34916416278841660149118834995221789800933234054136341959705308098682810567623269298544456161 

noncomputable def Ns96p1407 := nat_lit 354085270521127273203256541566563191121849223716553741537138242970873242084474188083681 

noncomputable def Ns96p1408 := nat_lit 210633661077669905083006400248814646482793719591145768769786011708419568928473227395946656225 

noncomputable def Ns96p1409 := BSN.cos_dyadic_bound_t 16308937 8388608 4 3 4194304 1210000 Ns96p1406 Ns96p908 Ns96p1407 Ns96p1408 Ns96p911 Ns96p1407 1529936 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16308937) (BSN.cosEvenQ 8388608) 0 3 Ns96p1406 Ns96p908 Ns96p1407 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16308937) (BSN.cosOddQ 8388608) 0 3 Ns96p1408 Ns96p911 Ns96p1407 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1410 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz182) 95621 262144 1502411 79298560000 11498044 11499240 4194304 (@Enclosure.Real.IsNear.neg qz182 Bool.true 95621 262144 1502411 79298560000 (Ns96p1399 (@Ns96p1400 1210000 (Ns96p1405 rfl) (Enclosure.sfrac_false_div 16308937 8388608) (Ns96p1409 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns96p1411 := Ns96p1397 (@Enclosure.Real.IsNear.neg qz752 Bool.false 5749321 2097152 299 2097152 (@Ns96p1398 299 2097152 (Ns96p1410 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p1412 := @Enclosure.Real.IsNear.recentre' qz183 Bool.true 686864 4194304 

noncomputable abbrev qz185 := (@HMul.hMul Real Real Real qz339 qz337 qz527)

noncomputable def Ns96p1413 := @Enclosure.Real.IsNear.cos_image qz185 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 14556737)) qz357) Bool.true 14556737 8388608 

noncomputable def Ns96p1414 := nat_lit 4195693871405798818103845 

noncomputable def Ns96p1415 := nat_lit 2417851639229258349412352 

noncomputable def Ns96p1416 := nat_lit 137425860399129215960496471619343 

noncomputable def Ns96p1417 := @Enclosure.Real.IsNear.recentre' qz185 Bool.true Ns96p1414 Ns96p1415 Ns96p1416 

noncomputable def Ns96p1418 := nat_lit 4722366482869645213696000000000000000 

noncomputable abbrev qz186 := qz527

noncomputable def Ns96p1419 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz186 884279719003555 140737488355328 1 500000000000000 4744758679 

noncomputable abbrev qz528 := (@HSub.hSub Real Real Real qz635 qz751 qz745)

noncomputable abbrev qz187 := qz528

noncomputable def Ns96p1420 := @Enclosure.Real.IsNear.subLit_tf qz187 qz26 3671016855 17179869184 5092473 1099511627776 1 16 

noncomputable abbrev qz529 := qz751

noncomputable abbrev qz188 := qz529

noncomputable def Ns96p1421 := @Enclosure.Real.IsNear.subLit_ff_n qz188 qz178 1644870249 17179869184 1946745 1099511627776 40557 131072 3 1048576 

noncomputable def Ns96p1422 := @Enclosure.Real.IsNear.mulLit_ff qz178 qz178 40557 131072 3 1048576 40557 131072 3 1048576 1644870249 17179869184 

noncomputable def Ns96p1423 := nat_lit 22092284047140445217156886455013667141384810981966217248822351960191927689214643010187528961 

noncomputable def Ns96p1424 := nat_lit 90524977779631347728358692970730556554634018092725824763550952663685592297359213300481 

noncomputable def Ns96p1425 := nat_lit 133546389430971648487455073659734256425935165056156273812746475960124117909580958643500845825 

noncomputable def Ns96p1426 := BSN.cos_dyadic_bound_t 14556737 8388608 4 3 4194304 1210000 Ns96p1423 Ns96p908 Ns96p1424 Ns96p1425 Ns96p911 Ns96p1424 686864 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 14556737) (BSN.cosEvenQ 8388608) 0 3 Ns96p1423 Ns96p908 Ns96p1424 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 14556737) (BSN.cosOddQ 8388608) 0 3 Ns96p1425 Ns96p911 Ns96p1424 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1427 := @Ns96p1412 304838608 10150215680000 42929 262144 19052413 634388480000 (@Ns96p1413 245 8388608 Bool.true 686864 4194304 1 1210000 (@Ns96p1417 Ns96p1418 14556737 8388608 245 8388608 (@Ns96p1419 17179869184 5092473 1099511627776 Ns96p1414 Ns96p1415 Ns96p1416 Ns96p1418 RS097to114.d35 (@Ns96p1420 0 1 75916138864 4744758679 17179869184 5092473 1099511627776 (@Ns96p1421 481167521218560 3671016855 17179869184 5092473 1099511627776 (@Ns96p1422 1946745 1099511627776 (Ns96p1404 rfl rfl) (Ns96p1404 rfl rfl) rfl) (Ns96p1404 rfl rfl) rfl rfl) qz369 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 14556737 8388608) (BSN.cos_neg_of_bound 14556737 8388608 Bool.true 686864 4194304 1 1210000 (Ns96p1426 rfl rfl)) rfl rfl) 

noncomputable def Ns96p1428 := @Ns96p1389 10936592518038532793 279007004114856968192000 (Ns96p1390 qz28 (@Enclosure.Real.IsNear.of_eq qz749 (@Inv.inv Real Real.instInv (Real.sqrt qz181)) Bool.false 387845 1048576 1 4194304 (BSN.rpow_neg_quarter_mk qz177 (BSN.t_div_two_pi_nonneg qz176 335696 1000 qz179)) Ns96p1394) rfl) (@Ns96p1395 549755813888 7030335032653 66520453480448000 (BSN.correction_mk qz178 (BSN.cos_two_pi_p_ne_zero_mk qz176 335696 1000 7 qz179 rfl rfl (@BSN.floor_sqrt_eq_dec qz176 335696 1000 7 qz179 rfl rfl rfl))) (@Ns96p1396 2097152 42929 262144 19052413 634388480000 246812601209 549755813888 7030335032653 66520453480448000 Ns96p1411 (Ns96p1427 rfl) rfl)) 

noncomputable def Ns96p1429 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz176) (hardyZApproximantRS₀ qz176) Bool.true 3040123000010036131 576460752303423488 528382570029073412793 279007004114856968192000 (@Eq.refl Real (hardyZApproximantRS₀ qz176)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz176) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz176) qz176 7) (@HMul.hMul Real Real Real qz5 qz746 (Zeta.RiemannSiegel.correction qz178))) Bool.true 3040123000010036131 576460752303423488 528382570029073412793 279007004114856968192000 (BSN.hardyZApproximantRS₀_eq qz176 7 (@BSN.floor_sqrt_eq_dec qz176 335696 1000 7 qz179 rfl rfl rfl)) (@Ns96p1328 3040123000010036131 576460752303423488 528382570029073412793 279007004114856968192000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz176) qz176 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz176) qz176 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz176) qz176 7)) Bool.true 182530379 33554432 31115 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz176) qz176 7) (Ns96p1388 (Ns96p1387 rfl) rfl rfl)) (Ns96p1428 rfl) rfl rfl)) 

theorem RS097to114.d51 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz176) Bool.true 3040123000010036131 576460752303423488 528382570029073412793 279007004114856968192000 := Ns96p1429 

noncomputable def Ns96p1430 := nat_lit 11160280164594278727680000 

noncomputable def Ns96p1431 := nat_lit 8613850542082168534926884864 

noncomputable abbrev qz919 := (Enclosure.sfrac Bool.false 337274 1000)

noncomputable abbrev qz753 := qz919

noncomputable abbrev qz530 := qz753

noncomputable abbrev qz189 := qz530

noncomputable abbrev qz920 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 337274 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz754 := qz920

noncomputable abbrev qz531 := qz754

noncomputable abbrev qz190 := qz531

noncomputable abbrev qz921 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 337274 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz755 := qz921

noncomputable abbrev qz532 := qz755

noncomputable abbrev qz191 := qz532

noncomputable abbrev qz756 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz190 qz9))

noncomputable def Ns96p1432 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz189) qz189 7) (@HMul.hMul Real Real Real qz5 qz756 (Zeta.RiemannSiegel.correction qz191)) 52950363 33554432 62515 33554432 23834591600716484125 147573952589676412928 348396600563627477387 Ns96p1430 Ns96p1431 

noncomputable def Ns96p1433 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz189) qz189 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 337274 1000 64 97 67108864 33554432 1125899906842624 Bool.false 33732583708 1274 

noncomputable def Ns96p1434 := Ns96p1433 120242927 57 27397080 8 130587807 57 25364760 8 Bool.false 65536891 46379 Bool.true 75710400 Bool.true 86095674 3537118876014220 1 Bool.false 28743502 Bool.false Bool.false 64347370 Bool.true Bool.false 52950363 

noncomputable def Ns96p1435 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz189) qz189 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 337274 1000 22 25 67108864 33554432 1125899906842624 Bool.false 33732583708 1274 

noncomputable def Ns96p1436 := Ns96p1435 93032624 56 33554424 8 108007536 56 30011992 8 Bool.false 117834021 27262 Bool.false 35982625 Bool.true 60191062 3537118876014220 1 Bool.false 57691137 Bool.true Bool.false 52439308 Bool.true Bool.false 65536891 

noncomputable def Ns96p1437 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz189) qz189 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 337274 1000 171 84 67108864 33554432 1125899906842624 Bool.false 33732583708 1274 

noncomputable def Ns96p1438 := Ns96p1437 46516304 56 47453136 16 73726608 56 38745320 8 Bool.false 67108856 1336 Bool.false 17988734 Bool.false 11709727 3537118876014220 1 Bool.false 17774084 Bool.false Bool.false 66089846 Bool.false Bool.false 117834021 

noncomputable def Ns96p1439 := nat_lit 18743559275931826131281768235963515329337151883780961 

noncomputable def Ns96p1440 := nat_lit 37289138039039750968821118188158807165732168663040 

noncomputable def Ns96p1441 := nat_lit 2094874314423783084475012459520000 

noncomputable def Ns96p1442 := nat_lit 4239284185023251549048509126368890880 

noncomputable abbrev qz533 := (@Eq.refl Real qz753)

noncomputable abbrev qz192 := qz533

noncomputable def Ns96p1443 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz189 337274 1000 455016004304 16000000 674548 4000 2000 Ns96p1441 Ns96p1442 qz192 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns96p1444 := nat_lit 383868093971083799168650613472532793944824870579834081280 

noncomputable abbrev qz757 := (Real.log (Enclosure.sfrac Bool.false 455016004304 16000000))

noncomputable abbrev qz193 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 337274 4000) qz757) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 674548))))))

noncomputable abbrev qz758 := (Enclosure.sfrac Bool.false 337274 2000)

noncomputable abbrev qz534 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz193 qz758) (@HMul.hMul Real Real Real qz5 qz758 (Real.log Real.pi)))

noncomputable def Ns96p1445 := @Enclosure.Real.IsNear.addLit_ft_p qz534 (Enclosure.sfrac Bool.true Ns96p1441 Ns96p1442) 90550303918345506581 180143985094819840 1175152004633680593 61952000000000000000000 Ns96p1441 Ns96p1442 0 1 Ns96p1444 

noncomputable def Ns96p1446 := nat_lit 75959100385186446326942924800000 

noncomputable abbrev qz535 := (@HSub.hSub Real Real Real qz12 qz193 qz758)

noncomputable abbrev qz536 := (@HMul.hMul Real Real Real qz5 qz758 (Real.log Real.pi))

noncomputable def Ns96p1447 := @Enclosure.Real.IsNear.subLit_ff_p qz535 qz536 3133149643114339940621 4503599627370496000 134872674106333 15125000000000000000 6477475502757 33554432000 168637 16777216000 Ns96p1446 90550303918345506581 180143985094819840 

noncomputable def Ns96p1448 := nat_lit 6266299286228679881242000 

noncomputable abbrev qz537 := qz758

noncomputable def Ns96p1449 := @Enclosure.Real.IsNear.subLit_ff_p qz193 qz537 3892623173475218274573 4503599627370496000 134872674106333 15125000000000000000 337274 2000 0 1 Ns96p1448 3133149643114339940621 4503599627370496000 134872674106333 15125000000000000000 

noncomputable def Ns96p1450 := nat_lit 8765408136778375315195210427063599104 

noncomputable def Ns96p1451 := nat_lit 12398137688468482370306048 

noncomputable def Ns96p1452 := nat_lit 2501270032126689311734039135345280140523801594138982685699462260856271809706876224866424645402436110780659502586104466044783948730975160816013148160 

noncomputable def Ns96p1453 := nat_lit 63064207535185047289829262549941265542253756007878096853385337454090597282275224784454736700791067625345054264373889982788836329739435120737124352 

noncomputable def Ns96p1454 := nat_lit 27545763687278814369848943123462452813588360313368934085629418920811230319721093615105944168451711643656958574561921229344055354976444088320 

noncomputable def Ns96p1455 := BSN.log_dyadic_bound 192872004304 717160004304 7 6 Ns96p1452 33554432 9680000 Ns96p1453 Ns96p1454 18503209 910032008608 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 192872004304) (BSN.artanhQ 717160004304) 0 6 Ns96p1453 Ns96p1452 Ns96p1454 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns96p1456 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 337274 4000) qz757 337274 4000 0 1 23093331024923329 2251799813685248 6250000847 60500000000000000 3894390064049995432573 4503599627370496000 1053981392835539 121000000000000000000 (Enclosure.Real.IsNear.const Bool.false 337274 4000) (BSN.isNear_log_sfrac 455016004304 16000000 23093331024923329 2251799813685248 6250000847 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 455016004304) qz350)) Bool.false Ns96p1451 Ns96p86 1000000135520000 9680000000000000000000 23093331024923329 2251799813685248 6250000847 60500000000000000 (BSN.log_rat_reduce_isNear 455016004304 16000000 14 910032008608 524288000000 18503209 33554432 24973259072661432 36028797018963968 9680000 1000000000000000 rfl rfl rfl rfl (Ns96p1455 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p1457 := BSN.arctan_dyadic_bound_f 1000 674548 1 0 4194304 1210000 0 1 1 0 1 1 6217 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 674548) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 674548) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz538 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 674548)))

noncomputable def Ns96p1458 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz538 884279719003555 562949953421312 1 2000000000000000 6217 4194304 1 1210000 3705438102675066454016 883445287388579 562949953421312 200000000121 242000000000000000 qz17 (Ns96p1457 rfl) rfl rfl 

noncomputable def Ns96p1459 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 337274 4000) qz757) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz538)) 3894390064049995432573 4503599627370496000 1053981392835539 121000000000000000000 883445287388579 2251799813685248 200000000121 968000000000000000 Ns96p1450 3892623173475218274573 4503599627370496000 134872674106333 15125000000000000000 (Ns96p1456 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz538) 1 4 0 1 883445287388579 562949953421312 200000000121 242000000000000000 883445287388579 2251799813685248 200000000121 968000000000000000 qz353 Ns96p1458 rfl) 

noncomputable def Ns96p1460 := @Ns96p1445 Ns96p1439 Ns96p1440 1175152004633680593 61952000000000000000000 (@Ns96p1447 1175152004633680593 61952000000000000000000 (Ns96p1449 (Ns96p1459 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 337274 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz537 (Real.log Real.pi) 337274 2000 0 1 38410761 33554432 1 16777216 6477475502757 33554432000 168637 16777216000 (Enclosure.Real.IsNear.const Bool.false 337274 2000) RS097to114.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns96p1441 Ns96p1442) 

noncomputable def Ns96p1461 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz189) Bool.false Ns96p1439 Ns96p1440 1175152004633680593 61952000000000000000000 4216572963 8388608 5 262144 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz189) (@HAdd.hAdd Real Real Real qz354 qz534 (Enclosure.sfrac Bool.true Ns96p1441 Ns96p1442)) Bool.false Ns96p1439 Ns96p1440 1175152004633680593 61952000000000000000000 Ns96p1443 (Ns96p1460 rfl rfl)) 

noncomputable def Ns96p1462 := nat_lit 1898786053317882938392576 

noncomputable def Ns96p1463 := nat_lit 139932709174759061224833798748492216384950647950223174490081839217222789566832632070400 

noncomputable def Ns96p1464 := nat_lit 281041115562411498530546546110049193576136416597317597434610079644044391769598525696 

noncomputable def Ns96p1465 := nat_lit 366035409842029827448372397552349058504318904718950752316272591154255043659791829238016 

noncomputable def Ns96p1466 := BSN.sin_dyadic_bound_f 26983372738 17179869184 3 2 8388608 2422364 Ns96p1463 Ns96p99 Ns96p1464 Ns96p1465 Ns96p102 Ns96p1464 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26983372738) qz355 0 2 Ns96p1463 Ns96p99 Ns96p1464 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26983372738) qz356 0 2 Ns96p1465 Ns96p102 Ns96p1464 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1467 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz189) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4216572963) qz357) Bool.false 4216572963 8388608 5 262144 Bool.false 8388607 8388608 1 1210000 (Ns96p1461 rfl) (Enclosure.sfrac_false_div 4216572963 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4216572963) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns96p1462) qz358) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 79 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q3 4216572963 8388608 226375608064910080 72057594037927936 79 Ns96p1462 Ns96p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns96p1462 Ns96p86 26983372738 17179869184 2422364 2420000 (Ns96p1466 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p1468 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz189) Bool.false Ns96p1439 Ns96p1440 1175152004633680593 61952000000000000000000 33732583708 67108864 1274 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz189) (@HAdd.hAdd Real Real Real qz354 qz534 (Enclosure.sfrac Bool.true Ns96p1441 Ns96p1442)) Bool.false Ns96p1439 Ns96p1440 1175152004633680593 61952000000000000000000 Ns96p1443 (Ns96p1460 rfl rfl)) 

noncomputable def Ns96p1469 := Ns96p1438 27262 BSN.abs_quadSignPos (BSN.cos_quad_nat3 171 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 17774084 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 84 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66089846 67108864) qz192 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz189) qz189 1) Bool.false 8388607 8388608 394509 19824640000 67108856 67108864 1336 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz189) qz189 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz189)) Bool.false 8388607 8388608 394509 19824640000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz189) qz189) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz189)) Bool.false 8388607 8388608 6312144 317194240000 8388607 8388608 394509 19824640000 (Ns96p1467 rfl rfl) rfl)) rfl) (Ns96p1468 rfl) RS097to114.d7 

noncomputable def Ns96p1470 := nat_lit 104713433386900126011078635536 

noncomputable def Ns96p1471 := BSN.sin_dyadic_bound_f 17988734 67108864 2 1 67108864 33554432 Ns96p1470 Ns96p127 Ns96p1470 Ns96p1470 Ns96p128 Ns96p1470 17774084 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 17988734) qz360 0 1 Ns96p1470 Ns96p127 Ns96p1470 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 17988734) (BSN.sinOddQ 67108864) 0 1 Ns96p1470 Ns96p128 Ns96p1470 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1472 := nat_lit 18801265412380967272782291841 

noncomputable def Ns96p1473 := BSN.cos_dyadic_bound_f 11709727 67108864 2 1 67108864 33554432 Ns96p1472 Ns96p131 Ns96p1472 Ns96p1472 Ns96p132 Ns96p1472 66089846 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 11709727) qz359 0 1 Ns96p1472 Ns96p131 Ns96p1472 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 11709727) (BSN.cosOddQ 67108864) 0 1 Ns96p1472 Ns96p132 Ns96p1472 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1474 := nat_lit 57124388944093654891318360106702331566385789971593716480712890625 

noncomputable def Ns96p1475 := nat_lit 2810235671101095519670432032292220918802480757236480712890625 

noncomputable def Ns96p1476 := nat_lit 171367546360938762482915739456042410257319764953266676480712890625 

noncomputable def Ns96p1477 := BSN.cos_dyadic_bound_f 35982625 67108864 3 2 67108864 33554432 Ns96p1474 Ns96p108 Ns96p1475 Ns96p1476 Ns96p111 Ns96p1475 57691137 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 35982625) qz359 0 2 Ns96p1474 Ns96p108 Ns96p1475 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 35982625) (BSN.cosOddQ 67108864) 0 2 Ns96p1476 Ns96p111 Ns96p1475 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1478 := nat_lit 805234347820404191885983393845611620763351986061645082564759281920 

noncomputable def Ns96p1479 := nat_lit 172288404046318239258191082721342508193169642994443427543408896 

noncomputable def Ns96p1480 := nat_lit 2108668158304031225409252769747433976033609117406127069739299266816 

noncomputable def Ns96p1481 := BSN.sin_dyadic_bound_f 60191062 67108864 3 2 67108864 33554432 Ns96p1478 Ns96p221 Ns96p1479 Ns96p1480 Ns96p224 Ns96p1479 52439308 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 60191062) qz360 0 2 Ns96p1478 Ns96p221 Ns96p1479 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 60191062) (BSN.sinOddQ 67108864) 0 2 Ns96p1480 Ns96p224 Ns96p1479 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1482 := Ns96p1436 46379 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 22 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 57691137 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 25 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 52439308 67108864) qz192 rfl rfl (Ns96p1469 RS097to114.d9 RS097to114.d11 RS097to114.d13 RS097to114.d17 (Ns96p1471 rfl rfl) (Ns96p1473 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns96p1468 rfl) RS097to114.d19 RS097to114.d21 RS097to114.d23 RS097to114.d25 RS097to114.d17 (Ns96p1477 rfl rfl) (Ns96p1481 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns96p1483 := nat_lit 270026017062659384659402297473591076819170963597453845521069964569814665024331178779596554240000000000 

noncomputable def Ns96p1484 := nat_lit 35470432856164301542090054572269892441203414507705892937819384254038016000000000000000000000000 

noncomputable def Ns96p1485 := nat_lit 1637105600325878330839587703254783971269051283721910399185919771830658064094164595637072429056000000000 

noncomputable def Ns96p1486 := BSN.cos_dyadic_bound_f 75710400 67108864 4 3 67108864 33554432 Ns96p1483 Ns96p236 Ns96p1484 Ns96p1485 Ns96p239 Ns96p1484 28743502 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 75710400) qz359 0 3 Ns96p1483 Ns96p236 Ns96p1484 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 75710400) (BSN.cosOddQ 67108864) 0 3 Ns96p1485 Ns96p239 Ns96p1484 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1487 := nat_lit 3372993741172920238863342618705786594028850964218198484813280354560 

noncomputable def Ns96p1488 := nat_lit 3018913309199836171205242315583367378664030520089575305931038976 

noncomputable def Ns96p1489 := nat_lit 8829143462476086605126803132861353722891058380681803385920417341696 

noncomputable def Ns96p1490 := BSN.sin_dyadic_bound_f 86095674 67108864 3 2 67108864 33554432 Ns96p1487 Ns96p221 Ns96p1488 Ns96p1489 Ns96p224 Ns96p1488 64347370 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 86095674) qz360 0 2 Ns96p1487 Ns96p221 Ns96p1488 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 86095674) (BSN.sinOddQ 67108864) 0 2 Ns96p1489 Ns96p224 Ns96p1488 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1491 := Ns96p1434 62515 BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 28743502 67108864) BSN.abs_quadSignNeg qz486 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 64347370 67108864) qz192 rfl rfl (Ns96p1482 rfl rfl) (Ns96p1468 rfl) RS097to114.d27 RS097to114.d29 RS097to114.d31 RS097to114.d33 RS097to114.d17 (Ns96p1486 rfl rfl) (Ns96p1490 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns96p1492 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz189) qz189 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz189) qz189 7) 52950363 67108864 62515 67108864 52950363 67108864 62515 67108864 7106877418635264 52950363 33554432 62515 33554432 (Ns96p1491 rfl) 

noncomputable def Ns96p1493 := @Enclosure.Real.IsNear.mulLit_tf qz756 (Zeta.RiemannSiegel.correction qz191) 3099125 8388608 1 8388608 7690748711561 17592186044416 112230024752887 1330409069608960000 23834591600716484125 147573952589676412928 

noncomputable abbrev qz759 := (@HPow.hPow Real Real Real qz7 qz190 qz9)

noncomputable def Ns96p1494 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz759 1 1 0 1 3099125 8388608 1 8388608 3099125 8388608 1 8388608 

noncomputable def Ns96p1495 := @Enclosure.Real.IsNear.sqrt_image qz190 225145403693 4194304000 168637 4194304000 30729913 30729937 4194304 (@Enclosure.Real.IsNear.of_eq qz190 (@HMul.hMul Real Real Real qz5 qz189 qz3) Bool.false 225145403693 4194304000 168637 4194304000 (BSN.t_div_two_pi_mk qz189 337274 1000 qz192) (@Enclosure.Real.IsNear.mulLit_ff qz189 qz3 337274 1000 0 1 1335089 8388608 1 8388608 225145403693 4194304000 168637 4194304000 (Enclosure.Real.IsNear.const Bool.false 337274 1000) RS097to114.d36 rfl)) 

noncomputable abbrev qz922 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 337274 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz760 := qz922

noncomputable abbrev qz539 := qz760

noncomputable abbrev qz194 := qz539

noncomputable def Ns96p1496 := @Enclosure.Real.IsNear.sqrt_image qz194 30729925 4194304 3 1048576 11352999 11353004 4194304 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 61459850 8388608 24 8388608 30729925 4194304 3 1048576 (Ns96p1495 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns96p1497 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz194) 22706003 8388608 5 8388608 1549562 1549563 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz194) Bool.false 22706003 8388608 5 8388608 22706003 8388608 5 8388608 (Ns96p1496 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns96p1498 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz194)) Bool.false 3099125 8388608 1 8388608 3099125 8388608 1 8388608 (Ns96p1497 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz195 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz532))

noncomputable abbrev qz761 := (@HMul.hMul Real Real Real qz863 qz921 qz921)

noncomputable abbrev qz540 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz761 qz755) qz641)

noncomputable abbrev qz196 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz540))

noncomputable def Ns96p1499 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz191) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz195) qz196) Bool.false 7690748711561 

noncomputable def Ns96p1500 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz195) qz196 18124153 8388608 743 

noncomputable abbrev qz762 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz195))

noncomputable def Ns96p1501 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz195) (@Neg.neg Real Real.instNeg qz762) Bool.true 18124153 8388608 743 8388608 (BSN.inv_eq_neg_inv_neg qz195) 

noncomputable def Ns96p1502 := @Enclosure.Real.IsNear.recentre' qz762 Bool.false 18124153 8388608 743 8388608 18124153 8388608 

noncomputable def Ns96p1503 := @Enclosure.Real.IsNear.recentre' qz195 Bool.true 3882595 8388608 24038576 1268776960000 3882595 8388608 1502411 79298560000 

noncomputable abbrev qz197 := (@HMul.hMul Real Real Real qz339 qz337 qz532)

noncomputable def Ns96p1504 := @Enclosure.Real.IsNear.cos_image qz197 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 268959) (@Nat.cast Real Real.instNatCast 131072)) Bool.false 268959 131072 19 1048576 Bool.true 3882595 8388608 1 

noncomputable def Ns96p1505 := nat_lit 80958226230073753024086357 

noncomputable def Ns96p1506 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz191 884279719003555 140737488355328 1 500000000000000 1369797 4194304 3 1048576 1211283706251912628335 590295810358705651712 Ns96p1505 

noncomputable def Ns96p1507 := @Enclosure.Real.IsNear.subLit_ff_p qz194 qz1 30729925 4194304 3 1048576 7 1 0 1 1369797 1369797 4194304 3 

noncomputable def Ns96p1508 := @Ns96p1507 1048576 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 61459850 8388608 24 8388608 30729925 4194304 3 1048576 (Ns96p1495 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns96p1509 := @Enclosure.Real.IsNear.recentre' qz197 Bool.false 1211283706251912628335 590295810358705651712 Ns96p1505 Ns96p487 268959 131072 19 1048576 (@Ns96p1506 Ns96p487 RS097to114.d35 (Ns96p1508 rfl rfl) rfl) 

noncomputable def Ns96p1510 := nat_lit 4670621277894404775339101105174061201936 

noncomputable def Ns96p1511 := nat_lit 10453474311811229597594867940303919455928320 

noncomputable def Ns96p1512 := nat_lit 73174320182678607183164075582127436191498240 

noncomputable def Ns96p1513 := BSN.sin_dyadic_bound_f 8266918638 17179869184 2 1 8388608 2422364 Ns96p1510 Ns96p1511 Ns96p1510 Ns96p1510 Ns96p1512 Ns96p1510 3882595 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 8266918638) qz355 0 1 Ns96p1510 Ns96p1511 Ns96p1510 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 8266918638) qz356 0 1 Ns96p1510 Ns96p1512 Ns96p1510 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1514 := @Ns96p1504 1210000 (Ns96p1509 rfl) (Enclosure.sfrac_false_div 268959 131072) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 268959) (@Nat.cast Real Real.instNatCast 131072)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9089573169410225471488) (@Nat.cast Real Real.instNatCast 18889465931478580854784)) 226375608064910080 72057594037927936 Bool.false 3882595 8388608 0 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q1 268959 131072 226375608064910080 72057594037927936 0 9089573169410225471488 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 3882595 8388608 9089573169410225471488 18889465931478580854784 8266918638 17179869184 2422364 2420000 (Ns96p1513 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p1515 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz195) 3882595 8388608 1502411 79298560000 9061705 9062448 4194304 (@Enclosure.Real.IsNear.neg qz195 Bool.true 3882595 8388608 1502411 79298560000 (Ns96p1503 (Ns96p1514 rfl rfl) rfl)) 

noncomputable def Ns96p1516 := Ns96p1501 (@Enclosure.Real.IsNear.neg qz762 Bool.false 18124153 8388608 743 8388608 (@Ns96p1502 743 8388608 (Ns96p1515 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p1517 := @Enclosure.Real.IsNear.recentre' qz196 Bool.true 848674 4194304 

noncomputable abbrev qz198 := (@HMul.hMul Real Real Real qz339 qz337 qz540)

noncomputable def Ns96p1518 := @Enclosure.Real.IsNear.cos_image qz198 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 14885943)) qz357) Bool.true 14885943 8388608 

noncomputable def Ns96p1519 := nat_lit 4393555140545373620901349525 

noncomputable def Ns96p1520 := nat_lit 11227141088584871835021221240959 

noncomputable def Ns96p1521 := @Enclosure.Real.IsNear.recentre' qz198 Bool.true Ns96p1519 Ns96p500 Ns96p1520 

noncomputable def Ns96p1522 := nat_lit 377789318629571617095680000000000000 

noncomputable abbrev qz199 := qz540

noncomputable def Ns96p1523 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz199 884279719003555 140737488355328 1 500000000000000 4968512842855 

noncomputable abbrev qz541 := (@HSub.hSub Real Real Real qz635 qz761 qz755)

noncomputable abbrev qz200 := qz541

noncomputable def Ns96p1524 := @Enclosure.Real.IsNear.subLit_tf qz200 qz26 3869001215079 17592186044416 10400865 2199023255552 1 16 

noncomputable abbrev qz542 := qz761

noncomputable abbrev qz201 := qz542

noncomputable def Ns96p1525 := @Enclosure.Real.IsNear.subLit_ff_n qz201 qz191 1876343821209 17592186044416 4109409 2199023255552 1369797 4194304 3 1048576 

noncomputable def Ns96p1526 := @Enclosure.Real.IsNear.mulLit_ff qz191 qz191 1369797 4194304 3 1048576 1369797 4194304 3 1048576 1876343821209 17592186044416 

noncomputable def Ns96p1527 := nat_lit 24171764205027005241412989420093312808552360400242449637413408207500766998910036888385510881 

noncomputable def Ns96p1528 := nat_lit 118390327064492387398541531304283004996522717713685514316275448000129300072072995692001 

noncomputable def Ns96p1529 := nat_lit 146067788008263359495210947930645715437721106895681291328347526682020856544964655680383376865 

noncomputable def Ns96p1530 := BSN.cos_dyadic_bound_t 14885943 8388608 4 3 4194304 1210000 Ns96p1527 Ns96p908 Ns96p1528 Ns96p1529 Ns96p911 Ns96p1528 848674 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 14885943) (BSN.cosEvenQ 8388608) 0 3 Ns96p1527 Ns96p908 Ns96p1528 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 14885943) (BSN.cosOddQ 8388608) 0 3 Ns96p1529 Ns96p911 Ns96p1528 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1531 := @Ns96p1517 312098608 10150215680000 424337 2097152 19506163 634388480000 (@Ns96p1518 251 8388608 Bool.true 848674 4194304 1 1210000 (@Ns96p1521 Ns96p1522 14885943 8388608 251 8388608 (@Ns96p1523 17592186044416 10400865 2199023255552 Ns96p1519 Ns96p500 Ns96p1520 Ns96p1522 RS097to114.d35 (@Ns96p1524 0 1 79496205485680 4968512842855 17592186044416 10400865 2199023255552 (@Ns96p1525 16227767272410710016 3869001215079 17592186044416 10400865 2199023255552 (@Ns96p1526 4109409 2199023255552 (Ns96p1508 rfl rfl) (Ns96p1508 rfl rfl) rfl) (Ns96p1508 rfl rfl) rfl rfl) qz369 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 14885943 8388608) (BSN.cos_neg_of_bound 14885943 8388608 Bool.true 848674 4194304 1 1210000 (Ns96p1530 rfl rfl)) rfl rfl) 

noncomputable def Ns96p1532 := @Ns96p1493 348396600563627477387 Ns96p1430 (Ns96p1494 qz28 (@Enclosure.Real.IsNear.of_eq qz759 (@Inv.inv Real Real.instInv (Real.sqrt qz194)) Bool.false 3099125 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz190 (BSN.t_div_two_pi_nonneg qz189 337274 1000 qz192)) Ns96p1498) rfl) (@Ns96p1499 17592186044416 112230024752887 1330409069608960000 (BSN.correction_mk qz191 (BSN.cos_two_pi_p_ne_zero_mk qz189 337274 1000 7 qz192 rfl rfl (@BSN.floor_sqrt_eq_dec qz189 337274 1000 7 qz192 rfl rfl rfl))) (@Ns96p1500 8388608 424337 2097152 19506163 634388480000 7690748711561 17592186044416 112230024752887 1330409069608960000 Ns96p1516 (Ns96p1531 rfl) rfl)) 

noncomputable def Ns96p1533 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz189) (hardyZApproximantRS₀ qz189) Bool.false 256712750854556814877 147573952589676412928 21141027347214661077387 Ns96p1430 (@Eq.refl Real (hardyZApproximantRS₀ qz189)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz189) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz189) qz189 7) (@HMul.hMul Real Real Real qz5 qz756 (Zeta.RiemannSiegel.correction qz191))) Bool.false 256712750854556814877 147573952589676412928 21141027347214661077387 Ns96p1430 (BSN.hardyZApproximantRS₀_eq qz189 7 (@BSN.floor_sqrt_eq_dec qz189 337274 1000 7 qz192 rfl rfl rfl)) (@Ns96p1432 256712750854556814877 147573952589676412928 21141027347214661077387 Ns96p1430 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz189) qz189 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz189) qz189 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz189) qz189 7)) Bool.false 52950363 33554432 62515 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz189) qz189 7) (Ns96p1492 (Ns96p1491 rfl) rfl rfl)) (Ns96p1532 rfl) rfl rfl)) 

theorem RS097to114.d52 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz189) Bool.false 256712750854556814877 147573952589676412928 21141027347214661077387 Ns96p1430 := Ns96p1533 

noncomputable def Ns96p1534 := nat_lit 1610978663367311370569646080 

noncomputable abbrev qz923 := (Enclosure.sfrac Bool.false 338851 1000)

noncomputable abbrev qz763 := qz923

noncomputable abbrev qz543 := qz763

noncomputable abbrev qz202 := qz543

noncomputable abbrev qz924 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 338851 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz764 := qz924

noncomputable abbrev qz544 := qz764

noncomputable abbrev qz203 := qz544

noncomputable abbrev qz925 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 338851 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz765 := qz925

noncomputable abbrev qz545 := qz765

noncomputable abbrev qz204 := qz545

noncomputable abbrev qz766 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz203 qz9))

noncomputable def Ns96p1535 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz202) qz202 7) (@HMul.hMul Real Real Real qz5 qz766 (Zeta.RiemannSiegel.correction qz204)) 48948641 33554432 31405 16777216 5808694457961958351 36893488147419103232 146088452741054210701 Ns96p180 Ns96p1534 

noncomputable def Ns96p1536 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz202) qz202 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 338851 1000 64 97 67108864 33554432 1125899906842624 Bool.false 33943470071 1280 

noncomputable def Ns96p1537 := Ns96p1536 120242927 57 27397080 8 130587807 57 25364760 8 Bool.true 44088296 46598 Bool.true 54447133 Bool.true 81146283 3537118876014220 1 Bool.false 46206988 Bool.false Bool.false 62768533 Bool.true Bool.true 48948641 

noncomputable def Ns96p1538 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz202) qz202 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 338851 1000 22 25 67108864 33554432 1125899906842624 Bool.false 33943470071 1280 

noncomputable def Ns96p1539 := Ns96p1538 93032624 56 33554424 8 108007536 56 30011992 8 Bool.true 32806823 27391 Bool.false 100156540 Bool.true 19632583 3537118876014220 1 Bool.false 5252439 Bool.true Bool.false 19353738 Bool.true Bool.true 44088296 

noncomputable def Ns96p1540 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz202) qz202 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 338851 1000 172 85 67108864 33554432 1125899906842624 Bool.false 33943470071 1280 

noncomputable def Ns96p1541 := Ns96p1540 46516304 56 47453136 16 73726608 56 38745320 8 Bool.true 67108840 1344 Bool.false 50104528 Bool.false 914872 3537118876014220 1 Bool.false 49257341 Bool.false Bool.false 914843 Bool.true Bool.true 32806823 

noncomputable def Ns96p1542 := nat_lit 62067477804564036696475428656071164707243718184314694451 

noncomputable def Ns96p1543 := nat_lit 122712201139695604996362630524689789448951565385728000 

noncomputable def Ns96p1544 := nat_lit 2144309605929176660109865240480000 

noncomputable def Ns96p1545 := nat_lit 4359613155447149956826629254347330880 

noncomputable abbrev qz546 := (@Eq.refl Real qz763)

noncomputable abbrev qz205 := qz546

noncomputable def Ns96p1546 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz202 338851 1000 459281000804 16000000 677702 4000 2000 Ns96p1544 Ns96p1545 qz205 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns96p1547 := nat_lit 19861592897460491742872137169942772706317989818980702224320 

noncomputable abbrev qz767 := (Real.log (Enclosure.sfrac Bool.false 459281000804 16000000))

noncomputable abbrev qz206 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 338851 4000) qz767) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 677702))))))

noncomputable abbrev qz768 := (Enclosure.sfrac Bool.false 338851 2000)

noncomputable abbrev qz547 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz206 qz768) (@HMul.hMul Real Real Real qz5 qz768 (Real.log Real.pi)))

noncomputable def Ns96p1548 := @Enclosure.Real.IsNear.addLit_ft_p qz547 (Enclosure.sfrac Bool.true Ns96p1544 Ns96p1545) 4555819863711564001539 9007199254740992000 2361173682656327439 123904000000000000000000 Ns96p1544 Ns96p1545 0 1 Ns96p1547 

noncomputable def Ns96p1549 := nat_lit 305735895642317883806576541696000 

noncomputable abbrev qz548 := (@HSub.hSub Real Real Real qz12 qz206 qz768)

noncomputable abbrev qz549 := (@HMul.hMul Real Real Real qz5 qz768 (Real.log Real.pi))

noncomputable def Ns96p1550 := @Enclosure.Real.IsNear.subLit_ff_p qz548 qz549 6302734027821782233347 9007199254740992000 2167819037037047 242000000000000000000 13015524775611 67108864000 338851 33554432000 Ns96p1549 4555819863711564001539 9007199254740992000 

noncomputable def Ns96p1551 := nat_lit 12605468055643564466694000 

noncomputable abbrev qz550 := qz768

noncomputable def Ns96p1552 := @Enclosure.Real.IsNear.subLit_ff_p qz206 qz550 7828783265155902173443 9007199254740992000 2167819037037047 242000000000000000000 338851 2000 0 1 Ns96p1551 6302734027821782233347 9007199254740992000 2167819037037047 242000000000000000000 

noncomputable def Ns96p1553 := nat_lit 17628852697860248004886792618706468864 

noncomputable def Ns96p1554 := nat_lit 12409416539404066059452416 

noncomputable def Ns96p1555 := nat_lit 2685728509456695022332342678229602809030461338853062276857711037774737494180307359223477578966640276318462034401004014401762032432834301128773468160 

noncomputable def Ns96p1556 := nat_lit 70013623361521227665414451924148919209372367387728918046777061291275249628151195518499208053831472306362626461229017390210361905377080728566628352 

noncomputable def Ns96p1557 := nat_lit 35813126260533411802653911170736628244605050985099304580766332486494371486067284060165403507000644184555317578097019289303697802274348728320 

noncomputable def Ns96p1558 := BSN.log_dyadic_bound 197137000804 721425000804 7 6 Ns96p1555 33554432 9680000 Ns96p1556 Ns96p1557 18816260 918562001608 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 197137000804) (BSN.artanhQ 721425000804) 0 6 Ns96p1556 Ns96p1555 Ns96p1557 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns96p1559 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 338851 4000) qz767 338851 4000 0 1 23114339521907393 2251799813685248 6250000847 60500000000000000 7832317061337842025443 9007199254740992000 2117819037006797 242000000000000000000 (Enclosure.Real.IsNear.const Bool.false 338851 4000) (BSN.isNear_log_sfrac 459281000804 16000000 23114339521907393 2251799813685248 6250000847 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 459281000804) qz350)) Bool.false Ns96p1554 Ns96p86 1000000135520000 9680000000000000000000 23114339521907393 2251799813685248 6250000847 60500000000000000 (BSN.log_rat_reduce_isNear 459281000804 16000000 14 918562001608 524288000000 18816260 33554432 24973259072661432 36028797018963968 9680000 1000000000000000 rfl rfl rfl rfl (Ns96p1558 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p1560 := BSN.arctan_dyadic_bound_f 1000 677702 1 0 4194304 1210000 0 1 1 0 1 1 6189 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 677702) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 677702) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz551 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 677702)))

noncomputable def Ns96p1561 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz551 884279719003555 562949953421312 1 2000000000000000 6189 4194304 1 1210000 3705453865273762250752 883449045484963 562949953421312 200000000121 242000000000000000 qz17 (Ns96p1560 rfl) rfl rfl 

noncomputable def Ns96p1562 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 338851 4000) qz767) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz551)) 7832317061337842025443 9007199254740992000 2117819037006797 242000000000000000000 883449045484963 2251799813685248 200000000121 968000000000000000 Ns96p1553 7828783265155902173443 9007199254740992000 2167819037037047 242000000000000000000 (Ns96p1559 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz551) 1 4 0 1 883449045484963 562949953421312 200000000121 242000000000000000 883449045484963 2251799813685248 200000000121 968000000000000000 qz353 Ns96p1561 rfl) 

noncomputable def Ns96p1563 := @Ns96p1548 Ns96p1542 Ns96p1543 2361173682656327439 123904000000000000000000 (@Ns96p1550 2361173682656327439 123904000000000000000000 (Ns96p1552 (Ns96p1562 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 338851 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz550 (Real.log Real.pi) 338851 2000 0 1 38410761 33554432 1 16777216 13015524775611 67108864000 338851 33554432000 (Enclosure.Real.IsNear.const Bool.false 338851 2000) RS097to114.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns96p1544 Ns96p1545) 

noncomputable def Ns96p1564 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz202) Bool.false Ns96p1542 Ns96p1543 2361173682656327439 123904000000000000000000 2121466879 4194304 161 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz202) (@HAdd.hAdd Real Real Real qz354 qz547 (Enclosure.sfrac Bool.true Ns96p1544 Ns96p1545)) Bool.false Ns96p1542 Ns96p1543 2361173682656327439 123904000000000000000000 Ns96p1546 (Ns96p1563 rfl rfl)) 

noncomputable def Ns96p1565 := nat_lit 140239696661069387682570693453016650977949336820999530806627967187121134254885437440000 

noncomputable def Ns96p1566 := nat_lit 282273094216790034879262875580447534208807651823794083991365295670088538521600000000 

noncomputable def Ns96p1567 := nat_lit 366837430055021212445499676292675266077338764999665009309944370249470446367093555200000 

noncomputable def Ns96p1568 := BSN.sin_dyadic_bound_f 26998130080 17179869184 3 2 8388608 2422364 Ns96p1565 Ns96p99 Ns96p1566 Ns96p1567 Ns96p102 Ns96p1566 8388605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26998130080) qz355 0 2 Ns96p1565 Ns96p99 Ns96p1566 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26998130080) qz356 0 2 Ns96p1567 Ns96p102 Ns96p1566 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1569 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz202) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2121466879) qz434) Bool.false 2121466879 4194304 161 8388608 Bool.true 8388605 8388608 1 1210000 (Ns96p1564 rfl) (Enclosure.sfrac_false_div 2121466879 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2121466879) qz434) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949912254467812798496768) qz678) 226375608064910080 72057594037927936 Bool.false 8388605 8388608 80 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q1 2121466879 4194304 226375608064910080 72057594037927936 80 949912254467812798496768 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388605 8388608 949912254467812798496768 604462909807314587353088 26998130080 17179869184 2422364 2420000 (Ns96p1568 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p1570 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz202) Bool.false Ns96p1542 Ns96p1543 2361173682656327439 123904000000000000000000 33943470071 67108864 1280 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz202) (@HAdd.hAdd Real Real Real qz354 qz547 (Enclosure.sfrac Bool.true Ns96p1544 Ns96p1545)) Bool.false Ns96p1542 Ns96p1543 2361173682656327439 123904000000000000000000 Ns96p1546 (Ns96p1563 rfl rfl)) 

noncomputable def Ns96p1571 := Ns96p1541 27391 BSN.abs_quadSignPos (BSN.cos_quad_nat0 172 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 49257341 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 85 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 914843 67108864) qz205 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz202) qz202 1) Bool.true 8388605 8388608 12699913 634388480000 67108840 67108864 1344 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz202) qz202 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz202)) Bool.true 8388605 8388608 12699913 634388480000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz202) qz202) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz202)) Bool.true 8388605 8388608 203198608 10150215680000 8388605 8388608 12699913 634388480000 (Ns96p1569 rfl rfl) rfl)) rfl) (Ns96p1570 rfl) RS097to114.d7 

noncomputable def Ns96p1572 := nat_lit 214791480696914999909234747216441119604735869112458687426242543616 

noncomputable def Ns96p1573 := nat_lit 39720600208748326024029393032435390392726511130456358006030336 

noncomputable def Ns96p1574 := nat_lit 644295000890327503075656182863258488033422154315115149562715570176 

noncomputable def Ns96p1575 := BSN.cos_dyadic_bound_f 50104528 67108864 3 2 67108864 33554432 Ns96p1572 Ns96p108 Ns96p1573 Ns96p1574 Ns96p111 Ns96p1573 49257341 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 50104528) qz359 0 2 Ns96p1572 Ns96p108 Ns96p1573 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 50104528) (BSN.cosOddQ 67108864) 0 2 Ns96p1574 Ns96p111 Ns96p1573 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1576 := BSN.sin_dyadic_bound_f 914872 67108864 1 0 67108864 33554432 0 1 1 0 1 1 914843 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 914872) qz360 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 914872) (BSN.sinOddQ 67108864) 0 0 rfl) rfl rfl 

noncomputable def Ns96p1577 := nat_lit 828634978547678845308402894165311932791930243724929359963765960198356567616280237227103203098624000000 

noncomputable def Ns96p1578 := nat_lit 1018947378387341536347365888126442758995905435106552732795255748182797840115760828416000000000000 

noncomputable def Ns96p1579 := nat_lit 5017179035358536201368972446823114301982820602124454052819274610608022266653493873696540010060185600000 

noncomputable def Ns96p1580 := BSN.cos_dyadic_bound_f 100156540 67108864 4 3 67108864 33554432 Ns96p1577 Ns96p236 Ns96p1578 Ns96p1579 Ns96p239 Ns96p1578 5252439 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 100156540) qz359 0 3 Ns96p1577 Ns96p236 Ns96p1578 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 100156540) (BSN.cosOddQ 67108864) 0 3 Ns96p1579 Ns96p239 Ns96p1578 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1581 := nat_lit 148562694864214568517518068321 

noncomputable def Ns96p1582 := BSN.sin_dyadic_bound_f 19632583 67108864 2 1 67108864 33554432 Ns96p1581 Ns96p127 Ns96p1581 Ns96p1581 Ns96p128 Ns96p1581 19353738 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 19632583) qz360 0 1 Ns96p1581 Ns96p127 Ns96p1581 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 19632583) (BSN.sinOddQ 67108864) 0 1 Ns96p1581 Ns96p128 Ns96p1581 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1583 := Ns96p1539 46598 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 22 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 5252439 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 25 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 19353738 67108864) qz205 rfl rfl (Ns96p1571 RS097to114.d9 RS097to114.d11 RS097to114.d13 RS097to114.d17 (Ns96p1575 rfl rfl) (Ns96p1576 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns96p1570 rfl) RS097to114.d19 RS097to114.d21 RS097to114.d23 RS097to114.d25 RS097to114.d17 (Ns96p1580 rfl rfl) (Ns96p1582 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns96p1584 := nat_lit 299530389289397869010168111154838677600750808448880885759235612321 

noncomputable def Ns96p1585 := nat_lit 77232506536097388427486037368970812051920775032762531620871841 

noncomputable def Ns96p1586 := nat_lit 898436702855121412253649361389778091178148583796577132214465093281 

noncomputable def Ns96p1587 := BSN.cos_dyadic_bound_f 54447133 67108864 3 2 67108864 33554432 Ns96p1584 Ns96p108 Ns96p1585 Ns96p1586 Ns96p111 Ns96p1585 46206988 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 54447133) qz359 0 2 Ns96p1584 Ns96p108 Ns96p1585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 54447133) (BSN.cosOddQ 67108864) 0 2 Ns96p1586 Ns96p111 Ns96p1585 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1588 := nat_lit 2661232177504293234163690635912978607557178935175842928013276983905 

noncomputable def Ns96p1589 := nat_lit 1879961909720171832028154045365894427339066149656489785893958241 

noncomputable def Ns96p1590 := nat_lit 6966850050371697239843525130365303952624538723123001923238563787361 

noncomputable def Ns96p1591 := BSN.sin_dyadic_bound_f 81146283 67108864 3 2 67108864 33554432 Ns96p1588 Ns96p221 Ns96p1589 Ns96p1590 Ns96p224 Ns96p1589 62768533 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 81146283) qz360 0 2 Ns96p1588 Ns96p221 Ns96p1589 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 81146283) (BSN.sinOddQ 67108864) 0 2 Ns96p1590 Ns96p224 Ns96p1589 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1592 := Ns96p1537 62810 BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 46206988 67108864) BSN.abs_quadSignNeg qz486 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 62768533 67108864) qz205 rfl rfl (Ns96p1583 rfl rfl) (Ns96p1570 rfl) RS097to114.d27 RS097to114.d29 RS097to114.d31 RS097to114.d33 RS097to114.d17 (Ns96p1587 rfl rfl) (Ns96p1591 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns96p1593 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz202) qz202 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz202) qz202 7) 48948641 67108864 62810 67108864 48948641 67108864 62810 67108864 6569775383707648 48948641 33554432 31405 16777216 (Ns96p1592 rfl) 

noncomputable def Ns96p1594 := @Enclosure.Real.IsNear.mulLit_tf qz766 (Zeta.RiemannSiegel.correction qz204) 3095513 8388608 1 8388608 1876488471527 4398046511104 94203827771243 1330409069608960000 5808694457961958351 36893488147419103232 

noncomputable abbrev qz769 := (@HPow.hPow Real Real Real qz7 qz203 qz9)

noncomputable def Ns96p1595 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz769 1 1 0 1 3095513 8388608 1 8388608 3095513 8388608 1 8388608 

noncomputable def Ns96p1596 := @Enclosure.Real.IsNear.sqrt_image qz203 452396242739 8388608000 338851 8388608000 30801671 30801695 4194304 (@Enclosure.Real.IsNear.of_eq qz203 (@HMul.hMul Real Real Real qz5 qz202 qz3) Bool.false 452396242739 8388608000 338851 8388608000 (BSN.t_div_two_pi_mk qz202 338851 1000 qz205) (@Enclosure.Real.IsNear.mulLit_ff qz202 qz3 338851 1000 0 1 1335089 8388608 1 8388608 452396242739 8388608000 338851 8388608000 (Enclosure.Real.IsNear.const Bool.false 338851 1000) RS097to114.d36 rfl)) 

noncomputable abbrev qz926 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 338851 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz770 := qz926

noncomputable abbrev qz552 := qz770

noncomputable abbrev qz207 := qz552

noncomputable def Ns96p1597 := @Enclosure.Real.IsNear.sqrt_image qz207 30801683 4194304 3 1048576 11366247 11366252 4194304 (@Enclosure.Real.IsNear.recentre' qz207 Bool.false 61603366 8388608 24 8388608 30801683 4194304 3 1048576 (Ns96p1596 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns96p1598 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz207) 22732499 8388608 5 8388608 1547756 1547757 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz207) Bool.false 22732499 8388608 5 8388608 22732499 8388608 5 8388608 (Ns96p1597 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns96p1599 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz207)) Bool.false 3095513 8388608 1 8388608 3095513 8388608 1 8388608 (Ns96p1598 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz208 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz545))

noncomputable abbrev qz771 := (@HMul.hMul Real Real Real qz863 qz925 qz925)

noncomputable abbrev qz553 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz771 qz765) qz641)

noncomputable abbrev qz209 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz553))

noncomputable def Ns96p1600 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz204) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz208) qz209) Bool.false 1876488471527 

noncomputable def Ns96p1601 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz208) qz209 1888391 1048576 129 

noncomputable abbrev qz772 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz208))

noncomputable def Ns96p1602 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz208) (@Neg.neg Real Real.instNeg qz772) Bool.true 1888391 1048576 129 2097152 (BSN.inv_eq_neg_inv_neg qz208) 

noncomputable def Ns96p1603 := @Enclosure.Real.IsNear.recentre' qz772 Bool.false 15107128 8388608 516 8388608 1888391 1048576 

noncomputable def Ns96p1604 := @Enclosure.Real.IsNear.recentre' qz208 Bool.true 4657983 8388608 24038576 1268776960000 4657983 8388608 1502411 79298560000 

noncomputable abbrev qz210 := (@HMul.hMul Real Real Real qz339 qz337 qz545)

noncomputable def Ns96p1605 := @Enclosure.Real.IsNear.cos_image qz210 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9057557) qz434) Bool.false 9057557 4194304 19 1048576 Bool.true 4657983 8388608 1 

noncomputable def Ns96p1606 := nat_lit 80958226230227852155699541 

noncomputable def Ns96p1607 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz204 884279719003555 140737488355328 1 500000000000000 1441555 4194304 3 1048576 1274737850328169728025 590295810358705651712 Ns96p1606 

noncomputable def Ns96p1608 := @Enclosure.Real.IsNear.subLit_ff_p qz207 qz1 30801683 4194304 3 1048576 7 1 0 1 1441555 1441555 4194304 3 

noncomputable def Ns96p1609 := @Ns96p1608 1048576 (@Enclosure.Real.IsNear.recentre' qz207 Bool.false 61603366 8388608 24 8388608 30801683 4194304 3 1048576 (Ns96p1596 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns96p1610 := @Enclosure.Real.IsNear.recentre' qz210 Bool.false 1274737850328169728025 590295810358705651712 Ns96p1606 Ns96p487 9057557 4194304 19 1048576 (@Ns96p1607 Ns96p487 RS097to114.d35 (Ns96p1609 rfl rfl) rfl) 

noncomputable def Ns96p1611 := nat_lit 10462524797172033322061744560730392312336 

noncomputable def Ns96p1612 := BSN.sin_dyadic_bound_f 10113678062 17179869184 2 1 8388608 2422364 Ns96p1611 Ns96p1511 Ns96p1611 Ns96p1611 Ns96p1512 Ns96p1611 4657983 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 10113678062) qz355 0 1 Ns96p1611 Ns96p1511 Ns96p1611 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 10113678062) qz356 0 1 Ns96p1611 Ns96p1512 Ns96p1611 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1613 := @Ns96p1605 1210000 (Ns96p1610 rfl) (Enclosure.sfrac_false_div 9057557 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9057557) qz434) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 355843412153700276240384) qz678) 226375608064910080 72057594037927936 Bool.false 4657983 8388608 0 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q1 9057557 4194304 226375608064910080 72057594037927936 0 355843412153700276240384 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 4657983 8388608 355843412153700276240384 604462909807314587353088 10113678062 17179869184 2422364 2420000 (Ns96p1612 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p1614 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz208) 4657983 8388608 1502411 79298560000 7553306 7553822 4194304 (@Enclosure.Real.IsNear.neg qz208 Bool.true 4657983 8388608 1502411 79298560000 (Ns96p1604 (Ns96p1613 rfl rfl) rfl)) 

noncomputable def Ns96p1615 := Ns96p1602 (@Enclosure.Real.IsNear.neg qz772 Bool.false 1888391 1048576 129 2097152 (@Ns96p1603 129 2097152 (Ns96p1614 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p1616 := @Enclosure.Real.IsNear.recentre' qz209 Bool.true 993697 4194304 

noncomputable abbrev qz211 := (@HMul.hMul Real Real Real qz339 qz337 qz553)

noncomputable def Ns96p1617 := @Enclosure.Real.IsNear.cos_image qz211 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7591633)) qz434) Bool.true 7591633 4194304 

noncomputable def Ns96p1618 := nat_lit 4481309176003921529431834405 

noncomputable def Ns96p1619 := nat_lit 286487927612334899567977933245517 

noncomputable def Ns96p1620 := @Enclosure.Real.IsNear.recentre' qz211 Bool.true Ns96p1618 Ns96p500 Ns96p1619 

noncomputable abbrev qz212 := qz553

noncomputable def Ns96p1621 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz212 884279719003555 140737488355328 1 500000000000000 5067750712471 

noncomputable abbrev qz554 := (@HSub.hSub Real Real Real qz635 qz771 qz765)

noncomputable abbrev qz213 := qz554

noncomputable def Ns96p1622 := @Enclosure.Real.IsNear.subLit_tf qz213 qz26 3968239084695 17592186044416 10616139 2199023255552 1 16 

noncomputable abbrev qz555 := qz771

noncomputable abbrev qz214 := qz555

noncomputable def Ns96p1623 := @Enclosure.Real.IsNear.subLit_ff_n qz214 qz204 2078080818025 17592186044416 4324683 2199023255552 1441555 4194304 3 1048576 

noncomputable def Ns96p1624 := @Enclosure.Real.IsNear.mulLit_ff qz204 qz204 1441555 4194304 3 1048576 1441555 4194304 3 1048576 2078080818025 17592186044416 

noncomputable def Ns96p1625 := nat_lit 6390191758324160848051502732914379644510806760729407145844211090380858359948885608162241 

noncomputable def Ns96p1626 := nat_lit 36645652545041406150439701736376413965171770475676592666005890469399922227655271361 

noncomputable def Ns96p1627 := nat_lit 38602919979794915801684483081751524465284339526218158634997005099056050381661027036095425 

noncomputable def Ns96p1628 := BSN.cos_dyadic_bound_t 7591633 4194304 4 3 4194304 1210000 Ns96p1625 Ns96p1217 Ns96p1626 Ns96p1627 Ns96p1220 Ns96p1626 993697 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 7591633) (BSN.cosEvenQ 4194304) 0 3 Ns96p1625 Ns96p1217 Ns96p1626 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 7591633) (BSN.cosOddQ 4194304) 0 3 Ns96p1627 Ns96p1220 Ns96p1626 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1629 := @Ns96p1616 316938608 10150215680000 993697 4194304 19808663 634388480000 (@Ns96p1617 255 8388608 Bool.true 993697 4194304 1 1210000 (@Ns96p1620 Ns96p1107 7591633 4194304 255 8388608 (@Ns96p1621 17592186044416 10616139 2199023255552 Ns96p1618 Ns96p500 Ns96p1619 Ns96p1107 RS097to114.d35 (@Ns96p1622 0 1 81084011399536 5067750712471 17592186044416 10616139 2199023255552 (@Ns96p1623 16644001065892577280 3968239084695 17592186044416 10616139 2199023255552 (@Ns96p1624 4324683 2199023255552 (Ns96p1609 rfl rfl) (Ns96p1609 rfl rfl) rfl) (Ns96p1609 rfl rfl) rfl rfl) qz369 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7591633 4194304) (BSN.cos_neg_of_bound 7591633 4194304 Bool.true 993697 4194304 1 1210000 (Ns96p1628 rfl rfl)) rfl rfl) 

noncomputable def Ns96p1630 := @Ns96p1594 146088452741054210701 Ns96p180 (Ns96p1595 qz28 (@Enclosure.Real.IsNear.of_eq qz769 (@Inv.inv Real Real.instInv (Real.sqrt qz207)) Bool.false 3095513 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz203 (BSN.t_div_two_pi_nonneg qz202 338851 1000 qz205)) Ns96p1599) rfl) (@Ns96p1600 4398046511104 94203827771243 1330409069608960000 (BSN.correction_mk qz204 (BSN.cos_two_pi_p_ne_zero_mk qz202 338851 1000 7 qz205 rfl rfl (@BSN.floor_sqrt_eq_dec qz202 338851 1000 7 qz205 rfl rfl rfl))) (@Ns96p1601 2097152 993697 4194304 19808663 634388480000 1876488471527 4398046511104 94203827771243 1330409069608960000 Ns96p1615 (Ns96p1629 rfl) rfl)) 

noncomputable def Ns96p1631 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz202) (hardyZApproximantRS₀ qz202) Bool.true 48010905485371094065 36893488147419103232 10591462660508401410701 Ns96p180 (@Eq.refl Real (hardyZApproximantRS₀ qz202)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz202) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz202) qz202 7) (@HMul.hMul Real Real Real qz5 qz766 (Zeta.RiemannSiegel.correction qz204))) Bool.true 48010905485371094065 36893488147419103232 10591462660508401410701 Ns96p180 (BSN.hardyZApproximantRS₀_eq qz202 7 (@BSN.floor_sqrt_eq_dec qz202 338851 1000 7 qz205 rfl rfl rfl)) (@Ns96p1535 48010905485371094065 36893488147419103232 10591462660508401410701 Ns96p180 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz202) qz202 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz202) qz202 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz202) qz202 7)) Bool.true 48948641 33554432 31405 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz202) qz202 7) (Ns96p1593 (Ns96p1592 rfl) rfl rfl)) (Ns96p1630 rfl) rfl rfl)) 

theorem RS097to114.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz202) Bool.true 48010905485371094065 36893488147419103232 10591462660508401410701 Ns96p180 := Ns96p1631 

noncomputable def Ns96p1632 := nat_lit 3781709526217491099850637312 

noncomputable abbrev qz927 := (Enclosure.sfrac Bool.false 340425 1000)

noncomputable abbrev qz773 := qz927

noncomputable abbrev qz556 := qz773

noncomputable abbrev qz215 := qz556

noncomputable abbrev qz928 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 340425 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz774 := qz928

noncomputable abbrev qz557 := qz774

noncomputable abbrev qz216 := qz557

noncomputable abbrev qz929 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 340425 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz775 := qz929

noncomputable abbrev qz558 := qz775

noncomputable abbrev qz217 := qz558

noncomputable abbrev qz776 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz216 qz9))

noncomputable def Ns96p1633 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz215) qz215 7) (@HMul.hMul Real Real Real qz5 qz776 (Zeta.RiemannSiegel.correction qz217)) 20463619 33554432 63103 33554432 22703778329440642965 147573952589676412928 6411241832137440183 279007004114856968192000 Ns96p1632 

noncomputable def Ns96p1634 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz215) qz215 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 340425 1000 64 97 67108864 33554432 1125899906842624 Bool.false 34154200635 1286 

noncomputable def Ns96p1635 := Ns96p1634 120242927 57 27397080 8 130587807 57 25364760 8 Bool.false 19269450 46816 Bool.true 32978936 Bool.true 75960927 3537118876014220 1 Bool.false 59167307 Bool.false Bool.false 60748538 Bool.true Bool.false 20463619 

noncomputable def Ns96p1636 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz215) qz215 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 340425 1000 23 24 67108864 33554432 1125899906842624 Bool.false 34154200635 1286 

noncomputable def Ns96p1637 := Ns96p1636 93032624 56 33554424 8 108007536 56 30011992 8 Bool.true 15866021 27520 Bool.false 59039397 Bool.true 84320238 3537118876014220 1 Bool.false 51712957 Bool.false Bool.false 20748476 Bool.false Bool.false 19269450 

noncomputable def Ns96p1638 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz215) qz215 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 340425 1000 173 85 67108864 33554432 1125899906842624 Bool.false 34154200635 1286 

noncomputable def Ns96p1639 := Ns96p1638 46516304 56 47453136 16 73726608 56 38745320 8 Bool.false 67108840 1352 Bool.false 82204073 Bool.false 95599755 3537118876014220 1 Bool.false 63134958 Bool.true Bool.false 66392454 Bool.true Bool.true 15866021 

noncomputable def Ns96p1640 := nat_lit 1168975569664448485724783010557089467007225057 

noncomputable def Ns96p1641 := nat_lit 2296895288529890718505673729687500535889920 

noncomputable def Ns96p1642 := nat_lit 2194577091662802861079687500000000 

noncomputable def Ns96p1643 := nat_lit 4482537951232488691725446953125000000 

noncomputable abbrev qz777 := (@Eq.refl Real qz927)

noncomputable abbrev qz559 := qz777

noncomputable abbrev qz218 := qz559

noncomputable def Ns96p1644 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz215 340425 1000 463557722500 16000000 680850 4000 2000 Ns96p1642 Ns96p1643 qz218 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns96p1645 := nat_lit 821935947420315341525238054297953531489455118203125000000 

noncomputable abbrev qz778 := (Real.log (Enclosure.sfrac Bool.false 463557722500 16000000))

noncomputable abbrev qz219 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 340425 4000) qz778) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 680850))))))

noncomputable abbrev qz779 := (Enclosure.sfrac Bool.false 340425 2000)

noncomputable abbrev qz560 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz219 qz779) (@HMul.hMul Real Real Real qz5 qz779 (Real.log Real.pi)))

noncomputable def Ns96p1646 := @Enclosure.Real.IsNear.addLit_ft_p qz560 (Enclosure.sfrac Bool.true Ns96p1642 Ns96p1643) 183364144830953831953 360287970189639680 8625537011502303 450560000000000000000 Ns96p1642 Ns96p1643 0 1 Ns96p1645 

noncomputable def Ns96p1647 := nat_lit 492214378317471347952509255680 

noncomputable abbrev qz561 := (@HSub.hSub Real Real Real qz12 qz219 qz779)

noncomputable abbrev qz562 := (@HMul.hMul Real Real Real qz5 qz779 (Real.log Real.pi))

noncomputable def Ns96p1648 := @Enclosure.Real.IsNear.subLit_ff_p qz561 qz562 253565295698706447889 360287970189639680 7918751048619 880000000000000000 523039332537 2684354560 13617 1342177280 Ns96p1647 183364144830953831953 360287970189639680 

noncomputable abbrev qz563 := qz779

noncomputable def Ns96p1649 := @Enclosure.Real.IsNear.subLit_ff_p qz219 qz563 314890811824610491921 360287970189639680 7918751048619 880000000000000000 340425 2000 0 1 507130591397412895778000 253565295698706447889 360287970189639680 7918751048619 880000000000000000 

noncomputable def Ns96p1650 := nat_lit 709071071397854393526736501140881408 

noncomputable def Ns96p1651 := nat_lit 12420621675420948948320256 

noncomputable def Ns96p1652 := nat_lit 2883139743979605621807985086609782049148671235568886585414693168700105631995169545058592305847936947203775346279144287109375000000000000000000000000 

noncomputable def Ns96p1653 := nat_lit 77651558856672391181953802164496676314624108938442727519757441378340661070347863616741105887578772513491630554199218750000000000000000000000000000 

noncomputable def Ns96p1654 := nat_lit 46333292939114765773948183352381538645291230102619617846873669626722117882924470860175194976707982718944549560546875000000000000000000000000 

noncomputable def Ns96p1655 := BSN.log_dyadic_bound 201413722500 725701722500 7 6 Ns96p1652 33554432 9680000 Ns96p1653 Ns96p1654 19127265 927115445000 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 201413722500) (BSN.artanhQ 725701722500) 0 6 Ns96p1653 Ns96p1652 Ns96p1654 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns96p1656 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 340425 4000) qz778 340425 4000 0 1 23135210714155713 2251799813685248 6250000847 60500000000000000 315032164294658343921 360287970189639680 85106261533599 9680000000000000000 (Enclosure.Real.IsNear.const Bool.false 340425 4000) (BSN.isNear_log_sfrac 463557722500 16000000 23135210714155713 2251799813685248 6250000847 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 463557722500) qz350)) Bool.false Ns96p1651 Ns96p86 1000000135520000 9680000000000000000000 23135210714155713 2251799813685248 6250000847 60500000000000000 (BSN.log_rat_reduce_isNear 463557722500 16000000 14 927115445000 524288000000 19127265 33554432 24973259072661432 36028797018963968 9680000 1000000000000000 rfl rfl rfl rfl (Ns96p1655 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p1657 := BSN.arctan_dyadic_bound_f 1000 680850 1 0 4194304 1210000 0 1 1 0 1 1 6160 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 680850) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 680850) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz564 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 680850)))

noncomputable def Ns96p1658 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz564 884279719003555 562949953421312 1 2000000000000000 6160 4194304 1 1210000 3705470190822411468800 883452937799075 562949953421312 200000000121 242000000000000000 qz17 (Ns96p1657 rfl) rfl rfl 

noncomputable def Ns96p1659 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 340425 4000) qz778) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz564)) 315032164294658343921 360287970189639680 85106261533599 9680000000000000000 883452937799075 2251799813685248 200000000121 968000000000000000 Ns96p1650 314890811824610491921 360287970189639680 7918751048619 880000000000000000 (Ns96p1656 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz564) 1 4 0 1 883452937799075 562949953421312 200000000121 242000000000000000 883452937799075 2251799813685248 200000000121 968000000000000000 qz353 Ns96p1658 rfl) 

noncomputable def Ns96p1660 := @Ns96p1646 Ns96p1640 Ns96p1641 8625537011502303 450560000000000000000 (@Ns96p1648 8625537011502303 450560000000000000000 (Ns96p1649 (Ns96p1659 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 340425 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz563 (Real.log Real.pi) 340425 2000 0 1 38410761 33554432 1 16777216 523039332537 2684354560 13617 1342177280 (Enclosure.Real.IsNear.const Bool.false 340425 2000) RS097to114.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns96p1642 Ns96p1643) 

noncomputable def Ns96p1661 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz215) Bool.false Ns96p1640 Ns96p1641 8625537011502303 450560000000000000000 4269275079 8388608 81 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz215) (@HAdd.hAdd Real Real Real qz354 qz560 (Enclosure.sfrac Bool.true Ns96p1642 Ns96p1643)) Bool.false Ns96p1640 Ns96p1641 8625537011502303 450560000000000000000 Ns96p1644 (Ns96p1660 rfl rfl)) 

noncomputable def Ns96p1662 := nat_lit 1898056465380779038343168 

noncomputable def Ns96p1663 := nat_lit 139717331568118761113236633357992511659693424603839141281646293481964635956778785440000 

noncomputable def Ns96p1664 := nat_lit 280178380491506051490659880269183223638906153658720167815720340432112291024100000000 

noncomputable def Ns96p1665 := nat_lit 365472722443324793117968209464782662460924549713655061180229126187303007606095895200000 

noncomputable def Ns96p1666 := BSN.sin_dyadic_bound_f 26973004670 17179869184 3 2 8388608 2422364 Ns96p1663 Ns96p99 Ns96p1664 Ns96p1665 Ns96p102 Ns96p1664 8388605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26973004670) qz355 0 2 Ns96p1663 Ns96p99 Ns96p1664 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26973004670) qz356 0 2 Ns96p1665 Ns96p102 Ns96p1664 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1667 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz215) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4269275079) qz357) Bool.false 4269275079 8388608 81 4194304 Bool.false 8388605 8388608 1 1210000 (Ns96p1661 rfl) (Enclosure.sfrac_false_div 4269275079 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4269275079) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns96p1662) qz358) 226375608064910080 72057594037927936 Bool.false 8388605 8388608 80 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q3 4269275079 8388608 226375608064910080 72057594037927936 80 Ns96p1662 Ns96p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388605 8388608 Ns96p1662 Ns96p86 26973004670 17179869184 2422364 2420000 (Ns96p1666 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p1668 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz215) Bool.false Ns96p1640 Ns96p1641 8625537011502303 450560000000000000000 34154200635 67108864 1286 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz215) (@HAdd.hAdd Real Real Real qz354 qz560 (Enclosure.sfrac Bool.true Ns96p1642 Ns96p1643)) Bool.false Ns96p1640 Ns96p1641 8625537011502303 450560000000000000000 Ns96p1644 (Ns96p1660 rfl rfl)) 

noncomputable def Ns96p1669 := Ns96p1639 27520 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 173 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 63134958 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 85 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66392454 67108864) qz218 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz215) qz215 1) Bool.false 8388605 8388608 6387769 317194240000 67108840 67108864 1352 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz215) qz215 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz215)) Bool.false 8388605 8388608 6387769 317194240000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz215) qz215) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz215)) Bool.false 8388605 8388608 102204304 5075107840000 8388605 8388608 6387769 317194240000 (Ns96p1667 rfl rfl) rfl)) rfl) (Ns96p1668 rfl) RS097to114.d7 

noncomputable def Ns96p1670 := nat_lit 2802837363354604001141698233228115306135021540858256805117117762625 

noncomputable def Ns96p1671 := nat_lit 2085195072429877830864221517713292705269478223110040239562198081 

noncomputable def Ns96p1672 := nat_lit 7337388492954314486502096156949718565973667737505637281585541057601 

noncomputable def Ns96p1673 := BSN.sin_dyadic_bound_f 82204073 67108864 3 2 67108864 33554432 Ns96p1670 Ns96p221 Ns96p1671 Ns96p1672 Ns96p224 Ns96p1671 63134958 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 82204073) qz360 0 2 Ns96p1670 Ns96p221 Ns96p1671 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 82204073) (BSN.sinOddQ 67108864) 0 2 Ns96p1672 Ns96p224 Ns96p1671 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1674 := nat_lit 1785486061290768990120109788605996142389230665671437101170019632824567092900131104282494269273483540625 

noncomputable def Ns96p1675 := nat_lit 582748751004894862444594676275360211983423265243616932900997845162927678858230713831640869140625 

noncomputable def Ns96p1676 := nat_lit 8919922515736096776617052006162359757904439946439062164940513365264535082421126846781831975259941140625 

noncomputable def Ns96p1677 := BSN.sin_dyadic_bound_f 95599755 67108864 4 3 67108864 33554432 Ns96p1674 Ns96p762 Ns96p1675 Ns96p1676 Ns96p765 Ns96p1675 66392454 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 95599755) qz360 0 3 Ns96p1674 Ns96p762 Ns96p1675 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 95599755) (BSN.sinOddQ 67108864) 0 3 Ns96p1676 Ns96p765 Ns96p1675 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1678 := nat_lit 745340997307751198152641817037338277104174607815842761324469450465 

noncomputable def Ns96p1679 := nat_lit 147616636418151040866476266810828339388574942015887229946984161 

noncomputable def Ns96p1680 := nat_lit 1951844566013718988714563797332477956056685327706800557477505824481 

noncomputable def Ns96p1681 := BSN.sin_dyadic_bound_f 59039397 67108864 3 2 67108864 33554432 Ns96p1678 Ns96p221 Ns96p1679 Ns96p1680 Ns96p224 Ns96p1679 51712957 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 59039397) qz360 0 2 Ns96p1678 Ns96p221 Ns96p1679 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 59039397) (BSN.sinOddQ 67108864) 0 2 Ns96p1680 Ns96p224 Ns96p1679 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1682 := nat_lit 415657924621827862057438667062483030053917215592435899553187512098551291753680833843427465155352334336 

noncomputable def Ns96p1683 := nat_lit 129176015498832875410004911049545248861266840858449128015373642009444930340690221659316506464256 

noncomputable def Ns96p1684 := nat_lit 2519167134248841018380960881980695822103191256069467934209214725285044411979653506316566527744441978880 

noncomputable def Ns96p1685 := BSN.cos_dyadic_bound_f 84320238 67108864 4 3 67108864 33554432 Ns96p1682 Ns96p236 Ns96p1683 Ns96p1684 Ns96p239 Ns96p1683 20748476 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 84320238) qz359 0 3 Ns96p1682 Ns96p236 Ns96p1683 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 84320238) (BSN.cosOddQ 67108864) 0 3 Ns96p1684 Ns96p239 Ns96p1683 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1686 := Ns96p1637 46816 BSN.abs_quadSignPos (BSN.cos_quad_nat3 23 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 51712957 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 24 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 20748476 67108864) qz218 rfl rfl (Ns96p1669 RS097to114.d9 RS097to114.d11 RS097to114.d13 RS097to114.d17 (Ns96p1673 rfl rfl) (Ns96p1677 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns96p1668 rfl) RS097to114.d19 RS097to114.d21 RS097to114.d23 RS097to114.d25 RS097to114.d17 (Ns96p1681 rfl rfl) (Ns96p1685 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns96p1687 := nat_lit 40307927301528002704766424713736561361024851809986771521409908736 

noncomputable def Ns96p1688 := nat_lit 1399242923107663477740762494792071385716190383533989514182656 

noncomputable def Ns96p1689 := nat_lit 120920983418737792787343792616220099940303123049193246585201360896 

noncomputable def Ns96p1690 := BSN.cos_dyadic_bound_f 32978936 67108864 3 2 67108864 33554432 Ns96p1687 Ns96p108 Ns96p1688 Ns96p1689 Ns96p111 Ns96p1688 59167307 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 32978936) qz359 0 2 Ns96p1687 Ns96p108 Ns96p1688 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 32978936) (BSN.cosOddQ 67108864) 0 2 Ns96p1689 Ns96p111 Ns96p1688 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1691 := nat_lit 2043139603216547929455697033824591731357343291628059715170237242625 

noncomputable def Ns96p1692 := nat_lit 1108465162946183759838695510965598011707140812446338359006158081 

noncomputable def Ns96p1693 := nat_lit 5349285255303331708201372438713319756774087535805719468102706617601 

noncomputable def Ns96p1694 := BSN.sin_dyadic_bound_f 75960927 67108864 3 2 67108864 33554432 Ns96p1691 Ns96p221 Ns96p1692 Ns96p1693 Ns96p224 Ns96p1692 60748538 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 75960927) qz360 0 2 Ns96p1691 Ns96p221 Ns96p1692 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 75960927) (BSN.sinOddQ 67108864) 0 2 Ns96p1693 Ns96p224 Ns96p1692 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1695 := Ns96p1635 63103 BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 59167307 67108864) BSN.abs_quadSignNeg qz486 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 60748538 67108864) qz218 rfl rfl (Ns96p1686 rfl rfl) (Ns96p1668 rfl) RS097to114.d27 RS097to114.d29 RS097to114.d31 RS097to114.d33 RS097to114.d17 (Ns96p1690 rfl rfl) (Ns96p1694 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns96p1696 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz215) qz215 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz215) qz215 7) 20463619 67108864 63103 67108864 20463619 67108864 63103 67108864 2746580448837632 20463619 33554432 63103 33554432 (Ns96p1695 rfl) 

noncomputable def Ns96p1697 := @Enclosure.Real.IsNear.mulLit_tf qz776 (Zeta.RiemannSiegel.correction qz217) 3091929 8388608 1 8388608 7342917101085 17592186044416 165524035265823 2660818139217920000 22703778329440642965 147573952589676412928 

noncomputable abbrev qz780 := (@HPow.hPow Real Real Real qz7 qz216 qz9)

noncomputable def Ns96p1698 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz780 1 1 0 1 3091929 8388608 1 8388608 3091929 8388608 1 8388608 

noncomputable def Ns96p1699 := @Enclosure.Real.IsNear.sqrt_image qz216 18179906913 335544320 13617 335544320 30873127 30873151 4194304 (@Enclosure.Real.IsNear.of_eq qz216 (@HMul.hMul Real Real Real qz5 qz215 qz3) Bool.false 18179906913 335544320 13617 335544320 (BSN.t_div_two_pi_mk qz215 340425 1000 qz218) (@Enclosure.Real.IsNear.mulLit_ff qz215 qz3 340425 1000 0 1 1335089 8388608 1 8388608 18179906913 335544320 13617 335544320 (Enclosure.Real.IsNear.const Bool.false 340425 1000) RS097to114.d36 rfl)) 

noncomputable abbrev qz930 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 340425 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz781 := qz930

noncomputable abbrev qz565 := qz781

noncomputable abbrev qz220 := qz565

noncomputable def Ns96p1700 := @Enclosure.Real.IsNear.sqrt_image qz220 30873139 4194304 3 1048576 11379423 11379428 4194304 (@Enclosure.Real.IsNear.recentre' qz220 Bool.false 61746278 8388608 24 8388608 30873139 4194304 3 1048576 (Ns96p1699 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns96p1701 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz220) 22758851 8388608 5 8388608 1545964 1545965 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz220) Bool.false 22758851 8388608 5 8388608 22758851 8388608 5 8388608 (Ns96p1700 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns96p1702 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz220)) Bool.false 3091929 8388608 1 8388608 3091929 8388608 1 8388608 (Ns96p1701 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz221 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz558))

noncomputable abbrev qz782 := (@HMul.hMul Real Real Real qz863 qz929 qz929)

noncomputable abbrev qz566 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz782 qz775) qz641)

noncomputable abbrev qz222 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz566))

noncomputable def Ns96p1703 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz217) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz221) qz222) Bool.false 7342917101085 

noncomputable def Ns96p1704 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz221) qz222 6543877 4194304 97 

noncomputable abbrev qz783 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz221))

noncomputable def Ns96p1705 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz221) (@Neg.neg Real Real.instNeg qz783) Bool.true 6543877 4194304 97 2097152 (BSN.inv_eq_neg_inv_neg qz221) 

noncomputable def Ns96p1706 := @Enclosure.Real.IsNear.recentre' qz783 Bool.false 13087754 8388608 388 8388608 6543877 4194304 

noncomputable def Ns96p1707 := @Enclosure.Real.IsNear.recentre' qz221 Bool.true 5376686 8388608 24038576 1268776960000 2688343 4194304 1502411 79298560000 

noncomputable abbrev qz223 := (@HMul.hMul Real Real Real qz339 qz337 qz558)

noncomputable def Ns96p1708 := @Enclosure.Real.IsNear.cos_image qz223 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 297079) (@Nat.cast Real Real.instNatCast 131072)) Bool.false 297079 131072 19 1048576 Bool.true 5376686 8388608 1 

noncomputable def Ns96p1709 := nat_lit 80958226230381302747251029 

noncomputable def Ns96p1710 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz217 884279719003555 140737488355328 1 500000000000000 1513011 4194304 3 1048576 1337924941929287754105 590295810358705651712 Ns96p1709 

noncomputable def Ns96p1711 := @Enclosure.Real.IsNear.subLit_ff_p qz220 qz1 30873139 4194304 3 1048576 7 1 0 1 1513011 1513011 4194304 3 

noncomputable def Ns96p1712 := @Ns96p1711 1048576 (@Enclosure.Real.IsNear.recentre' qz220 Bool.false 61746278 8388608 24 8388608 30873139 4194304 3 1048576 (Ns96p1699 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns96p1713 := @Enclosure.Real.IsNear.recentre' qz223 Bool.false 1337924941929287754105 590295810358705651712 Ns96p1709 Ns96p487 297079 131072 19 1048576 (@Ns96p1710 Ns96p487 RS097to114.d35 (Ns96p1712 rfl rfl) rfl) 

noncomputable def Ns96p1714 := nat_lit 5377167755958363532751415148682156269983548666983518031228468531995688705184062193920 

noncomputable def Ns96p1715 := nat_lit 416598287440991351843376700506885545082188346668901590273266841697924203466670336 

noncomputable def Ns96p1716 := nat_lit 14082383915997000028350721827128636225741065822871749955404594199387864255343121613056 

noncomputable def Ns96p1717 := BSN.sin_dyadic_bound_f 11952663278 17179869184 3 2 8388608 2422364 Ns96p1714 Ns96p99 Ns96p1715 Ns96p1716 Ns96p102 Ns96p1715 5376686 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 11952663278) qz355 0 2 Ns96p1714 Ns96p99 Ns96p1715 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 11952663278) qz356 0 2 Ns96p1716 Ns96p102 Ns96p1715 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1718 := @Ns96p1708 1210000 (Ns96p1713 rfl) (Enclosure.sfrac_false_div 297079 131072) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 297079) (@Nat.cast Real Real.instNatCast 131072)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13142092258103292592128) (@Nat.cast Real Real.instNatCast 18889465931478580854784)) 226375608064910080 72057594037927936 Bool.false 5376686 8388608 0 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q1 297079 131072 226375608064910080 72057594037927936 0 13142092258103292592128 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 5376686 8388608 13142092258103292592128 18889465931478580854784 11952663278 17179869184 2422364 2420000 (Ns96p1717 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p1719 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz221) 2688343 4194304 1502411 79298560000 6543683 6544071 4194304 (@Enclosure.Real.IsNear.neg qz221 Bool.true 2688343 4194304 1502411 79298560000 (Ns96p1707 (Ns96p1718 rfl rfl) rfl)) 

noncomputable def Ns96p1720 := Ns96p1705 (@Enclosure.Real.IsNear.neg qz783 Bool.false 6543877 4194304 97 2097152 (@Ns96p1706 97 2097152 (Ns96p1719 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p1721 := @Enclosure.Real.IsNear.recentre' qz222 Bool.true 1122105 4194304 

noncomputable abbrev qz224 := (@HMul.hMul Real Real Real qz339 qz337 qz566)

noncomputable def Ns96p1722 := @Enclosure.Real.IsNear.cos_image qz224 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 3862169)) qz706) Bool.true 3862169 2097152 

noncomputable def Ns96p1723 := nat_lit 4559644614571308388848201445 

noncomputable def Ns96p1724 := nat_lit 58454575725143194553769204735689 

noncomputable def Ns96p1725 := @Enclosure.Real.IsNear.recentre' qz224 Bool.true Ns96p1723 Ns96p500 Ns96p1724 

noncomputable abbrev qz225 := qz566

noncomputable def Ns96p1726 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz225 884279719003555 140737488355328 1 500000000000000 5156337430999 

noncomputable abbrev qz567 := (@HSub.hSub Real Real Real qz635 qz782 qz775)

noncomputable abbrev qz226 := qz567

noncomputable def Ns96p1727 := @Enclosure.Real.IsNear.subLit_tf qz226 qz26 4056825803223 17592186044416 10830507 2199023255552 1 16 

noncomputable abbrev qz568 := qz782

noncomputable abbrev qz227 := qz568

noncomputable def Ns96p1728 := @Enclosure.Real.IsNear.subLit_ff_n qz227 qz217 2289202286121 17592186044416 4539051 2199023255552 1513011 4194304 3 1048576 

noncomputable def Ns96p1729 := @Enclosure.Real.IsNear.mulLit_ff qz217 qz217 1513011 4194304 3 1048576 1513011 4194304 3 1048576 2289202286121 17592186044416 

noncomputable def Ns96p1730 := nat_lit 1672847686954046356353251529586566536953876540911442582486074133074986177216907611041 

noncomputable def Ns96p1731 := nat_lit 3466537250751077332112698720796095110148055492926080949987665366995300109908547993600 

noncomputable def Ns96p1732 := nat_lit 11014766207873469283194595247367938610010045972464114778986322840207233984531361 

noncomputable def Ns96p1733 := nat_lit 10102544244210457945774544767992361265650744250823958267565290667008249273374606658465 

noncomputable def Ns96p1734 := nat_lit 315454889818348037222255583592444655023473049856273366448877548396572310001677867417600 

noncomputable def Ns96p1735 := BSN.cos_dyadic_bound_t 3862169 2097152 4 3 4194304 1210000 Ns96p1730 Ns96p1731 Ns96p1732 Ns96p1733 Ns96p1734 Ns96p1732 1122105 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 3862169) (BSN.cosEvenQ 2097152) 0 3 Ns96p1730 Ns96p1731 Ns96p1732 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 3862169) (BSN.cosOddQ 2097152) 0 3 Ns96p1733 Ns96p1734 Ns96p1732 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1736 := @Ns96p1721 324198608 10150215680000 1122105 4194304 20262413 634388480000 (@Ns96p1722 261 8388608 Bool.true 1122105 4194304 1 1210000 (@Ns96p1725 Ns96p503 3862169 2097152 261 8388608 (@Ns96p1726 17592186044416 10830507 2199023255552 Ns96p1723 Ns96p500 Ns96p1724 Ns96p503 RS097to114.d35 (@Ns96p1727 0 1 82501398895984 5156337430999 17592186044416 10830507 2199023255552 (@Ns96p1728 17015560693761441792 4056825803223 17592186044416 10830507 2199023255552 (@Ns96p1729 4539051 2199023255552 (Ns96p1712 rfl rfl) (Ns96p1712 rfl rfl) rfl) (Ns96p1712 rfl rfl) rfl rfl) qz369 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 3862169 2097152) (BSN.cos_neg_of_bound 3862169 2097152 Bool.true 1122105 4194304 1 1210000 (Ns96p1735 rfl rfl)) rfl rfl) 

noncomputable def Ns96p1737 := @Ns96p1697 6411241832137440183 279007004114856968192000 (Ns96p1698 qz28 (@Enclosure.Real.IsNear.of_eq qz780 (@Inv.inv Real Real.instInv (Real.sqrt qz220)) Bool.false 3091929 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz216 (BSN.t_div_two_pi_nonneg qz215 340425 1000 qz218)) Ns96p1702) rfl) (@Ns96p1703 17592186044416 165524035265823 2660818139217920000 (BSN.correction_mk qz217 (BSN.cos_two_pi_p_ne_zero_mk qz215 340425 1000 7 qz218 rfl rfl (@BSN.floor_sqrt_eq_dec qz215 340425 1000 7 qz218 rfl rfl rfl))) (@Ns96p1704 2097152 1122105 4194304 20262413 634388480000 7342917101085 17592186044416 165524035265823 2660818139217920000 Ns96p1720 (Ns96p1736 rfl) rfl)) 

noncomputable def Ns96p1738 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz215) (hardyZApproximantRS₀ qz215) Bool.false 112703726476952168341 147573952589676412928 531116263829226208183 279007004114856968192000 (@Eq.refl Real (hardyZApproximantRS₀ qz215)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz215) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz215) qz215 7) (@HMul.hMul Real Real Real qz5 qz776 (Zeta.RiemannSiegel.correction qz217))) Bool.false 112703726476952168341 147573952589676412928 531116263829226208183 279007004114856968192000 (BSN.hardyZApproximantRS₀_eq qz215 7 (@BSN.floor_sqrt_eq_dec qz215 340425 1000 7 qz218 rfl rfl rfl)) (@Ns96p1633 112703726476952168341 147573952589676412928 531116263829226208183 279007004114856968192000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz215) qz215 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz215) qz215 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz215) qz215 7)) Bool.false 20463619 33554432 63103 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz215) qz215 7) (Ns96p1696 (Ns96p1695 rfl) rfl rfl)) (Ns96p1737 rfl) rfl rfl)) 

theorem RS097to114.d54 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz215) Bool.false 112703726476952168341 147573952589676412928 531116263829226208183 279007004114856968192000 := Ns96p1738 

noncomputable def Ns96p1739 := nat_lit 27479788352541572976345088 

noncomputable abbrev qz931 := (Enclosure.sfrac Bool.false 341998 1000)

noncomputable abbrev qz784 := qz931

noncomputable abbrev qz569 := qz784

noncomputable abbrev qz228 := qz569

noncomputable abbrev qz932 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 341998 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz785 := qz932

noncomputable abbrev qz570 := qz785

noncomputable abbrev qz229 := qz570

noncomputable abbrev qz933 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 341998 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz786 := qz933

noncomputable abbrev qz571 := qz786

noncomputable abbrev qz230 := qz571

noncomputable abbrev qz787 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz229 qz9))

noncomputable def Ns96p1740 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz228) qz228 7) (@HMul.hMul Real Real Real qz5 qz787 (Zeta.RiemannSiegel.correction qz230)) 11015089 33554432 15847 8388608 694940792932860399 4611686018427387904 11555978528448354123 558014008229713936384000 Ns96p1739 

noncomputable def Ns96p1741 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz228) qz228 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 341998 1000 64 97 67108864 33554432 1125899906842624 Bool.false 34365041434 1292 

noncomputable def Ns96p1742 := Ns96p1741 120242927 57 27397080 8 130587807 57 25364760 8 Bool.true 16010825 47026 Bool.true 11280261 Bool.true 70534748 3537118876014220 1 Bool.false 66163050 Bool.false Bool.false 58246804 Bool.true Bool.true 11015089 

noncomputable def Ns96p1743 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz228) qz228 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 341998 1000 24 24 67108864 33554432 1125899906842624 Bool.false 34365041434 1292 

noncomputable def Ns96p1744 := Ns96p1743 93032624 56 33554424 8 108007536 56 30011992 8 Bool.true 72307120 27641 Bool.false 18125521 Bool.true 43375293 3537118876014220 1 Bool.false 64675935 Bool.false Bool.false 53572475 Bool.false Bool.true 16010825 

noncomputable def Ns96p1745 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz228) qz228 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 341998 1000 175 86 67108864 33554432 1125899906842624 Bool.false 34365041434 1292 

noncomputable def Ns96p1746 := Ns96p1745 46516304 56 47453136 16 73726608 56 38745320 8 Bool.true 67108848 1352 Bool.false 9046011 Bool.false 85054243 3537118876014220 1 Bool.false 9018641 Bool.false Bool.false 20049206 Bool.true Bool.true 72307120 

noncomputable def Ns96p1747 := nat_lit 518923665722369504890847521219368271542471260089629619 

noncomputable def Ns96p1748 := nat_lit 1013366382090824977067150209610830646284558270464000 

noncomputable def Ns96p1749 := nat_lit 2245750063202022065809100784640000 

noncomputable def Ns96p1750 := nat_lit 4608256777332030547164095922247864320 

noncomputable abbrev qz788 := (@Eq.refl Real qz931)

noncomputable abbrev qz572 := qz788

noncomputable abbrev qz231 := qz572

noncomputable def Ns96p1751 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz228 341998 1000 467851528016 16000000 683996 4000 2000 Ns96p1749 Ns96p1750 qz231 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns96p1752 := nat_lit 10627556673994127460164557234572662201189811406635614597120 

noncomputable abbrev qz789 := (Real.log (Enclosure.sfrac Bool.false 467851528016 16000000))

noncomputable abbrev qz232 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 341998 4000) qz789) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 683996))))))

noncomputable abbrev qz790 := (Enclosure.sfrac Bool.false 341998 2000)

noncomputable abbrev qz573 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz232 qz790) (@HMul.hMul Real Real Real qz5 qz790 (Real.log Real.pi)))

noncomputable def Ns96p1753 := @Enclosure.Real.IsNear.addLit_ft_p qz573 (Enclosure.sfrac Bool.true Ns96p1749 Ns96p1750) 2306201086760219406791 4503599627370496000 108312035501934201 5632000000000000000000 Ns96p1749 Ns96p1750 0 1 Ns96p1752 

noncomputable def Ns96p1754 := nat_lit 77383267544021882390248947712000 

noncomputable abbrev qz574 := (@HSub.hSub Real Real Real qz12 qz232 qz790)

noncomputable abbrev qz575 := (@HMul.hMul Real Real Real qz5 qz790 (Real.log Real.pi))

noncomputable def Ns96p1755 := @Enclosure.Real.IsNear.subLit_ff_p qz574 qz575 3187770198696389603783 4503599627370496000 49715631584149 5500000000000000000 6568201720239 33554432000 170999 16777216000 Ns96p1754 2306201086760219406791 4503599627370496000 

noncomputable def Ns96p1756 := nat_lit 6375540397392779207566000 

noncomputable abbrev qz576 := qz790

noncomputable def Ns96p1757 := @Enclosure.Real.IsNear.subLit_ff_p qz232 qz576 3957881231377117049287 4503599627370496000 49715631584149 5500000000000000000 341998 2000 0 1 Ns96p1756 3187770198696389603783 4503599627370496000 49715631584149 5500000000000000000 

noncomputable def Ns96p1758 := nat_lit 8912356219403332102102285087120818176 

noncomputable def Ns96p1759 := nat_lit 12431768084498690925920256 

noncomputable def Ns96p1760 := nat_lit 3094640760268580853591117627399419991361919853598059156212430590408863776071117260618104249665618786652731821181163243173089772018195342931064258560 

noncomputable def Ns96p1761 := nat_lit 86050900065114119932958314220782040508665124169112116336581695763892795913262668187222158135208262577655533960886276465552239331402391904669663232 

noncomputable def Ns96p1762 := nat_lit 59679711818539650966402403981831044739476754792535543610498126763294552021504475758981026378435448829676972364067931000331462177283238789120 

noncomputable def Ns96p1763 := BSN.log_dyadic_bound 205707528016 729995528016 7 6 Ns96p1760 33554432 9680000 Ns96p1761 Ns96p1762 19436640 935703056032 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 205707528016) (BSN.artanhQ 729995528016) 0 6 Ns96p1761 Ns96p1760 Ns96p1762 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns96p1764 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 341998 4000) qz789 341998 4000 0 1 23155972518955713 2251799813685248 6250000847 60500000000000000 3959648144768907967287 4503599627370496000 1068743894836153 121000000000000000000 (Enclosure.Real.IsNear.const Bool.false 341998 4000) (BSN.isNear_log_sfrac 467851528016 16000000 23155972518955713 2251799813685248 6250000847 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 467851528016) qz350)) Bool.false Ns96p1759 Ns96p86 1000000135520000 9680000000000000000000 23155972518955713 2251799813685248 6250000847 60500000000000000 (BSN.log_rat_reduce_isNear 467851528016 16000000 14 935703056032 524288000000 19436640 33554432 24973259072661432 36028797018963968 9680000 1000000000000000 rfl rfl rfl rfl (Ns96p1763 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p1765 := BSN.arctan_dyadic_bound_f 1000 683996 1 0 4194304 1210000 0 1 1 0 1 1 6132 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 683996) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 683996) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz577 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 683996)))

noncomputable def Ns96p1766 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz577 884279719003555 562949953421312 1 2000000000000000 6132 4194304 1 1210000 3705485953421107265536 883456695895459 562949953421312 200000000121 242000000000000000 qz17 (Ns96p1765 rfl) rfl rfl 

noncomputable def Ns96p1767 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 341998 4000) qz789) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz577)) 3959648144768907967287 4503599627370496000 1068743894836153 121000000000000000000 883456695895459 2251799813685248 200000000121 968000000000000000 Ns96p1758 3957881231377117049287 4503599627370496000 49715631584149 5500000000000000000 (Ns96p1764 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz577) 1 4 0 1 883456695895459 562949953421312 200000000121 242000000000000000 883456695895459 2251799813685248 200000000121 968000000000000000 qz353 Ns96p1766 rfl) 

noncomputable def Ns96p1768 := @Ns96p1753 Ns96p1747 Ns96p1748 108312035501934201 5632000000000000000000 (@Ns96p1755 108312035501934201 5632000000000000000000 (Ns96p1757 (Ns96p1767 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 341998 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz576 (Real.log Real.pi) 341998 2000 0 1 38410761 33554432 1 16777216 6568201720239 33554432000 170999 16777216000 (Enclosure.Real.IsNear.const Bool.false 341998 2000) RS097to114.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns96p1749 Ns96p1750) 

noncomputable def Ns96p1769 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz228) Bool.false Ns96p1747 Ns96p1748 108312035501934201 5632000000000000000000 4295630179 8388608 81 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz228) (@HAdd.hAdd Real Real Real qz354 qz573 (Enclosure.sfrac Bool.true Ns96p1749 Ns96p1750)) Bool.false Ns96p1747 Ns96p1748 108312035501934201 5632000000000000000000 Ns96p1751 (Ns96p1768 rfl rfl)) 

noncomputable def Ns96p1770 := nat_lit 1898274185002429697753088 

noncomputable def Ns96p1771 := nat_lit 139781577240770980869189085238729572373399983891878757365886378218770365559418487111680 

noncomputable def Ns96p1772 := nat_lit 280435590240366883905538539989321318175870211730717696438011430638439720331058937856 

noncomputable def Ns96p1773 := nat_lit 365640568484487213035838637036689978843762834612118440640231353018603007394131466059776 

noncomputable def Ns96p1774 := BSN.sin_dyadic_bound_f 26976098652 17179869184 3 2 8388608 2422364 Ns96p1771 Ns96p99 Ns96p1772 Ns96p1773 Ns96p102 Ns96p1772 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26976098652) qz355 0 2 Ns96p1771 Ns96p99 Ns96p1772 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26976098652) qz356 0 2 Ns96p1773 Ns96p102 Ns96p1772 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1775 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz228) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4295630179) qz357) Bool.false 4295630179 8388608 81 4194304 Bool.true 8388606 8388608 1 1210000 (Ns96p1769 rfl) (Enclosure.sfrac_false_div 4295630179 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4295630179) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns96p1770) qz358) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 81 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q1 4295630179 8388608 226375608064910080 72057594037927936 81 Ns96p1770 Ns96p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388606 8388608 Ns96p1770 Ns96p86 26976098652 17179869184 2422364 2420000 (Ns96p1774 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p1776 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz228) Bool.false Ns96p1747 Ns96p1748 108312035501934201 5632000000000000000000 34365041434 67108864 1292 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz228) (@HAdd.hAdd Real Real Real qz354 qz573 (Enclosure.sfrac Bool.true Ns96p1749 Ns96p1750)) Bool.false Ns96p1747 Ns96p1748 108312035501934201 5632000000000000000000 Ns96p1751 (Ns96p1768 rfl rfl)) 

noncomputable def Ns96p1777 := Ns96p1746 27641 BSN.abs_quadSignPos (BSN.cos_quad_nat3 175 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 9018641 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 86 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 20049206 67108864) qz231 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz228) qz228 1) Bool.true 4194303 4194304 6387769 317194240000 67108848 67108864 1352 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz228) qz228 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz228)) Bool.true 4194303 4194304 6387769 317194240000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz228) qz228) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz228)) Bool.true 8388606 8388608 102204304 5075107840000 4194303 4194304 6387769 317194240000 (Ns96p1775 rfl rfl) rfl)) rfl) (Ns96p1776 rfl) RS097to114.d7 

noncomputable def Ns96p1778 := nat_lit 6696200454982955496376918641 

noncomputable def Ns96p1779 := BSN.sin_dyadic_bound_f 9046011 67108864 2 1 67108864 33554432 Ns96p1778 Ns96p127 Ns96p1778 Ns96p1778 Ns96p128 Ns96p1778 9018641 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 9046011) qz360 0 1 Ns96p1778 Ns96p127 Ns96p1778 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 9046011) (BSN.sinOddQ 67108864) 0 1 Ns96p1778 Ns96p128 Ns96p1778 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1780 := nat_lit 430343659630554608183276774024813892519532361567346203566425225860427855837050024749533460496993773681 

noncomputable def Ns96p1781 := nat_lit 143334852371913616971051243343354650886188939062248535130340996318768014473851841534151466969201 

noncomputable def Ns96p1782 := nat_lit 2608081721844550544118369502423727896083857907145519832908500120389627918613018206251304790978090002545 

noncomputable def Ns96p1783 := BSN.cos_dyadic_bound_f 85054243 67108864 4 3 67108864 33554432 Ns96p1780 Ns96p236 Ns96p1781 Ns96p1782 Ns96p239 Ns96p1781 20049206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 85054243) qz359 0 3 Ns96p1780 Ns96p236 Ns96p1781 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 85054243) (BSN.cosOddQ 67108864) 0 3 Ns96p1782 Ns96p239 Ns96p1781 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1784 := nat_lit 107934925260631849172602716481 

noncomputable def Ns96p1785 := BSN.cos_dyadic_bound_f 18125521 67108864 2 1 67108864 33554432 Ns96p1784 Ns96p131 Ns96p1784 Ns96p1784 Ns96p132 Ns96p1784 64675935 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 18125521) qz359 0 1 Ns96p1784 Ns96p131 Ns96p1784 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 18125521) (BSN.cosOddQ 67108864) 0 1 Ns96p1784 Ns96p132 Ns96p1784 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1786 := nat_lit 120626750774964682567515178886227603321985256011519656740969752481 

noncomputable def Ns96p1787 := nat_lit 12529662464677271665844989733787176841847310940679493699741601 

noncomputable def Ns96p1788 := nat_lit 361855192999964693159213846679215235612272073412677611235509774241 

noncomputable def Ns96p1789 := BSN.cos_dyadic_bound_f 43375293 67108864 3 2 67108864 33554432 Ns96p1786 Ns96p108 Ns96p1787 Ns96p1788 Ns96p111 Ns96p1787 53572475 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 43375293) qz359 0 2 Ns96p1786 Ns96p108 Ns96p1787 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 43375293) (BSN.cosOddQ 67108864) 0 2 Ns96p1788 Ns96p111 Ns96p1787 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1790 := Ns96p1744 47026 BSN.abs_quadSignPos (BSN.cos_quad_nat0 24 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 64675935 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 24 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 53572475 67108864) qz231 rfl rfl (Ns96p1777 RS097to114.d9 RS097to114.d11 RS097to114.d13 RS097to114.d17 (Ns96p1779 rfl rfl) (Ns96p1783 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns96p1776 rfl) RS097to114.d19 RS097to114.d21 RS097to114.d23 RS097to114.d25 RS097to114.d17 (Ns96p1785 rfl rfl) (Ns96p1789 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns96p1791 := nat_lit 16191108886681132497735190641 

noncomputable def Ns96p1792 := BSN.cos_dyadic_bound_f 11280261 67108864 2 1 67108864 33554432 Ns96p1791 Ns96p131 Ns96p1791 Ns96p1791 Ns96p132 Ns96p1791 66163050 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 11280261) qz359 0 1 Ns96p1791 Ns96p131 Ns96p1791 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 11280261) (BSN.cosOddQ 67108864) 0 1 Ns96p1791 Ns96p132 Ns96p1791 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1793 := nat_lit 1518759620374764424924211824718062275642434481946271159937468006400 

noncomputable def Ns96p1794 := nat_lit 612667654549172960706905897355851189326835577885612299224416256 

noncomputable def Ns96p1795 := nat_lit 3976711829540827213817505502808729819995084957018895379923195723776 

noncomputable def Ns96p1796 := BSN.sin_dyadic_bound_f 70534748 67108864 3 2 67108864 33554432 Ns96p1793 Ns96p221 Ns96p1794 Ns96p1795 Ns96p224 Ns96p1794 58246804 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 70534748) qz360 0 2 Ns96p1793 Ns96p221 Ns96p1794 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 70534748) (BSN.sinOddQ 67108864) 0 2 Ns96p1795 Ns96p224 Ns96p1794 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1797 := Ns96p1742 63388 BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66163050 67108864) BSN.abs_quadSignNeg qz486 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 58246804 67108864) qz231 rfl rfl (Ns96p1790 rfl rfl) (Ns96p1776 rfl) RS097to114.d27 RS097to114.d29 RS097to114.d31 RS097to114.d33 RS097to114.d17 (Ns96p1792 rfl rfl) (Ns96p1796 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns96p1798 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz228) qz228 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz228) qz228 7) 11015089 67108864 63388 67108864 11015089 67108864 63388 67108864 1478420219297792 11015089 33554432 15847 8388608 (Ns96p1797 rfl) 

noncomputable def Ns96p1799 := @Enclosure.Real.IsNear.mulLit_tf qz787 (Zeta.RiemannSiegel.correction qz230) 193023 524288 1 4194304 3600300445713 8796093022208 18620702804727 332602267402240000 694940792932860399 4611686018427387904 

noncomputable abbrev qz791 := (@HPow.hPow Real Real Real qz7 qz229 qz9)

noncomputable def Ns96p1800 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz791 1 1 0 1 193023 524288 1 4194304 193023 524288 1 4194304 

noncomputable def Ns96p1801 := @Enclosure.Real.IsNear.sqrt_image qz229 228298883911 4194304000 170999 4194304000 30944372 30944396 4194304 (@Enclosure.Real.IsNear.of_eq qz229 (@HMul.hMul Real Real Real qz5 qz228 qz3) Bool.false 228298883911 4194304000 170999 4194304000 (BSN.t_div_two_pi_mk qz228 341998 1000 qz231) (@Enclosure.Real.IsNear.mulLit_ff qz228 qz3 341998 1000 0 1 1335089 8388608 1 8388608 228298883911 4194304000 170999 4194304000 (Enclosure.Real.IsNear.const Bool.false 341998 1000) RS097to114.d36 rfl)) 

noncomputable abbrev qz934 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 341998 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz792 := qz934

noncomputable abbrev qz578 := qz792

noncomputable abbrev qz233 := qz578

noncomputable def Ns96p1802 := @Enclosure.Real.IsNear.sqrt_image qz233 241753 32768 3 1048576 11392545 11392551 4194304 (@Enclosure.Real.IsNear.recentre' qz233 Bool.false 61888768 8388608 24 8388608 241753 32768 3 1048576 (Ns96p1801 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns96p1803 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz233) 2848137 1048576 3 4194304 1544183 1544185 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz233) Bool.false 22785096 8388608 6 8388608 2848137 1048576 3 4194304 (Ns96p1802 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns96p1804 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz233)) Bool.false 3088368 8388608 2 8388608 193023 524288 1 4194304 (Ns96p1803 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz234 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz571))

noncomputable abbrev qz793 := (@HMul.hMul Real Real Real qz863 qz933 qz933)

noncomputable abbrev qz579 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz793 qz786) qz641)

noncomputable abbrev qz235 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz579))

noncomputable def Ns96p1805 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz230) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz234) qz235) Bool.false 3600300445713 

noncomputable def Ns96p1806 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz234) qz235 2916477 2097152 153 

noncomputable abbrev qz794 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz234))

noncomputable def Ns96p1807 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz234) (@Neg.neg Real Real.instNeg qz794) Bool.true 2916477 2097152 153 4194304 (BSN.inv_eq_neg_inv_neg qz234) 

noncomputable def Ns96p1808 := @Enclosure.Real.IsNear.recentre' qz794 Bool.false 11665908 8388608 306 8388608 2916477 2097152 

noncomputable def Ns96p1809 := @Enclosure.Real.IsNear.recentre' qz234 Bool.true 6031999 8388608 191098608 10150215680000 6031999 8388608 11943663 634388480000 

noncomputable abbrev qz236 := (@HMul.hMul Real Real Real qz339 qz337 qz571)

noncomputable def Ns96p1810 := @Enclosure.Real.IsNear.cos_image qz236 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4977087) qz706) Bool.false 4977087 2097152 151 8388608 Bool.true 6031999 8388608 1 

noncomputable def Ns96p1811 := nat_lit 80958226230534300219752789 

noncomputable def Ns96p1812 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz230 884279719003555 140737488355328 1 500000000000000 12377 32768 3 1048576 10944730082107000235 4611686018427387904 Ns96p1811 

noncomputable def Ns96p1813 := @Enclosure.Real.IsNear.subLit_ff_p qz233 qz1 241753 32768 3 1048576 7 1 0 1 12377 12377 32768 3 

noncomputable def Ns96p1814 := @Ns96p1813 1048576 (@Enclosure.Real.IsNear.recentre' qz233 Bool.false 61888768 8388608 24 8388608 241753 32768 3 1048576 (Ns96p1801 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns96p1815 := @Enclosure.Real.IsNear.recentre' qz236 Bool.false 10944730082107000235 4611686018427387904 Ns96p1811 Ns96p487 4977087 2097152 151 8388608 (@Ns96p1812 Ns96p487 RS097to114.d35 (Ns96p1814 rfl rfl) rfl) 

noncomputable def Ns96p1816 := nat_lit 9517036344589945447004539165536753815779918512797066716307416161507386084903485128960 

noncomputable def Ns96p1817 := nat_lit 1304854126915197837478490076220257898763745652220889444985339238348236061860905216 

noncomputable def Ns96p1818 := nat_lit 24923458757720565850417875497234760528539883373888721864560875588038209268742305300736 

noncomputable def Ns96p1819 := BSN.sin_dyadic_bound_f 13786221294 17179869184 3 2 8388608 2422364 Ns96p1816 Ns96p99 Ns96p1817 Ns96p1818 Ns96p102 Ns96p1817 6031999 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 13786221294) qz355 0 2 Ns96p1816 Ns96p99 Ns96p1817 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 13786221294) qz356 0 2 Ns96p1818 Ns96p102 Ns96p1817 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1820 := @Ns96p1810 1210000 (Ns96p1815 rfl) (Enclosure.sfrac_false_div 4977087 2097152) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4977087) qz706) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 242529769870354970312704) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 6031999 8388608 0 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q1 4977087 2097152 226375608064910080 72057594037927936 0 242529769870354970312704 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 6031999 8388608 242529769870354970312704 302231454903657293676544 13786221294 17179869184 2422364 2420000 (Ns96p1819 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p1821 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz234) 6031999 8388608 11943663 634388480000 5832801 5833107 4194304 (@Enclosure.Real.IsNear.neg qz234 Bool.true 6031999 8388608 11943663 634388480000 (Ns96p1809 (Ns96p1820 rfl rfl) rfl)) 

noncomputable def Ns96p1822 := Ns96p1807 (@Enclosure.Real.IsNear.neg qz794 Bool.false 2916477 2097152 153 4194304 (@Ns96p1808 153 4194304 (Ns96p1821 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p1823 := @Enclosure.Real.IsNear.recentre' qz235 Bool.true 1234469 4194304 

noncomputable abbrev qz237 := (@HMul.hMul Real Real Real qz339 qz337 qz579)

noncomputable def Ns96p1824 := @Enclosure.Real.IsNear.cos_image qz237 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 15682843)) qz357) Bool.true 15682843 8388608 

noncomputable def Ns96p1825 := nat_lit 1192162989813407695073308077931 

noncomputable def Ns96p1826 := @Enclosure.Real.IsNear.recentre' qz237 Bool.true 282516998504811629803405 151115727451828646838272 Ns96p1825 

noncomputable def Ns96p1827 := nat_lit 37778931862957161709568000000000000 

noncomputable abbrev qz238 := qz579

noncomputable def Ns96p1828 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz238 884279719003555 140737488355328 1 500000000000000 319488271 

noncomputable abbrev qz580 := (@HSub.hSub Real Real Real qz635 qz793 qz786)

noncomputable abbrev qz239 := qz580

noncomputable def Ns96p1829 := @Enclosure.Real.IsNear.subLit_tf qz239 qz26 252379407 1073741824 5522121 1099511627776 1 16 

noncomputable abbrev qz581 := qz793

noncomputable abbrev qz240 := qz581

noncomputable def Ns96p1830 := @Enclosure.Real.IsNear.subLit_ff_n qz240 qz230 153190129 1073741824 2376393 1099511627776 12377 32768 3 1048576 

noncomputable def Ns96p1831 := @Enclosure.Real.IsNear.mulLit_ff qz230 qz230 12377 32768 3 1048576 12377 32768 3 1048576 153190129 1073741824 

noncomputable def Ns96p1832 := nat_lit 29819057956913164748435804121493039864274513136420233877412307981515221172668447088801782481 

noncomputable def Ns96p1833 := nat_lit 221359180026917656439616581624419503815620427250759103724099763196022239057672889211601 

noncomputable def Ns96p1834 := nat_lit 180030534094510887176687520569526435018881716947018306169105919464666706664888156377449274065 

noncomputable def Ns96p1835 := BSN.cos_dyadic_bound_t 15682843 8388608 4 3 4194304 1210000 Ns96p1832 Ns96p908 Ns96p1833 Ns96p1834 Ns96p911 Ns96p1833 1234469 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 15682843) (BSN.cosEvenQ 8388608) 0 3 Ns96p1832 Ns96p908 Ns96p1833 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 15682843) (BSN.cosOddQ 8388608) 0 3 Ns96p1834 Ns96p911 Ns96p1833 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1836 := @Ns96p1823 165124304 5075107840000 1234469 4194304 10320269 317194240000 (@Ns96p1824 133 4194304 Bool.true 1234469 4194304 1 1210000 (@Ns96p1826 Ns96p1827 15682843 8388608 133 4194304 (@Ns96p1828 1073741824 5522121 1099511627776 282516998504811629803405 151115727451828646838272 Ns96p1825 Ns96p1827 RS097to114.d35 (@Ns96p1829 0 1 5111812336 319488271 1073741824 5522121 1099511627776 (@Ns96p1830 8269968408576 252379407 1073741824 5522121 1099511627776 (@Ns96p1831 2376393 1099511627776 (Ns96p1814 rfl rfl) (Ns96p1814 rfl rfl) rfl) (Ns96p1814 rfl rfl) rfl rfl) qz369 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 15682843 8388608) (BSN.cos_neg_of_bound 15682843 8388608 Bool.true 1234469 4194304 1 1210000 (Ns96p1835 rfl rfl)) rfl rfl) 

noncomputable def Ns96p1837 := @Ns96p1799 11555978528448354123 558014008229713936384000 (Ns96p1800 qz28 (@Enclosure.Real.IsNear.of_eq qz791 (@Inv.inv Real Real.instInv (Real.sqrt qz233)) Bool.false 193023 524288 1 4194304 (BSN.rpow_neg_quarter_mk qz229 (BSN.t_div_two_pi_nonneg qz228 341998 1000 qz231)) Ns96p1804) rfl) (@Ns96p1805 8796093022208 18620702804727 332602267402240000 (BSN.correction_mk qz230 (BSN.cos_two_pi_p_ne_zero_mk qz228 341998 1000 7 qz231 rfl rfl (@BSN.floor_sqrt_eq_dec qz228 341998 1000 7 qz231 rfl rfl rfl))) (@Ns96p1806 4194304 1234469 4194304 10320269 317194240000 3600300445713 8796093022208 18620702804727 332602267402240000 Ns96p1822 (Ns96p1836 rfl) rfl)) 

noncomputable def Ns96p1838 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz228) (hardyZApproximantRS₀ qz228) Bool.true 818961511628078609 4611686018427387904 1065705604833107810123 558014008229713936384000 (@Eq.refl Real (hardyZApproximantRS₀ qz228)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz228) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz228) qz228 7) (@HMul.hMul Real Real Real qz5 qz787 (Zeta.RiemannSiegel.correction qz230))) Bool.true 818961511628078609 4611686018427387904 1065705604833107810123 558014008229713936384000 (BSN.hardyZApproximantRS₀_eq qz228 7 (@BSN.floor_sqrt_eq_dec qz228 341998 1000 7 qz231 rfl rfl rfl)) (@Ns96p1740 818961511628078609 4611686018427387904 1065705604833107810123 558014008229713936384000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz228) qz228 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz228) qz228 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz228) qz228 7)) Bool.true 11015089 33554432 15847 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz228) qz228 7) (Ns96p1798 (Ns96p1797 rfl) rfl rfl)) (Ns96p1837 rfl) rfl rfl)) 

theorem RS097to114.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz228) Bool.true 818961511628078609 4611686018427387904 1065705604833107810123 558014008229713936384000 := Ns96p1838 

noncomputable def Ns96p1839 := nat_lit 7113316098584159996581249024 

noncomputable abbrev qz935 := (Enclosure.sfrac Bool.false 343569 1000)

noncomputable abbrev qz795 := qz935

noncomputable abbrev qz582 := qz795

noncomputable abbrev qz241 := qz582

noncomputable abbrev qz936 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 343569 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz796 := qz936

noncomputable abbrev qz583 := qz796

noncomputable abbrev qz242 := qz583

noncomputable abbrev qz937 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 343569 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz797 := qz937

noncomputable abbrev qz584 := qz797

noncomputable abbrev qz243 := qz584

noncomputable abbrev qz798 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz242 qz9))

noncomputable def Ns96p1840 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz241) qz241 7) (@HMul.hMul Real Real Real qz5 qz798 (Zeta.RiemannSiegel.correction qz243)) 93921001 16777216 995 524288 10917748463731081035 73786976294838206464 106685146194330735837 Ns96p180 Ns96p1839 

noncomputable def Ns96p1841 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz241) qz241 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 343569 1000 63 97 67108864 33554432 1125899906842624 Bool.false 34575856347 1298 

noncomputable def Ns96p1842 := Ns96p1841 120242927 57 27397080 8 130587807 57 25364760 8 Bool.false 181663512 47243 Bool.true 94781344 Bool.true 64873280 3537118876014220 1 Bool.false 66268254 Bool.false Bool.false 55231163 Bool.true Bool.false 187842002 

noncomputable def Ns96p1843 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz241) qz241 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 343569 1000 24 24 67108864 33554432 1125899906842624 Bool.false 34575856347 1298 

noncomputable def Ns96p1844 := Ns96p1843 93032624 56 33554424 8 108007536 56 30011992 8 Bool.false 140567333 27769 Bool.false 82786182 Bool.true 2240219 3537118876014220 1 Bool.false 22201822 Bool.false Bool.false 67071476 Bool.false Bool.false 181663512 

noncomputable def Ns96p1845 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz241) qz241 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 343569 1000 176 87 67108864 33554432 1125899906842624 Bool.false 34575856347 1298 

noncomputable def Ns96p1846 := Ns96p1845 46516304 56 47453136 16 73726608 56 38745320 8 Bool.false 67108832 1360 Bool.false 41369454 Bool.false 74630298 3537118876014220 1 Bool.false 54756425 Bool.false Bool.false 60171203 Bool.false Bool.false 140567333 

noncomputable def Ns96p1847 := nat_lit 1526509137069742787480558406823329515174162504581885389 

noncomputable def Ns96p1848 := nat_lit 2962827385789718908797714464981537112779328480870400 

noncomputable def Ns96p1849 := nat_lit 2297806330971468358249223447520000 

noncomputable def Ns96p1850 := nat_lit 4736734821638938473707623832501993280 

noncomputable abbrev qz938 := (@Eq.refl Real (Enclosure.sfrac Bool.false 343569 1000))

noncomputable abbrev qz799 := qz938

noncomputable abbrev qz585 := qz799

noncomputable abbrev qz244 := qz585

noncomputable def Ns96p1851 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz241 343569 1000 472159631044 16000000 687138 4000 2000 Ns96p1849 Ns96p1850 qz244 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns96p1852 := nat_lit 4396346314760859227944008211651189003701588013195829920320 

noncomputable abbrev qz800 := (Real.log (Enclosure.sfrac Bool.false 472159631044 16000000))

noncomputable abbrev qz245 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 343569 4000) qz800) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 687138))))))

noncomputable abbrev qz801 := (Enclosure.sfrac Bool.false 343569 2000)

noncomputable abbrev qz586 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz245 qz801) (@HMul.hMul Real Real Real qz5 qz801 (Real.log Real.pi)))

noncomputable def Ns96p1853 := @Enclosure.Real.IsNear.addLit_ft_p qz586 (Enclosure.sfrac Bool.true Ns96p1849 Ns96p1850) 928139450415674767869 1801439850948198400 2393693098667197941 123904000000000000000000 Ns96p1849 Ns96p1850 0 1 Ns96p1852 

noncomputable def Ns96p1854 := nat_lit 311431920754901307325761454080000 

noncomputable abbrev qz587 := (@HSub.hSub Real Real Real qz12 qz245 qz801)

noncomputable abbrev qz588 := (@HMul.hMul Real Real Real qz5 qz801 (Real.log Real.pi))

noncomputable def Ns96p1855 := @Enclosure.Real.IsNear.subLit_ff_p qz587 qz588 6411934617319094886897 9007199254740992000 2197306541033193 242000000000000000000 13196746746009 67108864000 343569 33554432000 Ns96p1854 928139450415674767869 1801439850948198400 

noncomputable def Ns96p1856 := nat_lit 12823869234638189773794000 

noncomputable abbrev qz589 := qz801

noncomputable def Ns96p1857 := @Enclosure.Real.IsNear.subLit_ff_p qz245 qz589 7959231837695148827121 9007199254740992000 2197306541033193 242000000000000000000 343569 2000 0 1 Ns96p1856 6411934617319094886897 9007199254740992000 2197306541033193 242000000000000000000 

noncomputable def Ns96p1858 := nat_lit 17922596769199630178235162471860011008 

noncomputable def Ns96p1859 := nat_lit 12442849245425031559774208 

noncomputable def Ns96p1860 := nat_lit 3321054135396525408189047503347670293141897208248615964545823913425610539067061333677055009169994517631673762492337786714240607910439101931045519360 

noncomputable def Ns96p1861 := nat_lit 95275526407610622795362160929034743640363448635197420399849003681209522535153126160996083010315543648838621443391860769280037073565094062422228992 

noncomputable def Ns96p1862 := nat_lit 76532152630325350238614302735870555097942346317462250410010488922423691596362968416167497573171595567688802747676068448216884469926954270720 

noncomputable def Ns96p1863 := BSN.log_dyadic_bound 210015631044 734303631044 7 6 Ns96p1860 33554432 9680000 Ns96p1861 Ns96p1862 19744204 944319262088 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 210015631044) (BSN.artanhQ 734303631044) 0 6 Ns96p1861 Ns96p1860 Ns96p1862 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns96p1864 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 343569 4000) qz800 343569 4000 0 1 23176612789603009 2251799813685248 6250000847 60500000000000000 7962765679511116199121 9007199254740992000 2147306541002943 242000000000000000000 (Enclosure.Real.IsNear.const Bool.false 343569 4000) (BSN.isNear_log_sfrac 472159631044 16000000 23176612789603009 2251799813685248 6250000847 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 472159631044) qz350)) Bool.false Ns96p1859 Ns96p86 1000000135520000 9680000000000000000000 23176612789603009 2251799813685248 6250000847 60500000000000000 (BSN.log_rat_reduce_isNear 472159631044 16000000 14 944319262088 524288000000 19744204 33554432 24973259072661432 36028797018963968 9680000 1000000000000000 rfl rfl rfl rfl (Ns96p1863 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p1865 := BSN.arctan_dyadic_bound_f 1000 687138 1 0 4194304 1210000 0 1 1 0 1 1 6104 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 687138) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 687138) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz590 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 687138)))

noncomputable def Ns96p1866 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz590 884279719003555 562949953421312 1 2000000000000000 6104 4194304 1 1210000 3705501716019803062272 883460453991843 562949953421312 200000000121 242000000000000000 qz17 (Ns96p1865 rfl) rfl rfl 

noncomputable def Ns96p1867 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 343569 4000) qz800) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz590)) 7962765679511116199121 9007199254740992000 2147306541002943 242000000000000000000 883460453991843 2251799813685248 200000000121 968000000000000000 Ns96p1858 7959231837695148827121 9007199254740992000 2197306541033193 242000000000000000000 (Ns96p1864 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz590) 1 4 0 1 883460453991843 562949953421312 200000000121 242000000000000000 883460453991843 2251799813685248 200000000121 968000000000000000 qz353 Ns96p1866 rfl) 

noncomputable def Ns96p1868 := @Ns96p1853 Ns96p1847 Ns96p1848 2393693098667197941 123904000000000000000000 (@Ns96p1855 2393693098667197941 123904000000000000000000 (Ns96p1857 (Ns96p1867 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 343569 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz589 (Real.log Real.pi) 343569 2000 0 1 38410761 33554432 1 16777216 13196746746009 67108864000 343569 33554432000 (Enclosure.Real.IsNear.const Bool.false 343569 2000) RS097to114.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns96p1849 Ns96p1850) 

noncomputable def Ns96p1869 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz241) Bool.false Ns96p1847 Ns96p1848 2393693098667197941 123904000000000000000000 4321982043 8388608 163 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz241) (@HAdd.hAdd Real Real Real qz354 qz586 (Enclosure.sfrac Bool.true Ns96p1849 Ns96p1850)) Bool.false Ns96p1847 Ns96p1848 2393693098667197941 123904000000000000000000 Ns96p1851 (Ns96p1868 rfl rfl)) 

noncomputable def Ns96p1870 := nat_lit 1898025547875466887561216 

noncomputable def Ns96p1871 := nat_lit 139708210099330873035623560843072485562049252621159431826766510619551127772764815663360 

noncomputable def Ns96p1872 := nat_lit 280141871907443768194615483371002711895404546123821452352079656082834689297157366016 

noncomputable def Ns96p1873 := nat_lit 365448891991349758516222805711160600652774530456931372432961303608023602288855310049536 

noncomputable def Ns96p1874 := BSN.sin_dyadic_bound_f 26972565306 17179869184 3 2 8388608 2422364 Ns96p1871 Ns96p99 Ns96p1872 Ns96p1873 Ns96p102 Ns96p1872 8388604 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26972565306) qz355 0 2 Ns96p1871 Ns96p99 Ns96p1872 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26972565306) qz356 0 2 Ns96p1873 Ns96p102 Ns96p1872 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1875 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz241) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4321982043) qz357) Bool.false 4321982043 8388608 163 8388608 Bool.false 8388604 8388608 1 1210000 (Ns96p1869 rfl) (Enclosure.sfrac_false_div 4321982043 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4321982043) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns96p1870) qz358) 226375608064910080 72057594037927936 Bool.false 8388604 8388608 81 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q3 4321982043 8388608 226375608064910080 72057594037927936 81 Ns96p1870 Ns96p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388604 8388608 Ns96p1870 Ns96p86 26972565306 17179869184 2422364 2420000 (Ns96p1874 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p1876 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz241) Bool.false Ns96p1847 Ns96p1848 2393693098667197941 123904000000000000000000 34575856347 67108864 1298 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz241) (@HAdd.hAdd Real Real Real qz354 qz586 (Enclosure.sfrac Bool.true Ns96p1849 Ns96p1850)) Bool.false Ns96p1847 Ns96p1848 2393693098667197941 123904000000000000000000 Ns96p1851 (Ns96p1868 rfl rfl)) 

noncomputable def Ns96p1877 := Ns96p1846 27769 BSN.abs_quadSignPos (BSN.cos_quad_nat0 176 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 54756425 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 87 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 60171203 67108864) qz244 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz241) qz241 1) Bool.false 2097151 2097152 12851163 634388480000 67108832 67108864 1360 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz241) qz241 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz241)) Bool.false 2097151 2097152 12851163 634388480000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz241) qz241) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz241)) Bool.false 8388604 8388608 205618608 10150215680000 2097151 2097152 12851163 634388480000 (Ns96p1875 rfl rfl) rfl)) rfl) (Ns96p1876 rfl) RS097to114.d7 

noncomputable def Ns96p1878 := nat_lit 99812588100281415355668213535648793175404259100293492284695593216 

noncomputable def Ns96p1879 := nat_lit 8579032487139570449819770698245702154502174458092172945735936 

noncomputable def Ns96p1880 := nat_lit 299420606235869966926105001065549888121903772951964292508195307776 

noncomputable def Ns96p1881 := BSN.cos_dyadic_bound_f 41369454 67108864 3 2 67108864 33554432 Ns96p1878 Ns96p108 Ns96p1879 Ns96p1880 Ns96p111 Ns96p1879 54756425 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 41369454) qz359 0 2 Ns96p1878 Ns96p108 Ns96p1879 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 41369454) (BSN.cosOddQ 67108864) 0 2 Ns96p1880 Ns96p111 Ns96p1879 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1882 := nat_lit 1903626052212501868211208387392399663291357947876760911676275564800 

noncomputable def Ns96p1883 := nat_lit 962324197385864094349172888960498174178742037962357375131853056 

noncomputable def Ns96p1884 := nat_lit 4984129230903642065352789972778920216338219519234815713878127288576 

noncomputable def Ns96p1885 := BSN.sin_dyadic_bound_f 74630298 67108864 3 2 67108864 33554432 Ns96p1882 Ns96p221 Ns96p1883 Ns96p1884 Ns96p224 Ns96p1883 60171203 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 74630298) qz360 0 2 Ns96p1882 Ns96p221 Ns96p1883 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 74630298) (BSN.sinOddQ 67108864) 0 2 Ns96p1884 Ns96p224 Ns96p1883 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1886 := nat_lit 386184296146549249230089126890156011772852945104014433353502503852929940718166294174567721694365945856 

noncomputable def Ns96p1887 := nat_lit 103632087627429024127149826413726032571962614330495284029282144243531903283545457397351308005376 

noncomputable def Ns96p1888 := nat_lit 2340700776325667042587266369238294645676884620881168008389086266544595693614900700281148423297391595520 

noncomputable def Ns96p1889 := BSN.cos_dyadic_bound_f 82786182 67108864 4 3 67108864 33554432 Ns96p1886 Ns96p236 Ns96p1887 Ns96p1888 Ns96p239 Ns96p1887 22201822 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 82786182) qz359 0 3 Ns96p1886 Ns96p236 Ns96p1887 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 82786182) (BSN.cosOddQ 67108864) 0 3 Ns96p1888 Ns96p239 Ns96p1887 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1890 := nat_lit 25186156939412794892897521 

noncomputable def Ns96p1891 := BSN.cos_dyadic_bound_f 2240219 67108864 2 1 67108864 33554432 Ns96p1890 Ns96p131 Ns96p1890 Ns96p1890 Ns96p132 Ns96p1890 67071476 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 2240219) qz359 0 1 Ns96p1890 Ns96p131 Ns96p1890 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 2240219) (BSN.cosOddQ 67108864) 0 1 Ns96p1890 Ns96p132 Ns96p1890 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1892 := Ns96p1844 47243 BSN.abs_quadSignPos (BSN.cos_quad_nat0 24 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 22201822 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 24 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 67071476 67108864) qz244 rfl rfl (Ns96p1877 RS097to114.d9 RS097to114.d11 RS097to114.d13 RS097to114.d17 (Ns96p1881 rfl rfl) (Ns96p1885 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns96p1876 rfl) RS097to114.d19 RS097to114.d21 RS097to114.d23 RS097to114.d25 RS097to114.d17 (Ns96p1889 rfl rfl) (Ns96p1891 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns96p1893 := nat_lit 1725046558159452716994363797033099302832981731090976017634686970338820868746762327467702503611287207936 

noncomputable def Ns96p1894 := nat_lit 525622990090696019407419338219580901746819649985497079803053392002895882015911007819172608475136 

noncomputable def Ns96p1895 := nat_lit 8618224110224886315871185583673196377623129565144640506753651141373219925150124358976907103463744208896 

noncomputable def Ns96p1896 := BSN.sin_dyadic_bound_f 94781344 67108864 4 3 67108864 33554432 Ns96p1893 Ns96p762 Ns96p1894 Ns96p1895 Ns96p765 Ns96p1894 66268254 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 94781344) qz360 0 3 Ns96p1893 Ns96p762 Ns96p1894 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 94781344) (BSN.sinOddQ 67108864) 0 3 Ns96p1895 Ns96p765 Ns96p1894 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1897 := nat_lit 1086651184480580980841585418356232514451713065049999788778455040000 

noncomputable def Ns96p1898 := nat_lit 313708908503443718226076945801575434653220960252565913600000000 

noncomputable def Ns96p1899 := nat_lit 2845483287787754136184167209211215939526952812623876244845363200000 

noncomputable def Ns96p1900 := BSN.sin_dyadic_bound_f 64873280 67108864 3 2 67108864 33554432 Ns96p1897 Ns96p221 Ns96p1898 Ns96p1899 Ns96p224 Ns96p1898 55231163 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 64873280) qz360 0 2 Ns96p1897 Ns96p221 Ns96p1898 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 64873280) (BSN.sinOddQ 67108864) 0 2 Ns96p1899 Ns96p224 Ns96p1898 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1901 := Ns96p1842 63680 BSN.abs_quadSignPos (BSN.cos_quad_nat3 63 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66268254 67108864) BSN.abs_quadSignNeg qz486 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 55231163 67108864) qz244 rfl rfl (Ns96p1892 rfl rfl) (Ns96p1876 rfl) RS097to114.d27 RS097to114.d29 RS097to114.d31 RS097to114.d33 RS097to114.d17 (Ns96p1896 rfl rfl) (Ns96p1900 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns96p1902 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz241) qz241 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz241) qz241 7) 187842002 67108864 63680 67108864 187842002 67108864 63680 67108864 25211726731411456 93921001 16777216 995 524288 (Ns96p1901 rfl) 

noncomputable def Ns96p1903 := @Enclosure.Real.IsNear.mulLit_tf qz798 (Zeta.RiemannSiegel.correction qz243) 1542415 4194304 1 4194304 7078346919429 17592186044416 68820503812557 1330409069608960000 10917748463731081035 73786976294838206464 

noncomputable abbrev qz802 := (@HPow.hPow Real Real Real qz7 qz242 qz9)

noncomputable def Ns96p1904 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz802 1 1 0 1 1542415 4194304 1 4194304 1542415 4194304 1 4194304 

noncomputable def Ns96p1905 := @Enclosure.Real.IsNear.sqrt_image qz242 458695192641 8388608000 343569 8388608000 31015364 31015388 4194304 (@Enclosure.Real.IsNear.of_eq qz242 (@HMul.hMul Real Real Real qz5 qz241 qz3) Bool.false 458695192641 8388608000 343569 8388608000 (BSN.t_div_two_pi_mk qz241 343569 1000 qz244) (@Enclosure.Real.IsNear.mulLit_ff qz241 qz3 343569 1000 0 1 1335089 8388608 1 8388608 458695192641 8388608000 343569 8388608000 (Enclosure.Real.IsNear.const Bool.false 343569 1000) RS097to114.d36 rfl)) 

noncomputable abbrev qz939 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 343569 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz803 := qz939

noncomputable abbrev qz591 := qz803

noncomputable abbrev qz246 := qz591

noncomputable def Ns96p1906 := @Enclosure.Real.IsNear.sqrt_image qz246 1938461 262144 3 1048576 11405606 11405612 4194304 (@Enclosure.Real.IsNear.recentre' qz246 Bool.false 62030752 8388608 24 8388608 1938461 262144 3 1048576 (Ns96p1905 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns96p1907 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz246) 11405609 4194304 3 4194304 1542414 1542416 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz246) Bool.false 22811218 8388608 6 8388608 11405609 4194304 3 4194304 (Ns96p1906 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns96p1908 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz246)) Bool.false 3084830 8388608 2 8388608 1542415 4194304 1 4194304 (Ns96p1907 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz247 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz584))

noncomputable abbrev qz804 := (@HMul.hMul Real Real Real qz863 qz937 qz937)

noncomputable abbrev qz592 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz804 qz797) qz641)

noncomputable abbrev qz248 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz592))

noncomputable def Ns96p1909 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz243) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz247) qz248) Bool.false 7078346919429 

noncomputable def Ns96p1910 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz247) qz248 10634999 8388608 257 

noncomputable abbrev qz805 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz247))

noncomputable def Ns96p1911 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz247) (@Neg.neg Real Real.instNeg qz805) Bool.true 10634999 8388608 257 8388608 (BSN.inv_eq_neg_inv_neg qz247) 

noncomputable def Ns96p1912 := @Enclosure.Real.IsNear.recentre' qz805 Bool.false 10634999 8388608 257 8388608 10634999 8388608 

noncomputable def Ns96p1913 := @Enclosure.Real.IsNear.recentre' qz247 Bool.true 6616714 8388608 24038576 1268776960000 3308357 4194304 1502411 79298560000 

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz339 qz337 qz584)

noncomputable def Ns96p1914 := @Enclosure.Real.IsNear.cos_image qz249 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 20800459) qz357) Bool.false 20800459 8388608 19 1048576 Bool.true 6616714 8388608 1 

noncomputable def Ns96p1915 := nat_lit 16191645246137350875778321 

noncomputable def Ns96p1916 := nat_lit 900719925474099200000000000000 

noncomputable def Ns96p1917 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz243 884279719003555 140737488355328 1 500000000000000 103453 262144 3 1048576 91481389770074775415 36893488147419103232 Ns96p1915 

noncomputable def Ns96p1918 := @Enclosure.Real.IsNear.subLit_ff_p qz246 qz1 1938461 262144 3 1048576 7 1 0 1 103453 103453 262144 3 

noncomputable def Ns96p1919 := @Ns96p1918 1048576 (@Enclosure.Real.IsNear.recentre' qz246 Bool.false 62030752 8388608 24 8388608 1938461 262144 3 1048576 (Ns96p1905 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns96p1920 := @Enclosure.Real.IsNear.recentre' qz249 Bool.false 91481389770074775415 36893488147419103232 Ns96p1915 Ns96p1916 20800459 8388608 19 1048576 (@Ns96p1917 Ns96p1916 RS097to114.d35 (Ns96p1919 rfl rfl) rfl) 

noncomputable def Ns96p1921 := nat_lit 15657918885091117997084231609453386046928346537726854665050532825606504413503563710720 

noncomputable def Ns96p1922 := nat_lit 3531423180505748350159719261184374428594578451442430743264353065119197613943111936 

noncomputable def Ns96p1923 := nat_lit 41003117632946394971225109907859807802404135424172760187262300828768747143991520870656 

noncomputable def Ns96p1924 := BSN.sin_dyadic_bound_f 15613264622 17179869184 3 2 8388608 2422364 Ns96p1921 Ns96p99 Ns96p1922 Ns96p1923 Ns96p102 Ns96p1922 6616714 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 15613264622) qz355 0 2 Ns96p1921 Ns96p99 Ns96p1922 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 15613264622) qz356 0 2 Ns96p1923 Ns96p102 Ns96p1922 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1925 := @Ns96p1914 1210000 (Ns96p1920 rfl) (Enclosure.sfrac_false_div 20800459 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 20800459) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1098685824030959739076608) qz358) 226375608064910080 72057594037927936 Bool.false 6616714 8388608 0 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q1 20800459 8388608 226375608064910080 72057594037927936 0 1098685824030959739076608 Ns96p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 6616714 8388608 1098685824030959739076608 Ns96p86 15613264622 17179869184 2422364 2420000 (Ns96p1924 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p1926 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz247) 3308357 4194304 1502411 79298560000 5317371 5317628 4194304 (@Enclosure.Real.IsNear.neg qz247 Bool.true 3308357 4194304 1502411 79298560000 (Ns96p1913 (Ns96p1925 rfl rfl) rfl)) 

noncomputable def Ns96p1927 := Ns96p1911 (@Enclosure.Real.IsNear.neg qz805 Bool.false 10634999 8388608 257 8388608 (@Ns96p1912 257 8388608 (Ns96p1926 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p1928 := @Enclosure.Real.IsNear.recentre' qz248 Bool.true 1331142 4194304 

noncomputable abbrev qz250 := (@HMul.hMul Real Real Real qz339 qz337 qz592)

noncomputable def Ns96p1929 := @Enclosure.Real.IsNear.cos_image qz250 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 15885925)) qz357) Bool.true 15885925 8388608 

noncomputable def Ns96p1930 := nat_lit 18315225697639274618119045 

noncomputable def Ns96p1931 := nat_lit 151894066924870635004379978078471 

noncomputable def Ns96p1932 := @Enclosure.Real.IsNear.recentre' qz250 Bool.true Ns96p1930 Ns96p603 Ns96p1931 

noncomputable abbrev qz251 := qz592

noncomputable def Ns96p1933 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz251 884279719003555 140737488355328 1 500000000000000 20712027319 

noncomputable abbrev qz593 := (@HSub.hSub Real Real Real qz635 qz804 qz797)

noncomputable abbrev qz252 := qz593

noncomputable def Ns96p1934 := @Enclosure.Real.IsNear.subLit_tf qz252 qz26 16417060023 68719476736 5628609 1099511627776 1 16 

noncomputable abbrev qz594 := qz804

noncomputable abbrev qz253 := qz594

noncomputable def Ns96p1935 := @Enclosure.Real.IsNear.subLit_ff_n qz253 qz243 10702523209 68719476736 2482881 1099511627776 103453 262144 3 1048576 

noncomputable def Ns96p1936 := @Enclosure.Real.IsNear.mulLit_ff qz243 qz243 103453 262144 3 1048576 103453 262144 3 1048576 10702523209 68719476736 

noncomputable def Ns96p1937 := nat_lit 31405858193425354489558855113223432955003663788443260027687746916775458333167941296494140625 

noncomputable def Ns96p1938 := nat_lit 258315278563615647167129540771705203840731934503128185784531662733416616916656494140625 

noncomputable def Ns96p1939 := nat_lit 189562547210181678006002608577347084885429603580031568803978215999050567579479799472494140625 

noncomputable def Ns96p1940 := BSN.cos_dyadic_bound_t 15885925 8388608 4 3 4194304 1210000 Ns96p1937 Ns96p908 Ns96p1938 Ns96p1939 Ns96p911 Ns96p1938 1331142 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 15885925) (BSN.cosEvenQ 8388608) 0 3 Ns96p1937 Ns96p908 Ns96p1938 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 15885925) (BSN.cosOddQ 8388608) 0 3 Ns96p1939 Ns96p911 Ns96p1938 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1941 := @Ns96p1928 336298608 10150215680000 665571 2097152 21018663 634388480000 (@Ns96p1929 271 8388608 Bool.true 1331142 4194304 1 1210000 (@Ns96p1932 Ns96p1418 15885925 8388608 271 8388608 (@Ns96p1933 68719476736 5628609 1099511627776 Ns96p1930 Ns96p603 Ns96p1931 Ns96p1418 RS097to114.d35 (@Ns96p1934 0 1 331392437104 20712027319 68719476736 5628609 1099511627776 (@Ns96p1935 4303633782669312 16417060023 68719476736 5628609 1099511627776 (@Ns96p1936 2482881 1099511627776 (Ns96p1919 rfl rfl) (Ns96p1919 rfl rfl) rfl) (Ns96p1919 rfl rfl) rfl rfl) qz369 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 15885925 8388608) (BSN.cos_neg_of_bound 15885925 8388608 Bool.true 1331142 4194304 1 1210000 (Ns96p1940 rfl rfl)) rfl rfl) 

noncomputable def Ns96p1942 := @Ns96p1903 106685146194330735837 Ns96p180 (Ns96p1904 qz28 (@Enclosure.Real.IsNear.of_eq qz802 (@Inv.inv Real Real.instInv (Real.sqrt qz246)) Bool.false 1542415 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz242 (BSN.t_div_two_pi_nonneg qz241 343569 1000 qz244)) Ns96p1908) rfl) (@Ns96p1909 17592186044416 68820503812557 1330409069608960000 (BSN.correction_mk qz243 (BSN.cos_two_pi_p_ne_zero_mk qz241 343569 1000 7 qz244 rfl rfl (@BSN.floor_sqrt_eq_dec qz241 343569 1000 7 qz244 rfl rfl rfl))) (@Ns96p1910 8388608 665571 2097152 21018663 634388480000 7078346919429 17592186044416 68820503812557 1330409069608960000 Ns96p1927 (Ns96p1941 rfl) rfl)) 

noncomputable def Ns96p1943 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz241) (hardyZApproximantRS₀ qz241) Bool.false 423986679231176376139 73786976294838206464 10696741340281652335837 Ns96p180 (@Eq.refl Real (hardyZApproximantRS₀ qz241)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz241) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz241) qz241 7) (@HMul.hMul Real Real Real qz5 qz798 (Zeta.RiemannSiegel.correction qz243))) Bool.false 423986679231176376139 73786976294838206464 10696741340281652335837 Ns96p180 (BSN.hardyZApproximantRS₀_eq qz241 7 (@BSN.floor_sqrt_eq_dec qz241 343569 1000 7 qz244 rfl rfl rfl)) (@Ns96p1840 423986679231176376139 73786976294838206464 10696741340281652335837 Ns96p180 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz241) qz241 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz241) qz241 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz241) qz241 7)) Bool.false 93921001 16777216 995 524288 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz241) qz241 7) (Ns96p1902 (Ns96p1901 rfl) rfl rfl)) (Ns96p1942 rfl) rfl rfl)) 

theorem RS097to114.d56 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz241) Bool.false 423986679231176376139 73786976294838206464 10696741340281652335837 Ns96p180 := Ns96p1943 

noncomputable def Ns96p1944 := nat_lit 10420813927410580387266560 

noncomputable abbrev qz940 := (Enclosure.sfrac Bool.false 345139 1000)

noncomputable abbrev qz806 := qz940

noncomputable abbrev qz595 := qz806

noncomputable abbrev qz254 := qz595

noncomputable abbrev qz941 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 345139 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz807 := qz941

noncomputable abbrev qz596 := qz807

noncomputable abbrev qz255 := qz596

noncomputable abbrev qz942 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 345139 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz808 := qz942

noncomputable abbrev qz597 := qz808

noncomputable abbrev qz256 := qz597

noncomputable abbrev qz809 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz255 qz9))

noncomputable def Ns96p1945 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz254) qz254 7) (@HMul.hMul Real Real Real qz5 qz809 (Zeta.RiemannSiegel.correction qz256)) 77195959 33554432 63973 33554432 20989663081481409 144115188075855872 5005320768015199161 279007004114856968192000 Ns96p1944 

noncomputable def Ns96p1946 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz254) qz254 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 345139 1000 63 97 67108864 33554432 1125899906842624 Bool.false 34786777980 1304 

noncomputable def Ns96p1947 := Ns96p1946 120242927 57 27397080 8 130587807 57 25364760 8 Bool.true 81860408 47461 Bool.true 72641106 Bool.true 58974504 3537118876014220 1 Bool.false 59264088 Bool.false Bool.false 51671574 Bool.true Bool.true 77195959 

noncomputable def Ns96p1948 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz254) qz254 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 345139 1000 25 23 67108864 33554432 1125899906842624 Bool.false 34786777980 1304 

noncomputable def Ns96p1949 := Ns96p1948 93032624 56 33554424 8 108007536 56 30011992 8 Bool.true 87168844 27898 Bool.false 42232238 Bool.true 66304774 3537118876014220 1 Bool.false 39499376 Bool.true Bool.false 56031667 Bool.false Bool.true 81860408 

noncomputable def Ns96p1950 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz254) qz254 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 345139 1000 177 88 67108864 33554432 1125899906842624 Bool.false 34786777980 1304 

noncomputable def Ns96p1951 := Ns96p1950 46516304 56 47453136 16 73726608 56 38745320 8 Bool.true 67108848 1368 Bool.false 73846132 Bool.false 64386799 3537118876014220 1 Bool.false 59819875 Bool.true Bool.false 38519160 Bool.false Bool.true 87168844 

noncomputable def Ns96p1952 := nat_lit 71028648443525303831182301507893200984198293885938745123 

noncomputable def Ns96p1953 := nat_lit 137024817622246279591464014397849139847865626001408000 

noncomputable def Ns96p1954 := nat_lit 2350789426467019039116769455520000 

noncomputable def Ns96p1955 := nat_lit 4868099439016982884405991228428303680 

noncomputable def Ns96p1956 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz254 345139 1000 476484717284 16000000 690278 4000 2000 Ns96p1954 Ns96p1955 (@Eq.refl Real qz254) rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns96p1957 := nat_lit 22729167501928097225978336482525824314943454043500398439360 

noncomputable abbrev qz810 := (Real.log (Enclosure.sfrac Bool.false 476484717284 16000000))

noncomputable abbrev qz257 := (@HSub.hSub Real Real Real qz342 (@HMul.hMul Real Real Real qz339 (Enclosure.sfrac Bool.false 345139 4000) qz810) (@HMul.hMul Real Real Real qz339 qz344 (@HSub.hSub Real Real Real qz342 qz345 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz346 (@Nat.cast Real Real.instNatCast 690278))))))

noncomputable abbrev qz811 := (Enclosure.sfrac Bool.false 345139 2000)

noncomputable abbrev qz598 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz257 qz811) (@HMul.hMul Real Real Real qz5 qz811 (Real.log Real.pi)))

noncomputable def Ns96p1958 := @Enclosure.Real.IsNear.addLit_ft_p qz598 (Enclosure.sfrac Bool.true Ns96p1954 Ns96p1955) 4669006654586041243027 9007199254740992000 2404514523664456671 123904000000000000000000 Ns96p1954 Ns96p1955 0 1 Ns96p1957 

noncomputable def Ns96p1959 := nat_lit 313331732597709618076689891328000 

noncomputable abbrev qz599 := (@HSub.hSub Real Real Real qz12 qz257 qz811)

noncomputable abbrev qz600 := (@HMul.hMul Real Real Real qz5 qz811 (Real.log Real.pi))

noncomputable def Ns96p1960 := @Enclosure.Real.IsNear.subLit_ff_p qz599 qz600 6448338005790070773139 9007199254740992000 2207119042362983 242000000000000000000 13257051640779 67108864000 345139 33554432000 Ns96p1959 4669006654586041243027 9007199254740992000 

noncomputable def Ns96p1961 := nat_lit 12896676011580141546278000 

noncomputable abbrev qz601 := qz811

noncomputable def Ns96p1962 := @Enclosure.Real.IsNear.subLit_ff_p qz257 qz601 8002705877581096392083 9007199254740992000 2207119042362983 242000000000000000000 345139 2000 0 1 Ns96p1961 6448338005790070773139 9007199254740992000 2207119042362983 242000000000000000000 

noncomputable def Ns96p1963 := nat_lit 18020491604114951945228165220961091584 

noncomputable def Ns96p1964 := nat_lit 12453872868362532908171264 

noncomputable def Ns96p1965 := nat_lit 3563543871805143335349283826278352142184268676204267831536069802655885276910650983420969816853463078334005024264957378648244772156607152658118082560 

noncomputable def Ns96p1966 := nat_lit 105406396361021905817202825428726208957250764241435305041713625541622307815914678408417647207450005435708631079909424983399999770411305860209836032 

noncomputable def Ns96p1967 := nat_lit 97741871515138008256437584157706388318303824927921746435151950561124855078560174529694399100621497840805532366352955462788304808373775237120 

noncomputable def Ns96p1968 := BSN.log_dyadic_bound 214340717284 738628717284 7 6 Ns96p1965 33554432 9680000 Ns96p1966 Ns96p1967 20050171 952969434568 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 214340717284) (BSN.artanhQ 738628717284) 0 6 Ns96p1966 Ns96p1965 Ns96p1967 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns96p1969 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 345139 4000) qz810 345139 4000 0 1 23197145887394497 2251799813685248 6250000847 60500000000000000 8006239734429449300083 9007199254740992000 2157119042332733 242000000000000000000 (Enclosure.Real.IsNear.const Bool.false 345139 4000) (BSN.isNear_log_sfrac 476484717284 16000000 23197145887394497 2251799813685248 6250000847 60500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 476484717284) qz350)) Bool.false Ns96p1964 Ns96p86 1000000135520000 9680000000000000000000 23197145887394497 2251799813685248 6250000847 60500000000000000 (BSN.log_rat_reduce_isNear 476484717284 16000000 14 952969434568 524288000000 20050171 33554432 24973259072661432 36028797018963968 9680000 1000000000000000 rfl rfl rfl rfl (Ns96p1968 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p1970 := BSN.arctan_dyadic_bound_f 1000 690278 1 0 4194304 1210000 0 1 1 0 1 1 6076 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 690278) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 690278) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz602 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 690278)))

noncomputable def Ns96p1971 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz602 884279719003555 562949953421312 1 2000000000000000 6076 4194304 1 1210000 3705517478618498859008 883464212088227 562949953421312 200000000121 242000000000000000 qz17 (Ns96p1970 rfl) rfl rfl 

noncomputable def Ns96p1972 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 345139 4000) qz810) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz602)) 8006239734429449300083 9007199254740992000 2157119042332733 242000000000000000000 883464212088227 2251799813685248 200000000121 968000000000000000 Ns96p1963 8002705877581096392083 9007199254740992000 2207119042362983 242000000000000000000 (Ns96p1969 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz602) 1 4 0 1 883464212088227 562949953421312 200000000121 242000000000000000 883464212088227 2251799813685248 200000000121 968000000000000000 qz353 Ns96p1971 rfl) 

noncomputable def Ns96p1973 := @Ns96p1958 Ns96p1952 Ns96p1953 2404514523664456671 123904000000000000000000 (@Ns96p1960 2404514523664456671 123904000000000000000000 (Ns96p1962 (Ns96p1972 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 345139 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz601 (Real.log Real.pi) 345139 2000 0 1 38410761 33554432 1 16777216 13257051640779 67108864000 345139 33554432000 (Enclosure.Real.IsNear.const Bool.false 345139 2000) RS097to114.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns96p1954 Ns96p1955) 

noncomputable def Ns96p1974 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz254) Bool.false Ns96p1952 Ns96p1953 2404514523664456671 123904000000000000000000 4348347247 8388608 41 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz254) (@HAdd.hAdd Real Real Real qz354 qz598 (Enclosure.sfrac Bool.true Ns96p1954 Ns96p1955)) Bool.false Ns96p1952 Ns96p1953 2404514523664456671 123904000000000000000000 Ns96p1956 (Ns96p1973 rfl rfl)) 

noncomputable def Ns96p1975 := nat_lit 1899699407357435994701824 

noncomputable def Ns96p1976 := nat_lit 140202687408883711345233210945500705342889620938857733301327426790122925743763619840000 

noncomputable def Ns96p1977 := nat_lit 282124429264291861863170246455495773836387849455029874645305995640648505753600000000 

noncomputable def Ns96p1978 := nat_lit 366740741756838961937356133982050092264213903083604967420717527124046612700541747200000 

noncomputable def Ns96p1979 := BSN.sin_dyadic_bound_f 26996352280 17179869184 3 2 8388608 2422364 Ns96p1976 Ns96p99 Ns96p1977 Ns96p1978 Ns96p102 Ns96p1977 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26996352280) qz355 0 2 Ns96p1976 Ns96p99 Ns96p1977 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26996352280) qz356 0 2 Ns96p1978 Ns96p102 Ns96p1977 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1980 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz254) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4348347247) qz357) Bool.false 4348347247 8388608 41 2097152 Bool.true 8388606 8388608 1 1210000 (Ns96p1974 rfl) (Enclosure.sfrac_false_div 4348347247 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4348347247) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns96p1975) qz358) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 82 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q1 4348347247 8388608 226375608064910080 72057594037927936 82 Ns96p1975 Ns96p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388606 8388608 Ns96p1975 Ns96p86 26996352280 17179869184 2422364 2420000 (Ns96p1979 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p1981 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz254) Bool.false Ns96p1952 Ns96p1953 2404514523664456671 123904000000000000000000 34786777980 67108864 1304 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz254) (@HAdd.hAdd Real Real Real qz354 qz598 (Enclosure.sfrac Bool.true Ns96p1954 Ns96p1955)) Bool.false Ns96p1952 Ns96p1953 2404514523664456671 123904000000000000000000 Ns96p1956 (Ns96p1973 rfl rfl)) 

noncomputable def Ns96p1982 := Ns96p1951 27898 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 177 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 59819875 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 88 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 38519160 67108864) (@Eq.refl Real qz254) rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz254) qz254 1) Bool.true 4194303 4194304 3231697 158597120000 67108848 67108864 1368 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz254) qz254 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz254)) Bool.true 4194303 4194304 3231697 158597120000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz254) qz254) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz254)) Bool.true 8388606 8388608 51707152 2537553920000 4194303 4194304 3231697 158597120000 (Ns96p1980 rfl rfl) rfl)) rfl) (Ns96p1981 rfl) RS097to114.d7 

noncomputable def Ns96p1983 := nat_lit 1824831893217872068269002405787505613243671632354245601661103964160 

noncomputable def Ns96p1984 := nat_lit 884345597297825800971101061875582046415697391200631174086066176 

noncomputable def Ns96p1985 := nat_lit 4777889827460706556074386422962335187563038384199175553878180560896 

noncomputable def Ns96p1986 := BSN.sin_dyadic_bound_f 73846132 67108864 3 2 67108864 33554432 Ns96p1983 Ns96p221 Ns96p1984 Ns96p1985 Ns96p224 Ns96p1984 59819875 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 73846132) qz360 0 2 Ns96p1983 Ns96p221 Ns96p1984 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 73846132) (BSN.sinOddQ 67108864) 0 2 Ns96p1985 Ns96p224 Ns96p1984 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1987 := nat_lit 585915738314683906878002505424498063839543562370221133261914596481 

noncomputable def Ns96p1988 := nat_lit 295375640838301943538950082608235244785927683198434222091625601 

noncomputable def Ns96p1989 := nat_lit 1757156463662375116746929616108277721029058831744266531341560538241 

noncomputable def Ns96p1990 := BSN.cos_dyadic_bound_f 64386799 67108864 3 2 67108864 33554432 Ns96p1987 Ns96p108 Ns96p1988 Ns96p1989 Ns96p111 Ns96p1988 38519160 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 64386799) qz359 0 2 Ns96p1987 Ns96p108 Ns96p1988 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 64386799) (BSN.cosOddQ 67108864) 0 2 Ns96p1989 Ns96p111 Ns96p1988 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1991 := nat_lit 195119307474098717818642149965890064777491016827791461717238104320 

noncomputable def Ns96p1992 := nat_lit 10119353601109803064114591662037383731791469673019756294717696 

noncomputable def Ns96p1993 := nat_lit 511010373954904368891482778667021156748339286455221320130194063616 

noncomputable def Ns96p1994 := BSN.sin_dyadic_bound_f 42232238 67108864 3 2 67108864 33554432 Ns96p1991 Ns96p221 Ns96p1992 Ns96p1993 Ns96p224 Ns96p1992 39499376 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 42232238) qz360 0 2 Ns96p1991 Ns96p221 Ns96p1992 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 42232238) (BSN.sinOddQ 67108864) 0 2 Ns96p1993 Ns96p224 Ns96p1992 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1995 := nat_lit 1185816164647007043801239438441235414845011138603840284397301244160 

noncomputable def Ns96p1996 := nat_lit 373558302133108397549897746771072896685372269606794531667026176 

noncomputable def Ns96p1997 := nat_lit 3105104193967279129692927266232272920856586188859265934655947120896 

noncomputable def Ns96p1998 := BSN.sin_dyadic_bound_f 66304774 67108864 3 2 67108864 33554432 Ns96p1995 Ns96p221 Ns96p1996 Ns96p1997 Ns96p224 Ns96p1996 56031667 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 66304774) qz360 0 2 Ns96p1995 Ns96p221 Ns96p1996 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 66304774) (BSN.sinOddQ 67108864) 0 2 Ns96p1997 Ns96p224 Ns96p1996 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p1999 := Ns96p1949 47461 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 25 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 39499376 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 23 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 56031667 67108864) (@Eq.refl Real qz254) rfl rfl (Ns96p1982 RS097to114.d9 RS097to114.d11 RS097to114.d13 RS097to114.d17 (Ns96p1986 rfl rfl) (Ns96p1990 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns96p1981 rfl) RS097to114.d19 RS097to114.d21 RS097to114.d23 RS097to114.d25 RS097to114.d17 (Ns96p1994 rfl rfl) (Ns96p1998 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns96p2000 := nat_lit 1708552153356091863416951351607898548571760172937863685148877799680 

noncomputable def Ns96p2001 := nat_lit 775281790301571164226578372268215305797246699961156052858716416 

noncomputable def Ns96p2002 := nat_lit 4473524231129276146111839079703680992907128720180182065590051553536 

noncomputable def Ns96p2003 := BSN.sin_dyadic_bound_f 72641106 67108864 3 2 67108864 33554432 Ns96p2000 Ns96p221 Ns96p2001 Ns96p2002 Ns96p224 Ns96p2001 59264088 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 72641106) qz360 0 2 Ns96p2000 Ns96p221 Ns96p2001 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 72641106) (BSN.sinOddQ 67108864) 0 2 Ns96p2002 Ns96p224 Ns96p2001 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p2004 := nat_lit 742068792552157815281869745256518621815530224172868033388048547840 

noncomputable def Ns96p2005 := nat_lit 146323599415147814161652176273873041355894114924863745777729536 

noncomputable def Ns96p2006 := nat_lit 1943276599428026895943873324529295834116574377600014117570772729856 

noncomputable def Ns96p2007 := BSN.sin_dyadic_bound_f 58974504 67108864 3 2 67108864 33554432 Ns96p2004 Ns96p221 Ns96p2005 Ns96p2006 Ns96p224 Ns96p2005 51671574 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 58974504) qz360 0 2 Ns96p2004 Ns96p221 Ns96p2005 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 58974504) (BSN.sinOddQ 67108864) 0 2 Ns96p2006 Ns96p224 Ns96p2005 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p2008 := Ns96p1947 63973 BSN.abs_quadSignPos (BSN.cos_quad_nat3 63 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 59264088 67108864) BSN.abs_quadSignNeg qz486 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 51671574 67108864) (@Eq.refl Real qz254) rfl rfl (Ns96p1999 rfl rfl) (Ns96p1981 rfl) RS097to114.d27 RS097to114.d29 RS097to114.d31 RS097to114.d33 RS097to114.d17 (Ns96p2003 rfl rfl) (Ns96p2007 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns96p2009 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz254) qz254 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz254) qz254 7) 77195959 67108864 63973 67108864 77195959 67108864 63973 67108864 10361066227761152 77195959 33554432 63973 33554432 (Ns96p2008 rfl) 

noncomputable def Ns96p2010 := @Enclosure.Real.IsNear.mulLit_tf qz809 (Zeta.RiemannSiegel.correction qz256) 770329 2097152 1 4194304 27247660521 68719476736 3231698274979 66520453480448000 20989663081481409 144115188075855872 

noncomputable abbrev qz812 := (@HPow.hPow Real Real Real qz7 qz255 qz9)

noncomputable def Ns96p2011 := @Enclosure.Real.IsNear.mulLit_tf qz6 qz812 1 1 0 1 770329 2097152 1 4194304 770329 2097152 1 4194304 

noncomputable def Ns96p2012 := @Enclosure.Real.IsNear.sqrt_image qz255 460791282371 8388608000 345139 8388608000 31086148 31086172 4194304 (@Enclosure.Real.IsNear.of_eq qz255 (@HMul.hMul Real Real Real qz5 qz254 qz3) Bool.false 460791282371 8388608000 345139 8388608000 (BSN.t_div_two_pi_mk qz254 345139 1000 (@Eq.refl Real qz254)) (@Enclosure.Real.IsNear.mulLit_ff qz254 qz3 345139 1000 0 1 1335089 8388608 1 8388608 460791282371 8388608000 345139 8388608000 (Enclosure.Real.IsNear.const Bool.false 345139 1000) RS097to114.d36 rfl)) 

noncomputable abbrev qz943 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 345139 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz813 := qz943

noncomputable abbrev qz603 := qz813

noncomputable abbrev qz258 := qz603

noncomputable def Ns96p2013 := @Enclosure.Real.IsNear.sqrt_image qz258 1942885 262144 3 1048576 11418614 11418619 4194304 (@Enclosure.Real.IsNear.recentre' qz258 Bool.false 62172320 8388608 24 8388608 1942885 262144 3 1048576 (Ns96p2012 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns96p2014 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz258) 22837233 8388608 5 8388608 1540657 1540659 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz258) Bool.false 22837233 8388608 5 8388608 22837233 8388608 5 8388608 (Ns96p2013 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns96p2015 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz258)) Bool.false 3081316 8388608 2 8388608 770329 2097152 1 4194304 (Ns96p2014 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz259 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz597))

noncomputable abbrev qz814 := (@HMul.hMul Real Real Real qz863 qz942 qz942)

noncomputable abbrev qz604 := (@HSub.hSub Real Real Real qz635 (@HSub.hSub Real Real Real qz635 qz814 qz808) qz641)

noncomputable abbrev qz260 := (Real.cos (@HMul.hMul Real Real Real qz339 qz337 qz604))

noncomputable def Ns96p2016 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz256) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz259) qz260) Bool.false 27247660521 

noncomputable def Ns96p2017 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz259) qz260 9875919 8388608 221 

noncomputable abbrev qz815 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz259))

noncomputable def Ns96p2018 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz259) (@Neg.neg Real Real.instNeg qz815) Bool.true 9875919 8388608 221 8388608 (BSN.inv_eq_neg_inv_neg qz259) 

noncomputable def Ns96p2019 := @Enclosure.Real.IsNear.recentre' qz815 Bool.false 9875919 8388608 221 8388608 9875919 8388608 

noncomputable def Ns96p2020 := @Enclosure.Real.IsNear.recentre' qz259 Bool.true 7125286 8388608 24038576 1268776960000 3562643 4194304 1502411 79298560000 

noncomputable abbrev qz261 := (@HMul.hMul Real Real Real qz339 qz337 qz597)

noncomputable def Ns96p2021 := @Enclosure.Real.IsNear.cos_image qz261 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21689957) qz357) Bool.false 21689957 8388608 19 1048576 Bool.true 7125286 8388608 1 

noncomputable def Ns96p2022 := nat_lit 80958226230838761861431637 

noncomputable def Ns96p2023 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz256 884279719003555 140737488355328 1 500000000000000 107877 262144 3 1048576 95393443246946502735 36893488147419103232 Ns96p2022 

noncomputable def Ns96p2024 := @Enclosure.Real.IsNear.subLit_ff_p qz258 qz1 1942885 262144 3 1048576 7 1 0 1 107877 107877 262144 3 

noncomputable def Ns96p2025 := @Ns96p2024 1048576 (@Enclosure.Real.IsNear.recentre' qz258 Bool.false 62172320 8388608 24 8388608 1942885 262144 3 1048576 (Ns96p2012 rfl rfl rfl rfl rfl rfl) rfl) qz365 

noncomputable def Ns96p2026 := @Enclosure.Real.IsNear.recentre' qz261 Bool.false 95393443246946502735 36893488147419103232 Ns96p2022 Ns96p487 21689957 8388608 19 1048576 (@Ns96p2023 Ns96p487 RS097to114.d35 (Ns96p2025 rfl rfl) rfl) 

noncomputable def Ns96p2027 := nat_lit 1226875995594057385508864 

noncomputable def Ns96p2028 := nat_lit 24349888845143639794960303925742788741616075290312550708925942251045619724027224080640 

noncomputable def Ns96p2029 := nat_lit 8538212323856768191728964054094760039755286381279453046051061550894433991173816576 

noncomputable def Ns96p2030 := nat_lit 63759694631613764695442758625619721854644402915725085123207670843560889241228448317696 

noncomputable def Ns96p2031 := BSN.sin_dyadic_bound_f 17434956526 17179869184 3 2 8388608 2422364 Ns96p2028 Ns96p99 Ns96p2029 Ns96p2030 Ns96p102 Ns96p2029 7125286 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 17434956526) qz355 0 2 Ns96p2028 Ns96p99 Ns96p2029 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 17434956526) qz356 0 2 Ns96p2030 Ns96p102 Ns96p2029 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p2032 := @Ns96p2021 1210000 (Ns96p2026 rfl) (Enclosure.sfrac_false_div 21689957 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21689957) qz357) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns96p2027) qz358) 226375608064910080 72057594037927936 Bool.false 7125286 8388608 0 1000000000000000 2420000 1210000 (BSN.sin_reduce_arg_pos_rat_q1 21689957 8388608 226375608064910080 72057594037927936 0 Ns96p2027 Ns96p86 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 7125286 8388608 Ns96p2027 Ns96p86 17434956526 17179869184 2422364 2420000 (Ns96p2031 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns96p2033 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz259) 3562643 4194304 1502411 79298560000 4937849 4938070 4194304 (@Enclosure.Real.IsNear.neg qz259 Bool.true 3562643 4194304 1502411 79298560000 (Ns96p2020 (Ns96p2032 rfl rfl) rfl)) 

noncomputable def Ns96p2034 := Ns96p2018 (@Enclosure.Real.IsNear.neg qz815 Bool.false 9875919 8388608 221 8388608 (@Ns96p2019 221 8388608 (Ns96p2033 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns96p2035 := @Enclosure.Real.IsNear.recentre' qz260 Bool.true 1412608 4194304 

noncomputable abbrev qz262 := (@HMul.hMul Real Real Real qz339 qz337 qz604)

noncomputable def Ns96p2036 := @Enclosure.Real.IsNear.cos_image qz262 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8029173)) qz434) Bool.true 8029173 4194304 

noncomputable def Ns96p2037 := nat_lit 18514012783013034570157525 

noncomputable def Ns96p2038 := nat_lit 30951868093506438401499831012571 

noncomputable def Ns96p2039 := @Enclosure.Real.IsNear.recentre' qz262 Bool.true Ns96p2037 Ns96p603 Ns96p2038 

noncomputable abbrev qz263 := qz604

noncomputable def Ns96p2040 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz263 884279719003555 140737488355328 1 500000000000000 20936828455 

noncomputable abbrev qz605 := (@HSub.hSub Real Real Real qz635 qz814 qz808)

noncomputable abbrev qz264 := qz605

noncomputable def Ns96p2041 := @Enclosure.Real.IsNear.subLit_tf qz264 qz26 16641861159 68719476736 5734785 1099511627776 1 16 

noncomputable abbrev qz606 := qz814

noncomputable abbrev qz265 := qz606

noncomputable def Ns96p2042 := @Enclosure.Real.IsNear.subLit_ff_n qz265 qz256 11637447129 68719476736 2589057 1099511627776 107877 262144 3 1048576 

noncomputable def Ns96p2043 := @Enclosure.Real.IsNear.mulLit_ff qz256 qz256 107877 262144 3 1048576 107877 262144 3 1048576 11637447129 68719476736 

noncomputable def Ns96p2044 := nat_lit 8008475017433376632216513600956311577547497807508852170606738663468229153386418175674001 

noncomputable def Ns96p2045 := nat_lit 71787658163710919337856516985892858319620779797515028728307301674612933873055499921 

noncomputable def Ns96p2046 := nat_lit 48327533598764926879483001108845142448230125071711633814562419864373609019273890365376145 

noncomputable def Ns96p2047 := BSN.cos_dyadic_bound_t 8029173 4194304 4 3 4194304 1210000 Ns96p2044 Ns96p1217 Ns96p2045 Ns96p2046 Ns96p1220 Ns96p2045 1412608 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 8029173) (BSN.cosEvenQ 4194304) 0 3 Ns96p2044 Ns96p1217 Ns96p2045 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 8029173) (BSN.cosOddQ 4194304) 0 3 Ns96p2046 Ns96p1220 Ns96p2045 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns96p2048 := @Ns96p2035 85587152 2537553920000 2759 8192 5349197 158597120000 (@Ns96p2036 69 2097152 Bool.true 1412608 4194304 1 1210000 (@Ns96p2039 Ns96p606 8029173 4194304 69 2097152 (@Ns96p2040 68719476736 5734785 1099511627776 Ns96p2037 Ns96p603 Ns96p2038 Ns96p606 RS097to114.d35 (@Ns96p2041 0 1 334989255280 20936828455 68719476736 5734785 1099511627776 (@Ns96p2042 4362564051664896 16641861159 68719476736 5734785 1099511627776 (@Ns96p2043 2589057 1099511627776 (Ns96p2025 rfl rfl) (Ns96p2025 rfl rfl) rfl) (Ns96p2025 rfl rfl) rfl rfl) qz369 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 8029173 4194304) (BSN.cos_neg_of_bound 8029173 4194304 Bool.true 1412608 4194304 1 1210000 (Ns96p2047 rfl rfl)) rfl rfl) 

noncomputable def Ns96p2049 := @Ns96p2010 5005320768015199161 279007004114856968192000 (Ns96p2011 qz28 (@Enclosure.Real.IsNear.of_eq qz812 (@Inv.inv Real Real.instInv (Real.sqrt qz258)) Bool.false 770329 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz255 (BSN.t_div_two_pi_nonneg qz254 345139 1000 (@Eq.refl Real qz254))) Ns96p2015) rfl) (@Ns96p2016 68719476736 3231698274979 66520453480448000 (BSN.correction_mk qz256 (BSN.cos_two_pi_p_ne_zero_mk qz254 345139 1000 7 (@Eq.refl Real qz254) rfl rfl (@BSN.floor_sqrt_eq_dec qz254 345139 1000 7 (@Eq.refl Real qz254) rfl rfl rfl))) (@Ns96p2017 8388608 2759 8192 5349197 158597120000 27247660521 68719476736 3231698274979 66520453480448000 Ns96p2034 (Ns96p2048 rfl) rfl)) 

noncomputable def Ns96p2050 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz254) (hardyZApproximantRS₀ qz254) Bool.true 310564456206875455 144115188075855872 536944442081102687161 279007004114856968192000 (@Eq.refl Real (hardyZApproximantRS₀ qz254)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz254) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz254) qz254 7) (@HMul.hMul Real Real Real qz5 qz809 (Zeta.RiemannSiegel.correction qz256))) Bool.true 310564456206875455 144115188075855872 536944442081102687161 279007004114856968192000 (BSN.hardyZApproximantRS₀_eq qz254 7 (@BSN.floor_sqrt_eq_dec qz254 345139 1000 7 (@Eq.refl Real qz254) rfl rfl rfl)) (@Ns96p1945 310564456206875455 144115188075855872 536944442081102687161 279007004114856968192000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz254) qz254 7) (@HAdd.hAdd Real Real Real qz354 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz254) qz254 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz254) qz254 7)) Bool.true 77195959 33554432 63973 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz254) qz254 7) (Ns96p2009 (Ns96p2008 rfl) rfl rfl)) (Ns96p2049 rfl) rfl rfl)) 

theorem RS097to114.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz254) Bool.true 310564456206875455 144115188075855872 536944442081102687161 279007004114856968192000 := Ns96p2050 

noncomputable def RS097to114.d58 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz266 := (RS097to114.d3 qz338 qz370 (@Enclosure.dec_le_dec qz338 qz370 316604 1000 318206 1000 (@Eq.refl Real qz338) qz373 rfl rfl rfl))

noncomputable abbrev qz816 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz266)

noncomputable def Ns96p2051 := @Enclosure.Real.IsNear.of_eq qz816 (hardyZApproximantRS₀ qz4) Bool.true 38269456319305304309 9223372036854775808 2462572192971076629899 Ns96p64 

noncomputable abbrev qz267 := (@Enclosure.dec_le_dec qz338 qz370 316604 1000 318206 1000 (@Eq.refl Real qz338) qz373 rfl rfl rfl)

noncomputable def Ns96p2052 := @Enclosure.Real.IsNear.neg_val qz816 38269456319305304309 9223372036854775808 2462572192971076629899 Ns96p64 (Ns96p2051 (RS097to114.d4 qz4 qz29 qz267) RS097to114.d37) rfl 

noncomputable abbrev qz817 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz266)

noncomputable def Ns96p2053 := @Enclosure.Real.IsNear.of_eq qz817 (hardyZApproximantRS₀ qz29) Bool.false 1431632976431146861 1152921504606846976 9908546347165736666391 Ns96p180 

noncomputable def Ns96p2054 := @Enclosure.Real.IsNear.pos_val qz817 1431632976431146861 1152921504606846976 9908546347165736666391 Ns96p180 (Ns96p2053 (RS097to114.d38 qz4 qz29 qz267) RS097to114.d39) rfl 

noncomputable def Ns96p2055 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz816 qz4 qz4 316604 1000 316604 1000 

noncomputable def Ns96p2056 := @Enclosure.norm_gt_of_isNear qz816 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 38269456319305304309 9223372036854775808 2462572192971076629899 

noncomputable def Ns96p2057 := @Ns96p2056 Ns96p64 30948275 268435456 2213 1342177280 (Ns96p2051 (RS097to114.d4 qz4 qz29 qz267) RS097to114.d37) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2058 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz817 qz4 qz29 316604 1000 318206 1000 

noncomputable def Ns96p2059 := @Enclosure.norm_gt_of_isNear qz817 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1431632976431146861 1152921504606846976 9908546347165736666391 

noncomputable def Ns96p2060 := @Ns96p2059 Ns96p180 30948275 268435456 2213 1342177280 (Ns96p2053 (RS097to114.d38 qz4 qz29 qz267) RS097to114.d39) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2061 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz266 (@BSN.thirtyTwoPi_le_dec qz4 316604 1000 qz11 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz816 qz817 (Ns96p2052 rfl rfl) (Ns96p2054 rfl rfl)) (Ns96p2055 qz11 qz11 rfl rfl rfl rfl (Ns96p2057 rfl)) (Ns96p2058 qz11 qz32 rfl rfl rfl rfl (Ns96p2060 rfl)) 

noncomputable abbrev qz268 := (RS097to114.d3 qz370 qz388 (@Enclosure.dec_le_dec qz370 qz388 318206 1000 319806 1000 qz373 qz391 rfl rfl rfl))

noncomputable abbrev qz818 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz268)

noncomputable def Ns96p2062 := @Enclosure.Real.IsNear.of_eq qz818 (hardyZApproximantRS₀ qz29) Bool.false 1431632976431146861 1152921504606846976 9908546347165736666391 Ns96p180 

noncomputable abbrev qz269 := (@Enclosure.dec_le_dec qz370 qz388 318206 1000 319806 1000 qz373 qz391 rfl rfl rfl)

noncomputable def Ns96p2063 := @Enclosure.Real.IsNear.pos_val qz818 1431632976431146861 1152921504606846976 9908546347165736666391 Ns96p180 (Ns96p2062 (RS097to114.d4 qz29 qz48 qz269) RS097to114.d39) rfl 

noncomputable abbrev qz819 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz268)

noncomputable def Ns96p2064 := @Enclosure.Real.IsNear.of_eq qz819 (hardyZApproximantRS₀ qz48) Bool.true 245833585414464500293 73786976294838206464 1246206337137489310773 697517510287142420480000 

noncomputable def Ns96p2065 := @Enclosure.Real.IsNear.neg_val qz819 245833585414464500293 73786976294838206464 1246206337137489310773 697517510287142420480000 (Ns96p2064 (RS097to114.d38 qz29 qz48 qz269) RS097to114.d41) rfl 

noncomputable def Ns96p2066 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz818 qz4 qz29 316604 1000 318206 1000 

noncomputable def Ns96p2067 := @Enclosure.norm_gt_of_isNear qz818 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1431632976431146861 1152921504606846976 9908546347165736666391 

noncomputable def Ns96p2068 := @Ns96p2067 Ns96p180 30948275 268435456 2213 1342177280 (Ns96p2062 (RS097to114.d4 qz29 qz48 qz269) RS097to114.d39) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2069 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz819 qz4 qz48 316604 1000 319806 1000 

noncomputable def Ns96p2070 := @Enclosure.norm_gt_of_isNear qz819 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 245833585414464500293 73786976294838206464 1246206337137489310773 

noncomputable def Ns96p2071 := @Ns96p2070 697517510287142420480000 30948275 268435456 2213 1342177280 (Ns96p2064 (RS097to114.d38 qz29 qz48 qz269) RS097to114.d41) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2072 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz268 (@BSN.thirtyTwoPi_le_dec qz29 318206 1000 qz32 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz818 qz819 (Ns96p2063 rfl rfl) (Ns96p2065 rfl rfl)) (Ns96p2066 qz11 qz32 rfl rfl rfl rfl (Ns96p2068 rfl)) (Ns96p2069 qz11 qz51 rfl rfl rfl rfl (Ns96p2071 rfl)) 

noncomputable abbrev qz270 := (RS097to114.d3 qz388 qz401 (@Enclosure.dec_le_dec qz388 qz401 319806 1000 321404 1000 qz391 qz404 rfl rfl rfl))

noncomputable abbrev qz820 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz270)

noncomputable def Ns96p2073 := @Enclosure.Real.IsNear.of_eq qz820 (hardyZApproximantRS₀ qz48) Bool.true 245833585414464500293 73786976294838206464 1246206337137489310773 697517510287142420480000 

noncomputable abbrev qz271 := (@Enclosure.dec_le_dec qz388 qz401 319806 1000 321404 1000 qz391 qz404 rfl rfl rfl)

noncomputable def Ns96p2074 := @Enclosure.Real.IsNear.neg_val qz820 245833585414464500293 73786976294838206464 1246206337137489310773 697517510287142420480000 (Ns96p2073 (RS097to114.d4 qz48 qz61 qz271) RS097to114.d41) rfl 

noncomputable abbrev qz821 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz270)

noncomputable def Ns96p2075 := @Enclosure.Real.IsNear.of_eq qz821 (hardyZApproximantRS₀ qz61) Bool.false 559611893399946563 1152921504606846976 91274716872929395263 50728546202701266944000 

noncomputable def Ns96p2076 := @Enclosure.Real.IsNear.pos_val qz821 559611893399946563 1152921504606846976 91274716872929395263 50728546202701266944000 (Ns96p2075 (RS097to114.d38 qz48 qz61 qz271) RS097to114.d42) rfl 

noncomputable def Ns96p2077 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz820 qz4 qz48 316604 1000 319806 1000 

noncomputable def Ns96p2078 := @Enclosure.norm_gt_of_isNear qz820 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 245833585414464500293 73786976294838206464 1246206337137489310773 

noncomputable def Ns96p2079 := @Ns96p2078 697517510287142420480000 30948275 268435456 2213 1342177280 (Ns96p2073 (RS097to114.d4 qz48 qz61 qz271) RS097to114.d41) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2080 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz821 qz4 qz61 316604 1000 321404 1000 

noncomputable def Ns96p2081 := @Enclosure.norm_gt_of_isNear qz821 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 559611893399946563 1152921504606846976 91274716872929395263 

noncomputable def Ns96p2082 := @Ns96p2081 50728546202701266944000 30948275 268435456 2213 1342177280 (Ns96p2075 (RS097to114.d38 qz48 qz61 qz271) RS097to114.d42) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2083 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz270 (@BSN.thirtyTwoPi_le_dec qz48 319806 1000 qz51 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz820 qz821 (Ns96p2074 rfl rfl) (Ns96p2076 rfl rfl)) (Ns96p2077 qz11 qz51 rfl rfl rfl rfl (Ns96p2079 rfl)) (Ns96p2080 qz11 qz64 rfl rfl rfl rfl (Ns96p2082 rfl)) 

noncomputable abbrev qz272 := (RS097to114.d3 qz401 qz413 (@Enclosure.dec_le_dec qz401 qz413 321404 1000 323000 1000 qz404 qz416 rfl rfl rfl))

noncomputable abbrev qz822 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz272)

noncomputable def Ns96p2084 := @Enclosure.Real.IsNear.of_eq qz822 (hardyZApproximantRS₀ qz61) Bool.false 559611893399946563 1152921504606846976 91274716872929395263 50728546202701266944000 

noncomputable abbrev qz273 := (@Enclosure.dec_le_dec qz401 qz413 321404 1000 323000 1000 qz404 qz416 rfl rfl rfl)

noncomputable def Ns96p2085 := @Enclosure.Real.IsNear.pos_val qz822 559611893399946563 1152921504606846976 91274716872929395263 50728546202701266944000 (Ns96p2084 (RS097to114.d4 qz61 qz74 qz273) RS097to114.d42) rfl 

noncomputable abbrev qz823 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz272)

noncomputable def Ns96p2086 := @Enclosure.Real.IsNear.of_eq qz823 (hardyZApproximantRS₀ qz74) Bool.true 130396609153378093971 147573952589676412928 4045920995766624861063 Ns96p515 

noncomputable def Ns96p2087 := @Enclosure.Real.IsNear.neg_val qz823 130396609153378093971 147573952589676412928 4045920995766624861063 Ns96p515 (Ns96p2086 (RS097to114.d38 qz61 qz74 qz273) RS097to114.d43) rfl 

noncomputable def Ns96p2088 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz822 qz4 qz61 316604 1000 321404 1000 

noncomputable def Ns96p2089 := @Enclosure.norm_gt_of_isNear qz822 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 559611893399946563 1152921504606846976 91274716872929395263 

noncomputable def Ns96p2090 := @Ns96p2089 50728546202701266944000 30948275 268435456 2213 1342177280 (Ns96p2084 (RS097to114.d4 qz61 qz74 qz273) RS097to114.d42) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2091 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz823 qz4 qz74 316604 1000 323000 1000 

noncomputable def Ns96p2092 := @Enclosure.norm_gt_of_isNear qz823 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 130396609153378093971 147573952589676412928 4045920995766624861063 

noncomputable def Ns96p2093 := @Ns96p2092 Ns96p515 30948275 268435456 2213 1342177280 (Ns96p2086 (RS097to114.d38 qz61 qz74 qz273) RS097to114.d43) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2094 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz272 (@BSN.thirtyTwoPi_le_dec qz61 321404 1000 qz64 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz822 qz823 (Ns96p2085 rfl rfl) (Ns96p2087 rfl rfl)) (Ns96p2088 qz11 qz64 rfl rfl rfl rfl (Ns96p2090 rfl)) (Ns96p2091 qz11 qz77 rfl rfl rfl rfl (Ns96p2093 rfl)) 

noncomputable abbrev qz274 := (RS097to114.d3 qz413 qz426 (@Enclosure.dec_le_dec qz413 qz426 323000 1000 324594 1000 qz416 qz429 rfl rfl rfl))

noncomputable abbrev qz824 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz274)

noncomputable def Ns96p2095 := @Enclosure.Real.IsNear.of_eq qz824 (hardyZApproximantRS₀ qz74) Bool.true 130396609153378093971 147573952589676412928 4045920995766624861063 Ns96p515 

noncomputable abbrev qz275 := (@Enclosure.dec_le_dec qz413 qz426 323000 1000 324594 1000 qz416 qz429 rfl rfl rfl)

noncomputable def Ns96p2096 := @Enclosure.Real.IsNear.neg_val qz824 130396609153378093971 147573952589676412928 4045920995766624861063 Ns96p515 (Ns96p2095 (RS097to114.d4 qz74 qz87 qz275) RS097to114.d43) rfl 

noncomputable abbrev qz825 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz274)

noncomputable def Ns96p2097 := @Enclosure.Real.IsNear.of_eq qz825 (hardyZApproximantRS₀ qz87) Bool.false 39341150402698687171 36893488147419103232 1019925397577889514353 558014008229713936384000 

noncomputable def Ns96p2098 := @Enclosure.Real.IsNear.pos_val qz825 39341150402698687171 36893488147419103232 1019925397577889514353 558014008229713936384000 (Ns96p2097 (RS097to114.d38 qz74 qz87 qz275) RS097to114.d44) rfl 

noncomputable def Ns96p2099 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz824 qz4 qz74 316604 1000 323000 1000 

noncomputable def Ns96p2100 := @Enclosure.norm_gt_of_isNear qz824 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 130396609153378093971 147573952589676412928 4045920995766624861063 

noncomputable def Ns96p2101 := @Ns96p2100 Ns96p515 30948275 268435456 2213 1342177280 (Ns96p2095 (RS097to114.d4 qz74 qz87 qz275) RS097to114.d43) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2102 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz825 qz4 qz87 316604 1000 324594 1000 

noncomputable def Ns96p2103 := @Enclosure.norm_gt_of_isNear qz825 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 39341150402698687171 36893488147419103232 1019925397577889514353 

noncomputable def Ns96p2104 := @Ns96p2103 558014008229713936384000 30948275 268435456 2213 1342177280 (Ns96p2097 (RS097to114.d38 qz74 qz87 qz275) RS097to114.d44) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2105 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz274 (@BSN.thirtyTwoPi_le_dec qz74 323000 1000 qz77 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz824 qz825 (Ns96p2096 rfl rfl) (Ns96p2098 rfl rfl)) (Ns96p2099 qz11 qz77 rfl rfl rfl rfl (Ns96p2101 rfl)) (Ns96p2102 qz11 qz90 rfl rfl rfl rfl (Ns96p2104 rfl)) 

noncomputable abbrev qz276 := (RS097to114.d3 qz426 qz439 (@Enclosure.dec_le_dec qz426 qz439 324594 1000 326185 1000 qz429 qz442 rfl rfl rfl))

noncomputable abbrev qz826 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz276)

noncomputable def Ns96p2106 := @Enclosure.Real.IsNear.of_eq qz826 (hardyZApproximantRS₀ qz87) Bool.false 39341150402698687171 36893488147419103232 1019925397577889514353 558014008229713936384000 

noncomputable abbrev qz277 := (@Enclosure.dec_le_dec qz426 qz439 324594 1000 326185 1000 qz429 qz442 rfl rfl rfl)

noncomputable def Ns96p2107 := @Enclosure.Real.IsNear.pos_val qz826 39341150402698687171 36893488147419103232 1019925397577889514353 558014008229713936384000 (Ns96p2106 (RS097to114.d4 qz87 qz100 qz277) RS097to114.d44) rfl 

noncomputable abbrev qz827 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz276)

noncomputable def Ns96p2108 := @Enclosure.Real.IsNear.of_eq qz827 (hardyZApproximantRS₀ qz100) Bool.true 111175073657433430073 18446744073709551616 10320402940147642209741 Ns96p180 

noncomputable def Ns96p2109 := @Enclosure.Real.IsNear.neg_val qz827 111175073657433430073 18446744073709551616 10320402940147642209741 Ns96p180 (Ns96p2108 (RS097to114.d38 qz87 qz100 qz277) RS097to114.d45) rfl 

noncomputable def Ns96p2110 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz826 qz4 qz87 316604 1000 324594 1000 

noncomputable def Ns96p2111 := @Enclosure.norm_gt_of_isNear qz826 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 39341150402698687171 36893488147419103232 1019925397577889514353 

noncomputable def Ns96p2112 := @Ns96p2111 558014008229713936384000 30948275 268435456 2213 1342177280 (Ns96p2106 (RS097to114.d4 qz87 qz100 qz277) RS097to114.d44) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2113 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz827 qz4 qz100 316604 1000 326185 1000 

noncomputable def Ns96p2114 := @Enclosure.norm_gt_of_isNear qz827 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 111175073657433430073 18446744073709551616 10320402940147642209741 

noncomputable def Ns96p2115 := @Ns96p2114 Ns96p180 30948275 268435456 2213 1342177280 (Ns96p2108 (RS097to114.d38 qz87 qz100 qz277) RS097to114.d45) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2116 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz276 (@BSN.thirtyTwoPi_le_dec qz87 324594 1000 qz90 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz826 qz827 (Ns96p2107 rfl rfl) (Ns96p2109 rfl rfl)) (Ns96p2110 qz11 qz90 rfl rfl rfl rfl (Ns96p2112 rfl)) (Ns96p2113 qz11 qz103 rfl rfl rfl rfl (Ns96p2115 rfl)) 

noncomputable abbrev qz607 := (@Enclosure.dec_le_dec qz682 qz690 326185 1000 327775 1000 (@Eq.refl Real qz682) (@Eq.refl Real qz690) rfl rfl rfl)

noncomputable abbrev qz278 := (RS097to114.d3 qz439 qz451 qz607)

noncomputable abbrev qz828 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz278)

noncomputable def Ns96p2117 := @Enclosure.Real.IsNear.of_eq qz828 (hardyZApproximantRS₀ qz100) Bool.true 111175073657433430073 18446744073709551616 10320402940147642209741 Ns96p180 

noncomputable abbrev qz279 := qz607

noncomputable def Ns96p2118 := @Enclosure.Real.IsNear.neg_val qz828 111175073657433430073 18446744073709551616 10320402940147642209741 Ns96p180 (Ns96p2117 (RS097to114.d4 qz100 qz113 qz279) RS097to114.d45) rfl 

noncomputable abbrev qz829 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz278)

noncomputable def Ns96p2119 := @Enclosure.Real.IsNear.of_eq qz829 (hardyZApproximantRS₀ qz113) Bool.false 3260941185584840737 2305843009213693952 131710201900582138533 69751751028714242048000 

noncomputable def Ns96p2120 := @Enclosure.Real.IsNear.pos_val qz829 3260941185584840737 2305843009213693952 131710201900582138533 69751751028714242048000 (Ns96p2119 (RS097to114.d38 qz100 qz113 qz279) RS097to114.d46) rfl 

noncomputable def Ns96p2121 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz828 qz4 qz100 316604 1000 326185 1000 

noncomputable def Ns96p2122 := @Enclosure.norm_gt_of_isNear qz828 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 111175073657433430073 18446744073709551616 10320402940147642209741 

noncomputable def Ns96p2123 := @Ns96p2122 Ns96p180 30948275 268435456 2213 1342177280 (Ns96p2117 (RS097to114.d4 qz100 qz113 qz279) RS097to114.d45) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2124 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz829 qz4 qz113 316604 1000 327775 1000 

noncomputable def Ns96p2125 := @Enclosure.norm_gt_of_isNear qz829 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 3260941185584840737 2305843009213693952 131710201900582138533 

noncomputable def Ns96p2126 := @Ns96p2125 69751751028714242048000 30948275 268435456 2213 1342177280 (Ns96p2119 (RS097to114.d38 qz100 qz113 qz279) RS097to114.d46) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2127 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz278 (@BSN.thirtyTwoPi_le_dec qz100 326185 1000 qz103 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz828 qz829 (Ns96p2118 rfl rfl) (Ns96p2120 rfl rfl)) (Ns96p2121 qz11 qz103 rfl rfl rfl rfl (Ns96p2123 rfl)) (Ns96p2124 qz11 qz116 rfl rfl rfl rfl (Ns96p2126 rfl)) 

noncomputable abbrev qz608 := (@Enclosure.dec_le_dec qz690 qz699 327775 1000 329363 1000 (@Eq.refl Real qz690) qz703 rfl rfl rfl)

noncomputable abbrev qz280 := (RS097to114.d3 qz451 qz464 qz608)

noncomputable abbrev qz830 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz280)

noncomputable def Ns96p2128 := @Enclosure.Real.IsNear.of_eq qz830 (hardyZApproximantRS₀ qz113) Bool.false 3260941185584840737 2305843009213693952 131710201900582138533 69751751028714242048000 

noncomputable abbrev qz281 := qz608

noncomputable def Ns96p2129 := @Enclosure.Real.IsNear.pos_val qz830 3260941185584840737 2305843009213693952 131710201900582138533 69751751028714242048000 (Ns96p2128 (RS097to114.d4 qz113 qz125 qz281) RS097to114.d46) rfl 

noncomputable abbrev qz831 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz280)

noncomputable def Ns96p2130 := @Enclosure.Real.IsNear.of_eq qz831 (hardyZApproximantRS₀ qz125) Bool.true 37728166222647521003 73786976294838206464 1036416308835791680877 507285462027012669440000 

noncomputable def Ns96p2131 := @Enclosure.Real.IsNear.neg_val qz831 37728166222647521003 73786976294838206464 1036416308835791680877 507285462027012669440000 (Ns96p2130 (RS097to114.d38 qz113 qz125 qz281) RS097to114.d47) rfl 

noncomputable def Ns96p2132 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz830 qz4 qz113 316604 1000 327775 1000 

noncomputable def Ns96p2133 := @Enclosure.norm_gt_of_isNear qz830 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 3260941185584840737 2305843009213693952 131710201900582138533 

noncomputable def Ns96p2134 := @Ns96p2133 69751751028714242048000 30948275 268435456 2213 1342177280 (Ns96p2128 (RS097to114.d4 qz113 qz125 qz281) RS097to114.d46) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2135 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz831 qz4 qz125 316604 1000 329363 1000 

noncomputable def Ns96p2136 := @Enclosure.norm_gt_of_isNear qz831 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 37728166222647521003 73786976294838206464 1036416308835791680877 

noncomputable def Ns96p2137 := @Ns96p2136 507285462027012669440000 30948275 268435456 2213 1342177280 (Ns96p2130 (RS097to114.d38 qz113 qz125 qz281) RS097to114.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2138 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz280 (@BSN.thirtyTwoPi_le_dec qz113 327775 1000 qz116 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz830 qz831 (Ns96p2129 rfl rfl) (Ns96p2131 rfl rfl)) (Ns96p2132 qz11 qz116 rfl rfl rfl rfl (Ns96p2134 rfl)) (Ns96p2135 qz11 qz128 rfl rfl rfl rfl (Ns96p2137 rfl)) 

noncomputable abbrev qz609 := (@Enclosure.dec_le_dec qz699 qz710 329363 1000 330949 1000 qz703 qz714 rfl rfl rfl)

noncomputable abbrev qz282 := (RS097to114.d3 qz464 qz477 qz609)

noncomputable abbrev qz832 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz282)

noncomputable def Ns96p2139 := @Enclosure.Real.IsNear.of_eq qz832 (hardyZApproximantRS₀ qz125) Bool.true 37728166222647521003 73786976294838206464 1036416308835791680877 507285462027012669440000 

noncomputable abbrev qz283 := qz609

noncomputable def Ns96p2140 := @Enclosure.Real.IsNear.neg_val qz832 37728166222647521003 73786976294838206464 1036416308835791680877 507285462027012669440000 (Ns96p2139 (RS097to114.d4 qz125 qz137 qz283) RS097to114.d47) rfl 

noncomputable abbrev qz833 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz282)

noncomputable def Ns96p2141 := @Enclosure.Real.IsNear.of_eq qz833 (hardyZApproximantRS₀ qz137) Bool.false 24446300811684375831 18446744073709551616 107610839220412858687 50728546202701266944000 

noncomputable def Ns96p2142 := @Enclosure.Real.IsNear.pos_val qz833 24446300811684375831 18446744073709551616 107610839220412858687 50728546202701266944000 (Ns96p2141 (RS097to114.d38 qz125 qz137 qz283) RS097to114.d48) rfl 

noncomputable def Ns96p2143 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz832 qz4 qz125 316604 1000 329363 1000 

noncomputable def Ns96p2144 := @Enclosure.norm_gt_of_isNear qz832 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 37728166222647521003 73786976294838206464 1036416308835791680877 

noncomputable def Ns96p2145 := @Ns96p2144 507285462027012669440000 30948275 268435456 2213 1342177280 (Ns96p2139 (RS097to114.d4 qz125 qz137 qz283) RS097to114.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2146 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz833 qz4 qz137 316604 1000 330949 1000 

noncomputable def Ns96p2147 := @Enclosure.norm_gt_of_isNear qz833 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 24446300811684375831 18446744073709551616 107610839220412858687 

noncomputable def Ns96p2148 := @Ns96p2147 50728546202701266944000 30948275 268435456 2213 1342177280 (Ns96p2141 (RS097to114.d38 qz125 qz137 qz283) RS097to114.d48) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2149 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz282 (@BSN.thirtyTwoPi_le_dec qz125 329363 1000 qz128 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz832 qz833 (Ns96p2140 rfl rfl) (Ns96p2142 rfl rfl)) (Ns96p2143 qz11 qz128 rfl rfl rfl rfl (Ns96p2145 rfl)) (Ns96p2146 qz11 qz140 rfl rfl rfl rfl (Ns96p2148 rfl)) 

noncomputable abbrev qz834 := (@Enclosure.dec_le_dec qz901 qz905 330949 1000 332533 1000 (@Eq.refl Real qz901) qz908 rfl rfl rfl)

noncomputable abbrev qz610 := qz834

noncomputable abbrev qz284 := (RS097to114.d3 qz477 qz491 qz610)

noncomputable abbrev qz835 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz284)

noncomputable def Ns96p2150 := @Enclosure.Real.IsNear.of_eq qz835 (hardyZApproximantRS₀ qz137) Bool.false 24446300811684375831 18446744073709551616 107610839220412858687 50728546202701266944000 

noncomputable abbrev qz285 := qz610

noncomputable def Ns96p2151 := @Enclosure.Real.IsNear.pos_val qz835 24446300811684375831 18446744073709551616 107610839220412858687 50728546202701266944000 (Ns96p2150 (RS097to114.d4 qz137 qz150 qz285) RS097to114.d48) rfl 

noncomputable abbrev qz836 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz284)

noncomputable def Ns96p2152 := @Enclosure.Real.IsNear.of_eq qz836 (hardyZApproximantRS₀ qz150) Bool.true 26009986968686582821 9223372036854775808 10754331801644631604941 Ns96p180 

noncomputable def Ns96p2153 := @Enclosure.Real.IsNear.neg_val qz836 26009986968686582821 9223372036854775808 10754331801644631604941 Ns96p180 (Ns96p2152 (RS097to114.d38 qz137 qz150 qz285) RS097to114.d49) rfl 

noncomputable def Ns96p2154 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz835 qz4 qz137 316604 1000 330949 1000 

noncomputable def Ns96p2155 := @Enclosure.norm_gt_of_isNear qz835 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 24446300811684375831 18446744073709551616 107610839220412858687 

noncomputable def Ns96p2156 := @Ns96p2155 50728546202701266944000 30948275 268435456 2213 1342177280 (Ns96p2150 (RS097to114.d4 qz137 qz150 qz285) RS097to114.d48) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2157 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz836 qz4 qz150 316604 1000 332533 1000 

noncomputable def Ns96p2158 := @Enclosure.norm_gt_of_isNear qz836 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 26009986968686582821 9223372036854775808 10754331801644631604941 

noncomputable def Ns96p2159 := @Ns96p2158 Ns96p180 30948275 268435456 2213 1342177280 (Ns96p2152 (RS097to114.d38 qz137 qz150 qz285) RS097to114.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2160 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz137 330949 1000 qz140 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz835 qz836 (Ns96p2151 rfl rfl) (Ns96p2153 rfl rfl)) (Ns96p2154 qz11 qz140 rfl rfl rfl rfl (Ns96p2156 rfl)) (Ns96p2157 qz11 qz153 rfl rfl rfl rfl (Ns96p2159 rfl)) 

noncomputable abbrev qz944 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 332533 1000) (Enclosure.sfrac Bool.false 334115 1000) 332533 1000 334115 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 332533 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 334115 1000)) rfl rfl rfl)

noncomputable abbrev qz837 := qz944

noncomputable abbrev qz611 := qz837

noncomputable abbrev qz286 := (RS097to114.d3 qz491 qz504 qz611)

noncomputable abbrev qz838 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz286)

noncomputable def Ns96p2161 := @Enclosure.Real.IsNear.of_eq qz838 (hardyZApproximantRS₀ qz150) Bool.true 26009986968686582821 9223372036854775808 10754331801644631604941 Ns96p180 

noncomputable abbrev qz287 := qz611

noncomputable def Ns96p2162 := @Enclosure.Real.IsNear.neg_val qz838 26009986968686582821 9223372036854775808 10754331801644631604941 Ns96p180 (Ns96p2161 (RS097to114.d4 qz150 qz163 qz287) RS097to114.d49) rfl 

noncomputable abbrev qz839 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz286)

noncomputable def Ns96p2163 := @Enclosure.Real.IsNear.of_eq qz839 (hardyZApproximantRS₀ qz163) Bool.false 3401920931704173351 18446744073709551616 10601722257768948890451 Ns96p180 

noncomputable def Ns96p2164 := @Enclosure.Real.IsNear.pos_val qz839 3401920931704173351 18446744073709551616 10601722257768948890451 Ns96p180 (Ns96p2163 (RS097to114.d38 qz150 qz163 qz287) RS097to114.d50) rfl 

noncomputable def Ns96p2165 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz838 qz4 qz150 316604 1000 332533 1000 

noncomputable def Ns96p2166 := @Enclosure.norm_gt_of_isNear qz838 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 26009986968686582821 9223372036854775808 10754331801644631604941 

noncomputable def Ns96p2167 := @Ns96p2166 Ns96p180 30948275 268435456 2213 1342177280 (Ns96p2161 (RS097to114.d4 qz150 qz163 qz287) RS097to114.d49) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2168 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz839 qz4 qz163 316604 1000 334115 1000 

noncomputable def Ns96p2169 := @Enclosure.norm_gt_of_isNear qz839 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 3401920931704173351 18446744073709551616 10601722257768948890451 

noncomputable def Ns96p2170 := @Ns96p2169 Ns96p180 30948275 268435456 2213 1342177280 (Ns96p2163 (RS097to114.d38 qz150 qz163 qz287) RS097to114.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2171 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz286 (@BSN.thirtyTwoPi_le_dec qz150 332533 1000 qz153 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz838 qz839 (Ns96p2162 rfl rfl) (Ns96p2164 rfl rfl)) (Ns96p2165 qz11 qz153 rfl rfl rfl rfl (Ns96p2167 rfl)) (Ns96p2168 qz11 qz166 rfl rfl rfl rfl (Ns96p2170 rfl)) 

noncomputable abbrev qz288 := (RS097to114.d3 qz504 qz517 (@Enclosure.dec_le_dec qz504 qz517 334115 1000 335696 1000 qz507 qz520 rfl rfl rfl))

noncomputable abbrev qz840 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz288)

noncomputable def Ns96p2172 := @Enclosure.Real.IsNear.of_eq qz840 (hardyZApproximantRS₀ qz163) Bool.false 3401920931704173351 18446744073709551616 10601722257768948890451 Ns96p180 

noncomputable abbrev qz289 := (@Enclosure.dec_le_dec qz504 qz517 334115 1000 335696 1000 qz507 qz520 rfl rfl rfl)

noncomputable def Ns96p2173 := @Enclosure.Real.IsNear.pos_val qz840 3401920931704173351 18446744073709551616 10601722257768948890451 Ns96p180 (Ns96p2172 (RS097to114.d4 qz163 qz176 qz289) RS097to114.d50) rfl 

noncomputable abbrev qz841 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz288)

noncomputable def Ns96p2174 := @Enclosure.Real.IsNear.of_eq qz841 (hardyZApproximantRS₀ qz176) Bool.true 3040123000010036131 576460752303423488 528382570029073412793 279007004114856968192000 

noncomputable def Ns96p2175 := @Enclosure.Real.IsNear.neg_val qz841 3040123000010036131 576460752303423488 528382570029073412793 279007004114856968192000 (Ns96p2174 (RS097to114.d38 qz163 qz176 qz289) RS097to114.d51) rfl 

noncomputable def Ns96p2176 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz840 qz4 qz163 316604 1000 334115 1000 

noncomputable def Ns96p2177 := @Enclosure.norm_gt_of_isNear qz840 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 3401920931704173351 18446744073709551616 10601722257768948890451 

noncomputable def Ns96p2178 := @Ns96p2177 Ns96p180 30948275 268435456 2213 1342177280 (Ns96p2172 (RS097to114.d4 qz163 qz176 qz289) RS097to114.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2179 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz841 qz4 qz176 316604 1000 335696 1000 

noncomputable def Ns96p2180 := @Enclosure.norm_gt_of_isNear qz841 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 3040123000010036131 576460752303423488 528382570029073412793 

noncomputable def Ns96p2181 := @Ns96p2180 279007004114856968192000 30948275 268435456 2213 1342177280 (Ns96p2174 (RS097to114.d38 qz163 qz176 qz289) RS097to114.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2182 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz163 334115 1000 qz166 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz840 qz841 (Ns96p2173 rfl rfl) (Ns96p2175 rfl rfl)) (Ns96p2176 qz11 qz166 rfl rfl rfl rfl (Ns96p2178 rfl)) (Ns96p2179 qz11 qz179 rfl rfl rfl rfl (Ns96p2181 rfl)) 

noncomputable abbrev qz290 := (RS097to114.d3 qz517 qz530 (@Enclosure.dec_le_dec qz517 qz530 335696 1000 337274 1000 qz520 qz533 rfl rfl rfl))

noncomputable abbrev qz842 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz290)

noncomputable def Ns96p2183 := @Enclosure.Real.IsNear.of_eq qz842 (hardyZApproximantRS₀ qz176) Bool.true 3040123000010036131 576460752303423488 528382570029073412793 279007004114856968192000 

noncomputable abbrev qz291 := (@Enclosure.dec_le_dec qz517 qz530 335696 1000 337274 1000 qz520 qz533 rfl rfl rfl)

noncomputable def Ns96p2184 := @Enclosure.Real.IsNear.neg_val qz842 3040123000010036131 576460752303423488 528382570029073412793 279007004114856968192000 (Ns96p2183 (RS097to114.d4 qz176 qz189 qz291) RS097to114.d51) rfl 

noncomputable abbrev qz843 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz290)

noncomputable def Ns96p2185 := @Enclosure.Real.IsNear.of_eq qz843 (hardyZApproximantRS₀ qz189) Bool.false 256712750854556814877 147573952589676412928 21141027347214661077387 Ns96p1430 

noncomputable def Ns96p2186 := @Enclosure.Real.IsNear.pos_val qz843 256712750854556814877 147573952589676412928 21141027347214661077387 Ns96p1430 (Ns96p2185 (RS097to114.d38 qz176 qz189 qz291) RS097to114.d52) rfl 

noncomputable def Ns96p2187 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz842 qz4 qz176 316604 1000 335696 1000 

noncomputable def Ns96p2188 := @Enclosure.norm_gt_of_isNear qz842 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 3040123000010036131 576460752303423488 528382570029073412793 

noncomputable def Ns96p2189 := @Ns96p2188 279007004114856968192000 30948275 268435456 2213 1342177280 (Ns96p2183 (RS097to114.d4 qz176 qz189 qz291) RS097to114.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2190 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz843 qz4 qz189 316604 1000 337274 1000 

noncomputable def Ns96p2191 := @Enclosure.norm_gt_of_isNear qz843 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 256712750854556814877 147573952589676412928 21141027347214661077387 

noncomputable def Ns96p2192 := @Ns96p2191 Ns96p1430 30948275 268435456 2213 1342177280 (Ns96p2185 (RS097to114.d38 qz176 qz189 qz291) RS097to114.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2193 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz290 (@BSN.thirtyTwoPi_le_dec qz176 335696 1000 qz179 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz842 qz843 (Ns96p2184 rfl rfl) (Ns96p2186 rfl rfl)) (Ns96p2187 qz11 qz179 rfl rfl rfl rfl (Ns96p2189 rfl)) (Ns96p2190 qz11 qz192 rfl rfl rfl rfl (Ns96p2192 rfl)) 

noncomputable abbrev qz612 := (@Enclosure.dec_le_dec qz753 qz763 337274 1000 338851 1000 (@Eq.refl Real qz753) (@Eq.refl Real qz763) rfl rfl rfl)

noncomputable abbrev qz292 := (RS097to114.d3 qz530 qz543 qz612)

noncomputable abbrev qz844 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz292)

noncomputable def Ns96p2194 := @Enclosure.Real.IsNear.of_eq qz844 (hardyZApproximantRS₀ qz189) Bool.false 256712750854556814877 147573952589676412928 21141027347214661077387 Ns96p1430 

noncomputable abbrev qz293 := qz612

noncomputable def Ns96p2195 := @Enclosure.Real.IsNear.pos_val qz844 256712750854556814877 147573952589676412928 21141027347214661077387 Ns96p1430 (Ns96p2194 (RS097to114.d4 qz189 qz202 qz293) RS097to114.d52) rfl 

noncomputable abbrev qz845 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz292)

noncomputable def Ns96p2196 := @Enclosure.Real.IsNear.of_eq qz845 (hardyZApproximantRS₀ qz202) Bool.true 48010905485371094065 36893488147419103232 10591462660508401410701 Ns96p180 

noncomputable def Ns96p2197 := @Enclosure.Real.IsNear.neg_val qz845 48010905485371094065 36893488147419103232 10591462660508401410701 Ns96p180 (Ns96p2196 (RS097to114.d38 qz189 qz202 qz293) RS097to114.d53) rfl 

noncomputable def Ns96p2198 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz844 qz4 qz189 316604 1000 337274 1000 

noncomputable def Ns96p2199 := @Enclosure.norm_gt_of_isNear qz844 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 256712750854556814877 147573952589676412928 21141027347214661077387 

noncomputable def Ns96p2200 := @Ns96p2199 Ns96p1430 30948275 268435456 2213 1342177280 (Ns96p2194 (RS097to114.d4 qz189 qz202 qz293) RS097to114.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2201 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz845 qz4 qz202 316604 1000 338851 1000 

noncomputable def Ns96p2202 := @Enclosure.norm_gt_of_isNear qz845 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 48010905485371094065 36893488147419103232 10591462660508401410701 

noncomputable def Ns96p2203 := @Ns96p2202 Ns96p180 30948275 268435456 2213 1342177280 (Ns96p2196 (RS097to114.d38 qz189 qz202 qz293) RS097to114.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2204 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz189 337274 1000 qz192 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz844 qz845 (Ns96p2195 rfl rfl) (Ns96p2197 rfl rfl)) (Ns96p2198 qz11 qz192 rfl rfl rfl rfl (Ns96p2200 rfl)) (Ns96p2201 qz11 qz205 rfl rfl rfl rfl (Ns96p2203 rfl)) 

noncomputable abbrev qz613 := (@Enclosure.dec_le_dec qz763 qz773 338851 1000 340425 1000 (@Eq.refl Real qz763) qz777 rfl rfl rfl)

noncomputable abbrev qz294 := (RS097to114.d3 qz543 qz556 qz613)

noncomputable abbrev qz846 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz294)

noncomputable def Ns96p2205 := @Enclosure.Real.IsNear.of_eq qz846 (hardyZApproximantRS₀ qz202) Bool.true 48010905485371094065 36893488147419103232 10591462660508401410701 Ns96p180 

noncomputable abbrev qz295 := qz613

noncomputable def Ns96p2206 := @Enclosure.Real.IsNear.neg_val qz846 48010905485371094065 36893488147419103232 10591462660508401410701 Ns96p180 (Ns96p2205 (RS097to114.d4 qz202 qz215 qz295) RS097to114.d53) rfl 

noncomputable abbrev qz847 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz294)

noncomputable def Ns96p2207 := @Enclosure.Real.IsNear.of_eq qz847 (hardyZApproximantRS₀ qz215) Bool.false 112703726476952168341 147573952589676412928 531116263829226208183 279007004114856968192000 

noncomputable def Ns96p2208 := @Enclosure.Real.IsNear.pos_val qz847 112703726476952168341 147573952589676412928 531116263829226208183 279007004114856968192000 (Ns96p2207 (RS097to114.d38 qz202 qz215 qz295) RS097to114.d54) rfl 

noncomputable def Ns96p2209 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz846 qz4 qz202 316604 1000 338851 1000 

noncomputable def Ns96p2210 := @Enclosure.norm_gt_of_isNear qz846 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 48010905485371094065 36893488147419103232 10591462660508401410701 

noncomputable def Ns96p2211 := @Ns96p2210 Ns96p180 30948275 268435456 2213 1342177280 (Ns96p2205 (RS097to114.d4 qz202 qz215 qz295) RS097to114.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2212 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz847 qz4 qz215 316604 1000 340425 1000 

noncomputable def Ns96p2213 := @Enclosure.norm_gt_of_isNear qz847 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 112703726476952168341 147573952589676412928 531116263829226208183 

noncomputable def Ns96p2214 := @Ns96p2213 279007004114856968192000 30948275 268435456 2213 1342177280 (Ns96p2207 (RS097to114.d38 qz202 qz215 qz295) RS097to114.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2215 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz294 (@BSN.thirtyTwoPi_le_dec qz202 338851 1000 qz205 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz846 qz847 (Ns96p2206 rfl rfl) (Ns96p2208 rfl rfl)) (Ns96p2209 qz11 qz205 rfl rfl rfl rfl (Ns96p2211 rfl)) (Ns96p2212 qz11 qz218 rfl rfl rfl rfl (Ns96p2214 rfl)) 

noncomputable abbrev qz614 := (@Enclosure.dec_le_dec qz773 qz784 340425 1000 341998 1000 qz777 qz788 rfl rfl rfl)

noncomputable abbrev qz296 := (RS097to114.d3 qz556 qz569 qz614)

noncomputable abbrev qz848 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz296)

noncomputable def Ns96p2216 := @Enclosure.Real.IsNear.of_eq qz848 (hardyZApproximantRS₀ qz215) Bool.false 112703726476952168341 147573952589676412928 531116263829226208183 279007004114856968192000 

noncomputable abbrev qz297 := qz614

noncomputable def Ns96p2217 := @Enclosure.Real.IsNear.pos_val qz848 112703726476952168341 147573952589676412928 531116263829226208183 279007004114856968192000 (Ns96p2216 (RS097to114.d4 qz215 qz228 qz297) RS097to114.d54) rfl 

noncomputable abbrev qz849 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz296)

noncomputable def Ns96p2218 := @Enclosure.Real.IsNear.of_eq qz849 (hardyZApproximantRS₀ qz228) Bool.true 818961511628078609 4611686018427387904 1065705604833107810123 558014008229713936384000 

noncomputable def Ns96p2219 := @Enclosure.Real.IsNear.neg_val qz849 818961511628078609 4611686018427387904 1065705604833107810123 558014008229713936384000 (Ns96p2218 (RS097to114.d38 qz215 qz228 qz297) RS097to114.d55) rfl 

noncomputable def Ns96p2220 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz848 qz4 qz215 316604 1000 340425 1000 

noncomputable def Ns96p2221 := @Enclosure.norm_gt_of_isNear qz848 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 112703726476952168341 147573952589676412928 531116263829226208183 

noncomputable def Ns96p2222 := @Ns96p2221 279007004114856968192000 30948275 268435456 2213 1342177280 (Ns96p2216 (RS097to114.d4 qz215 qz228 qz297) RS097to114.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2223 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz849 qz4 qz228 316604 1000 341998 1000 

noncomputable def Ns96p2224 := @Enclosure.norm_gt_of_isNear qz849 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 818961511628078609 4611686018427387904 1065705604833107810123 

noncomputable def Ns96p2225 := @Ns96p2224 558014008229713936384000 30948275 268435456 2213 1342177280 (Ns96p2218 (RS097to114.d38 qz215 qz228 qz297) RS097to114.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2226 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz296 (@BSN.thirtyTwoPi_le_dec qz215 340425 1000 qz218 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz848 qz849 (Ns96p2217 rfl rfl) (Ns96p2219 rfl rfl)) (Ns96p2220 qz11 qz218 rfl rfl rfl rfl (Ns96p2222 rfl)) (Ns96p2223 qz11 qz231 rfl rfl rfl rfl (Ns96p2225 rfl)) 

noncomputable abbrev qz850 := (@Enclosure.dec_le_dec qz931 qz935 341998 1000 343569 1000 (@Eq.refl Real qz931) qz938 rfl rfl rfl)

noncomputable abbrev qz615 := qz850

noncomputable abbrev qz298 := (RS097to114.d3 qz569 qz582 qz615)

noncomputable abbrev qz851 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz298)

noncomputable def Ns96p2227 := @Enclosure.Real.IsNear.of_eq qz851 (hardyZApproximantRS₀ qz228) Bool.true 818961511628078609 4611686018427387904 1065705604833107810123 558014008229713936384000 

noncomputable abbrev qz299 := qz615

noncomputable def Ns96p2228 := @Enclosure.Real.IsNear.neg_val qz851 818961511628078609 4611686018427387904 1065705604833107810123 558014008229713936384000 (Ns96p2227 (RS097to114.d4 qz228 qz241 qz299) RS097to114.d55) rfl 

noncomputable abbrev qz852 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz298)

noncomputable def Ns96p2229 := @Enclosure.Real.IsNear.of_eq qz852 (hardyZApproximantRS₀ qz241) Bool.false 423986679231176376139 73786976294838206464 10696741340281652335837 Ns96p180 

noncomputable def Ns96p2230 := @Enclosure.Real.IsNear.pos_val qz852 423986679231176376139 73786976294838206464 10696741340281652335837 Ns96p180 (Ns96p2229 (RS097to114.d38 qz228 qz241 qz299) RS097to114.d56) rfl 

noncomputable def Ns96p2231 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz851 qz4 qz228 316604 1000 341998 1000 

noncomputable def Ns96p2232 := @Enclosure.norm_gt_of_isNear qz851 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 818961511628078609 4611686018427387904 1065705604833107810123 

noncomputable def Ns96p2233 := @Ns96p2232 558014008229713936384000 30948275 268435456 2213 1342177280 (Ns96p2227 (RS097to114.d4 qz228 qz241 qz299) RS097to114.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2234 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz852 qz4 qz241 316604 1000 343569 1000 

noncomputable def Ns96p2235 := @Enclosure.norm_gt_of_isNear qz852 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 423986679231176376139 73786976294838206464 10696741340281652335837 

noncomputable def Ns96p2236 := @Ns96p2235 Ns96p180 30948275 268435456 2213 1342177280 (Ns96p2229 (RS097to114.d38 qz228 qz241 qz299) RS097to114.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2237 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz298 (@BSN.thirtyTwoPi_le_dec qz228 341998 1000 qz231 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz851 qz852 (Ns96p2228 rfl rfl) (Ns96p2230 rfl rfl)) (Ns96p2231 qz11 qz231 rfl rfl rfl rfl (Ns96p2233 rfl)) (Ns96p2234 qz11 qz244 rfl rfl rfl rfl (Ns96p2236 rfl)) 

noncomputable abbrev qz945 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 343569 1000) (Enclosure.sfrac Bool.false 345139 1000) 343569 1000 345139 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 343569 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 345139 1000)) rfl rfl rfl)

noncomputable abbrev qz853 := qz945

noncomputable abbrev qz616 := qz853

noncomputable abbrev qz300 := (RS097to114.d3 qz582 qz595 qz616)

noncomputable abbrev qz854 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz300)

noncomputable def Ns96p2238 := @Enclosure.Real.IsNear.of_eq qz854 (hardyZApproximantRS₀ qz241) Bool.false 423986679231176376139 73786976294838206464 10696741340281652335837 Ns96p180 

noncomputable abbrev qz301 := qz616

noncomputable def Ns96p2239 := @Enclosure.Real.IsNear.pos_val qz854 423986679231176376139 73786976294838206464 10696741340281652335837 Ns96p180 (Ns96p2238 (RS097to114.d4 qz241 qz254 qz301) RS097to114.d56) rfl 

noncomputable abbrev qz855 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz300)

noncomputable def Ns96p2240 := @Enclosure.Real.IsNear.of_eq qz855 (hardyZApproximantRS₀ qz254) Bool.true 310564456206875455 144115188075855872 536944442081102687161 279007004114856968192000 

noncomputable def Ns96p2241 := @Enclosure.Real.IsNear.neg_val qz855 310564456206875455 144115188075855872 536944442081102687161 279007004114856968192000 (Ns96p2240 (RS097to114.d38 qz241 qz254 qz301) RS097to114.d57) rfl 

noncomputable def Ns96p2242 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz854 qz4 qz241 316604 1000 343569 1000 

noncomputable def Ns96p2243 := @Enclosure.norm_gt_of_isNear qz854 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 423986679231176376139 73786976294838206464 10696741340281652335837 

noncomputable def Ns96p2244 := @Ns96p2243 Ns96p180 30948275 268435456 2213 1342177280 (Ns96p2238 (RS097to114.d4 qz241 qz254 qz301) RS097to114.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2245 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz855 qz4 qz254 316604 1000 345139 1000 

noncomputable def Ns96p2246 := @Enclosure.norm_gt_of_isNear qz855 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 310564456206875455 144115188075855872 536944442081102687161 

noncomputable def Ns96p2247 := @Ns96p2246 279007004114856968192000 30948275 268435456 2213 1342177280 (Ns96p2240 (RS097to114.d38 qz241 qz254 qz301) RS097to114.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 30948275 268435456 2213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS097to114.d40) rfl rfl rfl rfl 

noncomputable def Ns96p2248 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz241 343569 1000 qz244 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz854 qz855 (Ns96p2239 rfl rfl) (Ns96p2241 rfl rfl)) (Ns96p2242 qz11 qz244 rfl rfl rfl rfl (Ns96p2244 rfl)) (Ns96p2245 qz11 (@Eq.refl Real qz254) rfl rfl rfl rfl (Ns96p2247 rfl)) 

noncomputable def Ns96p2249 := @List.cons RS097to114.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz298 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz298) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz298) Ns96p2237)) (@List.cons RS097to114.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns96p2248)) (@List.nil RS097to114.d0)) 

noncomputable def Ns96p2250 := @List.cons RS097to114.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz294 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz294) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz294) Ns96p2215)) (@List.cons RS097to114.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns96p2226)) Ns96p2249) 

noncomputable def Ns96p2251 := @List.cons RS097to114.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz290 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz290) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz290) Ns96p2193)) (@List.cons RS097to114.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns96p2204)) Ns96p2250) 

noncomputable def Ns96p2252 := @List.cons RS097to114.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz286 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz286) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz286) Ns96p2171)) (@List.cons RS097to114.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns96p2182)) Ns96p2251) 

noncomputable def Ns96p2253 := @List.cons RS097to114.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz282 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz282) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz282) Ns96p2149)) (@List.cons RS097to114.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns96p2160)) Ns96p2252) 

noncomputable def Ns96p2254 := @List.cons RS097to114.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz278 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz278) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz278) Ns96p2127)) (@List.cons RS097to114.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz280 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz280) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz280) Ns96p2138)) Ns96p2253) 

noncomputable def Ns96p2255 := @List.cons RS097to114.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz274 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz274) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz274) Ns96p2105)) (@List.cons RS097to114.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz276 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz276) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz276) Ns96p2116)) Ns96p2254) 

noncomputable def Ns96p2256 := @List.cons RS097to114.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz270 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz270) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz270) Ns96p2083)) (@List.cons RS097to114.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz272 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz272) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz272) Ns96p2094)) Ns96p2255) 

noncomputable def Ns96p2257 := @List.cons RS097to114.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz266 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz266) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz266) Ns96p2061)) (@List.cons RS097to114.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz268 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz268) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz268) Ns96p2072)) Ns96p2256) 

noncomputable abbrev qz856 := (RS097to114.d2 qz931 qz935 (@Enclosure.dec_le_dec qz931 qz935 341998 1000 343569 1000 (@Eq.refl Real qz931) qz938 rfl rfl rfl))

noncomputable abbrev qz857 := (@List.cons RS097to114.d1 (RS097to114.d2 qz935 qz940 qz945) (@List.nil RS097to114.d1))

noncomputable abbrev qz617 := (@List.cons RS097to114.d1 (RS097to114.d2 qz773 qz784 (@Enclosure.dec_le_dec qz773 qz784 340425 1000 341998 1000 qz777 qz788 rfl rfl rfl)) (@List.cons RS097to114.d1 qz856 qz857))

noncomputable abbrev qz302 := (@List.cons RS097to114.d1 (RS097to114.d2 qz530 qz543 qz612) (@List.cons RS097to114.d1 (RS097to114.d2 qz543 qz556 qz613) qz617))

noncomputable def Ns96p2258 := @List.cons RS097to114.d1 (RS097to114.d2 qz163 qz176 qz289) (@List.cons RS097to114.d1 (RS097to114.d2 qz176 qz189 qz291) qz302) 

noncomputable abbrev qz858 := (RS097to114.d2 qz901 qz905 (@Enclosure.dec_le_dec qz901 qz905 330949 1000 332533 1000 (@Eq.refl Real qz901) qz908 rfl rfl rfl))

noncomputable abbrev qz859 := (@List.cons RS097to114.d1 (RS097to114.d2 qz905 qz910 qz944) Ns96p2258)

noncomputable abbrev qz618 := (@List.cons RS097to114.d1 (RS097to114.d2 qz699 qz710 (@Enclosure.dec_le_dec qz699 qz710 329363 1000 330949 1000 qz703 qz714 rfl rfl rfl)) (@List.cons RS097to114.d1 qz858 qz859))

noncomputable abbrev qz303 := (@List.cons RS097to114.d1 (RS097to114.d2 qz439 qz451 qz607) (@List.cons RS097to114.d1 (RS097to114.d2 qz451 qz464 qz608) qz618))

noncomputable def Ns96p2259 := @List.cons RS097to114.d1 (RS097to114.d2 qz74 qz87 qz275) (@List.cons RS097to114.d1 (RS097to114.d2 qz87 qz100 qz277) qz303) 

noncomputable def Ns96p2260 := @List.IsChain.cons_cons RS097to114.d1 RS097to114.d58 (RS097to114.d2 qz61 qz74 qz273) (RS097to114.d2 qz74 qz87 qz275) (@List.cons RS097to114.d1 (RS097to114.d2 qz87 qz100 qz277) qz303) 

noncomputable def Ns96p2261 := @List.IsChain.cons_cons RS097to114.d1 RS097to114.d58 (RS097to114.d2 qz74 qz87 qz275) (RS097to114.d2 qz87 qz100 qz277) qz303 (@Enclosure.dec_le_dec qz87 qz87 324594 1000 324594 1000 qz90 qz90 rfl rfl rfl) 

noncomputable abbrev qz860 := (RS097to114.d2 qz905 qz910 qz944)

noncomputable abbrev qz619 := qz860

noncomputable abbrev qz304 := qz619

noncomputable def Ns96p2262 := @List.IsChain.cons_cons RS097to114.d1 RS097to114.d58 qz304 (RS097to114.d2 qz163 qz176 qz289) (@List.cons RS097to114.d1 (RS097to114.d2 qz176 qz189 qz291) qz302) 

noncomputable def Ns96p2263 := @List.IsChain.cons_cons RS097to114.d1 RS097to114.d58 (RS097to114.d2 qz163 qz176 qz289) (RS097to114.d2 qz176 qz189 qz291) qz302 (@Enclosure.dec_le_dec qz176 qz176 335696 1000 335696 1000 qz179 qz179 rfl rfl rfl) 

noncomputable abbrev qz305 := qz617

noncomputable abbrev qz620 := (@List.cons RS097to114.d1 qz856 qz857)

noncomputable abbrev qz306 := qz620

noncomputable abbrev qz621 := qz856

noncomputable abbrev qz307 := qz621

noncomputable abbrev qz622 := qz857

noncomputable abbrev qz308 := qz622

noncomputable abbrev qz861 := (RS097to114.d2 qz935 qz940 qz945)

noncomputable abbrev qz623 := qz861

noncomputable abbrev qz309 := qz623

noncomputable def Ns96p2264 := @List.IsChain.cons_cons RS097to114.d1 RS097to114.d58 (RS097to114.d2 qz189 qz202 qz293) (RS097to114.d2 qz202 qz215 qz295) qz305 (@Enclosure.dec_le_dec qz202 qz202 338851 1000 338851 1000 qz205 qz205 rfl rfl rfl) (@List.IsChain.cons_cons RS097to114.d1 RS097to114.d58 (RS097to114.d2 qz202 qz215 qz295) (RS097to114.d2 qz215 qz228 qz297) qz306 (@Enclosure.dec_le_dec qz215 qz215 340425 1000 340425 1000 qz218 qz218 rfl rfl rfl) (@List.IsChain.cons_cons RS097to114.d1 RS097to114.d58 (RS097to114.d2 qz215 qz228 qz297) qz307 qz308 (@Enclosure.dec_le_dec qz228 qz228 341998 1000 341998 1000 qz231 qz231 rfl rfl rfl) (@List.IsChain.cons_cons RS097to114.d1 RS097to114.d58 qz307 qz309 (@List.nil RS097to114.d1) (@Enclosure.dec_le_dec qz241 qz241 343569 1000 343569 1000 qz244 qz244 rfl rfl rfl) (@List.IsChain.singleton RS097to114.d1 RS097to114.d58 qz309)))) 

noncomputable abbrev qz310 := (@List.cons RS097to114.d1 (RS097to114.d2 qz543 qz556 qz613) qz617)

noncomputable def Ns96p2265 := @List.IsChain.cons_cons RS097to114.d1 RS097to114.d58 (RS097to114.d2 qz176 qz189 qz291) (RS097to114.d2 qz189 qz202 qz293) qz310 (@Enclosure.dec_le_dec qz189 qz189 337274 1000 337274 1000 qz192 qz192 rfl rfl rfl) Ns96p2264 

noncomputable abbrev qz311 := qz618

noncomputable abbrev qz624 := (@List.cons RS097to114.d1 qz858 qz859)

noncomputable abbrev qz312 := qz624

noncomputable abbrev qz625 := qz858

noncomputable abbrev qz313 := qz625

noncomputable abbrev qz626 := qz859

noncomputable abbrev qz314 := qz626

noncomputable def Ns96p2266 := @List.IsChain.cons_cons RS097to114.d1 RS097to114.d58 (RS097to114.d2 qz100 qz113 qz279) (RS097to114.d2 qz113 qz125 qz281) qz311 (@Enclosure.dec_le_dec qz113 qz113 327775 1000 327775 1000 qz116 qz116 rfl rfl rfl) (@List.IsChain.cons_cons RS097to114.d1 RS097to114.d58 (RS097to114.d2 qz113 qz125 qz281) (RS097to114.d2 qz125 qz137 qz283) qz312 (@Enclosure.dec_le_dec qz125 qz125 329363 1000 329363 1000 qz128 qz128 rfl rfl rfl) (@List.IsChain.cons_cons RS097to114.d1 RS097to114.d58 (RS097to114.d2 qz125 qz137 qz283) qz313 qz314 (@Enclosure.dec_le_dec qz137 qz137 330949 1000 330949 1000 qz140 qz140 rfl rfl rfl) (@List.IsChain.cons_cons RS097to114.d1 RS097to114.d58 qz313 qz304 Ns96p2258 (@Enclosure.dec_le_dec qz150 qz150 332533 1000 332533 1000 qz153 qz153 rfl rfl rfl) (Ns96p2262 (@Enclosure.dec_le_dec qz163 qz163 334115 1000 334115 1000 qz166 qz166 rfl rfl rfl) (Ns96p2263 Ns96p2265))))) 

noncomputable abbrev qz315 := (@List.cons RS097to114.d1 (RS097to114.d2 qz451 qz464 qz608) qz618)

noncomputable def Ns96p2267 := @List.IsChain.cons_cons RS097to114.d1 RS097to114.d58 (RS097to114.d2 qz87 qz100 qz277) (RS097to114.d2 qz100 qz113 qz279) qz315 (@Enclosure.dec_le_dec qz100 qz100 326185 1000 326185 1000 qz103 qz103 rfl rfl rfl) Ns96p2266 

noncomputable def Ns96p2268 := Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns96p2257 (@List.IsChain.cons_cons RS097to114.d1 RS097to114.d58 (RS097to114.d2 qz4 qz29 qz267) (RS097to114.d2 qz29 qz48 qz269) (@List.cons RS097to114.d1 (RS097to114.d2 qz48 qz61 qz271) (@List.cons RS097to114.d1 (RS097to114.d2 qz61 qz74 qz273) Ns96p2259)) (@Enclosure.dec_le_dec qz29 qz29 318206 1000 318206 1000 qz32 qz32 rfl rfl rfl) (@List.IsChain.cons_cons RS097to114.d1 RS097to114.d58 (RS097to114.d2 qz29 qz48 qz269) (RS097to114.d2 qz48 qz61 qz271) (@List.cons RS097to114.d1 (RS097to114.d2 qz61 qz74 qz273) Ns96p2259) (@Enclosure.dec_le_dec qz48 qz48 319806 1000 319806 1000 qz51 qz51 rfl rfl rfl) (@List.IsChain.cons_cons RS097to114.d1 RS097to114.d58 (RS097to114.d2 qz48 qz61 qz271) (RS097to114.d2 qz61 qz74 qz273) Ns96p2259 (@Enclosure.dec_le_dec qz61 qz61 321404 1000 321404 1000 qz64 qz64 rfl rfl rfl) (Ns96p2260 (@Enclosure.dec_le_dec qz74 qz74 323000 1000 323000 1000 qz77 qz77 rfl rfl rfl) (Ns96p2261 Ns96p2267))))) 

noncomputable abbrev qz627 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz628 := (Zeta.Certificates.CertifiedZeroIntervals.intervals Ns96p2268)

theorem RS097to114.d59 : Zeta.Certificates.BatchSpec 18 316604 1000 345139 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz627 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 18) (And (@Eq (Option Real) (@Option.map qz627 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz627 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz627 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz627 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz254)))) Ns96p2268 (@And.intro (@Eq Nat (@List.length qz627 qz628) 18) (And (@Eq (Option Real) (@Option.map qz627 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz627 qz628)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz627 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz627 qz628)) (@Option.some Real qz254))) (@Eq.refl Nat 18) (@And.intro (@Eq (Option Real) (@Option.map qz627 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz627 qz628)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz627 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz627 qz628)) (@Option.some Real qz254)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz254))))

theorem solution : Zeta.Certificates.BatchSpec 18 316604 1000 345139 1000 := RS097to114.d59
#print axioms solution
#check solution
