-- Prove2me | solution 1 for RHHeight1000.rs_main_0079_0096
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T21:49:52.279916+00:00
-- url     : https://prove2.me/submissions/391e8855-09e1-44fa-b565-bd2ff5a0da98

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

noncomputable def RS079to096.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS079to096.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS079to096.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS079to096.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS079to096.d2 a b h 

theorem RS079to096.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS079to096.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS079to096.d3 a b h)) 

noncomputable def Ns78p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns78p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns78p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns78p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns78p0 Ns78p1 Ns78p2 Ns78p1 76821522 67108864 1 17647056 76821522 67108864 1 17647056 38410761 33554432 2 33554432 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns78p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns78p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns78p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns78p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns78p8 := nat_lit 4564579050430662680769181008104061220617401457132102377181523838895616693352443067851710738206186456870068891932464934433532008760270543541307416978974983178670584632435273151991067990877911260800542253584783113678675870571765297427794279500566373840368605043192397583789219721854001914445657820861544585749419999617014263230075963405112904900127091763553068379337562290951837345169106631254289648555755847509739637528572205479767112592191328488981867735095152085893116377698979776390335134938272744697179058821035388170748994050345731998297589980525805272027148669105172128531226596705145339433394591280230580530674088894892093599627198529211479716891686479023042798211193766875 

noncomputable def Ns78p9 := nat_lit 487897090127139370915718269131278067469793404735814825511781216300711748025172292443098109798278438646340651351778930478625246708087138935333656000353278407183834741097045313633566773106147391845370902603761794798142555380136213880615811008223525988937457841388015247818375543397617608528881621312159551521324412657167692163397240217814307445909713899850058291308690066733028125556419716734774904437710284132364898181426902860503703874999414246848733477446908396851600224567407637334679631394476122651438668110771117818686943497967108192010818356995023330089079080278635386063923383437486637555787861728490935630579993241432729945572572039527546968749899721199864050991936636425 

noncomputable def Ns78p10 := nat_lit 6037312065319767048564142443281100833094517501602298457411621838401909436348967513970575877459259771623941548258204445821942291045664120860093665600098153114527011142424471743215189638406506367790367599859596104992621477169994698594142049192256667252266301439715334971326182286325870243632349119406725171166047972624848379242642987691741446913322611634487665631123884299676351857591585933871955560195724863436092564725843702568563820604138142931407752731605404492259322164906548421338089777140624840599546449293504664341809058329304227251421882253537858630692969727217927909816425536009981778974686700833928275616694615814871054602955126209568752228017149733267081250625 

noncomputable def Ns78p11 := BSN.log_dyadic_bound Ns78p6 Ns78p7 14 13 Ns78p8 67108864 17647056 Ns78p9 Ns78p10 76821522 Ns78p4 Ns78p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP Ns78p6) (BSN.artanhQ Ns78p7) 0 13 Ns78p9 Ns78p8 Ns78p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns78p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns78p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns78p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns78p15 := nat_lit 4564579050430719991598727864173574027249459620864950728835381976489772818715667160654947079996042508112007609792086902604246591277951902079645511578729044446029890641532783292129843149875777032317116470385319181253925715321425403083930304095443896121595862314424397722115177325385869596477930511910402142030838288588290691454497602943515837117442179176528567975378491450565217634156690207739385924001994080445739653712153122146143735369275124802705327973995316801123426696765469161725178407791303143690561306079033018690304653273985689879967765287476386100315971524212560669782530460797364817008851488910076252022325883262600059844010859170953904690437223359663042798211193766875 

noncomputable def Ns78p16 := nat_lit 487897090127146028016094362581487656757614504303373888298359177917068925336311225982425876767220472971199663852495703606478044548245204650969304786130313739004418091807374551157966311600460925549125369213480618028519005676490156484647720769146106466452899814849266557198964140238149260938822380107756357944282785296375303842904282420173433118269847736574242174913483374429734863225743639963757643848706968740179283875896315642693907130861939137742544595612595383386022728925244773380688186919137495322289344312028838765525860232491884325012249877491080249836360703014994786844727995613684463741175252463635603207543937219860925630575346787413234983278028650172664050991936636425 

noncomputable def Ns78p17 := nat_lit 6037312065319913640506765330482094651728996212510072186683329349665034025528265882310343281188309943135362157762326025787898903072857099500666458772539172249805276355211909724494669715550462680374559205875381267976760313571991112548079805305194151041203595124480241065931717334103047325628819416103687949050116922196393250525830281764599302835242983634853487222885409728030646963007168165596579721200854339637057218394652367706804217404799249814690071011337988816707639904852988452679974011323771101001271418584434659185032723127441286381829860978672625319259709832419206399165424340759332155638209605427889981579187342651500575472600628768480466654897149733267081250625 

noncomputable def Ns78p18 := BSN.log_dyadic_bound Ns78p13 Ns78p14 14 13 Ns78p15 67108864 17647056 Ns78p16 Ns78p17 76821522 Ns78p12 Ns78p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP Ns78p13) (BSN.artanhQ Ns78p14) 0 13 Ns78p16 Ns78p15 Ns78p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns78p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 38410761 33554432 2 33554432 38410761 33554432 1 16777216 (Ns78p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns78p0 Ns78p1 76821522 67108864 1 17647056 Bool.false (BSN.logfrac_isNear Ns78p4 Ns78p5 1 Ns78p0 Ns78p1 76821522 67108864 17647056 rfl rfl rfl (Ns78p11 rfl))) (BSN.isNear_log_sfrac Ns78p2 Ns78p1 76821522 67108864 1 17647056 Bool.false (BSN.logfrac_isNear Ns78p12 Ns78p5 1 Ns78p2 Ns78p1 76821522 67108864 17647056 rfl rfl rfl (Ns78p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS079to096.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 16777216 := Ns78p19 

noncomputable def Ns78p20 := BSN.log_dyadic_bound 1 3 7 6 71816279535 4194304 1102941 2852596872 10395 2907269 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1) (BSN.artanhQ 3) 0 6 2852596872 71816279535 10395 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz316 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz0 := qz316

theorem RS079to096.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 2907269 4194304 1 1102941 := BSN.isNear_log_sfrac 2 1 2907269 4194304 1 1102941 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 2907269 4194304 1102941 rfl rfl rfl (Ns78p20 rfl)) 

theorem RS079to096.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 46516304 67108864 61 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 2907269 4194304 1 1102941 46516304 67108864 61 67108864 RS079to096.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz319 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def Ns78p21 := @Enclosure.Real.IsNear.inv_image qz317 11863283 8388608 1 8388608 2965820 2965822 4194304 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 11863283 8388608 1 8388608 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 11863283 8388608 1 8388608 11863283 8388608 1 8388608 (BSN.sqrt_enclosure 2 1 5931641 5931642 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS079to096.d8 : Enclosure.Real.IsNear qz320 Bool.false 2965821 4194304 1 4194304 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 5931642 8388608 2 8388608 2965821 4194304 1 4194304 (Ns78p21 rfl rfl) rfl 

theorem RS079to096.d9 : Enclosure.Real.IsNear qz320 Bool.false 47453136 67108864 16 67108864 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 2965821 4194304 1 4194304 47453136 67108864 16 67108864 RS079to096.d8 rfl 

noncomputable def Ns78p22 := BSN.log_dyadic_bound 1 2 12 11 1326382131865190400 4194304 1102941 130797573554866995 13749310575 4607913 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 1) (BSN.artanhQ 2) 0 11 130797573554866995 1326382131865190400 13749310575 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS079to096.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 4607913 4194304 1 1102941 := BSN.isNear_log_sfrac 3 1 4607913 4194304 1 1102941 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 4607913 4194304 1102941 rfl rfl rfl (Ns78p22 rfl)) 

theorem RS079to096.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 73726608 67108864 61 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 4607913 4194304 1 1102941 73726608 67108864 61 67108864 RS079to096.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns78p23 := @Enclosure.Real.IsNear.inv_image qz321 14529495 8388608 1 8388608 2421582 2421583 4194304 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 14529495 8388608 1 8388608 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 14529495 8388608 1 8388608 14529495 8388608 1 8388608 (BSN.sqrt_enclosure 3 1 7264747 7264748 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS079to096.d12 : Enclosure.Real.IsNear qz323 Bool.false 4843165 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 4843165 8388608 1 8388608 4843165 8388608 1 8388608 (Ns78p23 rfl rfl) rfl 

theorem RS079to096.d13 : Enclosure.Real.IsNear qz323 Bool.false 38745320 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 4843165 8388608 1 8388608 38745320 67108864 8 67108864 RS079to096.d12 rfl 

noncomputable def Ns78p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns78p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns78p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns78p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns78p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns78p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns78p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns78p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns78p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns78p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns78p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns78p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns78p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns78p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns78p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns78p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns78p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns78p25 Ns78p26 Ns78p27 Ns78p28 200200021673987500790625 Ns78p29 Ns78p30 Ns78p31 Ns78p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns78p32 Ns78p33 151412625 Ns78p34 Ns78p35 1322214852783825 Ns78p27 Ns78p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns78p32 Ns78p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns78p34 Ns78p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns78p36 Ns78p37 1267389585 Ns78p38 Ns78p39 1927077560082675 Ns78p29 Ns78p30 Ns78p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns78p36 Ns78p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns78p38 Ns78p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS079to096.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns78p24 Ns78p25 1 Ns78p26 := Ns78p40 rfl rfl rfl 

noncomputable def Ns78p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns78p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns78p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns78p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns78p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns78p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns78p25 Ns78p26 Ns78p42 Ns78p43 9945 Ns78p44 Ns78p45 65835 Ns78p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns78p42 Ns78p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns78p44 Ns78p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS079to096.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns78p41 Ns78p25 1 Ns78p26 := Ns78p46 rfl 

noncomputable def Ns78p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns78p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS079to096.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns78p47 Ns78p25 1 Ns78p48 := BSN.pi_combine Ns78p24 Ns78p41 Ns78p25 Ns78p26 Ns78p48 Ns78p47 rfl rfl rfl rfl RS079to096.d14 RS079to096.d15 

theorem RS079to096.d17 : Enclosure.Real.IsNear Real.pi Bool.false 3537118876014220 1125899906842624 1 1125899906842624 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns78p47 Ns78p25 1 Ns78p48 3537118876014220 1125899906842624 1 1125899906842624 RS079to096.d16 rfl 

noncomputable def Ns78p49 := nat_lit 178719669545544893480837345123291015625 

noncomputable def Ns78p50 := nat_lit 27745388228251122714770036239987464375 

noncomputable def Ns78p51 := nat_lit 1274524447665412456340166714375 

noncomputable def Ns78p52 := BSN.log_dyadic_bound 3 5 16 15 Ns78p49 4194304 1102941 Ns78p50 Ns78p51 5814539 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP 3) (BSN.artanhQ 5) 0 15 Ns78p50 Ns78p49 Ns78p51 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS079to096.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 5814539 4194304 1 1102941 := BSN.isNear_log_sfrac 4 1 5814539 4194304 1 1102941 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 5814539 4194304 1102941 rfl rfl rfl (Ns78p52 rfl)) 

theorem RS079to096.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 93032624 67108864 61 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 5814539 4194304 1 1102941 93032624 67108864 61 67108864 RS079to096.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns78p53 := @Enclosure.Real.IsNear.inv_image qz325 16777217 8388608 1 8388608 2097151 2097152 4194304 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 16777217 8388608 1 8388608 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 16777217 8388608 1 8388608 16777217 8388608 1 8388608 (BSN.sqrt_enclosure 4 1 8388608 8388609 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS079to096.d20 : Enclosure.Real.IsNear qz327 Bool.false 4194303 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 4194303 8388608 1 8388608 4194303 8388608 1 8388608 (Ns78p53 rfl rfl) rfl 

theorem RS079to096.d21 : Enclosure.Real.IsNear qz327 Bool.false 33554424 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 4194303 8388608 1 8388608 33554424 67108864 8 67108864 RS079to096.d20 rfl 

noncomputable def Ns78p54 := nat_lit 432044237847189949652629901200995702590625 

noncomputable def Ns78p55 := nat_lit 89467042677079332529401996239971435345500 

noncomputable def Ns78p56 := nat_lit 2254217236409302326906244300800000 

noncomputable def Ns78p57 := nat_lit 1703271991756449094855875 

noncomputable def Ns78p58 := BSN.log_dyadic_bound 2 3 20 19 Ns78p54 4194304 1102941 Ns78p55 Ns78p56 6750471 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 19 9 52520441922763380 253655458399017675 9033331507200 1156268355358836200013540 Ns78p57 249544393960587264000 Ns78p55 Ns78p54 Ns78p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 2) (BSN.artanhQ 3) 0 9 52520441922763380 253655458399017675 9033331507200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 9 19 1156268355358836200013540 Ns78p57 249544393960587264000 rfl rfl rfl rfl)) rfl rfl 

theorem RS079to096.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 6750471 4194304 1 1102941 := BSN.isNear_log_sfrac 5 1 6750471 4194304 1 1102941 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 6750471 4194304 1102941 rfl rfl rfl (Ns78p58 rfl rfl)) 

theorem RS079to096.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 108007536 67108864 61 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 6750471 4194304 1 1102941 108007536 67108864 61 67108864 RS079to096.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns78p59 := @Enclosure.Real.IsNear.inv_image qz328 18757497 8388608 1 8388608 1875749 1875750 4194304 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 18757497 8388608 1 8388608 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 18757497 8388608 1 8388608 18757497 8388608 1 8388608 (BSN.sqrt_enclosure 5 1 9378748 9378749 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS079to096.d24 : Enclosure.Real.IsNear qz329 Bool.false 3751499 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 3751499 8388608 1 8388608 3751499 8388608 1 8388608 (Ns78p59 rfl rfl) rfl 

theorem RS079to096.d25 : Enclosure.Real.IsNear qz329 Bool.false 30011992 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 3751499 8388608 1 8388608 30011992 67108864 8 67108864 RS079to096.d24 rfl 

noncomputable def Ns78p60 := BSN.log_dyadic_bound 2 10 5 4 94500000000 4194304 1102941 1291130880 26880 1700643 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 10) 0 4 1291130880 94500000000 26880 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz840 := (Enclosure.sfrac Bool.false 6 1)

noncomputable abbrev qz628 := qz840

noncomputable abbrev qz330 := qz628

noncomputable abbrev qz1 := qz330

noncomputable abbrev qz331 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) (@Nat.cast Real Real.instNatCast 1))

theorem RS079to096.d26 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 4034683142479095 2251799813685248 500000001102941 551470500000000000000 := BSN.isNear_log_sfrac 6 1 4034683142479095 2251799813685248 500000001102941 551470500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz331) Bool.false 270763002291722209198080 151115727451828646838272 1000000002205882 1102941000000000000000 4034683142479095 2251799813685248 500000001102941 551470500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 1700643 4194304 24973259072661432 36028797018963968 1102941 1000000000000000 rfl rfl rfl rfl (Ns78p60 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS079to096.d27 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 120242927 67108864 62 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 4034683142479095 2251799813685248 500000001102941 551470500000000000000 120242927 67108864 62 67108864 RS079to096.d26 rfl 

noncomputable abbrev qz332 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns78p61 := @Enclosure.Real.IsNear.inv_image qz332 20547809 8388608 1 8388608 1712317 1712318 4194304 (@Enclosure.Real.IsNear.of_eq qz332 (Real.sqrt qz331) Bool.false 20547809 8388608 1 8388608 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz331) Bool.false 20547809 8388608 1 8388608 20547809 8388608 1 8388608 (BSN.sqrt_enclosure 6 1 10273904 10273905 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz333 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS079to096.d28 : Enclosure.Real.IsNear qz333 Bool.false 3424635 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz333 Bool.false 3424635 8388608 1 8388608 3424635 8388608 1 8388608 (Ns78p61 rfl rfl) rfl 

theorem RS079to096.d29 : Enclosure.Real.IsNear qz333 Bool.false 27397080 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz333 Bool.false 3424635 8388608 1 8388608 27397080 67108864 8 67108864 RS079to096.d28 rfl 

theorem RS079to096.d30 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz841 := (@instHMul Real Real.instMul)

noncomputable abbrev qz629 := qz841

noncomputable abbrev qz334 := (@HMul.hMul Real Real Real qz629 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz2 := qz334

theorem RS079to096.d31 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS079to096.d30 rfl 

noncomputable abbrev qz3 := (@Inv.inv Real Real.instInv qz334)

theorem RS079to096.d32 : Enclosure.Real.IsNear qz3 Bool.false 1335089 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 1335089 8388608 1 8388608 1335089 8388608 1 8388608 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 667544 667545 4194304 RS079to096.d31 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns78p62 := nat_lit 54255120947736764183740416 

noncomputable def Ns78p63 := nat_lit 5304108076962024521291792384 

noncomputable abbrev qz842 := (Enclosure.sfrac Bool.false 287396 1000)

noncomputable abbrev qz630 := qz842

noncomputable abbrev qz335 := qz630

noncomputable abbrev qz4 := qz335

noncomputable abbrev qz336 := qz629

noncomputable abbrev qz5 := qz336

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 6)

noncomputable abbrev qz7 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz843 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 287396 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz631 := qz843

noncomputable abbrev qz337 := qz631

noncomputable abbrev qz8 := qz337

noncomputable abbrev qz9 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz844 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 287396 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz632 := qz844

noncomputable abbrev qz338 := qz632

noncomputable abbrev qz10 := qz338

noncomputable abbrev qz633 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz8 qz9))

noncomputable def Ns78p64 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 6) (@HMul.hMul Real Real Real qz5 qz633 (Zeta.RiemannSiegel.correction qz10)) 29315225 33554432 50665 33554432 29145015855322116587 147573952589676412928 13027963499574353640203 Ns78p62 Ns78p63 

noncomputable def Ns78p65 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin BSN.quadSignNeg 5 6 287396 1000 69 67108864 33554432 1125899906842624 Bool.false 27196841996 1137 120242927 62 27397080 8 

noncomputable def Ns78p66 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 287396 1000 4 36 67108864 33554432 1125899906842624 Bool.false 27196841996 1137 

noncomputable def Ns78p67 := Ns78p66 93032624 61 33554424 8 108007536 61 30011992 8 Bool.true 53585065 25213 Bool.false 37980560 Bool.true 49174965 3537118876014220 1 Bool.false 56645061 Bool.false Bool.false 49883916 Bool.false Bool.true 2953780 

noncomputable def Ns78p68 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 287396 1000 131 56 67108864 33554432 1125899906842624 Bool.false 27196841996 1137 

noncomputable def Ns78p69 := Ns78p68 46516304 61 47453136 16 73726608 61 38745320 8 Bool.true 67108824 1205 Bool.false 18961515 Bool.false 104905767 3537118876014220 1 Bool.false 18710225 Bool.false Bool.false 508585 Bool.false Bool.true 53585065 

noncomputable def Ns78p70 := nat_lit 141237233945122601479454456409658656402080570807789 

noncomputable def Ns78p71 := nat_lit 348506283405900874030257572159118151205781504000 

noncomputable def Ns78p72 := nat_lit 282352896000000000000000000 

noncomputable def Ns78p73 := nat_lit 941126850148598407642050068480000 

noncomputable def Ns78p74 := nat_lit 1622858845656276093936793376501268480 

noncomputable abbrev qz11 := (@Eq.refl Real qz335)

noncomputable def Ns78p75 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 287396 1000 330386843264 16000000 574792 4000 2000 Ns78p73 Ns78p74 qz11 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns78p76 := nat_lit 1480979738212408769689204360842142352954680366153481584640 

noncomputable abbrev qz845 := (@instHSub Real Real.instSub)

noncomputable abbrev qz634 := qz845

noncomputable abbrev qz339 := qz634

noncomputable abbrev qz12 := qz339

noncomputable abbrev qz340 := (Real.log (Enclosure.sfrac Bool.false 330386843264 16000000))

noncomputable abbrev qz341 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz342 := (@HMul.hMul Real Real Real qz629 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz343 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz344 := (Enclosure.sfrac Bool.false 287396 2000)

noncomputable abbrev qz13 := (@HSub.hSub Real Real Real qz339 (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 287396 4000) qz340) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 574792)))))) qz344)

noncomputable abbrev qz345 := (@HSub.hSub Real Real Real qz12 qz13 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 287396 2000) (Real.log Real.pi)))

noncomputable def Ns78p77 := @Enclosure.Real.IsNear.addLit_ft_p qz345 (Enclosure.sfrac Bool.true Ns78p73 Ns78p74) 912575891246273391793 2251799813685248000 4781540107444894648481 Ns78p72 Ns78p73 Ns78p74 0 1 Ns78p76 

noncomputable def Ns78p78 := nat_lit 3062096568766247577832757657600 

noncomputable abbrev qz346 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 287396 2000) (Real.log Real.pi))

noncomputable def Ns78p79 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz346 256597318055337629117 450359962737049600 9231126109570778351 1102941000000000000000000 2759774767089 16777216000 71849 8388608000 Ns78p78 912575891246273391793 2251799813685248000 

noncomputable def Ns78p80 := nat_lit 2565973180553376291170000 

noncomputable abbrev qz14 := (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 287396 4000) qz340) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 574792))))))

noncomputable def Ns78p81 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz344 1606565719903630912689 2251799813685248000 9231126109570778351 1102941000000000000000000 287396 2000 0 1 Ns78p80 256597318055337629117 450359962737049600 9231126109570778351 1102941000000000000000000 

noncomputable def Ns78p82 := nat_lit 3617664388752102413646632802815311872 

noncomputable def Ns78p83 := nat_lit 12011198784778350815608832 

noncomputable def Ns78p84 := nat_lit 1208925819614629174706176 

noncomputable def Ns78p85 := nat_lit 4544175227393224305886959413795399936374855258995853477537665583971041280 

noncomputable def Ns78p86 := nat_lit 20253559263429916764201556866620783342593757069803765750762391319085056 

noncomputable def Ns78p87 := nat_lit 1515074318646139176479275121781273840883393532538827303073915863040 

noncomputable def Ns78p88 := BSN.log_dyadic_bound 68242843264 592530843264 4 3 Ns78p85 33554432 8823528 Ns78p86 Ns78p87 7763497 660773686528 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 68242843264) (BSN.artanhQ 592530843264) 0 3 Ns78p86 Ns78p85 Ns78p87 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz347 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns78p89 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 287396 4000) qz340 287396 4000 0 1 22372601152916161 2251799813685248 62500007720587 551470500000000000000 1607449020235873251689 2251799813685248000 4490563054716455363 551470500000000000000000 (Enclosure.Real.IsNear.const Bool.false 287396 4000) (BSN.isNear_log_sfrac 330386843264 16000000 22372601152916161 2251799813685248 62500007720587 551470500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 330386843264) qz347)) Bool.false Ns78p83 Ns78p84 1000000123529392 8823528000000000000000 22372601152916161 2251799813685248 62500007720587 551470500000000000000 (BSN.log_rat_reduce_isNear 330386843264 16000000 14 660773686528 524288000000 7763497 33554432 24973259072661432 36028797018963968 8823528 1000000000000000 rfl rfl rfl rfl (Ns78p88 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns78p90 := BSN.arctan_dyadic_bound_f 1000 574792 1 0 4194304 1102941 0 1 1 0 1 1 7297 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 574792) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 574792) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz15 := qz342

noncomputable abbrev qz16 := qz343

noncomputable abbrev qz348 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz17 := (@Enclosure.Real.IsNear.mulLit_ff qz348 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz349 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 574792)))

noncomputable def Ns78p91 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz349 884279719003555 562949953421312 1 2000000000000000 7297 4194304 1 1102941 3704830116725371437056 883300332242339 562949953421312 2000000001102941 2205882000000000000000 qz17 (Ns78p90 rfl) rfl rfl 

noncomputable abbrev qz18 := qz341

noncomputable abbrev qz350 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns78p92 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 287396 4000) qz340) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz349)) 1607449020235873251689 2251799813685248000 4490563054716455363 551470500000000000000000 883300332242339 2251799813685248 2000000001102941 8823528000000000000000 Ns78p82 1606565719903630912689 2251799813685248000 9231126109570778351 1102941000000000000000000 (Ns78p89 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz349) 1 4 0 1 883300332242339 562949953421312 2000000001102941 2205882000000000000000 883300332242339 2251799813685248 2000000001102941 8823528000000000000000 qz350 Ns78p91 rfl) 

noncomputable def Ns78p93 := @Ns78p77 Ns78p70 Ns78p71 4781540107444894648481 Ns78p72 (@Ns78p79 4781540107444894648481 Ns78p72 (Ns78p81 (Ns78p92 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 287396 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz344 (Real.log Real.pi) 287396 2000 0 1 38410761 33554432 1 16777216 2759774767089 16777216000 71849 8388608000 (Enclosure.Real.IsNear.const Bool.false 287396 2000) RS079to096.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns78p73 Ns78p74) 

noncomputable abbrev qz351 := (@instHAdd Real Real.instAdd)

noncomputable def Ns78p94 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns78p70 Ns78p71 4781540107444894648481 Ns78p72 3399605249 8388608 143 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz351 qz345 (Enclosure.sfrac Bool.true Ns78p73 Ns78p74)) Bool.false Ns78p70 Ns78p71 4781540107444894648481 Ns78p72 Ns78p75 (Ns78p93 rfl rfl)) 

noncomputable def Ns78p95 := nat_lit 1897856981032344011931648 

noncomputable def Ns78p96 := nat_lit 139658486353021164696303737114155588002644403326912269454159779364726663179079181151905 

noncomputable def Ns78p97 := nat_lit 2753733154729970958028337252922338050165611694356407771374444090804896824278383046164480 

noncomputable def Ns78p98 := nat_lit 279942894790251112452650849237137188578479864713103729727810663417219885806656171681 

noncomputable def Ns78p99 := nat_lit 365318985285395024784443591066880698844465422265710918722287728690656238034853745405601 

noncomputable def Ns78p100 := nat_lit 50485107836716134230519516303576197586369547729867475808531474998089775111770355846348800 

noncomputable abbrev qz352 := (BSN.sinEvenQ 17179869184)

noncomputable abbrev qz353 := (BSN.sinOddQ 17179869184)

noncomputable def Ns78p101 := BSN.sin_dyadic_bound_f 26970169827 17179869184 3 2 8388608 2208037 Ns78p96 Ns78p97 Ns78p98 Ns78p99 Ns78p100 Ns78p98 8388603 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26970169827) qz352 0 2 Ns78p96 Ns78p97 Ns78p98 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26970169827) qz353 0 2 Ns78p99 Ns78p100 Ns78p98 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz354 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable abbrev qz355 := (@Nat.cast Real Real.instNatCast Ns78p84)

noncomputable def Ns78p102 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3399605249) qz354) Bool.false 3399605249 8388608 143 8388608 Bool.true 8388603 8388608 1 1102941 (Ns78p94 rfl) (Enclosure.sfrac_false_div 3399605249 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3399605249) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns78p95) qz355) 226375608064910080 72057594037927936 Bool.false 8388603 8388608 64 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q1 3399605249 8388608 226375608064910080 72057594037927936 64 Ns78p95 Ns78p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388603 8388608 Ns78p95 Ns78p84 26970169827 17179869184 2208037 2205882 (Ns78p101 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p103 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns78p70 Ns78p71 4781540107444894648481 Ns78p72 27196841996 67108864 1137 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz351 qz345 (Enclosure.sfrac Bool.true Ns78p73 Ns78p74)) Bool.false Ns78p70 Ns78p71 4781540107444894648481 Ns78p72 Ns78p75 (Ns78p93 rfl rfl)) 

noncomputable def Ns78p104 := Ns78p69 25213 BSN.abs_quadSignPos (BSN.cos_quad_nat3 131 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 18710225 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 56 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 508585 67108864) qz11 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 8388603 8388608 166109171 9252139696128 67108824 67108864 1205 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 8388603 8388608 166109171 9252139696128 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 8388603 8388608 166109171 9252139696128 8388603 8388608 166109171 9252139696128 (Ns78p102 rfl rfl) rfl)) rfl) (Ns78p103 rfl) RS079to096.d7 

noncomputable def Ns78p105 := nat_lit 129268329262454813272017800625 

noncomputable def Ns78p106 := nat_lit 2433889152438200450873670154321920 

noncomputable def Ns78p107 := nat_lit 17037224067067403156115691080253440 

noncomputable abbrev qz356 := (BSN.sinEvenQ 67108864)

noncomputable def Ns78p108 := BSN.sin_dyadic_bound_f 18961515 67108864 2 1 67108864 33554432 Ns78p105 Ns78p106 Ns78p105 Ns78p105 Ns78p107 Ns78p105 18710225 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 18961515) qz356 0 1 Ns78p105 Ns78p106 Ns78p105 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 18961515) (BSN.sinOddQ 67108864) 0 1 Ns78p105 Ns78p107 Ns78p105 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p109 := nat_lit 997938952635461765111496292767046518842676893828541158848159975365428854894931497876705309449587745441 

noncomputable def Ns78p110 := nat_lit 3996645342911614855169325114413848961633120431781532997847909552396155328908156533147964360867027353600 

noncomputable def Ns78p111 := nat_lit 1776611056697744676634319132280931317816999675156932122398323165788263891581758178579529214681761 

noncomputable def Ns78p112 := nat_lit 6039858793126640634408267438438861613075854072669661583166382154794843276207811931474762048501594940065 

noncomputable def Ns78p113 := nat_lit 363694726204956951820408585411660255508613959292119502804159769268050134930642244516464756838899489177600 

noncomputable abbrev qz357 := (BSN.cosEvenQ 67108864)

noncomputable def Ns78p114 := BSN.cos_dyadic_bound_f 104905767 67108864 4 3 67108864 33554432 Ns78p109 Ns78p110 Ns78p111 Ns78p112 Ns78p113 Ns78p111 508585 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 104905767) qz357 0 3 Ns78p109 Ns78p110 Ns78p111 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 104905767) (BSN.cosOddQ 67108864) 0 3 Ns78p112 Ns78p113 Ns78p111 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p115 := nat_lit 70908909597407591970959124962940837942398435097510794808524800000 

noncomputable def Ns78p116 := nat_lit 16586685937797756904922089360178093090225977525586485022553978961920 

noncomputable def Ns78p117 := nat_lit 4330030054980472370453530696502712633416772308539801600000000 

noncomputable def Ns78p118 := nat_lit 212718068732112814968136467827429508401928471747915304822374400000 

noncomputable def Ns78p119 := nat_lit 746400867200899060721494021208014189060168988651391826014929053286400 

noncomputable def Ns78p120 := BSN.cos_dyadic_bound_f 37980560 67108864 3 2 67108864 33554432 Ns78p115 Ns78p116 Ns78p117 Ns78p118 Ns78p119 Ns78p117 56645061 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 37980560) qz357 0 2 Ns78p115 Ns78p116 Ns78p117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 37980560) (BSN.cosOddQ 67108864) 0 2 Ns78p118 Ns78p119 Ns78p117 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p121 := nat_lit 199287285852559051679210382437740175129855288516587492093387190625 

noncomputable def Ns78p122 := nat_lit 34194202232097064163455116849847715154713247826696298750390625 

noncomputable def Ns78p123 := nat_lit 597793469153212960909304237079520829959256439054109083682660790625 

noncomputable def Ns78p124 := BSN.cos_dyadic_bound_f 49174965 67108864 3 2 67108864 33554432 Ns78p121 Ns78p116 Ns78p122 Ns78p123 Ns78p119 Ns78p122 49883916 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 49174965) qz357 0 2 Ns78p121 Ns78p116 Ns78p122 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 49174965) (BSN.cosOddQ 67108864) 0 2 Ns78p123 Ns78p119 Ns78p122 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p125 := Ns78p67 42916 BSN.abs_quadSignPos (BSN.cos_quad_nat0 4 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 56645061 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 49883916 67108864) qz11 rfl rfl (Ns78p104 RS079to096.d9 RS079to096.d11 RS079to096.d13 RS079to096.d17 (Ns78p108 rfl rfl) (Ns78p114 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns78p103 rfl) RS079to096.d19 RS079to096.d21 RS079to096.d23 RS079to096.d25 RS079to096.d17 (Ns78p120 rfl rfl) (Ns78p124 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns78p126 := nat_lit 3501517986502480488318579029761751929560765831598771593291849990400 

noncomputable def Ns78p127 := nat_lit 149280173440179812144298804241602837812033797730278365202985810657280 

noncomputable def Ns78p128 := nat_lit 3253139599337486749433522389409051663826419779226059395293184256 

noncomputable def Ns78p129 := nat_lit 9165375357678997728954338422650307065203429641211369124362465771776 

noncomputable def Ns78p130 := nat_lit 2736803179736629889312144744429385359887286291721770028721406528716800 

noncomputable def Ns78p131 := BSN.sin_dyadic_bound_f 86903614 67108864 3 2 67108864 33554432 Ns78p126 Ns78p127 Ns78p128 Ns78p129 Ns78p130 Ns78p128 64572085 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 86903614) qz356 0 2 Ns78p126 Ns78p127 Ns78p128 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 86903614) (BSN.sinOddQ 67108864) 0 2 Ns78p129 Ns78p130 Ns78p128 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz635 := (BSN.cos_quad_nat1 69 rfl)

noncomputable def Ns78p132 := Ns78p65 Bool.true 2953780 42916 Bool.true 86903614 3537118876014220 1 Bool.false 64572085 Bool.true Bool.true 29315225 50665 BSN.abs_quadSignNeg qz635 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 64572085 67108864) qz11 rfl (Ns78p125 rfl rfl) (Ns78p103 rfl) RS079to096.d27 RS079to096.d29 RS079to096.d17 (Ns78p131 rfl rfl) rfl 

noncomputable def Ns78p133 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 6) 29315225 67108864 50665 67108864 29315225 67108864 50665 67108864 3934622895308800 29315225 33554432 50665 33554432 (Ns78p132 rfl rfl rfl rfl) 

noncomputable def Ns78p134 := @Enclosure.Real.IsNear.mulLit_ff qz633 (Zeta.RiemannSiegel.correction qz10) 3225631 8388608 1 8388608 9035446353077 17592186044416 4037857277218537 6467714422671409152 29145015855322116587 147573952589676412928 

noncomputable abbrev qz636 := (@HPow.hPow Real Real Real qz7 qz8 qz9)

noncomputable def Ns78p135 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz636 1 1 0 1 3225631 8388608 1 8388608 3225631 8388608 1 8388608 

noncomputable abbrev qz358 := (@Enclosure.Real.IsNear.of_eq qz8 (@HMul.hMul Real Real Real qz5 qz4 qz3) Bool.false 95924809561 2097152000 71849 2097152000 (BSN.t_div_two_pi_mk qz4 287396 1000 qz11) (@Enclosure.Real.IsNear.mulLit_ff qz4 qz3 287396 1000 0 1 1335089 8388608 1 8388608 95924809561 2097152000 71849 2097152000 (Enclosure.Real.IsNear.const Bool.false 287396 1000) RS079to096.d32 rfl))

noncomputable def Ns78p136 := @Enclosure.Real.IsNear.sqrt_image qz8 95924809561 2097152000 71849 2097152000 28366794 28366816 4194304 qz358 

noncomputable abbrev qz846 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 287396 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz637 := qz846

noncomputable abbrev qz359 := qz637

noncomputable abbrev qz19 := qz359

noncomputable def Ns78p137 := @Enclosure.Real.IsNear.sqrt_image qz19 28366805 4194304 11 4194304 10907747 10907752 4194304 (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 56733610 8388608 22 8388608 28366805 4194304 11 4194304 (Ns78p136 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz638 := (Real.sqrt qz846)

noncomputable abbrev qz360 := qz638

noncomputable abbrev qz20 := qz360

noncomputable def Ns78p138 := @Enclosure.Real.IsNear.inv_image qz20 21815499 8388608 5 8388608 1612815 1612816 4194304 (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 21815499 8388608 5 8388608 21815499 8388608 5 8388608 (Ns78p137 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns78p139 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz20) Bool.false 3225631 8388608 1 8388608 3225631 8388608 1 8388608 (Ns78p138 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz21 := (@HMul.hMul Real Real Real qz336 qz334 qz338)

noncomputable abbrev qz639 := (@HMul.hMul Real Real Real qz841 qz844 qz844)

noncomputable abbrev qz640 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz361 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz639 qz632) qz640)

noncomputable abbrev qz22 := (Real.cos (@HMul.hMul Real Real Real qz336 qz334 qz361))

noncomputable def Ns78p140 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz10) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz21)) qz22) Bool.false 9035446353077 

noncomputable def Ns78p141 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz21)) qz22 101463727 8388608 21449 

noncomputable def Ns78p142 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz21)) Bool.false 101463727 8388608 21449 8388608 101463727 8388608 21449 

noncomputable def Ns78p143 := @Enclosure.Real.IsNear.recentre' (Real.cos qz21) Bool.false 693536 8388608 161697407 9252139696128 21673 262144 161697407 9252139696128 

noncomputable def Ns78p144 := @Enclosure.Real.IsNear.cos_image qz21 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 40224713) qz354) Bool.false 40224713 8388608 139 8388608 Bool.false 693536 8388608 1 

noncomputable def Ns78p145 := nat_lit 296846829526980717427093389 

noncomputable def Ns78p146 := nat_lit 18014398509481984000000000000000 

noncomputable def Ns78p147 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz10 884279719003555 140737488355328 1 500000000000000 3200981 4194304 11 4194304 2830562579215718487455 590295810358705651712 Ns78p145 

noncomputable def Ns78p148 := @Enclosure.Real.IsNear.subLit_ff_p qz19 qz1 28366805 4194304 11 4194304 6 1 0 1 3200981 3200981 4194304 11 

noncomputable abbrev qz362 := (Enclosure.Real.IsNear.const Bool.false 6 1)

noncomputable def Ns78p149 := @Ns78p148 4194304 (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 56733610 8388608 22 8388608 28366805 4194304 11 4194304 (Ns78p136 rfl rfl rfl rfl rfl rfl) rfl) qz362 

noncomputable def Ns78p150 := @Enclosure.Real.IsNear.recentre' qz21 Bool.false 2830562579215718487455 590295810358705651712 Ns78p145 Ns78p146 40224713 8388608 139 8388608 (@Ns78p147 Ns78p146 RS079to096.d31 (Ns78p149 rfl rfl) rfl) 

noncomputable def Ns78p151 := BSN.sin_dyadic_bound_f 1421985996 17179869184 1 0 8388608 2208037 0 1 1 0 1 1 693536 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 1421985996) qz352 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 1421985996) qz353 0 0 rfl) rfl rfl 

noncomputable def Ns78p152 := @Ns78p144 1102941 (Ns78p150 rfl) (Enclosure.sfrac_false_div 40224713 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 40224713) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 100063368837817031458816) qz355) 226375608064910080 72057594037927936 Bool.false 693536 8388608 0 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q3 40224713 8388608 226375608064910080 72057594037927936 0 100063368837817031458816 Ns78p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 693536 8388608 100063368837817031458816 Ns78p84 1421985996 17179869184 2208037 2205882 (Ns78p151 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p153 := @Enclosure.Real.IsNear.inv_image (Real.cos qz21) 21673 262144 161697407 9252139696128 50721139 50742588 4194304 (Ns78p143 (Ns78p152 rfl rfl) rfl) rfl 

noncomputable def Ns78p154 := @Enclosure.Real.IsNear.recentre' qz22 Bool.false 178102 4194304 

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz336 qz334 qz361)

noncomputable def Ns78p155 := @Enclosure.Real.IsNear.cos_image qz23 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 12820483)) qz354) Bool.true 12820483 8388608 

noncomputable def Ns78p156 := nat_lit 3783938746125197773895006645 

noncomputable def Ns78p157 := nat_lit 2475880078570760549798248448 

noncomputable def Ns78p158 := nat_lit 3145471231985066477421435152482737 

noncomputable def Ns78p159 := @Enclosure.Real.IsNear.recentre' qz23 Bool.true Ns78p156 Ns78p157 Ns78p158 

noncomputable def Ns78p160 := nat_lit 75557863725914323419136000000000000000 

noncomputable abbrev qz24 := qz361

noncomputable def Ns78p161 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz24 884279719003555 140737488355328 1 500000000000000 4279119677639 

noncomputable abbrev qz363 := (@HSub.hSub Real Real Real qz634 qz639 qz632)

noncomputable abbrev qz25 := qz363

noncomputable abbrev qz364 := qz640

noncomputable abbrev qz26 := qz364

noncomputable def Ns78p162 := @Enclosure.Real.IsNear.subLit_tf qz25 qz26 3179608049863 17592186044416 116559047 17592186044416 1 16 

noncomputable abbrev qz365 := qz639

noncomputable abbrev qz27 := qz365

noncomputable def Ns78p163 := @Enclosure.Real.IsNear.subLit_ff_n qz27 qz10 10246279362361 17592186044416 70421703 17592186044416 3200981 4194304 11 4194304 

noncomputable def Ns78p164 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz10 3200981 4194304 11 4194304 3200981 4194304 11 4194304 10246279362361 17592186044416 

noncomputable def Ns78p165 := nat_lit 13263898910658662959279069637217168093892770825257852854795395272089069601540692096022649841 

noncomputable def Ns78p166 := nat_lit 58158844227896986633558482781719779619497718984807332131428259197799420928759449934993817600 

noncomputable def Ns78p167 := nat_lit 19717536147327816950464312272135745411018501816524481377434718337395115128735019211761 

noncomputable def Ns78p168 := nat_lit 80293905398226501000819594854862178941074881952287786370021721248538612408013479409521433585 

noncomputable def Ns78p169 := nat_lit 5292454824738625783653821933136499945374292427617467223959971586999747304517109944084437401600 

noncomputable def Ns78p170 := BSN.cos_dyadic_bound_f 12820483 8388608 4 3 4194304 1102941 Ns78p165 Ns78p166 Ns78p167 Ns78p168 Ns78p169 Ns78p167 178102 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 12820483) (BSN.cosEvenQ 8388608) 0 3 Ns78p165 Ns78p166 Ns78p167 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 12820483) (BSN.cosOddQ 8388608) 0 3 Ns78p168 Ns78p169 Ns78p167 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz366 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns78p171 := @Ns78p154 197208979 4626069848064 89051 2097152 197208979 4626069848064 (@Ns78p155 175 4194304 Bool.false 178102 4194304 1 1102941 (@Ns78p159 Ns78p160 12820483 8388608 175 4194304 (@Ns78p161 17592186044416 116559047 17592186044416 Ns78p156 Ns78p157 Ns78p158 Ns78p160 RS079to096.d31 (@Ns78p162 0 1 68465914842224 4279119677639 17592186044416 116559047 17592186044416 (@Ns78p163 13336242761972580352 3179608049863 17592186044416 116559047 17592186044416 (@Ns78p164 70421703 17592186044416 (Ns78p149 rfl rfl) (Ns78p149 rfl rfl) rfl) (Ns78p149 rfl rfl) rfl rfl) qz366 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 12820483 8388608) (BSN.cos_neg_of_bound 12820483 8388608 Bool.false 178102 4194304 1 1102941 (Ns78p170 rfl rfl)) rfl rfl) 

noncomputable abbrev qz28 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 6) (Enclosure.sfrac Bool.false 1 1) Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 6 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1))

noncomputable def Ns78p172 := @Ns78p134 13027963499574353640203 Ns78p62 (Ns78p135 qz28 (@Enclosure.Real.IsNear.of_eq qz636 (@Inv.inv Real Real.instInv qz20) Bool.false 3225631 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz8 (BSN.t_div_two_pi_nonneg qz4 287396 1000 qz11)) Ns78p139) rfl) (@Ns78p140 17592186044416 4037857277218537 6467714422671409152 (BSN.correction_mk qz10 (BSN.cos_two_pi_p_ne_zero_mk qz4 287396 1000 6 qz11 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 287396 1000 6 qz11 rfl rfl rfl))) (@Ns78p141 8388608 89051 2097152 197208979 4626069848064 9035446353077 17592186044416 4037857277218537 6467714422671409152 (@Ns78p142 8388608 (Ns78p153 rfl rfl rfl rfl rfl) rfl) (Ns78p171 rfl) rfl)) 

noncomputable def Ns78p173 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 158074738888800874987 147573952589676412928 94949651305736089811723 Ns78p62 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 6) (@HMul.hMul Real Real Real qz5 qz633 (Zeta.RiemannSiegel.correction qz10))) Bool.true 158074738888800874987 147573952589676412928 94949651305736089811723 Ns78p62 (BSN.hardyZApproximantRS₀_eq qz4 6 (@BSN.floor_sqrt_eq_dec qz4 287396 1000 6 qz11 rfl rfl rfl)) (@Ns78p64 158074738888800874987 147573952589676412928 94949651305736089811723 Ns78p62 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 6) (@HAdd.hAdd Real Real Real qz351 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 6)) Bool.true 29315225 33554432 50665 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 6) (Ns78p133 (Ns78p132 rfl rfl rfl rfl) rfl rfl)) (Ns78p172 rfl) rfl rfl)) 

theorem RS079to096.d33 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 158074738888800874987 147573952589676412928 94949651305736089811723 Ns78p62 := Ns78p173 

theorem RS079to096.d34 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS079to096.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS079to096.d3 a b h)) 

noncomputable def Ns78p174 := nat_lit 108510241895473528367480832 

noncomputable def Ns78p175 := nat_lit 10018185423653988865968963584 

noncomputable abbrev qz847 := (Enclosure.sfrac Bool.false 289039 1000)

noncomputable abbrev qz641 := qz847

noncomputable abbrev qz367 := qz641

noncomputable abbrev qz29 := qz367

noncomputable abbrev qz848 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 289039 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz642 := qz848

noncomputable abbrev qz368 := qz642

noncomputable abbrev qz30 := qz368

noncomputable abbrev qz849 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 289039 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz643 := qz849

noncomputable abbrev qz369 := qz643

noncomputable abbrev qz31 := qz369

noncomputable abbrev qz644 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz30 qz9))

noncomputable def Ns78p176 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz29) qz29 6) (@HMul.hMul Real Real Real qz5 qz644 (Zeta.RiemannSiegel.correction qz31)) 37390319 16777216 25479 16777216 60647064637170166155 295147905179352825856 10843045576989619485043 Ns78p174 Ns78p175 

noncomputable def Ns78p177 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz29) qz29 Real.sin BSN.quadSignNeg 5 6 289039 1000 69 67108864 33554432 1125899906842624 Bool.false 27407759994 1144 120242927 62 27397080 8 

noncomputable def Ns78p178 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz29) qz29 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 289039 1000 4 36 67108864 33554432 1125899906842624 Bool.false 27407759994 1144 

noncomputable def Ns78p179 := Ns78p178 93032624 61 33554424 8 108007536 61 30011992 8 Bool.false 65283947 25359 Bool.false 96045957 Bool.true 15713349 3537118876014220 1 Bool.false 9338000 Bool.false Bool.false 65277635 Bool.false Bool.false 99145987 

noncomputable def Ns78p180 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz29) qz29 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 289039 1000 132 57 67108864 33554432 1125899906842624 Bool.false 27407759994 1144 

noncomputable def Ns78p181 := Ns78p180 46516304 61 47453136 16 73726608 61 38745320 8 Bool.false 67108848 1213 Bool.false 48038869 Bool.false 89276591 3537118876014220 1 Bool.false 50636696 Bool.false Bool.false 65177859 Bool.true Bool.false 65283947 

noncomputable def Ns78p182 := nat_lit 3860988477297260744201267407260667536040637436311158891 

noncomputable def Ns78p183 := nat_lit 9453766038665348612267769657636310607592970361241600 

noncomputable def Ns78p184 := nat_lit 376470528000000000000000000 

noncomputable def Ns78p185 := nat_lit 968337520146193125362161215520000 

noncomputable def Ns78p186 := nat_lit 1679326196087300468965212313612111680 

noncomputable abbrev qz370 := (@Eq.refl Real qz641)

noncomputable abbrev qz32 := qz370

noncomputable def Ns78p187 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz29 289039 1000 334175174084 16000000 578078 4000 2000 Ns78p185 Ns78p186 qz32 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns78p188 := nat_lit 1235516312735123438144405570323413611533003979619570845120 

noncomputable abbrev qz371 := (Real.log (Enclosure.sfrac Bool.false 334175174084 16000000))

noncomputable abbrev qz372 := (Enclosure.sfrac Bool.false 289039 2000)

noncomputable abbrev qz33 := (@HSub.hSub Real Real Real qz339 (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 289039 4000) qz371) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 578078)))))) qz372)

noncomputable abbrev qz373 := (@HSub.hSub Real Real Real qz12 qz33 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 289039 2000) (Real.log Real.pi)))

noncomputable def Ns78p189 := @Enclosure.Real.IsNear.addLit_ft_p qz373 (Enclosure.sfrac Bool.true Ns78p185 Ns78p186) 735722493947621644259 1801439850948198400 6411346106026559943197 Ns78p184 Ns78p185 Ns78p186 0 1 Ns78p188 

noncomputable def Ns78p190 := nat_lit 246867503940358820240168058880000 

noncomputable abbrev qz374 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 289039 2000) (Real.log Real.pi))

noncomputable def Ns78p191 := @Enclosure.Real.IsNear.subLit_ff_p qz33 qz374 5168725596393344202607 9007199254740992000 6188313243942160381 735294000000000000000000 11102207948679 67108864000 289039 33554432000 Ns78p190 735722493947621644259 1801439850948198400 

noncomputable def Ns78p192 := nat_lit 10337451192786688405214000 

noncomputable abbrev qz34 := (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 289039 4000) qz371) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 578078))))))

noncomputable def Ns78p193 := @Enclosure.Real.IsNear.subLit_ff_p qz34 qz372 6470441529088884995951 9007199254740992000 6188313243942160381 735294000000000000000000 289039 2000 0 1 Ns78p192 5168725596393344202607 9007199254740992000 6188313243942160381 735294000000000000000000 

noncomputable def Ns78p194 := nat_lit 2205882000000000000000000 

noncomputable def Ns78p195 := nat_lit 14570139029663642411186067822868430848 

noncomputable def Ns78p196 := nat_lit 12024981853279534614315008 

noncomputable def Ns78p197 := nat_lit 4721303753962459208888219344295522614670779572514738976413340998032199680 

noncomputable def Ns78p198 := nat_lit 23165886341843663558682443308676644397341366257135489548399479912820736 

noncomputable def Ns78p199 := nat_lit 2095145657829979157127962754947997569351732229676341108718210314240 

noncomputable def Ns78p200 := BSN.log_dyadic_bound 72031174084 596319174084 4 3 Ns78p197 33554432 8823528 Ns78p198 Ns78p199 8146054 668350348168 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 72031174084) (BSN.artanhQ 596319174084) 0 3 Ns78p198 Ns78p197 Ns78p199 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns78p201 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 289039 4000) qz371 289039 4000 0 1 22398274118601409 2251799813685248 62500007720587 551470500000000000000 6473974752966432655951 9007199254740992000 18064939731550745893 Ns78p194 (Enclosure.Real.IsNear.const Bool.false 289039 4000) (BSN.isNear_log_sfrac 334175174084 16000000 22398274118601409 2251799813685248 62500007720587 551470500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 334175174084) qz347)) Bool.false Ns78p196 Ns78p84 1000000123529392 8823528000000000000000 22398274118601409 2251799813685248 62500007720587 551470500000000000000 (BSN.log_rat_reduce_isNear 334175174084 16000000 14 668350348168 524288000000 8146054 33554432 24973259072661432 36028797018963968 8823528 1000000000000000 rfl rfl rfl rfl (Ns78p200 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns78p202 := BSN.arctan_dyadic_bound_f 1000 578078 1 0 4194304 1102941 0 1 1 0 1 1 7255 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 578078) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 578078) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz375 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 578078)))

noncomputable def Ns78p203 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz375 884279719003555 562949953421312 1 2000000000000000 7255 4194304 1 1102941 3704853760623415132160 883305969386915 562949953421312 2000000001102941 2205882000000000000000 qz17 (Ns78p202 rfl) rfl rfl 

noncomputable def Ns78p204 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 289039 4000) qz371) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz375)) 6473974752966432655951 9007199254740992000 18064939731550745893 Ns78p194 883305969386915 2251799813685248 2000000001102941 8823528000000000000000 Ns78p195 6470441529088884995951 9007199254740992000 6188313243942160381 735294000000000000000000 (Ns78p201 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz375) 1 4 0 1 883305969386915 562949953421312 2000000001102941 2205882000000000000000 883305969386915 2251799813685248 2000000001102941 8823528000000000000000 qz350 Ns78p203 rfl) 

noncomputable def Ns78p205 := @Ns78p189 Ns78p182 Ns78p183 6411346106026559943197 Ns78p184 (@Ns78p191 6411346106026559943197 Ns78p184 (Ns78p193 (Ns78p204 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 289039 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz372 (Real.log Real.pi) 289039 2000 0 1 38410761 33554432 1 16777216 11102207948679 67108864000 289039 33554432000 (Enclosure.Real.IsNear.const Bool.false 289039 2000) RS079to096.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns78p185 Ns78p186) 

noncomputable def Ns78p206 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz29) Bool.false Ns78p182 Ns78p183 6411346106026559943197 Ns78p184 3425969999 8388608 9 524288 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz29) (@HAdd.hAdd Real Real Real qz351 qz373 (Enclosure.sfrac Bool.true Ns78p185 Ns78p186)) Bool.false Ns78p182 Ns78p183 6411346106026559943197 Ns78p184 Ns78p187 (Ns78p205 rfl rfl)) 

noncomputable def Ns78p207 := nat_lit 1899465412218926680506368 

noncomputable def Ns78p208 := nat_lit 140133483495814926960557508559802529113147570838812449738742664632464697864974906228225 

noncomputable def Ns78p209 := nat_lit 281846544065720351168380012727524052977255601813896728019524374238890182872592350721 

noncomputable def Ns78p210 := nat_lit 366559943322456499566235145255066823020089985984429154613246796479116005540759604887041 

noncomputable def Ns78p211 := BSN.sin_dyadic_bound_f 26993027009 17179869184 3 2 8388608 2208037 Ns78p208 Ns78p97 Ns78p209 Ns78p210 Ns78p100 Ns78p209 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26993027009) qz352 0 2 Ns78p208 Ns78p97 Ns78p209 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26993027009) qz353 0 2 Ns78p210 Ns78p100 Ns78p209 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p212 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz29) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3425969999) qz354) Bool.false 3425969999 8388608 9 524288 Bool.false 8388606 8388608 1 1102941 (Ns78p206 rfl) (Enclosure.sfrac_false_div 3425969999 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3425969999) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns78p207) qz355) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 64 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q3 3425969999 8388608 226375608064910080 72057594037927936 64 Ns78p207 Ns78p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388606 8388608 Ns78p207 Ns78p84 26993027009 17179869184 2208037 2205882 (Ns78p211 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p213 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz29) Bool.false Ns78p182 Ns78p183 6411346106026559943197 Ns78p184 27407759994 67108864 1144 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz29) (@HAdd.hAdd Real Real Real qz351 qz373 (Enclosure.sfrac Bool.true Ns78p185 Ns78p186)) Bool.false Ns78p182 Ns78p183 6411346106026559943197 Ns78p184 Ns78p187 (Ns78p205 rfl rfl)) 

noncomputable def Ns78p214 := Ns78p181 25359 BSN.abs_quadSignPos (BSN.cos_quad_nat0 132 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 50636696 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 57 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 65177859 67108864) qz32 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 1) Bool.false 4194303 4194304 10450757 578258731008 67108848 67108864 1213 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz29)) Bool.false 4194303 4194304 10450757 578258731008 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz29) qz29) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz29)) Bool.false 8388606 8388608 10450757 578258731008 4194303 4194304 10450757 578258731008 (Ns78p212 rfl rfl) rfl)) rfl) (Ns78p213 rfl) RS079to096.d7 

noncomputable def Ns78p215 := nat_lit 181496309806108077865397292108942178524894401502784572622911450721 

noncomputable def Ns78p216 := nat_lit 28362348726036988624195628521295762996967695480805226219974241 

noncomputable def Ns78p217 := nat_lit 544432204720872159618943485069783944048689269117392107416294403681 

noncomputable def Ns78p218 := BSN.cos_dyadic_bound_f 48038869 67108864 3 2 67108864 33554432 Ns78p215 Ns78p116 Ns78p216 Ns78p217 Ns78p119 Ns78p216 50636696 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 48038869) qz357 0 2 Ns78p215 Ns78p116 Ns78p216 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 48038869) (BSN.cosOddQ 67108864) 0 2 Ns78p217 Ns78p119 Ns78p216 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p219 := nat_lit 3900329623414107973698911930176256772725742868648344207809651324545 

noncomputable def Ns78p220 := nat_lit 4035531931380133470119620096953944544757300279890600770768123521 

noncomputable def Ns78p221 := nat_lit 10208615295338524476926480432209413732637814741244888143015462221441 

noncomputable def Ns78p222 := BSN.sin_dyadic_bound_f 89276591 67108864 3 2 67108864 33554432 Ns78p219 Ns78p127 Ns78p220 Ns78p221 Ns78p130 Ns78p220 65177859 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 89276591) qz356 0 2 Ns78p219 Ns78p127 Ns78p220 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 89276591) (BSN.sinOddQ 67108864) 0 2 Ns78p221 Ns78p130 Ns78p220 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p223 := nat_lit 700430112674202574246317289047684917492143832337790806234887248125624468492584243306500251170248780881 

noncomputable def Ns78p224 := nat_lit 616238827359987407402624782488306987244500655282601567320902963567728568317627696501730208312401 

noncomputable def Ns78p225 := nat_lit 4242215773520693059072177215520520896316406901170491668554956517568824197036405210470871855352926628945 

noncomputable def Ns78p226 := BSN.cos_dyadic_bound_f 96045957 67108864 4 3 67108864 33554432 Ns78p223 Ns78p110 Ns78p224 Ns78p225 Ns78p113 Ns78p224 9338000 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 96045957) qz357 0 3 Ns78p223 Ns78p110 Ns78p224 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 96045957) (BSN.cosOddQ 67108864) 0 3 Ns78p225 Ns78p113 Ns78p224 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p227 := nat_lit 60964220596942289629571231601 

noncomputable def Ns78p228 := nat_lit 486777830487640090174734030864384 

noncomputable def Ns78p229 := nat_lit 7301667457314601352621010462965760 

noncomputable def Ns78p230 := BSN.cos_dyadic_bound_f 15713349 67108864 2 1 67108864 33554432 Ns78p227 Ns78p228 Ns78p227 Ns78p227 Ns78p229 Ns78p227 65277635 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 15713349) qz357 0 1 Ns78p227 Ns78p228 Ns78p227 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 15713349) (BSN.cosOddQ 67108864) 0 1 Ns78p227 Ns78p229 Ns78p227 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p231 := Ns78p179 43164 BSN.abs_quadSignPos (BSN.cos_quad_nat0 4 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 9338000 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 65277635 67108864) qz32 rfl rfl (Ns78p214 RS079to096.d9 RS079to096.d11 RS079to096.d13 RS079to096.d17 (Ns78p218 rfl rfl) (Ns78p222 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns78p213 rfl) RS079to096.d19 RS079to096.d21 RS079to096.d23 RS079to096.d25 RS079to096.d17 (Ns78p226 rfl rfl) (Ns78p230 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns78p232 := nat_lit 1795209032208460399255205512033900767167828197586490941235016130625 

noncomputable def Ns78p233 := nat_lit 855880579153261669541011484125715943581694527094269413437890625 

noncomputable def Ns78p234 := nat_lit 4700352230084481479155805179590679421530893964444561743231857090625 

noncomputable def Ns78p235 := BSN.sin_dyadic_bound_f 73544745 67108864 3 2 67108864 33554432 Ns78p232 Ns78p127 Ns78p233 Ns78p234 Ns78p130 Ns78p233 59682670 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 73544745) qz356 0 2 Ns78p232 Ns78p127 Ns78p233 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 73544745) (BSN.sinOddQ 67108864) 0 2 Ns78p234 Ns78p130 Ns78p233 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p236 := Ns78p177 Bool.false 99145987 43164 Bool.true 73544745 3537118876014220 1 Bool.false 59682670 Bool.true Bool.false 74780638 50958 BSN.abs_quadSignNeg qz635 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 59682670 67108864) qz32 rfl (Ns78p231 rfl rfl) (Ns78p213 rfl) RS079to096.d27 RS079to096.d29 RS079to096.d17 (Ns78p235 rfl rfl) rfl 

noncomputable def Ns78p237 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 6) 74780638 67108864 50958 67108864 74780638 67108864 50958 67108864 10036887330750464 37390319 16777216 25479 16777216 (Ns78p236 rfl rfl rfl rfl) 

noncomputable def Ns78p238 := @Enclosure.Real.IsNear.mulLit_ff qz644 (Zeta.RiemannSiegel.correction qz31) 3221037 8388608 1 8388608 18828428433815 35184372088832 3364171227337651 12935428845342818304 60647064637170166155 295147905179352825856 

noncomputable abbrev qz645 := (@HPow.hPow Real Real Real qz7 qz30 qz9)

noncomputable def Ns78p239 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz645 1 1 0 1 3221037 8388608 1 8388608 3221037 8388608 1 8388608 

noncomputable def Ns78p240 := @Enclosure.Real.IsNear.sqrt_image qz30 385892789471 8388608000 289039 8388608000 28447763 28447785 4194304 (@Enclosure.Real.IsNear.of_eq qz30 (@HMul.hMul Real Real Real qz5 qz29 qz3) Bool.false 385892789471 8388608000 289039 8388608000 (BSN.t_div_two_pi_mk qz29 289039 1000 qz32) (@Enclosure.Real.IsNear.mulLit_ff qz29 qz3 289039 1000 0 1 1335089 8388608 1 8388608 385892789471 8388608000 289039 8388608000 (Enclosure.Real.IsNear.const Bool.false 289039 1000) RS079to096.d32 rfl)) 

noncomputable abbrev qz850 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 289039 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz646 := qz850

noncomputable abbrev qz376 := qz646

noncomputable abbrev qz35 := qz376

noncomputable def Ns78p241 := @Enclosure.Real.IsNear.sqrt_image qz35 14223887 2097152 11 4194304 10923303 10923309 4194304 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 56895548 8388608 22 8388608 14223887 2097152 11 4194304 (Ns78p240 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns78p242 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz35) 5461653 2097152 3 4194304 1610518 1610519 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz35) Bool.false 21846612 8388608 6 8388608 5461653 2097152 3 4194304 (Ns78p241 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns78p243 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz35)) Bool.false 3221037 8388608 1 8388608 3221037 8388608 1 8388608 (Ns78p242 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz36 := (@HMul.hMul Real Real Real qz336 qz334 qz369)

noncomputable abbrev qz647 := (@HMul.hMul Real Real Real qz841 qz849 qz849)

noncomputable abbrev qz377 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz647 qz643) qz640)

noncomputable abbrev qz37 := (Real.cos (@HMul.hMul Real Real Real qz336 qz334 qz377))

noncomputable def Ns78p244 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz31) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz36)) qz37) Bool.false 18828428433815 

noncomputable def Ns78p245 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz36)) qz37 41394353 8388608 3571 

noncomputable def Ns78p246 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz36)) Bool.false 41394353 8388608 3571 8388608 41394353 8388608 3571 

noncomputable def Ns78p247 := @Enclosure.Real.IsNear.recentre' (Real.cos qz36) Bool.false 1699960 8388608 161697407 9252139696128 212495 1048576 161697407 9252139696128 

noncomputable def Ns78p248 := @Enclosure.Real.IsNear.cos_image qz36 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5155275) (@Nat.cast Real Real.instNatCast 1048576)) Bool.false 5155275 1048576 139 8388608 Bool.false 1699960 8388608 1 

noncomputable def Ns78p249 := nat_lit 296846829527676235841073037 

noncomputable def Ns78p250 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz31 884279719003555 140737488355328 1 500000000000000 1640975 2097152 11 4194304 1451080911891858666125 295147905179352825856 Ns78p249 

noncomputable def Ns78p251 := @Enclosure.Real.IsNear.subLit_ff_p qz35 qz1 14223887 2097152 11 4194304 6 1 0 1 1640975 1640975 2097152 11 

noncomputable def Ns78p252 := @Ns78p251 4194304 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 56895548 8388608 22 8388608 14223887 2097152 11 4194304 (Ns78p240 rfl rfl rfl rfl rfl rfl) rfl) qz362 

noncomputable def Ns78p253 := @Enclosure.Real.IsNear.recentre' qz36 Bool.false 1451080911891858666125 295147905179352825856 Ns78p249 Ns78p146 5155275 1048576 139 8388608 (@Ns78p250 Ns78p146 RS079to096.d31 (Ns78p252 rfl rfl) rfl) 

noncomputable def Ns78p254 := nat_lit 151059567034408154210727696570412339456 

noncomputable def Ns78p255 := nat_lit 10453474311811229597594867940303919455928320 

noncomputable def Ns78p256 := nat_lit 73174320182678607183164075582127436191498240 

noncomputable def Ns78p257 := BSN.sin_dyadic_bound_f 3505799372 17179869184 2 1 8388608 2208037 Ns78p254 Ns78p255 Ns78p254 Ns78p254 Ns78p256 Ns78p254 1699960 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 3505799372) qz352 0 1 Ns78p254 Ns78p255 Ns78p254 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 3505799372) qz353 0 1 Ns78p254 Ns78p256 Ns78p254 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p258 := @Ns78p248 1102941 (Ns78p253 rfl) (Enclosure.sfrac_false_div 5155275 1048576) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5155275) (@Nat.cast Real Real.instNatCast 1048576)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 30837337400944424386560) (@Nat.cast Real Real.instNatCast 151115727451828646838272)) 226375608064910080 72057594037927936 Bool.false 1699960 8388608 0 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q3 5155275 1048576 226375608064910080 72057594037927936 0 30837337400944424386560 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1699960 8388608 30837337400944424386560 151115727451828646838272 3505799372 17179869184 2208037 2205882 (Ns78p257 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p259 := @Enclosure.Real.IsNear.inv_image (Real.cos qz36) 212495 1048576 161697407 9252139696128 20695391 20698962 4194304 (Ns78p247 (Ns78p258 rfl rfl) rfl) rfl 

noncomputable def Ns78p260 := @Enclosure.Real.IsNear.recentre' qz37 Bool.false 454855 4194304 

noncomputable abbrev qz38 := (@HMul.hMul Real Real Real qz336 qz334 qz377)

noncomputable abbrev qz378 := (@Nat.cast Real Real.instNatCast 4194304)

noncomputable def Ns78p261 := @Enclosure.Real.IsNear.cos_image qz38 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 6132645)) qz378) Bool.true 6132645 4194304 

noncomputable def Ns78p262 := nat_lit 905018695456818070432090045 

noncomputable def Ns78p263 := nat_lit 618970019642690137449562112 

noncomputable def Ns78p264 := nat_lit 3193542013858962216162314826577947 

noncomputable def Ns78p265 := @Enclosure.Real.IsNear.recentre' qz38 Bool.true Ns78p262 Ns78p263 Ns78p264 

noncomputable abbrev qz39 := qz377

noncomputable def Ns78p266 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz39 884279719003555 140737488355328 1 500000000000000 1023452959519 

noncomputable abbrev qz379 := (@HSub.hSub Real Real Real qz634 qz647 qz643)

noncomputable abbrev qz40 := qz379

noncomputable def Ns78p267 := @Enclosure.Real.IsNear.subLit_tf qz40 qz26 748575052575 4398046511104 118340365 17592186044416 1 16 

noncomputable abbrev qz380 := qz647

noncomputable abbrev qz41 := qz380

noncomputable def Ns78p268 := @Enclosure.Real.IsNear.subLit_ff_n qz41 qz31 2692798950625 4398046511104 72203021 17592186044416 1640975 2097152 11 4194304 

noncomputable def Ns78p269 := @Enclosure.Real.IsNear.mulLit_ff qz31 qz31 1640975 2097152 11 4194304 1640975 2097152 11 4194304 2692798950625 4398046511104 

noncomputable def Ns78p270 := nat_lit 737428772585372878104345561769827174259236918769873190625 

noncomputable def Ns78p271 := nat_lit 3861888762982039923063034508418779142719222587902677483520 

noncomputable def Ns78p272 := nat_lit 2000702908649140995418424321964458159566489578500390625 

noncomputable def Ns78p273 := nat_lit 2208284911938820352322199836665552606458577777152618790625 

noncomputable def Ns78p274 := nat_lit 173784994334191796537836552878845061422365016455620486758400 

noncomputable def Ns78p275 := BSN.cos_dyadic_bound_f 6132645 4194304 3 2 4194304 1102941 Ns78p270 Ns78p271 Ns78p272 Ns78p273 Ns78p274 Ns78p272 454855 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 6132645) (BSN.cosEvenQ 4194304) 0 2 Ns78p270 Ns78p271 Ns78p272 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 6132645) (BSN.cosOddQ 4194304) 0 2 Ns78p273 Ns78p274 Ns78p272 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p276 := @Ns78p260 100258901 2313034924032 454855 4194304 100258901 2313034924032 (@Ns78p261 89 2097152 Bool.false 454855 4194304 1 1102941 (@Ns78p265 Ns78p160 6132645 4194304 89 2097152 (@Ns78p266 4398046511104 118340365 17592186044416 Ns78p262 Ns78p263 Ns78p264 Ns78p160 RS079to096.d31 (@Ns78p267 0 1 16375247352304 1023452959519 4398046511104 118340365 17592186044416 (@Ns78p268 1569875668657766400 748575052575 4398046511104 118340365 17592186044416 (@Ns78p269 72203021 17592186044416 (Ns78p252 rfl rfl) (Ns78p252 rfl rfl) rfl) (Ns78p252 rfl rfl) rfl rfl) qz366 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 6132645 4194304) (BSN.cos_neg_of_bound 6132645 4194304 Bool.false 454855 4194304 1 1102941 (Ns78p275 rfl rfl)) rfl rfl) 

noncomputable def Ns78p277 := @Ns78p238 10843045576989619485043 Ns78p174 (Ns78p239 qz28 (@Enclosure.Real.IsNear.of_eq qz645 (@Inv.inv Real Real.instInv (Real.sqrt qz35)) Bool.false 3221037 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz30 (BSN.t_div_two_pi_nonneg qz29 289039 1000 qz32)) Ns78p243) rfl) (@Ns78p244 35184372088832 3364171227337651 12935428845342818304 (BSN.correction_mk qz31 (BSN.cos_two_pi_p_ne_zero_mk qz29 289039 1000 6 qz32 rfl rfl (@BSN.floor_sqrt_eq_dec qz29 289039 1000 6 qz32 rfl rfl rfl))) (@Ns78p245 8388608 454855 4194304 100258901 2313034924032 18828428433815 35184372088832 3364171227337651 12935428845342818304 (@Ns78p246 8388608 (Ns78p259 rfl rfl rfl rfl rfl) rfl) (Ns78p276 rfl) rfl)) 

noncomputable def Ns78p278 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz29) (hardyZApproximantRS₀ qz29) Bool.false 597130383470892242549 295147905179352825856 175633941352234453268851 Ns78p174 (@Eq.refl Real (hardyZApproximantRS₀ qz29)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz29) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz29) qz29 6) (@HMul.hMul Real Real Real qz5 qz644 (Zeta.RiemannSiegel.correction qz31))) Bool.false 597130383470892242549 295147905179352825856 175633941352234453268851 Ns78p174 (BSN.hardyZApproximantRS₀_eq qz29 6 (@BSN.floor_sqrt_eq_dec qz29 289039 1000 6 qz32 rfl rfl rfl)) (@Ns78p176 597130383470892242549 295147905179352825856 175633941352234453268851 Ns78p174 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz29) qz29 6) (@HAdd.hAdd Real Real Real qz351 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz29) qz29 6)) Bool.false 37390319 16777216 25479 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz29) qz29 6) (Ns78p237 (Ns78p236 rfl rfl rfl rfl) rfl rfl)) (Ns78p277 rfl) rfl rfl)) 

theorem RS079to096.d35 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz29) Bool.false 597130383470892242549 295147905179352825856 175633941352234453268851 Ns78p174 := Ns78p278 

noncomputable abbrev qz648 := (@HMul.hMul Real Real Real qz841 (Real.sqrt qz846) qz843)

noncomputable abbrev qz381 := qz648

noncomputable abbrev qz42 := qz381

noncomputable abbrev qz382 := (@HMul.hMul Real Real Real qz629 (@HMul.hMul Real Real Real qz629 qz648 qz648) qz648)

noncomputable abbrev qz43 := (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz382))

noncomputable abbrev qz44 := (@HMul.hMul Real Real Real qz336 (@HMul.hMul Real Real Real qz336 qz360 qz360) qz360)

noncomputable abbrev qz383 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz42))

noncomputable def Ns78p279 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz351 (@HAdd.hAdd Real Real Real qz351 qz383 qz43) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz44))) Bool.false 

noncomputable def Ns78p280 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz351 qz383 qz43) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz44)) 14104205 268435456 

noncomputable def Ns78p281 := @Enclosure.Real.IsNear.addLit_ff qz383 qz43 1763025 33554432 25 33554432 

noncomputable def Ns78p282 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz42) 25 4 0 1 70521 8388608 1 8388608 1763025 

noncomputable def Ns78p283 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz42) Bool.false 70521 8388608 1 8388608 70521 8388608 1 8388608 

noncomputable def Ns78p284 := @Enclosure.Real.IsNear.mulLit_ff qz20 qz8 21815499 8388608 5 8388608 95924809561 2097152000 71849 2097152000 2092647587053185939 17592186044416000 2047046194701 

noncomputable def Ns78p285 := @Enclosure.Real.IsNear.sqrt_image qz8 95924809561 2097152000 71849 2097152000 28366794 28366816 4194304 qz358 

noncomputable def Ns78p286 := @Enclosure.Real.IsNear.sqrt_image qz19 28366805 4194304 11 4194304 10907747 10907752 4194304 (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 56733610 8388608 22 8388608 28366805 4194304 11 4194304 (Ns78p285 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz384 := (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 21815499 8388608 5 8388608 21815499 8388608 5 8388608 (Ns78p286 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns78p287 := @Ns78p284 17592186044416000 qz384 

noncomputable def Ns78p288 := Ns78p287 qz358 

noncomputable def Ns78p289 := @Enclosure.Real.IsNear.inv_image qz42 2092647587053185939 17592186044416000 2047046194701 17592186044416000 35260 35261 4194304 (Ns78p288 rfl) rfl rfl 

noncomputable abbrev qz45 := (@Inv.inv Real Real.instInv qz382)

noncomputable def Ns78p290 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz45 1 32 0 1 5 

noncomputable def Ns78p291 := @Enclosure.Real.IsNear.recentre' qz45 Bool.false 5 8388608 1 8388608 

noncomputable def Ns78p292 := nat_lit 9164067744506771336998796729879041348433939771647091019 

noncomputable def Ns78p293 := nat_lit 5444517870735015415413993718908291383296000000000 

noncomputable def Ns78p294 := nat_lit 26893140255802886196481202536289653571594759052981 

noncomputable abbrev qz46 := qz382

noncomputable def Ns78p295 := @Enclosure.Real.IsNear.inv_image qz46 Ns78p292 Ns78p293 Ns78p294 Ns78p293 2 3 

noncomputable def Ns78p296 := nat_lit 4379173923599521422824187130107311721 

noncomputable def Ns78p297 := nat_lit 309485009821345068724781056000000 

noncomputable def Ns78p298 := nat_lit 8567496750253031060901499497879 

noncomputable abbrev qz385 := (@HMul.hMul Real Real Real qz629 qz648 qz648)

noncomputable abbrev qz47 := qz385

noncomputable def Ns78p299 := @Enclosure.Real.IsNear.mulLit_ff qz47 qz42 Ns78p296 Ns78p297 Ns78p298 Ns78p297 2092647587053185939 17592186044416000 2047046194701 

noncomputable def Ns78p300 := @Enclosure.Real.IsNear.mulLit_ff qz42 qz42 2092647587053185939 17592186044416000 2047046194701 17592186044416000 2092647587053185939 17592186044416000 2047046194701 17592186044416000 Ns78p296 

noncomputable def Ns78p301 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv qz44) 13 10 0 1 476941 8388608 1 

noncomputable def Ns78p302 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz44) Bool.false 476941 8388608 1 8388608 476941 8388608 

noncomputable def Ns78p303 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz20 qz20) qz20 475915996619001 70368744177664 218155015 70368744177664 21815499 8388608 5 8388608 10382344948325819696499 

noncomputable def Ns78p304 := @Enclosure.Real.IsNear.mulLit_ff qz20 qz20 21815499 8388608 5 8388608 21815499 8388608 5 8388608 475915996619001 70368744177664 218155015 

noncomputable def Ns78p305 := @Ns78p304 70368744177664 qz384 

noncomputable def Ns78p306 := Ns78p305 qz384 

noncomputable def Ns78p307 := @Ns78p303 590295810358705651712 7138741585447565 590295810358705651712 (Ns78p306 rfl) qz384 

noncomputable def Ns78p308 := @Enclosure.Real.IsNear.inv_image qz44 10382344948325819696499 590295810358705651712 7138741585447565 590295810358705651712 238470 238471 4194304 (Ns78p307 rfl) 

noncomputable def Ns78p309 := @Ns78p280 201 268435456 6200233 83886080 13 83886080 2847508841627648 169724753 1342177280 1213 1342177280 (@Ns78p281 5 268435456 1 268435456 473258587586560 14104205 268435456 201 268435456 (@Ns78p282 33554432 25 33554432 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns78p283 (Ns78p289 rfl rfl rfl rfl) rfl) rfl) (@Ns78p290 8388608 1 8388608 5 268435456 1 268435456 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns78p291 5 8388608 1 8388608 (@Ns78p295 4194304 (@Ns78p299 17592186044416000 Ns78p292 Ns78p293 Ns78p294 Ns78p293 (@Ns78p300 Ns78p297 Ns78p298 Ns78p297 (Ns78p288 rfl) (Ns78p288 rfl) rfl) (Ns78p288 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns78p301 8388608 6200233 83886080 13 83886080 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns78p302 1 8388608 (Ns78p308 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS079to096.d36 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 := @Ns78p279 169724753 1342177280 1213 1342177280 (BSN.hardyZErrorBoundRS₀_mk qz4 287396 1000 qz11 rfl rfl) (Ns78p309 rfl rfl) 

noncomputable def Ns78p310 := nat_lit 7750731563962394883391488 

noncomputable def Ns78p311 := nat_lit 11063337295753478835137413120 

noncomputable abbrev qz851 := (Enclosure.sfrac Bool.false 290679 1000)

noncomputable abbrev qz649 := qz851

noncomputable abbrev qz386 := qz649

noncomputable abbrev qz48 := qz386

noncomputable abbrev qz852 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 290679 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz650 := qz852

noncomputable abbrev qz387 := qz650

noncomputable abbrev qz49 := qz387

noncomputable abbrev qz853 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 290679 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz651 := qz853

noncomputable abbrev qz388 := qz651

noncomputable abbrev qz50 := qz388

noncomputable abbrev qz652 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz49 qz9))

noncomputable def Ns78p312 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz48) qz48 6) (@HMul.hMul Real Real Real qz5 qz652 (Zeta.RiemannSiegel.correction qz50)) 142750393 33554432 25619 16777216 15801710825670987099 73786976294838206464 523327605704482773755 Ns78p310 Ns78p311 

noncomputable def Ns78p313 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz48) qz48 Real.sin BSN.quadSignNeg 5 6 290679 1000 69 67108864 33554432 1125899906842624 Bool.false 27618605544 1150 120242927 62 27397080 8 

noncomputable def Ns78p314 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz48) qz48 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 290679 1000 5 35 67108864 33554432 1125899906842624 Bool.false 27618605544 1150 

noncomputable def Ns78p315 := Ns78p314 93032624 61 33554424 8 108007536 61 30011992 8 Bool.true 128011569 25495 Bool.false 48903646 Bool.true 87414515 3537118876014220 1 Bool.false 44688872 Bool.true Bool.false 64709355 Bool.false Bool.true 121417101 

noncomputable def Ns78p316 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz48) qz48 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 290679 1000 133 58 67108864 33554432 1125899906842624 Bool.false 27618605544 1150 

noncomputable def Ns78p317 := Ns78p316 46516304 61 47453136 16 73726608 61 38745320 8 Bool.true 67108840 1213 Bool.false 77183323 Bool.false 73796147 3537118876014220 1 Bool.false 61257871 Bool.true Bool.false 30461353 Bool.true Bool.true 128011569 

noncomputable def Ns78p318 := nat_lit 2236131965983679431031456173124297742945861373528416567 

noncomputable def Ns78p319 := nat_lit 5433448685520351878816727744913695436860274245632000 

noncomputable def Ns78p320 := nat_lit 1129411584000000000000000000 

noncomputable def Ns78p321 := nat_lit 996122568925269239966327711520000 

noncomputable def Ns78p322 := nat_lit 1737313872129787985064927713957532480 

noncomputable abbrev qz389 := (@Eq.refl Real qz649)

noncomputable abbrev qz51 := qz389

noncomputable def Ns78p323 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz48 290679 1000 337978124164 16000000 581358 4000 2000 Ns78p321 Ns78p322 qz51 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns78p324 := nat_lit 6440060062032996761370593778597977499684080755761839712960 

noncomputable abbrev qz390 := (Real.log (Enclosure.sfrac Bool.false 337978124164 16000000))

noncomputable abbrev qz391 := (Enclosure.sfrac Bool.false 290679 2000)

noncomputable abbrev qz52 := (@HSub.hSub Real Real Real qz339 (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 290679 4000) qz390) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 581358)))))) qz391)

noncomputable abbrev qz392 := (@HSub.hSub Real Real Real qz12 qz52 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 290679 2000) (Real.log Real.pi)))

noncomputable def Ns78p325 := @Enclosure.Real.IsNear.addLit_ft_p qz392 (Enclosure.sfrac Bool.true Ns78p321 Ns78p322) 3706911651152892320727 9007199254740992000 19341719229103517946751 Ns78p320 Ns78p321 Ns78p322 0 1 Ns78p324 

noncomputable def Ns78p326 := nat_lit 248766629857234893958312624128000 

noncomputable abbrev qz393 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 290679 2000) (Real.log Real.pi))

noncomputable def Ns78p327 := @Enclosure.Real.IsNear.subLit_ff_p qz52 qz393 5205479642126488755159 9007199254740992000 18667439744488243823 Ns78p194 11165201596719 67108864000 290679 33554432000 Ns78p326 3706911651152892320727 9007199254740992000 

noncomputable def Ns78p328 := nat_lit 10410959284252977510318000 

noncomputable abbrev qz53 := (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 290679 4000) qz390) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 581358))))))

noncomputable def Ns78p329 := @Enclosure.Real.IsNear.subLit_ff_p qz53 qz391 6514581478210917161943 9007199254740992000 18667439744488243823 Ns78p194 290679 2000 0 1 Ns78p328 5205479642126488755159 9007199254740992000 18667439744488243823 Ns78p194 

noncomputable def Ns78p330 := nat_lit 14669533358872710768602812680046116864 

noncomputable def Ns78p331 := nat_lit 12038661879421244176072704 

noncomputable def Ns78p332 := nat_lit 4904865761380925023412587030078109761306888103934491529248576128922849280 

noncomputable def Ns78p333 := nat_lit 26359916455268374589550551770915662355363584331069804964157594857926656 

noncomputable def Ns78p334 := nat_lit 2852852452849285022312928713651866914920163069555105409197480407040 

noncomputable def Ns78p335 := BSN.log_dyadic_bound 75834124164 600122124164 4 3 Ns78p332 33554432 8823528 Ns78p333 Ns78p334 8525751 675956248328 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 75834124164) (BSN.artanhQ 600122124164) 0 3 Ns78p333 Ns78p332 Ns78p334 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns78p336 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 290679 4000) qz390 290679 4000 0 1 22423755152935617 2251799813685248 62500007720587 551470500000000000000 6518114724100172213943 9007199254740992000 6055813248070836191 735294000000000000000000 (Enclosure.Real.IsNear.const Bool.false 290679 4000) (BSN.isNear_log_sfrac 337978124164 16000000 22423755152935617 2251799813685248 62500007720587 551470500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 337978124164) qz347)) Bool.false Ns78p331 Ns78p84 1000000123529392 8823528000000000000000 22423755152935617 2251799813685248 62500007720587 551470500000000000000 (BSN.log_rat_reduce_isNear 337978124164 16000000 14 675956248328 524288000000 8525751 33554432 24973259072661432 36028797018963968 8823528 1000000000000000 rfl rfl rfl rfl (Ns78p335 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns78p337 := BSN.arctan_dyadic_bound_f 1000 581358 1 0 4194304 1102941 0 1 1 0 1 1 7214 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 581358) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 581358) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz394 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 581358)))

noncomputable def Ns78p338 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz394 884279719003555 562949953421312 1 2000000000000000 7214 4194304 1 1102941 3704876841571505405952 883311472313763 562949953421312 2000000001102941 2205882000000000000000 qz17 (Ns78p337 rfl) rfl rfl 

noncomputable def Ns78p339 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 290679 4000) qz390) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz394)) 6518114724100172213943 9007199254740992000 6055813248070836191 735294000000000000000000 883311472313763 2251799813685248 2000000001102941 8823528000000000000000 Ns78p330 6514581478210917161943 9007199254740992000 18667439744488243823 Ns78p194 (Ns78p336 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz394) 1 4 0 1 883311472313763 562949953421312 2000000001102941 2205882000000000000000 883311472313763 2251799813685248 2000000001102941 8823528000000000000000 qz350 Ns78p338 rfl) 

noncomputable def Ns78p340 := @Ns78p325 Ns78p318 Ns78p319 19341719229103517946751 Ns78p320 (@Ns78p327 19341719229103517946751 Ns78p320 (Ns78p329 (Ns78p339 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 290679 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz391 (Real.log Real.pi) 290679 2000 0 1 38410761 33554432 1 16777216 11165201596719 67108864000 290679 33554432000 (Enclosure.Real.IsNear.const Bool.false 290679 2000) RS079to096.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns78p321 Ns78p322) 

noncomputable def Ns78p341 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz48) Bool.false Ns78p318 Ns78p319 19341719229103517946751 Ns78p320 3452325693 8388608 9 524288 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz48) (@HAdd.hAdd Real Real Real qz351 qz392 (Enclosure.sfrac Bool.true Ns78p321 Ns78p322)) Bool.false Ns78p318 Ns78p319 19341719229103517946751 Ns78p320 Ns78p323 (Ns78p340 rfl rfl)) 

noncomputable def Ns78p342 := nat_lit 1899768736262294398304256 

noncomputable def Ns78p343 := nat_lit 140223196325626467178553590699768142398141654571604686933682539694598971145079149593345 

noncomputable def Ns78p344 := nat_lit 282206808092337765913274263122437859662576210702048541743439277549361089849791906561 

noncomputable def Ns78p345 := nat_lit 366794322211157914799018864930527854508060162394018482425393464179345958853545728705281 

noncomputable def Ns78p346 := BSN.sin_dyadic_bound_f 26997337503 17179869184 3 2 8388608 2208037 Ns78p343 Ns78p97 Ns78p344 Ns78p345 Ns78p100 Ns78p344 8388605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26997337503) qz352 0 2 Ns78p343 Ns78p97 Ns78p344 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26997337503) qz353 0 2 Ns78p345 Ns78p100 Ns78p344 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p347 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz48) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3452325693) qz354) Bool.false 3452325693 8388608 9 524288 Bool.true 8388605 8388608 1 1102941 (Ns78p341 rfl) (Enclosure.sfrac_false_div 3452325693 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3452325693) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns78p342) qz355) 226375608064910080 72057594037927936 Bool.false 8388605 8388608 65 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q1 3452325693 8388608 226375608064910080 72057594037927936 65 Ns78p342 Ns78p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388605 8388608 Ns78p342 Ns78p84 26997337503 17179869184 2208037 2205882 (Ns78p346 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p348 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz48) Bool.false Ns78p318 Ns78p319 19341719229103517946751 Ns78p320 27618605544 67108864 1150 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz48) (@HAdd.hAdd Real Real Real qz351 qz392 (Enclosure.sfrac Bool.true Ns78p321 Ns78p322)) Bool.false Ns78p318 Ns78p319 19341719229103517946751 Ns78p320 Ns78p323 (Ns78p340 rfl rfl)) 

noncomputable def Ns78p349 := Ns78p317 25495 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 133 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 61257871 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 58 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 30461353 67108864) qz51 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 1) Bool.true 8388605 8388608 10450757 578258731008 67108840 67108864 1213 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz48)) Bool.true 8388605 8388608 10450757 578258731008 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz48) qz48) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz48)) Bool.true 8388605 8388608 10450757 578258731008 8388605 8388608 10450757 578258731008 (Ns78p347 rfl rfl) rfl)) rfl) (Ns78p348 rfl) RS079to096.d7 

noncomputable def Ns78p350 := nat_lit 2177942672024529688772365588325129217694439591295546302758786086625 

noncomputable def Ns78p351 := nat_lit 1259469862169170667729090004774473314041238481499772281564346081 

noncomputable def Ns78p352 := nat_lit 5702096427906446718084634204653322613357941686327812114007621285601 

noncomputable def Ns78p353 := BSN.sin_dyadic_bound_f 77183323 67108864 3 2 67108864 33554432 Ns78p350 Ns78p127 Ns78p351 Ns78p352 Ns78p130 Ns78p351 61257871 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 77183323) qz356 0 2 Ns78p350 Ns78p127 Ns78p351 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 77183323) (BSN.sinOddQ 67108864) 0 2 Ns78p352 Ns78p130 Ns78p351 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p354 := nat_lit 1011443002573787582842557128825740825150563692525379420276994897441 

noncomputable def Ns78p355 := nat_lit 879568157263945083237643527926995911327360942603995841869936161 

noncomputable def Ns78p356 := nat_lit 3032569871406834858361196099421368483629036355690930269147244820001 

noncomputable def Ns78p357 := BSN.cos_dyadic_bound_f 73796147 67108864 3 2 67108864 33554432 Ns78p354 Ns78p116 Ns78p355 Ns78p356 Ns78p119 Ns78p355 30461353 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 73796147) qz357 0 2 Ns78p354 Ns78p116 Ns78p355 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 73796147) (BSN.cosOddQ 67108864) 0 2 Ns78p356 Ns78p119 Ns78p355 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p358 := nat_lit 350838131649588753713299399594594048297278544091183697120064733440 

noncomputable def Ns78p359 := nat_lit 32713718512402381469664994468841333951148363190385146035732736 

noncomputable def Ns78p360 := nat_lit 918808808299902846345785636566225335761713375269839535554206925056 

noncomputable def Ns78p361 := BSN.sin_dyadic_bound_f 48903646 67108864 3 2 67108864 33554432 Ns78p358 Ns78p127 Ns78p359 Ns78p360 Ns78p130 Ns78p359 44688872 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 48903646) qz356 0 2 Ns78p358 Ns78p127 Ns78p359 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 48903646) (BSN.sinOddQ 67108864) 0 2 Ns78p360 Ns78p130 Ns78p359 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p362 := nat_lit 3584666795088104180483293812133750488915277122253819122917182830625 

noncomputable def Ns78p363 := nat_lit 3409325121716038392645808496318962631635449912823541306625390625 

noncomputable def Ns78p364 := nat_lit 9382893175033684981963390579927687245755458877472573874096180590625 

noncomputable def Ns78p365 := BSN.sin_dyadic_bound_f 87414515 67108864 3 2 67108864 33554432 Ns78p362 Ns78p127 Ns78p363 Ns78p364 Ns78p130 Ns78p363 64709355 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 87414515) qz356 0 2 Ns78p362 Ns78p127 Ns78p363 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 87414515) (BSN.sinOddQ 67108864) 0 2 Ns78p364 Ns78p130 Ns78p363 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p366 := Ns78p315 43400 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 5 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 44688872 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 35 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 64709355 67108864) qz51 rfl rfl (Ns78p349 RS079to096.d9 RS079to096.d11 RS079to096.d13 RS079to096.d17 (Ns78p353 rfl rfl) (Ns78p357 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns78p348 rfl) RS079to096.d19 RS079to096.d21 RS079to096.d23 RS079to096.d25 RS079to096.d17 (Ns78p361 rfl rfl) (Ns78p365 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns78p367 := nat_lit 789641579888211354967210310090512440916271128283014174923127430625 

noncomputable def Ns78p368 := nat_lit 165681905248722807287203742683181956403744974787769284000390625 

noncomputable def Ns78p369 := nat_lit 2067840652813007997511847720367950288756056415543952165005523590625 

noncomputable def Ns78p370 := BSN.sin_dyadic_bound_f 59897595 67108864 3 2 67108864 33554432 Ns78p367 Ns78p127 Ns78p368 Ns78p369 Ns78p130 Ns78p368 52255677 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 59897595) qz356 0 2 Ns78p367 Ns78p127 Ns78p368 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 59897595) (BSN.sinOddQ 67108864) 0 2 Ns78p369 Ns78p130 Ns78p368 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p371 := Ns78p313 Bool.true 121417101 43400 Bool.true 59897595 3537118876014220 1 Bool.false 52255677 Bool.true Bool.true 142750393 51238 BSN.abs_quadSignNeg qz635 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 52255677 67108864) qz51 rfl (Ns78p366 rfl rfl) (Ns78p348 rfl) RS079to096.d27 RS079to096.d29 RS079to096.d17 (Ns78p370 rfl rfl) rfl 

noncomputable def Ns78p372 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 6) 142750393 67108864 51238 67108864 142750393 67108864 51238 67108864 19159633419567104 142750393 33554432 25619 16777216 (Ns78p371 rfl rfl rfl rfl) 

noncomputable def Ns78p373 := @Enclosure.Real.IsNear.mulLit_ff qz652 (Zeta.RiemannSiegel.correction qz50) 804121 2097152 1 4194304 19650911772819 35184372088832 426249559438177 2425392908501778432 15801710825670987099 73786976294838206464 

noncomputable abbrev qz653 := (@HPow.hPow Real Real Real qz7 qz49 qz9)

noncomputable def Ns78p374 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz653 1 1 0 1 804121 2097152 1 4194304 804121 2097152 1 4194304 

noncomputable def Ns78p375 := @Enclosure.Real.IsNear.sqrt_image qz49 388082335431 8388608000 290679 8388608000 28528354 28528377 4194304 (@Enclosure.Real.IsNear.of_eq qz49 (@HMul.hMul Real Real Real qz5 qz48 qz3) Bool.false 388082335431 8388608000 290679 8388608000 (BSN.t_div_two_pi_mk qz48 290679 1000 qz51) (@Enclosure.Real.IsNear.mulLit_ff qz48 qz3 290679 1000 0 1 1335089 8388608 1 8388608 388082335431 8388608000 290679 8388608000 (Enclosure.Real.IsNear.const Bool.false 290679 1000) RS079to096.d32 rfl)) 

noncomputable abbrev qz854 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 290679 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz654 := qz854

noncomputable abbrev qz395 := qz654

noncomputable abbrev qz54 := qz395

noncomputable def Ns78p376 := @Enclosure.Real.IsNear.sqrt_image qz54 57056731 8388608 23 8388608 10938765 10938770 4194304 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 57056731 8388608 23 8388608 57056731 8388608 23 8388608 (Ns78p375 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns78p377 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz54) 21877535 8388608 5 8388608 1608241 1608243 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz54) Bool.false 21877535 8388608 5 8388608 21877535 8388608 5 8388608 (Ns78p376 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns78p378 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz54)) Bool.false 3216484 8388608 2 8388608 804121 2097152 1 4194304 (Ns78p377 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz55 := (@HMul.hMul Real Real Real qz336 qz334 qz388)

noncomputable abbrev qz655 := (@HMul.hMul Real Real Real qz841 qz853 qz853)

noncomputable abbrev qz396 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz655 qz651) qz640)

noncomputable abbrev qz56 := (Real.cos (@HMul.hMul Real Real Real qz336 qz334 qz396))

noncomputable def Ns78p379 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz50) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz55)) qz56) Bool.false 19650911772819 

noncomputable def Ns78p380 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz55)) qz56 26287333 8388608 1509 

noncomputable def Ns78p381 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz55)) Bool.false 26287333 8388608 1509 8388608 26287333 8388608 1509 

noncomputable def Ns78p382 := @Enclosure.Real.IsNear.recentre' (Real.cos qz55) Bool.false 2676907 8388608 84708997 4626069848064 2676907 8388608 84708997 4626069848064 

noncomputable def Ns78p383 := @Enclosure.Real.IsNear.cos_image qz55 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21127471) qz378) Bool.false 21127471 4194304 73 4194304 Bool.false 2676907 8388608 1 

noncomputable def Ns78p384 := nat_lit 620679734465781068564657377 

noncomputable def Ns78p385 := nat_lit 36028797018963968000000000000000 

noncomputable def Ns78p386 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz50 884279719003555 140737488355328 1 500000000000000 6725083 8388608 23 8388608 5946854505515584670065 1180591620717411303424 Ns78p384 

noncomputable def Ns78p387 := @Enclosure.Real.IsNear.subLit_ff_p qz54 qz1 57056731 8388608 23 8388608 6 1 0 1 6725083 6725083 8388608 23 

noncomputable def Ns78p388 := @Ns78p387 8388608 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 57056731 8388608 23 8388608 57056731 8388608 23 8388608 (Ns78p375 rfl rfl rfl rfl rfl rfl) rfl) qz362 

noncomputable def Ns78p389 := @Enclosure.Real.IsNear.recentre' qz55 Bool.false 5946854505515584670065 1180591620717411303424 Ns78p384 Ns78p385 21127471 4194304 73 4194304 (@Ns78p386 Ns78p385 RS079to096.d31 (Ns78p388 rfl rfl) rfl) 

noncomputable def Ns78p390 := nat_lit 969402427413504446341635326757365780736 

noncomputable def Ns78p391 := BSN.sin_dyadic_bound_f 5579894988 17179869184 2 1 8388608 2208037 Ns78p390 Ns78p255 Ns78p390 Ns78p390 Ns78p256 Ns78p390 2676907 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 5579894988) qz352 0 1 Ns78p390 Ns78p255 Ns78p390 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 5579894988) qz353 0 1 Ns78p390 Ns78p256 Ns78p390 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz397 := (@Nat.cast Real Real.instNatCast 604462909807314587353088)

noncomputable def Ns78p392 := @Ns78p383 1102941 (Ns78p389 rfl) (Enclosure.sfrac_false_div 21127471 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21127471) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 196325101504936911306752) qz397) 226375608064910080 72057594037927936 Bool.false 2676907 8388608 0 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q3 21127471 4194304 226375608064910080 72057594037927936 0 196325101504936911306752 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 2676907 8388608 196325101504936911306752 604462909807314587353088 5579894988 17179869184 2208037 2205882 (Ns78p391 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p393 := @Enclosure.Real.IsNear.inv_image (Real.cos qz55) 2676907 8388608 84708997 4626069848064 13142912 13144421 4194304 (Ns78p382 (Ns78p392 rfl rfl) rfl) rfl 

noncomputable def Ns78p394 := @Enclosure.Real.IsNear.recentre' qz56 Bool.false 747543 4194304 

noncomputable abbrev qz57 := (@HMul.hMul Real Real Real qz336 qz334 qz396)

noncomputable abbrev qz398 := (@Nat.cast Real Real.instNatCast 2097152)

noncomputable def Ns78p395 := @Enclosure.Real.IsNear.cos_image qz57 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 2918419)) qz398) Bool.true 2918419 2097152 

noncomputable def Ns78p396 := nat_lit 13781844474291423543392853845 

noncomputable def Ns78p397 := nat_lit 9903520314283042199192993792 

noncomputable def Ns78p398 := nat_lit 2710979744376877911166025254803209 

noncomputable def Ns78p399 := @Enclosure.Real.IsNear.recentre' qz57 Bool.true Ns78p396 Ns78p397 Ns78p398 

noncomputable def Ns78p400 := nat_lit 60446290980731458735308800000000000000 

noncomputable abbrev qz58 := qz396

noncomputable def Ns78p401 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz58 884279719003555 140737488355328 1 500000000000000 15585390208679 

noncomputable abbrev qz399 := (@HSub.hSub Real Real Real qz634 qz655 qz651)

noncomputable abbrev qz59 := qz399

noncomputable def Ns78p402 := @Enclosure.Real.IsNear.subLit_tf qz59 qz26 11187343697575 70368744177664 502292331 70368744177664 1 16 

noncomputable abbrev qz400 := qz655

noncomputable abbrev qz60 := qz400

noncomputable def Ns78p403 := @Enclosure.Real.IsNear.subLit_ff_n qz60 qz50 45226741356889 70368744177664 309354347 70368744177664 6725083 8388608 23 8388608 

noncomputable def Ns78p404 := @Enclosure.Real.IsNear.mulLit_ff qz50 qz50 6725083 8388608 23 8388608 6725083 8388608 23 8388608 45226741356889 70368744177664 

noncomputable def Ns78p405 := nat_lit 2362587539777654750063908938036791306556684052846828321 

noncomputable def Ns78p406 := nat_lit 15085502980398593449464978548510856026246963233994833920 

noncomputable def Ns78p407 := nat_lit 5262367241198877612866258434955259118453479582423841 

noncomputable def Ns78p408 := nat_lit 7077237884850566494965994297240463401433145199375637281 

noncomputable def Ns78p409 := nat_lit 678847634117936705225924034682988521181113345529767526400 

noncomputable def Ns78p410 := BSN.cos_dyadic_bound_f 2918419 2097152 3 2 4194304 1102941 Ns78p405 Ns78p406 Ns78p407 Ns78p408 Ns78p409 Ns78p407 747543 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2918419) (BSN.cosEvenQ 2097152) 0 2 Ns78p405 Ns78p406 Ns78p407 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2918419) (BSN.cosOddQ 2097152) 0 2 Ns78p408 Ns78p409 Ns78p407 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p411 := @Ns78p394 424197365 9252139696128 747543 4194304 424197365 9252139696128 (@Ns78p395 377 8388608 Bool.false 747543 4194304 1 1102941 (@Ns78p399 Ns78p400 2918419 2097152 377 8388608 (@Ns78p401 70368744177664 502292331 70368744177664 Ns78p396 Ns78p397 Ns78p398 Ns78p400 RS079to096.d31 (@Ns78p402 0 1 249366243338864 15585390208679 70368744177664 502292331 70368744177664 (@Ns78p403 93846240840227225600 11187343697575 70368744177664 502292331 70368744177664 (@Ns78p404 309354347 70368744177664 (Ns78p388 rfl rfl) (Ns78p388 rfl rfl) rfl) (Ns78p388 rfl rfl) rfl rfl) qz366 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 2918419 2097152) (BSN.cos_neg_of_bound 2918419 2097152 Bool.false 747543 4194304 1 1102941 (Ns78p410 rfl rfl)) rfl rfl) 

noncomputable def Ns78p412 := @Ns78p373 523327605704482773755 Ns78p310 (Ns78p374 qz28 (@Enclosure.Real.IsNear.of_eq qz653 (@Inv.inv Real Real.instInv (Real.sqrt qz54)) Bool.false 804121 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz49 (BSN.t_div_two_pi_nonneg qz48 290679 1000 qz51)) Ns78p378) rfl) (@Ns78p379 35184372088832 426249559438177 2425392908501778432 (BSN.correction_mk qz50 (BSN.cos_two_pi_p_ne_zero_mk qz48 290679 1000 6 qz51 rfl rfl (@BSN.floor_sqrt_eq_dec qz48 290679 1000 6 qz51 rfl rfl rfl))) (@Ns78p380 8388608 747543 4194304 424197365 9252139696128 19650911772819 35184372088832 426249559438177 2425392908501778432 (@Ns78p381 8388608 (Ns78p393 rfl rfl rfl rfl rfl) rfl) (Ns78p411 rfl) rfl)) 

noncomputable def Ns78p413 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz48) (hardyZApproximantRS₀ qz48) Bool.true 329713144771858419035 73786976294838206464 12358783019591542135547 Ns78p310 (@Eq.refl Real (hardyZApproximantRS₀ qz48)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz48) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz48) qz48 6) (@HMul.hMul Real Real Real qz5 qz652 (Zeta.RiemannSiegel.correction qz50))) Bool.true 329713144771858419035 73786976294838206464 12358783019591542135547 Ns78p310 (BSN.hardyZApproximantRS₀_eq qz48 6 (@BSN.floor_sqrt_eq_dec qz48 290679 1000 6 qz51 rfl rfl rfl)) (@Ns78p312 329713144771858419035 73786976294838206464 12358783019591542135547 Ns78p310 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz48) qz48 6) (@HAdd.hAdd Real Real Real qz351 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz48) qz48 6)) Bool.true 142750393 33554432 25619 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz48) qz48 6) (Ns78p372 (Ns78p371 rfl rfl rfl rfl) rfl rfl)) (Ns78p412 rfl) rfl rfl)) 

theorem RS079to096.d37 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz48) Bool.true 329713144771858419035 73786976294838206464 12358783019591542135547 Ns78p310 := Ns78p413 

noncomputable def Ns78p414 := nat_lit 2260630039489031840989184 

noncomputable def Ns78p415 := nat_lit 279126444468454775807016960 

noncomputable abbrev qz855 := (Enclosure.sfrac Bool.false 292316 1000)

noncomputable abbrev qz656 := qz855

noncomputable abbrev qz401 := qz656

noncomputable abbrev qz61 := qz401

noncomputable abbrev qz856 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 292316 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz657 := qz856

noncomputable abbrev qz402 := qz657

noncomputable abbrev qz62 := qz402

noncomputable abbrev qz857 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 292316 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz658 := qz857

noncomputable abbrev qz403 := qz658

noncomputable abbrev qz63 := qz403

noncomputable abbrev qz659 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz62 qz9))

noncomputable def Ns78p416 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz61) qz61 6) (@HMul.hMul Real Real Real qz5 qz659 (Zeta.RiemannSiegel.correction qz63)) 17006541 8388608 6441 4194304 4123314015578476887 18446744073709551616 115479248871891693837 Ns78p414 Ns78p415 

noncomputable def Ns78p417 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.sin BSN.quadSignNeg 5 6 292316 1000 69 67108864 33554432 1125899906842624 Bool.false 27829375018 1157 120242927 62 27397080 8 

noncomputable def Ns78p418 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 292316 1000 6 35 67108864 33554432 1125899906842624 Bool.false 27829375018 1157 

noncomputable def Ns78p419 := Ns78p418 93032624 61 33554424 8 108007536 61 30011992 8 Bool.false 97442078 25640 Bool.false 1964358 Bool.true 53453378 3537118876014220 1 Bool.false 67080116 Bool.true Bool.false 47977831 Bool.false Bool.false 85358363 

noncomputable def Ns78p420 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 292316 1000 135 59 67108864 33554432 1125899906842624 Bool.false 27829375018 1157 

noncomputable def Ns78p421 := Ns78p420 46516304 61 47453136 16 73726608 61 38745320 8 Bool.false 67108856 1221 Bool.false 976893 Bool.false 58460806 3537118876014220 1 Bool.false 976858 Bool.false Bool.false 51342281 Bool.false Bool.false 97442078 

noncomputable def Ns78p422 := nat_lit 160016679682849289311044881081370503502849697826147 

noncomputable def Ns78p423 := nat_lit 385870598508772459849854421567104531755433984000 

noncomputable def Ns78p424 := nat_lit 1024489218863883388448534036480000 

noncomputable def Ns78p425 := nat_lit 1796849996358027960405938427742126080 

noncomputable abbrev qz404 := (@Eq.refl Real qz656)

noncomputable abbrev qz64 := qz404

noncomputable def Ns78p426 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz61 292316 1000 341795575424 16000000 584632 4000 2000 Ns78p424 Ns78p425 qz64 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns78p427 := nat_lit 1677896499151233763886181972247791570810041247477499166720 

noncomputable abbrev qz405 := (Real.log (Enclosure.sfrac Bool.false 341795575424 16000000))

noncomputable abbrev qz406 := (Enclosure.sfrac Bool.false 292316 2000)

noncomputable abbrev qz65 := (@HSub.hSub Real Real Real qz339 (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 292316 4000) qz405) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 584632)))))) qz406)

noncomputable abbrev qz407 := (@HSub.hSub Real Real Real qz12 qz65 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 292316 2000) (Real.log Real.pi)))

noncomputable def Ns78p428 := @Enclosure.Real.IsNear.addLit_ft_p qz407 (Enclosure.sfrac Bool.true Ns78p424 Ns78p425) 933800155548175964159 2251799813685248000 4862300790712773236351 Ns78p72 Ns78p424 Ns78p425 0 1 Ns78p427 

noncomputable def Ns78p429 := nat_lit 15666566910465346556703801344000 

noncomputable abbrev qz408 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 292316 2000) (Real.log Real.pi))

noncomputable def Ns78p430 := @Enclosure.Real.IsNear.subLit_ff_p qz65 qz408 1310552002817361057791 2251799813685248000 9384876128563422371 1102941000000000000000000 2807020003119 16777216000 73079 8388608000 Ns78p429 933800155548175964159 2251799813685248000 

noncomputable abbrev qz66 := (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 292316 4000) qz405) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 584632))))))

noncomputable def Ns78p431 := @Enclosure.Real.IsNear.subLit_ff_p qz66 qz406 65586822399438781399 90071992547409920 9384876128563422371 1102941000000000000000000 292316 2000 0 1 104844160225388884623280 1310552002817361057791 2251799813685248000 9384876128563422371 1102941000000000000000000 

noncomputable def Ns78p432 := nat_lit 147688394459263698134786704463101952 

noncomputable def Ns78p433 := nat_lit 12052240124211375164620800 

noncomputable def Ns78p434 := nat_lit 5095070938382798181074271726036414604020654050941660553210156752023060480 

noncomputable def Ns78p435 := nat_lit 29853515244887010995369400713524374490417580251157167489700916306640896 

noncomputable def Ns78p436 := nat_lit 3830517755056580527366571055317125118031972579099702590356209008640 

noncomputable def Ns78p437 := BSN.log_dyadic_bound 79651575424 603939575424 4 3 Ns78p434 33554432 8823528 Ns78p435 Ns78p436 8902623 683591150848 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 79651575424) (BSN.artanhQ 603939575424) 0 3 Ns78p435 Ns78p434 Ns78p436 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns78p438 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 292316 4000) qz405 292316 4000 0 1 22449046604729025 2251799813685248 62500007720587 551470500000000000000 65622155073079696719 90071992547409920 4567438064212777373 551470500000000000000000 (Enclosure.Real.IsNear.const Bool.false 292316 4000) (BSN.isNear_log_sfrac 341795575424 16000000 22449046604729025 2251799813685248 62500007720587 551470500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 341795575424) qz347)) Bool.false Ns78p433 Ns78p84 1000000123529392 8823528000000000000000 22449046604729025 2251799813685248 62500007720587 551470500000000000000 (BSN.log_rat_reduce_isNear 341795575424 16000000 14 683591150848 524288000000 8902623 33554432 24973259072661432 36028797018963968 8823528 1000000000000000 rfl rfl rfl rfl (Ns78p437 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns78p439 := BSN.arctan_dyadic_bound_f 1000 584632 1 0 4194304 1102941 0 1 1 0 1 1 7174 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 584632) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 584632) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz409 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 584632)))

noncomputable def Ns78p440 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz409 884279719003555 562949953421312 1 2000000000000000 7174 4194304 1 1102941 3704899359569642258432 883316841022883 562949953421312 2000000001102941 2205882000000000000000 qz17 (Ns78p439 rfl) rfl rfl 

noncomputable def Ns78p441 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 292316 4000) qz405) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz409)) 65622155073079696719 90071992547409920 4567438064212777373 551470500000000000000000 883316841022883 2251799813685248 2000000001102941 8823528000000000000000 Ns78p432 65586822399438781399 90071992547409920 9384876128563422371 1102941000000000000000000 (Ns78p438 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz409) 1 4 0 1 883316841022883 562949953421312 2000000001102941 2205882000000000000000 883316841022883 2251799813685248 2000000001102941 8823528000000000000000 qz350 Ns78p440 rfl) 

noncomputable def Ns78p442 := @Ns78p428 Ns78p422 Ns78p423 4862300790712773236351 Ns78p72 (@Ns78p430 4862300790712773236351 Ns78p72 (Ns78p431 (Ns78p441 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 292316 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz406 (Real.log Real.pi) 292316 2000 0 1 38410761 33554432 1 16777216 2807020003119 16777216000 73079 8388608000 (Enclosure.Real.IsNear.const Bool.false 292316 2000) RS079to096.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns78p424 Ns78p425) 

noncomputable def Ns78p443 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz61) Bool.false Ns78p422 Ns78p423 4862300790712773236351 Ns78p72 3478671877 8388608 145 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz61) (@HAdd.hAdd Real Real Real qz351 qz407 (Enclosure.sfrac Bool.true Ns78p424 Ns78p425)) Bool.false Ns78p422 Ns78p423 4862300790712773236351 Ns78p72 Ns78p426 (Ns78p442 rfl rfl)) 

noncomputable def Ns78p444 := nat_lit 1898701524867060726759424 

noncomputable def Ns78p445 := nat_lit 139907743223121286352157092771643255136097304777095411251152860575599364271872555476385 

noncomputable def Ns78p446 := nat_lit 280941042114181241469965679408278014204658284093430601067954732233545711177690113441 

noncomputable def Ns78p447 := nat_lit 365970184849513742245650536635261789523923494337193856113195089083905927655854718444961 

noncomputable def Ns78p448 := BSN.sin_dyadic_bound_f 26982171517 17179869184 3 2 8388608 2208037 Ns78p445 Ns78p97 Ns78p446 Ns78p447 Ns78p100 Ns78p446 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26982171517) qz352 0 2 Ns78p445 Ns78p97 Ns78p446 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26982171517) qz353 0 2 Ns78p447 Ns78p100 Ns78p446 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p449 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz61) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3478671877) qz354) Bool.false 3478671877 8388608 145 8388608 Bool.false 8388607 8388608 1 1102941 (Ns78p443 rfl) (Enclosure.sfrac_false_div 3478671877 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3478671877) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns78p444) qz355) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 65 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q3 3478671877 8388608 226375608064910080 72057594037927936 65 Ns78p444 Ns78p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns78p444 Ns78p84 26982171517 17179869184 2208037 2205882 (Ns78p448 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p450 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz61) Bool.false Ns78p422 Ns78p423 4862300790712773236351 Ns78p72 27829375018 67108864 1157 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz61) (@HAdd.hAdd Real Real Real qz351 qz407 (Enclosure.sfrac Bool.true Ns78p424 Ns78p425)) Bool.false Ns78p422 Ns78p423 4862300790712773236351 Ns78p72 Ns78p426 (Ns78p442 rfl rfl)) 

noncomputable def Ns78p451 := Ns78p421 25640 BSN.abs_quadSignPos (BSN.cos_quad_nat3 135 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 976858 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 59 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 51342281 67108864) qz64 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 1) Bool.false 8388607 8388608 168315053 9252139696128 67108856 67108864 1221 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz61)) Bool.false 8388607 8388608 168315053 9252139696128 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz61) qz61) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz61)) Bool.false 8388607 8388608 168315053 9252139696128 8388607 8388608 168315053 9252139696128 (Ns78p449 rfl rfl) rfl)) rfl) (Ns78p450 rfl) RS079to096.d7 

noncomputable def Ns78p452 := BSN.sin_dyadic_bound_f 976893 67108864 1 0 67108864 33554432 0 1 1 0 1 1 976858 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 976893) qz356 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 976893) (BSN.sinOddQ 67108864) 0 0 rfl) rfl rfl 

noncomputable def Ns78p453 := nat_lit 716544603800339912691405520560753224279101907459104928826772660480 

noncomputable def Ns78p454 := nat_lit 136432673486719199412451500951409385717355156177338829057270016 

noncomputable def Ns78p455 := nat_lit 1876443547529530797392727632371860924582676896901940074537359483136 

noncomputable def Ns78p456 := BSN.sin_dyadic_bound_f 58460806 67108864 3 2 67108864 33554432 Ns78p453 Ns78p127 Ns78p454 Ns78p455 Ns78p130 Ns78p454 51342281 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 58460806) qz356 0 2 Ns78p453 Ns78p127 Ns78p454 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 58460806) (BSN.sinOddQ 67108864) 0 2 Ns78p455 Ns78p130 Ns78p454 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p457 := nat_lit 14889583842595986275482896 

noncomputable def Ns78p458 := BSN.cos_dyadic_bound_f 1964358 67108864 2 1 67108864 33554432 Ns78p457 Ns78p228 Ns78p457 Ns78p457 Ns78p229 Ns78p457 67080116 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1964358) qz357 0 1 Ns78p457 Ns78p228 Ns78p457 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1964358) (BSN.cosOddQ 67108864) 0 1 Ns78p457 Ns78p229 Ns78p457 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p459 := nat_lit 500794744398060571207253979425731839022727979711523165881851511040 

noncomputable def Ns78p460 := nat_lit 66650167641780344711563021454611351407119160515513123111239936 

noncomputable def Ns78p461 := nat_lit 1311497373152071946889465510746942588585818896794106984634097664256 

noncomputable def Ns78p462 := BSN.sin_dyadic_bound_f 53453378 67108864 3 2 67108864 33554432 Ns78p459 Ns78p127 Ns78p460 Ns78p461 Ns78p130 Ns78p460 47977831 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 53453378) qz356 0 2 Ns78p459 Ns78p127 Ns78p460 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 53453378) (BSN.sinOddQ 67108864) 0 2 Ns78p461 Ns78p130 Ns78p460 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p463 := Ns78p419 43646 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 6 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 67080116 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 35 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 47977831 67108864) qz64 rfl rfl (Ns78p451 RS079to096.d9 RS079to096.d11 RS079to096.d13 RS079to096.d17 (Ns78p452 rfl rfl) (Ns78p456 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns78p450 rfl) RS079to096.d19 RS079to096.d21 RS079to096.d23 RS079to096.d25 RS079to096.d17 (Ns78p458 rfl rfl) (Ns78p462 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns78p464 := nat_lit 273824291314638735384231690256983872287490104371946948675828285185 

noncomputable def Ns78p465 := nat_lit 19928658063396491553706724393084187397075439970591100137209601 

noncomputable def Ns78p466 := nat_lit 717126592758617855496186520738321338735259770261813432369804312321 

noncomputable def Ns78p467 := BSN.sin_dyadic_bound_f 45965793 67108864 3 2 67108864 33554432 Ns78p464 Ns78p127 Ns78p465 Ns78p466 Ns78p130 Ns78p465 42455040 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 45965793) qz356 0 2 Ns78p464 Ns78p127 Ns78p465 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 45965793) (BSN.sinOddQ 67108864) 0 2 Ns78p466 Ns78p130 Ns78p465 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p468 := Ns78p417 Bool.false 85358363 43646 Bool.true 45965793 3537118876014220 1 Bool.false 42455040 Bool.true Bool.false 68026164 51528 BSN.abs_quadSignNeg qz635 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 42455040 67108864) qz64 rfl (Ns78p463 rfl rfl) (Ns78p450 rfl) RS079to096.d27 RS079to096.d29 RS079to096.d17 (Ns78p467 rfl rfl) rfl 

noncomputable def Ns78p469 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 6) 68026164 67108864 51528 67108864 68026164 67108864 51528 67108864 9130317176635392 17006541 8388608 6441 4194304 (Ns78p468 rfl rfl rfl rfl) 

noncomputable def Ns78p470 := @Enclosure.Real.IsNear.mulLit_ff qz659 (Zeta.RiemannSiegel.correction qz63) 802993 2097152 1 4194304 5134931457159 8796093022208 1290771938538581 9701571634007113728 4123314015578476887 18446744073709551616 

noncomputable abbrev qz660 := (@HPow.hPow Real Real Real qz7 qz62 qz9)

noncomputable def Ns78p471 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz660 1 1 0 1 802993 2097152 1 4194304 802993 2097152 1 4194304 

noncomputable def Ns78p472 := @Enclosure.Real.IsNear.sqrt_image qz62 97566969031 2097152000 73079 2097152000 28608572 28608595 4194304 (@Enclosure.Real.IsNear.of_eq qz62 (@HMul.hMul Real Real Real qz5 qz61 qz3) Bool.false 97566969031 2097152000 73079 2097152000 (BSN.t_div_two_pi_mk qz61 292316 1000 qz64) (@Enclosure.Real.IsNear.mulLit_ff qz61 qz3 292316 1000 0 1 1335089 8388608 1 8388608 97566969031 2097152000 73079 2097152000 (Enclosure.Real.IsNear.const Bool.false 292316 1000) RS079to096.d32 rfl)) 

noncomputable abbrev qz858 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 292316 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz661 := qz858

noncomputable abbrev qz410 := qz661

noncomputable abbrev qz67 := qz410

noncomputable def Ns78p473 := @Enclosure.Real.IsNear.sqrt_image qz67 57217167 8388608 23 8388608 10954133 10954139 4194304 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 57217167 8388608 23 8388608 57217167 8388608 23 8388608 (Ns78p472 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns78p474 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz67) 1369267 524288 3 4194304 1605985 1605987 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz67) Bool.false 21908272 8388608 6 8388608 1369267 524288 3 4194304 (Ns78p473 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns78p475 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz67)) Bool.false 3211972 8388608 2 8388608 802993 2097152 1 4194304 (Ns78p474 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz68 := (@HMul.hMul Real Real Real qz336 qz334 qz403)

noncomputable abbrev qz662 := (@HMul.hMul Real Real Real qz841 qz857 qz857)

noncomputable abbrev qz411 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz662 qz658) qz640)

noncomputable abbrev qz69 := (Real.cos (@HMul.hMul Real Real Real qz336 qz334 qz411))

noncomputable def Ns78p476 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz63) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz68)) qz69) Bool.false 5134931457159 

noncomputable def Ns78p477 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz68)) qz69 9744609 4194304 415 

noncomputable def Ns78p478 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz68)) Bool.false 19489218 8388608 830 8388608 9744609 4194304 415 

noncomputable def Ns78p479 := @Enclosure.Real.IsNear.recentre' (Real.cos qz68) Bool.false 3610650 8388608 84708997 4626069848064 1805325 4194304 84708997 4626069848064 

noncomputable def Ns78p480 := @Enclosure.Real.IsNear.cos_image qz68 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 43262991) qz354) Bool.false 43262991 8388608 73 4194304 Bool.false 3610650 8388608 1 

noncomputable def Ns78p481 := nat_lit 620679734467159203310859489 

noncomputable def Ns78p482 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz63 884279719003555 140737488355328 1 500000000000000 6885519 8388608 23 8388608 6088724806513639020045 1180591620717411303424 Ns78p481 

noncomputable def Ns78p483 := @Enclosure.Real.IsNear.subLit_ff_p qz67 qz1 57217167 8388608 23 8388608 6 1 0 1 6885519 6885519 8388608 23 

noncomputable def Ns78p484 := @Ns78p483 8388608 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 57217167 8388608 23 8388608 57217167 8388608 23 8388608 (Ns78p472 rfl rfl rfl rfl rfl rfl) rfl) qz362 

noncomputable def Ns78p485 := @Enclosure.Real.IsNear.recentre' qz68 Bool.false 6088724806513639020045 1180591620717411303424 Ns78p481 Ns78p385 43262991 8388608 73 4194304 (@Ns78p482 Ns78p385 RS079to096.d31 (Ns78p484 rfl rfl) rfl) 

noncomputable def Ns78p486 := nat_lit 3414828680520348584254334393339827360000 

noncomputable def Ns78p487 := BSN.sin_dyadic_bound_f 7644379340 17179869184 2 1 8388608 2208037 Ns78p486 Ns78p255 Ns78p486 Ns78p486 Ns78p256 Ns78p486 3610650 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 7644379340) qz352 0 1 Ns78p486 Ns78p255 Ns78p486 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 7644379340) qz353 0 1 Ns78p486 Ns78p256 Ns78p486 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p488 := @Ns78p480 1102941 (Ns78p485 rfl) (Enclosure.sfrac_false_div 43262991 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 43262991) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 537925374234552258527232) qz355) 226375608064910080 72057594037927936 Bool.false 3610650 8388608 0 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q3 43262991 8388608 226375608064910080 72057594037927936 0 537925374234552258527232 Ns78p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 3610650 8388608 537925374234552258527232 Ns78p84 7644379340 17179869184 2208037 2205882 (Ns78p487 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p489 := @Enclosure.Real.IsNear.inv_image (Real.cos qz68) 1805325 4194304 84708997 4626069848064 9744194 9745024 4194304 (Ns78p479 (Ns78p488 rfl rfl) rfl) rfl 

noncomputable def Ns78p490 := @Enclosure.Real.IsNear.recentre' qz69 Bool.false 1053902 4194304 

noncomputable abbrev qz70 := (@HMul.hMul Real Real Real qz336 qz334 qz411)

noncomputable def Ns78p491 := @Enclosure.Real.IsNear.cos_image qz70 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 11046155)) qz354) Bool.true 11046155 8388608 

noncomputable def Ns78p492 := nat_lit 13040998613701389716123393725 

noncomputable def Ns78p493 := nat_lit 13754057469616160906379959788286869 

noncomputable def Ns78p494 := @Enclosure.Real.IsNear.recentre' qz70 Bool.true Ns78p492 Ns78p397 Ns78p493 

noncomputable def Ns78p495 := nat_lit 302231454903657293676544000000000000000 

noncomputable abbrev qz71 := qz411

noncomputable def Ns78p496 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz71 884279719003555 140737488355328 1 500000000000000 14747594379295 

noncomputable abbrev qz412 := (@HSub.hSub Real Real Real qz634 qz662 qz658)

noncomputable abbrev qz72 := qz412

noncomputable def Ns78p497 := @Enclosure.Real.IsNear.subLit_tf qz72 qz26 10349547868191 70368744177664 509672387 70368744177664 1 16 

noncomputable abbrev qz413 := qz662

noncomputable abbrev qz73 := qz413

noncomputable def Ns78p498 := @Enclosure.Real.IsNear.subLit_ff_n qz73 qz63 47410371899361 70368744177664 316734403 70368744177664 6885519 8388608 23 8388608 

noncomputable def Ns78p499 := @Enclosure.Real.IsNear.mulLit_ff qz63 qz63 6885519 8388608 23 8388608 6885519 8388608 23 8388608 47410371899361 70368744177664 

noncomputable def Ns78p500 := nat_lit 124076624101608046701701220066081104261198105745104147190625 

noncomputable def Ns78p501 := nat_lit 988643523323402220304136834155207460536120982503085435781120 

noncomputable def Ns78p502 := nat_lit 221660885436706768077012557132305426326679565127750390625 

noncomputable def Ns78p503 := nat_lit 371786550533950726568949635083978701930940958105056940790625 

noncomputable def Ns78p504 := nat_lit 44488958549553099913686157536984335724125444212638844610150400 

noncomputable def Ns78p505 := BSN.cos_dyadic_bound_f 11046155 8388608 3 2 4194304 1102941 Ns78p500 Ns78p501 Ns78p502 Ns78p503 Ns78p504 Ns78p502 1053902 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 11046155) (BSN.cosEvenQ 8388608) 0 2 Ns78p500 Ns78p501 Ns78p502 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 11046155) (BSN.cosOddQ 8388608) 0 2 Ns78p503 Ns78p504 Ns78p502 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p506 := @Ns78p490 430815011 9252139696128 526951 2097152 430815011 9252139696128 (@Ns78p491 383 8388608 Bool.false 1053902 4194304 1 1102941 (@Ns78p494 Ns78p495 11046155 8388608 383 8388608 (@Ns78p496 70368744177664 509672387 70368744177664 Ns78p492 Ns78p397 Ns78p493 Ns78p495 RS079to096.d31 (@Ns78p497 0 1 235961510068720 14747594379295 70368744177664 509672387 70368744177664 (@Ns78p498 86818300043489968128 10349547868191 70368744177664 509672387 70368744177664 (@Ns78p499 316734403 70368744177664 (Ns78p484 rfl rfl) (Ns78p484 rfl rfl) rfl) (Ns78p484 rfl rfl) rfl rfl) qz366 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 11046155 8388608) (BSN.cos_neg_of_bound 11046155 8388608 Bool.false 1053902 4194304 1 1102941 (Ns78p505 rfl rfl)) rfl rfl) 

noncomputable def Ns78p507 := @Ns78p470 115479248871891693837 Ns78p414 (Ns78p471 qz28 (@Enclosure.Real.IsNear.of_eq qz660 (@Inv.inv Real Real.instInv (Real.sqrt qz67)) Bool.false 802993 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz62 (BSN.t_div_two_pi_nonneg qz61 292316 1000 qz64)) Ns78p475) rfl) (@Ns78p476 8796093022208 1290771938538581 9701571634007113728 (BSN.correction_mk qz63 (BSN.cos_two_pi_p_ne_zero_mk qz61 292316 1000 6 qz64 rfl rfl (@BSN.floor_sqrt_eq_dec qz61 292316 1000 6 qz64 rfl rfl rfl))) (@Ns78p477 4194304 526951 2097152 430815011 9252139696128 5134931457159 8796093022208 1290771938538581 9701571634007113728 (@Ns78p478 4194304 (Ns78p489 rfl rfl rfl rfl rfl) rfl) (Ns78p506 rfl) rfl)) 

noncomputable def Ns78p508 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz61) (hardyZApproximantRS₀ qz61) Bool.false 33274465139920088745 18446744073709551616 3587024965240770556173 Ns78p414 (@Eq.refl Real (hardyZApproximantRS₀ qz61)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz61) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz61) qz61 6) (@HMul.hMul Real Real Real qz5 qz659 (Zeta.RiemannSiegel.correction qz63))) Bool.false 33274465139920088745 18446744073709551616 3587024965240770556173 Ns78p414 (BSN.hardyZApproximantRS₀_eq qz61 6 (@BSN.floor_sqrt_eq_dec qz61 292316 1000 6 qz64 rfl rfl rfl)) (@Ns78p416 33274465139920088745 18446744073709551616 3587024965240770556173 Ns78p414 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz61) qz61 6) (@HAdd.hAdd Real Real Real qz351 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 6)) Bool.false 17006541 8388608 6441 4194304 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz61) qz61 6) (Ns78p469 (Ns78p468 rfl rfl rfl rfl) rfl rfl)) (Ns78p507 rfl) rfl rfl)) 

theorem RS079to096.d38 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz61) Bool.false 33274465139920088745 18446744073709551616 3587024965240770556173 Ns78p414 := Ns78p508 

noncomputable def Ns78p509 := nat_lit 8079174466170965805443842048 

noncomputable abbrev qz859 := (Enclosure.sfrac Bool.false 294360 1000)

noncomputable abbrev qz663 := qz859

noncomputable abbrev qz414 := qz663

noncomputable abbrev qz74 := qz414

noncomputable abbrev qz860 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 294360 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz664 := qz860

noncomputable abbrev qz415 := qz664

noncomputable abbrev qz75 := qz415

noncomputable abbrev qz861 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 294360 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz665 := qz861

noncomputable abbrev qz416 := qz665

noncomputable abbrev qz76 := qz416

noncomputable abbrev qz666 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz75 qz9))

noncomputable def Ns78p510 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz74) qz74 6) (@HMul.hMul Real Real Real qz5 qz666 (Zeta.RiemannSiegel.correction qz76)) 19445985 33554432 51895 33554432 69729469098801864509 295147905179352825856 4170588251464729676887 Ns78p174 Ns78p509 

noncomputable def Ns78p511 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz74) qz74 Real.sin BSN.quadSignNeg 5 6 294360 1000 69 67108864 33554432 1125899906842624 Bool.false 28092978774 1165 120242927 62 27397080 8 

noncomputable def Ns78p512 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz74) qz74 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 294360 1000 6 35 67108864 33554432 1125899906842624 Bool.false 28092978774 1165 

noncomputable def Ns78p513 := Ns78p512 93032624 61 33554424 8 108007536 61 30011992 8 Bool.false 1487176 25826 Bool.false 75409430 Bool.true 10617025 3537118876014220 1 Bool.false 29015178 Bool.true Bool.false 10572791 Bool.false Bool.true 8292115 

noncomputable def Ns78p514 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz74) qz74 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 294360 1000 136 60 67108864 33554432 1125899906842624 Bool.false 28092978774 1165 

noncomputable def Ns78p515 := Ns78p514 46516304 61 47453136 16 73726608 61 38745320 8 Bool.true 47415912 1237 Bool.false 64086967 Bool.false 65953019 3537118876014220 1 Bool.false 38764298 Bool.false Bool.false 37226257 Bool.false Bool.false 1487176 

noncomputable def Ns78p516 := nat_lit 958173671720895947647490367712093006256659191 

noncomputable def Ns78p517 := nat_lit 2288897419530334289044455638035118371635200 

noncomputable def Ns78p518 := nat_lit 28235289600000000000000000 

noncomputable def Ns78p519 := nat_lit 1060811900211048081896448000000000 

noncomputable def Ns78p520 := nat_lit 1873566068368109754501356359680000000 

noncomputable abbrev qz417 := (@Eq.refl Real qz663)

noncomputable abbrev qz77 := qz417

noncomputable def Ns78p521 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz74 294360 1000 346592238400 16000000 588720 4000 2000 Ns78p519 Ns78p520 qz77 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns78p522 := nat_lit 176610571171595541070385424576692982913227422085120000000 

noncomputable abbrev qz418 := (Real.log (Enclosure.sfrac Bool.false 346592238400 16000000))

noncomputable abbrev qz419 := (Enclosure.sfrac Bool.false 294360 2000)

noncomputable abbrev qz78 := (@HSub.hSub Real Real Real qz339 (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 294360 4000) qz418) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 588720)))))) qz419)

noncomputable abbrev qz420 := (@HSub.hSub Real Real Real qz12 qz78 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 294360 2000) (Real.log Real.pi)))

noncomputable def Ns78p523 := @Enclosure.Real.IsNear.addLit_ft_p qz420 (Enclosure.sfrac Bool.true Ns78p519 Ns78p520) 94264522093436939859 225179981368524800 489585258676959108871 Ns78p518 Ns78p519 Ns78p520 0 1 Ns78p522 

noncomputable def Ns78p524 := nat_lit 158149624829836372239345254400 

noncomputable abbrev qz421 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 294360 2000) (Real.log Real.pi))

noncomputable def Ns78p525 := @Enclosure.Real.IsNear.subLit_ff_p qz78 qz421 132203148019543387731 225179981368524800 1889750227290772457 220588200000000000000000 282664790199 1677721600 7359 838860800 Ns78p524 94264522093436939859 225179981368524800 

noncomputable abbrev qz79 := (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 294360 4000) qz418) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 588720))))))

noncomputable def Ns78p526 := @Enclosure.Real.IsNear.subLit_ff_p qz79 qz419 33069027535472573559 45035996273704960 1889750227290772457 220588200000000000000000 294360 2000 0 1 52881259207817355092400 132203148019543387731 225179981368524800 1889750227290772457 220588200000000000000000 

noncomputable def Ns78p527 := nat_lit 74464830043129476987412454553157632 

noncomputable def Ns78p528 := nat_lit 12069087910273383095336960 

noncomputable def Ns78p529 := nat_lit 17818250449303357617121090865065111726077390213173668711751863308877698241344307200000000000000000 

noncomputable def Ns78p530 := nat_lit 115643697399394509064878142298465053470689917894024975704228492149061253846794240000000000000000 

noncomputable def Ns78p531 := nat_lit 271590175430643054244588666910252549622742601626220236148787071251434700800000000000000000 

noncomputable def Ns78p532 := BSN.log_dyadic_bound 84448238400 608736238400 5 4 Ns78p529 33554432 8823528 Ns78p530 Ns78p531 9370243 693184476800 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 84448238400) (BSN.artanhQ 608736238400) 0 4 Ns78p530 Ns78p529 Ns78p531 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns78p533 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 294360 4000) qz418 294360 4000 0 1 22480428051712705 2251799813685248 62500007720587 551470500000000000000 33086694006510759219 45035996273704960 153312518938599911 18382350000000000000000 (Enclosure.Real.IsNear.const Bool.false 294360 4000) (BSN.isNear_log_sfrac 346592238400 16000000 22480428051712705 2251799813685248 62500007720587 551470500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 346592238400) qz347)) Bool.false Ns78p528 Ns78p84 1000000123529392 8823528000000000000000 22480428051712705 2251799813685248 62500007720587 551470500000000000000 (BSN.log_rat_reduce_isNear 346592238400 16000000 14 693184476800 524288000000 9370243 33554432 24973259072661432 36028797018963968 8823528 1000000000000000 rfl rfl rfl rfl (Ns78p532 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns78p534 := BSN.arctan_dyadic_bound_f 1000 588720 1 0 4194304 1102941 0 1 1 0 1 1 7124 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 588720) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 588720) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz422 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 588720)))

noncomputable def Ns78p535 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz422 884279719003555 562949953421312 1 2000000000000000 7124 4194304 1 1102941 3704927507067313324032 883323551909283 562949953421312 2000000001102941 2205882000000000000000 qz17 (Ns78p534 rfl) rfl rfl 

noncomputable def Ns78p536 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 294360 4000) qz418) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz422)) 33086694006510759219 45035996273704960 153312518938599911 18382350000000000000000 883323551909283 2251799813685248 2000000001102941 8823528000000000000000 Ns78p527 33069027535472573559 45035996273704960 1889750227290772457 220588200000000000000000 (Ns78p533 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz422) 1 4 0 1 883323551909283 562949953421312 2000000001102941 2205882000000000000000 883323551909283 2251799813685248 2000000001102941 8823528000000000000000 qz350 Ns78p535 rfl) 

noncomputable def Ns78p537 := @Ns78p523 Ns78p516 Ns78p517 489585258676959108871 Ns78p518 (@Ns78p525 489585258676959108871 Ns78p518 (Ns78p526 (Ns78p536 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 294360 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz419 (Real.log Real.pi) 294360 2000 0 1 38410761 33554432 1 16777216 282664790199 1677721600 7359 838860800 (Enclosure.Real.IsNear.const Bool.false 294360 2000) RS079to096.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns78p519 Ns78p520) 

noncomputable def Ns78p538 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz74) Bool.false Ns78p516 Ns78p517 489585258676959108871 Ns78p518 1755811173 4194304 147 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz74) (@HAdd.hAdd Real Real Real qz351 qz420 (Enclosure.sfrac Bool.true Ns78p519 Ns78p520)) Bool.false Ns78p516 Ns78p517 489585258676959108871 Ns78p518 Ns78p521 (Ns78p537 rfl rfl)) 

noncomputable def Ns78p539 := nat_lit 4871463755509715807691132379274255060646488282118533280317649472727315613570736251136 

noncomputable def Ns78p540 := nat_lit 305970350525552328669815250324704227796179077150711974597160454533877424919820338462720 

noncomputable def Ns78p541 := nat_lit 1107500869487597417984098522550901239729331497579255745146028933465130200448819456 

noncomputable def Ns78p542 := nat_lit 14612176264790172228237428940777663379460006183360441329462656360315016580311311114496 

noncomputable def Ns78p543 := nat_lit 13768665773649854790141686264611690250828058471782038856872220454024484121391915230822400 

noncomputable def Ns78p544 := BSN.cos_dyadic_bound_f 13506505802 17179869184 3 2 8388608 2208037 Ns78p539 Ns78p540 Ns78p541 Ns78p542 Ns78p543 Ns78p541 5926989 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 13506505802) (BSN.cosEvenQ 17179869184) 0 2 Ns78p539 Ns78p540 Ns78p541 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 13506505802) (BSN.cosOddQ 17179869184) 0 2 Ns78p542 Ns78p543 Ns78p541 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p545 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz74) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1755811173) qz378) Bool.false 1755811173 4194304 147 8388608 Bool.true 5926989 8388608 1 1102941 (Ns78p538 rfl) (Enclosure.sfrac_false_div 1755811173 4194304) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1755811173) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 475217925767605818228736) qz397) 226375608064910080 72057594037927936 Bool.false 5926989 8388608 66 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q2 1755811173 4194304 226375608064910080 72057594037927936 66 475217925767605818228736 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 5926989 8388608 475217925767605818228736 604462909807314587353088 13506505802 17179869184 2208037 2205882 (Ns78p544 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p546 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz74) Bool.false Ns78p516 Ns78p517 489585258676959108871 Ns78p518 28092978774 67108864 1165 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz74) (@HAdd.hAdd Real Real Real qz351 qz420 (Enclosure.sfrac Bool.true Ns78p519 Ns78p520)) Bool.false Ns78p516 Ns78p517 489585258676959108871 Ns78p518 Ns78p521 (Ns78p537 rfl rfl)) 

noncomputable def Ns78p547 := Ns78p515 25826 BSN.abs_quadSignPos (BSN.cos_quad_nat0 136 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 38764298 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 60 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 37226257 67108864) qz77 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 1) Bool.true 5926989 8388608 170520935 9252139696128 47415912 67108864 1237 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz74)) Bool.true 5926989 8388608 170520935 9252139696128 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz74) qz74) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz74)) Bool.true 5926989 8388608 170520935 9252139696128 5926989 8388608 170520935 9252139696128 (Ns78p545 rfl rfl) rfl)) rfl) (Ns78p546 rfl) RS079to096.d7 

noncomputable def Ns78p548 := nat_lit 575072565534903022504531974636526750428868702247647404371777382721 

noncomputable def Ns78p549 := nat_lit 284549448425598362065397631832921690442725607686907699980626241 

noncomputable def Ns78p550 := nat_lit 1724648597707857870789465128645914407905720655527568397715370895681 

noncomputable def Ns78p551 := BSN.cos_dyadic_bound_f 64086967 67108864 3 2 67108864 33554432 Ns78p548 Ns78p116 Ns78p549 Ns78p550 Ns78p119 Ns78p549 38764298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 64086967) qz357 0 2 Ns78p548 Ns78p116 Ns78p549 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 64086967) (BSN.cosOddQ 67108864) 0 2 Ns78p550 Ns78p119 Ns78p549 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p552 := nat_lit 645072664051255303885599889009864515140638237537261428522325847521 

noncomputable def Ns78p553 := nat_lit 357995395944240802150026416777554841495763100481633047013699041 

noncomputable def Ns78p554 := nat_lit 1934502001361877430052499614196038435738923186410821019472950144481 

noncomputable def Ns78p555 := BSN.cos_dyadic_bound_f 65953019 67108864 3 2 67108864 33554432 Ns78p552 Ns78p116 Ns78p553 Ns78p554 Ns78p119 Ns78p553 37226257 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 65953019) qz357 0 2 Ns78p552 Ns78p116 Ns78p553 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 65953019) (BSN.cosOddQ 67108864) 0 2 Ns78p554 Ns78p119 Ns78p553 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p556 := nat_lit 265753789044689055949974449084403294272142835156609088074549906736780741190399650642005295485504000000 

noncomputable def Ns78p557 := nat_lit 33814883615035296630091312937733899168715830311203550556812116413675226319436712001000000000000 

noncomputable def Ns78p558 := nat_lit 1611220421332591702989684365935292223054407205076100928013489219770805421933419719946797950135257600000 

noncomputable def Ns78p559 := BSN.cos_dyadic_bound_f 75409430 67108864 4 3 67108864 33554432 Ns78p556 Ns78p110 Ns78p557 Ns78p558 Ns78p113 Ns78p557 29015178 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 75409430) qz357 0 3 Ns78p556 Ns78p110 Ns78p557 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 75409430) (BSN.cosOddQ 67108864) 0 3 Ns78p558 Ns78p113 Ns78p557 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p560 := nat_lit 12706073404612935547312890625 

noncomputable def Ns78p561 := BSN.sin_dyadic_bound_f 10617025 67108864 2 1 67108864 33554432 Ns78p560 Ns78p106 Ns78p560 Ns78p560 Ns78p107 Ns78p560 10572791 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 10617025) qz356 0 1 Ns78p560 Ns78p106 Ns78p560 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 10617025) (BSN.sinOddQ 67108864) 0 1 Ns78p560 Ns78p107 Ns78p560 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p562 := Ns78p513 43958 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 6 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 29015178 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 35 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 10572791 67108864) qz77 rfl rfl (Ns78p547 RS079to096.d9 RS079to096.d11 RS079to096.d13 RS079to096.d17 (Ns78p551 rfl rfl) (Ns78p555 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns78p546 rfl) RS079to096.d19 RS079to096.d21 RS079to096.d23 RS079to096.d25 RS079to096.d17 (Ns78p559 rfl rfl) (Ns78p561 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns78p563 := nat_lit 626915068654533977008588960000 

noncomputable def Ns78p564 := BSN.sin_dyadic_bound_f 28138580 67108864 2 1 67108864 33554432 Ns78p563 Ns78p106 Ns78p563 Ns78p563 Ns78p107 Ns78p563 27321288 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 28138580) qz356 0 1 Ns78p563 Ns78p106 Ns78p563 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 28138580) (BSN.sinOddQ 67108864) 0 1 Ns78p563 Ns78p107 Ns78p563 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p565 := Ns78p511 Bool.true 8292115 43958 Bool.true 28138580 3537118876014220 1 Bool.false 27321288 Bool.true Bool.true 19445985 51895 BSN.abs_quadSignNeg qz635 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 27321288 67108864) qz77 rfl (Ns78p562 rfl rfl) (Ns78p546 rfl) RS079to096.d27 RS079to096.d29 RS079to096.d17 (Ns78p564 rfl rfl) rfl 

noncomputable def Ns78p566 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 6) 19445985 67108864 51895 67108864 19445985 67108864 51895 67108864 2609995925422080 19445985 33554432 51895 33554432 (Ns78p565 rfl rfl rfl rfl) 

noncomputable def Ns78p567 := @Enclosure.Real.IsNear.mulLit_ff qz666 (Zeta.RiemannSiegel.correction qz76) 3206381 8388608 1 8388608 21747094028689 35184372088832 973665878922029 9701571634007113728 69729469098801864509 295147905179352825856 

noncomputable abbrev qz667 := (@HPow.hPow Real Real Real qz7 qz75 qz9)

noncomputable def Ns78p568 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz667 1 1 0 1 3206381 8388608 1 8388608 3206381 8388608 1 8388608 

noncomputable def Ns78p569 := @Enclosure.Real.IsNear.sqrt_image qz75 9824919951 209715200 7359 209715200 28708420 28708442 4194304 (@Enclosure.Real.IsNear.of_eq qz75 (@HMul.hMul Real Real Real qz5 qz74 qz3) Bool.false 9824919951 209715200 7359 209715200 (BSN.t_div_two_pi_mk qz74 294360 1000 qz77) (@Enclosure.Real.IsNear.mulLit_ff qz74 qz3 294360 1000 0 1 1335089 8388608 1 8388608 9824919951 209715200 7359 209715200 (Enclosure.Real.IsNear.const Bool.false 294360 1000) RS079to096.d32 rfl)) 

noncomputable abbrev qz862 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 294360 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz668 := qz862

noncomputable abbrev qz423 := qz668

noncomputable abbrev qz80 := qz423

noncomputable def Ns78p570 := @Enclosure.Real.IsNear.sqrt_image qz80 28708431 4194304 11 4194304 10973232 10973238 4194304 (@Enclosure.Real.IsNear.recentre' qz80 Bool.false 57416862 8388608 22 8388608 28708431 4194304 11 4194304 (Ns78p569 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns78p571 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz80) 10973235 4194304 3 4194304 1603190 1603191 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz80) Bool.false 21946470 8388608 6 8388608 10973235 4194304 3 4194304 (Ns78p570 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns78p572 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz80)) Bool.false 3206381 8388608 1 8388608 3206381 8388608 1 8388608 (Ns78p571 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz81 := (@HMul.hMul Real Real Real qz336 qz334 qz416)

noncomputable abbrev qz669 := (@HMul.hMul Real Real Real qz841 qz861 qz861)

noncomputable abbrev qz424 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz669 qz665) qz640)

noncomputable abbrev qz82 := (Real.cos (@HMul.hMul Real Real Real qz336 qz334 qz424))

noncomputable def Ns78p573 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz76) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz81)) qz82) Bool.false 21747094028689 

noncomputable def Ns78p574 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz81)) qz82 14976337 8388608 469 

noncomputable def Ns78p575 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz81)) Bool.false 14976337 8388608 469 8388608 14976337 8388608 469 

noncomputable def Ns78p576 := @Enclosure.Real.IsNear.recentre' (Real.cos qz81) Bool.false 4698662 8388608 161697407 9252139696128 2349331 4194304 161697407 9252139696128 

noncomputable def Ns78p577 := @Enclosure.Real.IsNear.cos_image qz81 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2782357) (@Nat.cast Real Real.instNatCast 524288)) Bool.false 2782357 524288 139 8388608 Bool.false 4698662 8388608 1 

noncomputable def Ns78p578 := nat_lit 296846829529915262422019981 

noncomputable def Ns78p579 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz76 884279719003555 140737488355328 1 500000000000000 3542607 4194304 11 4194304 3132655522500026967885 590295810358705651712 Ns78p578 

noncomputable def Ns78p580 := @Enclosure.Real.IsNear.subLit_ff_p qz80 qz1 28708431 4194304 11 4194304 6 1 0 1 3542607 3542607 4194304 11 

noncomputable def Ns78p581 := @Ns78p580 4194304 (@Enclosure.Real.IsNear.recentre' qz80 Bool.false 57416862 8388608 22 8388608 28708431 4194304 11 4194304 (Ns78p569 rfl rfl rfl rfl rfl rfl) rfl) qz362 

noncomputable def Ns78p582 := @Enclosure.Real.IsNear.recentre' qz81 Bool.false 3132655522500026967885 590295810358705651712 Ns78p578 Ns78p146 2782357 524288 139 8388608 (@Ns78p579 Ns78p146 RS079to096.d31 (Ns78p581 rfl rfl) rfl) 

noncomputable def Ns78p583 := nat_lit 10884076082897917770375235411392658575616 

noncomputable def Ns78p584 := BSN.sin_dyadic_bound_f 10214047948 17179869184 2 1 8388608 2208037 Ns78p583 Ns78p255 Ns78p583 Ns78p583 Ns78p256 Ns78p583 4698662 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 10214047948) qz352 0 1 Ns78p583 Ns78p255 Ns78p583 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 10214047948) qz353 0 1 Ns78p583 Ns78p256 Ns78p583 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p585 := @Ns78p577 1102941 (Ns78p582 rfl) (Enclosure.sfrac_false_div 2782357 524288) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2782357) (@Nat.cast Real Real.instNatCast 524288)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 44921857945767388381184) (@Nat.cast Real Real.instNatCast 75557863725914323419136)) 226375608064910080 72057594037927936 Bool.false 4698662 8388608 0 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q3 2782357 524288 226375608064910080 72057594037927936 0 44921857945767388381184 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 4698662 8388608 44921857945767388381184 75557863725914323419136 10214047948 17179869184 2208037 2205882 (Ns78p584 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p586 := @Enclosure.Real.IsNear.inv_image (Real.cos qz81) 2349331 4194304 161697407 9252139696128 7487934 7488403 4194304 (Ns78p576 (Ns78p585 rfl rfl) rfl) rfl 

noncomputable def Ns78p587 := @Enclosure.Real.IsNear.recentre' qz82 Bool.false 1452097 4194304 

noncomputable abbrev qz83 := (@HMul.hMul Real Real Real qz336 qz334 qz424)

noncomputable def Ns78p588 := @Enclosure.Real.IsNear.cos_image qz83 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 2552803)) qz398) Bool.true 2552803 2097152 

noncomputable def Ns78p589 := nat_lit 3013818039297602713670494525 

noncomputable def Ns78p590 := nat_lit 3348292421926767272417274887770133 

noncomputable def Ns78p591 := @Enclosure.Real.IsNear.recentre' qz83 Bool.true Ns78p589 Ns78p157 Ns78p590 

noncomputable abbrev qz84 := qz424

noncomputable def Ns78p592 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz84 884279719003555 140737488355328 1 500000000000000 3408217981855 

noncomputable abbrev qz425 := (@HSub.hSub Real Real Real qz634 qz669 qz665)

noncomputable abbrev qz85 := qz425

noncomputable def Ns78p593 := @Enclosure.Real.IsNear.subLit_tf qz85 qz26 2308706354079 17592186044416 124074819 17592186044416 1 16 

noncomputable abbrev qz426 := qz669

noncomputable abbrev qz86 := qz426

noncomputable def Ns78p594 := @Enclosure.Real.IsNear.subLit_ff_n qz86 qz76 12550064356449 17592186044416 77937475 17592186044416 3542607 4194304 11 4194304 

noncomputable def Ns78p595 := @Enclosure.Real.IsNear.mulLit_ff qz76 qz76 3542607 4194304 11 4194304 3542607 4194304 11 4194304 12550064356449 17592186044416 

noncomputable def Ns78p596 := nat_lit 1381864086212985520714539128662169309206307762451668641 

noncomputable def Ns78p597 := nat_lit 1803592465917309712163625213528025006490960869875361 

noncomputable def Ns78p598 := nat_lit 4141985073707121942719290135559451877605941365615255201 

noncomputable def Ns78p599 := BSN.cos_dyadic_bound_f 2552803 2097152 3 2 4194304 1102941 Ns78p596 Ns78p406 Ns78p597 Ns78p598 Ns78p409 Ns78p597 1452097 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2552803) (BSN.cosEvenQ 2097152) 0 2 Ns78p596 Ns78p406 Ns78p597 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2552803) (BSN.cosOddQ 2097152) 0 2 Ns78p598 Ns78p409 Ns78p597 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p600 := @Ns78p587 419785601 9252139696128 1452097 4194304 419785601 9252139696128 (@Ns78p588 373 8388608 Bool.false 1452097 4194304 1 1102941 (@Ns78p591 Ns78p160 2552803 2097152 373 8388608 (@Ns78p592 17592186044416 124074819 17592186044416 Ns78p589 Ns78p157 Ns78p590 Ns78p160 RS079to096.d31 (@Ns78p593 0 1 54531487709680 3408217981855 17592186044416 124074819 17592186044416 (@Ns78p594 9683416295738966016 2308706354079 17592186044416 124074819 17592186044416 (@Ns78p595 77937475 17592186044416 (Ns78p581 rfl rfl) (Ns78p581 rfl rfl) rfl) (Ns78p581 rfl rfl) rfl rfl) qz366 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 2552803 2097152) (BSN.cos_neg_of_bound 2552803 2097152 Bool.false 1452097 4194304 1 1102941 (Ns78p599 rfl rfl)) rfl rfl) 

noncomputable def Ns78p601 := @Ns78p567 4170588251464729676887 Ns78p174 (Ns78p568 qz28 (@Enclosure.Real.IsNear.of_eq qz667 (@Inv.inv Real Real.instInv (Real.sqrt qz80)) Bool.false 3206381 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz75 (BSN.t_div_two_pi_nonneg qz74 294360 1000 qz77)) Ns78p572) rfl) (@Ns78p573 35184372088832 973665878922029 9701571634007113728 (BSN.correction_mk qz76 (BSN.cos_two_pi_p_ne_zero_mk qz74 294360 1000 6 qz77 rfl rfl (@BSN.floor_sqrt_eq_dec qz74 294360 1000 6 qz77 rfl rfl rfl))) (@Ns78p574 8388608 1452097 4194304 419785601 9252139696128 21747094028689 35184372088832 973665878922029 9701571634007113728 (@Ns78p575 8388608 (Ns78p586 rfl rfl rfl rfl rfl) rfl) (Ns78p600 rfl) rfl)) 

noncomputable def Ns78p602 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz74) (hardyZApproximantRS₀ qz74) Bool.true 240778162067263299389 295147905179352825856 171991608233731118648407 Ns78p174 (@Eq.refl Real (hardyZApproximantRS₀ qz74)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz74) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz74) qz74 6) (@HMul.hMul Real Real Real qz5 qz666 (Zeta.RiemannSiegel.correction qz76))) Bool.true 240778162067263299389 295147905179352825856 171991608233731118648407 Ns78p174 (BSN.hardyZApproximantRS₀_eq qz74 6 (@BSN.floor_sqrt_eq_dec qz74 294360 1000 6 qz77 rfl rfl rfl)) (@Ns78p510 240778162067263299389 295147905179352825856 171991608233731118648407 Ns78p174 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz74) qz74 6) (@HAdd.hAdd Real Real Real qz351 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz74) qz74 6)) Bool.true 19445985 33554432 51895 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz74) qz74 6) (Ns78p566 (Ns78p565 rfl rfl rfl rfl) rfl rfl)) (Ns78p601 rfl) rfl rfl)) 

theorem RS079to096.d39 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz74) Bool.true 240778162067263299389 295147905179352825856 171991608233731118648407 Ns78p174 := Ns78p602 

noncomputable def Ns78p603 := nat_lit 162765362843210292551221248 

noncomputable def Ns78p604 := nat_lit 949185045982169601637613568 

noncomputable abbrev qz863 := (Enclosure.sfrac Bool.false 295176 1000)

noncomputable abbrev qz670 := qz863

noncomputable abbrev qz427 := qz670

noncomputable abbrev qz87 := qz427

noncomputable abbrev qz864 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 295176 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz671 := qz864

noncomputable abbrev qz428 := qz671

noncomputable abbrev qz88 := qz428

noncomputable abbrev qz865 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 295176 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz672 := qz865

noncomputable abbrev qz429 := qz672

noncomputable abbrev qz89 := qz429

noncomputable abbrev qz673 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz88 qz9))

noncomputable def Ns78p605 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz87) qz87 6) (@HMul.hMul Real Real Real qz5 qz673 (Zeta.RiemannSiegel.correction qz89)) 14540565 33554432 52035 33554432 35662162421790916011 147573952589676412928 5817724980663144129025 Ns78p603 Ns78p604 

noncomputable def Ns78p606 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz87) qz87 Real.sin BSN.quadSignNeg 5 6 295176 1000 69 67108864 33554432 1125899906842624 Bool.false 28198347031 1168 120242927 62 27397080 8 

noncomputable def Ns78p607 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz87) qz87 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 295176 1000 6 34 67108864 33554432 1125899906842624 Bool.false 28198347031 1168 

noncomputable def Ns78p608 := Ns78p607 93032624 61 33554424 8 108007536 61 30011992 8 Bool.false 26161343 25894 Bool.false 104863066 Bool.true 98797275 3537118876014220 1 Bool.false 551284 Bool.true Bool.false 6606364 Bool.true Bool.false 22931245 

noncomputable def Ns78p609 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz87) qz87 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 295176 1000 137 61 67108864 33554432 1125899906842624 Bool.false 28198347031 1168 

noncomputable def Ns78p610 := Ns78p609 46516304 61 47453136 16 73726608 61 38745320 8 Bool.false 47457728 1237 Bool.false 26083563 Bool.false 5746006 3537118876014220 1 Bool.false 25431771 Bool.true Bool.false 5738987 Bool.true Bool.false 26161343 

noncomputable def Ns78p611 := nat_lit 76396523615547624297714742305197639734470928222057 

noncomputable def Ns78p612 := nat_lit 181815051345677899295474094097543508361478144000 

noncomputable def Ns78p613 := nat_lit 141176448000000000000000000 

noncomputable def Ns78p614 := nat_lit 1075597069547516759063334420480000 

noncomputable def Ns78p615 := nat_lit 1904945194384899332257065510933626880 

noncomputable abbrev qz430 := (@Eq.refl Real qz670)

noncomputable abbrev qz90 := qz430

noncomputable def Ns78p616 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz87 295176 1000 348516483904 16000000 590352 4000 2000 Ns78p614 Ns78p615 qz90 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns78p617 := nat_lit 901210062900335239075506003308417853174891615352930959360 

noncomputable abbrev qz431 := (Real.log (Enclosure.sfrac Bool.false 348516483904 16000000))

noncomputable abbrev qz432 := (Enclosure.sfrac Bool.false 295176 2000)

noncomputable abbrev qz91 := (@HSub.hSub Real Real Real qz339 (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 295176 4000) qz431) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 590352)))))) qz432)

noncomputable abbrev qz433 := (@HSub.hSub Real Real Real qz12 qz91 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 295176 2000) (Real.log Real.pi)))

noncomputable def Ns78p618 := @Enclosure.Real.IsNear.addLit_ft_p qz433 (Enclosure.sfrac Bool.true Ns78p614 Ns78p615) 473090394711315492997 1125899906842624000 2454623520777741573593 Ns78p613 Ns78p614 Ns78p615 0 1 Ns78p617 

noncomputable def Ns78p619 := nat_lit 3968569869798498835078578176000 

noncomputable abbrev qz434 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 295176 2000) (Real.log Real.pi))

noncomputable def Ns78p620 := @Enclosure.Real.IsNear.subLit_ff_p qz91 qz434 663309375659209175173 1125899906842624000 9474251139603861781 1102941000000000000000000 1417241848617 8388608000 36897 4194304000 Ns78p619 473090394711315492997 1125899906842624000 

noncomputable abbrev qz92 := (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 295176 4000) qz431) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 590352))))))

noncomputable def Ns78p621 := @Enclosure.Real.IsNear.subLit_ff_p qz92 qz432 165895738222059673217 225179981368524800 9474251139603861781 1102941000000000000000000 295176 2000 0 1 265323750263683670069200 663309375659209175173 1125899906842624000 9474251139603861781 1102941000000000000000000 

noncomputable def Ns78p622 := nat_lit 373563992419610647450071655373602816 

noncomputable def Ns78p623 := nat_lit 12075781160039581126492160 

noncomputable def Ns78p624 := nat_lit 18273862329448705904468479139911060181927245831009973945871391374853371325448453908274456580587520 

noncomputable def Ns78p625 := nat_lit 123343700715364409856224667215899458589734967150953944238687543366146485074467953694496453033984 

noncomputable def Ns78p626 := nat_lit 325231478151504770126271480807082329233723982612445707916602337203146988741625946340065280 

noncomputable def Ns78p627 := BSN.log_dyadic_bound 86372483904 610660483904 5 4 Ns78p624 33554432 8823528 Ns78p625 Ns78p626 9556018 697032967808 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 86372483904) (BSN.artanhQ 610660483904) 0 4 Ns78p625 Ns78p624 Ns78p626 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns78p628 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 295176 4000) qz431 295176 4000 0 1 22492895200922305 2251799813685248 62500007720587 551470500000000000000 165984070845686057517 225179981368524800 15687501937867337 1875750000000000000000 (Enclosure.Real.IsNear.const Bool.false 295176 4000) (BSN.isNear_log_sfrac 348516483904 16000000 22492895200922305 2251799813685248 62500007720587 551470500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 348516483904) qz347)) Bool.false Ns78p623 Ns78p84 1000000123529392 8823528000000000000000 22492895200922305 2251799813685248 62500007720587 551470500000000000000 (BSN.log_rat_reduce_isNear 348516483904 16000000 14 697032967808 524288000000 9556018 33554432 24973259072661432 36028797018963968 8823528 1000000000000000 rfl rfl rfl rfl (Ns78p627 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns78p629 := BSN.arctan_dyadic_bound_f 1000 590352 1 0 4194304 1102941 0 1 1 0 1 1 7104 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 590352) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 590352) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz435 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 590352)))

noncomputable def Ns78p630 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz435 884279719003555 562949953421312 1 2000000000000000 7104 4194304 1 1102941 3704938766066381750272 883326236263843 562949953421312 2000000001102941 2205882000000000000000 qz17 (Ns78p629 rfl) rfl rfl 

noncomputable def Ns78p631 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 295176 4000) qz431) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz435)) 165984070845686057517 225179981368524800 15687501937867337 1875750000000000000000 883326236263843 2251799813685248 2000000001102941 8823528000000000000000 Ns78p622 165895738222059673217 225179981368524800 9474251139603861781 1102941000000000000000000 (Ns78p628 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz435) 1 4 0 1 883326236263843 562949953421312 2000000001102941 2205882000000000000000 883326236263843 2251799813685248 2000000001102941 8823528000000000000000 qz350 Ns78p630 rfl) 

noncomputable def Ns78p632 := @Ns78p618 Ns78p611 Ns78p612 2454623520777741573593 Ns78p613 (@Ns78p620 2454623520777741573593 Ns78p613 (Ns78p621 (Ns78p631 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 295176 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz432 (Real.log Real.pi) 295176 2000 0 1 38410761 33554432 1 16777216 1417241848617 8388608000 36897 4194304000 (Enclosure.Real.IsNear.const Bool.false 295176 2000) RS079to096.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns78p614 Ns78p615) 

noncomputable def Ns78p633 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz87) Bool.false Ns78p611 Ns78p612 2454623520777741573593 Ns78p613 1762396689 4194304 147 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz87) (@HAdd.hAdd Real Real Real qz351 qz433 (Enclosure.sfrac Bool.true Ns78p614 Ns78p615)) Bool.false Ns78p611 Ns78p612 2454623520777741573593 Ns78p613 Ns78p616 (Ns78p632 rfl rfl)) 

noncomputable def Ns78p634 := nat_lit 8737140303939021104838934974839280548737657571441690375794973046963709382661376458945 

noncomputable def Ns78p635 := nat_lit 1099782703921844955496680329670580243052870438786038260223852101932427917649133761 

noncomputable def Ns78p636 := nat_lit 22881205909748229430364501737378649069157493754017821207994090791025633976055982604481 

noncomputable def Ns78p637 := BSN.sin_dyadic_bound_f 13494703929 17179869184 3 2 8388608 2208037 Ns78p634 Ns78p97 Ns78p635 Ns78p636 Ns78p100 Ns78p635 5932216 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 13494703929) qz352 0 2 Ns78p634 Ns78p97 Ns78p635 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 13494703929) qz353 0 2 Ns78p636 Ns78p100 Ns78p635 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p638 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz87) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1762396689) qz378) Bool.false 1762396689 4194304 147 8388608 Bool.false 5932216 8388608 1 1102941 (Ns78p633 rfl) (Enclosure.sfrac_false_div 1762396689 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1762396689) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474802684275079268794368) qz397) 226375608064910080 72057594037927936 Bool.false 5932216 8388608 66 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q3 1762396689 4194304 226375608064910080 72057594037927936 66 474802684275079268794368 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 5932216 8388608 474802684275079268794368 604462909807314587353088 13494703929 17179869184 2208037 2205882 (Ns78p637 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p639 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz87) Bool.false Ns78p611 Ns78p612 2454623520777741573593 Ns78p613 28198347031 67108864 1168 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz87) (@HAdd.hAdd Real Real Real qz351 qz433 (Enclosure.sfrac Bool.true Ns78p614 Ns78p615)) Bool.false Ns78p611 Ns78p612 2454623520777741573593 Ns78p613 Ns78p616 (Ns78p632 rfl rfl)) 

noncomputable def Ns78p640 := Ns78p610 25894 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 137 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 25431771 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 61 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 5738987 67108864) qz90 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 1) Bool.false 741527 1048576 170520935 9252139696128 47457728 67108864 1237 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz87)) Bool.false 741527 1048576 170520935 9252139696128 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz87) qz87) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz87)) Bool.false 5932216 8388608 170520935 9252139696128 741527 1048576 170520935 9252139696128 (Ns78p638 rfl rfl) rfl)) rfl) (Ns78p639 rfl) RS079to096.d7 

noncomputable def Ns78p641 := nat_lit 462879196020202382660580950961 

noncomputable def Ns78p642 := BSN.sin_dyadic_bound_f 26083563 67108864 2 1 67108864 33554432 Ns78p641 Ns78p106 Ns78p641 Ns78p641 Ns78p107 Ns78p641 25431771 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 26083563) qz356 0 1 Ns78p641 Ns78p106 Ns78p641 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 26083563) (BSN.sinOddQ 67108864) 0 1 Ns78p641 Ns78p107 Ns78p641 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p643 := nat_lit 1090094881895010036420545296 

noncomputable def Ns78p644 := BSN.sin_dyadic_bound_f 5746006 67108864 2 1 67108864 33554432 Ns78p643 Ns78p106 Ns78p643 Ns78p643 Ns78p107 Ns78p643 5738987 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 5746006) qz356 0 1 Ns78p643 Ns78p106 Ns78p643 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 5746006) (BSN.sinOddQ 67108864) 0 1 Ns78p643 Ns78p107 Ns78p643 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p645 := nat_lit 996309386482395304163917779909378482975145562112374439430408767394985205622723793760466294769563406336 

noncomputable def Ns78p646 := nat_lit 1767952604717944903003412111551439733719528861185472427075340685205089508796215724381617811296256 

noncomputable def Ns78p647 := nat_lit 6030019285937664193209868056051312442255096004643072630334199612156262710967284477175789648737574522880 

noncomputable def Ns78p648 := BSN.cos_dyadic_bound_f 104863066 67108864 4 3 67108864 33554432 Ns78p645 Ns78p110 Ns78p646 Ns78p647 Ns78p113 Ns78p646 551284 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 104863066) qz357 0 3 Ns78p645 Ns78p110 Ns78p646 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 104863066) (BSN.cosOddQ 67108864) 0 3 Ns78p647 Ns78p113 Ns78p646 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p649 := nat_lit 784436504090081482092882248786369577871204752123276121783133503573834730138464510842806549708994140625 

noncomputable def Ns78p650 := nat_lit 864847618601365049232014423323228479378993705416454358993701143228207118875460684299468994140625 

noncomputable def Ns78p651 := nat_lit 4750064253597650719352601525328001396030233791821682011698706282436962929854379461035745950924994140625 

noncomputable def Ns78p652 := BSN.cos_dyadic_bound_f 98797275 67108864 4 3 67108864 33554432 Ns78p649 Ns78p110 Ns78p650 Ns78p651 Ns78p113 Ns78p650 6606364 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 98797275) qz357 0 3 Ns78p649 Ns78p110 Ns78p650 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 98797275) (BSN.cosOddQ 67108864) 0 3 Ns78p651 Ns78p113 Ns78p650 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p653 := Ns78p608 44076 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 6 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 551284 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 34 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 6606364 67108864) qz90 rfl rfl (Ns78p640 RS079to096.d9 RS079to096.d11 RS079to096.d13 RS079to096.d17 (Ns78p642 rfl rfl) (Ns78p644 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns78p639 rfl) RS079to096.d19 RS079to096.d21 RS079to096.d23 RS079to096.d25 RS079to096.d17 (Ns78p648 rfl rfl) (Ns78p652 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns78p654 := nat_lit 190385232764955201307221919201 

noncomputable def Ns78p655 := BSN.sin_dyadic_bound_f 20888551 67108864 2 1 67108864 33554432 Ns78p654 Ns78p106 Ns78p654 Ns78p654 Ns78p107 Ns78p654 20552883 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 20888551) qz356 0 1 Ns78p654 Ns78p106 Ns78p654 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 20888551) (BSN.sinOddQ 67108864) 0 1 Ns78p654 Ns78p107 Ns78p654 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p656 := Ns78p606 Bool.false 22931245 44076 Bool.true 20888551 3537118876014220 1 Bool.false 20552883 Bool.true Bool.false 14540565 52035 BSN.abs_quadSignNeg qz635 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 20552883 67108864) qz90 rfl (Ns78p653 rfl rfl) (Ns78p639 rfl) RS079to096.d27 RS079to096.d29 RS079to096.d17 (Ns78p655 rfl rfl) rfl 

noncomputable def Ns78p657 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 6) 14540565 67108864 52035 67108864 14540565 67108864 52035 67108864 1951601598136320 14540565 33554432 52035 33554432 (Ns78p656 rfl rfl rfl rfl) 

noncomputable def Ns78p658 := @Enclosure.Real.IsNear.mulLit_ff qz673 (Zeta.RiemannSiegel.correction qz89) 1602081 4194304 1 4194304 22259899731531 35184372088832 3616028158729297 38806286536028454912 35662162421790916011 147573952589676412928 

noncomputable abbrev qz674 := (@HPow.hPow Real Real Real qz7 qz88 qz9)

noncomputable def Ns78p659 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz674 1 1 0 1 1602081 4194304 1 4194304 1602081 4194304 1 4194304 

noncomputable def Ns78p660 := @Enclosure.Real.IsNear.sqrt_image qz88 49260778833 1048576000 36897 1048576000 28748184 28748206 4194304 (@Enclosure.Real.IsNear.of_eq qz88 (@HMul.hMul Real Real Real qz5 qz87 qz3) Bool.false 49260778833 1048576000 36897 1048576000 (BSN.t_div_two_pi_mk qz87 295176 1000 qz90) (@Enclosure.Real.IsNear.mulLit_ff qz87 qz3 295176 1000 0 1 1335089 8388608 1 8388608 49260778833 1048576000 36897 1048576000 (Enclosure.Real.IsNear.const Bool.false 295176 1000) RS079to096.d32 rfl)) 

noncomputable abbrev qz866 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 295176 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz675 := qz866

noncomputable abbrev qz436 := qz675

noncomputable abbrev qz93 := qz436

noncomputable def Ns78p661 := @Enclosure.Real.IsNear.sqrt_image qz93 28748195 4194304 11 4194304 10980829 10980835 4194304 (@Enclosure.Real.IsNear.recentre' qz93 Bool.false 57496390 8388608 22 8388608 28748195 4194304 11 4194304 (Ns78p660 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns78p662 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz93) 343151 131072 3 4194304 1602080 1602082 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz93) Bool.false 21961664 8388608 6 8388608 343151 131072 3 4194304 (Ns78p661 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns78p663 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz93)) Bool.false 3204162 8388608 2 8388608 1602081 4194304 1 4194304 (Ns78p662 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz94 := (@HMul.hMul Real Real Real qz336 qz334 qz429)

noncomputable abbrev qz676 := (@HMul.hMul Real Real Real qz841 qz865 qz865)

noncomputable abbrev qz437 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz676 qz672) qz640)

noncomputable abbrev qz95 := (Real.cos (@HMul.hMul Real Real Real qz336 qz334 qz437))

noncomputable def Ns78p664 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz89) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz94)) qz95) Bool.false 22259899731531 

noncomputable def Ns78p665 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz94)) qz95 13786899 8388608 397 

noncomputable def Ns78p666 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz94)) Bool.false 13786899 8388608 397 8388608 13786899 8388608 397 

noncomputable def Ns78p667 := @Enclosure.Real.IsNear.recentre' (Real.cos qz94) Bool.false 5104030 8388608 161697407 9252139696128 2552015 4194304 161697407 9252139696128 

noncomputable def Ns78p668 := @Enclosure.Real.IsNear.cos_image qz94 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 45017401) qz354) Bool.false 45017401 8388608 139 8388608 Bool.false 5104030 8388608 1 

noncomputable def Ns78p669 := nat_lit 296846829530256832581136269 

noncomputable def Ns78p670 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz89 884279719003555 140737488355328 1 500000000000000 3582371 4194304 11 4194304 3167818021246484328905 590295810358705651712 Ns78p669 

noncomputable def Ns78p671 := @Enclosure.Real.IsNear.subLit_ff_p qz93 qz1 28748195 4194304 11 4194304 6 1 0 1 3582371 3582371 4194304 11 

noncomputable def Ns78p672 := @Ns78p671 4194304 (@Enclosure.Real.IsNear.recentre' qz93 Bool.false 57496390 8388608 22 8388608 28748195 4194304 11 4194304 (Ns78p660 rfl rfl rfl rfl rfl rfl) rfl) qz362 

noncomputable def Ns78p673 := @Enclosure.Real.IsNear.recentre' qz94 Bool.false 3167818021246484328905 590295810358705651712 Ns78p669 Ns78p146 45017401 8388608 139 8388608 (@Ns78p670 Ns78p146 RS079to096.d31 (Ns78p672 rfl rfl) rfl) 

noncomputable def Ns78p674 := nat_lit 15946488488923671222489647562087552160000 

noncomputable def Ns78p675 := BSN.sin_dyadic_bound_f 11237411020 17179869184 2 1 8388608 2208037 Ns78p674 Ns78p255 Ns78p674 Ns78p674 Ns78p256 Ns78p674 5104030 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 11237411020) qz352 0 1 Ns78p674 Ns78p255 Ns78p674 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 11237411020) qz353 0 1 Ns78p674 Ns78p256 Ns78p674 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p676 := @Ns78p668 1102941 (Ns78p673 rfl) (Enclosure.sfrac_false_div 45017401 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 45017401) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 790762501346714558922752) qz355) 226375608064910080 72057594037927936 Bool.false 5104030 8388608 0 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q3 45017401 8388608 226375608064910080 72057594037927936 0 790762501346714558922752 Ns78p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 5104030 8388608 790762501346714558922752 Ns78p84 11237411020 17179869184 2208037 2205882 (Ns78p675 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p677 := @Enclosure.Real.IsNear.inv_image (Real.cos qz94) 2552015 4194304 161697407 9252139696128 6893251 6893648 4194304 (Ns78p667 (Ns78p676 rfl rfl) rfl) rfl 

noncomputable def Ns78p678 := @Enclosure.Real.IsNear.recentre' qz95 Bool.false 1614569 4194304 

noncomputable abbrev qz96 := (@HMul.hMul Real Real Real qz336 qz334 qz437)

noncomputable def Ns78p679 := @Enclosure.Real.IsNear.cos_image qz96 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 4931033)) qz378) Bool.true 4931033 4194304 

noncomputable def Ns78p680 := nat_lit 2910768218446327533620567045 

noncomputable def Ns78p681 := nat_lit 3371900056582201244949322373235357 

noncomputable def Ns78p682 := @Enclosure.Real.IsNear.recentre' qz96 Bool.true Ns78p680 Ns78p157 Ns78p681 

noncomputable abbrev qz97 := qz437

noncomputable def Ns78p683 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz97 884279719003555 140737488355328 1 500000000000000 3291682660919 

noncomputable abbrev qz438 := (@HSub.hSub Real Real Real qz634 qz676 qz672)

noncomputable abbrev qz98 := qz438

noncomputable def Ns78p684 := @Enclosure.Real.IsNear.subLit_tf qz98 qz26 2192171033143 17592186044416 124949627 17592186044416 1 16 

noncomputable abbrev qz439 := qz676

noncomputable abbrev qz99 := qz439

noncomputable def Ns78p685 := @Enclosure.Real.IsNear.subLit_ff_n qz99 qz89 12833381981641 17592186044416 78812283 17592186044416 3582371 4194304 11 4194304 

noncomputable def Ns78p686 := @Enclosure.Real.IsNear.mulLit_ff qz89 qz89 3582371 4194304 11 4194304 3582371 4194304 11 4194304 12833381981641 17592186044416 

noncomputable def Ns78p687 := nat_lit 307747190173746298700918192746233940273617053959077481921 

noncomputable def Ns78p688 := nat_lit 349545142915050499811578000285384932461688604417314241 

noncomputable def Ns78p689 := nat_lit 922542480235408795103131422238131050955927784668397817281 

noncomputable def Ns78p690 := BSN.cos_dyadic_bound_f 4931033 4194304 3 2 4194304 1102941 Ns78p687 Ns78p271 Ns78p688 Ns78p689 Ns78p274 Ns78p688 1614569 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 4931033) (BSN.cosEvenQ 4194304) 0 2 Ns78p687 Ns78p271 Ns78p688 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 4931033) (BSN.cosOddQ 4194304) 0 2 Ns78p689 Ns78p274 Ns78p688 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p691 := @Ns78p678 421991483 9252139696128 1614569 4194304 421991483 9252139696128 (@Ns78p679 375 8388608 Bool.false 1614569 4194304 1 1102941 (@Ns78p682 Ns78p160 4931033 4194304 375 8388608 (@Ns78p683 17592186044416 124949627 17592186044416 Ns78p680 Ns78p157 Ns78p681 Ns78p160 RS079to096.d31 (@Ns78p684 0 1 52666922574704 3291682660919 17592186044416 124949627 17592186044416 (@Ns78p685 9194631732995817472 2192171033143 17592186044416 124949627 17592186044416 (@Ns78p686 78812283 17592186044416 (Ns78p672 rfl rfl) (Ns78p672 rfl rfl) rfl) (Ns78p672 rfl rfl) rfl rfl) qz366 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 4931033 4194304) (BSN.cos_neg_of_bound 4931033 4194304 Bool.false 1614569 4194304 1 1102941 (Ns78p690 rfl rfl)) rfl rfl) 

noncomputable def Ns78p692 := @Ns78p658 5817724980663144129025 Ns78p603 (Ns78p659 qz28 (@Enclosure.Real.IsNear.of_eq qz674 (@Inv.inv Real Real.instInv (Real.sqrt qz93)) Bool.false 1602081 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz88 (BSN.t_div_two_pi_nonneg qz87 295176 1000 qz90)) Ns78p663) rfl) (@Ns78p664 35184372088832 3616028158729297 38806286536028454912 (BSN.correction_mk qz89 (BSN.cos_two_pi_p_ne_zero_mk qz87 295176 1000 6 qz90 rfl rfl (@BSN.floor_sqrt_eq_dec qz87 295176 1000 6 qz90 rfl rfl rfl))) (@Ns78p665 8388608 1614569 4194304 421991483 9252139696128 22259899731531 35184372088832 3616028158729297 38806286536028454912 (@Ns78p666 8388608 (Ns78p677 rfl rfl rfl rfl rfl) rfl) (Ns78p691 rfl) rfl)) 

noncomputable def Ns78p693 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz87) (hardyZApproximantRS₀ qz87) Bool.false 28287918745940017749 147573952589676412928 258228364968443225547265 Ns78p603 (@Eq.refl Real (hardyZApproximantRS₀ qz87)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz87) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz87) qz87 6) (@HMul.hMul Real Real Real qz5 qz673 (Zeta.RiemannSiegel.correction qz89))) Bool.false 28287918745940017749 147573952589676412928 258228364968443225547265 Ns78p603 (BSN.hardyZApproximantRS₀_eq qz87 6 (@BSN.floor_sqrt_eq_dec qz87 295176 1000 6 qz90 rfl rfl rfl)) (@Ns78p605 28287918745940017749 147573952589676412928 258228364968443225547265 Ns78p603 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz87) qz87 6) (@HAdd.hAdd Real Real Real qz351 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz87) qz87 6)) Bool.false 14540565 33554432 52035 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz87) qz87 6) (Ns78p657 (Ns78p656 rfl rfl rfl rfl) rfl rfl)) (Ns78p692 rfl) rfl rfl)) 

theorem RS079to096.d40 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz87) Bool.false 28287918745940017749 147573952589676412928 258228364968443225547265 Ns78p603 := Ns78p693 

noncomputable def Ns78p694 := nat_lit 40691340710802573137805312 

noncomputable def Ns78p695 := nat_lit 197062943151451131344846848 

noncomputable abbrev qz867 := (Enclosure.sfrac Bool.false 296399 1000)

noncomputable abbrev qz677 := qz867

noncomputable abbrev qz440 := qz677

noncomputable abbrev qz100 := qz440

noncomputable abbrev qz868 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 296399 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz678 := qz868

noncomputable abbrev qz441 := qz678

noncomputable abbrev qz101 := qz441

noncomputable abbrev qz869 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 296399 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz679 := qz869

noncomputable abbrev qz442 := qz679

noncomputable abbrev qz102 := qz442

noncomputable abbrev qz680 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz101 qz9))

noncomputable def Ns78p696 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz100) qz100 6) (@HMul.hMul Real Real Real qz5 qz680 (Zeta.RiemannSiegel.correction qz102)) 9633795 4194304 52253 33554432 4613588411299806007 18446744073709551616 1386223471704965910901 Ns78p694 Ns78p695 

noncomputable def Ns78p697 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz100) qz100 Real.sin BSN.quadSignNeg 5 6 296399 1000 69 67108864 33554432 1125899906842624 Bool.false 28356412205 1173 120242927 62 27397080 8 

noncomputable def Ns78p698 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz100) qz100 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 296399 1000 7 34 67108864 33554432 1125899906842624 Bool.false 28356412205 1173 

noncomputable def Ns78p699 := Ns78p698 93032624 61 33554424 8 108007536 61 30011992 8 Bool.true 79395190 26004 Bool.false 43734984 Bool.true 72825317 3537118876014220 1 Bool.false 40704243 Bool.false Bool.false 31323192 Bool.true Bool.true 73051229 

noncomputable def Ns78p700 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz100) qz100 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 296399 1000 138 61 67108864 33554432 1125899906842624 Bool.false 28356412205 1173 

noncomputable def Ns78p701 := Ns78p700 46516304 61 47453136 16 73726608 61 38745320 8 Bool.false 49848 1245 Bool.false 21844940 Bool.false 73643539 3537118876014220 1 Bool.false 63584720 Bool.true Bool.false 59727778 Bool.true Bool.true 79395190 

noncomputable def Ns78p702 := nat_lit 23225645088210643702220798751490488774665321454526980439 

noncomputable def Ns78p703 := nat_lit 54966285799238803988713590690435365782574730313728000 

noncomputable def Ns78p704 := nat_lit 1098064973791126033714199359520000 

noncomputable def Ns78p705 := nat_lit 1952794754318134237845810854510210880 

noncomputable abbrev qz443 := (@Eq.refl Real qz677)

noncomputable abbrev qz103 := qz443

noncomputable def Ns78p706 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz100 296399 1000 351410468804 16000000 592798 4000 2000 Ns78p704 Ns78p705 qz103 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns78p707 := nat_lit 7432206428227405984710655600476956407892902865448633740480 

noncomputable abbrev qz444 := (Real.log (Enclosure.sfrac Bool.false 351410468804 16000000))

noncomputable abbrev qz445 := (Enclosure.sfrac Bool.false 296399 2000)

noncomputable abbrev qz104 := (@HSub.hSub Real Real Real qz339 (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 296399 4000) qz444) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 592798)))))) qz445)

noncomputable abbrev qz446 := (@HSub.hSub Real Real Real qz12 qz104 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 296399 2000) (Real.log Real.pi)))

noncomputable def Ns78p708 := @Enclosure.Real.IsNear.addLit_ft_p qz446 (Enclosure.sfrac Bool.true Ns78p704 Ns78p705) 3805938285261606298671 9007199254740992000 19717289235845197233431 Ns78p320 Ns78p704 Ns78p705 0 1 Ns78p707 

noncomputable def Ns78p709 := nat_lit 255412194778014341519055519744000 

noncomputable abbrev qz447 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 296399 2000) (Real.log Real.pi))

noncomputable def Ns78p710 := @Enclosure.Real.IsNear.subLit_ff_p qz104 qz447 5333995193248020898863 9007199254740992000 19024939788650001463 Ns78p194 11384911149639 67108864000 296399 33554432000 Ns78p709 3805938285261606298671 9007199254740992000 

noncomputable def Ns78p711 := nat_lit 10667990386496041797726000 

noncomputable abbrev qz105 := (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 296399 4000) qz444) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 592798))))))

noncomputable def Ns78p712 := @Enclosure.Real.IsNear.subLit_ff_p qz105 qz445 6668857619201008542767 9007199254740992000 19024939788650001463 Ns78p194 296399 2000 0 1 Ns78p711 5333995193248020898863 9007199254740992000 19024939788650001463 Ns78p194 

noncomputable def Ns78p713 := nat_lit 15016932344410277591856385804485001216 

noncomputable def Ns78p714 := nat_lit 12085778322550012191440896 

noncomputable def Ns78p715 := nat_lit 18978277715025478060501479655139367674261133022617372696106047315913091040796936034086579925483520 

noncomputable def Ns78p716 := nat_lit 135634677866126920338755953599670524109157258500211157764720889209176304792532211266253956317184 

noncomputable def Ns78p717 := nat_lit 423346663834281645021924850049221902764826304257209736793303368650412389018341739600609280 

noncomputable def Ns78p718 := BSN.log_dyadic_bound 89266468804 613554468804 5 4 Ns78p715 33554432 8823528 Ns78p716 Ns78p717 9833495 702820937608 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 89266468804) (BSN.artanhQ 613554468804) 0 4 Ns78p716 Ns78p715 Ns78p717 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns78p719 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 296399 4000) qz444 296399 4000 0 1 22511516367178433 2251799813685248 62500007720587 551470500000000000000 6672390939715320362767 9007199254740992000 303687537514332233 36162000000000000000000 (Enclosure.Real.IsNear.const Bool.false 296399 4000) (BSN.isNear_log_sfrac 351410468804 16000000 22511516367178433 2251799813685248 62500007720587 551470500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 351410468804) qz347)) Bool.false Ns78p714 Ns78p84 1000000123529392 8823528000000000000000 22511516367178433 2251799813685248 62500007720587 551470500000000000000 (BSN.log_rat_reduce_isNear 351410468804 16000000 14 702820937608 524288000000 9833495 33554432 24973259072661432 36028797018963968 8823528 1000000000000000 rfl rfl rfl rfl (Ns78p718 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns78p720 := BSN.arctan_dyadic_bound_f 1000 592798 1 0 4194304 1102941 0 1 1 0 1 1 7075 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 592798) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 592798) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz448 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 592798)))

noncomputable def Ns78p721 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz448 884279719003555 562949953421312 1 2000000000000000 7075 4194304 1 1102941 3704955091615030968320 883330128577955 562949953421312 2000000001102941 2205882000000000000000 qz17 (Ns78p720 rfl) rfl rfl 

noncomputable def Ns78p722 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 296399 4000) qz444) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz448)) 6672390939715320362767 9007199254740992000 303687537514332233 36162000000000000000000 883330128577955 2251799813685248 2000000001102941 8823528000000000000000 Ns78p713 6668857619201008542767 9007199254740992000 19024939788650001463 Ns78p194 (Ns78p719 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz448) 1 4 0 1 883330128577955 562949953421312 2000000001102941 2205882000000000000000 883330128577955 2251799813685248 2000000001102941 8823528000000000000000 qz350 Ns78p721 rfl) 

noncomputable def Ns78p723 := @Ns78p708 Ns78p702 Ns78p703 19717289235845197233431 Ns78p320 (@Ns78p710 19717289235845197233431 Ns78p320 (Ns78p712 (Ns78p722 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 296399 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz445 (Real.log Real.pi) 296399 2000 0 1 38410761 33554432 1 16777216 11384911149639 67108864000 296399 33554432000 (Enclosure.Real.IsNear.const Bool.false 296399 2000) RS079to096.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns78p704 Ns78p705) 

noncomputable def Ns78p724 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz100) Bool.false Ns78p702 Ns78p703 19717289235845197233431 Ns78p320 3544551525 8388608 37 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz100) (@HAdd.hAdd Real Real Real qz351 qz446 (Enclosure.sfrac Bool.true Ns78p704 Ns78p705)) Bool.false Ns78p702 Ns78p703 19717289235845197233431 Ns78p320 Ns78p706 (Ns78p723 rfl rfl)) 

noncomputable def Ns78p725 := nat_lit 1898078202667396791009280 

noncomputable def Ns78p726 := nat_lit 80461950784351967523485062342443207446156390630494176744599120398960934498395890403869461717708092301856824519118464456592097017856 

noncomputable def Ns78p727 := nat_lit 316646866740079143295725755612190180511469568587383446887297628374512813051459112748418952103360324986451946705925428665111910809600 

noncomputable def Ns78p728 := nat_lit 148324063597620542457151851039564209945535677578967638674146418843469724399531091331983653964117764358745724165937242388299776 

noncomputable def Ns78p729 := nat_lit 486962269266667504672608948643191822974818637413684554428217363655427411531229202943239495210892942820002453656856173109812658176000 

noncomputable def Ns78p730 := nat_lit 28814864873347202039911043760709306426543730741451893666744084182080665987682779260106124641405789573767127150239214008525183883673600 

noncomputable def Ns78p731 := BSN.cos_dyadic_bound_f 26973313576 17179869184 4 3 8388608 2208037 Ns78p726 Ns78p727 Ns78p728 Ns78p729 Ns78p730 Ns78p728 6231 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 26973313576) (BSN.cosEvenQ 17179869184) 0 3 Ns78p726 Ns78p727 Ns78p728 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 26973313576) (BSN.cosOddQ 17179869184) 0 3 Ns78p729 Ns78p730 Ns78p728 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p732 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz100) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3544551525) qz354) Bool.false 3544551525 8388608 37 2097152 Bool.false 6231 8388608 1 1102941 (Ns78p724 rfl) (Enclosure.sfrac_false_div 3544551525 8388608) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3544551525) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns78p725) qz355) 226375608064910080 72057594037927936 Bool.false 6231 8388608 67 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q0 3544551525 8388608 226375608064910080 72057594037927936 67 Ns78p725 Ns78p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 6231 8388608 Ns78p725 Ns78p84 26973313576 17179869184 2208037 2205882 (Ns78p731 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p733 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz100) Bool.false Ns78p702 Ns78p703 19717289235845197233431 Ns78p320 28356412205 67108864 1173 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz100) (@HAdd.hAdd Real Real Real qz351 qz446 (Enclosure.sfrac Bool.true Ns78p704 Ns78p705)) Bool.false Ns78p702 Ns78p703 19717289235845197233431 Ns78p320 Ns78p706 (Ns78p723 rfl rfl)) 

noncomputable def Ns78p734 := Ns78p701 26004 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 138 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 63584720 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 61 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 59727778 67108864) qz103 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 1) Bool.false 6231 8388608 42905969 2313034924032 49848 67108864 1245 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz100)) Bool.false 6231 8388608 42905969 2313034924032 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz100) qz100) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz100)) Bool.false 6231 8388608 42905969 2313034924032 6231 8388608 42905969 2313034924032 (Ns78p732 rfl rfl) rfl)) rfl) (Ns78p733 rfl) RS079to096.d7 

noncomputable def Ns78p735 := nat_lit 227721179601245943065932960000 

noncomputable def Ns78p736 := BSN.cos_dyadic_bound_f 21844940 67108864 2 1 67108864 33554432 Ns78p735 Ns78p228 Ns78p735 Ns78p735 Ns78p229 Ns78p735 63584720 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 21844940) qz357 0 1 Ns78p735 Ns78p228 Ns78p735 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 21844940) (BSN.cosOddQ 67108864) 0 1 Ns78p735 Ns78p229 Ns78p735 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p737 := nat_lit 1804879267760562370506590864524078132974793054536782510929723009825 

noncomputable def Ns78p738 := nat_lit 865121700034648341778863996940975066563397345554855283591752481 

noncomputable def Ns78p739 := nat_lit 4725664075668083444487715055853728769588117261417817762928221236001 

noncomputable def Ns78p740 := BSN.sin_dyadic_bound_f 73643539 67108864 3 2 67108864 33554432 Ns78p737 Ns78p127 Ns78p738 Ns78p739 Ns78p130 Ns78p738 59727778 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 73643539) qz356 0 2 Ns78p737 Ns78p127 Ns78p738 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 73643539) (BSN.sinOddQ 67108864) 0 2 Ns78p739 Ns78p130 Ns78p738 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p741 := nat_lit 224410477038554625786614234319612863377543798775350604722203525120 

noncomputable def Ns78p742 := nat_lit 13385413005303905150199936304040901466816096189952267749687296 

noncomputable def Ns78p743 := nat_lit 587720053956110670737556004273541433100716056446372613457985929216 

noncomputable def Ns78p744 := BSN.sin_dyadic_bound_f 43734984 67108864 3 2 67108864 33554432 Ns78p741 Ns78p127 Ns78p742 Ns78p743 Ns78p130 Ns78p742 40704243 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 43734984) qz356 0 2 Ns78p741 Ns78p127 Ns78p742 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 43734984) (BSN.sinOddQ 67108864) 0 2 Ns78p743 Ns78p130 Ns78p742 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p745 := nat_lit 959216662852953680636487722099429758236674532874798218983677905121 

noncomputable def Ns78p746 := nat_lit 791150432601707058053032667787067998692495604818645584376252641 

noncomputable def Ns78p747 := nat_lit 2876067687693657627793357100962715138712638607414757365782281210081 

noncomputable def Ns78p748 := BSN.cos_dyadic_bound_f 72825317 67108864 3 2 67108864 33554432 Ns78p745 Ns78p116 Ns78p746 Ns78p747 Ns78p119 Ns78p746 31323192 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 72825317) qz357 0 2 Ns78p745 Ns78p116 Ns78p746 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 72825317) (BSN.cosOddQ 67108864) 0 2 Ns78p747 Ns78p119 Ns78p746 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p749 := Ns78p699 44261 BSN.abs_quadSignPos (BSN.cos_quad_nat3 7 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 40704243 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 34 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 31323192 67108864) qz103 rfl rfl (Ns78p734 RS079to096.d9 RS079to096.d11 RS079to096.d13 RS079to096.d17 (Ns78p736 rfl rfl) (Ns78p740 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns78p733 rfl) RS079to096.d19 RS079to096.d21 RS079to096.d23 RS079to096.d25 RS079to096.d17 (Ns78p744 rfl rfl) (Ns78p748 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns78p750 := nat_lit 9530411353583906115649605841 

noncomputable def Ns78p751 := BSN.sin_dyadic_bound_f 9880477 67108864 2 1 67108864 33554432 Ns78p750 Ns78p106 Ns78p750 Ns78p750 Ns78p107 Ns78p750 9844819 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 9880477) qz356 0 1 Ns78p750 Ns78p106 Ns78p750 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 9880477) (BSN.sinOddQ 67108864) 0 1 Ns78p750 Ns78p107 Ns78p750 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p752 := Ns78p697 Bool.true 73051229 44261 Bool.true 9880477 3537118876014220 1 Bool.false 9844819 Bool.true Bool.true 77070360 52253 BSN.abs_quadSignNeg qz635 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 9844819 67108864) qz103 rfl (Ns78p749 rfl rfl) (Ns78p733 rfl) RS079to096.d27 RS079to096.d29 RS079to096.d17 (Ns78p751 rfl rfl) rfl 

noncomputable def Ns78p753 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 6) 77070360 67108864 52253 67108864 77070360 67108864 52253 67108864 10344208615342080 9633795 4194304 52253 33554432 (Ns78p752 rfl rfl rfl rfl) 

noncomputable def Ns78p754 := @Enclosure.Real.IsNear.mulLit_ff qz680 (Zeta.RiemannSiegel.correction qz102) 800213 2097152 1 4194304 5765450462939 8796093022208 431092614660313 4850785817003556864 4613588411299806007 18446744073709551616 

noncomputable abbrev qz681 := (@HPow.hPow Real Real Real qz7 qz101 qz9)

noncomputable def Ns78p755 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz681 1 1 0 1 800213 2097152 1 4194304 800213 2097152 1 4194304 

noncomputable def Ns78p756 := @Enclosure.Real.IsNear.sqrt_image qz101 395719044511 8388608000 296399 8388608000 28807678 28807701 4194304 (@Enclosure.Real.IsNear.of_eq qz101 (@HMul.hMul Real Real Real qz5 qz100 qz3) Bool.false 395719044511 8388608000 296399 8388608000 (BSN.t_div_two_pi_mk qz100 296399 1000 qz103) (@Enclosure.Real.IsNear.mulLit_ff qz100 qz3 296399 1000 0 1 1335089 8388608 1 8388608 395719044511 8388608000 296399 8388608000 (Enclosure.Real.IsNear.const Bool.false 296399 1000) RS079to096.d32 rfl)) 

noncomputable abbrev qz870 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 296399 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz682 := qz870

noncomputable abbrev qz449 := qz682

noncomputable abbrev qz106 := qz449

noncomputable def Ns78p757 := @Enclosure.Real.IsNear.sqrt_image qz106 57615379 8388608 23 8388608 10992186 10992191 4194304 (@Enclosure.Real.IsNear.recentre' qz106 Bool.false 57615379 8388608 23 8388608 57615379 8388608 23 8388608 (Ns78p756 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns78p758 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz106) 21984377 8388608 5 8388608 1600425 1600427 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz106) Bool.false 21984377 8388608 5 8388608 21984377 8388608 5 8388608 (Ns78p757 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns78p759 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz106)) Bool.false 3200852 8388608 2 8388608 800213 2097152 1 4194304 (Ns78p758 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz107 := (@HMul.hMul Real Real Real qz336 qz334 qz442)

noncomputable abbrev qz683 := (@HMul.hMul Real Real Real qz841 qz869 qz869)

noncomputable abbrev qz450 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz683 qz679) qz640)

noncomputable abbrev qz108 := (Real.cos (@HMul.hMul Real Real Real qz336 qz334 qz450))

noncomputable def Ns78p760 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz102) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz107)) qz108) Bool.false 5765450462939 

noncomputable def Ns78p761 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz107)) qz108 3099233 2097152 21 

noncomputable def Ns78p762 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz107)) Bool.false 12396932 8388608 336 8388608 3099233 2097152 21 

noncomputable def Ns78p763 := @Enclosure.Real.IsNear.recentre' (Real.cos qz107) Bool.false 5676303 8388608 84708997 4626069848064 5676303 8388608 84708997 4626069848064 

noncomputable def Ns78p764 := @Enclosure.Real.IsNear.cos_image qz107 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 45765031) qz354) Bool.false 45765031 8388608 73 4194304 Bool.false 5676303 8388608 1 

noncomputable def Ns78p765 := nat_lit 620679734470579818344608993 

noncomputable def Ns78p766 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz102 884279719003555 140737488355328 1 500000000000000 7283731 8388608 23 8388608 6440855601977482663705 1180591620717411303424 Ns78p765 

noncomputable def Ns78p767 := @Enclosure.Real.IsNear.subLit_ff_p qz106 qz1 57615379 8388608 23 8388608 6 1 0 1 7283731 7283731 8388608 23 

noncomputable def Ns78p768 := @Ns78p767 8388608 (@Enclosure.Real.IsNear.recentre' qz106 Bool.false 57615379 8388608 23 8388608 57615379 8388608 23 8388608 (Ns78p756 rfl rfl rfl rfl rfl rfl) rfl) qz362 

noncomputable def Ns78p769 := @Enclosure.Real.IsNear.recentre' qz107 Bool.false 6440855601977482663705 1180591620717411303424 Ns78p765 Ns78p385 45765031 8388608 73 4194304 (@Ns78p766 Ns78p385 RS079to096.d31 (Ns78p768 rfl rfl) rfl) 

noncomputable def Ns78p770 := nat_lit 7002809791775868046351446005740693938354589759423339017630360666874439906074992640000 

noncomputable def Ns78p771 := nat_lit 706536539960876922486762456865853259804299981814924842934894792424661017600000000 

noncomputable def Ns78p772 := nat_lit 18339548395491146320664999066295463218984242408042949453571907155007226493310771200000 

noncomputable def Ns78p773 := BSN.sin_dyadic_bound_f 12768557260 17179869184 3 2 8388608 2208037 Ns78p770 Ns78p97 Ns78p771 Ns78p772 Ns78p100 Ns78p771 5676303 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 12768557260) qz352 0 2 Ns78p770 Ns78p97 Ns78p771 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 12768557260) qz353 0 2 Ns78p772 Ns78p100 Ns78p771 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p774 := @Ns78p764 1102941 (Ns78p769 rfl) (Enclosure.sfrac_false_div 45765031 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 45765031) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 898507339407866684506112) qz355) 226375608064910080 72057594037927936 Bool.false 5676303 8388608 0 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q3 45765031 8388608 226375608064910080 72057594037927936 0 898507339407866684506112 Ns78p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 5676303 8388608 898507339407866684506112 Ns78p84 12768557260 17179869184 2208037 2205882 (Ns78p773 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p775 := @Enclosure.Real.IsNear.inv_image (Real.cos qz107) 5676303 8388608 84708997 4626069848064 6198298 6198634 4194304 (Ns78p763 (Ns78p774 rfl rfl) rfl) rfl 

noncomputable def Ns78p776 := @Enclosure.Real.IsNear.recentre' qz108 Bool.false 1860283 4194304 

noncomputable abbrev qz109 := (@HMul.hMul Real Real Real qz336 qz334 qz450)

noncomputable def Ns78p777 := @Enclosure.Real.IsNear.cos_image qz109 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 18207)) (@Nat.cast Real Real.instNatCast 16384)) Bool.true 18207 16384 

noncomputable def Ns78p778 := nat_lit 11005456547949685668149364005 

noncomputable def Ns78p779 := nat_lit 2849676341278510987434909648717497 

noncomputable def Ns78p780 := @Enclosure.Real.IsNear.recentre' qz109 Bool.true Ns78p778 Ns78p397 Ns78p779 

noncomputable abbrev qz110 := qz450

noncomputable def Ns78p781 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz110 884279719003555 140737488355328 1 500000000000000 12445673367191 

noncomputable abbrev qz451 := (@HSub.hSub Real Real Real qz634 qz683 qz679)

noncomputable abbrev qz111 := qz451

noncomputable def Ns78p782 := @Enclosure.Real.IsNear.subLit_tf qz111 qz26 8047626856087 70368744177664 527990139 70368744177664 1 16 

noncomputable abbrev qz452 := qz683

noncomputable abbrev qz112 := qz452

noncomputable def Ns78p783 := @Enclosure.Real.IsNear.subLit_ff_n qz112 qz102 53052737280361 70368744177664 335052155 70368744177664 7283731 8388608 23 8388608 

noncomputable def Ns78p784 := @Enclosure.Real.IsNear.mulLit_ff qz102 qz102 7283731 8388608 23 8388608 7283731 8388608 23 8388608 53052737280361 70368744177664 

noncomputable def Ns78p785 := nat_lit 13314861649279037340277627351687182081 

noncomputable def Ns78p786 := nat_lit 209353409336124249982349611994154270720 

noncomputable def Ns78p787 := nat_lit 12075556038653665479830246502905601 

noncomputable def Ns78p788 := nat_lit 39920433835759804689873221562055735041 

noncomputable def Ns78p789 := nat_lit 9420903420125591249205732539736942182400 

noncomputable def Ns78p790 := BSN.cos_dyadic_bound_f 18207 16384 3 2 4194304 1102941 Ns78p785 Ns78p786 Ns78p787 Ns78p788 Ns78p789 Ns78p787 1860283 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 18207) (BSN.cosEvenQ 16384) 0 2 Ns78p785 Ns78p786 Ns78p787 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 18207) (BSN.cosOddQ 16384) 0 2 Ns78p788 Ns78p789 Ns78p787 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p791 := @Ns78p776 111288311 2313034924032 1860283 4194304 111288311 2313034924032 (@Ns78p777 99 2097152 Bool.false 1860283 4194304 1 1102941 (@Ns78p780 Ns78p400 18207 16384 99 2097152 (@Ns78p781 70368744177664 527990139 70368744177664 Ns78p778 Ns78p397 Ns78p779 Ns78p400 RS079to096.d31 (@Ns78p782 0 1 199130773875056 12445673367191 70368744177664 527990139 70368744177664 (@Ns78p783 67508387025986256896 8047626856087 70368744177664 527990139 70368744177664 (@Ns78p784 335052155 70368744177664 (Ns78p768 rfl rfl) (Ns78p768 rfl rfl) rfl) (Ns78p768 rfl rfl) rfl rfl) qz366 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 18207 16384) (BSN.cos_neg_of_bound 18207 16384 Bool.false 1860283 4194304 1 1102941 (Ns78p790 rfl rfl)) rfl rfl) 

noncomputable def Ns78p792 := @Ns78p754 1386223471704965910901 Ns78p694 (Ns78p755 qz28 (@Enclosure.Real.IsNear.of_eq qz681 (@Inv.inv Real Real.instInv (Real.sqrt qz106)) Bool.false 800213 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz101 (BSN.t_div_two_pi_nonneg qz100 296399 1000 qz103)) Ns78p759) rfl) (@Ns78p760 8796093022208 431092614660313 4850785817003556864 (BSN.correction_mk qz102 (BSN.cos_two_pi_p_ne_zero_mk qz100 296399 1000 6 qz103 rfl rfl (@BSN.floor_sqrt_eq_dec qz100 296399 1000 6 qz103 rfl rfl rfl))) (@Ns78p761 524288 1860283 4194304 111288311 2313034924032 5765450462939 8796093022208 431092614660313 4850785817003556864 (@Ns78p762 524288 (Ns78p775 rfl rfl rfl rfl rfl) rfl) (Ns78p791 rfl) rfl)) 

noncomputable def Ns78p793 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz100) (hardyZApproximantRS₀ qz100) Bool.true 46983466899740965687 18446744073709551616 64753251295676680114549 Ns78p694 (@Eq.refl Real (hardyZApproximantRS₀ qz100)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz100) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz100) qz100 6) (@HMul.hMul Real Real Real qz5 qz680 (Zeta.RiemannSiegel.correction qz102))) Bool.true 46983466899740965687 18446744073709551616 64753251295676680114549 Ns78p694 (BSN.hardyZApproximantRS₀_eq qz100 6 (@BSN.floor_sqrt_eq_dec qz100 296399 1000 6 qz103 rfl rfl rfl)) (@Ns78p696 46983466899740965687 18446744073709551616 64753251295676680114549 Ns78p694 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz100) qz100 6) (@HAdd.hAdd Real Real Real qz351 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz100) qz100 6)) Bool.true 9633795 4194304 52253 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz100) qz100 6) (Ns78p753 (Ns78p752 rfl rfl rfl rfl) rfl rfl)) (Ns78p792 rfl) rfl rfl)) 

theorem RS079to096.d41 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz100) Bool.true 46983466899740965687 18446744073709551616 64753251295676680114549 Ns78p694 := Ns78p793 

noncomputable def Ns78p794 := nat_lit 18085040315912254727913472 

noncomputable def Ns78p795 := nat_lit 8211538686753054920080883712 

noncomputable abbrev qz871 := (Enclosure.sfrac Bool.false 298842 1000)

noncomputable abbrev qz684 := qz871

noncomputable abbrev qz453 := qz684

noncomputable abbrev qz113 := qz453

noncomputable abbrev qz872 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 298842 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz685 := qz872

noncomputable abbrev qz454 := qz685

noncomputable abbrev qz114 := qz454

noncomputable abbrev qz873 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 298842 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz686 := qz873

noncomputable abbrev qz455 := qz686

noncomputable abbrev qz115 := qz455

noncomputable abbrev qz687 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz114 qz9))

noncomputable def Ns78p796 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz113) qz113 6) (@HMul.hMul Real Real Real qz5 qz687 (Zeta.RiemannSiegel.correction qz115)) 60143739 16777216 52683 33554432 39584076464105686755 147573952589676412928 540427036252761068025 Ns78p794 Ns78p795 

noncomputable def Ns78p797 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz113) qz113 Real.cos BSN.quadSignPos 5 6 298842 1000 68 67108864 33554432 1125899906842624 Bool.false 28672660774 1183 120242927 62 27397080 8 

noncomputable def Ns78p798 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz113) qz113 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 298842 1000 8 34 67108864 33554432 1125899906842624 Bool.false 28672660774 1183 

noncomputable def Ns78p799 := Ns78p798 93032624 61 33554424 8 108007536 61 30011992 8 Bool.false 112980640 26217 Bool.false 27290496 Bool.true 20439159 3537118876014220 1 Bool.false 61635936 Bool.false Bool.false 64020301 Bool.true Bool.false 115167855 

noncomputable def Ns78p800 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz113) qz113 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 298842 1000 140 62 67108864 33554432 1125899906842624 Bool.false 28672660774 1183 

noncomputable def Ns78p801 := Ns78p800 46516304 61 47453136 16 73726608 61 38745320 8 Bool.false 67108840 1253 Bool.false 13625464 Bool.false 104363647 3537118876014220 1 Bool.false 65730384 Bool.false Bool.false 1050667 Bool.true Bool.false 112980640 

noncomputable def Ns78p802 := nat_lit 21415161932084217392327043633175409203737850565828929 

noncomputable def Ns78p803 := nat_lit 50122561031932206798456495660349475104453820416000 

noncomputable def Ns78p804 := nat_lit 564705792000000000000000000 

noncomputable def Ns78p805 := nat_lit 1144069712715203048809975311360000 

noncomputable def Ns78p806 := nat_lit 2051379166402465949368472415440670720 

noncomputable abbrev qz456 := (@Eq.refl Real qz684)

noncomputable abbrev qz116 := qz456

noncomputable def Ns78p807 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz113 298842 1000 357227163856 16000000 597684 4000 2000 Ns78p805 Ns78p806 qz116 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns78p808 := nat_lit 3947242647321762949753720682466891424432960616293588193280 

noncomputable abbrev qz457 := (Enclosure.sfrac Bool.false 298842 2000)

noncomputable abbrev qz688 := (Real.log (Enclosure.sfrac Bool.false 357227163856 16000000))

noncomputable abbrev qz117 := (@HSub.hSub Real Real Real qz339 (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 298842 4000) qz688) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 597684)))))) qz457)

noncomputable abbrev qz458 := (@HSub.hSub Real Real Real qz12 qz117 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 298842 2000) (Real.log Real.pi)))

noncomputable def Ns78p809 := @Enclosure.Real.IsNear.addLit_ft_p qz458 (Enclosure.sfrac Bool.true Ns78p805 Ns78p806) 1924192204153092669949 4503599627370496000 9938847198907731702149 Ns78p804 Ns78p805 Ns78p806 0 1 Ns78p808 

noncomputable def Ns78p810 := nat_lit 64565176469185065583502163968000 

noncomputable abbrev qz459 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 298842 2000) (Real.log Real.pi))

noncomputable def Ns78p811 := @Enclosure.Real.IsNear.subLit_ff_p qz117 qz459 2694517985441956856317 4503599627370496000 1198601706719462219 137867625000000000000000 5739374319381 33554432000 149421 16777216000 Ns78p810 1924192204153092669949 4503599627370496000 

noncomputable def Ns78p812 := nat_lit 5389035970883913712634000 

noncomputable abbrev qz118 := (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 298842 4000) qz688) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 597684))))))

noncomputable def Ns78p813 := @Enclosure.Real.IsNear.subLit_ff_p qz118 qz457 3367450345363283739133 4503599627370496000 1198601706719462219 137867625000000000000000 298842 2000 0 1 Ns78p812 2694517985441956856317 4503599627370496000 1198601706719462219 137867625000000000000000 

noncomputable def Ns78p814 := nat_lit 7582824060283366355105129637802409984 

noncomputable def Ns78p815 := nat_lit 12105625145675878682853376 

noncomputable def Ns78p816 := nat_lit 20466315484025401885185436031670122399308944288796108024791897256784797478383326063675728587653120 

noncomputable def Ns78p817 := nat_lit 163089310454726170346041838470289325743373766501056708927450650294091466929714015779689284501504 

noncomputable def Ns78p818 := nat_lit 701484845671050767349906690664233722304258980665070118292074729024893082555569539834183680 

noncomputable def Ns78p819 := BSN.log_dyadic_bound 95083163856 619371163856 5 4 Ns78p816 33554432 8823528 Ns78p817 Ns78p818 10384355 714454327712 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 95083163856) (BSN.artanhQ 619371163856) 0 4 Ns78p817 Ns78p816 Ns78p818 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns78p820 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 298842 4000) qz688 298842 4000 0 1 22548483956001473 2251799813685248 62500007720587 551470500000000000000 3369217021189696097133 4503599627370496000 3112937884539276709 367647000000000000000000 (Enclosure.Real.IsNear.const Bool.false 298842 4000) (BSN.isNear_log_sfrac 357227163856 16000000 22548483956001473 2251799813685248 62500007720587 551470500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 357227163856) qz347)) Bool.false Ns78p815 Ns78p84 1000000123529392 8823528000000000000000 22548483956001473 2251799813685248 62500007720587 551470500000000000000 (BSN.log_rat_reduce_isNear 357227163856 16000000 14 714454327712 524288000000 10384355 33554432 24973259072661432 36028797018963968 8823528 1000000000000000 rfl rfl rfl rfl (Ns78p819 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns78p821 := BSN.arctan_dyadic_bound_f 1000 597684 1 0 4194304 1102941 0 1 1 0 1 1 7017 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 597684) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 597684) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz460 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 597684)))

noncomputable def Ns78p822 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz460 884279719003555 562949953421312 1 2000000000000000 7017 4194304 1 1102941 3704987742712329404416 883337913206179 562949953421312 2000000001102941 2205882000000000000000 qz17 (Ns78p821 rfl) rfl rfl 

noncomputable def Ns78p823 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 298842 4000) qz688) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz460)) 3369217021189696097133 4503599627370496000 3112937884539276709 367647000000000000000000 883337913206179 2251799813685248 2000000001102941 8823528000000000000000 Ns78p814 3367450345363283739133 4503599627370496000 1198601706719462219 137867625000000000000000 (Ns78p820 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz460) 1 4 0 1 883337913206179 562949953421312 2000000001102941 2205882000000000000000 883337913206179 2251799813685248 2000000001102941 8823528000000000000000 qz350 Ns78p822 rfl) 

noncomputable def Ns78p824 := @Ns78p809 Ns78p802 Ns78p803 9938847198907731702149 Ns78p804 (@Ns78p811 9938847198907731702149 Ns78p804 (Ns78p813 (Ns78p823 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 298842 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz457 (Real.log Real.pi) 298842 2000 0 1 38410761 33554432 1 16777216 5739374319381 33554432000 149421 16777216000 (Enclosure.Real.IsNear.const Bool.false 298842 2000) RS079to096.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns78p805 Ns78p806) 

noncomputable def Ns78p825 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz113) Bool.false Ns78p802 Ns78p803 9938847198907731702149 Ns78p804 896020649 2097152 149 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz113) (@HAdd.hAdd Real Real Real qz351 qz458 (Enclosure.sfrac Bool.true Ns78p805 Ns78p806)) Bool.false Ns78p802 Ns78p803 9938847198907731702149 Ns78p804 Ns78p807 (Ns78p824 rfl rfl)) 

noncomputable def Ns78p826 := nat_lit 139752962890749754260601974864561485636985487769337674564499279112710250067445071156065 

noncomputable def Ns78p827 := nat_lit 280321017194250987882603555851032612286877414593620207611170061316778779406454952801 

noncomputable def Ns78p828 := nat_lit 365565811638411045273576195078664123867449904534161381618508598529252060724269497389921 

noncomputable def Ns78p829 := BSN.sin_dyadic_bound_f 26974720757 17179869184 3 2 8388608 2208037 Ns78p826 Ns78p97 Ns78p827 Ns78p828 Ns78p100 Ns78p827 8388605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26974720757) qz352 0 2 Ns78p826 Ns78p97 Ns78p827 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26974720757) qz353 0 2 Ns78p828 Ns78p100 Ns78p827 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p830 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz113) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 896020649) qz398) Bool.false 896020649 2097152 149 8388608 Bool.false 8388605 8388608 1 1102941 (Ns78p825 rfl) (Enclosure.sfrac_false_div 896020649 2097152) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 896020649) qz398) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474544306054475250925568) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 8388605 8388608 67 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q3 896020649 2097152 226375608064910080 72057594037927936 67 474544306054475250925568 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388605 8388608 474544306054475250925568 302231454903657293676544 26974720757 17179869184 2208037 2205882 (Ns78p829 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p831 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz113) Bool.false Ns78p802 Ns78p803 9938847198907731702149 Ns78p804 28672660774 67108864 1183 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz113) (@HAdd.hAdd Real Real Real qz351 qz458 (Enclosure.sfrac Bool.true Ns78p805 Ns78p806)) Bool.false Ns78p802 Ns78p803 9938847198907731702149 Ns78p804 Ns78p807 (Ns78p824 rfl rfl)) 

noncomputable def Ns78p832 := Ns78p801 26217 BSN.abs_quadSignPos (BSN.cos_quad_nat0 140 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 65730384 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 62 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 1050667 67108864) qz116 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 1) Bool.false 8388605 8388608 172726817 9252139696128 67108840 67108864 1253 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz113)) Bool.false 8388605 8388608 172726817 9252139696128 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz113) qz113) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz113)) Bool.false 8388605 8388608 172726817 9252139696128 8388605 8388608 172726817 9252139696128 (Ns78p830 rfl rfl) rfl)) rfl) (Ns78p831 rfl) RS079to096.d7 

noncomputable def Ns78p833 := nat_lit 34467136370327173451600367616 

noncomputable def Ns78p834 := BSN.cos_dyadic_bound_f 13625464 67108864 2 1 67108864 33554432 Ns78p833 Ns78p228 Ns78p833 Ns78p833 Ns78p229 Ns78p833 65730384 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 13625464) qz357 0 1 Ns78p833 Ns78p228 Ns78p833 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 13625464) (BSN.cosOddQ 67108864) 0 1 Ns78p833 Ns78p229 Ns78p833 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p835 := nat_lit 977399083358241255920236494692758495708115022402042975471547323259956560282388770627312657236481733121 

noncomputable def Ns78p836 := nat_lit 1669517462579640779769748566850021562057103611989241573076722708774830362470859418507501853667841 

noncomputable def Ns78p837 := nat_lit 5915831200284395694474972376176569553620009842065352429522519479614016553187625976305292224235353076225 

noncomputable def Ns78p838 := BSN.cos_dyadic_bound_f 104363647 67108864 4 3 67108864 33554432 Ns78p835 Ns78p110 Ns78p836 Ns78p837 Ns78p113 Ns78p836 1050667 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 104363647) qz357 0 3 Ns78p835 Ns78p110 Ns78p836 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 104363647) (BSN.cosOddQ 67108864) 0 3 Ns78p837 Ns78p113 Ns78p836 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p839 := nat_lit 18900862220708866219098824008091462518522815341951609915169570816 

noncomputable def Ns78p840 := nat_lit 307674449164314376536075802411663700135732814440539971649536 

noncomputable def Ns78p841 := nat_lit 56701971313228270028543399872669564228168174560225948665565413376 

noncomputable def Ns78p842 := BSN.cos_dyadic_bound_f 27290496 67108864 3 2 67108864 33554432 Ns78p839 Ns78p116 Ns78p840 Ns78p841 Ns78p119 Ns78p840 61635936 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 27290496) qz357 0 2 Ns78p839 Ns78p116 Ns78p840 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 27290496) (BSN.cosOddQ 67108864) 0 2 Ns78p841 Ns78p119 Ns78p840 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p843 := nat_lit 174522766419113242955121452961 

noncomputable def Ns78p844 := BSN.cos_dyadic_bound_f 20439159 67108864 2 1 67108864 33554432 Ns78p843 Ns78p228 Ns78p843 Ns78p843 Ns78p229 Ns78p843 64020301 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 20439159) qz357 0 1 Ns78p843 Ns78p228 Ns78p843 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 20439159) (BSN.cosOddQ 67108864) 0 1 Ns78p843 Ns78p229 Ns78p843 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p845 := Ns78p799 44625 BSN.abs_quadSignPos (BSN.cos_quad_nat0 8 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 61635936 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 34 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 64020301 67108864) qz116 rfl rfl (Ns78p832 RS079to096.d9 RS079to096.d11 RS079to096.d13 RS079to096.d17 (Ns78p834 rfl rfl) (Ns78p838 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns78p831 rfl) RS079to096.d19 RS079to096.d21 RS079to096.d23 RS079to096.d25 RS079to096.d17 (Ns78p842 rfl rfl) (Ns78p844 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns78p846 := nat_lit 610233839817297766954127936162081693207045036667266222764509454145943926829848057236319965344144818176 

noncomputable def Ns78p847 := nat_lit 407906746855504501740306467052948548591975361847628054381134932089065622563806138096160966967296 

noncomputable def Ns78p848 := nat_lit 3696723178796318380605604015121200248916796422150367205581568852304453667144576806704766936939453480960 

noncomputable def Ns78p849 := BSN.cos_dyadic_bound_f 92799736 67108864 4 3 67108864 33554432 Ns78p846 Ns78p110 Ns78p847 Ns78p848 Ns78p113 Ns78p847 12540465 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 92799736) qz357 0 3 Ns78p846 Ns78p110 Ns78p847 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 92799736) (BSN.cosOddQ 67108864) 0 3 Ns78p848 Ns78p113 Ns78p847 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz689 := (BSN.cos_quad_nat0 68 rfl)

noncomputable def Ns78p850 := Ns78p797 Bool.false 115167855 44625 Bool.true 92799736 3537118876014220 1 Bool.false 12540465 Bool.false Bool.false 120287478 52683 BSN.abs_quadSignPos qz689 (BSN.sfrac_eq_quadSignPos_mul Bool.false 12540465 67108864) qz116 rfl (Ns78p845 rfl rfl) (Ns78p831 rfl) RS079to096.d27 RS079to096.d29 RS079to096.d17 (Ns78p849 rfl rfl) rfl 

noncomputable def Ns78p851 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 6) 120287478 67108864 52683 67108864 120287478 67108864 52683 67108864 16144712004009984 60143739 16777216 52683 33554432 (Ns78p850 rfl rfl rfl rfl) 

noncomputable def Ns78p852 := @Enclosure.Real.IsNear.mulLit_ff qz687 (Zeta.RiemannSiegel.correction qz115) 1597145 4194304 1 4194304 24784272225819 35184372088832 336468768963989 4311809615114272768 39584076464105686755 147573952589676412928 

noncomputable abbrev qz690 := (@HPow.hPow Real Real Real qz7 qz114 qz9)

noncomputable def Ns78p853 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz690 1 1 0 1 1597145 4194304 1 4194304 1597145 4194304 1 4194304 

noncomputable def Ns78p854 := @Enclosure.Real.IsNear.sqrt_image qz114 199490333469 4194304000 149421 4194304000 28926155 28926178 4194304 (@Enclosure.Real.IsNear.of_eq qz114 (@HMul.hMul Real Real Real qz5 qz113 qz3) Bool.false 199490333469 4194304000 149421 4194304000 (BSN.t_div_two_pi_mk qz113 298842 1000 qz116) (@Enclosure.Real.IsNear.mulLit_ff qz113 qz3 298842 1000 0 1 1335089 8388608 1 8388608 199490333469 4194304000 149421 4194304000 (Enclosure.Real.IsNear.const Bool.false 298842 1000) RS079to096.d32 rfl)) 

noncomputable abbrev qz874 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 298842 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz691 := qz874

noncomputable abbrev qz461 := qz691

noncomputable abbrev qz119 := qz461

noncomputable def Ns78p855 := @Enclosure.Real.IsNear.sqrt_image qz119 57852333 8388608 23 8388608 11014766 11014772 4194304 (@Enclosure.Real.IsNear.recentre' qz119 Bool.false 57852333 8388608 23 8388608 57852333 8388608 23 8388608 (Ns78p854 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns78p856 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz119) 11014769 4194304 3 4194304 1597144 1597146 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz119) Bool.false 22029538 8388608 6 8388608 11014769 4194304 3 4194304 (Ns78p855 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns78p857 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz119)) Bool.false 3194290 8388608 2 8388608 1597145 4194304 1 4194304 (Ns78p856 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz120 := (@HMul.hMul Real Real Real qz336 qz334 qz455)

noncomputable abbrev qz692 := (@HMul.hMul Real Real Real qz841 qz873 qz873)

noncomputable abbrev qz462 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz692 qz686) qz640)

noncomputable abbrev qz121 := (Real.cos (@HMul.hMul Real Real Real qz336 qz334 qz462))

noncomputable def Ns78p858 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz115) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz120)) qz121) Bool.false 24784272225819 

noncomputable def Ns78p859 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz120)) qz121 10538037 8388608 243 

noncomputable def Ns78p860 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz120)) Bool.false 10538037 8388608 243 8388608 10538037 8388608 243 

noncomputable def Ns78p861 := @Enclosure.Real.IsNear.recentre' (Real.cos qz120) Bool.false 6677595 8388608 84708997 4626069848064 6677595 8388608 84708997 4626069848064 

noncomputable def Ns78p862 := @Enclosure.Real.IsNear.cos_image qz120 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 47253857) qz354) Bool.false 47253857 8388608 73 4194304 Bool.false 6677595 8388608 1 

noncomputable def Ns78p863 := nat_lit 620679734472615237705921761 

noncomputable def Ns78p864 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz115 884279719003555 140737488355328 1 500000000000000 7520685 8388608 23 8388608 6650389218514251035175 1180591620717411303424 Ns78p863 

noncomputable def Ns78p865 := @Enclosure.Real.IsNear.subLit_ff_p qz119 qz1 57852333 8388608 23 8388608 6 1 0 1 7520685 7520685 8388608 23 

noncomputable def Ns78p866 := @Ns78p865 8388608 (@Enclosure.Real.IsNear.recentre' qz119 Bool.false 57852333 8388608 23 8388608 57852333 8388608 23 8388608 (Ns78p854 rfl rfl rfl rfl rfl rfl) rfl) qz362 

noncomputable def Ns78p867 := @Enclosure.Real.IsNear.recentre' qz120 Bool.false 6650389218514251035175 1180591620717411303424 Ns78p863 Ns78p385 47253857 8388608 73 4194304 (@Ns78p864 Ns78p385 RS079to096.d31 (Ns78p866 rfl rfl) rfl) 

noncomputable def Ns78p868 := nat_lit 16494332705157987764415960041465370343426772786275450450105982202138593339989110620160 

noncomputable def Ns78p869 := nat_lit 3918688338880709931888172748901143706261333864568525946684981082957002543810543616 

noncomputable def Ns78p870 := nat_lit 43193098256198446805009219257482510952498077042559735470173415798133433124424358363136 

noncomputable def Ns78p871 := BSN.sin_dyadic_bound_f 15817672908 17179869184 3 2 8388608 2208037 Ns78p868 Ns78p97 Ns78p869 Ns78p870 Ns78p100 Ns78p869 6677595 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 15817672908) qz352 0 2 Ns78p868 Ns78p97 Ns78p869 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 15817672908) qz353 0 2 Ns78p870 Ns78p100 Ns78p869 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p872 := @Ns78p862 1102941 (Ns78p867 rfl) (Enclosure.sfrac_false_div 47253857 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 47253857) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1113069778410090878992384) qz355) 226375608064910080 72057594037927936 Bool.false 6677595 8388608 0 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q3 47253857 8388608 226375608064910080 72057594037927936 0 1113069778410090878992384 Ns78p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 6677595 8388608 1113069778410090878992384 Ns78p84 15817672908 17179869184 2208037 2205882 (Ns78p871 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p873 := @Enclosure.Real.IsNear.inv_image (Real.cos qz120) 6677595 8388608 84708997 4626069848064 5268897 5269140 4194304 (Ns78p861 (Ns78p872 rfl rfl) rfl) rfl 

noncomputable def Ns78p874 := @Enclosure.Real.IsNear.recentre' qz121 Bool.false 2351887 4194304 

noncomputable abbrev qz122 := (@HMul.hMul Real Real Real qz336 qz334 qz462)

noncomputable def Ns78p875 := @Enclosure.Real.IsNear.cos_image qz122 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 4091647)) qz378) Bool.true 4091647 4194304 

noncomputable def Ns78p876 := nat_lit 9661129094704154856325166245 

noncomputable def Ns78p877 := nat_lit 14542526797953328723704951836850769 

noncomputable def Ns78p878 := @Enclosure.Real.IsNear.recentre' qz122 Bool.true Ns78p876 Ns78p397 Ns78p877 

noncomputable abbrev qz123 := qz462

noncomputable def Ns78p879 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz123 884279719003555 140737488355328 1 500000000000000 10925421998359 

noncomputable abbrev qz463 := (@HSub.hSub Real Real Real qz634 qz692 qz686)

noncomputable abbrev qz124 := qz463

noncomputable def Ns78p880 := @Enclosure.Real.IsNear.subLit_tf qz124 qz26 6527375487255 70368744177664 538890023 70368744177664 1 16 

noncomputable abbrev qz464 := qz692

noncomputable abbrev qz125 := qz464

noncomputable def Ns78p881 := @Enclosure.Real.IsNear.subLit_ff_n qz125 qz115 56560702869225 70368744177664 345952039 70368744177664 7520685 8388608 23 8388608 

noncomputable def Ns78p882 := @Enclosure.Real.IsNear.mulLit_ff qz115 qz115 7520685 8388608 23 8388608 7520685 8388608 23 8388608 56560702869225 70368744177664 

noncomputable def Ns78p883 := nat_lit 145806063830303681411294555347190586989056815465587312641 

noncomputable def Ns78p884 := nat_lit 78557068575766881706437629730002692290509495448668161 

noncomputable def Ns78p885 := nat_lit 437261077353759510470470790782111755582589427405864601601 

noncomputable def Ns78p886 := BSN.cos_dyadic_bound_f 4091647 4194304 3 2 4194304 1102941 Ns78p883 Ns78p271 Ns78p884 Ns78p885 Ns78p274 Ns78p884 2351887 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 4091647) (BSN.cosEvenQ 4194304) 0 2 Ns78p883 Ns78p271 Ns78p884 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 4091647) (BSN.cosOddQ 4194304) 0 2 Ns78p885 Ns78p274 Ns78p884 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p887 := @Ns78p874 455079713 9252139696128 2351887 4194304 455079713 9252139696128 (@Ns78p875 405 8388608 Bool.false 2351887 4194304 1 1102941 (@Ns78p878 Ns78p495 4091647 4194304 405 8388608 (@Ns78p879 70368744177664 538890023 70368744177664 Ns78p876 Ns78p397 Ns78p877 Ns78p495 RS079to096.d31 (@Ns78p880 0 1 174806751973744 10925421998359 70368744177664 538890023 70368744177664 (@Ns78p881 54755594231391191040 6527375487255 70368744177664 538890023 70368744177664 (@Ns78p882 345952039 70368744177664 (Ns78p866 rfl rfl) (Ns78p866 rfl rfl) rfl) (Ns78p866 rfl rfl) rfl rfl) qz366 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 4091647 4194304) (BSN.cos_neg_of_bound 4091647 4194304 Bool.false 2351887 4194304 1 1102941 (Ns78p886 rfl rfl)) rfl rfl) 

noncomputable def Ns78p888 := @Ns78p852 540427036252761068025 Ns78p794 (Ns78p853 qz28 (@Enclosure.Real.IsNear.of_eq qz690 (@Inv.inv Real Real.instInv (Real.sqrt qz119)) Bool.false 1597145 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz114 (BSN.t_div_two_pi_nonneg qz113 298842 1000 qz116)) Ns78p857) rfl) (@Ns78p858 35184372088832 336468768963989 4311809615114272768 (BSN.correction_mk qz115 (BSN.cos_two_pi_p_ne_zero_mk qz113 298842 1000 6 qz116 rfl rfl (@BSN.floor_sqrt_eq_dec qz113 298842 1000 6 qz116 rfl rfl rfl))) (@Ns78p859 8388608 2351887 4194304 455079713 9252139696128 24784272225819 35184372088832 336468768963989 4311809615114272768 (@Ns78p860 8388608 (Ns78p873 rfl rfl rfl rfl rfl) rfl) (Ns78p887 rfl) rfl)) 

noncomputable def Ns78p889 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz113) (hardyZApproximantRS₀ qz113) Bool.false 489445846483293468957 147573952589676412928 28935310280385915097593 Ns78p794 (@Eq.refl Real (hardyZApproximantRS₀ qz113)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz113) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz113) qz113 6) (@HMul.hMul Real Real Real qz5 qz687 (Zeta.RiemannSiegel.correction qz115))) Bool.false 489445846483293468957 147573952589676412928 28935310280385915097593 Ns78p794 (BSN.hardyZApproximantRS₀_eq qz113 6 (@BSN.floor_sqrt_eq_dec qz113 298842 1000 6 qz116 rfl rfl rfl)) (@Ns78p796 489445846483293468957 147573952589676412928 28935310280385915097593 Ns78p794 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz113) qz113 6) (@HAdd.hAdd Real Real Real qz351 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz113) qz113 6)) Bool.false 60143739 16777216 52683 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz113) qz113 6) (Ns78p851 (Ns78p850 rfl rfl rfl rfl) rfl rfl)) (Ns78p888 rfl) rfl rfl)) 

theorem RS079to096.d42 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz113) Bool.false 489445846483293468957 147573952589676412928 28935310280385915097593 Ns78p794 := Ns78p889 

noncomputable def Ns78p890 := nat_lit 705474935843695900630188032 

noncomputable abbrev qz875 := (Enclosure.sfrac Bool.false 300468 1000)

noncomputable abbrev qz693 := qz875

noncomputable abbrev qz465 := qz693

noncomputable abbrev qz126 := qz465

noncomputable abbrev qz876 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 300468 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz694 := qz876

noncomputable abbrev qz466 := qz694

noncomputable abbrev qz127 := qz466

noncomputable abbrev qz877 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 300468 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz695 := qz877

noncomputable abbrev qz467 := qz695

noncomputable abbrev qz128 := qz467

noncomputable abbrev qz696 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz127 qz9))

noncomputable def Ns78p891 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz126) qz126 6) (@HMul.hMul Real Real Real qz5 qz696 (Zeta.RiemannSiegel.correction qz128)) 33525737 16777216 52967 33554432 5187645287644914315 18446744073709551616 1145722615488800515763 Ns78p694 Ns78p890 

noncomputable def Ns78p892 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz126) qz126 Real.cos BSN.quadSignPos 5 6 300468 1000 68 67108864 33554432 1125899906842624 Bool.false 28883519839 1188 120242927 62 27397080 8 

noncomputable def Ns78p893 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz126) qz126 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 300468 1000 8 33 67108864 33554432 1125899906842624 Bool.false 28883519839 1188 

noncomputable def Ns78p894 := Ns78p893 93032624 61 33554424 8 108007536 61 30011992 8 Bool.true 58003613 26359 Bool.false 86878514 Bool.true 90614704 3537118876014220 1 Bool.false 18301058 Bool.false Bool.false 65483568 Bool.true Bool.true 78138224 

noncomputable def Ns78p895 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz126) qz126 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 300468 1000 141 63 67108864 33554432 1125899906842624 Bool.false 28883519839 1188 

noncomputable def Ns78p896 := Ns78p895 46516304 61 47453136 16 73726608 61 38745320 8 Bool.true 67108856 1261 Bool.false 43434662 Bool.false 89928891 3537118876014220 1 Bool.false 40465065 Bool.true Bool.false 65330130 Bool.false Bool.true 58003613 

noncomputable def Ns78p897 := nat_lit 4352843310069933014120923975797510667157827101721 

noncomputable def Ns78p898 := nat_lit 10113530876153357480223743557877560070950092800 

noncomputable def Ns78p899 := nat_lit 1175534596294334192757833072640000 

noncomputable def Ns78p900 := nat_lit 2119265913157263242686486151555973120 

noncomputable abbrev qz697 := (@Eq.refl Real qz875)

noncomputable abbrev qz468 := qz697

noncomputable abbrev qz129 := qz468

noncomputable def Ns78p901 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz126 300468 1000 361125076096 16000000 600936 4000 2000 Ns78p899 Ns78p900 qz129 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns78p902 := nat_lit 410785832402990107219337578096126549079311713991277936640 

noncomputable abbrev qz469 := (Enclosure.sfrac Bool.false 300468 2000)

noncomputable abbrev qz698 := (Real.log (Enclosure.sfrac Bool.false 361125076096 16000000))

noncomputable abbrev qz130 := (@HSub.hSub Real Real Real qz339 (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 300468 4000) qz698) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 600936)))))) qz469)

noncomputable abbrev qz470 := (@HSub.hSub Real Real Real qz12 qz130 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 300468 2000) (Real.log Real.pi)))

noncomputable def Ns78p903 := @Enclosure.Real.IsNear.addLit_ft_p qz470 (Enclosure.sfrac Bool.true Ns78p899 Ns78p900) 193834270284997541297 450359962737049600 4996114020387518408773 Ns78p72 Ns78p899 Ns78p900 0 1 Ns78p902 

noncomputable def Ns78p904 := nat_lit 16259997103868926549043445760000 

noncomputable abbrev qz471 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 300468 2000) (Real.log Real.pi))

noncomputable def Ns78p905 := @Enclosure.Real.IsNear.subLit_ff_p qz130 qz471 1356429914231257314421 2251799813685248000 9639626160032534983 1102941000000000000000000 2885301134037 16777216000 75117 8388608000 Ns78p904 193834270284997541297 450359962737049600 

noncomputable def Ns78p906 := nat_lit 2712859828462514628842000 

noncomputable abbrev qz131 := (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 300468 4000) qz698) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 600936))))))

noncomputable def Ns78p907 := @Enclosure.Real.IsNear.subLit_ff_p qz131 qz469 1694726807440446862453 2251799813685248000 9639626160032534983 1102941000000000000000000 300468 2000 0 1 Ns78p906 1356429914231257314421 2251799813685248000 9639626160032534983 1102941000000000000000000 

noncomputable def Ns78p908 := nat_lit 3816185509241793408853053452891193344 

noncomputable def Ns78p909 := nat_lit 12118744996081537392836608 

noncomputable def Ns78p910 := nat_lit 21519711536253921461092024139899119561288640379241519622283352948901213386532484786612814238187520 

noncomputable def Ns78p911 := nat_lit 183700318340877491496722465178371341391659217565300233010613967011259031774550524710293270953984 

noncomputable def Ns78p912 := nat_lit 967401301539177994859981843744717764195021778092951811926763911032944209974258239306465280 

noncomputable def Ns78p913 := BSN.log_dyadic_bound 98981076096 623269076096 5 4 Ns78p910 33554432 8823528 Ns78p911 Ns78p912 10748504 722250152192 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 98981076096) (BSN.artanhQ 623269076096) 0 4 Ns78p911 Ns78p910 Ns78p912 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns78p914 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 300468 4000) qz698 300468 4000 0 1 22572921581718209 2251799813685248 62500007720587 551470500000000000000 1695610150453926705453 2251799813685248000 31937503945219957 3751500000000000000000 (Enclosure.Real.IsNear.const Bool.false 300468 4000) (BSN.isNear_log_sfrac 361125076096 16000000 22572921581718209 2251799813685248 62500007720587 551470500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 361125076096) qz347)) Bool.false Ns78p909 Ns78p84 1000000123529392 8823528000000000000000 22572921581718209 2251799813685248 62500007720587 551470500000000000000 (BSN.log_rat_reduce_isNear 361125076096 16000000 14 722250152192 524288000000 10748504 33554432 24973259072661432 36028797018963968 8823528 1000000000000000 rfl rfl rfl rfl (Ns78p913 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns78p915 := BSN.arctan_dyadic_bound_f 1000 600936 1 0 4194304 1102941 0 1 1 0 1 1 6979 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 600936) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 600936) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz472 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 600936)))

noncomputable def Ns78p916 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz472 884279719003555 562949953421312 1 2000000000000000 6979 4194304 1 1102941 3705009134810559414272 883343013479843 562949953421312 2000000001102941 2205882000000000000000 qz17 (Ns78p915 rfl) rfl rfl 

noncomputable def Ns78p917 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 300468 4000) qz698) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz472)) 1695610150453926705453 2251799813685248000 31937503945219957 3751500000000000000000 883343013479843 2251799813685248 2000000001102941 8823528000000000000000 Ns78p908 1694726807440446862453 2251799813685248000 9639626160032534983 1102941000000000000000000 (Ns78p914 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz472) 1 4 0 1 883343013479843 562949953421312 2000000001102941 2205882000000000000000 883343013479843 2251799813685248 2000000001102941 8823528000000000000000 qz350 Ns78p916 rfl) 

noncomputable def Ns78p918 := @Ns78p903 Ns78p897 Ns78p898 4996114020387518408773 Ns78p72 (@Ns78p905 4996114020387518408773 Ns78p72 (Ns78p907 (Ns78p917 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 300468 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz469 (Real.log Real.pi) 300468 2000 0 1 38410761 33554432 1 16777216 2885301134037 16777216000 75117 8388608000 (Enclosure.Real.IsNear.const Bool.false 300468 2000) RS079to096.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns78p899 Ns78p900) 

noncomputable def Ns78p919 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz126) Bool.false Ns78p897 Ns78p898 4996114020387518408773 Ns78p72 3610439979 8388608 75 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz126) (@HAdd.hAdd Real Real Real qz351 qz470 (Enclosure.sfrac Bool.true Ns78p899 Ns78p900)) Bool.false Ns78p897 Ns78p898 4996114020387518408773 Ns78p72 Ns78p901 (Ns78p918 rfl rfl)) 

noncomputable def Ns78p920 := nat_lit 1898723958813928842067968 

noncomputable def Ns78p921 := nat_lit 139914368879591367247412463788678384596982437682816900820589180827633247077228277285120 

noncomputable def Ns78p922 := nat_lit 280967598646249695663562625532304769951933973727682449189563448442242650250253844736 

noncomputable def Ns78p923 := nat_lit 365987494763026319474053541862343466221698491307056587707617132774894873292335553331456 

noncomputable def Ns78p924 := BSN.sin_dyadic_bound_f 26982490322 17179869184 3 2 8388608 2208037 Ns78p921 Ns78p97 Ns78p922 Ns78p923 Ns78p100 Ns78p922 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26982490322) qz352 0 2 Ns78p921 Ns78p97 Ns78p922 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26982490322) qz353 0 2 Ns78p923 Ns78p100 Ns78p922 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p925 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz126) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3610439979) qz354) Bool.false 3610439979 8388608 75 4194304 Bool.true 8388607 8388608 1 1102941 (Ns78p919 rfl) (Enclosure.sfrac_false_div 3610439979 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3610439979) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns78p920) qz355) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 68 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q1 3610439979 8388608 226375608064910080 72057594037927936 68 Ns78p920 Ns78p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns78p920 Ns78p84 26982490322 17179869184 2208037 2205882 (Ns78p924 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p926 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz126) Bool.false Ns78p897 Ns78p898 4996114020387518408773 Ns78p72 28883519839 67108864 1188 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz126) (@HAdd.hAdd Real Real Real qz351 qz470 (Enclosure.sfrac Bool.true Ns78p899 Ns78p900)) Bool.false Ns78p897 Ns78p898 4996114020387518408773 Ns78p72 Ns78p901 (Ns78p918 rfl rfl)) 

noncomputable def Ns78p927 := Ns78p896 26359 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 141 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 40465065 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 63 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 65330130 67108864) qz129 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz126) qz126 1) Bool.true 8388607 8388608 86914879 4626069848064 67108856 67108864 1261 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz126) qz126 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz126)) Bool.true 8388607 8388608 86914879 4626069848064 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz126) qz126) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz126)) Bool.true 8388607 8388608 86914879 4626069848064 8388607 8388608 86914879 4626069848064 (Ns78p925 rfl rfl) rfl)) rfl) (Ns78p926 rfl) RS079to096.d7 

noncomputable def Ns78p928 := nat_lit 218309342609580360149387681980296509268251053536989670070024741120 

noncomputable def Ns78p929 := nat_lit 12667519168649027703975742327750166268551330579508553553879296 

noncomputable def Ns78p930 := nat_lit 571742054660723130536875587317960214480984628537844217287168041216 

noncomputable def Ns78p931 := BSN.sin_dyadic_bound_f 43434662 67108864 3 2 67108864 33554432 Ns78p928 Ns78p127 Ns78p929 Ns78p930 Ns78p130 Ns78p929 40465065 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 43434662) qz356 0 2 Ns78p928 Ns78p127 Ns78p929 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 43434662) (BSN.sinOddQ 67108864) 0 2 Ns78p930 Ns78p130 Ns78p929 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p932 := nat_lit 4015698936565019611958675324431694068199326084362043643544747083745 

noncomputable def Ns78p933 := nat_lit 4277538252138831707003082459169355487351868138810980216592893921 

noncomputable def Ns78p934 := nat_lit 10510381200500159922842335144768162650685379577294896527028425295841 

noncomputable def Ns78p935 := BSN.sin_dyadic_bound_f 89928891 67108864 3 2 67108864 33554432 Ns78p932 Ns78p127 Ns78p933 Ns78p934 Ns78p130 Ns78p933 65330130 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 89928891) qz356 0 2 Ns78p932 Ns78p127 Ns78p933 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 89928891) (BSN.sinOddQ 67108864) 0 2 Ns78p934 Ns78p130 Ns78p933 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p936 := nat_lit 468532839289671916659026631299092335582609875625706471961611465873745651572692140209419683388557234176 

noncomputable def Ns78p937 := nat_lit 184904979902095272433309304433840931778932704876305057229104100762968536466923524906913854263296 

noncomputable def Ns78p938 := nat_lit 2839268659785927184579138667572913179975029410024247792286128742880029756061729898323080677895521832960 

noncomputable def Ns78p939 := BSN.cos_dyadic_bound_f 86878514 67108864 4 3 67108864 33554432 Ns78p936 Ns78p110 Ns78p937 Ns78p938 Ns78p113 Ns78p937 18301058 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 86878514) qz357 0 3 Ns78p936 Ns78p110 Ns78p937 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 86878514) (BSN.cosOddQ 67108864) 0 3 Ns78p938 Ns78p113 Ns78p937 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p940 := nat_lit 1440821226393087200800272156284478903446449374569575169529352310003295563122683392573969469095821705216 

noncomputable def Ns78p941 := nat_lit 51956389457850993117201226487380036501230565613159928972022824181150019275806034930923536691271355596800 

noncomputable def Ns78p942 := nat_lit 306467279801234574193965614246042166342525225138120773596891568087502075645987226017014078242816 

noncomputable def Ns78p943 := nat_lit 7199214865399611378655418856428124827634383786942059652053713633106047312475574416069290590772737867776 

noncomputable def Ns78p944 := nat_lit 1818473631024784759102042927058301277543069796460597514020798846340250674653211222582323784194497445888000 

noncomputable def Ns78p945 := BSN.sin_dyadic_bound_f 90614704 67108864 4 3 67108864 33554432 Ns78p940 Ns78p941 Ns78p942 Ns78p943 Ns78p944 Ns78p942 65483568 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 90614704) qz356 0 3 Ns78p940 Ns78p941 Ns78p942 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 90614704) (BSN.sinOddQ 67108864) 0 3 Ns78p943 Ns78p944 Ns78p942 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p946 := Ns78p894 44866 BSN.abs_quadSignPos (BSN.cos_quad_nat0 8 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 18301058 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 33 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 65483568 67108864) qz129 rfl rfl (Ns78p927 RS079to096.d9 RS079to096.d11 RS079to096.d13 RS079to096.d17 (Ns78p931 rfl rfl) (Ns78p935 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns78p926 rfl) RS079to096.d19 RS079to096.d21 RS079to096.d23 RS079to096.d25 RS079to096.d17 (Ns78p939 rfl rfl) (Ns78p945 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns78p947 := nat_lit 295825936880647240579337869779955367520679357028808370257328563012092438896904541219610843537984000000 

noncomputable def Ns78p948 := nat_lit 46627118763660900330513048942224008309045493477095938458309394205813834983742162561000000000000 

noncomputable def Ns78p949 := nat_lit 1793414645569194468286818551071915075732182995739534179779050787605970136776570021702773361834969600000 

noncomputable def Ns78p950 := BSN.cos_dyadic_bound_f 77455670 67108864 4 3 67108864 33554432 Ns78p947 Ns78p110 Ns78p948 Ns78p949 Ns78p113 Ns78p948 27156880 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 77455670) qz357 0 3 Ns78p947 Ns78p110 Ns78p948 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 77455670) (BSN.cosOddQ 67108864) 0 3 Ns78p949 Ns78p113 Ns78p948 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p951 := Ns78p892 Bool.true 78138224 44866 Bool.true 77455670 3537118876014220 1 Bool.false 27156880 Bool.false Bool.true 67051474 52967 BSN.abs_quadSignPos qz689 (BSN.sfrac_eq_quadSignPos_mul Bool.false 27156880 67108864) qz129 rfl (Ns78p946 rfl rfl) (Ns78p926 rfl) RS079to096.d27 RS079to096.d29 RS079to096.d17 (Ns78p950 rfl rfl) rfl 

noncomputable def Ns78p952 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz126) qz126 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz126) qz126 6) 67051474 67108864 52967 67108864 67051474 67108864 52967 67108864 8999496499331072 33525737 16777216 52967 33554432 (Ns78p951 rfl rfl rfl rfl) 

noncomputable def Ns78p953 := @Enclosure.Real.IsNear.mulLit_ff qz696 (Zeta.RiemannSiegel.correction qz128) 398745 1048576 1 4194304 13009931880387 17592186044416 1427663429031139 19403143268014227456 5187645287644914315 18446744073709551616 

noncomputable abbrev qz699 := (@HPow.hPow Real Real Real qz7 qz127 qz9)

noncomputable def Ns78p954 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz699 1 1 0 1 398745 1048576 1 4194304 398745 1048576 1 4194304 

noncomputable def Ns78p955 := @Enclosure.Real.IsNear.sqrt_image qz127 100287880413 2097152000 75117 2097152000 29004742 29004765 4194304 (@Enclosure.Real.IsNear.of_eq qz127 (@HMul.hMul Real Real Real qz5 qz126 qz3) Bool.false 100287880413 2097152000 75117 2097152000 (BSN.t_div_two_pi_mk qz126 300468 1000 qz129) (@Enclosure.Real.IsNear.mulLit_ff qz126 qz3 300468 1000 0 1 1335089 8388608 1 8388608 100287880413 2097152000 75117 2097152000 (Enclosure.Real.IsNear.const Bool.false 300468 1000) RS079to096.d32 rfl)) 

noncomputable abbrev qz878 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 300468 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz700 := qz878

noncomputable abbrev qz473 := qz700

noncomputable abbrev qz132 := qz473

noncomputable def Ns78p956 := @Enclosure.Real.IsNear.sqrt_image qz132 58009507 8388608 23 8388608 11029719 11029724 4194304 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 58009507 8388608 23 8388608 58009507 8388608 23 8388608 (Ns78p955 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns78p957 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz132) 22059443 8388608 5 8388608 1594979 1594981 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz132) Bool.false 22059443 8388608 5 8388608 22059443 8388608 5 8388608 (Ns78p956 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns78p958 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz132)) Bool.false 3189960 8388608 2 8388608 398745 1048576 1 4194304 (Ns78p957 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz133 := (@HMul.hMul Real Real Real qz336 qz334 qz467)

noncomputable abbrev qz701 := (@HMul.hMul Real Real Real qz841 qz877 qz877)

noncomputable abbrev qz474 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz701 qz695) qz640)

noncomputable abbrev qz134 := (Real.cos (@HMul.hMul Real Real Real qz336 qz334 qz474))

noncomputable def Ns78p959 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz128) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz133)) qz134) Bool.false 13009931880387 

noncomputable def Ns78p960 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz133)) qz134 4867979 4194304 13 

noncomputable def Ns78p961 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz133)) Bool.false 9735958 8388608 208 8388608 4867979 4194304 13 

noncomputable def Ns78p962 := @Enclosure.Real.IsNear.recentre' (Real.cos qz133) Bool.false 7227717 8388608 84708997 4626069848064 7227717 8388608 84708997 4626069848064 

noncomputable def Ns78p963 := @Enclosure.Real.IsNear.cos_image qz133 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24120705) qz378) Bool.false 24120705 4194304 73 4194304 Bool.false 7227717 8388608 1 

noncomputable def Ns78p964 := nat_lit 620679734473965352085484769 

noncomputable def Ns78p965 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz128 884279719003555 140737488355328 1 500000000000000 7677859 8388608 23 8388608 6789374999068915788745 1180591620717411303424 Ns78p964 

noncomputable def Ns78p966 := @Enclosure.Real.IsNear.subLit_ff_p qz132 qz1 58009507 8388608 23 8388608 6 1 0 1 7677859 7677859 8388608 23 

noncomputable def Ns78p967 := @Ns78p966 8388608 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 58009507 8388608 23 8388608 58009507 8388608 23 8388608 (Ns78p955 rfl rfl rfl rfl rfl rfl) rfl) qz362 

noncomputable def Ns78p968 := @Enclosure.Real.IsNear.recentre' qz133 Bool.false 6789374999068915788745 1180591620717411303424 Ns78p964 Ns78p385 24120705 4194304 73 4194304 (@Ns78p965 Ns78p385 RS079to096.d31 (Ns78p967 rfl rfl) rfl) 

noncomputable def Ns78p969 := nat_lit 26694711737567964727095639121535271387950339523067434511451781403000364685416667873280 

noncomputable def Ns78p970 := nat_lit 10261105151003206546865889481468629274565464843802429243981380042100117410173485056 

noncomputable def Ns78p971 := nat_lit 69898107999576378617507938640098571092473021331619981692169171916361364462189087358976 

noncomputable def Ns78p972 := BSN.sin_dyadic_bound_f 17840181452 17179869184 3 2 8388608 2208037 Ns78p969 Ns78p97 Ns78p970 Ns78p971 Ns78p100 Ns78p970 7227717 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 17840181452) qz352 0 2 Ns78p969 Ns78p97 Ns78p970 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 17840181452) qz353 0 2 Ns78p971 Ns78p100 Ns78p970 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p973 := @Ns78p963 1102941 (Ns78p968 rfl) (Enclosure.sfrac_false_div 24120705 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24120705) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 627695582369983286476800) qz397) 226375608064910080 72057594037927936 Bool.false 7227717 8388608 0 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q3 24120705 4194304 226375608064910080 72057594037927936 0 627695582369983286476800 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 7227717 8388608 627695582369983286476800 604462909807314587353088 17840181452 17179869184 2208037 2205882 (Ns78p972 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p974 := @Enclosure.Real.IsNear.inv_image (Real.cos qz133) 7227717 8388608 84708997 4626069848064 4867875 4868083 4194304 (Ns78p962 (Ns78p973 rfl rfl) rfl) rfl 

noncomputable def Ns78p975 := @Enclosure.Real.IsNear.recentre' qz134 Bool.false 2672553 4194304 

noncomputable abbrev qz135 := (@HMul.hMul Real Real Real qz336 qz334 qz474)

noncomputable def Ns78p976 := @Enclosure.Real.IsNear.cos_image qz135 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7381591)) qz354) Bool.true 7381591 8388608 

noncomputable def Ns78p977 := nat_lit 8714644824216843383057694725 

noncomputable def Ns78p978 := nat_lit 14737636231095824616004501496489149 

noncomputable def Ns78p979 := @Enclosure.Real.IsNear.recentre' qz135 Bool.true Ns78p977 Ns78p397 Ns78p978 

noncomputable abbrev qz136 := qz474

noncomputable def Ns78p980 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz136 884279719003555 140737488355328 1 500000000000000 9855077117495 

noncomputable abbrev qz475 := (@HSub.hSub Real Real Real qz634 qz701 qz695)

noncomputable abbrev qz137 := qz475

noncomputable def Ns78p981 := @Enclosure.Real.IsNear.subLit_tf qz137 qz26 5457030606391 70368744177664 546120027 70368744177664 1 16 

noncomputable abbrev qz476 := qz701

noncomputable abbrev qz138 := qz476

noncomputable def Ns78p982 := @Enclosure.Real.IsNear.subLit_ff_n qz138 qz128 58949518823881 70368744177664 353182043 70368744177664 7677859 8388608 23 8388608 

noncomputable def Ns78p983 := @Enclosure.Real.IsNear.mulLit_ff qz128 qz128 7677859 8388608 23 8388608 7677859 8388608 23 8388608 58949518823881 70368744177664 

noncomputable def Ns78p984 := nat_lit 24707213136550955771929541950342739960553234431118612417601 

noncomputable def Ns78p985 := nat_lit 8814543486979952989529879599295003932213390754566163521 

noncomputable def Ns78p986 := nat_lit 74104010322678907409809566091829629873795276511846704925761 

noncomputable def Ns78p987 := BSN.cos_dyadic_bound_f 7381591 8388608 3 2 4194304 1102941 Ns78p984 Ns78p501 Ns78p985 Ns78p986 Ns78p504 Ns78p985 2672553 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 7381591) (BSN.cosEvenQ 8388608) 0 2 Ns78p984 Ns78p501 Ns78p985 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 7381591) (BSN.cosOddQ 8388608) 0 2 Ns78p986 Ns78p504 Ns78p985 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p988 := @Ns78p975 230297209 4626069848064 2672553 4194304 230297209 4626069848064 (@Ns78p976 205 4194304 Bool.false 2672553 4194304 1 1102941 (@Ns78p979 Ns78p495 7381591 8388608 205 4194304 (@Ns78p980 70368744177664 546120027 70368744177664 Ns78p977 Ns78p397 Ns78p978 Ns78p495 RS079to096.d31 (@Ns78p981 0 1 157681233879920 9855077117495 70368744177664 546120027 70368744177664 (@Ns78p982 45776890601016393728 5457030606391 70368744177664 546120027 70368744177664 (@Ns78p983 353182043 70368744177664 (Ns78p967 rfl rfl) (Ns78p967 rfl rfl) rfl) (Ns78p967 rfl rfl) rfl rfl) qz366 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7381591 8388608) (BSN.cos_neg_of_bound 7381591 8388608 Bool.false 2672553 4194304 1 1102941 (Ns78p987 rfl rfl)) rfl rfl) 

noncomputable def Ns78p989 := @Ns78p953 1145722615488800515763 Ns78p694 (Ns78p954 qz28 (@Enclosure.Real.IsNear.of_eq qz699 (@Inv.inv Real Real.instInv (Real.sqrt qz132)) Bool.false 398745 1048576 1 4194304 (BSN.rpow_neg_quarter_mk qz127 (BSN.t_div_two_pi_nonneg qz126 300468 1000 qz129)) Ns78p958) rfl) (@Ns78p959 17592186044416 1427663429031139 19403143268014227456 (BSN.correction_mk qz128 (BSN.cos_two_pi_p_ne_zero_mk qz126 300468 1000 6 qz129 rfl rfl (@BSN.floor_sqrt_eq_dec qz126 300468 1000 6 qz129 rfl rfl rfl))) (@Ns78p960 524288 2672553 4194304 230297209 4626069848064 13009931880387 17592186044416 1427663429031139 19403143268014227456 (@Ns78p961 524288 (Ns78p974 rfl rfl rfl rfl rfl) rfl) (Ns78p988 rfl) rfl)) 

noncomputable def Ns78p990 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz126) (hardyZApproximantRS₀ qz126) Bool.true 42049582948904985227 18446744073709551616 65378615707795649619635 Ns78p694 (@Eq.refl Real (hardyZApproximantRS₀ qz126)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz126) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz126) qz126 6) (@HMul.hMul Real Real Real qz5 qz696 (Zeta.RiemannSiegel.correction qz128))) Bool.true 42049582948904985227 18446744073709551616 65378615707795649619635 Ns78p694 (BSN.hardyZApproximantRS₀_eq qz126 6 (@BSN.floor_sqrt_eq_dec qz126 300468 1000 6 qz129 rfl rfl rfl)) (@Ns78p891 42049582948904985227 18446744073709551616 65378615707795649619635 Ns78p694 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz126) qz126 6) (@HAdd.hAdd Real Real Real qz351 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz126) qz126 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz126) qz126 6)) Bool.true 33525737 16777216 52967 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz126) qz126 6) (Ns78p952 (Ns78p951 rfl rfl rfl rfl) rfl rfl)) (Ns78p989 rfl) rfl rfl)) 

theorem RS079to096.d43 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz126) Bool.true 42049582948904985227 18446744073709551616 65378615707795649619635 Ns78p694 := Ns78p990 

noncomputable abbrev qz879 := (Enclosure.sfrac Bool.false 302092 1000)

noncomputable abbrev qz702 := qz879

noncomputable abbrev qz477 := qz702

noncomputable abbrev qz139 := qz477

noncomputable abbrev qz880 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 302092 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz703 := qz880

noncomputable abbrev qz478 := qz703

noncomputable abbrev qz140 := qz478

noncomputable abbrev qz881 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 302092 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz704 := qz881

noncomputable abbrev qz479 := qz704

noncomputable abbrev qz141 := qz479

noncomputable abbrev qz705 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz140 qz9))

noncomputable def Ns78p991 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz139) qz139 6) (@HMul.hMul Real Real Real qz5 qz705 (Zeta.RiemannSiegel.correction qz141)) 37149523 33554432 53247 33554432 10625720869897455 36028797018963968 4396702518527553218981 Ns78p603 981912595138378364616704 

noncomputable def Ns78p992 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz139) qz139 Real.cos BSN.quadSignPos 5 6 302092 1000 68 67108864 33554432 1125899906842624 Bool.false 29094414194 1195 120242927 62 27397080 8 

noncomputable def Ns78p993 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz139) qz139 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 302092 1000 9 33 67108864 33554432 1125899906842624 Bool.false 29094414194 1195 

noncomputable def Ns78p994 := Ns78p993 93032624 61 33554424 8 108007536 61 30011992 8 Bool.false 61915270 26495 Bool.false 41273530 Bool.true 55124588 3537118876014220 1 Bool.false 38720320 Bool.true Bool.false 49131345 Bool.true Bool.false 20582912 

noncomputable def Ns78p995 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz139) qz139 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 302092 1000 142 64 67108864 33554432 1125899906842624 Bool.false 29094414194 1195 

noncomputable def Ns78p996 := Ns78p995 46516304 61 47453136 16 73726608 61 38745320 8 Bool.false 67108840 1261 Bool.false 73372182 Bool.false 75676877 3537118876014220 1 Bool.false 30838516 Bool.true Bool.false 28773791 Bool.false Bool.false 61915270 

noncomputable def Ns78p997 := nat_lit 203793814906712238974498538184160652316741928215531 

noncomputable def Ns78p998 := nat_lit 470068629570967482105173307065917127478214656000 

noncomputable def Ns78p999 := nat_lit 94117632000000000000000000 

noncomputable def Ns78p1000 := nat_lit 1207648019653295260072084111360000 

noncomputable def Ns78p1001 := nat_lit 2188927631690015467373529947669790720 

noncomputable abbrev qz706 := (@Eq.refl Real qz879)

noncomputable abbrev qz480 := qz706

noncomputable abbrev qz142 := qz480

noncomputable def Ns78p1002 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz139 302092 1000 365039305856 16000000 604184 4000 2000 Ns78p1000 Ns78p1001 qz142 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns78p1003 := nat_lit 2136933032596206926949237791749944401636799841205286338560 

noncomputable abbrev qz481 := (Enclosure.sfrac Bool.false 302092 2000)

noncomputable abbrev qz707 := (Real.log (Enclosure.sfrac Bool.false 365039305856 16000000))

noncomputable abbrev qz143 := (@HSub.hSub Real Real Real qz339 (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 302092 4000) qz707) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 604184)))))) qz481)

noncomputable abbrev qz482 := (@HSub.hSub Real Real Real qz12 qz143 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 302092 2000) (Real.log Real.pi)))

noncomputable def Ns78p1004 := @Enclosure.Real.IsNear.addLit_ft_p qz482 (Enclosure.sfrac Bool.true Ns78p1000 Ns78p1001) 976247785006907114123 2251799813685248000 1674257203925042371129 Ns78p999 Ns78p1000 Ns78p1001 0 1 Ns78p1003 

noncomputable def Ns78p1005 := nat_lit 16378719958582442145578221568000 

noncomputable abbrev qz483 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 302092 2000) (Real.log Real.pi))

noncomputable def Ns78p1006 := @Enclosure.Real.IsNear.subLit_ff_p qz143 qz483 1365599442272478151307 2251799813685248000 3230125388767217209 367647000000000000000000 2900895903003 16777216000 75523 8388608000 Ns78p1005 976247785006907114123 2251799813685248000 

noncomputable abbrev qz144 := (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 302092 4000) qz707) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 604184))))))

noncomputable def Ns78p1007 := @Enclosure.Real.IsNear.subLit_ff_p qz144 qz481 341144959386076024143 450359962737049600 3230125388767217209 367647000000000000000000 302092 2000 0 1 546239776908991260522800 1365599442272478151307 2251799813685248000 3230125388767217209 367647000000000000000000 

noncomputable def Ns78p1008 := nat_lit 768190155985227487098380708650942464 

noncomputable def Ns78p1009 := nat_lit 12131778017086380399656960 

noncomputable def Ns78p1010 := nat_lit 22624955202457043605768137051742090284056446392720951733381575018085335798929058401604200426373120 

noncomputable def Ns78p1011 := nat_lit 206329624301918200380710911168485290895316689761878212973567643558797282576145793948559557525504 

noncomputable def Ns78p1012 := nat_lit 1319331095905289407769747547482850770198791794505835757222015120642819906323426267816263680 

noncomputable def Ns78p1013 := BSN.log_dyadic_bound 102895305856 627183305856 5 4 Ns78p1010 33554432 8823528 Ns78p1011 Ns78p1012 11110243 730078611712 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 102895305856) (BSN.artanhQ 627183305856) 0 4 Ns78p1011 Ns78p1010 Ns78p1012 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns78p1014 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 302092 4000) qz707 302092 4000 0 1 22597197475072705 2251799813685248 62500007720587 551470500000000000000 341321628981983179943 450359962737049600 674312583297413143 78781500000000000000000 (Enclosure.Real.IsNear.const Bool.false 302092 4000) (BSN.isNear_log_sfrac 365039305856 16000000 22597197475072705 2251799813685248 62500007720587 551470500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 365039305856) qz347)) Bool.false Ns78p1009 Ns78p84 1000000123529392 8823528000000000000000 22597197475072705 2251799813685248 62500007720587 551470500000000000000 (BSN.log_rat_reduce_isNear 365039305856 16000000 14 730078611712 524288000000 11110243 33554432 24973259072661432 36028797018963968 8823528 1000000000000000 rfl rfl rfl rfl (Ns78p1013 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns78p1015 := BSN.arctan_dyadic_bound_f 1000 604184 1 0 4194304 1102941 0 1 1 0 1 1 6942 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 604184) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 604184) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz484 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 604184)))

noncomputable def Ns78p1016 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz484 884279719003555 562949953421312 1 2000000000000000 6942 4194304 1 1102941 3705029963958836002816 883347979535779 562949953421312 2000000001102941 2205882000000000000000 qz17 (Ns78p1015 rfl) rfl rfl 

noncomputable def Ns78p1017 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 302092 4000) qz707) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz484)) 341321628981983179943 450359962737049600 674312583297413143 78781500000000000000000 883347979535779 2251799813685248 2000000001102941 8823528000000000000000 Ns78p1008 341144959386076024143 450359962737049600 3230125388767217209 367647000000000000000000 (Ns78p1014 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz484) 1 4 0 1 883347979535779 562949953421312 2000000001102941 2205882000000000000000 883347979535779 2251799813685248 2000000001102941 8823528000000000000000 qz350 Ns78p1016 rfl) 

noncomputable def Ns78p1018 := @Ns78p1004 Ns78p997 Ns78p998 1674257203925042371129 Ns78p999 (@Ns78p1006 1674257203925042371129 Ns78p999 (Ns78p1007 (Ns78p1017 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 302092 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz481 (Real.log Real.pi) 302092 2000 0 1 38410761 33554432 1 16777216 2900895903003 16777216000 75523 8388608000 (Enclosure.Real.IsNear.const Bool.false 302092 2000) RS079to096.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns78p1000 Ns78p1001) 

noncomputable def Ns78p1019 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz139) Bool.false Ns78p997 Ns78p998 1674257203925042371129 Ns78p999 1818400887 4194304 75 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz139) (@HAdd.hAdd Real Real Real qz351 qz482 (Enclosure.sfrac Bool.true Ns78p1000 Ns78p1001)) Bool.false Ns78p997 Ns78p998 1674257203925042371129 Ns78p999 Ns78p1002 (Ns78p1018 rfl rfl)) 

noncomputable def Ns78p1020 := nat_lit 140263965130500702562318515776431161080059850786569271514263482998913921877626511687680 

noncomputable def Ns78p1021 := nat_lit 282370601035513918567680316438273970999345249289953566008797337712077324067438329856 

noncomputable def Ns78p1022 := nat_lit 366900832463920531795057963664038692589967335942164357716199640736097860678626916171776 

noncomputable def Ns78p1023 := BSN.sin_dyadic_bound_f 26999295664 17179869184 3 2 8388608 2208037 Ns78p1020 Ns78p97 Ns78p1021 Ns78p1022 Ns78p100 Ns78p1021 8388605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26999295664) qz352 0 2 Ns78p1020 Ns78p97 Ns78p1021 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26999295664) qz353 0 2 Ns78p1022 Ns78p100 Ns78p1021 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1024 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz139) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1818400887) qz378) Bool.false 1818400887 4194304 75 4194304 Bool.false 8388605 8388608 1 1102941 (Ns78p1019 rfl) (Enclosure.sfrac_false_div 1818400887 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1818400887) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949953264809873678270464) qz397) 226375608064910080 72057594037927936 Bool.false 8388605 8388608 68 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q3 1818400887 4194304 226375608064910080 72057594037927936 68 949953264809873678270464 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388605 8388608 949953264809873678270464 604462909807314587353088 26999295664 17179869184 2208037 2205882 (Ns78p1023 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p1025 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz139) Bool.false Ns78p997 Ns78p998 1674257203925042371129 Ns78p999 29094414194 67108864 1195 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz139) (@HAdd.hAdd Real Real Real qz351 qz482 (Enclosure.sfrac Bool.true Ns78p1000 Ns78p1001)) Bool.false Ns78p997 Ns78p998 1674257203925042371129 Ns78p999 Ns78p1002 (Ns78p1018 rfl rfl)) 

noncomputable def Ns78p1026 := Ns78p996 26495 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 142 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 30838516 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 28773791 67108864) qz142 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz139) qz139 1) Bool.false 8388605 8388608 86914879 4626069848064 67108840 67108864 1261 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz139) qz139 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz139)) Bool.false 8388605 8388608 86914879 4626069848064 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz139) qz139) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz139)) Bool.false 8388605 8388608 86914879 4626069848064 8388605 8388608 86914879 4626069848064 (Ns78p1024 rfl rfl) rfl)) rfl) (Ns78p1025 rfl) RS079to096.d7 

noncomputable def Ns78p1027 := nat_lit 988379659252491222229674626193237946186895916785432741347318784256 

noncomputable def Ns78p1028 := nat_lit 839946214765171140416906558126297077266772763002422093793157376 

noncomputable def Ns78p1029 := nat_lit 2963459085327943324408190065463461244406154204830293379854370038016 

noncomputable def Ns78p1030 := BSN.cos_dyadic_bound_f 73372182 67108864 3 2 67108864 33554432 Ns78p1027 Ns78p116 Ns78p1028 Ns78p1029 Ns78p119 Ns78p1028 30838516 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 73372182) qz357 0 2 Ns78p1027 Ns78p116 Ns78p1028 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 73372182) (BSN.cosOddQ 67108864) 0 2 Ns78p1029 Ns78p119 Ns78p1028 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1031 := nat_lit 269547627138774045812284446185849192149208577608623024055129873805866751256190064080282579388143271601 

noncomputable def Ns78p1032 := nat_lit 35282424257379429124695792657921588608643020716023157465452878152150520682787291174028116524721 

noncomputable def Ns78p1033 := nat_lit 1634207089935431573469411903381362663061395349560489404689719937197376723049271199493315841423942123185 

noncomputable def Ns78p1034 := BSN.cos_dyadic_bound_f 75676877 67108864 4 3 67108864 33554432 Ns78p1031 Ns78p110 Ns78p1032 Ns78p1033 Ns78p113 Ns78p1032 28773791 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 75676877) qz357 0 3 Ns78p1031 Ns78p110 Ns78p1032 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 75676877) (BSN.cosOddQ 67108864) 0 3 Ns78p1033 Ns78p113 Ns78p1032 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1035 := nat_lit 177995220485024808710835900877313372302194506822519372011323040000 

noncomputable def Ns78p1036 := nat_lit 8421179311676651809946565311020982636742356844789216100000000 

noncomputable def Ns78p1037 := nat_lit 466164324122846070139735065001507655391002315957421077489303200000 

noncomputable def Ns78p1038 := BSN.sin_dyadic_bound_f 41273530 67108864 3 2 67108864 33554432 Ns78p1035 Ns78p127 Ns78p1036 Ns78p1037 Ns78p130 Ns78p1036 38720320 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 41273530) qz356 0 2 Ns78p1035 Ns78p127 Ns78p1036 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 41273530) (BSN.sinOddQ 67108864) 0 2 Ns78p1037 Ns78p130 Ns78p1036 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1039 := nat_lit 566432469293856463231988249798864558303299894713284129556302725120 

noncomputable def Ns78p1040 := nat_lit 85263440418164488560095969681460748893293330316609347660087296 

noncomputable def Ns78p1041 := nat_lit 1483375564485137518340395736950875287677101058857136305132200329216 

noncomputable def Ns78p1042 := BSN.sin_dyadic_bound_f 55124588 67108864 3 2 67108864 33554432 Ns78p1039 Ns78p127 Ns78p1040 Ns78p1041 Ns78p130 Ns78p1040 49131345 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 55124588) qz356 0 2 Ns78p1039 Ns78p127 Ns78p1040 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 55124588) (BSN.sinOddQ 67108864) 0 2 Ns78p1041 Ns78p130 Ns78p1040 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1043 := Ns78p994 45102 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 9 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 38720320 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 33 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 49131345 67108864) qz142 rfl rfl (Ns78p1026 RS079to096.d9 RS079to096.d11 RS079to096.d13 RS079to096.d17 (Ns78p1030 rfl rfl) (Ns78p1034 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns78p1025 rfl) RS079to096.d19 RS079to096.d21 RS079to096.d23 RS079to096.d25 RS079to096.d17 (Ns78p1038 rfl rfl) (Ns78p1042 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns78p1044 := nat_lit 498397502213246020242183085370318883161943842286874581480379580416 

noncomputable def Ns78p1045 := nat_lit 213757540567542629025955327017366266523217372758783254436315136 

noncomputable def Ns78p1046 := nat_lit 1494764991558602975468497345456921916952785092115106177932266110976 

noncomputable def Ns78p1047 := BSN.cos_dyadic_bound_f 61835828 67108864 3 2 67108864 33554432 Ns78p1044 Ns78p116 Ns78p1045 Ns78p1046 Ns78p119 Ns78p1045 40579743 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 61835828) qz357 0 2 Ns78p1044 Ns78p116 Ns78p1045 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 61835828) (BSN.cosOddQ 67108864) 0 2 Ns78p1046 Ns78p119 Ns78p1045 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1048 := Ns78p992 Bool.false 20582912 45102 Bool.true 61835828 3537118876014220 1 Bool.false 40579743 Bool.false Bool.false 37149523 53247 BSN.abs_quadSignPos qz689 (BSN.sfrac_eq_quadSignPos_mul Bool.false 40579743 67108864) qz142 rfl (Ns78p1043 rfl rfl) (Ns78p1025 rfl) RS079to096.d27 RS079to096.d29 RS079to096.d17 (Ns78p1047 rfl rfl) rfl 

noncomputable def Ns78p1049 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz139) qz139 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz139) qz139 6) 37149523 67108864 53247 67108864 37149523 67108864 53247 67108864 4986124573343744 37149523 33554432 53247 33554432 (Ns78p1048 rfl rfl rfl rfl) 

noncomputable def Ns78p1050 := @Enclosure.Real.IsNear.mulLit_ff qz705 (Zeta.RiemannSiegel.correction qz141) 3111 8192 1 4194304 3415532262905 4398046511104 2741383104174077 38806286536028454912 10625720869897455 36028797018963968 

noncomputable abbrev qz708 := (@HPow.hPow Real Real Real qz7 qz140 qz9)

noncomputable def Ns78p1051 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz708 1 1 0 1 3111 8192 1 4194304 3111 8192 1 4194304 

noncomputable def Ns78p1052 := @Enclosure.Real.IsNear.sqrt_image qz140 100829926547 2097152000 75523 2097152000 29083020 29083043 4194304 (@Enclosure.Real.IsNear.of_eq qz140 (@HMul.hMul Real Real Real qz5 qz139 qz3) Bool.false 100829926547 2097152000 75523 2097152000 (BSN.t_div_two_pi_mk qz139 302092 1000 qz142) (@Enclosure.Real.IsNear.mulLit_ff qz139 qz3 302092 1000 0 1 1335089 8388608 1 8388608 100829926547 2097152000 75523 2097152000 (Enclosure.Real.IsNear.const Bool.false 302092 1000) RS079to096.d32 rfl)) 

noncomputable abbrev qz882 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 302092 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz709 := qz882

noncomputable abbrev qz485 := qz709

noncomputable abbrev qz145 := qz485

noncomputable def Ns78p1053 := @Enclosure.Real.IsNear.sqrt_image qz145 58166063 8388608 23 8388608 11044592 11044598 4194304 (@Enclosure.Real.IsNear.recentre' qz145 Bool.false 58166063 8388608 23 8388608 58166063 8388608 23 8388608 (Ns78p1052 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns78p1054 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz145) 11044595 4194304 3 4194304 1592831 1592833 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz145) Bool.false 22089190 8388608 6 8388608 11044595 4194304 3 4194304 (Ns78p1053 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns78p1055 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz145)) Bool.false 3185664 8388608 2 8388608 3111 8192 1 4194304 (Ns78p1054 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz146 := (@HMul.hMul Real Real Real qz336 qz334 qz479)

noncomputable abbrev qz710 := (@HMul.hMul Real Real Real qz841 qz881 qz881)

noncomputable abbrev qz486 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz710 qz704) qz640)

noncomputable abbrev qz147 := (Real.cos (@HMul.hMul Real Real Real qz336 qz334 qz486))

noncomputable def Ns78p1056 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz141) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz146)) qz147) Bool.false 3415532262905 

noncomputable def Ns78p1057 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz146)) qz147 4583555 4194304 23 

noncomputable def Ns78p1058 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz146)) Bool.false 9167110 8388608 184 8388608 4583555 4194304 23 

noncomputable def Ns78p1059 := @Enclosure.Real.IsNear.recentre' (Real.cos qz146) Bool.false 7676219 8388608 168315053 9252139696128 7676219 8388608 168315053 9252139696128 

noncomputable def Ns78p1060 := @Enclosure.Real.IsNear.cos_image qz146 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 49225081) qz354) Bool.false 49225081 8388608 145 8388608 Bool.false 7676219 8388608 1 

noncomputable def Ns78p1061 := nat_lit 620679734475310157885469921 

noncomputable def Ns78p1062 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz141 884279719003555 140737488355328 1 500000000000000 7834415 8388608 23 8388608 6927814294757236345325 1180591620717411303424 Ns78p1061 

noncomputable def Ns78p1063 := @Enclosure.Real.IsNear.subLit_ff_p qz145 qz1 58166063 8388608 23 8388608 6 1 0 1 7834415 7834415 8388608 23 

noncomputable def Ns78p1064 := @Ns78p1063 8388608 (@Enclosure.Real.IsNear.recentre' qz145 Bool.false 58166063 8388608 23 8388608 58166063 8388608 23 8388608 (Ns78p1052 rfl rfl rfl rfl rfl rfl) rfl) qz362 

noncomputable def Ns78p1065 := @Enclosure.Real.IsNear.recentre' qz146 Bool.false 6927814294757236345325 1180591620717411303424 Ns78p1061 Ns78p385 49225081 8388608 145 8388608 (@Ns78p1062 Ns78p385 RS079to096.d31 (Ns78p1064 rfl rfl) rfl) 

noncomputable def Ns78p1066 := nat_lit 1397153095909731794419712 

noncomputable def Ns78p1067 := nat_lit 40961335652196972875874573880558466109512238945126296723821696944949272693573591040000 

noncomputable def Ns78p1068 := nat_lit 24149802029577866467447369306579360037573139888459977276774279007737585689600000000 

noncomputable def Ns78p1069 := nat_lit 107240588933420374319676588232109139894375983582178032408703952689806996201576243200000 

noncomputable def Ns78p1070 := BSN.sin_dyadic_bound_f 19854739660 17179869184 3 2 8388608 2208037 Ns78p1067 Ns78p97 Ns78p1068 Ns78p1069 Ns78p100 Ns78p1068 7676219 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 19854739660) qz352 0 2 Ns78p1067 Ns78p97 Ns78p1068 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 19854739660) qz353 0 2 Ns78p1069 Ns78p100 Ns78p1068 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1071 := @Ns78p1060 1102941 (Ns78p1065 rfl) (Enclosure.sfrac_false_div 49225081 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 49225081) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns78p1066) qz355) 226375608064910080 72057594037927936 Bool.false 7676219 8388608 0 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q3 49225081 8388608 226375608064910080 72057594037927936 0 Ns78p1066 Ns78p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 7676219 8388608 Ns78p1066 Ns78p84 19854739660 17179869184 2208037 2205882 (Ns78p1070 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p1072 := @Enclosure.Real.IsNear.inv_image (Real.cos qz146) 7676219 8388608 168315053 9252139696128 4583463 4583647 4194304 (Ns78p1059 (Ns78p1071 rfl rfl) rfl) rfl 

noncomputable def Ns78p1073 := @Enclosure.Real.IsNear.recentre' qz147 Bool.false 2980684 4194304 

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz336 qz334 qz486)

noncomputable def Ns78p1074 := @Enclosure.Real.IsNear.cos_image qz148 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 6546251)) qz354) Bool.true 6546251 8388608 

noncomputable def Ns78p1075 := nat_lit 7728449520458007637047672445 

noncomputable def Ns78p1076 := nat_lit 14931978504086206449343398377373909 

noncomputable def Ns78p1077 := @Enclosure.Real.IsNear.recentre' qz148 Bool.true Ns78p1075 Ns78p397 Ns78p1076 

noncomputable abbrev qz149 := qz486

noncomputable def Ns78p1078 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz149 884279719003555 140737488355328 1 500000000000000 8739824463199 

noncomputable abbrev qz487 := (@HSub.hSub Real Real Real qz634 qz710 qz704)

noncomputable abbrev qz150 := qz487

noncomputable def Ns78p1079 := @Enclosure.Real.IsNear.subLit_tf qz150 qz26 4341777952095 70368744177664 553321603 70368744177664 1 16 

noncomputable abbrev qz488 := qz710

noncomputable abbrev qz151 := qz488

noncomputable def Ns78p1080 := @Enclosure.Real.IsNear.subLit_ff_n qz151 qz141 61378058392225 70368744177664 360383619 70368744177664 7834415 8388608 23 8388608 

noncomputable def Ns78p1081 := @Enclosure.Real.IsNear.mulLit_ff qz141 qz141 7834415 8388608 23 8388608 7834415 8388608 23 8388608 61378058392225 70368744177664 

noncomputable def Ns78p1082 := nat_lit 15280422268772914023334898690254647208543482871680430205281 

noncomputable def Ns78p1083 := nat_lit 3372416659479420897887544463143199897001243777758620001 

noncomputable def Ns78p1084 := nat_lit 45834521972999783228208920981837655225836446127485773375841 

noncomputable def Ns78p1085 := BSN.cos_dyadic_bound_f 6546251 8388608 3 2 4194304 1102941 Ns78p1082 Ns78p501 Ns78p1083 Ns78p1084 Ns78p504 Ns78p1083 2980684 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 6546251) (BSN.cosEvenQ 8388608) 0 2 Ns78p1082 Ns78p501 Ns78p1083 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 6546251) (BSN.cosOddQ 8388608) 0 2 Ns78p1084 Ns78p504 Ns78p1083 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1086 := @Ns78p1073 466109123 9252139696128 745171 1048576 466109123 9252139696128 (@Ns78p1074 415 8388608 Bool.false 2980684 4194304 1 1102941 (@Ns78p1077 Ns78p495 6546251 8388608 415 8388608 (@Ns78p1078 70368744177664 553321603 70368744177664 Ns78p1075 Ns78p397 Ns78p1076 Ns78p495 RS079to096.d31 (@Ns78p1079 0 1 139837191411184 8739824463199 70368744177664 553321603 70368744177664 (@Ns78p1080 36421473263167733760 4341777952095 70368744177664 553321603 70368744177664 (@Ns78p1081 360383619 70368744177664 (Ns78p1064 rfl rfl) (Ns78p1064 rfl rfl) rfl) (Ns78p1064 rfl rfl) rfl rfl) qz366 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 6546251 8388608) (BSN.cos_neg_of_bound 6546251 8388608 Bool.false 2980684 4194304 1 1102941 (Ns78p1085 rfl rfl)) rfl rfl) 

noncomputable def Ns78p1087 := @Ns78p1050 4396702518527553218981 Ns78p603 (Ns78p1051 qz28 (@Enclosure.Real.IsNear.of_eq qz708 (@Inv.inv Real Real.instInv (Real.sqrt qz145)) Bool.false 3111 8192 1 4194304 (BSN.rpow_neg_quarter_mk qz140 (BSN.t_div_two_pi_nonneg qz139 302092 1000 qz142)) Ns78p1055) rfl) (@Ns78p1056 4398046511104 2741383104174077 38806286536028454912 (BSN.correction_mk qz141 (BSN.cos_two_pi_p_ne_zero_mk qz139 302092 1000 6 qz142 rfl rfl (@BSN.floor_sqrt_eq_dec qz139 302092 1000 6 qz142 rfl rfl rfl))) (@Ns78p1057 1048576 745171 1048576 466109123 9252139696128 3415532262905 4398046511104 2741383104174077 38806286536028454912 (@Ns78p1058 1048576 (Ns78p1072 rfl rfl rfl rfl rfl) rfl) (Ns78p1086 rfl) rfl)) 

noncomputable def Ns78p1088 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz139) (hardyZApproximantRS₀ qz139) Bool.false 29263275716852497 36028797018963968 262686494916515945556389 Ns78p603 (@Eq.refl Real (hardyZApproximantRS₀ qz139)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz139) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz139) qz139 6) (@HMul.hMul Real Real Real qz5 qz705 (Zeta.RiemannSiegel.correction qz141))) Bool.false 29263275716852497 36028797018963968 262686494916515945556389 Ns78p603 (BSN.hardyZApproximantRS₀_eq qz139 6 (@BSN.floor_sqrt_eq_dec qz139 302092 1000 6 qz142 rfl rfl rfl)) (@Ns78p991 29263275716852497 36028797018963968 262686494916515945556389 Ns78p603 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz139) qz139 6) (@HAdd.hAdd Real Real Real qz351 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz139) qz139 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz139) qz139 6)) Bool.false 37149523 33554432 53247 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz139) qz139 6) (Ns78p1049 (Ns78p1048 rfl rfl rfl rfl) rfl rfl)) (Ns78p1087 rfl) rfl rfl)) 

theorem RS079to096.d44 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz139) Bool.false 29263275716852497 36028797018963968 262686494916515945556389 Ns78p603 := Ns78p1088 

noncomputable def Ns78p1089 := nat_lit 6024216183375853412279123968 

noncomputable abbrev qz883 := (Enclosure.sfrac Bool.false 303713 1000)

noncomputable abbrev qz711 := qz883

noncomputable abbrev qz489 := qz711

noncomputable abbrev qz152 := qz489

noncomputable abbrev qz884 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 303713 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz712 := qz884

noncomputable abbrev qz490 := qz712

noncomputable abbrev qz153 := qz490

noncomputable abbrev qz885 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 303713 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz713 := qz885

noncomputable abbrev qz491 := qz713

noncomputable abbrev qz154 := qz491

noncomputable abbrev qz714 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz153 qz9))

noncomputable def Ns78p1090 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 6) (@HMul.hMul Real Real Real qz5 qz714 (Zeta.RiemannSiegel.correction qz154)) 71264937 33554432 53535 33554432 22822379061690425975 73786976294838206464 1069837702615763750783 Ns78p694 Ns78p1089 

noncomputable def Ns78p1091 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos BSN.quadSignPos 5 6 303713 1000 68 67108864 33554432 1125899906842624 Bool.false 29305211146 1202 120242927 62 27397080 8 

noncomputable def Ns78p1092 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 303713 1000 9 33 67108864 33554432 1125899906842624 Bool.false 29305211146 1202 

noncomputable def Ns78p1093 := Ns78p1092 93032624 61 33554424 8 108007536 61 30011992 8 Bool.true 50436858 26639 Bool.false 101264599 Bool.true 19407851 3537118876014220 1 Bool.false 66980602 Bool.true Bool.false 19138446 Bool.true Bool.true 92486124 

noncomputable def Ns78p1094 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 303713 1000 143 65 67108864 33554432 1125899906842624 Bool.false 29305211146 1202 

noncomputable def Ns78p1095 := Ns78p1094 46516304 61 47453136 16 73726608 61 38745320 8 Bool.true 67108856 1269 Bool.false 103351848 Bool.false 61548641 3537118876014220 1 Bool.false 67077172 Bool.false Bool.false 53275680 Bool.true Bool.true 50436858 

noncomputable def Ns78p1096 := nat_lit 27783123435130946905460884943518707487132110592291753657 

noncomputable def Ns78p1097 := nat_lit 63623286751143502041035163811881836375075614359552000 

noncomputable def Ns78p1098 := nat_lit 1240398200708741177234071900640000 

noncomputable def Ns78p1099 := nat_lit 2260353211310342020149561073050457920 

noncomputable abbrev qz886 := (@Eq.refl Real (Enclosure.sfrac Bool.false 303713 1000))

noncomputable abbrev qz715 := qz886

noncomputable abbrev qz492 := qz715

noncomputable abbrev qz155 := qz492

noncomputable def Ns78p1100 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz152 303713 1000 368967345476 16000000 607426 4000 2000 Ns78p1098 Ns78p1099 qz155 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns78p1101 := nat_lit 8890599499241903009747483181925986395882275389533361170240 

noncomputable abbrev qz493 := (Enclosure.sfrac Bool.false 303713 2000)

noncomputable abbrev qz716 := (Real.log (Enclosure.sfrac Bool.false 368967345476 16000000))

noncomputable abbrev qz156 := (@HSub.hSub Real Real Real qz339 (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 303713 4000) qz716) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 607426)))))) qz493)

noncomputable abbrev qz494 := (@HSub.hSub Real Real Real qz12 qz156 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 303713 2000) (Real.log Real.pi)))

noncomputable def Ns78p1102 := @Enclosure.Real.IsNear.addLit_ft_p qz494 (Enclosure.sfrac Bool.true Ns78p1098 Ns78p1099) 3933283801517774725697 9007199254740992000 20197519835374680153497 Ns78p320 Ns78p1098 Ns78p1099 0 1 Ns78p1101 

noncomputable def Ns78p1103 := nat_lit 263958207709459337649437278208000 

noncomputable abbrev qz495 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 303713 2000) (Real.log Real.pi))

noncomputable def Ns78p1104 := @Enclosure.Real.IsNear.subLit_ff_p qz156 qz495 5499047342202048078401 9007199254740992000 19482064845118374781 Ns78p194 11665847455593 67108864000 303713 33554432000 Ns78p1103 3933283801517774725697 9007199254740992000 

noncomputable def Ns78p1105 := nat_lit 10998094684404096156802000 

noncomputable abbrev qz157 := (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 303713 4000) qz716) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 607426))))))

noncomputable def Ns78p1106 := @Enclosure.Real.IsNear.subLit_ff_p qz157 qz493 6866849095829623530049 9007199254740992000 19482064845118374781 Ns78p194 303713 2000 0 1 Ns78p1105 5499047342202048078401 9007199254740992000 19482064845118374781 Ns78p194 

noncomputable def Ns78p1107 := nat_lit 15462769514593859954043795945556017152 

noncomputable def Ns78p1108 := nat_lit 12144717291161380062232576 

noncomputable def Ns78p1109 := nat_lit 23783715920716618703845382935355259123522163279720405685292076138637975776843411745099648712376320 

noncomputable def Ns78p1110 := nat_lit 231118308658323012677623484719721955904390791533687050617437400256631655397669548998978129362944 

noncomputable def Ns78p1111 := nat_lit 1780404564966317943475823755103460641728449359645071755693951758844894464535245841714708480 

noncomputable def Ns78p1112 := BSN.log_dyadic_bound 106823345476 631111345476 5 4 Ns78p1109 33554432 8823528 Ns78p1110 Ns78p1111 11469380 737934690952 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 106823345476) (BSN.artanhQ 631111345476) 0 4 Ns78p1110 Ns78p1109 Ns78p1111 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns78p1113 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 303713 4000) qz716 303713 4000 0 1 22621298751163073 2251799813685248 62500007720587 551470500000000000000 6870382507611990390049 9007199254740992000 18982064844842639531 Ns78p194 (Enclosure.Real.IsNear.const Bool.false 303713 4000) (BSN.isNear_log_sfrac 368967345476 16000000 22621298751163073 2251799813685248 62500007720587 551470500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 368967345476) qz347)) Bool.false Ns78p1108 Ns78p84 1000000123529392 8823528000000000000000 22621298751163073 2251799813685248 62500007720587 551470500000000000000 (BSN.log_rat_reduce_isNear 368967345476 16000000 14 737934690952 524288000000 11469380 33554432 24973259072661432 36028797018963968 8823528 1000000000000000 rfl rfl rfl rfl (Ns78p1112 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns78p1114 := BSN.arctan_dyadic_bound_f 1000 607426 1 0 4194304 1102941 0 1 1 0 1 1 6905 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 607426) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 607426) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz496 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 607426)))

noncomputable def Ns78p1115 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz496 884279719003555 562949953421312 1 2000000000000000 6905 4194304 1 1102941 3705050793107112591360 883352945591715 562949953421312 2000000001102941 2205882000000000000000 qz17 (Ns78p1114 rfl) rfl rfl 

noncomputable def Ns78p1116 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 303713 4000) qz716) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz496)) 6870382507611990390049 9007199254740992000 18982064844842639531 Ns78p194 883352945591715 2251799813685248 2000000001102941 8823528000000000000000 Ns78p1107 6866849095829623530049 9007199254740992000 19482064845118374781 Ns78p194 (Ns78p1113 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz496) 1 4 0 1 883352945591715 562949953421312 2000000001102941 2205882000000000000000 883352945591715 2251799813685248 2000000001102941 8823528000000000000000 qz350 Ns78p1115 rfl) 

noncomputable def Ns78p1117 := @Ns78p1102 Ns78p1096 Ns78p1097 20197519835374680153497 Ns78p320 (@Ns78p1104 20197519835374680153497 Ns78p320 (Ns78p1106 (Ns78p1116 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 303713 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz493 (Real.log Real.pi) 303713 2000 0 1 38410761 33554432 1 16777216 11665847455593 67108864000 303713 33554432000 (Enclosure.Real.IsNear.const Bool.false 303713 2000) RS079to096.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns78p1098 Ns78p1099) 

noncomputable def Ns78p1118 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns78p1096 Ns78p1097 20197519835374680153497 Ns78p320 3663151393 8388608 151 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz351 qz494 (Enclosure.sfrac Bool.true Ns78p1098 Ns78p1099)) Bool.false Ns78p1096 Ns78p1097 20197519835374680153497 Ns78p320 Ns78p1100 (Ns78p1117 rfl rfl)) 

noncomputable def Ns78p1119 := nat_lit 1899334353895554249916416 

noncomputable def Ns78p1120 := nat_lit 140094734308897514969136291523682903927622658483680602941587269401505441652808963375360 

noncomputable def Ns78p1121 := nat_lit 281691008006634141808546955667846088234590107997026293503929745868775307693564150016 

noncomputable def Ns78p1122 := nat_lit 366458709177006560118143116062373949953298578710977822276579343129679091925852943073536 

noncomputable def Ns78p1123 := BSN.sin_dyadic_bound_f 26991164558 17179869184 3 2 8388608 2208037 Ns78p1120 Ns78p97 Ns78p1121 Ns78p1122 Ns78p100 Ns78p1121 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26991164558) qz352 0 2 Ns78p1120 Ns78p97 Ns78p1121 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26991164558) qz353 0 2 Ns78p1122 Ns78p100 Ns78p1121 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1124 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz152) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3663151393) qz354) Bool.false 3663151393 8388608 151 8388608 Bool.true 8388607 8388608 1 1102941 (Ns78p1118 rfl) (Enclosure.sfrac_false_div 3663151393 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3663151393) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns78p1119) qz355) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 69 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q1 3663151393 8388608 226375608064910080 72057594037927936 69 Ns78p1119 Ns78p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns78p1119 Ns78p84 26991164558 17179869184 2208037 2205882 (Ns78p1123 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p1125 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns78p1096 Ns78p1097 20197519835374680153497 Ns78p320 29305211146 67108864 1202 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz351 qz494 (Enclosure.sfrac Bool.true Ns78p1098 Ns78p1099)) Bool.false Ns78p1096 Ns78p1097 20197519835374680153497 Ns78p320 Ns78p1100 (Ns78p1117 rfl rfl)) 

noncomputable def Ns78p1126 := Ns78p1095 26639 BSN.abs_quadSignPos (BSN.cos_quad_nat3 143 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 67077172 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 65 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 53275680 67108864) qz155 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) Bool.true 8388607 8388608 174932699 9252139696128 67108856 67108864 1269 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.true 8388607 8388608 174932699 9252139696128 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz152) qz152) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.true 8388607 8388608 174932699 9252139696128 8388607 8388608 174932699 9252139696128 (Ns78p1124 rfl rfl) rfl)) rfl) (Ns78p1125 rfl) RS079to096.d7 

noncomputable def Ns78p1127 := nat_lit 2440161469422265996139072145761715232776871713152139723123303783347284776609175867932320333034732650496 

noncomputable def Ns78p1128 := nat_lit 1485316337718166155378321786910494882105231098255204262231145241425559194812301589961952771178496 

noncomputable def Ns78p1129 := nat_lit 12186796859778143289244890389311442122841247235395278052883416744426650734740372564899490972866923462656 

noncomputable def Ns78p1130 := BSN.sin_dyadic_bound_f 103351848 67108864 4 3 67108864 33554432 Ns78p1127 Ns78p941 Ns78p1128 Ns78p1129 Ns78p944 Ns78p1128 67077172 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 103351848) qz356 0 3 Ns78p1127 Ns78p941 Ns78p1128 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 103351848) (BSN.sinOddQ 67108864) 0 3 Ns78p1129 Ns78p944 Ns78p1128 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1131 := nat_lit 880393467026229922676287968998017156052904784716229707023452287745 

noncomputable def Ns78p1132 := nat_lit 205943336678421848172820381349881741387711685053740462024241921 

noncomputable def Ns78p1133 := nat_lit 2305458981571218066874188685805954647795360998195276510027669123841 

noncomputable def Ns78p1134 := BSN.sin_dyadic_bound_f 61548641 67108864 3 2 67108864 33554432 Ns78p1131 Ns78p127 Ns78p1132 Ns78p1133 Ns78p130 Ns78p1132 53275680 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 61548641) qz356 0 2 Ns78p1131 Ns78p127 Ns78p1132 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 61548641) (BSN.sinOddQ 67108864) 0 2 Ns78p1133 Ns78p130 Ns78p1132 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1135 := nat_lit 2248603738295296916146163605572722698800201842317821315858544600423776978788054353185987658820079266401 

noncomputable def Ns78p1136 := nat_lit 1162764508866393015749569517807893910121995764743032678527634833444706881328369013527548933384801 

noncomputable def Ns78p1137 := nat_lit 11231118498200847445432827760495725415122698063606262752587942205405144852095318499343433534316738456161 

noncomputable def Ns78p1138 := BSN.sin_dyadic_bound_f 101264599 67108864 4 3 67108864 33554432 Ns78p1135 Ns78p941 Ns78p1136 Ns78p1137 Ns78p944 Ns78p1136 66980602 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 101264599) qz356 0 3 Ns78p1135 Ns78p941 Ns78p1136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 101264599) (BSN.sinOddQ 67108864) 0 3 Ns78p1137 Ns78p944 Ns78p1136 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1139 := nat_lit 141876281489612079073380116401 

noncomputable def Ns78p1140 := BSN.sin_dyadic_bound_f 19407851 67108864 2 1 67108864 33554432 Ns78p1139 Ns78p106 Ns78p1139 Ns78p1139 Ns78p107 Ns78p1139 19138446 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 19407851) qz356 0 1 Ns78p1139 Ns78p106 Ns78p1139 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 19407851) (BSN.sinOddQ 67108864) 0 1 Ns78p1139 Ns78p107 Ns78p1139 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1141 := Ns78p1093 45346 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 9 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66980602 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 33 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 19138446 67108864) qz155 rfl rfl (Ns78p1126 RS079to096.d9 RS079to096.d11 RS079to096.d13 RS079to096.d17 (Ns78p1130 rfl rfl) (Ns78p1134 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns78p1125 rfl) RS079to096.d19 RS079to096.d21 RS079to096.d23 RS079to096.d25 RS079to096.d17 (Ns78p1138 rfl rfl) (Ns78p1140 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns78p1142 := nat_lit 151959662748896656250638961912399103996347359475396843375185112161 

noncomputable def Ns78p1143 := nat_lit 19883156121443681378568318409232170145728996388054299247914081 

noncomputable def Ns78p1144 := nat_lit 455839221934447081389159749100378847648750620433414421527059508321 

noncomputable def Ns78p1145 := BSN.cos_dyadic_bound_f 45952661 67108864 3 2 67108864 33554432 Ns78p1142 Ns78p116 Ns78p1143 Ns78p1144 Ns78p119 Ns78p1143 51981079 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 45952661) qz357 0 2 Ns78p1142 Ns78p116 Ns78p1143 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 45952661) (BSN.cosOddQ 67108864) 0 2 Ns78p1144 Ns78p119 Ns78p1143 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1146 := Ns78p1091 Bool.true 92486124 45346 Bool.true 45952661 3537118876014220 1 Bool.false 51981079 Bool.false Bool.true 71264937 53535 BSN.abs_quadSignPos qz689 (BSN.sfrac_eq_quadSignPos_mul Bool.false 51981079 67108864) qz155 rfl (Ns78p1141 rfl rfl) (Ns78p1125 rfl) RS079to096.d27 RS079to096.d29 RS079to096.d17 (Ns78p1145 rfl rfl) rfl 

noncomputable def Ns78p1147 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 6) 71264937 67108864 53535 67108864 71264937 67108864 53535 67108864 9565017930203136 71264937 33554432 53535 33554432 (Ns78p1146 rfl rfl rfl rfl) 

noncomputable def Ns78p1148 := @Enclosure.Real.IsNear.mulLit_ff qz714 (Zeta.RiemannSiegel.correction qz154) 3181405 8388608 1 8388608 7173679258595 8796093022208 1340139083321257 19403143268014227456 22822379061690425975 73786976294838206464 

noncomputable abbrev qz717 := (@HPow.hPow Real Real Real qz7 qz153 qz9)

noncomputable def Ns78p1149 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz717 1 1 0 1 3181405 8388608 1 8388608 3181405 8388608 1 8388608 

noncomputable def Ns78p1150 := @Enclosure.Real.IsNear.sqrt_image qz153 405483885457 8388608000 303713 8388608000 29160944 29160967 4194304 (@Enclosure.Real.IsNear.of_eq qz153 (@HMul.hMul Real Real Real qz5 qz152 qz3) Bool.false 405483885457 8388608000 303713 8388608000 (BSN.t_div_two_pi_mk qz152 303713 1000 qz155) (@Enclosure.Real.IsNear.mulLit_ff qz152 qz3 303713 1000 0 1 1335089 8388608 1 8388608 405483885457 8388608000 303713 8388608000 (Enclosure.Real.IsNear.const Bool.false 303713 1000) RS079to096.d32 rfl)) 

noncomputable abbrev qz887 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 303713 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz718 := qz887

noncomputable abbrev qz497 := qz718

noncomputable abbrev qz158 := qz497

noncomputable def Ns78p1151 := @Enclosure.Real.IsNear.sqrt_image qz158 58321911 8388608 23 8388608 11059379 11059384 4194304 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 58321911 8388608 23 8388608 58321911 8388608 23 8388608 (Ns78p1150 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns78p1152 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz158) 22118763 8388608 5 8388608 1590702 1590703 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz158) Bool.false 22118763 8388608 5 8388608 22118763 8388608 5 8388608 (Ns78p1151 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns78p1153 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz158)) Bool.false 3181405 8388608 1 8388608 3181405 8388608 1 8388608 (Ns78p1152 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz336 qz334 qz491)

noncomputable abbrev qz719 := (@HMul.hMul Real Real Real qz841 qz885 qz885)

noncomputable abbrev qz498 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz719 qz713) qz640)

noncomputable abbrev qz160 := (Real.cos (@HMul.hMul Real Real Real qz336 qz334 qz498))

noncomputable def Ns78p1154 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz154) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz159)) qz160) Bool.false 7173679258595 

noncomputable def Ns78p1155 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz159)) qz160 2194091 2097152 21 

noncomputable def Ns78p1156 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz159)) Bool.false 8776364 8388608 168 8388608 2194091 2097152 21 

noncomputable def Ns78p1157 := @Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.false 8017983 8388608 168315053 9252139696128 8017983 8388608 168315053 9252139696128 

noncomputable def Ns78p1158 := @Enclosure.Real.IsNear.cos_image qz159 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50204303) qz354) Bool.false 50204303 8388608 145 8388608 Bool.false 8017983 8388608 1 

noncomputable def Ns78p1159 := nat_lit 620679734476648882011763937 

noncomputable def Ns78p1160 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz154 884279719003555 140737488355328 1 500000000000000 7990263 8388608 23 8388608 7065627520404502384965 1180591620717411303424 Ns78p1159 

noncomputable def Ns78p1161 := @Enclosure.Real.IsNear.subLit_ff_p qz158 qz1 58321911 8388608 23 8388608 6 1 0 1 7990263 7990263 8388608 23 

noncomputable def Ns78p1162 := @Ns78p1161 8388608 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 58321911 8388608 23 8388608 58321911 8388608 23 8388608 (Ns78p1150 rfl rfl rfl rfl rfl rfl) rfl) qz362 

noncomputable def Ns78p1163 := @Enclosure.Real.IsNear.recentre' qz159 Bool.false 7065627520404502384965 1180591620717411303424 Ns78p1159 Ns78p385 50204303 8388608 145 8388608 (@Ns78p1160 Ns78p385 RS079to096.d31 (Ns78p1162 rfl rfl) rfl) 

noncomputable def Ns78p1164 := nat_lit 1538273858607747533111296 

noncomputable def Ns78p1165 := nat_lit 60207826260428630628065254928127505608381255302309272736499439576797001576055375462400 

noncomputable def Ns78p1166 := nat_lit 52147185461278023720382552490874489302774747662930947807783753848669276999159709696 

noncomputable def Ns78p1167 := nat_lit 157602735238947201511290286393443955991651176200308111822952596623475253869765439062016 

noncomputable def Ns78p1168 := BSN.sin_dyadic_bound_f 21860186316 17179869184 3 2 8388608 2208037 Ns78p1165 Ns78p97 Ns78p1166 Ns78p1167 Ns78p100 Ns78p1166 8017983 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 21860186316) qz352 0 2 Ns78p1165 Ns78p97 Ns78p1166 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 21860186316) qz353 0 2 Ns78p1167 Ns78p100 Ns78p1166 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1169 := @Ns78p1158 1102941 (Ns78p1163 rfl) (Enclosure.sfrac_false_div 50204303 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 50204303) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns78p1164) qz355) 226375608064910080 72057594037927936 Bool.false 8017983 8388608 0 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q3 50204303 8388608 226375608064910080 72057594037927936 0 Ns78p1164 Ns78p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8017983 8388608 Ns78p1164 Ns78p84 21860186316 17179869184 2208037 2205882 (Ns78p1168 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p1170 := @Enclosure.Real.IsNear.inv_image (Real.cos qz159) 8017983 8388608 168315053 9252139696128 4388098 4388266 4194304 (Ns78p1157 (Ns78p1169 rfl rfl) rfl) rfl 

noncomputable def Ns78p1171 := @Enclosure.Real.IsNear.recentre' qz160 Bool.false 3269545 4194304 

noncomputable abbrev qz161 := (@HMul.hMul Real Real Real qz336 qz334 qz498)

noncomputable def Ns78p1172 := @Enclosure.Real.IsNear.cos_image qz161 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 5678221)) qz354) Bool.true 5678221 8388608 

noncomputable def Ns78p1173 := nat_lit 6703660727619142057661857645 

noncomputable def Ns78p1174 := nat_lit 605017675782891665490002287983661 

noncomputable def Ns78p1175 := @Enclosure.Real.IsNear.recentre' qz161 Bool.true Ns78p1173 Ns78p397 Ns78p1174 

noncomputable def Ns78p1176 := nat_lit 12089258196146291747061760000000000000 

noncomputable abbrev qz162 := qz498

noncomputable def Ns78p1177 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz162 884279719003555 140737488355328 1 500000000000000 7580927825839 

noncomputable abbrev qz499 := (@HSub.hSub Real Real Real qz634 qz719 qz713)

noncomputable abbrev qz163 := qz499

noncomputable def Ns78p1178 := @Enclosure.Real.IsNear.subLit_tf qz163 qz26 3182881314735 70368744177664 560490611 70368744177664 1 16 

noncomputable abbrev qz500 := qz719

noncomputable abbrev qz164 := qz500

noncomputable def Ns78p1179 := @Enclosure.Real.IsNear.subLit_ff_n qz164 qz154 63844302809169 70368744177664 367552627 70368744177664 7990263 8388608 23 8388608 

noncomputable def Ns78p1180 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz154 7990263 8388608 23 8388608 7990263 8388608 23 8388608 63844302809169 70368744177664 

noncomputable def Ns78p1181 := nat_lit 8649127836967414206143305142438714486020443040415994692641 

noncomputable def Ns78p1182 := nat_lit 1080683031307010246470733670725321464739632433132028961 

noncomputable def Ns78p1183 := nat_lit 25945222144839628597936973959974692815131849856381720020001 

noncomputable def Ns78p1184 := BSN.cos_dyadic_bound_f 5678221 8388608 3 2 4194304 1102941 Ns78p1181 Ns78p501 Ns78p1182 Ns78p1183 Ns78p504 Ns78p1182 3269545 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 5678221) (BSN.cosEvenQ 8388608) 0 2 Ns78p1181 Ns78p501 Ns78p1182 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 5678221) (BSN.cosOddQ 8388608) 0 2 Ns78p1183 Ns78p504 Ns78p1182 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1185 := @Ns78p1171 472726769 9252139696128 3269545 4194304 472726769 9252139696128 (@Ns78p1172 421 8388608 Bool.false 3269545 4194304 1 1102941 (@Ns78p1175 Ns78p1176 5678221 8388608 421 8388608 (@Ns78p1177 70368744177664 560490611 70368744177664 Ns78p1173 Ns78p397 Ns78p1174 Ns78p1176 RS079to096.d31 (@Ns78p1178 0 1 121294845213424 7580927825839 70368744177664 560490611 70368744177664 (@Ns78p1179 26699943659836538880 3182881314735 70368744177664 560490611 70368744177664 (@Ns78p1180 367552627 70368744177664 (Ns78p1162 rfl rfl) (Ns78p1162 rfl rfl) rfl) (Ns78p1162 rfl rfl) rfl rfl) qz366 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 5678221 8388608) (BSN.cos_neg_of_bound 5678221 8388608 Bool.false 3269545 4194304 1 1102941 (Ns78p1184 rfl rfl)) rfl rfl) 

noncomputable def Ns78p1186 := @Ns78p1148 1069837702615763750783 Ns78p694 (Ns78p1149 qz28 (@Enclosure.Real.IsNear.of_eq qz717 (@Inv.inv Real Real.instInv (Real.sqrt qz158)) Bool.false 3181405 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz153 (BSN.t_div_two_pi_nonneg qz152 303713 1000 qz155)) Ns78p1153) rfl) (@Ns78p1154 8796093022208 1340139083321257 19403143268014227456 (BSN.correction_mk qz154 (BSN.cos_two_pi_p_ne_zero_mk qz152 303713 1000 6 qz155 rfl rfl (@BSN.floor_sqrt_eq_dec qz152 303713 1000 6 qz155 rfl rfl rfl))) (@Ns78p1155 1048576 3269545 4194304 472726769 9252139696128 7173679258595 8796093022208 1340139083321257 19403143268014227456 (@Ns78p1156 1048576 (Ns78p1170 rfl rfl rfl rfl rfl) rfl) (Ns78p1185 rfl) rfl)) 

noncomputable def Ns78p1187 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (hardyZApproximantRS₀ qz152) Bool.true 179535632830138606199 73786976294838206464 65991542380937117929343 Ns78p694 (@Eq.refl Real (hardyZApproximantRS₀ qz152)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 6) (@HMul.hMul Real Real Real qz5 qz714 (Zeta.RiemannSiegel.correction qz154))) Bool.true 179535632830138606199 73786976294838206464 65991542380937117929343 Ns78p694 (BSN.hardyZApproximantRS₀_eq qz152 6 (@BSN.floor_sqrt_eq_dec qz152 303713 1000 6 qz155 rfl rfl rfl)) (@Ns78p1090 179535632830138606199 73786976294838206464 65991542380937117929343 Ns78p694 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 6) (@HAdd.hAdd Real Real Real qz351 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 6)) Bool.true 71264937 33554432 53535 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz152) qz152 6) (Ns78p1147 (Ns78p1146 rfl rfl rfl rfl) rfl rfl)) (Ns78p1186 rfl) rfl rfl)) 

theorem RS079to096.d45 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz152) Bool.true 179535632830138606199 73786976294838206464 65991542380937117929343 Ns78p694 := Ns78p1187 

noncomputable def Ns78p1188 := nat_lit 81382681421605146275610624 

noncomputable def Ns78p1189 := nat_lit 78973374454522848556875776 

noncomputable abbrev qz888 := (Enclosure.sfrac Bool.false 305332 1000)

noncomputable abbrev qz720 := qz888

noncomputable abbrev qz501 := qz720

noncomputable abbrev qz165 := qz501

noncomputable abbrev qz889 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 305332 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz721 := qz889

noncomputable abbrev qz502 := qz721

noncomputable abbrev qz166 := qz502

noncomputable abbrev qz890 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 305332 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz722 := qz890

noncomputable abbrev qz503 := qz722

noncomputable abbrev qz167 := qz503

noncomputable abbrev qz723 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz166 qz9))

noncomputable def Ns78p1190 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz165) qz165 6) (@HMul.hMul Real Real Real qz5 qz723 (Zeta.RiemannSiegel.correction qz167)) 3500923 4194304 26909 16777216 11965724647284526965 36893488147419103232 2128725280010660100925 Ns78p1188 Ns78p1189 

noncomputable def Ns78p1191 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz165) qz165 Real.cos BSN.quadSignPos 5 6 305332 1000 68 67108864 33554432 1125899906842624 Bool.false 29516037675 1207 120242927 62 27397080 8 

noncomputable def Ns78p1192 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz165) qz165 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 305332 1000 10 32 67108864 33554432 1125899906842624 Bool.false 29516037675 1207 

noncomputable def Ns78p1193 := Ns78p1192 93032624 61 33554424 8 108007536 61 30011992 8 Bool.false 18451897 26780 Bool.false 56056953 Bool.true 88859880 3537118876014220 1 Bool.false 45026364 Bool.true Bool.false 16387093 Bool.false Bool.false 3267250 

noncomputable def Ns78p1194 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz165) qz165 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 305332 1000 145 66 67108864 33554432 1125899906842624 Bool.false 29516037675 1207 

noncomputable def Ns78p1195 := Ns78p1194 46516304 61 47453136 16 73726608 61 38745320 8 Bool.false 67108856 1277 Bool.false 28039767 Bool.false 47597434 3537118876014220 1 Bool.false 27231005 Bool.true Bool.false 50925290 Bool.true Bool.false 18451897 

noncomputable def Ns78p1196 := nat_lit 220413378093713693626420116020039938262862284818789 

noncomputable def Ns78p1197 := nat_lit 501140823068505387931272876148810717725720576000 

noncomputable def Ns78p1198 := nat_lit 1273813361388915501693960847360000 

noncomputable def Ns78p1199 := nat_lit 2333618807925402130611580219812741120 

noncomputable abbrev qz891 := (@Eq.refl Real (Enclosure.sfrac Bool.false 305332 1000))

noncomputable abbrev qz724 := qz891

noncomputable abbrev qz504 := qz724

noncomputable abbrev qz168 := qz504

noncomputable def Ns78p1200 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz165 305332 1000 372911520896 16000000 610664 4000 2000 Ns78p1198 Ns78p1199 qz168 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns78p1201 := nat_lit 2311201783479939300080170995758293983039190831661464944640 

noncomputable abbrev qz505 := (Enclosure.sfrac Bool.false 305332 2000)

noncomputable abbrev qz725 := (Real.log (Enclosure.sfrac Bool.false 372911520896 16000000))

noncomputable abbrev qz169 := (@HSub.hSub Real Real Real qz339 (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 305332 4000) qz725) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 610664)))))) qz505)

noncomputable abbrev qz506 := (@HSub.hSub Real Real Real qz12 qz169 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 305332 2000) (Real.log Real.pi)))

noncomputable def Ns78p1202 := @Enclosure.Real.IsNear.addLit_ft_p qz506 (Enclosure.sfrac Bool.true Ns78p1198 Ns78p1199) 990395108234193881397 2251799813685248000 1691985158788723036759 Ns78p999 Ns78p1198 Ns78p1199 0 1 Ns78p1201 

noncomputable def Ns78p1203 := nat_lit 16616072656188449334075850752000 

noncomputable abbrev qz507 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 305332 2000) (Real.log Real.pi))

noncomputable def Ns78p1204 := @Enclosure.Real.IsNear.subLit_ff_p qz169 qz507 1383922643608223435061 2251799813685248000 3263875392936334189 367647000000000000000000 2932008619413 16777216000 76333 8388608000 Ns78p1203 990395108234193881397 2251799813685248000 

noncomputable def Ns78p1205 := nat_lit 2767845287216446870122000 

noncomputable abbrev qz170 := (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 305332 4000) qz725) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 610664))))))

noncomputable def Ns78p1206 := @Enclosure.Real.IsNear.subLit_ff_p qz170 qz505 1727695913964295506229 2251799813685248000 3263875392936334189 367647000000000000000000 305332 2000 0 1 Ns78p1205 1383922643608223435061 2251799813685248000 3263875392936334189 367647000000000000000000 

noncomputable def Ns78p1207 := nat_lit 3890425337169564879255408102229409792 

noncomputable def Ns78p1208 := nat_lit 12157571825505791121555456 

noncomputable def Ns78p1209 := nat_lit 24999157693883028567031619891765510764604001019344860793130162081338743811565265867415917973995520 

noncomputable def Ns78p1210 := nat_lit 258246700483362161272108310073924940262881432248984593368115547014858428792594027747501443907584 

noncomputable def Ns78p1211 := nat_lit 2379516855857510131795323995769941334389278216935477061154716934372002219370617609943777280 

noncomputable def Ns78p1212 := BSN.log_dyadic_bound 110767520896 635055520896 5 4 Ns78p1209 33554432 8823528 Ns78p1210 Ns78p1211 11826165 745823041792 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 110767520896) (BSN.artanhQ 635055520896) 0 4 Ns78p1210 Ns78p1209 Ns78p1211 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns78p1213 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 305332 4000) qz725 305332 4000 0 1 22645242187205313 2251799813685248 62500007720587 551470500000000000000 1728579271875943157229 2251799813685248000 4770813089335567471 551470500000000000000000 (Enclosure.Real.IsNear.const Bool.false 305332 4000) (BSN.isNear_log_sfrac 372911520896 16000000 22645242187205313 2251799813685248 62500007720587 551470500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 372911520896) qz347)) Bool.false Ns78p1208 Ns78p84 1000000123529392 8823528000000000000000 22645242187205313 2251799813685248 62500007720587 551470500000000000000 (BSN.log_rat_reduce_isNear 372911520896 16000000 14 745823041792 524288000000 11826165 33554432 24973259072661432 36028797018963968 8823528 1000000000000000 rfl rfl rfl rfl (Ns78p1212 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns78p1214 := BSN.arctan_dyadic_bound_f 1000 610664 1 0 4194304 1102941 0 1 1 0 1 1 6868 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 610664) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 610664) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz508 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 610664)))

noncomputable def Ns78p1215 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz508 884279719003555 562949953421312 1 2000000000000000 6868 4194304 1 1102941 3705071622255389179904 883357911647651 562949953421312 2000000001102941 2205882000000000000000 qz17 (Ns78p1214 rfl) rfl rfl 

noncomputable def Ns78p1216 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 305332 4000) qz725) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz508)) 1728579271875943157229 2251799813685248000 4770813089335567471 551470500000000000000000 883357911647651 2251799813685248 2000000001102941 8823528000000000000000 Ns78p1207 1727695913964295506229 2251799813685248000 3263875392936334189 367647000000000000000000 (Ns78p1213 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz508) 1 4 0 1 883357911647651 562949953421312 2000000001102941 2205882000000000000000 883357911647651 2251799813685248 2000000001102941 8823528000000000000000 qz350 Ns78p1215 rfl) 

noncomputable def Ns78p1217 := @Ns78p1202 Ns78p1196 Ns78p1197 1691985158788723036759 Ns78p999 (@Ns78p1204 1691985158788723036759 Ns78p999 (Ns78p1206 (Ns78p1216 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 305332 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz505 (Real.log Real.pi) 305332 2000 0 1 38410761 33554432 1 16777216 2932008619413 16777216000 76333 8388608000 (Enclosure.Real.IsNear.const Bool.false 305332 2000) RS079to096.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns78p1198 Ns78p1199) 

noncomputable def Ns78p1218 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz165) Bool.false Ns78p1196 Ns78p1197 1691985158788723036759 Ns78p999 3689504709 8388608 19 1048576 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz165) (@HAdd.hAdd Real Real Real qz351 qz506 (Enclosure.sfrac Bool.true Ns78p1198 Ns78p1199)) Bool.false Ns78p1196 Ns78p1197 1691985158788723036759 Ns78p999 Ns78p1200 (Ns78p1217 rfl rfl)) 

noncomputable def Ns78p1219 := nat_lit 1899294972021677582450688 

noncomputable def Ns78p1220 := nat_lit 140083092097638852582491768455295901340137307930366897444768190741132918172825497436160 

noncomputable def Ns78p1221 := nat_lit 281644285477987039226517782791959353774263283842697800906466735677944982166915055616 

noncomputable def Ns78p1222 := nat_lit 366428293317327872985873602877445140746629856405691792106258601035679065243415583195136 

noncomputable def Ns78p1223 := BSN.sin_dyadic_bound_f 26990604908 17179869184 3 2 8388608 2208037 Ns78p1220 Ns78p97 Ns78p1221 Ns78p1222 Ns78p100 Ns78p1221 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26990604908) qz352 0 2 Ns78p1220 Ns78p97 Ns78p1221 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26990604908) qz353 0 2 Ns78p1222 Ns78p100 Ns78p1221 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1224 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz165) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3689504709) qz354) Bool.false 3689504709 8388608 19 1048576 Bool.false 8388607 8388608 1 1102941 (Ns78p1218 rfl) (Enclosure.sfrac_false_div 3689504709 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3689504709) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns78p1219) qz355) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 69 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q3 3689504709 8388608 226375608064910080 72057594037927936 69 Ns78p1219 Ns78p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns78p1219 Ns78p84 26990604908 17179869184 2208037 2205882 (Ns78p1223 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p1225 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz165) Bool.false Ns78p1196 Ns78p1197 1691985158788723036759 Ns78p999 29516037675 67108864 1207 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz165) (@HAdd.hAdd Real Real Real qz351 qz506 (Enclosure.sfrac Bool.true Ns78p1198 Ns78p1199)) Bool.false Ns78p1196 Ns78p1197 1691985158788723036759 Ns78p999 Ns78p1200 (Ns78p1217 rfl rfl)) 

noncomputable def Ns78p1226 := Ns78p1195 26780 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 145 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 27231005 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 66 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 50925290 67108864) qz168 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz165) qz165 1) Bool.false 8388607 8388608 22004455 1156517462016 67108856 67108864 1277 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz165) qz165 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz165)) Bool.false 8388607 8388608 22004455 1156517462016 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz165) qz165) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz165)) Bool.false 8388607 8388608 22004455 1156517462016 8388607 8388608 22004455 1156517462016 (Ns78p1224 rfl rfl) rfl)) rfl) (Ns78p1225 rfl) RS079to096.d7 

noncomputable def Ns78p1227 := nat_lit 618155306754783754587709375521 

noncomputable def Ns78p1228 := BSN.sin_dyadic_bound_f 28039767 67108864 2 1 67108864 33554432 Ns78p1227 Ns78p106 Ns78p1227 Ns78p1227 Ns78p107 Ns78p1227 27231005 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 28039767) qz356 0 1 Ns78p1227 Ns78p106 Ns78p1227 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 28039767) (BSN.sinOddQ 67108864) 0 1 Ns78p1227 Ns78p107 Ns78p1227 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1229 := nat_lit 174915543572616331325053252380554394588899156703889813636509573376 

noncomputable def Ns78p1230 := nat_lit 26343187478417757071373795655480453020661019836337401302589696 

noncomputable def Ns78p1231 := nat_lit 524693944342892158461017009550352222860656148071996766106923540736 

noncomputable def Ns78p1232 := BSN.cos_dyadic_bound_f 47597434 67108864 3 2 67108864 33554432 Ns78p1229 Ns78p116 Ns78p1230 Ns78p1231 Ns78p119 Ns78p1230 50925290 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 47597434) qz357 0 2 Ns78p1229 Ns78p116 Ns78p1230 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 47597434) (BSN.cosOddQ 67108864) 0 2 Ns78p1231 Ns78p119 Ns78p1230 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1233 := nat_lit 336567843130798319017755034058576875900154979700126642314901519041 

noncomputable def Ns78p1234 := nat_lit 97507024183010024865016941350944634996747890246114362719533761 

noncomputable def Ns78p1235 := nat_lit 1009508515344028937003535068293028738430471443319887698219265489601 

noncomputable def Ns78p1236 := BSN.cos_dyadic_bound_f 56056953 67108864 3 2 67108864 33554432 Ns78p1233 Ns78p116 Ns78p1234 Ns78p1235 Ns78p119 Ns78p1234 45026364 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 56056953) qz357 0 2 Ns78p1233 Ns78p116 Ns78p1234 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 56056953) (BSN.cosOddQ 67108864) 0 2 Ns78p1235 Ns78p119 Ns78p1234 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1237 := nat_lit 512839943660004048209792685651542678803204901577552792609836669455386977557983357470446341586944000000 

noncomputable def Ns78p1238 := nat_lit 242364311105000407808746244308411782121812605152460529614633598502134786961761632256000000000000 

noncomputable def Ns78p1239 := nat_lit 3107439496013730064299681042631593671071998354624660763293302566243587479914473820709425379907993600000 

noncomputable def Ns78p1240 := BSN.cos_dyadic_bound_f 88859880 67108864 4 3 67108864 33554432 Ns78p1237 Ns78p110 Ns78p1238 Ns78p1239 Ns78p113 Ns78p1238 16387093 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 88859880) qz357 0 3 Ns78p1237 Ns78p110 Ns78p1238 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 88859880) (BSN.cosOddQ 67108864) 0 3 Ns78p1239 Ns78p113 Ns78p1238 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1241 := Ns78p1193 45586 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 10 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 45026364 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 32 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 16387093 67108864) qz168 rfl rfl (Ns78p1226 RS079to096.d9 RS079to096.d11 RS079to096.d13 RS079to096.d17 (Ns78p1228 rfl rfl) (Ns78p1232 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns78p1225 rfl) RS079to096.d19 RS079to096.d21 RS079to096.d23 RS079to096.d25 RS079to096.d17 (Ns78p1236 rfl rfl) (Ns78p1240 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns78p1242 := nat_lit 26870191867570890414534874254555591672442131874894341190144317121 

noncomputable def Ns78p1243 := nat_lit 621818691827473664243659936692653047723042296826287334184641 

noncomputable def Ns78p1244 := nat_lit 80609331965329016296276135443793389711230949540089370995764582081 

noncomputable def Ns78p1245 := BSN.cos_dyadic_bound_f 29799431 67108864 3 2 67108864 33554432 Ns78p1242 Ns78p116 Ns78p1243 Ns78p1244 Ns78p119 Ns78p1243 60600703 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 29799431) qz357 0 2 Ns78p1242 Ns78p116 Ns78p1243 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 29799431) (BSN.cosOddQ 67108864) 0 2 Ns78p1244 Ns78p119 Ns78p1243 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1246 := Ns78p1191 Bool.false 3267250 45586 Bool.true 29799431 3537118876014220 1 Bool.false 60600703 Bool.false Bool.false 28007384 53818 BSN.abs_quadSignPos qz689 (BSN.sfrac_eq_quadSignPos_mul Bool.false 60600703 67108864) qz168 rfl (Ns78p1241 rfl rfl) (Ns78p1225 rfl) RS079to096.d27 RS079to096.d29 RS079to096.d17 (Ns78p1245 rfl rfl) rfl 

noncomputable def Ns78p1247 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz165) qz165 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz165) qz165 6) 28007384 67108864 53818 67108864 28007384 67108864 53818 67108864 3759087447703552 3500923 4194304 26909 16777216 (Ns78p1246 rfl rfl rfl rfl) 

noncomputable def Ns78p1248 := @Enclosure.Real.IsNear.mulLit_ff qz723 (Zeta.RiemannSiegel.correction qz167) 794295 2097152 1 4194304 15064585131827 17592186044416 664774612036949 9701571634007113728 11965724647284526965 36893488147419103232 

noncomputable abbrev qz726 := (@HPow.hPow Real Real Real qz7 qz166 qz9)

noncomputable def Ns78p1249 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz726 1 1 0 1 794295 2097152 1 4194304 794295 2097152 1 4194304 

noncomputable def Ns78p1250 := @Enclosure.Real.IsNear.sqrt_image qz166 101911348637 2097152000 76333 2097152000 29238565 29238588 4194304 (@Enclosure.Real.IsNear.of_eq qz166 (@HMul.hMul Real Real Real qz5 qz165 qz3) Bool.false 101911348637 2097152000 76333 2097152000 (BSN.t_div_two_pi_mk qz165 305332 1000 qz168) (@Enclosure.Real.IsNear.mulLit_ff qz165 qz3 305332 1000 0 1 1335089 8388608 1 8388608 101911348637 2097152000 76333 2097152000 (Enclosure.Real.IsNear.const Bool.false 305332 1000) RS079to096.d32 rfl)) 

noncomputable abbrev qz892 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 305332 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz727 := qz892

noncomputable abbrev qz509 := qz727

noncomputable abbrev qz171 := qz509

noncomputable def Ns78p1251 := @Enclosure.Real.IsNear.sqrt_image qz171 58477153 8388608 23 8388608 11074088 11074093 4194304 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 58477153 8388608 23 8388608 58477153 8388608 23 8388608 (Ns78p1250 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns78p1252 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz171) 22148181 8388608 5 8388608 1588589 1588591 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz171) Bool.false 22148181 8388608 5 8388608 22148181 8388608 5 8388608 (Ns78p1251 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns78p1253 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz171)) Bool.false 3177180 8388608 2 8388608 794295 2097152 1 4194304 (Ns78p1252 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz336 qz334 qz503)

noncomputable abbrev qz728 := (@HMul.hMul Real Real Real qz841 qz890 qz890)

noncomputable abbrev qz510 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz728 qz722) qz640)

noncomputable abbrev qz173 := (Real.cos (@HMul.hMul Real Real Real qz336 qz334 qz510))

noncomputable def Ns78p1254 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz167) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz172)) qz173) Bool.false 15064585131827 

noncomputable def Ns78p1255 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz172)) qz173 8529623 8388608 159 

noncomputable def Ns78p1256 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz172)) Bool.false 8529623 8388608 159 8388608 8529623 8388608 159 

noncomputable def Ns78p1257 := @Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.false 8249925 8388608 168315053 9252139696128 8249925 8388608 168315053 9252139696128 

noncomputable def Ns78p1258 := @Enclosure.Real.IsNear.cos_image qz172 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51179717) qz354) Bool.false 51179717 8388608 145 8388608 Bool.false 8249925 8388608 1 

noncomputable def Ns78p1259 := nat_lit 620679734477982400637695201 

noncomputable def Ns78p1260 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz167 884279719003555 140737488355328 1 500000000000000 8145505 8388608 23 8388608 7202904872542052270275 1180591620717411303424 Ns78p1259 

noncomputable def Ns78p1261 := @Enclosure.Real.IsNear.subLit_ff_p qz171 qz1 58477153 8388608 23 8388608 6 1 0 1 8145505 8145505 8388608 23 

noncomputable def Ns78p1262 := @Ns78p1261 8388608 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 58477153 8388608 23 8388608 58477153 8388608 23 8388608 (Ns78p1250 rfl rfl rfl rfl rfl rfl) rfl) qz362 

noncomputable def Ns78p1263 := @Enclosure.Real.IsNear.recentre' qz172 Bool.false 7202904872542052270275 1180591620717411303424 Ns78p1259 Ns78p385 51179717 8388608 145 8388608 (@Ns78p1260 Ns78p385 RS079to096.d31 (Ns78p1262 rfl rfl) rfl) 

noncomputable def Ns78p1264 := nat_lit 1678845830669570412642304 

noncomputable def Ns78p1265 := nat_lit 85451376472183671158891599713884904616260108459669093503252970584500910228830593024000 

noncomputable def Ns78p1266 := nat_lit 104965874241483452820485275433279375434179561647370807037301111164156521214493392896 

noncomputable def Ns78p1267 := nat_lit 223631279345042451254435308804711345482359231437418549297125959255617559088780468617216 

noncomputable def Ns78p1268 := BSN.sin_dyadic_bound_f 23857834188 17179869184 3 2 8388608 2208037 Ns78p1265 Ns78p97 Ns78p1266 Ns78p1267 Ns78p100 Ns78p1266 8249925 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 23857834188) qz352 0 2 Ns78p1265 Ns78p97 Ns78p1266 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 23857834188) qz353 0 2 Ns78p1267 Ns78p100 Ns78p1266 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1269 := @Ns78p1258 1102941 (Ns78p1263 rfl) (Enclosure.sfrac_false_div 51179717 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 51179717) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns78p1264) qz355) 226375608064910080 72057594037927936 Bool.false 8249925 8388608 0 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q3 51179717 8388608 226375608064910080 72057594037927936 0 Ns78p1264 Ns78p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8249925 8388608 Ns78p1264 Ns78p84 23857834188 17179869184 2208037 2205882 (Ns78p1268 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p1270 := @Enclosure.Real.IsNear.inv_image (Real.cos qz172) 8249925 8388608 168315053 9252139696128 4264732 4264891 4194304 (Ns78p1257 (Ns78p1269 rfl rfl) rfl) rfl 

noncomputable def Ns78p1271 := @Enclosure.Real.IsNear.recentre' qz173 Bool.false 3532298 4194304 

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz336 qz334 qz510)

noncomputable def Ns78p1272 := @Enclosure.Real.IsNear.cos_image qz174 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 4777393)) qz354) Bool.true 4777393 8388608 

noncomputable def Ns78p1273 := nat_lit 5640151116233201088183638045 

noncomputable def Ns78p1274 := nat_lit 15318153021219898177501349224031929 

noncomputable def Ns78p1275 := @Enclosure.Real.IsNear.recentre' qz174 Bool.true Ns78p1273 Ns78p397 Ns78p1274 

noncomputable abbrev qz175 := qz510

noncomputable def Ns78p1276 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz175 884279719003555 140737488355328 1 500000000000000 6378243213119 

noncomputable abbrev qz511 := (@HSub.hSub Real Real Real qz634 qz728 qz722)

noncomputable abbrev qz176 := qz511

noncomputable def Ns78p1277 := @Enclosure.Real.IsNear.subLit_tf qz176 qz26 1980196702015 70368744177664 567631743 70368744177664 1 16 

noncomputable abbrev qz512 := qz728

noncomputable abbrev qz177 := qz512

noncomputable def Ns78p1278 := @Enclosure.Real.IsNear.subLit_ff_n qz177 qz167 66349251705025 70368744177664 374693759 70368744177664 8145505 8388608 23 8388608 

noncomputable def Ns78p1279 := @Enclosure.Real.IsNear.mulLit_ff qz167 qz167 8145505 8388608 23 8388608 8145505 8388608 23 8388608 66349251705025 70368744177664 

noncomputable def Ns78p1280 := nat_lit 4333711054704540814339042622686836518508793707883382532481 

noncomputable def Ns78p1281 := nat_lit 271348703588464878988212716917266392232117348813859201 

noncomputable def Ns78p1282 := nat_lit 13000590466706445513259151442626675022741916888952519879041 

noncomputable def Ns78p1283 := BSN.cos_dyadic_bound_f 4777393 8388608 3 2 4194304 1102941 Ns78p1280 Ns78p501 Ns78p1281 Ns78p1282 Ns78p504 Ns78p1281 3532298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 4777393) (BSN.cosEvenQ 8388608) 0 2 Ns78p1280 Ns78p501 Ns78p1281 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 4777393) (BSN.cosOddQ 8388608) 0 2 Ns78p1282 Ns78p504 Ns78p1281 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1284 := @Ns78p1271 239120737 4626069848064 1766149 2097152 239120737 4626069848064 (@Ns78p1272 213 4194304 Bool.false 3532298 4194304 1 1102941 (@Ns78p1275 Ns78p495 4777393 8388608 213 4194304 (@Ns78p1276 70368744177664 567631743 70368744177664 Ns78p1273 Ns78p397 Ns78p1274 Ns78p495 RS079to096.d31 (@Ns78p1277 0 1 102051891409904 6378243213119 70368744177664 567631743 70368744177664 (@Ns78p1278 16611093896096645120 1980196702015 70368744177664 567631743 70368744177664 (@Ns78p1279 374693759 70368744177664 (Ns78p1262 rfl rfl) (Ns78p1262 rfl rfl) rfl) (Ns78p1262 rfl rfl) rfl rfl) qz366 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 4777393 8388608) (BSN.cos_neg_of_bound 4777393 8388608 Bool.false 3532298 4194304 1 1102941 (Ns78p1283 rfl rfl)) rfl rfl) 

noncomputable def Ns78p1285 := @Ns78p1248 2128725280010660100925 Ns78p1188 (Ns78p1249 qz28 (@Enclosure.Real.IsNear.of_eq qz726 (@Inv.inv Real Real.instInv (Real.sqrt qz171)) Bool.false 794295 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz166 (BSN.t_div_two_pi_nonneg qz165 305332 1000 qz168)) Ns78p1253) rfl) (@Ns78p1254 17592186044416 664774612036949 9701571634007113728 (BSN.correction_mk qz167 (BSN.cos_two_pi_p_ne_zero_mk qz165 305332 1000 6 qz168 rfl rfl (@BSN.floor_sqrt_eq_dec qz165 305332 1000 6 qz168 rfl rfl rfl))) (@Ns78p1255 8388608 1766149 2097152 239120737 4626069848064 15064585131827 17592186044416 664774612036949 9701571634007113728 (@Ns78p1256 8388608 (Ns78p1270 rfl rfl rfl rfl rfl) rfl) (Ns78p1284 rfl) rfl)) 

noncomputable def Ns78p1286 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz165) (hardyZApproximantRS₀ qz165) Bool.false 18828719724302971019 36893488147419103232 132658520829759371754301 Ns78p1188 (@Eq.refl Real (hardyZApproximantRS₀ qz165)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz165) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz165) qz165 6) (@HMul.hMul Real Real Real qz5 qz723 (Zeta.RiemannSiegel.correction qz167))) Bool.false 18828719724302971019 36893488147419103232 132658520829759371754301 Ns78p1188 (BSN.hardyZApproximantRS₀_eq qz165 6 (@BSN.floor_sqrt_eq_dec qz165 305332 1000 6 qz168 rfl rfl rfl)) (@Ns78p1190 18828719724302971019 36893488147419103232 132658520829759371754301 Ns78p1188 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz165) qz165 6) (@HAdd.hAdd Real Real Real qz351 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz165) qz165 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz165) qz165 6)) Bool.false 3500923 4194304 26909 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz165) qz165 6) (Ns78p1247 (Ns78p1246 rfl rfl rfl rfl) rfl rfl)) (Ns78p1285 rfl) rfl rfl)) 

theorem RS079to096.d46 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz165) Bool.false 18828719724302971019 36893488147419103232 132658520829759371754301 Ns78p1188 := Ns78p1286 

noncomputable def Ns78p1287 := nat_lit 1937682890990598720847872 

noncomputable def Ns78p1288 := nat_lit 680166670699429624463491072 

noncomputable abbrev qz893 := (Enclosure.sfrac Bool.false 306949 1000)

noncomputable abbrev qz729 := qz893

noncomputable abbrev qz513 := qz729

noncomputable abbrev qz178 := qz513

noncomputable abbrev qz894 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 306949 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz730 := qz894

noncomputable abbrev qz514 := qz730

noncomputable abbrev qz179 := qz514

noncomputable abbrev qz895 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 306949 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz731 := qz895

noncomputable abbrev qz515 := qz731

noncomputable abbrev qz180 := qz515

noncomputable abbrev qz732 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz179 qz9))

noncomputable def Ns78p1289 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz178) qz178 6) (@HMul.hMul Real Real Real qz5 qz732 (Zeta.RiemannSiegel.correction qz180)) 12732221 16777216 27051 16777216 12542642721272052675 36893488147419103232 50976542383911374945 Ns78p1287 Ns78p1288 

noncomputable def Ns78p1290 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz178) qz178 Real.cos BSN.quadSignPos 5 6 306949 1000 68 67108864 33554432 1125899906842624 Bool.false 29726891452 1213 120242927 62 27397080 8 

noncomputable def Ns78p1291 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz178) qz178 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 306949 1000 11 32 67108864 33554432 1125899906842624 Bool.false 29726891452 1213 

noncomputable def Ns78p1292 := Ns78p1291 93032624 61 33554424 8 108007536 61 30011992 8 Bool.true 79063603 26922 Bool.false 11062620 Bool.true 52654289 3537118876014220 1 Bool.false 11012585 Bool.false Bool.false 47490516 Bool.false Bool.true 52318911 

noncomputable def Ns78p1293 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz178) qz178 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 306949 1000 146 67 67108864 33554432 1125899906842624 Bool.false 29726891452 1213 

noncomputable def Ns78p1294 := Ns78p1293 46516304 61 47453136 16 73726608 61 38745320 8 Bool.true 67108840 1285 Bool.false 58262323 Bool.false 33820929 3537118876014220 1 Bool.false 43367050 Bool.true Bool.false 32407321 Bool.false Bool.true 79063603 

noncomputable def Ns78p1295 := nat_lit 30033274384723995975822595475345453595276809290965613157 

noncomputable def Ns78p1296 := nat_lit 67800527660664899585246969637819711533543564771328000 

noncomputable def Ns78p1297 := nat_lit 1307902201872531503217380679520000 

noncomputable def Ns78p1298 := nat_lit 2408758620499359167341671992723906880 

noncomputable abbrev qz516 := (@Eq.refl Real qz729)

noncomputable abbrev qz181 := qz516

noncomputable def Ns78p1299 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz178 306949 1000 376871754404 16000000 613898 4000 2000 Ns78p1297 Ns78p1298 qz181 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns78p1300 := nat_lit 9610647803111678712263230552110545150488578973108996210240 

noncomputable abbrev qz517 := (Enclosure.sfrac Bool.false 306949 2000)

noncomputable abbrev qz733 := (Real.log (Enclosure.sfrac Bool.false 376871754404 16000000))

noncomputable abbrev qz182 := (@HSub.hSub Real Real Real qz339 (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 306949 4000) qz733) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 613898)))))) qz517)

noncomputable abbrev qz518 := (@HSub.hSub Real Real Real qz12 qz182 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 306949 2000) (Real.log Real.pi)))

noncomputable def Ns78p1301 := @Enclosure.Real.IsNear.addLit_ft_p qz518 (Enclosure.sfrac Bool.true Ns78p1297 Ns78p1298) 3989880721902733939173 9007199254740992000 6803330885790165772127 Ns78p184 Ns78p1297 Ns78p1298 0 1 Ns78p1300 

noncomputable def Ns78p1302 := nat_lit 53551272548478478630429025894400 

noncomputable abbrev qz519 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 306949 2000) (Real.log Real.pi))

noncomputable def Ns78p1303 := @Enclosure.Real.IsNear.subLit_ff_p qz182 qz519 1114465430680110534753 1801439850948198400 6561438290034064771 735294000000000000000000 11790144678189 67108864000 306949 33554432000 Ns78p1302 3989880721902733939173 9007199254740992000 

noncomputable def Ns78p1304 := nat_lit 11144654306801105347530000 

noncomputable abbrev qz183 := (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 306949 4000) qz733) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 613898))))))

noncomputable def Ns78p1305 := @Enclosure.Real.IsNear.subLit_ff_p qz183 qz517 6954702555422299050469 9007199254740992000 6561438290034064771 735294000000000000000000 306949 2000 0 1 Ns78p1304 1114465430680110534753 1801439850948198400 6561438290034064771 735294000000000000000000 

noncomputable def Ns78p1306 := nat_lit 15660597918536251154574191342032781312 

noncomputable def Ns78p1307 := nat_lit 12170342664954727127580672 

noncomputable def Ns78p1308 := nat_lit 26273887269357889404642169975019630681952184245385414018365293632767990035549545430544378556907520 

noncomputable def Ns78p1309 := nat_lit 287892663414298333036985623360328005252647625018994225382824968297487890307760932955178135977984 

noncomputable def Ns78p1310 := nat_lit 3151644645338906847907689102970364296719836763143077121430100836378294905766791795448545280 

noncomputable def Ns78p1311 := BSN.log_dyadic_bound 114727754404 639015754404 5 4 Ns78p1308 33554432 8823528 Ns78p1309 Ns78p1310 12180627 753743508808 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 114727754404) (BSN.artanhQ 639015754404) 0 4 Ns78p1309 Ns78p1308 Ns78p1310 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns78p1312 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 306949 4000) qz733 306949 4000 0 1 22669029729356481 2251799813685248 62500007720587 551470500000000000000 6958236006396242486469 9007199254740992000 19184314869826459063 Ns78p194 (Enclosure.Real.IsNear.const Bool.false 306949 4000) (BSN.isNear_log_sfrac 376871754404 16000000 22669029729356481 2251799813685248 62500007720587 551470500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 376871754404) qz347)) Bool.false Ns78p1307 Ns78p84 1000000123529392 8823528000000000000000 22669029729356481 2251799813685248 62500007720587 551470500000000000000 (BSN.log_rat_reduce_isNear 376871754404 16000000 14 753743508808 524288000000 12180627 33554432 24973259072661432 36028797018963968 8823528 1000000000000000 rfl rfl rfl rfl (Ns78p1311 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns78p1313 := BSN.arctan_dyadic_bound_f 1000 613898 1 0 4194304 1102941 0 1 1 0 1 1 6832 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 613898) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 613898) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz520 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 613898)))

noncomputable def Ns78p1314 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz520 884279719003555 562949953421312 1 2000000000000000 6832 4194304 1 1102941 3705091888453712347136 883362743485859 562949953421312 2000000001102941 2205882000000000000000 qz17 (Ns78p1313 rfl) rfl rfl 

noncomputable def Ns78p1315 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 306949 4000) qz733) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz520)) 6958236006396242486469 9007199254740992000 19184314869826459063 Ns78p194 883362743485859 2251799813685248 2000000001102941 8823528000000000000000 Ns78p1306 6954702555422299050469 9007199254740992000 6561438290034064771 735294000000000000000000 (Ns78p1312 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz520) 1 4 0 1 883362743485859 562949953421312 2000000001102941 2205882000000000000000 883362743485859 2251799813685248 2000000001102941 8823528000000000000000 qz350 Ns78p1314 rfl) 

noncomputable def Ns78p1316 := @Ns78p1301 Ns78p1295 Ns78p1296 6803330885790165772127 Ns78p184 (@Ns78p1303 6803330885790165772127 Ns78p184 (Ns78p1305 (Ns78p1315 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 306949 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz517 (Real.log Real.pi) 306949 2000 0 1 38410761 33554432 1 16777216 11790144678189 67108864000 306949 33554432000 (Enclosure.Real.IsNear.const Bool.false 306949 2000) RS079to096.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns78p1297 Ns78p1298) 

noncomputable def Ns78p1317 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz178) Bool.false Ns78p1295 Ns78p1296 6803330885790165772127 Ns78p184 3715861431 8388608 153 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz178) (@HAdd.hAdd Real Real Real qz351 qz518 (Enclosure.sfrac Bool.true Ns78p1297 Ns78p1298)) Bool.false Ns78p1295 Ns78p1296 6803330885790165772127 Ns78p184 Ns78p1299 (Ns78p1316 rfl rfl)) 

noncomputable def Ns78p1318 := nat_lit 1899746446478387280084992 

noncomputable def Ns78p1319 := nat_lit 140216602300195812197434130054244500254560219993452627908644813423977134238970017931520 

noncomputable def Ns78p1320 := nat_lit 282180320351127362997478354969669084519332613330619704282801962172085600081348321536 

noncomputable def Ns78p1321 := nat_lit 366777095029468159072236328043546607863197847180316831668088070076423403463837387776256 

noncomputable def Ns78p1322 := BSN.sin_dyadic_bound_f 26997020746 17179869184 3 2 8388608 2208037 Ns78p1319 Ns78p97 Ns78p1320 Ns78p1321 Ns78p100 Ns78p1320 8388605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26997020746) qz352 0 2 Ns78p1319 Ns78p97 Ns78p1320 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26997020746) qz353 0 2 Ns78p1321 Ns78p100 Ns78p1320 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1323 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz178) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3715861431) qz354) Bool.false 3715861431 8388608 153 8388608 Bool.true 8388605 8388608 1 1102941 (Ns78p1317 rfl) (Enclosure.sfrac_false_div 3715861431 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3715861431) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns78p1318) qz355) 226375608064910080 72057594037927936 Bool.false 8388605 8388608 70 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q1 3715861431 8388608 226375608064910080 72057594037927936 70 Ns78p1318 Ns78p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388605 8388608 Ns78p1318 Ns78p84 26997020746 17179869184 2208037 2205882 (Ns78p1322 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p1324 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz178) Bool.false Ns78p1295 Ns78p1296 6803330885790165772127 Ns78p184 29726891452 67108864 1213 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz178) (@HAdd.hAdd Real Real Real qz351 qz518 (Enclosure.sfrac Bool.true Ns78p1297 Ns78p1298)) Bool.false Ns78p1295 Ns78p1296 6803330885790165772127 Ns78p184 Ns78p1299 (Ns78p1316 rfl rfl)) 

noncomputable abbrev qz734 := (BSN.cos_quad_nat3 67 rfl)

noncomputable def Ns78p1325 := Ns78p1294 26922 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 146 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 43367050 67108864) BSN.abs_quadSignPos qz734 (BSN.sfrac_eq_quadSignPos_mul Bool.false 32407321 67108864) qz181 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 1) Bool.true 8388605 8388608 177138581 9252139696128 67108840 67108864 1285 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz178)) Bool.true 8388605 8388608 177138581 9252139696128 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz178) qz178) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz178)) Bool.true 8388605 8388608 177138581 9252139696128 8388605 8388608 177138581 9252139696128 (Ns78p1323 rfl rfl) rfl)) rfl) (Ns78p1324 rfl) RS079to096.d7 

noncomputable def Ns78p1326 := nat_lit 392759639985232402761901280516810563872687355941442626028255088161 

noncomputable def Ns78p1327 := nat_lit 132770738989272260311244047043662590219198872192572855283650081 

noncomputable def Ns78p1328 := nat_lit 1178013378477718663765081353456344366437623670079942732374197964321 

noncomputable def Ns78p1329 := BSN.cos_dyadic_bound_f 58262323 67108864 3 2 67108864 33554432 Ns78p1326 Ns78p116 Ns78p1327 Ns78p1328 Ns78p119 Ns78p1327 43367050 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 58262323) qz357 0 2 Ns78p1326 Ns78p116 Ns78p1327 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 58262323) (BSN.cosOddQ 67108864) 0 2 Ns78p1328 Ns78p119 Ns78p1327 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1330 := nat_lit 1308404806467831971656479687681 

noncomputable def Ns78p1331 := BSN.sin_dyadic_bound_f 33820929 67108864 2 1 67108864 33554432 Ns78p1330 Ns78p106 Ns78p1330 Ns78p1330 Ns78p107 Ns78p1330 32407321 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 33820929) qz356 0 1 Ns78p1330 Ns78p106 Ns78p1330 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 33820929) (BSN.sinOddQ 67108864) 0 1 Ns78p1330 Ns78p107 Ns78p1330 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1332 := nat_lit 14977246537512090526707360000 

noncomputable def Ns78p1333 := BSN.sin_dyadic_bound_f 11062620 67108864 2 1 67108864 33554432 Ns78p1332 Ns78p106 Ns78p1332 Ns78p1332 Ns78p107 Ns78p1332 11012585 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 11062620) qz356 0 1 Ns78p1332 Ns78p106 Ns78p1332 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 11062620) (BSN.sinOddQ 67108864) 0 1 Ns78p1332 Ns78p107 Ns78p1332 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1334 := nat_lit 261976177047486946497458396187099337639913956378856461738518610561 

noncomputable def Ns78p1335 := nat_lit 59084018073497116199845070958596813193736081003901156319396481 

noncomputable def Ns78p1336 := nat_lit 785810363106313845259975498419380819293354396974561582902917038721 

noncomputable def Ns78p1337 := BSN.cos_dyadic_bound_f 52654289 67108864 3 2 67108864 33554432 Ns78p1334 Ns78p116 Ns78p1335 Ns78p1336 Ns78p119 Ns78p1335 47490516 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 52654289) qz357 0 2 Ns78p1334 Ns78p116 Ns78p1335 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 52654289) (BSN.cosOddQ 67108864) 0 2 Ns78p1336 Ns78p119 Ns78p1335 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1338 := Ns78p1292 45827 BSN.abs_quadSignPos (BSN.cos_quad_nat3 11 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 11012585 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 32 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 47490516 67108864) qz181 rfl rfl (Ns78p1325 RS079to096.d9 RS079to096.d11 RS079to096.d13 RS079to096.d17 (Ns78p1329 rfl rfl) (Ns78p1331 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns78p1324 rfl) RS079to096.d19 RS079to096.d21 RS079to096.d23 RS079to096.d25 RS079to096.d17 (Ns78p1333 rfl rfl) (Ns78p1337 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns78p1339 := nat_lit 32035050054940524774410067921 

noncomputable def Ns78p1340 := BSN.cos_dyadic_bound_f 13378467 67108864 2 1 67108864 33554432 Ns78p1339 Ns78p228 Ns78p1339 Ns78p1339 Ns78p229 Ns78p1339 65779744 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 13378467) qz357 0 1 Ns78p1339 Ns78p228 Ns78p1339 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 13378467) (BSN.cosOddQ 67108864) 0 1 Ns78p1339 Ns78p229 Ns78p1339 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1341 := Ns78p1290 Bool.true 52318911 45827 Bool.true 13378467 3537118876014220 1 Bool.false 65779744 Bool.false Bool.true 25464442 54102 BSN.abs_quadSignPos qz689 (BSN.sfrac_eq_quadSignPos_mul Bool.false 65779744 67108864) qz181 rfl (Ns78p1338 rfl rfl) (Ns78p1324 rfl) RS079to096.d27 RS079to096.d29 RS079to096.d17 (Ns78p1340 rfl rfl) rfl 

noncomputable def Ns78p1342 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 6) 25464442 67108864 54102 67108864 25464442 67108864 54102 67108864 3417779550027776 12732221 16777216 27051 16777216 (Ns78p1341 rfl rfl rfl rfl) 

noncomputable def Ns78p1343 := @Enclosure.Real.IsNear.mulLit_ff qz732 (Zeta.RiemannSiegel.correction qz180) 1586493 4194304 1 4194304 7905892254975 8796093022208 223088911220285 3233857211335704576 12542642721272052675 36893488147419103232 

noncomputable abbrev qz735 := (@HPow.hPow Real Real Real qz7 qz179 qz9)

noncomputable def Ns78p1344 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz735 1 1 0 1 1586493 4194304 1 4194304 1586493 4194304 1 4194304 

noncomputable def Ns78p1345 := @Enclosure.Real.IsNear.sqrt_image qz179 409804233461 8388608000 306949 8388608000 29315885 29315908 4194304 (@Enclosure.Real.IsNear.of_eq qz179 (@HMul.hMul Real Real Real qz5 qz178 qz3) Bool.false 409804233461 8388608000 306949 8388608000 (BSN.t_div_two_pi_mk qz178 306949 1000 qz181) (@Enclosure.Real.IsNear.mulLit_ff qz178 qz3 306949 1000 0 1 1335089 8388608 1 8388608 409804233461 8388608000 306949 8388608000 (Enclosure.Real.IsNear.const Bool.false 306949 1000) RS079to096.d32 rfl)) 

noncomputable abbrev qz896 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 306949 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz736 := qz896

noncomputable abbrev qz521 := qz736

noncomputable abbrev qz184 := qz521

noncomputable def Ns78p1346 := @Enclosure.Real.IsNear.sqrt_image qz184 58631793 8388608 23 8388608 11088721 11088726 4194304 (@Enclosure.Real.IsNear.recentre' qz184 Bool.false 58631793 8388608 23 8388608 58631793 8388608 23 8388608 (Ns78p1345 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns78p1347 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz184) 22177447 8388608 5 8388608 1586492 1586494 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz184) Bool.false 22177447 8388608 5 8388608 22177447 8388608 5 8388608 (Ns78p1346 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns78p1348 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz184)) Bool.false 3172986 8388608 2 8388608 1586493 4194304 1 4194304 (Ns78p1347 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz185 := (@HMul.hMul Real Real Real qz336 qz334 qz515)

noncomputable abbrev qz737 := (@HMul.hMul Real Real Real qz841 qz895 qz895)

noncomputable abbrev qz522 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz737 qz731) qz640)

noncomputable abbrev qz186 := (Real.cos (@HMul.hMul Real Real Real qz336 qz334 qz522))

noncomputable def Ns78p1349 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz180) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz185)) qz186) Bool.false 7905892254975 

noncomputable def Ns78p1350 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz185)) qz186 4203529 4194304 77 

noncomputable def Ns78p1351 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz185)) Bool.false 8407058 8388608 154 8388608 4203529 4194304 77 

noncomputable def Ns78p1352 := @Enclosure.Real.IsNear.recentre' (Real.cos qz185) Bool.false 8370199 8388608 168315053 9252139696128 8370199 8388608 168315053 9252139696128 

noncomputable def Ns78p1353 := @Enclosure.Real.IsNear.cos_image qz185 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 52151349) qz354) Bool.false 52151349 8388608 145 8388608 Bool.false 8370199 8388608 1 

noncomputable def Ns78p1354 := nat_lit 620679734479310748123002081 

noncomputable def Ns78p1355 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz180 884279719003555 140737488355328 1 500000000000000 8300145 8388608 23 8388608 7339649888288762015475 1180591620717411303424 Ns78p1354 

noncomputable def Ns78p1356 := @Enclosure.Real.IsNear.subLit_ff_p qz184 qz1 58631793 8388608 23 8388608 6 1 0 1 8300145 8300145 8388608 23 

noncomputable def Ns78p1357 := @Ns78p1356 8388608 (@Enclosure.Real.IsNear.recentre' qz184 Bool.false 58631793 8388608 23 8388608 58631793 8388608 23 8388608 (Ns78p1345 rfl rfl rfl rfl rfl rfl) rfl) qz362 

noncomputable def Ns78p1358 := @Enclosure.Real.IsNear.recentre' qz185 Bool.false 7339649888288762015475 1180591620717411303424 Ns78p1354 Ns78p385 52151349 8388608 145 8388608 (@Ns78p1355 Ns78p385 RS079to096.d31 (Ns78p1357 rfl rfl) rfl) 

noncomputable def Ns78p1359 := nat_lit 1818872759090090405265408 

noncomputable def Ns78p1360 := nat_lit 117784064594622989305651711198030595316224649855221455565885161398986877450987088445440 

noncomputable def Ns78p1361 := nat_lit 199241656954464278561898953868739190994841873539708761735990699141073620487257522176 

noncomputable def Ns78p1362 := nat_lit 308159492207991077444749502450483124280882434206515712296412390151118178890843957559296 

noncomputable def Ns78p1363 := BSN.sin_dyadic_bound_f 25847736524 17179869184 3 2 8388608 2208037 Ns78p1360 Ns78p97 Ns78p1361 Ns78p1362 Ns78p100 Ns78p1361 8370199 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 25847736524) qz352 0 2 Ns78p1360 Ns78p97 Ns78p1361 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 25847736524) qz353 0 2 Ns78p1362 Ns78p100 Ns78p1361 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1364 := @Ns78p1353 1102941 (Ns78p1358 rfl) (Enclosure.sfrac_false_div 52151349 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 52151349) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns78p1359) qz355) 226375608064910080 72057594037927936 Bool.false 8370199 8388608 0 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q3 52151349 8388608 226375608064910080 72057594037927936 0 Ns78p1359 Ns78p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8370199 8388608 Ns78p1359 Ns78p84 25847736524 17179869184 2208037 2205882 (Ns78p1363 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p1365 := @Enclosure.Real.IsNear.inv_image (Real.cos qz185) 8370199 8388608 168315053 9252139696128 4203452 4203606 4194304 (Ns78p1352 (Ns78p1364 rfl rfl) rfl) rfl 

noncomputable def Ns78p1366 := @Enclosure.Real.IsNear.recentre' qz186 Bool.false 3761550 4194304 

noncomputable abbrev qz187 := (@HMul.hMul Real Real Real qz336 qz334 qz522)

noncomputable def Ns78p1367 := @Enclosure.Real.IsNear.cos_image qz187 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 1922083)) qz378) Bool.true 1922083 4194304 

noncomputable def Ns78p1368 := nat_lit 4538390781071299309297939645 

noncomputable def Ns78p1369 := nat_lit 15510116849466905900724254445599449 

noncomputable def Ns78p1370 := @Enclosure.Real.IsNear.recentre' qz187 Bool.true Ns78p1368 Ns78p397 Ns78p1369 

noncomputable abbrev qz188 := qz522

noncomputable def Ns78p1371 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz188 884279719003555 140737488355328 1 500000000000000 5132302238239 

noncomputable abbrev qz523 := (@HSub.hSub Real Real Real qz634 qz737 qz731)

noncomputable abbrev qz189 := qz523

noncomputable def Ns78p1372 := @Enclosure.Real.IsNear.subLit_tf qz189 qz26 734255727135 70368744177664 574745183 70368744177664 1 16 

noncomputable abbrev qz524 := qz737

noncomputable abbrev qz190 := qz524

noncomputable def Ns78p1373 := @Enclosure.Real.IsNear.subLit_ff_n qz190 qz180 68892407021025 70368744177664 381807199 70368744177664 8300145 8388608 23 8388608 

noncomputable def Ns78p1374 := @Enclosure.Real.IsNear.mulLit_ff qz180 qz180 8300145 8388608 23 8388608 8300145 8388608 23 8388608 68892407021025 70368744177664 

noncomputable def Ns78p1375 := nat_lit 13648613961528400001914321 

noncomputable def Ns78p1376 := nat_lit 7427640235712281649394745344 

noncomputable def Ns78p1377 := nat_lit 111414603535684224740921180160 

noncomputable def Ns78p1378 := BSN.cos_dyadic_bound_f 1922083 4194304 2 1 4194304 1102941 Ns78p1375 Ns78p1376 Ns78p1375 Ns78p1375 Ns78p1377 Ns78p1375 3761550 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1922083) (BSN.cosEvenQ 4194304) 0 1 Ns78p1375 Ns78p1376 Ns78p1375 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1922083) (BSN.cosOddQ 4194304) 0 1 Ns78p1375 Ns78p1377 Ns78p1375 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1379 := @Ns78p1366 30303695 578258731008 1880775 2097152 30303695 578258731008 (@Ns78p1367 27 524288 Bool.false 3761550 4194304 1 1102941 (@Ns78p1370 Ns78p495 1922083 4194304 27 524288 (@Ns78p1371 70368744177664 574745183 70368744177664 Ns78p1368 Ns78p397 Ns78p1369 Ns78p495 RS079to096.d31 (@Ns78p1372 0 1 82116835811824 5132302238239 70368744177664 574745183 70368744177664 (@Ns78p1373 6159383466690478080 734255727135 70368744177664 574745183 70368744177664 (@Ns78p1374 381807199 70368744177664 (Ns78p1357 rfl rfl) (Ns78p1357 rfl rfl) rfl) (Ns78p1357 rfl rfl) rfl rfl) qz366 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 1922083 4194304) (BSN.cos_neg_of_bound 1922083 4194304 Bool.false 3761550 4194304 1 1102941 (Ns78p1378 rfl rfl)) rfl rfl) 

noncomputable def Ns78p1380 := @Ns78p1343 50976542383911374945 Ns78p1287 (Ns78p1344 qz28 (@Enclosure.Real.IsNear.of_eq qz735 (@Inv.inv Real Real.instInv (Real.sqrt qz184)) Bool.false 1586493 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz179 (BSN.t_div_two_pi_nonneg qz178 306949 1000 qz181)) Ns78p1348) rfl) (@Ns78p1349 8796093022208 223088911220285 3233857211335704576 (BSN.correction_mk qz180 (BSN.cos_two_pi_p_ne_zero_mk qz178 306949 1000 6 qz181 rfl rfl (@BSN.floor_sqrt_eq_dec qz178 306949 1000 6 qz181 rfl rfl rfl))) (@Ns78p1350 4194304 1880775 2097152 30303695 578258731008 7905892254975 8796093022208 223088911220285 3233857211335704576 (@Ns78p1351 4194304 (Ns78p1365 rfl rfl rfl rfl rfl) rfl) (Ns78p1379 rfl) rfl)) 

noncomputable def Ns78p1381 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz178) (hardyZApproximantRS₀ qz178) Bool.true 40541092795099593667 36893488147419103232 3175229093235416535137 Ns78p1287 (@Eq.refl Real (hardyZApproximantRS₀ qz178)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz178) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz178) qz178 6) (@HMul.hMul Real Real Real qz5 qz732 (Zeta.RiemannSiegel.correction qz180))) Bool.true 40541092795099593667 36893488147419103232 3175229093235416535137 Ns78p1287 (BSN.hardyZApproximantRS₀_eq qz178 6 (@BSN.floor_sqrt_eq_dec qz178 306949 1000 6 qz181 rfl rfl rfl)) (@Ns78p1289 40541092795099593667 36893488147419103232 3175229093235416535137 Ns78p1287 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz178) qz178 6) (@HAdd.hAdd Real Real Real qz351 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz178) qz178 6)) Bool.true 12732221 16777216 27051 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz178) qz178 6) (Ns78p1342 (Ns78p1341 rfl rfl rfl rfl) rfl rfl)) (Ns78p1380 rfl) rfl rfl)) 

theorem RS079to096.d47 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz178) Bool.true 40541092795099593667 36893488147419103232 3175229093235416535137 Ns78p1287 := Ns78p1381 

noncomputable def Ns78p1382 := BSN.log_dyadic_bound 3 11 6 5 269619528727395 4194304 1102941 6999933372849 55801305 2347198 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 3) (BSN.artanhQ 11) 0 5 6999933372849 269619528727395 55801305 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz897 := (Enclosure.sfrac Bool.false 7 1)

noncomputable abbrev qz738 := qz897

noncomputable abbrev qz525 := qz738

noncomputable abbrev qz191 := qz525

noncomputable abbrev qz526 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) (@Nat.cast Real Real.instNatCast 1))

theorem RS079to096.d48 : Enclosure.Real.IsNear (Real.log qz191) Bool.false 4381799714987255 2251799813685248 500000001102941 551470500000000000000 := BSN.isNear_log_sfrac 7 1 4381799714987255 2251799813685248 500000001102941 551470500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz526) Bool.false 294057601148318457528320 151115727451828646838272 1000000002205882 1102941000000000000000 4381799714987255 2251799813685248 500000001102941 551470500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 2347198 4194304 24973259072661432 36028797018963968 1102941 1000000000000000 rfl rfl rfl rfl (Ns78p1382 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS079to096.d49 : Enclosure.Real.IsNear (Real.log qz191) Bool.false 130587807 67108864 62 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log qz191) Bool.false 4381799714987255 2251799813685248 500000001102941 551470500000000000000 130587807 67108864 62 67108864 RS079to096.d48 rfl 

noncomputable abbrev qz527 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns78p1383 := @Enclosure.Real.IsNear.inv_image qz527 22194171 8388608 1 8388608 1585297 1585298 4194304 (@Enclosure.Real.IsNear.of_eq qz527 (Real.sqrt qz526) Bool.false 22194171 8388608 1 8388608 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz526) Bool.false 22194171 8388608 1 8388608 22194171 8388608 1 8388608 (BSN.sqrt_enclosure 7 1 11097085 11097086 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz528 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS079to096.d50 : Enclosure.Real.IsNear qz528 Bool.false 3170595 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz528 Bool.false 3170595 8388608 1 8388608 3170595 8388608 1 8388608 (Ns78p1383 rfl rfl) rfl 

theorem RS079to096.d51 : Enclosure.Real.IsNear qz528 Bool.false 25364760 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz528 Bool.false 3170595 8388608 1 8388608 25364760 67108864 8 67108864 RS079to096.d50 rfl 

noncomputable def Ns78p1384 := nat_lit 2066144212556025075670712320 

noncomputable abbrev qz898 := (Enclosure.sfrac Bool.false 308563 1000)

noncomputable abbrev qz739 := qz898

noncomputable abbrev qz529 := qz739

noncomputable abbrev qz192 := qz529

noncomputable abbrev qz193 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 7)

noncomputable abbrev qz899 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 308563 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz740 := qz899

noncomputable abbrev qz530 := qz740

noncomputable abbrev qz194 := qz530

noncomputable abbrev qz900 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 308563 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz741 := qz900

noncomputable abbrev qz531 := qz741

noncomputable abbrev qz195 := qz531

noncomputable abbrev qz742 := (@HMul.hMul Real Real Real qz5 qz193 (@HPow.hPow Real Real Real qz7 qz194 qz9))

noncomputable def Ns78p1385 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz192) qz192 7) (@HMul.hMul Real Real Real qz5 qz742 (Zeta.RiemannSiegel.correction qz195)) 13283585 2097152 62083 33554432 50465140125793610595 147573952589676412928 104965422160197116261 Ns78p310 Ns78p1384 

noncomputable def Ns78p1386 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz192) qz192 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 308563 1000 67 98 67108864 33554432 1125899906842624 Bool.false 29937638890 1220 

noncomputable def Ns78p1387 := Ns78p1386 120242927 62 27397080 8 130587807 62 25364760 8 Bool.false 208612230 46063 Bool.true 102117470 Bool.true 26319608 3537118876014220 1 Bool.false 67027896 Bool.false Bool.false 62013502 Bool.true Bool.false 212537360 

noncomputable def Ns78p1388 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz192) qz192 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 308563 1000 11 32 67108864 33554432 1125899906842624 Bool.false 29937638890 1220 

noncomputable def Ns78p1389 := Ns78p1388 93032624 61 33554424 8 108007536 61 30011992 8 Bool.false 150076156 27058 Bool.false 71655402 Bool.true 16231014 3537118876014220 1 Bool.false 58795241 Bool.false Bool.false 65155589 Bool.false Bool.false 208612230 

noncomputable def Ns78p1390 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz192) qz192 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 308563 1000 147 68 67108864 33554432 1125899906842624 Bool.false 29937638890 1220 

noncomputable def Ns78p1391 := Ns78p1390 46516304 61 47453136 16 73726608 61 38745320 8 Bool.false 67108848 1285 Bool.false 88518090 Bool.false 20159265 3537118876014220 1 Bool.false 64993055 Bool.false Bool.false 64103678 Bool.false Bool.false 150076156 

noncomputable def Ns78p1392 := nat_lit 31213067303075908867686551666908329764158284085533896963 

noncomputable def Ns78p1393 := nat_lit 69967892134051463934323226560923589122591347965952000 

noncomputable def Ns78p1394 := nat_lit 1342651705194689807130581940640000 

noncomputable def Ns78p1395 := nat_lit 2485758874614826081537558854994201920 

noncomputable abbrev qz532 := (@Eq.refl Real qz739)

noncomputable abbrev qz196 := qz532

noncomputable def Ns78p1396 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz192 308563 1000 380845499876 16000000 617126 4000 2000 Ns78p1394 Ns78p1395 qz196 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns78p1397 := nat_lit 9988181536984290837659696533410665524530650907370847028160 

noncomputable abbrev qz533 := (Enclosure.sfrac Bool.false 308563 2000)

noncomputable abbrev qz743 := (Real.log (Enclosure.sfrac Bool.false 380845499876 16000000))

noncomputable abbrev qz197 := (@HSub.hSub Real Real Real qz339 (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 308563 4000) qz743) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 617126)))))) qz533)

noncomputable abbrev qz534 := (@HSub.hSub Real Real Real qz12 qz197 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 308563 2000) (Real.log Real.pi)))

noncomputable def Ns78p1398 := @Enclosure.Real.IsNear.addLit_ft_p qz534 (Enclosure.sfrac Bool.true Ns78p1394 Ns78p1395) 4018166738744288812723 9007199254740992000 6838655477333351691049 Ns78p184 Ns78p1394 Ns78p1395 0 1 Ns78p1397 

noncomputable def Ns78p1399 := nat_lit 269654605199714008709749276672000 

noncomputable abbrev qz535 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 308563 2000) (Real.log Real.pi))

noncomputable def Ns78p1400 := @Enclosure.Real.IsNear.subLit_ff_p qz197 qz535 5608933994028591554227 9007199254740992000 6595063294187740577 735294000000000000000000 11852139646443 67108864000 308563 33554432000 Ns78p1399 4018166738744288812723 9007199254740992000 

noncomputable abbrev qz198 := (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 308563 4000) qz743) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 617126))))))

noncomputable def Ns78p1401 := @Enclosure.Real.IsNear.subLit_ff_p qz198 qz533 279943128233956556459 360287970189639680 6595063294187740577 735294000000000000000000 308563 2000 0 1 448714719522287324338160 5608933994028591554227 9007199254740992000 6595063294187740577 735294000000000000000000 

noncomputable def Ns78p1402 := nat_lit 630375883999688862820562404567416832 

noncomputable def Ns78p1403 := nat_lit 12183022855950363420262400 

noncomputable def Ns78p1404 := nat_lit 27609774243616892621392187175734425024745224000701440187806777792598017786366958566265676218040320 

noncomputable def Ns78p1405 := nat_lit 320224563536440030923699210716297121060366812911288033683997087015357283305014042617961257631744 

noncomputable def Ns78p1406 := nat_lit 4138461810298872460764839604275632174394216546737026308387341920139578083550763019882004480 

noncomputable def Ns78p1407 := BSN.log_dyadic_bound 118701499876 642989499876 5 4 Ns78p1404 33554432 8823528 Ns78p1405 Ns78p1406 12532573 761690999752 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 118701499876) (BSN.artanhQ 642989499876) 0 4 Ns78p1405 Ns78p1404 Ns78p1406 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns78p1408 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 308563 4000) qz743 308563 4000 0 1 22692648425605825 2251799813685248 62500007720587 551470500000000000000 280084467046008407179 360287970189639680 19285189882287486481 Ns78p194 (Enclosure.Real.IsNear.const Bool.false 308563 4000) (BSN.isNear_log_sfrac 380845499876 16000000 22692648425605825 2251799813685248 62500007720587 551470500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 380845499876) qz347)) Bool.false Ns78p1403 Ns78p84 1000000123529392 8823528000000000000000 22692648425605825 2251799813685248 62500007720587 551470500000000000000 (BSN.log_rat_reduce_isNear 380845499876 16000000 14 761690999752 524288000000 12532573 33554432 24973259072661432 36028797018963968 8823528 1000000000000000 rfl rfl rfl rfl (Ns78p1407 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns78p1409 := BSN.arctan_dyadic_bound_f 1000 617126 1 0 4194304 1102941 0 1 1 0 1 1 6796 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 617126) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 617126) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz536 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 617126)))

noncomputable def Ns78p1410 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz536 884279719003555 562949953421312 1 2000000000000000 6796 4194304 1 1102941 3705112154652035514368 883367575324067 562949953421312 2000000001102941 2205882000000000000000 qz17 (Ns78p1409 rfl) rfl rfl 

noncomputable def Ns78p1411 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 308563 4000) qz743) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz536)) 280084467046008407179 360287970189639680 19285189882287486481 Ns78p194 883367575324067 2251799813685248 2000000001102941 8823528000000000000000 Ns78p1402 279943128233956556459 360287970189639680 6595063294187740577 735294000000000000000000 (Ns78p1408 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz536) 1 4 0 1 883367575324067 562949953421312 2000000001102941 2205882000000000000000 883367575324067 2251799813685248 2000000001102941 8823528000000000000000 qz350 Ns78p1410 rfl) 

noncomputable def Ns78p1412 := @Ns78p1398 Ns78p1392 Ns78p1393 6838655477333351691049 Ns78p184 (@Ns78p1400 6838655477333351691049 Ns78p184 (Ns78p1401 (Ns78p1411 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 308563 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz533 (Real.log Real.pi) 308563 2000 0 1 38410761 33554432 1 16777216 11852139646443 67108864000 308563 33554432000 (Enclosure.Real.IsNear.const Bool.false 308563 2000) RS079to096.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns78p1394 Ns78p1395) 

noncomputable def Ns78p1413 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz192) Bool.false Ns78p1392 Ns78p1393 6838655477333351691049 Ns78p184 3742204861 8388608 153 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz192) (@HAdd.hAdd Real Real Real qz351 qz534 (Enclosure.sfrac Bool.true Ns78p1394 Ns78p1395)) Bool.false Ns78p1392 Ns78p1393 6838655477333351691049 Ns78p184 Ns78p1396 (Ns78p1412 rfl rfl)) 

noncomputable def Ns78p1414 := nat_lit 1898282341855192701468672 

noncomputable def Ns78p1415 := nat_lit 139783984636101637703714249803374753748853567241269171639734162000155613842776302551040 

noncomputable def Ns78p1416 := nat_lit 280445230614592739378526631731115818214158571532026095286596811647389006525812965376 

noncomputable def Ns78p1417 := nat_lit 365646857959271139074543515890797786588936419373224550140268315162502263577658047594496 

noncomputable def Ns78p1418 := BSN.sin_dyadic_bound_f 26976214568 17179869184 3 2 8388608 2208037 Ns78p1415 Ns78p97 Ns78p1416 Ns78p1417 Ns78p100 Ns78p1416 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26976214568) qz352 0 2 Ns78p1415 Ns78p97 Ns78p1416 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26976214568) qz353 0 2 Ns78p1417 Ns78p100 Ns78p1416 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1419 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz192) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3742204861) qz354) Bool.false 3742204861 8388608 153 8388608 Bool.false 8388606 8388608 1 1102941 (Ns78p1413 rfl) (Enclosure.sfrac_false_div 3742204861 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3742204861) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns78p1414) qz355) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 70 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q3 3742204861 8388608 226375608064910080 72057594037927936 70 Ns78p1414 Ns78p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388606 8388608 Ns78p1414 Ns78p84 26976214568 17179869184 2208037 2205882 (Ns78p1418 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p1420 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz192) Bool.false Ns78p1392 Ns78p1393 6838655477333351691049 Ns78p184 29937638890 67108864 1220 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz192) (@HAdd.hAdd Real Real Real qz351 qz534 (Enclosure.sfrac Bool.true Ns78p1394 Ns78p1395)) Bool.false Ns78p1392 Ns78p1393 6838655477333351691049 Ns78p184 Ns78p1396 (Ns78p1412 rfl rfl)) 

noncomputable def Ns78p1421 := Ns78p1391 27058 BSN.abs_quadSignPos (BSN.cos_quad_nat3 147 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 64993055 67108864) BSN.abs_quadSignPos qz689 (BSN.sfrac_eq_quadSignPos_mul Bool.false 64103678 67108864) qz196 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz192) qz192 1) Bool.false 4194303 4194304 177138581 9252139696128 67108848 67108864 1285 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz192) qz192 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz192)) Bool.false 4194303 4194304 177138581 9252139696128 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz192) qz192) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz192)) Bool.false 8388606 8388608 177138581 9252139696128 4194303 4194304 177138581 9252139696128 (Ns78p1419 rfl rfl) rfl)) rfl) (Ns78p1420 rfl) RS079to096.d7 

noncomputable def Ns78p1422 := nat_lit 3769328406147770959835874277565996544865709946836431255626606240000 

noncomputable def Ns78p1423 := nat_lit 3769261555237925439286940129666451114818258540373852032100000000 

noncomputable def Ns78p1424 := nat_lit 9865947973583300634573206157224816696652867918363381337636759200000 

noncomputable def Ns78p1425 := BSN.sin_dyadic_bound_f 88518090 67108864 3 2 67108864 33554432 Ns78p1422 Ns78p127 Ns78p1423 Ns78p1424 Ns78p130 Ns78p1423 64993055 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 88518090) qz356 0 2 Ns78p1422 Ns78p127 Ns78p1423 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 88518090) (BSN.sinOddQ 67108864) 0 2 Ns78p1424 Ns78p130 Ns78p1423 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1426 := nat_lit 165157680644813359500003050625 

noncomputable def Ns78p1427 := BSN.cos_dyadic_bound_f 20159265 67108864 2 1 67108864 33554432 Ns78p1426 Ns78p228 Ns78p1426 Ns78p1426 Ns78p229 Ns78p1426 64103678 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 20159265) qz357 0 1 Ns78p1426 Ns78p228 Ns78p1426 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 20159265) (BSN.cosOddQ 67108864) 0 1 Ns78p1426 Ns78p229 Ns78p1426 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1428 := nat_lit 1617646844273476222130968487310734656296981878109148498622622163200 

noncomputable def Ns78p1429 := nat_lit 695010705991709493196928369606500180592276122156205562557849856 

noncomputable def Ns78p1430 := nat_lit 4235568860525594004496884344643989766199707900373802687386535813376 

noncomputable def Ns78p1431 := BSN.sin_dyadic_bound_f 71655402 67108864 3 2 67108864 33554432 Ns78p1428 Ns78p127 Ns78p1429 Ns78p1430 Ns78p130 Ns78p1429 58795241 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 71655402) qz356 0 2 Ns78p1428 Ns78p127 Ns78p1429 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 71655402) (BSN.sinOddQ 67108864) 0 2 Ns78p1430 Ns78p130 Ns78p1429 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1432 := nat_lit 69403697687702778818687494416 

noncomputable def Ns78p1433 := BSN.cos_dyadic_bound_f 16231014 67108864 2 1 67108864 33554432 Ns78p1432 Ns78p228 Ns78p1432 Ns78p1432 Ns78p229 Ns78p1432 65155589 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 16231014) qz357 0 1 Ns78p1432 Ns78p228 Ns78p1432 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 16231014) (BSN.cosOddQ 67108864) 0 1 Ns78p1432 Ns78p229 Ns78p1432 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1434 := Ns78p1389 46063 BSN.abs_quadSignPos (BSN.cos_quad_nat3 11 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 58795241 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 32 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 65155589 67108864) qz196 rfl rfl (Ns78p1421 RS079to096.d9 RS079to096.d11 RS079to096.d13 RS079to096.d17 (Ns78p1425 rfl rfl) (Ns78p1427 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns78p1420 rfl) RS079to096.d19 RS079to096.d21 RS079to096.d23 RS079to096.d25 RS079to096.d17 (Ns78p1431 rfl rfl) (Ns78p1433 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns78p1435 := nat_lit 2325454782306685211250058136933390644116263642389241676477323750609761210094904053546810771711142400000 

noncomputable def Ns78p1436 := nat_lit 1285880343044373006399248317851655080497149454653501596654743627795943277825305379441000000000000 

noncomputable def Ns78p1437 := nat_lit 11614547704056346610608176299725034129274363320621400149991798589668159659931258894653485909851712000000 

noncomputable def Ns78p1438 := BSN.sin_dyadic_bound_f 102117470 67108864 4 3 67108864 33554432 Ns78p1435 Ns78p941 Ns78p1436 Ns78p1437 Ns78p944 Ns78p1436 67027896 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 102117470) qz356 0 3 Ns78p1435 Ns78p941 Ns78p1436 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 102117470) (BSN.sinOddQ 67108864) 0 3 Ns78p1437 Ns78p944 Ns78p1436 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1439 := nat_lit 16351312305827795726513519213083386902461373839693899001596215296 

noncomputable def Ns78p1440 := nat_lit 230268924968025026033220581843931947093611454679727332130816 

noncomputable def Ns78p1441 := nat_lit 49053476379633451129488491198086472843489934296172337550124384256 

noncomputable def Ns78p1442 := BSN.cos_dyadic_bound_f 26319608 67108864 3 2 67108864 33554432 Ns78p1439 Ns78p116 Ns78p1440 Ns78p1441 Ns78p119 Ns78p1440 62013502 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 26319608) qz357 0 2 Ns78p1439 Ns78p116 Ns78p1440 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 26319608) (BSN.cosOddQ 67108864) 0 2 Ns78p1441 Ns78p119 Ns78p1440 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1443 := Ns78p1387 62083 BSN.abs_quadSignPos qz734 (BSN.sfrac_eq_quadSignPos_mul Bool.false 67027896 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 98 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 62013502 67108864) qz196 rfl rfl (Ns78p1434 rfl rfl) (Ns78p1420 rfl) RS079to096.d27 RS079to096.d29 RS079to096.d49 RS079to096.d51 RS079to096.d17 (Ns78p1438 rfl rfl) (Ns78p1442 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns78p1444 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz192) qz192 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz192) qz192 7) 212537360 67108864 62083 67108864 212537360 67108864 62083 67108864 28526281574318080 13283585 2097152 62083 33554432 (Ns78p1443 rfl) 

noncomputable def Ns78p1445 := @Enclosure.Real.IsNear.mulLit_tf qz742 (Zeta.RiemannSiegel.correction qz195) 1584415 4194304 1 4194304 31850960844093 35184372088832 65192839409413 1847918406477545472 50465140125793610595 147573952589676412928 

noncomputable abbrev qz744 := (@HPow.hPow Real Real Real qz7 qz194 qz9)

noncomputable def Ns78p1446 := @Enclosure.Real.IsNear.mulLit_tf qz193 qz744 1 1 0 1 1584415 4194304 1 4194304 1584415 4194304 1 4194304 

noncomputable def Ns78p1447 := @Enclosure.Real.IsNear.sqrt_image qz194 411959067107 8388608000 308563 8388608000 29392858 29392881 4194304 (@Enclosure.Real.IsNear.of_eq qz194 (@HMul.hMul Real Real Real qz5 qz192 qz3) Bool.false 411959067107 8388608000 308563 8388608000 (BSN.t_div_two_pi_mk qz192 308563 1000 qz196) (@Enclosure.Real.IsNear.mulLit_ff qz192 qz3 308563 1000 0 1 1335089 8388608 1 8388608 411959067107 8388608000 308563 8388608000 (Enclosure.Real.IsNear.const Bool.false 308563 1000) RS079to096.d32 rfl)) 

noncomputable abbrev qz901 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 308563 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz745 := qz901

noncomputable abbrev qz537 := qz745

noncomputable abbrev qz199 := qz537

noncomputable def Ns78p1448 := @Enclosure.Real.IsNear.sqrt_image qz199 58785739 8388608 23 8388608 11103268 11103274 4194304 (@Enclosure.Real.IsNear.recentre' qz199 Bool.false 58785739 8388608 23 8388608 58785739 8388608 23 8388608 (Ns78p1447 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns78p1449 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz199) 11103271 4194304 3 4194304 1584414 1584416 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz199) Bool.false 22206542 8388608 6 8388608 11103271 4194304 3 4194304 (Ns78p1448 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns78p1450 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz199)) Bool.false 3168830 8388608 2 8388608 1584415 4194304 1 4194304 (Ns78p1449 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz200 := (@HMul.hMul Real Real Real qz336 qz334 qz531)

noncomputable abbrev qz746 := (@HMul.hMul Real Real Real qz841 qz900 qz900)

noncomputable abbrev qz538 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz746 qz741) qz640)

noncomputable abbrev qz201 := (Real.cos (@HMul.hMul Real Real Real qz336 qz334 qz538))

noncomputable def Ns78p1451 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz195) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz200)) qz201) Bool.false 31850960844093 

noncomputable def Ns78p1452 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz200)) qz201 8398711 8388608 155 

noncomputable def Ns78p1453 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz200)) Bool.false 8398711 8388608 155 8388608 8398711 8388608 155 

noncomputable def Ns78p1454 := @Enclosure.Real.IsNear.recentre' (Real.cos qz200) Bool.false 4189259 4194304 84708997 4626069848064 4189259 4194304 84708997 4626069848064 

noncomputable def Ns78p1455 := @Enclosure.Real.IsNear.cos_image qz200 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 411441) qz354) Bool.false 411441 8388608 73 4194304 Bool.false 4189259 4194304 1 

noncomputable def Ns78p1456 := nat_lit 620679734408575540155774177 

noncomputable def Ns78p1457 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz195 884279719003555 140737488355328 1 500000000000000 65483 8388608 23 8388608 57905288839509792065 1180591620717411303424 Ns78p1456 

noncomputable def Ns78p1458 := @Enclosure.Real.IsNear.subLit_ff_p qz199 qz191 58785739 8388608 23 8388608 7 1 0 1 65483 65483 8388608 23 

noncomputable abbrev qz539 := (Enclosure.Real.IsNear.const Bool.false 7 1)

noncomputable def Ns78p1459 := @Ns78p1458 8388608 (@Enclosure.Real.IsNear.recentre' qz199 Bool.false 58785739 8388608 23 8388608 58785739 8388608 23 8388608 (Ns78p1447 rfl rfl rfl rfl rfl rfl) rfl) qz539 

noncomputable def Ns78p1460 := @Enclosure.Real.IsNear.recentre' qz200 Bool.false 57905288839509792065 1180591620717411303424 Ns78p1456 Ns78p385 411441 8388608 73 4194304 (@Ns78p1457 Ns78p385 RS079to096.d31 (Ns78p1459 rfl rfl) rfl) 

noncomputable def Ns78p1461 := nat_lit 118842243771396506390315925504 

noncomputable def Ns78p1462 := nat_lit 1782633656570947595854738882560 

noncomputable def Ns78p1463 := BSN.cos_dyadic_bound_f 411441 8388608 2 1 4194304 1102941 28656969894271331783361 Ns78p1461 28656969894271331783361 28656969894271331783361 Ns78p1462 28656969894271331783361 4189259 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 411441) (BSN.cosEvenQ 8388608) 0 1 28656969894271331783361 Ns78p1461 28656969894271331783361 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 411441) (BSN.cosOddQ 8388608) 0 1 28656969894271331783361 Ns78p1462 28656969894271331783361 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1464 := @Enclosure.Real.IsNear.inv_image (Real.cos qz200) 4189259 4194304 84708997 4626069848064 4199278 4199433 4194304 (Ns78p1454 (@Ns78p1455 1102941 (Ns78p1460 rfl) (Enclosure.sfrac_false_div 411441 8388608) (Ns78p1463 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns78p1465 := @Enclosure.Real.IsNear.recentre' qz201 Bool.false 3792363 4194304 

noncomputable abbrev qz202 := (@HMul.hMul Real Real Real qz336 qz334 qz538)

noncomputable def Ns78p1466 := @Enclosure.Real.IsNear.cos_image qz202 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 925607)) qz398) Bool.true 925607 2097152 

noncomputable def Ns78p1467 := nat_lit 4371056290175955493203977845 

noncomputable def Ns78p1468 := nat_lit 1057588240653153072718269625238889 

noncomputable def Ns78p1469 := @Enclosure.Real.IsNear.recentre' qz202 Bool.true Ns78p1467 Ns78p397 Ns78p1468 

noncomputable abbrev qz203 := qz538

noncomputable def Ns78p1470 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz203 884279719003555 140737488355328 1 500000000000000 4943069705479 

noncomputable abbrev qz540 := (@HSub.hSub Real Real Real qz634 qz746 qz741)

noncomputable abbrev qz204 := qz540

noncomputable def Ns78p1471 := @Enclosure.Real.IsNear.subLit_tf qz204 qz26 545023194375 70368744177664 195950731 70368744177664 1 16 

noncomputable abbrev qz541 := qz746

noncomputable abbrev qz205 := qz541

noncomputable def Ns78p1472 := @Enclosure.Real.IsNear.subLit_ff_n qz205 qz195 4288023289 70368744177664 3012747 70368744177664 65483 8388608 23 8388608 

noncomputable def Ns78p1473 := @Enclosure.Real.IsNear.mulLit_ff qz195 qz195 65483 8388608 23 8388608 65483 8388608 23 8388608 4288023289 70368744177664 

noncomputable def Ns78p1474 := nat_lit 464227514732017603087171584 

noncomputable def Ns78p1475 := nat_lit 6963412720980264046307573760 

noncomputable def Ns78p1476 := BSN.cos_dyadic_bound_f 925607 2097152 2 1 4194304 1102941 734017681165189113765601 Ns78p1474 734017681165189113765601 734017681165189113765601 Ns78p1475 734017681165189113765601 3792363 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 925607) (BSN.cosEvenQ 2097152) 0 1 734017681165189113765601 Ns78p1474 734017681165189113765601 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 925607) (BSN.cosOddQ 2097152) 0 1 734017681165189113765601 Ns78p1475 734017681165189113765601 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1477 := @Ns78p1465 42905969 2313034924032 3792363 4194304 42905969 2313034924032 (@Ns78p1466 37 2097152 Bool.false 3792363 4194304 1 1102941 (@Ns78p1469 Ns78p400 925607 2097152 37 2097152 (@Ns78p1470 70368744177664 195950731 70368744177664 Ns78p1467 Ns78p397 Ns78p1468 Ns78p400 RS079to096.d31 (@Ns78p1471 0 1 79089115287664 4943069705479 70368744177664 195950731 70368744177664 (@Ns78p1472 4571985928519680000 545023194375 70368744177664 195950731 70368744177664 (@Ns78p1473 3012747 70368744177664 (Ns78p1459 rfl rfl) (Ns78p1459 rfl rfl) rfl) (Ns78p1459 rfl rfl) rfl rfl) qz366 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 925607 2097152) (BSN.cos_neg_of_bound 925607 2097152 Bool.false 3792363 4194304 1 1102941 (Ns78p1476 rfl rfl)) rfl rfl) 

noncomputable abbrev qz542 := (@Enclosure.Real.IsNear.of_eq qz193 (Enclosure.sfrac Bool.true 1 1) Bool.true 1 1 0 1 (BSN.neg_one_pow_odd_mk 7 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1))

noncomputable def Ns78p1478 := @Ns78p1445 104965422160197116261 Ns78p310 (Ns78p1446 qz542 (@Enclosure.Real.IsNear.of_eq qz744 (@Inv.inv Real Real.instInv (Real.sqrt qz199)) Bool.false 1584415 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz194 (BSN.t_div_two_pi_nonneg qz192 308563 1000 qz196)) Ns78p1450) rfl) (@Ns78p1451 35184372088832 65192839409413 1847918406477545472 (BSN.correction_mk qz195 (BSN.cos_two_pi_p_ne_zero_mk qz192 308563 1000 7 qz196 rfl rfl (@BSN.floor_sqrt_eq_dec qz192 308563 1000 7 qz196 rfl rfl rfl))) (@Ns78p1452 8388608 3792363 4194304 42905969 2313034924032 31850960844093 35184372088832 65192839409413 1847918406477545472 (@Ns78p1453 8388608 (Ns78p1464 rfl rfl rfl rfl rfl) rfl) (Ns78p1477 rfl) rfl)) 

noncomputable def Ns78p1479 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz192) (hardyZApproximantRS₀ qz192) Bool.false 985214334753048456035 147573952589676412928 14445505225828379058533 Ns78p310 (@Eq.refl Real (hardyZApproximantRS₀ qz192)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz192) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz192) qz192 7) (@HMul.hMul Real Real Real qz5 qz742 (Zeta.RiemannSiegel.correction qz195))) Bool.false 985214334753048456035 147573952589676412928 14445505225828379058533 Ns78p310 (BSN.hardyZApproximantRS₀_eq qz192 7 (@BSN.floor_sqrt_eq_dec qz192 308563 1000 7 qz196 rfl rfl rfl)) (@Ns78p1385 985214334753048456035 147573952589676412928 14445505225828379058533 Ns78p310 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz192) qz192 7) (@HAdd.hAdd Real Real Real qz351 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz192) qz192 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz192) qz192 7)) Bool.false 13283585 2097152 62083 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz192) qz192 7) (Ns78p1444 (Ns78p1443 rfl) rfl rfl)) (Ns78p1478 rfl) rfl rfl)) 

theorem RS079to096.d52 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz192) Bool.false 985214334753048456035 147573952589676412928 14445505225828379058533 Ns78p310 := Ns78p1479 

noncomputable def Ns78p1480 := nat_lit 546930823222713752146149376 

noncomputable abbrev qz902 := (Enclosure.sfrac Bool.false 310176 1000)

noncomputable abbrev qz747 := qz902

noncomputable abbrev qz543 := qz747

noncomputable abbrev qz206 := qz543

noncomputable abbrev qz903 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 310176 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz748 := qz903

noncomputable abbrev qz544 := qz748

noncomputable abbrev qz207 := qz544

noncomputable abbrev qz904 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 310176 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz749 := qz904

noncomputable abbrev qz545 := qz749

noncomputable abbrev qz208 := qz545

noncomputable abbrev qz750 := (@HMul.hMul Real Real Real qz5 qz193 (@HPow.hPow Real Real Real qz7 qz207 qz9))

noncomputable def Ns78p1481 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 7) (@HMul.hMul Real Real Real qz5 qz750 (Zeta.RiemannSiegel.correction qz208)) 9167417 16777216 31209 16777216 48037835270469177975 147573952589676412928 738639254781613415975 Ns78p62 Ns78p1480 

noncomputable def Ns78p1482 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 310176 1000 67 98 67108864 33554432 1125899906842624 Bool.false 30148538847 1227 

noncomputable def Ns78p1483 := Ns78p1482 120242927 62 27397080 8 130587807 62 25364760 8 Bool.true 21018133 46314 Bool.true 85169354 Bool.true 26057784 3537118876014220 1 Bool.false 64078256 Bool.false Bool.false 62113103 Bool.true Bool.true 18334834 

noncomputable def Ns78p1484 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 310176 1000 12 31 67108864 33554432 1125899906842624 Bool.false 30148538847 1227 

noncomputable def Ns78p1485 := Ns78p1484 93032624 61 33554424 8 108007536 61 30011992 8 Bool.true 80506610 27209 Bool.false 27079380 Bool.true 84961570 3537118876014220 1 Bool.false 61719137 Bool.false Bool.false 64016212 Bool.false Bool.true 21018133 

noncomputable def Ns78p1486 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 310176 1000 149 69 67108864 33554432 1125899906842624 Bool.false 30148538847 1227 

noncomputable def Ns78p1487 := Ns78p1486 46516304 61 47453136 16 73726608 61 38745320 8 Bool.true 67108848 1301 Bool.false 13558534 Bool.false 6723846 3537118876014220 1 Bool.false 13466480 Bool.true Bool.false 6712601 Bool.true Bool.true 80506610 

noncomputable def Ns78p1488 := nat_lit 13746393183156441568019055722832951049276207208523 

noncomputable def Ns78p1489 := nat_lit 30598658040415453531137316699034583478304768000 

noncomputable def Ns78p1490 := nat_lit 1378113704580765215756070420480000 

noncomputable def Ns78p1491 := nat_lit 2564749888738049955854526257992826880 

noncomputable abbrev qz546 := (@Eq.refl Real qz747)

noncomputable abbrev qz209 := qz546

noncomputable def Ns78p1492 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz206 310176 1000 384837603904 16000000 620352 4000 2000 Ns78p1490 Ns78p1491 qz209 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns78p1493 := nat_lit 162159052257241299828305430453284450393765792811197399040 

noncomputable abbrev qz547 := (Enclosure.sfrac Bool.false 310176 2000)

noncomputable abbrev qz751 := (Real.log (Enclosure.sfrac Bool.false 384837603904 16000000))

noncomputable abbrev qz210 := (@HSub.hSub Real Real Real qz339 (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 310176 4000) qz751) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 620352)))))) qz547)

noncomputable abbrev qz548 := (@HSub.hSub Real Real Real qz12 qz210 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 310176 2000) (Real.log Real.pi)))

noncomputable def Ns78p1494 := @Enclosure.Real.IsNear.addLit_ft_p qz548 (Enclosure.sfrac Bool.true Ns78p1490 Ns78p1491) 63226144163823703683 140737488355328000 10564484911648322297 578592000000000000000000 Ns78p1490 Ns78p1491 0 1 Ns78p1493 

noncomputable def Ns78p1495 := nat_lit 26518966937090241565242163200 

noncomputable abbrev qz549 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 310176 2000) (Real.log Real.pi))

noncomputable def Ns78p1496 := @Enclosure.Real.IsNear.subLit_ff_p qz210 qz549 17642362969220098791 28147497671065600 163000019631283021 18081000000000000000000 372315506373 2097152000 9693 1048576000 Ns78p1495 63226144163823703683 140737488355328000 

noncomputable abbrev qz211 := (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 310176 4000) qz751) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 620352))))))

noncomputable def Ns78p1497 := @Enclosure.Real.IsNear.subLit_ff_p qz211 qz547 110038510440151602819 140737488355328000 163000019631283021 18081000000000000000000 310176 2000 0 1 176423629692200987910000 17642362969220098791 28147497671065600 163000019631283021 18081000000000000000000 

noncomputable def Ns78p1498 := nat_lit 495569394614671192243134956751028224 

noncomputable def Ns78p1499 := nat_lit 12195629115854516798881792 

noncomputable def Ns78p1500 := nat_lit 29011305100973275867931402401877796721348379429536619006096352135513737922468291362894017745387520 

noncomputable def Ns78p1501 := nat_lit 355483701703589020839795781525379511349360147181977796851529317924681490476342562438440481193984 

noncomputable def Ns78p1502 := nat_lit 5392183774062271092670458392574009372002668251648954806990774793507522877595923764247265280 

noncomputable def Ns78p1503 := BSN.log_dyadic_bound 122693603904 646981603904 5 4 Ns78p1500 33554432 8823528 Ns78p1501 Ns78p1502 12882467 769675207808 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 122693603904) (BSN.artanhQ 646981603904) 0 4 Ns78p1501 Ns78p1500 Ns78p1502 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns78p1504 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 310176 4000) qz751 310176 4000 0 1 22716129414466241 2251799813685248 62500007720587 551470500000000000000 220187442414421274013 281474976710656000 67312508315072199 7659312500000000000000 (Enclosure.Real.IsNear.const Bool.false 310176 4000) (BSN.isNear_log_sfrac 384837603904 16000000 22716129414466241 2251799813685248 62500007720587 551470500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 384837603904) qz347)) Bool.false Ns78p1499 Ns78p84 1000000123529392 8823528000000000000000 22716129414466241 2251799813685248 62500007720587 551470500000000000000 (BSN.log_rat_reduce_isNear 384837603904 16000000 14 769675207808 524288000000 12882467 33554432 24973259072661432 36028797018963968 8823528 1000000000000000 rfl rfl rfl rfl (Ns78p1503 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns78p1505 := BSN.arctan_dyadic_bound_f 1000 620352 1 0 4194304 1102941 0 1 1 0 1 1 6761 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 620352) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 620352) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz550 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 620352)))

noncomputable def Ns78p1506 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz550 884279719003555 562949953421312 1 2000000000000000 6761 4194304 1 1102941 3705131857900405260288 883372272944547 562949953421312 2000000001102941 2205882000000000000000 qz17 (Ns78p1505 rfl) rfl rfl 

noncomputable def Ns78p1507 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 310176 4000) qz751) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz550)) 220187442414421274013 281474976710656000 67312508315072199 7659312500000000000000 883372272944547 2251799813685248 2000000001102941 8823528000000000000000 Ns78p1498 110038510440151602819 140737488355328000 163000019631283021 18081000000000000000000 (Ns78p1504 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz550) 1 4 0 1 883372272944547 562949953421312 2000000001102941 2205882000000000000000 883372272944547 2251799813685248 2000000001102941 8823528000000000000000 qz350 Ns78p1506 rfl) 

noncomputable def Ns78p1508 := @Ns78p1494 Ns78p1488 Ns78p1489 10564484911648322297 578592000000000000000000 (@Ns78p1496 10564484911648322297 578592000000000000000000 (Ns78p1497 (Ns78p1507 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 310176 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz547 (Real.log Real.pi) 310176 2000 0 1 38410761 33554432 1 16777216 372315506373 2097152000 9693 1048576000 (Enclosure.Real.IsNear.const Bool.false 310176 2000) RS079to096.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns78p1490 Ns78p1491) 

noncomputable def Ns78p1509 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz206) Bool.false Ns78p1488 Ns78p1489 10564484911648322297 578592000000000000000000 3768567355 8388608 155 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz206) (@HAdd.hAdd Real Real Real qz351 qz548 (Enclosure.sfrac Bool.true Ns78p1490 Ns78p1491)) Bool.false Ns78p1488 Ns78p1489 10564484911648322297 578592000000000000000000 Ns78p1492 (Ns78p1508 rfl rfl)) 

noncomputable def Ns78p1510 := nat_lit 1899565649177476239196160 

noncomputable def Ns78p1511 := nat_lit 140163125366792224805462902230013212589762322287691332353806417627308751131565632364800 

noncomputable def Ns78p1512 := nat_lit 281965552968386067690896934795231658599335764633261089854784211877244541055277834496 

noncomputable def Ns78p1513 := nat_lit 366637384112983201809474720327032800764026205229785352495442395538007380849534777794816 

noncomputable def Ns78p1514 := BSN.sin_dyadic_bound_f 26994451462 17179869184 3 2 8388608 2208037 Ns78p1511 Ns78p97 Ns78p1512 Ns78p1513 Ns78p100 Ns78p1512 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26994451462) qz352 0 2 Ns78p1511 Ns78p97 Ns78p1512 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26994451462) qz353 0 2 Ns78p1513 Ns78p100 Ns78p1512 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1515 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz206) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3768567355) qz354) Bool.false 3768567355 8388608 155 8388608 Bool.true 8388606 8388608 1 1102941 (Ns78p1509 rfl) (Enclosure.sfrac_false_div 3768567355 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3768567355) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns78p1510) qz355) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 71 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q1 3768567355 8388608 226375608064910080 72057594037927936 71 Ns78p1510 Ns78p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388606 8388608 Ns78p1510 Ns78p84 26994451462 17179869184 2208037 2205882 (Ns78p1514 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p1516 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz206) Bool.false Ns78p1488 Ns78p1489 10564484911648322297 578592000000000000000000 30148538847 67108864 1227 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz206) (@HAdd.hAdd Real Real Real qz351 qz548 (Enclosure.sfrac Bool.true Ns78p1490 Ns78p1491)) Bool.false Ns78p1488 Ns78p1489 10564484911648322297 578592000000000000000000 Ns78p1492 (Ns78p1508 rfl rfl)) 

noncomputable def Ns78p1517 := Ns78p1487 27209 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 149 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 13466480 67108864) BSN.abs_quadSignNeg qz635 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 6712601 67108864) qz209 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 1) Bool.true 4194303 4194304 179344463 9252139696128 67108848 67108864 1301 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz206)) Bool.true 4194303 4194304 179344463 9252139696128 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz206) qz206) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz206)) Bool.true 8388606 8388608 179344463 9252139696128 4194303 4194304 179344463 9252139696128 (Ns78p1515 rfl rfl) rfl)) rfl) (Ns78p1516 rfl) RS079to096.d7 

noncomputable def Ns78p1518 := nat_lit 33794882284069592763840472336 

noncomputable def Ns78p1519 := BSN.sin_dyadic_bound_f 13558534 67108864 2 1 67108864 33554432 Ns78p1518 Ns78p106 Ns78p1518 Ns78p1518 Ns78p107 Ns78p1518 13466480 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 13558534) qz356 0 1 Ns78p1518 Ns78p106 Ns78p1518 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 13558534) (BSN.sinOddQ 67108864) 0 1 Ns78p1518 Ns78p107 Ns78p1518 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1520 := nat_lit 2043953596978792381365904656 

noncomputable def Ns78p1521 := BSN.sin_dyadic_bound_f 6723846 67108864 2 1 67108864 33554432 Ns78p1520 Ns78p106 Ns78p1520 Ns78p1520 Ns78p107 Ns78p1520 6712601 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 6723846) qz356 0 1 Ns78p1520 Ns78p106 Ns78p1520 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 6723846) (BSN.sinOddQ 67108864) 0 1 Ns78p1520 Ns78p107 Ns78p1520 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1522 := nat_lit 18322745564167189142650421014170612824217777234637727936716800000 

noncomputable def Ns78p1523 := nat_lit 289141036402408272227061191019036265329826014347289600000000 

noncomputable def Ns78p1524 := nat_lit 54967658410428762611406808920129800400122672051884489230950400000 

noncomputable def Ns78p1525 := BSN.cos_dyadic_bound_f 27079380 67108864 3 2 67108864 33554432 Ns78p1522 Ns78p116 Ns78p1523 Ns78p1524 Ns78p119 Ns78p1523 61719137 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 27079380) qz357 0 2 Ns78p1522 Ns78p116 Ns78p1523 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 27079380) (BSN.cosOddQ 67108864) 0 2 Ns78p1524 Ns78p119 Ns78p1523 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1526 := nat_lit 3198602338673289388241687683627540179393928134562952461248391840000 

noncomputable def Ns78p1527 := nat_lit 2715065010262734979223590213758313904378559316804961040100000000 

noncomputable def Ns78p1528 := nat_lit 8372896019841999207809486692011758437805579827818619842538007200000 

noncomputable def Ns78p1529 := BSN.sin_dyadic_bound_f 84961570 67108864 3 2 67108864 33554432 Ns78p1526 Ns78p127 Ns78p1527 Ns78p1528 Ns78p130 Ns78p1527 64016212 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 84961570) qz356 0 2 Ns78p1526 Ns78p127 Ns78p1527 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 84961570) (BSN.sinOddQ 67108864) 0 2 Ns78p1528 Ns78p130 Ns78p1527 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1530 := Ns78p1485 46314 BSN.abs_quadSignPos (BSN.cos_quad_nat0 12 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 61719137 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 31 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 64016212 67108864) qz209 rfl rfl (Ns78p1517 RS079to096.d9 RS079to096.d11 RS079to096.d13 RS079to096.d17 (Ns78p1519 rfl rfl) (Ns78p1521 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns78p1516 rfl) RS079to096.d19 RS079to096.d21 RS079to096.d23 RS079to096.d25 RS079to096.d17 (Ns78p1525 rfl rfl) (Ns78p1529 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns78p1531 := nat_lit 3230034538179894978652242156282439129750603468320299563271516381440 

noncomputable def Ns78p1532 := nat_lit 2768642144417577513668503092069870128790531047254008389728788736 

noncomputable def Ns78p1533 := nat_lit 8455131703189715532876599499543036978662110128667135223556315341056 

noncomputable def Ns78p1534 := BSN.sin_dyadic_bound_f 85169354 67108864 3 2 67108864 33554432 Ns78p1531 Ns78p127 Ns78p1532 Ns78p1533 Ns78p130 Ns78p1532 64078256 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 85169354) qz356 0 2 Ns78p1531 Ns78p127 Ns78p1532 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 85169354) (BSN.sinOddQ 67108864) 0 2 Ns78p1533 Ns78p130 Ns78p1532 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1535 := nat_lit 15710305348998378299092371829448747329846980187272252128363544576 

noncomputable def Ns78p1536 := nat_lit 212568955334002909290398317714931860141514607426744820432896 

noncomputable def Ns78p1537 := nat_lit 47130490909084466891458534691710812125820657532601902895449767936 

noncomputable def Ns78p1538 := BSN.cos_dyadic_bound_f 26057784 67108864 3 2 67108864 33554432 Ns78p1535 Ns78p116 Ns78p1536 Ns78p1537 Ns78p119 Ns78p1536 62113103 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 26057784) qz357 0 2 Ns78p1535 Ns78p116 Ns78p1536 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 26057784) (BSN.cosOddQ 67108864) 0 2 Ns78p1537 Ns78p119 Ns78p1536 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1539 := Ns78p1483 62418 BSN.abs_quadSignPos qz734 (BSN.sfrac_eq_quadSignPos_mul Bool.false 64078256 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 98 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 62113103 67108864) qz209 rfl rfl (Ns78p1530 rfl rfl) (Ns78p1516 rfl) RS079to096.d27 RS079to096.d29 RS079to096.d49 RS079to096.d51 RS079to096.d17 (Ns78p1534 rfl rfl) (Ns78p1538 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns78p1540 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 7) 18334834 67108864 62418 67108864 18334834 67108864 62418 67108864 2460859762737152 9167417 16777216 31209 16777216 (Ns78p1539 rfl) 

noncomputable def Ns78p1541 := @Enclosure.Real.IsNear.mulLit_tf qz750 (Zeta.RiemannSiegel.correction qz208) 1582351 4194304 1 4194304 30358520499225 35184372088832 229872378521225 6467714422671409152 48037835270469177975 147573952589676412928 

noncomputable abbrev qz752 := (@HPow.hPow Real Real Real qz7 qz207 qz9)

noncomputable def Ns78p1542 := @Enclosure.Real.IsNear.mulLit_tf qz193 qz752 1 1 0 1 1582351 4194304 1 4194304 1582351 4194304 1 4194304 

noncomputable def Ns78p1543 := @Enclosure.Real.IsNear.sqrt_image qz207 12941017677 262144000 9693 262144000 29469583 29469606 4194304 (@Enclosure.Real.IsNear.of_eq qz207 (@HMul.hMul Real Real Real qz5 qz206 qz3) Bool.false 12941017677 262144000 9693 262144000 (BSN.t_div_two_pi_mk qz206 310176 1000 qz209) (@Enclosure.Real.IsNear.mulLit_ff qz206 qz3 310176 1000 0 1 1335089 8388608 1 8388608 12941017677 262144000 9693 262144000 (Enclosure.Real.IsNear.const Bool.false 310176 1000) RS079to096.d32 rfl)) 

noncomputable abbrev qz905 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 310176 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz753 := qz905

noncomputable abbrev qz551 := qz753

noncomputable abbrev qz212 := qz551

noncomputable def Ns78p1544 := @Enclosure.Real.IsNear.sqrt_image qz212 58939189 8388608 23 8388608 11117751 11117756 4194304 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 58939189 8388608 23 8388608 58939189 8388608 23 8388608 (Ns78p1543 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns78p1545 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz212) 22235507 8388608 5 8388608 1582350 1582352 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz212) Bool.false 22235507 8388608 5 8388608 22235507 8388608 5 8388608 (Ns78p1544 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns78p1546 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz212)) Bool.false 3164702 8388608 2 8388608 1582351 4194304 1 4194304 (Ns78p1545 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz336 qz334 qz545)

noncomputable abbrev qz754 := (@HMul.hMul Real Real Real qz841 qz904 qz904)

noncomputable abbrev qz552 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz754 qz749) qz640)

noncomputable abbrev qz214 := (Real.cos (@HMul.hMul Real Real Real qz336 qz334 qz552))

noncomputable def Ns78p1547 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz208) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz213)) qz214) Bool.false 30358520499225 

noncomputable def Ns78p1548 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz213)) qz214 8502675 8388608 159 

noncomputable def Ns78p1549 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz213)) Bool.false 8502675 8388608 159 8388608 8502675 8388608 159 

noncomputable def Ns78p1550 := @Enclosure.Real.IsNear.recentre' (Real.cos qz213) Bool.false 4138036 4194304 84708997 4626069848064 1034509 1048576 84708997 4626069848064 

noncomputable def Ns78p1551 := @Enclosure.Real.IsNear.cos_image qz213 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 343899) qz398) Bool.false 343899 2097152 73 4194304 Bool.false 4138036 4194304 1 

noncomputable def Ns78p1552 := nat_lit 620679734409893665618916577 

noncomputable def Ns78p1553 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz208 884279719003555 140737488355328 1 500000000000000 218933 8388608 23 8388608 193598011720605306815 1180591620717411303424 Ns78p1552 

noncomputable def Ns78p1554 := @Enclosure.Real.IsNear.subLit_ff_p qz212 qz191 58939189 8388608 23 8388608 7 1 0 1 218933 218933 8388608 23 

noncomputable def Ns78p1555 := @Ns78p1554 8388608 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 58939189 8388608 23 8388608 58939189 8388608 23 8388608 (Ns78p1543 rfl rfl rfl rfl rfl rfl) rfl) qz539 

noncomputable def Ns78p1556 := @Enclosure.Real.IsNear.recentre' qz213 Bool.false 193598011720605306815 1180591620717411303424 Ns78p1552 Ns78p385 343899 2097152 73 4194304 (@Ns78p1553 Ns78p385 RS079to096.d31 (Ns78p1555 rfl rfl) rfl) 

noncomputable def Ns78p1557 := BSN.cos_dyadic_bound_f 343899 2097152 2 1 4194304 1102941 13986970273519625884401 Ns78p1474 13986970273519625884401 13986970273519625884401 Ns78p1475 13986970273519625884401 4138036 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 343899) (BSN.cosEvenQ 2097152) 0 1 13986970273519625884401 Ns78p1474 13986970273519625884401 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 343899) (BSN.cosOddQ 2097152) 0 1 13986970273519625884401 Ns78p1475 13986970273519625884401 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1558 := @Enclosure.Real.IsNear.inv_image (Real.cos qz213) 1034509 1048576 84708997 4626069848064 4251258 4251417 4194304 (Ns78p1550 (@Ns78p1551 1102941 (Ns78p1556 rfl) (Enclosure.sfrac_false_div 343899 2097152) (Ns78p1557 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns78p1559 := @Enclosure.Real.IsNear.recentre' qz214 Bool.false 3570467 4194304 

noncomputable abbrev qz215 := (@HMul.hMul Real Real Real qz336 qz334 qz552)

noncomputable def Ns78p1560 := @Enclosure.Real.IsNear.cos_image qz215 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 4633893)) qz354) Bool.true 4633893 8388608 

noncomputable def Ns78p1561 := nat_lit 5470736169407146715076809845 

noncomputable def Ns78p1562 := nat_lit 1095685562753253381815828849299629 

noncomputable def Ns78p1563 := @Enclosure.Real.IsNear.recentre' qz215 Bool.true Ns78p1561 Ns78p397 Ns78p1562 

noncomputable abbrev qz216 := qz552

noncomputable def Ns78p1564 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz216 884279719003555 140737488355328 1 500000000000000 6186657967879 

noncomputable abbrev qz553 := (@HSub.hSub Real Real Real qz634 qz754 qz749)

noncomputable abbrev qz217 := qz553

noncomputable def Ns78p1565 := @Enclosure.Real.IsNear.subLit_tf qz217 qz26 1788611456775 70368744177664 203009431 70368744177664 1 16 

noncomputable abbrev qz554 := qz754

noncomputable abbrev qz218 := qz554

noncomputable def Ns78p1566 := @Enclosure.Real.IsNear.subLit_ff_n qz218 qz208 47931658489 70368744177664 10071447 70368744177664 218933 8388608 23 8388608 

noncomputable def Ns78p1567 := @Enclosure.Real.IsNear.mulLit_ff qz208 qz208 218933 8388608 23 8388608 218933 8388608 23 8388608 47931658489 70368744177664 

noncomputable def Ns78p1568 := nat_lit 461088197351464714198031601 

noncomputable def Ns78p1569 := BSN.cos_dyadic_bound_f 4633893 8388608 2 1 4194304 1102941 Ns78p1568 Ns78p1461 Ns78p1568 Ns78p1568 Ns78p1462 Ns78p1568 3570467 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 4633893) (BSN.cosEvenQ 8388608) 0 1 Ns78p1568 Ns78p1461 Ns78p1568 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 4633893) (BSN.cosOddQ 8388608) 0 1 Ns78p1568 Ns78p1462 Ns78p1568 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1570 := @Ns78p1559 177138581 9252139696128 3570467 4194304 177138581 9252139696128 (@Ns78p1560 153 8388608 Bool.false 3570467 4194304 1 1102941 (@Ns78p1563 Ns78p400 4633893 8388608 153 8388608 (@Ns78p1564 70368744177664 203009431 70368744177664 Ns78p1561 Ns78p397 Ns78p1562 Ns78p400 RS079to096.d31 (@Ns78p1565 0 1 98986527486064 6186657967879 70368744177664 203009431 70368744177664 (@Ns78p1566 15003960375194419200 1788611456775 70368744177664 203009431 70368744177664 (@Ns78p1567 10071447 70368744177664 (Ns78p1555 rfl rfl) (Ns78p1555 rfl rfl) rfl) (Ns78p1555 rfl rfl) rfl rfl) qz366 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 4633893 8388608) (BSN.cos_neg_of_bound 4633893 8388608 Bool.false 3570467 4194304 1 1102941 (Ns78p1569 rfl rfl)) rfl rfl) 

noncomputable def Ns78p1571 := @Ns78p1541 738639254781613415975 Ns78p62 (Ns78p1542 qz542 (@Enclosure.Real.IsNear.of_eq qz752 (@Inv.inv Real Real.instInv (Real.sqrt qz212)) Bool.false 1582351 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz207 (BSN.t_div_two_pi_nonneg qz206 310176 1000 qz209)) Ns78p1546) rfl) (@Ns78p1547 35184372088832 229872378521225 6467714422671409152 (BSN.correction_mk qz208 (BSN.cos_two_pi_p_ne_zero_mk qz206 310176 1000 7 qz209 rfl rfl (@BSN.floor_sqrt_eq_dec qz206 310176 1000 7 qz209 rfl rfl rfl))) (@Ns78p1548 8388608 3570467 4194304 177138581 9252139696128 30358520499225 35184372088832 229872378521225 6467714422671409152 (@Ns78p1549 8388608 (Ns78p1558 rfl rfl rfl rfl rfl) rfl) (Ns78p1570 rfl) rfl)) 

noncomputable def Ns78p1572 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz206) (hardyZApproximantRS₀ qz206) Bool.true 32599617434901818761 147573952589676412928 101664088963357617528359 Ns78p62 (@Eq.refl Real (hardyZApproximantRS₀ qz206)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz206) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 7) (@HMul.hMul Real Real Real qz5 qz750 (Zeta.RiemannSiegel.correction qz208))) Bool.true 32599617434901818761 147573952589676412928 101664088963357617528359 Ns78p62 (BSN.hardyZApproximantRS₀_eq qz206 7 (@BSN.floor_sqrt_eq_dec qz206 310176 1000 7 qz209 rfl rfl rfl)) (@Ns78p1481 32599617434901818761 147573952589676412928 101664088963357617528359 Ns78p62 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 7) (@HAdd.hAdd Real Real Real qz351 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 7)) Bool.true 9167417 16777216 31209 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz206) qz206 7) (Ns78p1540 (Ns78p1539 rfl) rfl rfl)) (Ns78p1571 rfl) rfl rfl)) 

theorem RS079to096.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz206) Bool.true 32599617434901818761 147573952589676412928 101664088963357617528359 Ns78p62 := Ns78p1572 

noncomputable def Ns78p1573 := nat_lit 33796692076333333439578112 

noncomputable abbrev qz906 := (Enclosure.sfrac Bool.false 311786 1000)

noncomputable abbrev qz755 := qz906

noncomputable abbrev qz555 := qz755

noncomputable abbrev qz219 := qz555

noncomputable abbrev qz907 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 311786 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz756 := qz907

noncomputable abbrev qz556 := qz756

noncomputable abbrev qz220 := qz556

noncomputable abbrev qz908 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 311786 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz757 := qz908

noncomputable abbrev qz557 := qz757

noncomputable abbrev qz221 := qz557

noncomputable abbrev qz758 := (@HMul.hMul Real Real Real qz5 qz193 (@HPow.hPow Real Real Real qz7 qz220 qz9))

noncomputable def Ns78p1574 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz219) qz219 7) (@HMul.hMul Real Real Real qz5 qz758 (Zeta.RiemannSiegel.correction qz221)) 9458329 16777216 62731 33554432 714496986439239069 2305843009213693952 1131139728357265027717 Ns78p1188 Ns78p1573 

noncomputable def Ns78p1575 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz219) qz219 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 311786 1000 67 98 67108864 33554432 1125899906842624 Bool.false 30359327310 1232 

noncomputable def Ns78p1576 := Ns78p1575 120242927 62 27397080 8 130587807 62 25364760 8 Bool.false 19227681 46544 Bool.true 67972004 Bool.true 25515690 3537118876014220 1 Bool.false 56931834 Bool.false Bool.false 62316315 Bool.true Bool.false 18916658 

noncomputable def Ns78p1577 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz219) qz219 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 311786 1000 12 31 67108864 33554432 1125899906842624 Bool.false 30359327310 1232 

noncomputable def Ns78p1578 := Ns78p1577 93032624 61 33554424 8 108007536 61 30011992 8 Bool.true 9045062 27342 Bool.false 88085318 Bool.true 48065240 3537118876014220 1 Bool.false 17137099 Bool.false Bool.false 44059928 Bool.false Bool.false 19227681 

noncomputable def Ns78p1579 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz219) qz219 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 311786 1000 150 69 67108864 33554432 1125899906842624 Bool.false 30359327310 1232 

noncomputable def Ns78p1580 := Ns78p1579 46516304 61 47453136 16 73726608 61 38745320 8 Bool.false 67108856 1301 Bool.false 44041391 Bool.false 98812470 3537118876014220 1 Bool.false 53168672 Bool.true Bool.false 66784392 Bool.true Bool.true 9045062 

noncomputable def Ns78p1581 := nat_lit 263194966826226076911539526583479792920601878221727969 

noncomputable def Ns78p1582 := nat_lit 581788754862166450423903523217579227684259495936000 

noncomputable def Ns78p1583 := nat_lit 1414253032137050208758338964480000 

noncomputable def Ns78p1584 := nat_lit 2645668950491046645874591937252167680 

noncomputable abbrev qz759 := (@Eq.refl Real qz906)

noncomputable abbrev qz558 := qz759

noncomputable abbrev qz222 := qz558

noncomputable def Ns78p1585 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz219 311786 1000 388843039184 16000000 623572 4000 2000 Ns78p1583 Ns78p1584 qz222 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns78p1586 := nat_lit 5390232920601110055148329504429666159013926465980988805120 

noncomputable abbrev qz760 := (Real.log (Enclosure.sfrac Bool.false 388843039184 16000000))

noncomputable abbrev qz223 := (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 311786 4000) qz760) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 623572))))))

noncomputable abbrev qz761 := (Enclosure.sfrac Bool.false 311786 2000)

noncomputable abbrev qz559 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz223 qz761) (@HMul.hMul Real Real Real qz5 qz761 (Real.log Real.pi)))

noncomputable def Ns78p1587 := @Enclosure.Real.IsNear.addLit_ft_p qz559 (Enclosure.sfrac Bool.true Ns78p1583 Ns78p1584) 2037382375005795344709 4503599627370496000 10363792842899366027917 Ns78p804 Ns78p1583 Ns78p1584 0 1 Ns78p1586 

noncomputable def Ns78p1588 := nat_lit 68363208360130459499954700288000 

noncomputable abbrev qz560 := (@HSub.hSub Real Real Real qz12 qz223 qz761)

noncomputable abbrev qz561 := (@HMul.hMul Real Real Real qz5 qz761 (Real.log Real.pi))

noncomputable def Ns78p1589 := @Enclosure.Real.IsNear.subLit_ff_p qz560 qz561 2841073937921750294853 4503599627370496000 624582106482708551 68933812500000000000000 5987968764573 33554432000 155893 16777216000 Ns78p1588 2037382375005795344709 4503599627370496000 

noncomputable def Ns78p1590 := nat_lit 5682147875843500589706000 

noncomputable abbrev qz562 := qz761

noncomputable def Ns78p1591 := @Enclosure.Real.IsNear.subLit_ff_p qz223 qz562 3543153594631419027781 4503599627370496000 624582106482708551 68933812500000000000000 311786 2000 0 1 Ns78p1590 2841073937921750294853 4503599627370496000 624582106482708551 68933812500000000000000 

noncomputable def Ns78p1592 := nat_lit 7978472604249246085095888230901874688 

noncomputable def Ns78p1593 := nat_lit 12208146744918003526139904 

noncomputable def Ns78p1594 := nat_lit 142084896225825210408755763750988301583878876139475605226214989922823284817390941570713195411338788784055142928044544491520 

noncomputable def Ns78p1595 := nat_lit 1835936101018311541637657594023809347191640905242078749747871719759750738901530897652098482484511672611160705940643119104 

noncomputable def Ns78p1596 := nat_lit 1007314354847607048007177302676158858491038551934054065989262085674759331918201543985542413477753805310330740408320 

noncomputable def Ns78p1597 := BSN.log_dyadic_bound 126699039184 650987039184 6 5 Ns78p1594 33554432 8823528 Ns78p1595 Ns78p1596 13229901 777686078368 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 126699039184) (BSN.artanhQ 650987039184) 0 5 Ns78p1595 Ns78p1594 Ns78p1596 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns78p1598 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 311786 4000) qz760 311786 4000 0 1 22739445315521217 2251799813685248 62500007720587 551470500000000000000 3544920348572549081781 4503599627370496000 9743313703585469191 1102941000000000000000000 (Enclosure.Real.IsNear.const Bool.false 311786 4000) (BSN.isNear_log_sfrac 388843039184 16000000 22739445315521217 2251799813685248 62500007720587 551470500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 388843039184) qz347)) Bool.false Ns78p1593 Ns78p84 1000000123529392 8823528000000000000000 22739445315521217 2251799813685248 62500007720587 551470500000000000000 (BSN.log_rat_reduce_isNear 388843039184 16000000 14 777686078368 524288000000 13229901 33554432 24973259072661432 36028797018963968 8823528 1000000000000000 rfl rfl rfl rfl (Ns78p1597 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns78p1599 := BSN.arctan_dyadic_bound_f 1000 623572 1 0 4194304 1102941 0 1 1 0 1 1 6726 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 623572) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 623572) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz563 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 623572)))

noncomputable def Ns78p1600 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz563 884279719003555 562949953421312 1 2000000000000000 6726 4194304 1 1102941 3705151561148775006208 883376970565027 562949953421312 2000000001102941 2205882000000000000000 qz17 (Ns78p1599 rfl) rfl rfl 

noncomputable def Ns78p1601 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 311786 4000) qz760) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz563)) 3544920348572549081781 4503599627370496000 9743313703585469191 1102941000000000000000000 883376970565027 2251799813685248 2000000001102941 8823528000000000000000 Ns78p1592 3543153594631419027781 4503599627370496000 624582106482708551 68933812500000000000000 (Ns78p1598 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz563) 1 4 0 1 883376970565027 562949953421312 2000000001102941 2205882000000000000000 883376970565027 2251799813685248 2000000001102941 8823528000000000000000 qz350 Ns78p1600 rfl) 

noncomputable def Ns78p1602 := @Ns78p1587 Ns78p1581 Ns78p1582 10363792842899366027917 Ns78p804 (@Ns78p1589 10363792842899366027917 Ns78p804 (Ns78p1591 (Ns78p1601 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 311786 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz562 (Real.log Real.pi) 311786 2000 0 1 38410761 33554432 1 16777216 5987968764573 33554432000 155893 16777216000 (Enclosure.Real.IsNear.const Bool.false 311786 2000) RS079to096.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns78p1583 Ns78p1584) 

noncomputable def Ns78p1603 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz219) Bool.false Ns78p1581 Ns78p1582 10363792842899366027917 Ns78p804 3794915913 8388608 155 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz219) (@HAdd.hAdd Real Real Real qz351 qz559 (Enclosure.sfrac Bool.true Ns78p1583 Ns78p1584)) Bool.false Ns78p1581 Ns78p1582 10363792842899366027917 Ns78p804 Ns78p1585 (Ns78p1602 rfl rfl)) 

noncomputable def Ns78p1604 := nat_lit 1898840567238734649491456 

noncomputable def Ns78p1605 := nat_lit 139948811964304372995198624592942003379774880997864604961148342915416583343782005637120 

noncomputable def Ns78p1606 := nat_lit 281105671353173295592334625525779695538675137851805071469586172397771418659140468736 

noncomputable def Ns78p1607 := nat_lit 366077479295749172508846903587806365535204928580742471449199663356494659793980930195456 

noncomputable def Ns78p1608 := BSN.sin_dyadic_bound_f 26984147428 17179869184 3 2 8388608 2208037 Ns78p1605 Ns78p97 Ns78p1606 Ns78p1607 Ns78p100 Ns78p1606 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26984147428) qz352 0 2 Ns78p1605 Ns78p97 Ns78p1606 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26984147428) qz353 0 2 Ns78p1607 Ns78p100 Ns78p1606 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1609 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz219) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3794915913) qz354) Bool.false 3794915913 8388608 155 8388608 Bool.false 8388607 8388608 1 1102941 (Ns78p1603 rfl) (Enclosure.sfrac_false_div 3794915913 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3794915913) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns78p1604) qz355) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 71 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q3 3794915913 8388608 226375608064910080 72057594037927936 71 Ns78p1604 Ns78p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns78p1604 Ns78p84 26984147428 17179869184 2208037 2205882 (Ns78p1608 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p1610 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz219) Bool.false Ns78p1581 Ns78p1582 10363792842899366027917 Ns78p804 30359327310 67108864 1232 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz219) (@HAdd.hAdd Real Real Real qz351 qz559 (Enclosure.sfrac Bool.true Ns78p1583 Ns78p1584)) Bool.false Ns78p1581 Ns78p1582 10363792842899366027917 Ns78p804 Ns78p1585 (Ns78p1602 rfl rfl)) 

noncomputable def Ns78p1611 := Ns78p1580 27342 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 150 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 53168672 67108864) BSN.abs_quadSignNeg qz635 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66784392 67108864) qz222 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz219) qz219 1) Bool.false 8388607 8388608 179344463 9252139696128 67108856 67108864 1301 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz219) qz219 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz219)) Bool.false 8388607 8388608 179344463 9252139696128 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz219) qz219) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz219)) Bool.false 8388607 8388608 179344463 9252139696128 8388607 8388608 179344463 9252139696128 (Ns78p1609 rfl rfl) rfl)) rfl) (Ns78p1610 rfl) RS079to096.d7 

noncomputable def Ns78p1612 := nat_lit 128209701279300018317480564346193942690201258485964880459006121601 

noncomputable def Ns78p1613 := nat_lit 14154294188932913040823547426004101134296373124302383357793921 

noncomputable def Ns78p1614 := nat_lit 384600795249522189126360045943729819868335182711646036610302776961 

noncomputable def Ns78p1615 := BSN.cos_dyadic_bound_f 44041391 67108864 3 2 67108864 33554432 Ns78p1612 Ns78p116 Ns78p1613 Ns78p1614 Ns78p119 Ns78p1613 53168672 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 44041391) qz357 0 2 Ns78p1612 Ns78p116 Ns78p1613 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 44041391) (BSN.cosOddQ 67108864) 0 2 Ns78p1614 Ns78p119 Ns78p1613 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1616 := nat_lit 2038261453608206545798901884271145787021906247834056281335764111817620342187886047672658383128742400000 

noncomputable def Ns78p1617 := nat_lit 866445130054143684494309952089987729367356051822308291791543427393222378478154381441000000000000 

noncomputable def Ns78p1618 := nat_lit 10181526543530402629590219463795018182308919855362490786490322131247194686713191110285146174939712000000 

noncomputable def Ns78p1619 := BSN.sin_dyadic_bound_f 98812470 67108864 4 3 67108864 33554432 Ns78p1616 Ns78p941 Ns78p1617 Ns78p1618 Ns78p944 Ns78p1617 66784392 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 98812470) qz356 0 3 Ns78p1616 Ns78p941 Ns78p1617 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 98812470) (BSN.sinOddQ 67108864) 0 3 Ns78p1618 Ns78p944 Ns78p1617 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1620 := nat_lit 495160221713340438393336933988562314626901750952895373767933681006145996815627772941148434775836921856 

noncomputable def Ns78p1621 := nat_lit 218193756075643557582692059210589835680262680284794400660150232308605690259013878634619525861376 

noncomputable def Ns78p1622 := nat_lit 3000438886845872240409270992197801030570870630670733327076076123834659898360316343591344165422128107520 

noncomputable def Ns78p1623 := BSN.cos_dyadic_bound_f 88085318 67108864 4 3 67108864 33554432 Ns78p1620 Ns78p110 Ns78p1621 Ns78p1622 Ns78p113 Ns78p1621 17137099 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 88085318) qz357 0 3 Ns78p1620 Ns78p110 Ns78p1621 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 88085318) (BSN.cosOddQ 67108864) 0 3 Ns78p1622 Ns78p113 Ns78p1621 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1624 := nat_lit 327388626265268646619529298240665059531560098549814450548899840000 

noncomputable def Ns78p1625 := nat_lit 28487144690411807616648152553047408020439481307896217600000000 

noncomputable def Ns78p1626 := nat_lit 857400280079538169648340255526179745826814784660729824228147200000 

noncomputable def Ns78p1627 := BSN.sin_dyadic_bound_f 48065240 67108864 3 2 67108864 33554432 Ns78p1624 Ns78p127 Ns78p1625 Ns78p1626 Ns78p130 Ns78p1625 44059928 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 48065240) qz356 0 2 Ns78p1624 Ns78p127 Ns78p1625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 48065240) (BSN.sinOddQ 67108864) 0 2 Ns78p1626 Ns78p130 Ns78p1625 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1628 := Ns78p1578 46544 BSN.abs_quadSignPos (BSN.cos_quad_nat0 12 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 17137099 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 31 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 44059928 67108864) qz222 rfl rfl (Ns78p1611 RS079to096.d9 RS079to096.d11 RS079to096.d13 RS079to096.d17 (Ns78p1615 rfl rfl) (Ns78p1619 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns78p1610 rfl) RS079to096.d19 RS079to096.d21 RS079to096.d23 RS079to096.d25 RS079to096.d17 (Ns78p1623 rfl rfl) (Ns78p1627 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns78p1629 := nat_lit 1309702797243219386131649814291766115735644849551432661858259107840 

noncomputable def Ns78p1630 := nat_lit 455659673226962460743584885258814108910654592131367432618049536 

noncomputable def Ns78p1631 := nat_lit 3429436258070826167313117042854682699321785927104587138547392249856 

noncomputable def Ns78p1632 := BSN.sin_dyadic_bound_f 67972004 67108864 3 2 67108864 33554432 Ns78p1629 Ns78p127 Ns78p1630 Ns78p1631 Ns78p130 Ns78p1630 56931834 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 67972004) qz356 0 2 Ns78p1629 Ns78p127 Ns78p1630 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 67972004) (BSN.sinOddQ 67108864) 0 2 Ns78p1631 Ns78p130 Ns78p1630 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1633 := nat_lit 14443202540823946039769133658607546140984787626083509522224800000 

noncomputable def Ns78p1634 := nat_lit 179662954314206583015313941504759165911072052409664100000000 

noncomputable def Ns78p1635 := nat_lit 43329248296563209706141370347939628904622540734145709238474400000 

noncomputable def Ns78p1636 := BSN.cos_dyadic_bound_f 25515690 67108864 3 2 67108864 33554432 Ns78p1633 Ns78p116 Ns78p1634 Ns78p1635 Ns78p119 Ns78p1634 62316315 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 25515690) qz357 0 2 Ns78p1633 Ns78p116 Ns78p1634 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 25515690) (BSN.cosOddQ 67108864) 0 2 Ns78p1635 Ns78p119 Ns78p1634 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1637 := Ns78p1576 62731 BSN.abs_quadSignPos qz734 (BSN.sfrac_eq_quadSignPos_mul Bool.false 56931834 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 98 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 62316315 67108864) qz222 rfl rfl (Ns78p1628 rfl rfl) (Ns78p1610 rfl) RS079to096.d27 RS079to096.d29 RS079to096.d49 RS079to096.d51 RS079to096.d17 (Ns78p1632 rfl rfl) (Ns78p1636 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns78p1638 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz219) qz219 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz219) qz219 7) 18916658 67108864 62731 67108864 18916658 67108864 62731 67108864 2538950858113024 9458329 16777216 62731 33554432 (Ns78p1637 rfl) 

noncomputable def Ns78p1639 := @Enclosure.Real.IsNear.mulLit_tf qz758 (Zeta.RiemannSiegel.correction qz221) 98769 262144 1 4194304 7234020658701 8796093022208 705675380637667 19403143268014227456 714496986439239069 2305843009213693952 

noncomputable abbrev qz762 := (@HPow.hPow Real Real Real qz7 qz220 qz9)

noncomputable def Ns78p1640 := @Enclosure.Real.IsNear.mulLit_tf qz193 qz762 1 1 0 1 98769 262144 1 4194304 98769 262144 1 4194304 

noncomputable def Ns78p1641 := @Enclosure.Real.IsNear.sqrt_image qz220 208131029477 4194304000 155893 4194304000 29545966 29545989 4194304 (@Enclosure.Real.IsNear.of_eq qz220 (@HMul.hMul Real Real Real qz5 qz219 qz3) Bool.false 208131029477 4194304000 155893 4194304000 (BSN.t_div_two_pi_mk qz219 311786 1000 qz222) (@Enclosure.Real.IsNear.mulLit_ff qz219 qz3 311786 1000 0 1 1335089 8388608 1 8388608 208131029477 4194304000 155893 4194304000 (Enclosure.Real.IsNear.const Bool.false 311786 1000) RS079to096.d32 rfl)) 

noncomputable abbrev qz909 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 311786 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz763 := qz909

noncomputable abbrev qz564 := qz763

noncomputable abbrev qz224 := qz564

noncomputable def Ns78p1642 := @Enclosure.Real.IsNear.sqrt_image qz224 59091955 8388608 23 8388608 11132149 11132155 4194304 (@Enclosure.Real.IsNear.recentre' qz224 Bool.false 59091955 8388608 23 8388608 59091955 8388608 23 8388608 (Ns78p1641 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns78p1643 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz224) 1391519 524288 3 4194304 1580303 1580305 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz224) Bool.false 22264304 8388608 6 8388608 1391519 524288 3 4194304 (Ns78p1642 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns78p1644 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz224)) Bool.false 3160608 8388608 2 8388608 98769 262144 1 4194304 (Ns78p1643 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz225 := (@HMul.hMul Real Real Real qz336 qz334 qz557)

noncomputable abbrev qz764 := (@HMul.hMul Real Real Real qz841 qz908 qz908)

noncomputable abbrev qz565 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz764 qz757) qz640)

noncomputable abbrev qz226 := (Real.cos (@HMul.hMul Real Real Real qz336 qz334 qz565))

noncomputable def Ns78p1645 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz221) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz225)) qz226) Bool.false 7234020658701 

noncomputable def Ns78p1646 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz225)) qz226 4362277 4194304 21 

noncomputable def Ns78p1647 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz225)) Bool.false 8724554 8388608 168 8388608 4362277 4194304 21 

noncomputable def Ns78p1648 := @Enclosure.Real.IsNear.recentre' (Real.cos qz225) Bool.false 4032799 4194304 84708997 4626069848064 4032799 4194304 84708997 4626069848064 

noncomputable def Ns78p1649 := @Enclosure.Real.IsNear.cos_image qz225 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2335453) qz354) Bool.false 2335453 8388608 73 4194304 Bool.false 4032799 4194304 1 

noncomputable def Ns78p1650 := nat_lit 620679734411205915566798049 

noncomputable def Ns78p1651 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz221 884279719003555 140737488355328 1 500000000000000 371699 8388608 23 8388608 328685887273902389945 1180591620717411303424 Ns78p1650 

noncomputable def Ns78p1652 := @Enclosure.Real.IsNear.subLit_ff_p qz224 qz191 59091955 8388608 23 8388608 7 1 0 1 371699 371699 8388608 23 

noncomputable def Ns78p1653 := @Ns78p1652 8388608 (@Enclosure.Real.IsNear.recentre' qz224 Bool.false 59091955 8388608 23 8388608 59091955 8388608 23 8388608 (Ns78p1641 rfl rfl rfl rfl rfl rfl) rfl) qz539 

noncomputable def Ns78p1654 := @Enclosure.Real.IsNear.recentre' qz225 Bool.false 328685887273902389945 1180591620717411303424 Ns78p1650 Ns78p385 2335453 8388608 73 4194304 (@Ns78p1651 Ns78p385 RS079to096.d31 (Ns78p1653 rfl rfl) rfl) 

noncomputable def Ns78p1655 := nat_lit 29749832637586625643913681 

noncomputable def Ns78p1656 := BSN.cos_dyadic_bound_f 2335453 8388608 2 1 4194304 1102941 Ns78p1655 Ns78p1461 Ns78p1655 Ns78p1655 Ns78p1462 Ns78p1655 4032799 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 2335453) (BSN.cosEvenQ 8388608) 0 1 Ns78p1655 Ns78p1461 Ns78p1655 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 2335453) (BSN.cosOddQ 8388608) 0 1 Ns78p1655 Ns78p1462 Ns78p1655 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1657 := @Enclosure.Real.IsNear.inv_image (Real.cos qz225) 4032799 4194304 84708997 4626069848064 4362193 4362361 4194304 (Ns78p1648 (@Ns78p1649 1102941 (Ns78p1654 rfl) (Enclosure.sfrac_false_div 2335453 8388608) (Ns78p1656 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns78p1658 := @Enclosure.Real.IsNear.recentre' qz226 Bool.false 3316626 4194304 

noncomputable abbrev qz227 := (@HMul.hMul Real Real Real qz336 qz334 qz565)

noncomputable def Ns78p1659 := @Enclosure.Real.IsNear.cos_image qz227 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 690771)) (@Nat.cast Real Real.instNatCast 1048576)) Bool.true 690771 1048576 

noncomputable def Ns78p1660 := nat_lit 6524148180862744090194554725 

noncomputable def Ns78p1661 := nat_lit 5668065334389648844486924966984029 

noncomputable def Ns78p1662 := @Enclosure.Real.IsNear.recentre' qz227 Bool.true Ns78p1660 Ns78p397 Ns78p1661 

noncomputable abbrev qz228 := qz565

noncomputable def Ns78p1663 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz228 884279719003555 140737488355328 1 500000000000000 7377923569495 

noncomputable abbrev qz566 := (@HSub.hSub Real Real Real qz634 qz764 qz757)

noncomputable abbrev qz229 := qz566

noncomputable def Ns78p1664 := @Enclosure.Real.IsNear.subLit_tf qz229 qz26 2979877058391 70368744177664 210036667 70368744177664 1 16 

noncomputable abbrev qz567 := qz764

noncomputable abbrev qz230 := qz567

noncomputable def Ns78p1665 := @Enclosure.Real.IsNear.subLit_ff_n qz230 qz221 138160146601 70368744177664 17098683 70368744177664 371699 8388608 23 8388608 

noncomputable def Ns78p1666 := @Enclosure.Real.IsNear.mulLit_ff qz221 qz221 371699 8388608 23 8388608 371699 8388608 23 8388608 138160146601 70368744177664 

noncomputable def Ns78p1667 := nat_lit 462481117492505942136608602862545901420380479537441 

noncomputable def Ns78p1668 := nat_lit 58927746017182005661972572455120531352527200132792320 

noncomputable def Ns78p1669 := nat_lit 51840928758735297515814246139666127459948675361 

noncomputable def Ns78p1670 := nat_lit 1387339670620000355814794180095358372006221541261601 

noncomputable def Ns78p1671 := nat_lit 2651748570773190254788765760480423910863724005975654400 

noncomputable def Ns78p1672 := BSN.cos_dyadic_bound_f 690771 1048576 3 2 4194304 1102941 Ns78p1667 Ns78p1668 Ns78p1669 Ns78p1670 Ns78p1671 Ns78p1669 3316626 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 690771) (BSN.cosEvenQ 1048576) 0 2 Ns78p1667 Ns78p1668 Ns78p1669 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 690771) (BSN.cosOddQ 1048576) 0 2 Ns78p1670 Ns78p1671 Ns78p1669 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1673 := @Ns78p1658 91326643 4626069848064 1658313 2097152 91326643 4626069848064 (@Ns78p1659 79 4194304 Bool.false 3316626 4194304 1 1102941 (@Ns78p1662 Ns78p495 690771 1048576 79 4194304 (@Ns78p1663 70368744177664 210036667 70368744177664 Ns78p1660 Ns78p397 Ns78p1661 Ns78p495 RS079to096.d31 (@Ns78p1664 0 1 118046777111920 7377923569495 70368744177664 210036667 70368744177664 (@Ns78p1665 24997020531035209728 2979877058391 70368744177664 210036667 70368744177664 (@Ns78p1666 17098683 70368744177664 (Ns78p1653 rfl rfl) (Ns78p1653 rfl rfl) rfl) (Ns78p1653 rfl rfl) rfl rfl) qz366 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 690771 1048576) (BSN.cos_neg_of_bound 690771 1048576 Bool.false 3316626 4194304 1 1102941 (Ns78p1672 rfl rfl)) rfl rfl) 

noncomputable def Ns78p1674 := @Ns78p1639 1131139728357265027717 Ns78p1188 (Ns78p1640 qz542 (@Enclosure.Real.IsNear.of_eq qz762 (@Inv.inv Real Real.instInv (Real.sqrt qz224)) Bool.false 98769 262144 1 4194304 (BSN.rpow_neg_quarter_mk qz220 (BSN.t_div_two_pi_nonneg qz219 311786 1000 qz222)) Ns78p1644) rfl) (@Ns78p1645 8796093022208 705675380637667 19403143268014227456 (BSN.correction_mk qz221 (BSN.cos_two_pi_p_ne_zero_mk qz219 311786 1000 7 qz222 rfl rfl (@BSN.floor_sqrt_eq_dec qz219 311786 1000 7 qz222 rfl rfl rfl))) (@Ns78p1646 1048576 1658313 2097152 91326643 4626069848064 7234020658701 8796093022208 705675380637667 19403143268014227456 (@Ns78p1647 1048576 (Ns78p1657 rfl rfl rfl rfl rfl) rfl) (Ns78p1673 rfl) rfl)) 

noncomputable def Ns78p1675 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz219) (hardyZApproximantRS₀ qz219) Bool.false 2014439825793107357 2305843009213693952 153278462271582327845509 Ns78p1188 (@Eq.refl Real (hardyZApproximantRS₀ qz219)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz219) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz219) qz219 7) (@HMul.hMul Real Real Real qz5 qz758 (Zeta.RiemannSiegel.correction qz221))) Bool.false 2014439825793107357 2305843009213693952 153278462271582327845509 Ns78p1188 (BSN.hardyZApproximantRS₀_eq qz219 7 (@BSN.floor_sqrt_eq_dec qz219 311786 1000 7 qz222 rfl rfl rfl)) (@Ns78p1574 2014439825793107357 2305843009213693952 153278462271582327845509 Ns78p1188 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz219) qz219 7) (@HAdd.hAdd Real Real Real qz351 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz219) qz219 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz219) qz219 7)) Bool.false 9458329 16777216 62731 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz219) qz219 7) (Ns78p1638 (Ns78p1637 rfl) rfl rfl)) (Ns78p1674 rfl) rfl rfl)) 

theorem RS079to096.d54 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz219) Bool.false 2014439825793107357 2305843009213693952 153278462271582327845509 Ns78p1188 := Ns78p1675 

noncomputable def Ns78p1676 := nat_lit 427815627855678728426225664 

noncomputable abbrev qz910 := (Enclosure.sfrac Bool.false 313394 1000)

noncomputable abbrev qz765 := qz910

noncomputable abbrev qz568 := qz765

noncomputable abbrev qz231 := qz568

noncomputable abbrev qz911 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 313394 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz766 := qz911

noncomputable abbrev qz569 := qz766

noncomputable abbrev qz232 := qz569

noncomputable abbrev qz912 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 313394 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz767 := qz912

noncomputable abbrev qz570 := qz767

noncomputable abbrev qz233 := qz570

noncomputable abbrev qz768 := (@HMul.hMul Real Real Real qz5 qz193 (@HPow.hPow Real Real Real qz7 qz232 qz9))

noncomputable def Ns78p1677 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz231) qz231 7) (@HMul.hMul Real Real Real qz5 qz768 (Zeta.RiemannSiegel.correction qz233)) 56283033 33554432 63055 33554432 2721063043650860625 9223372036854775808 1167943643286802881061 Ns78p1188 Ns78p1676 

noncomputable def Ns78p1678 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz231) qz231 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 313394 1000 67 98 67108864 33554432 1125899906842624 Bool.false 30570132324 1238 

noncomputable def Ns78p1679 := Ns78p1678 120242927 62 27397080 8 130587807 62 25364760 8 Bool.true 51346840 46785 Bool.true 50517616 Bool.true 24695870 3537118876014220 1 Bool.false 45879897 Bool.false Bool.false 62615908 Bool.true Bool.true 56283033 

noncomputable def Ns78p1680 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz231) qz231 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 313394 1000 13 31 67108864 33554432 1125899906842624 Bool.false 30570132324 1238 

noncomputable def Ns78p1681 := Ns78p1680 93032624 61 33554424 8 108007536 61 30011992 8 Bool.true 35806576 27484 Bool.false 43879516 Bool.true 10936344 3537118876014220 1 Bool.false 40819059 Bool.true Bool.false 10888001 Bool.false Bool.true 51346840 

noncomputable def Ns78p1682 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz231) qz231 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 313394 1000 151 70 67108864 33554432 1125899906842624 Bool.false 30570132324 1238 

noncomputable def Ns78p1683 := Ns78p1682 46516304 61 47453136 16 73726608 61 38745320 8 Bool.true 67108848 1309 Bool.false 74633831 Bool.false 85650741 3537118876014220 1 Bool.false 60172767 Bool.false Bool.false 19479166 Bool.true Bool.true 35806576 

noncomputable def Ns78p1684 := nat_lit 273329887718968607919902319049162564603528448322921629 

noncomputable def Ns78p1685 := nat_lit 600025478058762162490313741260438280788934393856000 

noncomputable def Ns78p1686 := nat_lit 1451100278925302381429323627520000 

noncomputable def Ns78p1687 := nat_lit 2728599966116062944321646415394017280 

noncomputable abbrev qz769 := (@Eq.refl Real qz910)

noncomputable abbrev qz571 := qz769

noncomputable abbrev qz234 := qz571

noncomputable def Ns78p1688 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz231 313394 1000 392864196944 16000000 626788 4000 2000 Ns78p1686 Ns78p1687 qz234 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns78p1689 := nat_lit 5597796100484477090199599494126849323080262621653434961920 

noncomputable abbrev qz770 := (Real.log (Enclosure.sfrac Bool.false 392864196944 16000000))

noncomputable abbrev qz235 := (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 313394 4000) qz770) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 626788))))))

noncomputable abbrev qz771 := (Enclosure.sfrac Bool.false 313394 2000)

noncomputable abbrev qz572 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz235 qz771) (@HMul.hMul Real Real Real qz5 qz771 (Real.log Real.pi)))

noncomputable def Ns78p1690 := @Enclosure.Real.IsNear.addLit_ft_p qz572 (Enclosure.sfrac Bool.true Ns78p1686 Ns78p1687) 2051529247662918870889 4503599627370496000 10416582752937881787793 Ns78p804 Ns78p1686 Ns78p1687 0 1 Ns78p1689 

noncomputable def Ns78p1691 := nat_lit 13767579727343314034952346009600 

noncomputable abbrev qz573 := (@HSub.hSub Real Real Real qz12 qz235 qz771)

noncomputable abbrev qz574 := (@HMul.hMul Real Real Real qz5 qz771 (Real.log Real.pi))

noncomputable def Ns78p1692 := @Enclosure.Real.IsNear.subLit_ff_p qz573 qz574 571873151251379862293 900719925474099200 2510890927482672191 275735250000000000000000 6018851016417 33554432000 156697 16777216000 Ns78p1691 2051529247662918870889 4503599627370496000 

noncomputable def Ns78p1693 := nat_lit 5718731512513798622930000 

noncomputable abbrev qz575 := qz771

noncomputable def Ns78p1694 := @Enclosure.Real.IsNear.subLit_ff_p qz235 qz575 3565066307066973923177 4503599627370496000 2510890927482672191 275735250000000000000000 313394 2000 0 1 Ns78p1693 571873151251379862293 900719925474099200 2510890927482672191 275735250000000000000000 

noncomputable def Ns78p1695 := nat_lit 8027815646028967015470874712810192896 

noncomputable def Ns78p1696 := nat_lit 12220584462109702191316992 

noncomputable def Ns78p1697 := nat_lit 151109525787002459824498506778921754761602403976007123614069022163602590910836199899854802113466483205799797793568084459520 

noncomputable def Ns78p1698 := nat_lit 2055494185318259125615546514336083061291362417591114470446876125909647961166803264568898367701838219576593160649733832704 

noncomputable def Ns78p1699 := nat_lit 1376761597346488913618504148746088149682540483458285688525219396082259331276069948871719801816357062721459789496320 

noncomputable def Ns78p1700 := BSN.log_dyadic_bound 130720196944 655008196944 6 5 Ns78p1697 33554432 8823528 Ns78p1698 Ns78p1699 13575117 785728393888 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 130720196944) (BSN.artanhQ 655008196944) 0 5 Ns78p1698 Ns78p1697 Ns78p1699 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns78p1701 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 313394 4000) qz770 313394 4000 0 1 22762612369115841 2251799813685248 62500007720587 551470500000000000000 3566833070403344937177 4503599627370496000 9793563709792821139 1102941000000000000000000 (Enclosure.Real.IsNear.const Bool.false 313394 4000) (BSN.isNear_log_sfrac 392864196944 16000000 22762612369115841 2251799813685248 62500007720587 551470500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 392864196944) qz347)) Bool.false Ns78p1696 Ns78p84 1000000123529392 8823528000000000000000 22762612369115841 2251799813685248 62500007720587 551470500000000000000 (BSN.log_rat_reduce_isNear 392864196944 16000000 14 785728393888 524288000000 13575117 33554432 24973259072661432 36028797018963968 8823528 1000000000000000 rfl rfl rfl rfl (Ns78p1700 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns78p1702 := BSN.arctan_dyadic_bound_f 1000 626788 1 0 4194304 1102941 0 1 1 0 1 1 6691 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 626788) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 626788) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz576 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 626788)))

noncomputable def Ns78p1703 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz576 884279719003555 562949953421312 1 2000000000000000 6691 4194304 1 1102941 3705171264397144752128 883381668185507 562949953421312 2000000001102941 2205882000000000000000 qz17 (Ns78p1702 rfl) rfl rfl 

noncomputable def Ns78p1704 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 313394 4000) qz770) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz576)) 3566833070403344937177 4503599627370496000 9793563709792821139 1102941000000000000000000 883381668185507 2251799813685248 2000000001102941 8823528000000000000000 Ns78p1695 3565066307066973923177 4503599627370496000 2510890927482672191 275735250000000000000000 (Ns78p1701 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz576) 1 4 0 1 883381668185507 562949953421312 2000000001102941 2205882000000000000000 883381668185507 2251799813685248 2000000001102941 8823528000000000000000 qz350 Ns78p1703 rfl) 

noncomputable def Ns78p1705 := @Ns78p1690 Ns78p1684 Ns78p1685 10416582752937881787793 Ns78p804 (@Ns78p1692 10416582752937881787793 Ns78p804 (Ns78p1694 (Ns78p1704 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 313394 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz575 (Real.log Real.pi) 313394 2000 0 1 38410761 33554432 1 16777216 6018851016417 33554432000 156697 16777216000 (Enclosure.Real.IsNear.const Bool.false 313394 2000) RS079to096.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns78p1686 Ns78p1687) 

noncomputable def Ns78p1706 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz231) Bool.false Ns78p1684 Ns78p1685 10416582752937881787793 Ns78p804 955316635 2097152 39 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz231) (@HAdd.hAdd Real Real Real qz351 qz572 (Enclosure.sfrac Bool.true Ns78p1686 Ns78p1687)) Bool.false Ns78p1684 Ns78p1685 10416582752937881787793 Ns78p804 Ns78p1688 (Ns78p1705 rfl rfl)) 

noncomputable def Ns78p1707 := nat_lit 139822745719159329490061066816036045776255368009186724577014892786203751099119556296960 

noncomputable def Ns78p1708 := nat_lit 280600471441700119104424470106623871119982685425528859035831015359681912081136681216 

noncomputable def Ns78p1709 := nat_lit 365748123739273586566848011566588443146474563295276279548980992796141767878134140436736 

noncomputable def Ns78p1710 := BSN.sin_dyadic_bound_f 26978080706 17179869184 3 2 8388608 2208037 Ns78p1707 Ns78p97 Ns78p1708 Ns78p1709 Ns78p100 Ns78p1708 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26978080706) qz352 0 2 Ns78p1707 Ns78p97 Ns78p1708 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26978080706) qz353 0 2 Ns78p1709 Ns78p100 Ns78p1708 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1711 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz231) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 955316635) qz398) Bool.false 955316635 2097152 39 2097152 Bool.true 8388606 8388608 1 1102941 (Ns78p1706 rfl) (Enclosure.sfrac_false_div 955316635 2097152) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 955316635) qz398) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474603414906030501396480) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 72 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q1 955316635 2097152 226375608064910080 72057594037927936 72 474603414906030501396480 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388606 8388608 474603414906030501396480 302231454903657293676544 26978080706 17179869184 2208037 2205882 (Ns78p1710 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p1712 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz231) Bool.false Ns78p1684 Ns78p1685 10416582752937881787793 Ns78p804 30570132324 67108864 1238 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz231) (@HAdd.hAdd Real Real Real qz351 qz572 (Enclosure.sfrac Bool.true Ns78p1686 Ns78p1687)) Bool.false Ns78p1684 Ns78p1685 10416582752937881787793 Ns78p804 Ns78p1688 (Ns78p1705 rfl rfl)) 

noncomputable def Ns78p1713 := Ns78p1683 27484 BSN.abs_quadSignPos (BSN.cos_quad_nat3 151 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 60172767 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 70 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 19479166 67108864) qz234 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 1) Bool.true 4194303 4194304 45111851 2313034924032 67108848 67108864 1309 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz231)) Bool.true 4194303 4194304 45111851 2313034924032 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz231) qz231) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz231)) Bool.true 8388606 8388608 45111851 2313034924032 4194303 4194304 45111851 2313034924032 (Ns78p1711 rfl rfl) rfl)) rfl) (Ns78p1712 rfl) RS079to096.d7 

noncomputable def Ns78p1714 := nat_lit 1903986730885552946876358140503315639040263651161297146507967904705 

noncomputable def Ns78p1715 := nat_lit 962688709372240196790221960927423849751363568768662402709371841 

noncomputable def Ns78p1716 := nat_lit 4985073275361274091024230008619563225539188307263486120773624576961 

noncomputable def Ns78p1717 := BSN.sin_dyadic_bound_f 74633831 67108864 3 2 67108864 33554432 Ns78p1714 Ns78p127 Ns78p1715 Ns78p1716 Ns78p130 Ns78p1715 60172767 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 74633831) qz356 0 2 Ns78p1714 Ns78p127 Ns78p1715 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 74633831) (BSN.sinOddQ 67108864) 0 2 Ns78p1716 Ns78p130 Ns78p1715 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1718 := nat_lit 442562753942852993064821684986442850929362548207977398297127553249555448794692868825960004396288092561 

noncomputable def Ns78p1719 := nat_lit 155873933472714964336710858998483462699100105636467492766535237319220296855640329038772781230481 

noncomputable def Ns78p1720 := nat_lit 2682057353086122425271728562906087836583330674677328761984745268603975713714233199278505120533186914705 

noncomputable def Ns78p1721 := BSN.cos_dyadic_bound_f 85650741 67108864 4 3 67108864 33554432 Ns78p1718 Ns78p110 Ns78p1719 Ns78p1720 Ns78p113 Ns78p1719 19479166 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 85650741) qz357 0 3 Ns78p1718 Ns78p110 Ns78p1719 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 85650741) (BSN.cosOddQ 67108864) 0 3 Ns78p1720 Ns78p113 Ns78p1719 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1722 := nat_lit 227391852330038453527471946382845596637270661480652225692076933120 

noncomputable def Ns78p1723 := nat_lit 13743413981291551651838296400196395706985880207611226499383296 

noncomputable def Ns78p1724 := nat_lit 595527838194131001488323549951376244647421374357562553874440585216 

noncomputable def Ns78p1725 := BSN.sin_dyadic_bound_f 43879516 67108864 3 2 67108864 33554432 Ns78p1722 Ns78p127 Ns78p1723 Ns78p1724 Ns78p130 Ns78p1723 40819059 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 43879516) qz356 0 2 Ns78p1722 Ns78p127 Ns78p1723 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 43879516) (BSN.sinOddQ 67108864) 0 2 Ns78p1724 Ns78p130 Ns78p1723 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1726 := nat_lit 14305025937756596280093904896 

noncomputable def Ns78p1727 := BSN.sin_dyadic_bound_f 10936344 67108864 2 1 67108864 33554432 Ns78p1726 Ns78p106 Ns78p1726 Ns78p1726 Ns78p107 Ns78p1726 10888001 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 10936344) qz356 0 1 Ns78p1726 Ns78p106 Ns78p1726 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 10936344) (BSN.sinOddQ 67108864) 0 1 Ns78p1726 Ns78p107 Ns78p1726 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1728 := Ns78p1681 46785 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 13 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 40819059 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 31 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 10888001 67108864) qz234 rfl rfl (Ns78p1713 RS079to096.d9 RS079to096.d11 RS079to096.d13 RS079to096.d17 (Ns78p1717 rfl rfl) (Ns78p1721 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns78p1712 rfl) RS079to096.d19 RS079to096.d21 RS079to096.d23 RS079to096.d25 RS079to096.d17 (Ns78p1725 rfl rfl) (Ns78p1727 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns78p1729 := nat_lit 399501890898844191382011361201223462743001596946529838150734315520 

noncomputable def Ns78p1730 := nat_lit 42417276385342448738639483821935384781919097201348867675652096 

noncomputable def Ns78p1731 := nat_lit 1046245800573301375369214815410349745132500122988299773180448342016 

noncomputable def Ns78p1732 := BSN.sin_dyadic_bound_f 50517616 67108864 3 2 67108864 33554432 Ns78p1729 Ns78p127 Ns78p1730 Ns78p1731 Ns78p130 Ns78p1730 45879897 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 50517616) qz356 0 2 Ns78p1729 Ns78p127 Ns78p1730 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 50517616) (BSN.sinOddQ 67108864) 0 2 Ns78p1731 Ns78p130 Ns78p1730 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1733 := nat_lit 12674501668777433793775418353886224005414947243202586471856800000 

noncomputable def Ns78p1734 := nat_lit 138354931189811461489818264704648726462003477938512100000000 

noncomputable def Ns78p1735 := nat_lit 38023228296469921758403275425129262718791917722651882391370400000 

noncomputable def Ns78p1736 := BSN.cos_dyadic_bound_f 24695870 67108864 3 2 67108864 33554432 Ns78p1733 Ns78p116 Ns78p1734 Ns78p1735 Ns78p119 Ns78p1734 62615908 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 24695870) qz357 0 2 Ns78p1733 Ns78p116 Ns78p1734 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 24695870) (BSN.cosOddQ 67108864) 0 2 Ns78p1735 Ns78p119 Ns78p1734 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1737 := Ns78p1679 63055 BSN.abs_quadSignPos qz734 (BSN.sfrac_eq_quadSignPos_mul Bool.false 45879897 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 98 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 62615908 67108864) qz234 rfl rfl (Ns78p1728 rfl rfl) (Ns78p1712 rfl) RS079to096.d27 RS079to096.d29 RS079to096.d49 RS079to096.d51 RS079to096.d17 (Ns78p1732 rfl rfl) (Ns78p1736 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns78p1738 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 7) 56283033 67108864 63055 67108864 56283033 67108864 63055 67108864 7554180814209024 56283033 33554432 63055 33554432 (Ns78p1737 rfl) 

noncomputable def Ns78p1739 := @Enclosure.Real.IsNear.mulLit_tf qz768 (Zeta.RiemannSiegel.correction qz233) 1578273 4194304 1 4194304 1724076280625 2199023255552 1460749157561453 38806286536028454912 2721063043650860625 9223372036854775808 

noncomputable abbrev qz772 := (@HPow.hPow Real Real Real qz7 qz232 qz9)

noncomputable def Ns78p1740 := @Enclosure.Real.IsNear.mulLit_tf qz193 qz772 1 1 0 1 1578273 4194304 1 4194304 1578273 4194304 1 4194304 

noncomputable def Ns78p1741 := @Enclosure.Real.IsNear.sqrt_image qz232 209204441033 4194304000 156697 4194304000 29622058 29622081 4194304 (@Enclosure.Real.IsNear.of_eq qz232 (@HMul.hMul Real Real Real qz5 qz231 qz3) Bool.false 209204441033 4194304000 156697 4194304000 (BSN.t_div_two_pi_mk qz231 313394 1000 qz234) (@Enclosure.Real.IsNear.mulLit_ff qz231 qz3 313394 1000 0 1 1335089 8388608 1 8388608 209204441033 4194304000 156697 4194304000 (Enclosure.Real.IsNear.const Bool.false 313394 1000) RS079to096.d32 rfl)) 

noncomputable abbrev qz913 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 313394 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz773 := qz913

noncomputable abbrev qz577 := qz773

noncomputable abbrev qz236 := qz577

noncomputable def Ns78p1742 := @Enclosure.Real.IsNear.sqrt_image qz236 59244139 8388608 23 8388608 11146475 11146480 4194304 (@Enclosure.Real.IsNear.recentre' qz236 Bool.false 59244139 8388608 23 8388608 59244139 8388608 23 8388608 (Ns78p1741 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns78p1743 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz236) 22292955 8388608 5 8388608 1578272 1578274 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz236) Bool.false 22292955 8388608 5 8388608 22292955 8388608 5 8388608 (Ns78p1742 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns78p1744 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz236)) Bool.false 3156546 8388608 2 8388608 1578273 4194304 1 4194304 (Ns78p1743 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz237 := (@HMul.hMul Real Real Real qz336 qz334 qz570)

noncomputable abbrev qz774 := (@HMul.hMul Real Real Real qz841 qz912 qz912)

noncomputable abbrev qz578 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz774 qz767) qz640)

noncomputable abbrev qz238 := (Real.cos (@HMul.hMul Real Real Real qz336 qz334 qz578))

noncomputable def Ns78p1745 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz233) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz237)) qz238) Bool.false 1724076280625 

noncomputable def Ns78p1746 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz237)) qz238 9078625 8388608 181 

noncomputable def Ns78p1747 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz237)) Bool.false 9078625 8388608 181 8388608 9078625 8388608 181 

noncomputable def Ns78p1748 := @Enclosure.Real.IsNear.recentre' (Real.cos qz237) Bool.false 3875518 4194304 84708997 4626069848064 1937759 2097152 84708997 4626069848064 

noncomputable def Ns78p1749 := @Enclosure.Real.IsNear.cos_image qz237 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3291653) qz354) Bool.false 3291653 8388608 73 4194304 Bool.false 3875518 4194304 1 

noncomputable def Ns78p1750 := nat_lit 620679734412513166172746977 

noncomputable def Ns78p1751 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz233 884279719003555 140737488355328 1 500000000000000 523883 8388608 23 8388608 463259112030739404065 1180591620717411303424 Ns78p1750 

noncomputable def Ns78p1752 := @Enclosure.Real.IsNear.subLit_ff_p qz236 qz191 59244139 8388608 23 8388608 7 1 0 1 523883 523883 8388608 23 

noncomputable def Ns78p1753 := @Ns78p1752 8388608 (@Enclosure.Real.IsNear.recentre' qz236 Bool.false 59244139 8388608 23 8388608 59244139 8388608 23 8388608 (Ns78p1741 rfl rfl rfl rfl rfl rfl) rfl) qz539 

noncomputable def Ns78p1754 := @Enclosure.Real.IsNear.recentre' qz237 Bool.false 463259112030739404065 1180591620717411303424 Ns78p1750 Ns78p385 3291653 8388608 73 4194304 (@Ns78p1751 Ns78p385 RS079to096.d31 (Ns78p1753 rfl rfl) rfl) 

noncomputable def Ns78p1755 := nat_lit 117396780167524411992263281 

noncomputable def Ns78p1756 := BSN.cos_dyadic_bound_f 3291653 8388608 2 1 4194304 1102941 Ns78p1755 Ns78p1461 Ns78p1755 Ns78p1755 Ns78p1462 Ns78p1755 3875518 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 3291653) (BSN.cosEvenQ 8388608) 0 1 Ns78p1755 Ns78p1461 Ns78p1755 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 3291653) (BSN.cosOddQ 8388608) 0 1 Ns78p1755 Ns78p1462 Ns78p1755 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1757 := @Enclosure.Real.IsNear.inv_image (Real.cos qz237) 1937759 2097152 84708997 4626069848064 4539222 4539403 4194304 (Ns78p1748 (@Ns78p1749 1102941 (Ns78p1754 rfl) (Enclosure.sfrac_false_div 3291653 8388608) (Ns78p1756 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns78p1758 := @Enclosure.Real.IsNear.recentre' qz238 Bool.false 3038480 4194304 

noncomputable abbrev qz239 := (@HMul.hMul Real Real Real qz336 qz334 qz578)

noncomputable def Ns78p1759 := @Enclosure.Real.IsNear.cos_image qz239 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 6380283)) qz354) Bool.true 6380283 8388608 

noncomputable def Ns78p1760 := nat_lit 7532508852869567514758081845 

noncomputable def Ns78p1761 := nat_lit 1171396076760348444377818001312169 

noncomputable def Ns78p1762 := @Enclosure.Real.IsNear.recentre' qz239 Bool.true Ns78p1760 Ns78p397 Ns78p1761 

noncomputable abbrev qz240 := qz578

noncomputable def Ns78p1763 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz240 884279719003555 140737488355328 1 500000000000000 8518242238279 

noncomputable abbrev qz579 := (@HSub.hSub Real Real Real qz634 qz774 qz767)

noncomputable abbrev qz241 := qz579

noncomputable def Ns78p1764 := @Enclosure.Real.IsNear.subLit_tf qz241 qz26 4120195727175 70368744177664 217037131 70368744177664 1 16 

noncomputable abbrev qz580 := qz774

noncomputable abbrev qz242 := qz580

noncomputable def Ns78p1765 := @Enclosure.Real.IsNear.subLit_ff_n qz242 qz233 274453397689 70368744177664 24099147 70368744177664 523883 8388608 23 8388608 

noncomputable def Ns78p1766 := @Enclosure.Real.IsNear.mulLit_ff qz233 qz233 523883 8388608 23 8388608 523883 8388608 23 8388608 274453397689 70368744177664 

noncomputable def Ns78p1767 := nat_lit 13788440703062212063076511318428729489730169146485707505121 

noncomputable def Ns78p1768 := nat_lit 2746120180242360928708083460671228690424233863478902241 

noncomputable def Ns78p1769 := nat_lit 41359829868826151467372117788364846011809658971730164710881 

noncomputable def Ns78p1770 := BSN.cos_dyadic_bound_f 6380283 8388608 3 2 4194304 1102941 Ns78p1767 Ns78p501 Ns78p1768 Ns78p1769 Ns78p504 Ns78p1768 3038480 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 6380283) (BSN.cosEvenQ 8388608) 0 2 Ns78p1767 Ns78p501 Ns78p1768 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 6380283) (BSN.cosOddQ 8388608) 0 2 Ns78p1769 Ns78p504 Ns78p1768 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1771 := @Ns78p1758 188167991 9252139696128 189905 262144 188167991 9252139696128 (@Ns78p1759 163 8388608 Bool.false 3038480 4194304 1 1102941 (@Ns78p1762 Ns78p400 6380283 8388608 163 8388608 (@Ns78p1763 70368744177664 217037131 70368744177664 Ns78p1760 Ns78p397 Ns78p1761 Ns78p400 RS079to096.d31 (@Ns78p1764 0 1 136291875812464 8518242238279 70368744177664 217037131 70368744177664 (@Ns78p1765 34562706838546022400 4120195727175 70368744177664 217037131 70368744177664 (@Ns78p1766 24099147 70368744177664 (Ns78p1753 rfl rfl) (Ns78p1753 rfl rfl) rfl) (Ns78p1753 rfl rfl) rfl rfl) qz366 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 6380283 8388608) (BSN.cos_neg_of_bound 6380283 8388608 Bool.false 3038480 4194304 1 1102941 (Ns78p1770 rfl rfl)) rfl rfl) 

noncomputable def Ns78p1772 := @Ns78p1739 1167943643286802881061 Ns78p1188 (Ns78p1740 qz542 (@Enclosure.Real.IsNear.of_eq qz772 (@Inv.inv Real Real.instInv (Real.sqrt qz236)) Bool.false 1578273 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz232 (BSN.t_div_two_pi_nonneg qz231 313394 1000 qz234)) Ns78p1744) rfl) (@Ns78p1745 2199023255552 1460749157561453 38806286536028454912 (BSN.correction_mk qz233 (BSN.cos_two_pi_p_ne_zero_mk qz231 313394 1000 7 qz234 rfl rfl (@BSN.floor_sqrt_eq_dec qz231 313394 1000 7 qz234 rfl rfl rfl))) (@Ns78p1746 8388608 189905 262144 188167991 9252139696128 1724076280625 2199023255552 1460749157561453 38806286536028454912 (@Ns78p1747 8388608 (Ns78p1757 rfl rfl rfl rfl rfl) rfl) (Ns78p1771 rfl) rfl)) 

noncomputable def Ns78p1773 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz231) (hardyZApproximantRS₀ qz231) Bool.true 12749899263849220527 9223372036854775808 154101093488866441910821 Ns78p1188 (@Eq.refl Real (hardyZApproximantRS₀ qz231)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz231) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz231) qz231 7) (@HMul.hMul Real Real Real qz5 qz768 (Zeta.RiemannSiegel.correction qz233))) Bool.true 12749899263849220527 9223372036854775808 154101093488866441910821 Ns78p1188 (BSN.hardyZApproximantRS₀_eq qz231 7 (@BSN.floor_sqrt_eq_dec qz231 313394 1000 7 qz234 rfl rfl rfl)) (@Ns78p1677 12749899263849220527 9223372036854775808 154101093488866441910821 Ns78p1188 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz231) qz231 7) (@HAdd.hAdd Real Real Real qz351 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 7)) Bool.true 56283033 33554432 63055 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz231) qz231 7) (Ns78p1738 (Ns78p1737 rfl) rfl rfl)) (Ns78p1772 rfl) rfl rfl)) 

theorem RS079to096.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz231) Bool.true 12749899263849220527 9223372036854775808 154101093488866441910821 Ns78p1188 := Ns78p1773 

noncomputable def Ns78p1774 := nat_lit 4043512703468193800744075264 

noncomputable abbrev qz914 := (Enclosure.sfrac Bool.false 315000 1000)

noncomputable abbrev qz775 := qz914

noncomputable abbrev qz581 := qz775

noncomputable abbrev qz243 := qz581

noncomputable abbrev qz915 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 315000 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz776 := qz915

noncomputable abbrev qz582 := qz776

noncomputable abbrev qz244 := qz582

noncomputable abbrev qz916 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 315000 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz777 := qz916

noncomputable abbrev qz583 := qz777

noncomputable abbrev qz245 := qz583

noncomputable abbrev qz778 := (@HMul.hMul Real Real Real qz5 qz193 (@HPow.hPow Real Real Real qz7 qz244 qz9))

noncomputable def Ns78p1775 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz243) qz243 7) (@HMul.hMul Real Real Real qz5 qz778 (Zeta.RiemannSiegel.correction qz245)) 45371311 33554432 63379 33554432 20733501143618280905 73786976294838206464 1220893530131362885477 Ns78p1188 Ns78p1774 

noncomputable def Ns78p1776 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz243) qz243 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 315000 1000 67 98 67108864 33554432 1125899906842624 Bool.false 30780951445 1245 

noncomputable def Ns78p1777 := Ns78p1776 120242927 62 27397080 8 130587807 62 25364760 8 Bool.false 56316783 47026 Bool.true 32808636 Bool.true 23600767 3537118876014220 1 Bool.false 31517232 Bool.false Bool.false 63001513 Bool.true Bool.false 45371311 

noncomputable def Ns78p1778 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz243) qz243 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 315000 1000 13 30 67108864 33554432 1125899906842624 Bool.false 30780951445 1245 

noncomputable def Ns78p1779 := Ns78p1778 93032624 61 33554424 8 108007536 61 30011992 8 Bool.false 101384778 27626 Bool.false 105288243 Bool.true 78991683 3537118876014220 1 Bool.false 67108745 Bool.true Bool.false 25745262 Bool.true Bool.false 56316783 

noncomputable def Ns78p1780 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz243) qz243 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 315000 1000 152 71 67108864 33554432 1125899906842624 Bool.false 30780951445 1245 

noncomputable def Ns78p1781 := Ns78p1780 46516304 61 47453136 16 73726608 61 38745320 8 Bool.false 67108840 1317 Bool.false 105333410 Bool.false 72650573 3537118876014220 1 Bool.false 80947 Bool.false Bool.false 59268529 Bool.false Bool.false 101384778 

noncomputable def Ns78p1782 := nat_lit 258308383814290964449599382463673491 

noncomputable def Ns78p1783 := nat_lit 563165899213183823112033001275392 

noncomputable def Ns78p1784 := nat_lit 1488664316280330000000000000000000 

noncomputable def Ns78p1785 := nat_lit 2813578865955931545000000000000000000 

noncomputable abbrev qz917 := (@Eq.refl Real (Enclosure.sfrac Bool.false 315000 1000))

noncomputable abbrev qz779 := qz917

noncomputable abbrev qz584 := qz779

noncomputable abbrev qz246 := qz584

noncomputable def Ns78p1786 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz243 315000 1000 396901000000 16000000 630000 4000 2000 Ns78p1784 Ns78p1785 qz246 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns78p1787 := nat_lit 11623877271643093400231972210865307095000000000000000000 

noncomputable abbrev qz780 := (Real.log (Enclosure.sfrac Bool.false 396901000000 16000000))

noncomputable abbrev qz247 := (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 315000 4000) qz780) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 630000))))))

noncomputable abbrev qz781 := (Enclosure.sfrac Bool.false 315000 2000)

noncomputable abbrev qz585 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz247 qz781) (@HMul.hMul Real Real Real qz5 qz781 (Real.log Real.pi)))

noncomputable def Ns78p1788 := @Enclosure.Real.IsNear.addLit_ft_p qz585 (Enclosure.sfrac Bool.true Ns78p1784 Ns78p1785) 4131354134404162799 9007199254740992 20938614007768619683 1129411584000000000000000 Ns78p1784 Ns78p1785 0 1 Ns78p1787 

noncomputable def Ns78p1789 := nat_lit 277250482741566682311950336 

noncomputable abbrev qz586 := (@HSub.hSub Real Real Real qz12 qz247 qz781)

noncomputable abbrev qz587 := (@HMul.hMul Real Real Real qz5 qz781 (Real.log Real.pi))

noncomputable def Ns78p1790 := @Enclosure.Real.IsNear.subLit_ff_p qz586 qz587 5755306732138030319 9007199254740992 80750009729042561 8823528000000000000000 12099389715 67108864 315 33554432 Ns78p1789 4131354134404162799 9007199254740992 

noncomputable abbrev qz588 := qz781

noncomputable def Ns78p1791 := @Enclosure.Real.IsNear.subLit_ff_p qz247 qz588 7173940614759736559 9007199254740992 80750009729042561 8823528000000000000000 315000 2000 0 1 11510613464276060638000 5755306732138030319 9007199254740992 80750009729042561 8823528000000000000000 

noncomputable def Ns78p1792 := nat_lit 16154278139705008281868343424581632 

noncomputable def Ns78p1793 := nat_lit 12232943168149538268512256 

noncomputable def Ns78p1794 := nat_lit 160684945083221335621840018533305506713127846849932992138671875000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns78p1795 := nat_lit 2297283101234397698123161008749063764203539064718771546102305000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns78p1796 := nat_lit 1866143982624303419113940488759484759063394170705635305000000000000000000000000000000000000000000000000000000000000 

noncomputable def Ns78p1797 := BSN.log_dyadic_bound 134757000000 659045000000 6 5 Ns78p1794 33554432 8823528 Ns78p1795 Ns78p1796 13918140 793802000000 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 134757000000) (BSN.artanhQ 659045000000) 0 5 Ns78p1795 Ns78p1794 Ns78p1796 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns78p1798 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 315000 4000) qz780 315000 4000 0 1 22785632252971713 2251799813685248 62500007720587 551470500000000000000 7177474159686089595 9007199254740992 62500007720587 7002800000000000000 (Enclosure.Real.IsNear.const Bool.false 315000 4000) (BSN.isNear_log_sfrac 396901000000 16000000 22785632252971713 2251799813685248 62500007720587 551470500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 396901000000) qz347)) Bool.false Ns78p1793 Ns78p84 1000000123529392 8823528000000000000000 22785632252971713 2251799813685248 62500007720587 551470500000000000000 (BSN.log_rat_reduce_isNear 396901000000 16000000 14 793802000000 524288000000 13918140 33554432 24973259072661432 36028797018963968 8823528 1000000000000000 rfl rfl rfl rfl (Ns78p1797 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns78p1799 := BSN.arctan_dyadic_bound_f 1000 630000 1 0 4194304 1102941 0 1 1 0 1 1 6657 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 630000) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 630000) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz589 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 630000)))

noncomputable def Ns78p1800 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz589 884279719003555 562949953421312 1 2000000000000000 6657 4194304 1 1102941 3705190404695561076736 883386231588259 562949953421312 2000000001102941 2205882000000000000000 qz17 (Ns78p1799 rfl) rfl rfl 

noncomputable def Ns78p1801 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 315000 4000) qz780) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz589)) 7177474159686089595 9007199254740992 62500007720587 7002800000000000000 883386231588259 2251799813685248 2000000001102941 8823528000000000000000 Ns78p1792 7173940614759736559 9007199254740992 80750009729042561 8823528000000000000000 (Ns78p1798 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz589) 1 4 0 1 883386231588259 562949953421312 2000000001102941 2205882000000000000000 883386231588259 2251799813685248 2000000001102941 8823528000000000000000 qz350 Ns78p1800 rfl) 

noncomputable def Ns78p1802 := @Ns78p1788 Ns78p1782 Ns78p1783 20938614007768619683 1129411584000000000000000 (@Ns78p1790 20938614007768619683 1129411584000000000000000 (Ns78p1791 (Ns78p1801 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 315000 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz588 (Real.log Real.pi) 315000 2000 0 1 38410761 33554432 1 16777216 12099389715 67108864 315 33554432 (Enclosure.Real.IsNear.const Bool.false 315000 2000) RS079to096.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns78p1784 Ns78p1785) 

noncomputable def Ns78p1803 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz243) Bool.false Ns78p1782 Ns78p1783 20938614007768619683 1129411584000000000000000 1923809465 4194304 157 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz243) (@HAdd.hAdd Real Real Real qz351 qz585 (Enclosure.sfrac Bool.true Ns78p1784 Ns78p1785)) Bool.false Ns78p1782 Ns78p1783 20938614007768619683 1129411584000000000000000 Ns78p1786 (Ns78p1802 rfl rfl)) 

noncomputable def Ns78p1804 := nat_lit 139771732407651758023165145287669524599043366022463256213181493106736283063814990069760 

noncomputable def Ns78p1805 := nat_lit 280396168488661535503510443037069171360997835750099187367618812259425156190559010816 

noncomputable def Ns78p1806 := nat_lit 365614848223439628526998268369455404815291009753332177112118241964460719676159307022336 

noncomputable def Ns78p1807 := BSN.sin_dyadic_bound_f 26975624608 17179869184 3 2 8388608 2208037 Ns78p1804 Ns78p97 Ns78p1805 Ns78p1806 Ns78p100 Ns78p1805 8388605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26975624608) qz352 0 2 Ns78p1804 Ns78p97 Ns78p1805 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26975624608) qz353 0 2 Ns78p1806 Ns78p100 Ns78p1805 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1808 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz243) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1923809465) qz378) Bool.false 1923809465 4194304 157 8388608 Bool.false 8388605 8388608 1 1102941 (Ns78p1803 rfl) (Enclosure.sfrac_false_div 1923809465 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1923809465) qz378) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949120413543043547791360) qz397) 226375608064910080 72057594037927936 Bool.false 8388605 8388608 72 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q3 1923809465 4194304 226375608064910080 72057594037927936 72 949120413543043547791360 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388605 8388608 949120413543043547791360 604462909807314587353088 26975624608 17179869184 2208037 2205882 (Ns78p1807 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p1809 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz243) Bool.false Ns78p1782 Ns78p1783 20938614007768619683 1129411584000000000000000 30780951445 67108864 1245 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz243) (@HAdd.hAdd Real Real Real qz351 qz585 (Enclosure.sfrac Bool.true Ns78p1784 Ns78p1785)) Bool.false Ns78p1782 Ns78p1783 20938614007768619683 1129411584000000000000000 Ns78p1786 (Ns78p1802 rfl rfl)) 

noncomputable def Ns78p1810 := Ns78p1781 27626 BSN.abs_quadSignPos (BSN.cos_quad_nat0 152 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 80947 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 71 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 59268529 67108864) qz246 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 1) Bool.false 8388605 8388608 181550345 9252139696128 67108840 67108864 1317 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz243)) Bool.false 8388605 8388608 181550345 9252139696128 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz243) qz243) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz243)) Bool.false 8388605 8388608 181550345 9252139696128 8388605 8388608 181550345 9252139696128 (Ns78p1808 rfl rfl) rfl)) rfl) (Ns78p1809 rfl) RS079to096.d7 

noncomputable def Ns78p1811 := nat_lit 1014369908710505246373399086653561709373162821210661872548383413110582158738661129890117684641344000000 

noncomputable def Ns78p1812 := nat_lit 1865493447747754498812341766518426598711613722307563032573143995543262682275011949681000000000000 

noncomputable def Ns78p1813 := nat_lit 6139066581703915698235035421099975315651934582276646777838036909187384743221650553209643505211353600000 

noncomputable def Ns78p1814 := BSN.cos_dyadic_bound_f 105333410 67108864 4 3 67108864 33554432 Ns78p1811 Ns78p110 Ns78p1812 Ns78p1813 Ns78p113 Ns78p1812 80947 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 105333410) qz357 0 3 Ns78p1811 Ns78p110 Ns78p1812 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 105333410) (BSN.cosOddQ 67108864) 0 3 Ns78p1813 Ns78p113 Ns78p1812 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1815 := nat_lit 1709443404674066258649999932674366045151186291867463751894990254625 

noncomputable def Ns78p1816 := nat_lit 776090471982376083930479544352208452351315155278406517167682081 

noncomputable def Ns78p1817 := nat_lit 4475857151477440163756969523456293209330252444639573358697179181601 

noncomputable def Ns78p1818 := BSN.sin_dyadic_bound_f 72650573 67108864 3 2 67108864 33554432 Ns78p1815 Ns78p127 Ns78p1816 Ns78p1817 Ns78p130 Ns78p1816 59268529 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 72650573) qz356 0 2 Ns78p1815 Ns78p127 Ns78p1816 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 72650573) (BSN.sinOddQ 67108864) 0 2 Ns78p1817 Ns78p130 Ns78p1816 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1819 := nat_lit 2628616835197209097497743393427290495651264949537778065459663008452639048730246950657476367558235994801 

noncomputable def Ns78p1820 := nat_lit 1855916963666014358341797721987365208381309490252887005680225926685151935155647121068940082625201 

noncomputable def Ns78p1821 := nat_lit 13126830167132476081882867867654576675565029230309888825811579011568804404489965062252338775292772432561 

noncomputable def Ns78p1822 := BSN.sin_dyadic_bound_f 105288243 67108864 4 3 67108864 33554432 Ns78p1819 Ns78p941 Ns78p1820 Ns78p1821 Ns78p944 Ns78p1820 67108745 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 105288243) qz356 0 3 Ns78p1819 Ns78p941 Ns78p1820 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 105288243) (BSN.sinOddQ 67108864) 0 3 Ns78p1821 Ns78p944 Ns78p1820 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1823 := nat_lit 320026773505826847188846075195422254652718848629186048288497282159467507604999439891263857816280576241 

noncomputable def Ns78p1824 := nat_lit 59016901468561249601115985708869458908116850791830469355998261806626239607351792273038359736561 

noncomputable def Ns78p1825 := nat_lit 1940018238136876999175883699497638057947166562479979748678578901506113300593375254891594370882902503665 

noncomputable def Ns78p1826 := BSN.cos_dyadic_bound_f 78991683 67108864 4 3 67108864 33554432 Ns78p1823 Ns78p110 Ns78p1824 Ns78p1825 Ns78p113 Ns78p1824 25745262 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 78991683) qz357 0 3 Ns78p1823 Ns78p110 Ns78p1824 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 78991683) (BSN.cosOddQ 67108864) 0 3 Ns78p1825 Ns78p113 Ns78p1824 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1827 := Ns78p1779 47026 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 13 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 67108745 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 30 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 25745262 67108864) qz246 rfl rfl (Ns78p1810 RS079to096.d9 RS079to096.d11 RS079to096.d13 RS079to096.d17 (Ns78p1814 rfl rfl) (Ns78p1818 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns78p1809 rfl) RS079to096.d19 RS079to096.d21 RS079to096.d23 RS079to096.d25 RS079to096.d17 (Ns78p1822 rfl rfl) (Ns78p1826 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns78p1828 := nat_lit 1158651160300881385935810806016 

noncomputable def Ns78p1829 := BSN.sin_dyadic_bound_f 32808636 67108864 2 1 67108864 33554432 Ns78p1828 Ns78p106 Ns78p1828 Ns78p1828 Ns78p107 Ns78p1828 31517232 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 32808636) qz356 0 1 Ns78p1828 Ns78p106 Ns78p1828 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 32808636) (BSN.sinOddQ 67108864) 0 1 Ns78p1828 Ns78p107 Ns78p1828 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1830 := nat_lit 310244770143371243933471147521 

noncomputable def Ns78p1831 := BSN.cos_dyadic_bound_f 23600767 67108864 2 1 67108864 33554432 Ns78p1830 Ns78p228 Ns78p1830 Ns78p1830 Ns78p229 Ns78p1830 63001513 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 23600767) qz357 0 1 Ns78p1830 Ns78p228 Ns78p1830 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 23600767) (BSN.cosOddQ 67108864) 0 1 Ns78p1830 Ns78p229 Ns78p1830 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1832 := Ns78p1777 63379 BSN.abs_quadSignPos qz734 (BSN.sfrac_eq_quadSignPos_mul Bool.false 31517232 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 98 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 63001513 67108864) qz246 rfl rfl (Ns78p1827 rfl rfl) (Ns78p1809 rfl) RS079to096.d27 RS079to096.d29 RS079to096.d49 RS079to096.d51 RS079to096.d17 (Ns78p1829 rfl rfl) (Ns78p1831 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns78p1833 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 7) 45371311 67108864 63379 67108864 45371311 67108864 63379 67108864 6089634278801408 45371311 33554432 63379 33554432 (Ns78p1832 rfl) 

noncomputable def Ns78p1834 := @Enclosure.Real.IsNear.mulLit_tf qz778 (Zeta.RiemannSiegel.correction qz245) 3152515 8388608 1 8388608 6576812844227 8796093022208 769949902615015 19403143268014227456 20733501143618280905 73786976294838206464 

noncomputable abbrev qz782 := (@HPow.hPow Real Real Real qz7 qz244 qz9)

noncomputable def Ns78p1835 := @Enclosure.Real.IsNear.mulLit_tf qz193 qz782 1 1 0 1 3152515 8388608 1 8388608 3152515 8388608 1 8388608 

noncomputable def Ns78p1836 := @Enclosure.Real.IsNear.sqrt_image qz244 420553035 8388608 315 8388608 29697861 29697884 4194304 (@Enclosure.Real.IsNear.of_eq qz244 (@HMul.hMul Real Real Real qz5 qz243 qz3) Bool.false 420553035 8388608 315 8388608 (BSN.t_div_two_pi_mk qz243 315000 1000 qz246) (@Enclosure.Real.IsNear.mulLit_ff qz243 qz3 315000 1000 0 1 1335089 8388608 1 8388608 420553035 8388608 315 8388608 (Enclosure.Real.IsNear.const Bool.false 315000 1000) RS079to096.d32 rfl)) 

noncomputable abbrev qz918 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 315000 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz783 := qz918

noncomputable abbrev qz590 := qz783

noncomputable abbrev qz248 := qz590

noncomputable def Ns78p1837 := @Enclosure.Real.IsNear.sqrt_image qz248 59395745 8388608 23 8388608 11160728 11160733 4194304 (@Enclosure.Real.IsNear.recentre' qz248 Bool.false 59395745 8388608 23 8388608 59395745 8388608 23 8388608 (Ns78p1836 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns78p1838 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz248) 22321461 8388608 5 8388608 1576257 1576258 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz248) Bool.false 22321461 8388608 5 8388608 22321461 8388608 5 8388608 (Ns78p1837 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns78p1839 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz248)) Bool.false 3152515 8388608 1 8388608 3152515 8388608 1 8388608 (Ns78p1838 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz336 qz334 qz583)

noncomputable abbrev qz784 := (@HMul.hMul Real Real Real qz841 qz916 qz916)

noncomputable abbrev qz591 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz784 qz777) qz640)

noncomputable abbrev qz250 := (Real.cos (@HMul.hMul Real Real Real qz336 qz334 qz591))

noncomputable def Ns78p1840 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz245) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz249)) qz250) Bool.false 6576812844227 

noncomputable def Ns78p1841 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz249)) qz250 2397529 2097152 101 

noncomputable def Ns78p1842 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz249)) Bool.false 9590116 8388608 202 8388608 2397529 2097152 101 

noncomputable def Ns78p1843 := @Enclosure.Real.IsNear.recentre' (Real.cos qz249) Bool.false 3668816 4194304 84708997 4626069848064 229301 262144 84708997 4626069848064 

noncomputable def Ns78p1844 := @Enclosure.Real.IsNear.cos_image qz249 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2122111) qz378) Bool.false 2122111 4194304 73 4194304 Bool.false 3668816 4194304 1 

noncomputable def Ns78p1845 := nat_lit 620679734413815451796501729 

noncomputable def Ns78p1846 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz245 884279719003555 140737488355328 1 500000000000000 675489 8388608 23 8388608 597321223109992363395 1180591620717411303424 Ns78p1845 

noncomputable def Ns78p1847 := @Enclosure.Real.IsNear.subLit_ff_p qz248 qz191 59395745 8388608 23 8388608 7 1 0 1 675489 675489 8388608 23 

noncomputable def Ns78p1848 := @Ns78p1847 8388608 (@Enclosure.Real.IsNear.recentre' qz248 Bool.false 59395745 8388608 23 8388608 59395745 8388608 23 8388608 (Ns78p1836 rfl rfl rfl rfl rfl rfl) rfl) qz539 

noncomputable def Ns78p1849 := @Enclosure.Real.IsNear.recentre' qz249 Bool.false 597321223109992363395 1180591620717411303424 Ns78p1845 Ns78p385 2122111 4194304 73 4194304 (@Ns78p1846 Ns78p385 RS079to096.d31 (Ns78p1848 rfl rfl) rfl) 

noncomputable def Ns78p1850 := nat_lit 20280207123560323187735041 

noncomputable def Ns78p1851 := BSN.cos_dyadic_bound_f 2122111 4194304 2 1 4194304 1102941 Ns78p1850 Ns78p1376 Ns78p1850 Ns78p1850 Ns78p1377 Ns78p1850 3668816 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 2122111) (BSN.cosEvenQ 4194304) 0 1 Ns78p1850 Ns78p1376 Ns78p1850 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 2122111) (BSN.cosOddQ 4194304) 0 1 Ns78p1850 Ns78p1377 Ns78p1850 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1852 := @Enclosure.Real.IsNear.inv_image (Real.cos qz249) 229301 262144 84708997 4626069848064 4794957 4795159 4194304 (Ns78p1843 (@Ns78p1844 1102941 (Ns78p1849 rfl) (Enclosure.sfrac_false_div 2122111 4194304) (Ns78p1851 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns78p1853 := @Enclosure.Real.IsNear.recentre' qz250 Bool.false 2743163 4194304 

noncomputable abbrev qz251 := (@HMul.hMul Real Real Real qz336 qz334 qz591)

noncomputable def Ns78p1854 := @Enclosure.Real.IsNear.cos_image qz251 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7196657)) qz354) Bool.true 7196657 8388608 

noncomputable def Ns78p1855 := nat_lit 8496313008076531743079853725 

noncomputable def Ns78p1856 := nat_lit 6045177927440427112120382059716409 

noncomputable def Ns78p1857 := @Enclosure.Real.IsNear.recentre' qz251 Bool.true Ns78p1855 Ns78p397 Ns78p1856 

noncomputable abbrev qz252 := qz591

noncomputable def Ns78p1858 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz252 884279719003555 140737488355328 1 500000000000000 9608173551295 

noncomputable abbrev qz592 := (@HSub.hSub Real Real Real qz634 qz784 qz777)

noncomputable abbrev qz253 := qz592

noncomputable def Ns78p1859 := @Enclosure.Real.IsNear.subLit_tf qz253 qz26 5210127040191 70368744177664 224011007 70368744177664 1 16 

noncomputable abbrev qz593 := qz784

noncomputable abbrev qz254 := qz593

noncomputable def Ns78p1860 := @Enclosure.Real.IsNear.subLit_ff_n qz254 qz245 456285389121 70368744177664 31073023 70368744177664 675489 8388608 23 8388608 

noncomputable def Ns78p1861 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz245 675489 8388608 23 8388608 675489 8388608 23 8388608 456285389121 70368744177664 

noncomputable def Ns78p1862 := nat_lit 22321949072409281030474915892000231521249572516646346103681 

noncomputable def Ns78p1863 := nat_lit 7195259045114357819862292020966231158049607639327382401 

noncomputable def Ns78p1864 := nat_lit 66951456699137614375785023091958762101432618334660383546241 

noncomputable def Ns78p1865 := BSN.cos_dyadic_bound_f 7196657 8388608 3 2 4194304 1102941 Ns78p1862 Ns78p501 Ns78p1863 Ns78p1864 Ns78p504 Ns78p1863 2743163 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 7196657) (BSN.cosEvenQ 8388608) 0 2 Ns78p1862 Ns78p501 Ns78p1863 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 7196657) (BSN.cosOddQ 8388608) 0 2 Ns78p1864 Ns78p504 Ns78p1863 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1866 := @Ns78p1853 24210337 1156517462016 2743163 4194304 24210337 1156517462016 (@Ns78p1854 21 1048576 Bool.false 2743163 4194304 1 1102941 (@Ns78p1857 Ns78p495 7196657 8388608 21 1048576 (@Ns78p1858 70368744177664 224011007 70368744177664 Ns78p1855 Ns78p397 Ns78p1856 Ns78p495 RS079to096.d31 (@Ns78p1859 0 1 153730776820720 9608173551295 70368744177664 224011007 70368744177664 (@Ns78p1860 43705713370362544128 5210127040191 70368744177664 224011007 70368744177664 (@Ns78p1861 31073023 70368744177664 (Ns78p1848 rfl rfl) (Ns78p1848 rfl rfl) rfl) (Ns78p1848 rfl rfl) rfl rfl) qz366 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7196657 8388608) (BSN.cos_neg_of_bound 7196657 8388608 Bool.false 2743163 4194304 1 1102941 (Ns78p1865 rfl rfl)) rfl rfl) 

noncomputable def Ns78p1867 := @Ns78p1834 1220893530131362885477 Ns78p1188 (Ns78p1835 qz542 (@Enclosure.Real.IsNear.of_eq qz782 (@Inv.inv Real Real.instInv (Real.sqrt qz248)) Bool.false 3152515 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz244 (BSN.t_div_two_pi_nonneg qz243 315000 1000 qz246)) Ns78p1839) rfl) (@Ns78p1840 8796093022208 769949902615015 19403143268014227456 (BSN.correction_mk qz245 (BSN.cos_two_pi_p_ne_zero_mk qz243 315000 1000 7 qz246 rfl rfl (@BSN.floor_sqrt_eq_dec qz243 315000 1000 7 qz246 rfl rfl rfl))) (@Ns78p1841 4194304 2743163 4194304 24210337 1156517462016 6576812844227 8796093022208 769949902615015 19403143268014227456 (@Ns78p1842 4194304 (Ns78p1852 rfl rfl rfl rfl rfl) rfl) (Ns78p1866 rfl) rfl)) 

noncomputable def Ns78p1868 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz243) (hardyZApproximantRS₀ qz243) Bool.false 120506069167500549577 73786976294838206464 154939870678065578127205 Ns78p1188 (@Eq.refl Real (hardyZApproximantRS₀ qz243)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz243) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz243) qz243 7) (@HMul.hMul Real Real Real qz5 qz778 (Zeta.RiemannSiegel.correction qz245))) Bool.false 120506069167500549577 73786976294838206464 154939870678065578127205 Ns78p1188 (BSN.hardyZApproximantRS₀_eq qz243 7 (@BSN.floor_sqrt_eq_dec qz243 315000 1000 7 qz246 rfl rfl rfl)) (@Ns78p1775 120506069167500549577 73786976294838206464 154939870678065578127205 Ns78p1188 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz243) qz243 7) (@HAdd.hAdd Real Real Real qz351 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz243) qz243 7)) Bool.false 45371311 33554432 63379 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz243) qz243 7) (Ns78p1833 (Ns78p1832 rfl) rfl rfl)) (Ns78p1867 rfl) rfl rfl)) 

theorem RS079to096.d56 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz243) Bool.false 120506069167500549577 73786976294838206464 154939870678065578127205 Ns78p1188 := Ns78p1868 

noncomputable def Ns78p1869 := nat_lit 2906524336485898081271808 

noncomputable def Ns78p1870 := nat_lit 642054934871550060337823744 

noncomputable abbrev qz919 := (Enclosure.sfrac Bool.false 316604 1000)

noncomputable abbrev qz785 := qz919

noncomputable abbrev qz594 := qz785

noncomputable abbrev qz255 := qz594

noncomputable abbrev qz920 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 316604 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz786 := qz920

noncomputable abbrev qz595 := qz786

noncomputable abbrev qz256 := qz595

noncomputable abbrev qz921 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 316604 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz787 := qz921

noncomputable abbrev qz596 := qz787

noncomputable abbrev qz257 := qz596

noncomputable abbrev qz788 := (@HMul.hMul Real Real Real qz5 qz193 (@HPow.hPow Real Real Real qz7 qz256 qz9))

noncomputable def Ns78p1871 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz255) qz255 7) (@HMul.hMul Real Real Real qz5 qz788 (Zeta.RiemannSiegel.correction qz257)) 74104393 16777216 63695 33554432 2469864567085905675 9223372036854775808 47024893716658108513 Ns78p1869 Ns78p1870 

noncomputable def Ns78p1872 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz255) qz255 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 316604 1000 67 98 67108864 33554432 1125899906842624 Bool.false 30991782316 1251 

noncomputable def Ns78p1873 := Ns78p1872 120242927 62 27397080 8 130587807 62 25364760 8 Bool.true 130235406 47259 Bool.true 14847420 Bool.true 22232738 3537118876014220 1 Bool.false 14726588 Bool.false Bool.false 63459642 Bool.true Bool.true 148208786 

noncomputable def Ns78p1874 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz255) qz255 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 316604 1000 14 30 67108864 33554432 1125899906842624 Bool.false 30991782316 1251 

noncomputable def Ns78p1875 := Ns78p1874 93032624 61 33554424 8 108007536 61 30011992 8 Bool.true 85325646 27760 Bool.false 61480428 Bool.true 41404899 3537118876014220 1 Bool.false 40862236 Bool.true Bool.false 54735925 Bool.true Bool.true 130235406 

noncomputable def Ns78p1876 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz255) qz255 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 316604 1000 154 72 67108864 33554432 1125899906842624 Bool.false 30991782316 1251 

noncomputable def Ns78p1877 := Ns78p1876 46516304 61 47453136 16 73726608 61 38745320 8 Bool.true 67108848 1317 Bool.false 30723416 Bool.false 59809607 3537118876014220 1 Bool.false 60198031 Bool.true Bool.false 42174816 Bool.false Bool.true 85325646 

noncomputable def Ns78p1878 := nat_lit 287667403440821817776032675259388517534759638112067 

noncomputable def Ns78p1879 := nat_lit 622908113442758028455857613920960258982805504000 

noncomputable def Ns78p1880 := nat_lit 40336128000000000000000000 

noncomputable def Ns78p1881 := nat_lit 1526954051811337955778007531520000 

noncomputable def Ns78p1882 := nat_lit 2900641939801899848765961890672148480 

noncomputable def Ns78p1883 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz255 316604 1000 400953371264 16000000 633208 4000 2000 Ns78p1881 Ns78p1882 (@Eq.refl Real qz255) rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns78p1884 := nat_lit 3016411352303631783963212384927885741625281222929987665920 

noncomputable abbrev qz789 := (Real.log (Enclosure.sfrac Bool.false 400953371264 16000000))

noncomputable abbrev qz258 := (@HSub.hSub Real Real Real qz339 (@HMul.hMul Real Real Real qz336 (Enclosure.sfrac Bool.false 316604 4000) qz789) (@HMul.hMul Real Real Real qz336 qz341 (@HSub.hSub Real Real Real qz339 qz342 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz343 (@Nat.cast Real Real.instNatCast 633208))))))

noncomputable abbrev qz790 := (Enclosure.sfrac Bool.false 316604 2000)

noncomputable abbrev qz597 := (@HSub.hSub Real Real Real qz12 (@HSub.hSub Real Real Real qz12 qz258 qz790) (@HMul.hMul Real Real Real qz5 qz790 (Real.log Real.pi)))

noncomputable def Ns78p1885 := @Enclosure.Real.IsNear.addLit_ft_p qz597 (Enclosure.sfrac Bool.true Ns78p1881 Ns78p1882) 1039912837674989988279 2251799813685248000 751568971124189299217 Ns78p1880 Ns78p1881 Ns78p1882 0 1 Ns78p1884 

noncomputable def Ns78p1886 := nat_lit 17446842298846244831194251264000 

noncomputable abbrev qz598 := (@HSub.hSub Real Real Real qz12 qz258 qz790)

noncomputable abbrev qz599 := (@HMul.hMul Real Real Real qz5 qz790 (Real.log Real.pi))

noncomputable def Ns78p1887 := @Enclosure.Real.IsNear.subLit_ff_p qz598 qz599 1447968304542397442487 2251799813685248000 1449125174617461557 157563000000000000000000 3040250143911 16777216000 79151 8388608000 Ns78p1886 1039912837674989988279 2251799813685248000 

noncomputable def Ns78p1888 := nat_lit 2895936609084794884974000 

noncomputable abbrev qz600 := qz790

noncomputable def Ns78p1889 := @Enclosure.Real.IsNear.subLit_ff_p qz258 qz600 1804432718648399571383 2251799813685248000 1449125174617461557 157563000000000000000000 316604 2000 0 1 Ns78p1888 1447968304542397442487 2251799813685248000 1449125174617461557 157563000000000000000000 

noncomputable def Ns78p1890 := nat_lit 4063221259660031679177898060870057984 

noncomputable def Ns78p1891 := nat_lit 12245223763757437231824896 

noncomputable def Ns78p1892 := nat_lit 170843144345348883781708170383944782762278530799733430375706175257913986070368765749755159076483952020796598307931050475520 

noncomputable def Ns78p1893 := nat_lit 2563249506432439787519923222500507323681419183412570678395522290026633622182006010133710389021864237553059443715975675904 

noncomputable def Ns78p1894 := nat_lit 2509687683920446640020025064909199916801971229266741600230144767474527634555474457147556409718412079222550240952320 

noncomputable def Ns78p1895 := BSN.log_dyadic_bound 138809371264 663097371264 6 5 Ns78p1892 33554432 8823528 Ns78p1893 Ns78p1894 14258995 801906742528 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 138809371264) (BSN.artanhQ 663097371264) 0 5 Ns78p1893 Ns78p1892 Ns78p1894 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns78p1896 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 316604 4000) qz789 316604 4000 0 1 22808506644810433 2251799813685248 62500007720587 551470500000000000000 1805316109443390582383 2251799813685248000 4946938111092181637 551470500000000000000000 (Enclosure.Real.IsNear.const Bool.false 316604 4000) (BSN.isNear_log_sfrac 400953371264 16000000 22808506644810433 2251799813685248 62500007720587 551470500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 400953371264) qz347)) Bool.false Ns78p1891 Ns78p84 1000000123529392 8823528000000000000000 22808506644810433 2251799813685248 62500007720587 551470500000000000000 (BSN.log_rat_reduce_isNear 400953371264 16000000 14 801906742528 524288000000 14258995 33554432 24973259072661432 36028797018963968 8823528 1000000000000000 rfl rfl rfl rfl (Ns78p1895 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns78p1897 := BSN.arctan_dyadic_bound_f 1000 633208 1 0 4194304 1102941 0 1 1 0 1 1 6623 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 633208) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 633208) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz601 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 633208)))

noncomputable def Ns78p1898 := @Enclosure.Real.IsNear.subLit_ff_p qz15 qz601 884279719003555 562949953421312 1 2000000000000000 6623 4194304 1 1102941 3705209544993977401344 883390794991011 562949953421312 2000000001102941 2205882000000000000000 qz17 (Ns78p1897 rfl) rfl rfl 

noncomputable def Ns78p1899 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 316604 4000) qz789) (@HMul.hMul Real Real Real qz5 qz18 (@HSub.hSub Real Real Real qz12 qz15 qz601)) 1805316109443390582383 2251799813685248000 4946938111092181637 551470500000000000000000 883390794991011 2251799813685248 2000000001102941 8823528000000000000000 Ns78p1890 1804432718648399571383 2251799813685248000 1449125174617461557 157563000000000000000000 (Ns78p1896 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@HSub.hSub Real Real Real qz12 qz15 qz601) 1 4 0 1 883390794991011 562949953421312 2000000001102941 2205882000000000000000 883390794991011 2251799813685248 2000000001102941 8823528000000000000000 qz350 Ns78p1898 rfl) 

noncomputable def Ns78p1900 := @Ns78p1885 Ns78p1878 Ns78p1879 751568971124189299217 Ns78p1880 (@Ns78p1887 751568971124189299217 Ns78p1880 (Ns78p1889 (Ns78p1899 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 316604 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz600 (Real.log Real.pi) 316604 2000 0 1 38410761 33554432 1 16777216 3040250143911 16777216000 79151 8388608000 (Enclosure.Real.IsNear.const Bool.false 316604 2000) RS079to096.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns78p1881 Ns78p1882) 

noncomputable def Ns78p1901 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz255) Bool.false Ns78p1878 Ns78p1879 751568971124189299217 Ns78p1880 3873972789 8388608 157 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz255) (@HAdd.hAdd Real Real Real qz351 qz597 (Enclosure.sfrac Bool.true Ns78p1881 Ns78p1882)) Bool.false Ns78p1878 Ns78p1879 751568971124189299217 Ns78p1880 Ns78p1883 (Ns78p1900 rfl rfl)) 

noncomputable def Ns78p1902 := nat_lit 1898279699759335617855488 

noncomputable def Ns78p1903 := nat_lit 139783204860565253061567234157026390937453994421535725933430534823414593031712976011520 

noncomputable def Ns78p1904 := nat_lit 280442107998464744792493705031379996642444752367967317098465153252207591090797281536 

noncomputable def Ns78p1905 := nat_lit 365644820745673386526821575841208789603529836743045430359872933337010836126053646336256 

noncomputable def Ns78p1906 := BSN.sin_dyadic_bound_f 26976177022 17179869184 3 2 8388608 2208037 Ns78p1903 Ns78p97 Ns78p1904 Ns78p1905 Ns78p100 Ns78p1904 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26976177022) qz352 0 2 Ns78p1903 Ns78p97 Ns78p1904 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26976177022) qz353 0 2 Ns78p1905 Ns78p100 Ns78p1904 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1907 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz255) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3873972789) qz354) Bool.false 3873972789 8388608 157 8388608 Bool.true 8388606 8388608 1 1102941 (Ns78p1901 rfl) (Enclosure.sfrac_false_div 3873972789 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3873972789) qz354) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns78p1902) qz355) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 73 1000000000000000 2205882 1102941 (BSN.sin_reduce_arg_pos_rat_q1 3873972789 8388608 226375608064910080 72057594037927936 73 Ns78p1902 Ns78p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388606 8388608 Ns78p1902 Ns78p84 26976177022 17179869184 2208037 2205882 (Ns78p1906 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns78p1908 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz255) Bool.false Ns78p1878 Ns78p1879 751568971124189299217 Ns78p1880 30991782316 67108864 1251 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz255) (@HAdd.hAdd Real Real Real qz351 qz597 (Enclosure.sfrac Bool.true Ns78p1881 Ns78p1882)) Bool.false Ns78p1878 Ns78p1879 751568971124189299217 Ns78p1880 Ns78p1883 (Ns78p1900 rfl rfl)) 

noncomputable def Ns78p1909 := Ns78p1877 27760 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 154 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 60198031 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 72 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 42174816 67108864) (@Eq.refl Real qz255) rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz255) qz255 1) Bool.true 4194303 4194304 181550345 9252139696128 67108848 67108864 1317 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz255) qz255 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz255)) Bool.true 4194303 4194304 181550345 9252139696128 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz255) qz255) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz255)) Bool.true 8388606 8388608 181550345 9252139696128 4194303 4194304 181550345 9252139696128 (Ns78p1907 rfl rfl) rfl)) rfl) (Ns78p1908 rfl) RS079to096.d7 

noncomputable def Ns78p1910 := nat_lit 30361148227655690457002939210457229077449211802771819139669426176 

noncomputable def Ns78p1911 := nat_lit 793882101278021606939078973667190458565214552707466312810496 

noncomputable def Ns78p1912 := nat_lit 91081856918764515327794939473424352851430504979210042486382657536 

noncomputable def Ns78p1913 := BSN.cos_dyadic_bound_f 30723416 67108864 3 2 67108864 33554432 Ns78p1910 Ns78p116 Ns78p1911 Ns78p1912 Ns78p119 Ns78p1911 60198031 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 30723416) qz357 0 2 Ns78p1910 Ns78p116 Ns78p1911 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 30723416) (BSN.cosOddQ 67108864) 0 2 Ns78p1912 Ns78p119 Ns78p1911 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1914 := nat_lit 436189984717913523807486674784483540890446358832854298795386662081 

noncomputable def Ns78p1915 := nat_lit 163744827444297110925540873705127806473701269482169725948587201 

noncomputable def Ns78p1916 := nat_lit 1308242464498851977200608942606040367058391673959598556934262811841 

noncomputable def Ns78p1917 := BSN.cos_dyadic_bound_f 59809607 67108864 3 2 67108864 33554432 Ns78p1914 Ns78p116 Ns78p1915 Ns78p1916 Ns78p119 Ns78p1915 42174816 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 59809607) qz357 0 2 Ns78p1914 Ns78p116 Ns78p1915 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 59809607) (BSN.cosOddQ 67108864) 0 2 Ns78p1916 Ns78p119 Ns78p1915 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1918 := nat_lit 487033033351100339671933160628105332107229573143724591020224086016 

noncomputable def Ns78p1919 := nat_lit 204124464143672413041596830700102958355106540383592356197236736 

noncomputable def Ns78p1920 := nat_lit 1460690851125013674189716288222915790404978506350406588348277784576 

noncomputable def Ns78p1921 := BSN.cos_dyadic_bound_f 61480428 67108864 3 2 67108864 33554432 Ns78p1918 Ns78p116 Ns78p1919 Ns78p1920 Ns78p119 Ns78p1919 40862236 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 61480428) qz357 0 2 Ns78p1918 Ns78p116 Ns78p1919 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 61480428) (BSN.cosOddQ 67108864) 0 2 Ns78p1920 Ns78p119 Ns78p1919 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1922 := nat_lit 100155131863313404762532078073628749492739046796822733654307499681 

noncomputable def Ns78p1923 := nat_lit 8638012670599695485143343581308408368371967259779467157040801 

noncomputable def Ns78p1924 := nat_lit 300448119564599014896625947533723631661480396455948642028608417441 

noncomputable def Ns78p1925 := BSN.cos_dyadic_bound_f 41404899 67108864 3 2 67108864 33554432 Ns78p1922 Ns78p116 Ns78p1923 Ns78p1924 Ns78p119 Ns78p1923 54735925 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 41404899) qz357 0 2 Ns78p1922 Ns78p116 Ns78p1923 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 41404899) (BSN.cosOddQ 67108864) 0 2 Ns78p1924 Ns78p119 Ns78p1923 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1926 := Ns78p1875 47259 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 14 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 40862236 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 30 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 54735925 67108864) (@Eq.refl Real qz255) rfl rfl (Ns78p1909 RS079to096.d9 RS079to096.d11 RS079to096.d13 RS079to096.d17 (Ns78p1913 rfl rfl) (Ns78p1917 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns78p1908 rfl) RS079to096.d19 RS079to096.d21 RS079to096.d23 RS079to096.d25 RS079to096.d17 (Ns78p1921 rfl rfl) (Ns78p1925 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns78p1927 := nat_lit 48596386298375751694860960000 

noncomputable def Ns78p1928 := BSN.sin_dyadic_bound_f 14847420 67108864 2 1 67108864 33554432 Ns78p1927 Ns78p106 Ns78p1927 Ns78p1927 Ns78p107 Ns78p1927 14726588 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 14847420) qz356 0 1 Ns78p1927 Ns78p106 Ns78p1927 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 14847420) (BSN.sinOddQ 67108864) 0 1 Ns78p1927 Ns78p107 Ns78p1927 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1929 := nat_lit 244327190121050829823577502736 

noncomputable def Ns78p1930 := BSN.cos_dyadic_bound_f 22232738 67108864 2 1 67108864 33554432 Ns78p1929 Ns78p228 Ns78p1929 Ns78p1929 Ns78p229 Ns78p1929 63459642 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 22232738) qz357 0 1 Ns78p1929 Ns78p228 Ns78p1929 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 22232738) (BSN.cosOddQ 67108864) 0 1 Ns78p1929 Ns78p229 Ns78p1929 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1931 := Ns78p1873 63695 BSN.abs_quadSignPos qz734 (BSN.sfrac_eq_quadSignPos_mul Bool.false 14726588 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 98 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 63459642 67108864) (@Eq.refl Real qz255) rfl rfl (Ns78p1926 rfl rfl) (Ns78p1908 rfl) RS079to096.d27 RS079to096.d29 RS079to096.d49 RS079to096.d51 RS079to096.d17 (Ns78p1928 rfl rfl) (Ns78p1930 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns78p1932 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz255) qz255 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz255) qz255 7) 148208786 67108864 63695 67108864 148208786 67108864 63695 67108864 19892246526558208 74104393 16777216 63695 33554432 (Ns78p1931 rfl) 

noncomputable def Ns78p1933 := @Enclosure.Real.IsNear.mulLit_tf qz788 (Zeta.RiemannSiegel.correction qz257) 1574257 4194304 1 4194304 1568908105275 2199023255552 413799300835729 9701571634007113728 2469864567085905675 9223372036854775808 

noncomputable abbrev qz791 := (@HPow.hPow Real Real Real qz7 qz256 qz9)

noncomputable def Ns78p1934 := @Enclosure.Real.IsNear.mulLit_tf qz193 qz791 1 1 0 1 1574257 4194304 1 4194304 1574257 4194304 1 4194304 

noncomputable def Ns78p1935 := @Enclosure.Real.IsNear.sqrt_image qz256 105673629439 2097152000 79151 2097152000 29773377 29773400 4194304 (@Enclosure.Real.IsNear.of_eq qz256 (@HMul.hMul Real Real Real qz5 qz255 qz3) Bool.false 105673629439 2097152000 79151 2097152000 (BSN.t_div_two_pi_mk qz255 316604 1000 (@Eq.refl Real qz255)) (@Enclosure.Real.IsNear.mulLit_ff qz255 qz3 316604 1000 0 1 1335089 8388608 1 8388608 105673629439 2097152000 79151 2097152000 (Enclosure.Real.IsNear.const Bool.false 316604 1000) RS079to096.d32 rfl)) 

noncomputable abbrev qz922 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 316604 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz792 := qz922

noncomputable abbrev qz602 := qz792

noncomputable abbrev qz259 := qz602

noncomputable def Ns78p1936 := @Enclosure.Real.IsNear.sqrt_image qz259 59546777 8388608 23 8388608 11174909 11174914 4194304 (@Enclosure.Real.IsNear.recentre' qz259 Bool.false 59546777 8388608 23 8388608 59546777 8388608 23 8388608 (Ns78p1935 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns78p1937 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz259) 22349823 8388608 5 8388608 1574256 1574258 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz259) Bool.false 22349823 8388608 5 8388608 22349823 8388608 5 8388608 (Ns78p1936 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns78p1938 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz259)) Bool.false 3148514 8388608 2 8388608 1574257 4194304 1 4194304 (Ns78p1937 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz260 := (@HMul.hMul Real Real Real qz336 qz334 qz596)

noncomputable abbrev qz793 := (@HMul.hMul Real Real Real qz841 qz921 qz921)

noncomputable abbrev qz603 := (@HSub.hSub Real Real Real qz634 (@HSub.hSub Real Real Real qz634 qz793 qz787) qz640)

noncomputable abbrev qz261 := (Real.cos (@HMul.hMul Real Real Real qz336 qz334 qz603))

noncomputable def Ns78p1939 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz257) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv (Real.cos qz260)) qz261) Bool.false 1568908105275 

noncomputable def Ns78p1940 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos qz260)) qz261 2575041 2097152 29 

noncomputable def Ns78p1941 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos qz260)) Bool.false 10300164 8388608 232 8388608 2575041 2097152 29 

noncomputable def Ns78p1942 := @Enclosure.Real.IsNear.recentre' (Real.cos qz260) Bool.false 3415904 4194304 84708997 4626069848064 106747 131072 84708997 4626069848064 

noncomputable def Ns78p1943 := @Enclosure.Real.IsNear.cos_image qz260 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 162287) (@Nat.cast Real Real.instNatCast 262144)) Bool.false 162287 262144 73 4194304 Bool.false 3415904 4194304 1 

noncomputable def Ns78p1944 := nat_lit 620679734415112806797800673 

noncomputable def Ns78p1945 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz257 884279719003555 140737488355328 1 500000000000000 826521 8388608 23 8388608 730875757630537282155 1180591620717411303424 Ns78p1944 

noncomputable def Ns78p1946 := @Enclosure.Real.IsNear.subLit_ff_p qz259 qz191 59546777 8388608 23 8388608 7 1 0 1 826521 826521 8388608 23 

noncomputable def Ns78p1947 := @Ns78p1946 8388608 (@Enclosure.Real.IsNear.recentre' qz259 Bool.false 59546777 8388608 23 8388608 59546777 8388608 23 8388608 (Ns78p1935 rfl rfl rfl rfl rfl rfl) rfl) qz539 

noncomputable def Ns78p1948 := @Enclosure.Real.IsNear.recentre' qz260 Bool.false 730875757630537282155 1180591620717411303424 Ns78p1944 Ns78p385 162287 262144 73 4194304 (@Ns78p1945 Ns78p385 RS079to096.d31 (Ns78p1947 rfl rfl) rfl) 

noncomputable def Ns78p1949 := nat_lit 5503536700918758713426248343089642737173712001 

noncomputable def Ns78p1950 := nat_lit 899166046404754725066720160753181935921130373120 

noncomputable def Ns78p1951 := nat_lit 481138219246040638072070706077751426337921 

noncomputable def Ns78p1952 := nat_lit 16509647826317784059002600887856772708668460161 

noncomputable def Ns78p1953 := nat_lit 40462472088213962628002407233893187116450866790400 

noncomputable def Ns78p1954 := BSN.cos_dyadic_bound_f 162287 262144 3 2 4194304 1102941 Ns78p1949 Ns78p1950 Ns78p1951 Ns78p1952 Ns78p1953 Ns78p1951 3415904 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 162287) (BSN.cosEvenQ 262144) 0 2 Ns78p1949 Ns78p1950 Ns78p1951 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 162287) (BSN.cosOddQ 262144) 0 2 Ns78p1952 Ns78p1953 Ns78p1951 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1955 := @Enclosure.Real.IsNear.inv_image (Real.cos qz260) 106747 131072 84708997 4626069848064 5149966 5150198 4194304 (Ns78p1942 (@Ns78p1943 1102941 (Ns78p1948 rfl) (Enclosure.sfrac_false_div 162287 262144) (Ns78p1954 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns78p1956 := @Enclosure.Real.IsNear.recentre' qz261 Bool.false 2437100 4194304 

noncomputable abbrev qz262 := (@HMul.hMul Real Real Real qz336 qz334 qz603)

noncomputable def Ns78p1957 := @Enclosure.Real.IsNear.cos_image qz262 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 996963)) (@Nat.cast Real Real.instNatCast 1048576)) Bool.true 996963 1048576 

noncomputable def Ns78p1958 := nat_lit 9416049398396647339522632205 

noncomputable def Ns78p1959 := nat_lit 1246532586148716705408826203674069 

noncomputable def Ns78p1960 := @Enclosure.Real.IsNear.recentre' qz262 Bool.true Ns78p1958 Ns78p397 Ns78p1959 

noncomputable abbrev qz263 := qz603

noncomputable def Ns78p1961 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz263 884279719003555 140737488355328 1 500000000000000 10648270220431 

noncomputable abbrev qz604 := (@HSub.hSub Real Real Real qz634 qz793 qz787)

noncomputable abbrev qz264 := qz604

noncomputable def Ns78p1962 := @Enclosure.Real.IsNear.subLit_tf qz264 qz26 6250223709327 70368744177664 230958479 70368744177664 1 16 

noncomputable abbrev qz605 := qz793

noncomputable abbrev qz265 := qz605

noncomputable def Ns78p1963 := @Enclosure.Real.IsNear.subLit_ff_n qz265 qz257 683136963441 70368744177664 38020495 70368744177664 826521 8388608 23 8388608 

noncomputable def Ns78p1964 := @Enclosure.Real.IsNear.mulLit_ff qz257 qz257 826521 8388608 23 8388608 826521 8388608 23 8388608 683136963441 70368744177664 

noncomputable def Ns78p1965 := nat_lit 2007410974132698900360774172356256471689081433930401 

noncomputable def Ns78p1966 := nat_lit 975960691635678766340042064251656754187534645921 

noncomputable def Ns78p1967 := nat_lit 6020281001014825343549642432940266101558869232499361 

noncomputable def Ns78p1968 := BSN.cos_dyadic_bound_f 996963 1048576 3 2 4194304 1102941 Ns78p1965 Ns78p1668 Ns78p1966 Ns78p1967 Ns78p1671 Ns78p1966 2437100 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 996963) (BSN.cosEvenQ 1048576) 0 2 Ns78p1965 Ns78p1668 Ns78p1966 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 996963) (BSN.cosOddQ 1048576) 0 2 Ns78p1967 Ns78p1671 Ns78p1966 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns78p1969 := @Ns78p1956 100150171 4626069848064 609275 1048576 100150171 4626069848064 (@Ns78p1957 87 4194304 Bool.false 2437100 4194304 1 1102941 (@Ns78p1960 Ns78p400 996963 1048576 87 4194304 (@Ns78p1961 70368744177664 230958479 70368744177664 Ns78p1958 Ns78p397 Ns78p1959 Ns78p400 RS079to096.d31 (@Ns78p1962 0 1 170372323526896 10648270220431 70368744177664 230958479 70368744177664 (@Ns78p1963 52430676609850146816 6250223709327 70368744177664 230958479 70368744177664 (@Ns78p1964 38020495 70368744177664 (Ns78p1947 rfl rfl) (Ns78p1947 rfl rfl) rfl) (Ns78p1947 rfl rfl) rfl rfl) qz366 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 996963 1048576) (BSN.cos_neg_of_bound 996963 1048576 Bool.false 2437100 4194304 1 1102941 (Ns78p1968 rfl rfl)) rfl rfl) 

noncomputable def Ns78p1970 := @Ns78p1933 47024893716658108513 Ns78p1869 (Ns78p1934 qz542 (@Enclosure.Real.IsNear.of_eq qz791 (@Inv.inv Real Real.instInv (Real.sqrt qz259)) Bool.false 1574257 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz256 (BSN.t_div_two_pi_nonneg qz255 316604 1000 (@Eq.refl Real qz255))) Ns78p1938) rfl) (@Ns78p1939 2199023255552 413799300835729 9701571634007113728 (BSN.correction_mk qz257 (BSN.cos_two_pi_p_ne_zero_mk qz255 316604 1000 7 (@Eq.refl Real qz255) rfl rfl (@BSN.floor_sqrt_eq_dec qz255 316604 1000 7 (@Eq.refl Real qz255) rfl rfl rfl))) (@Ns78p1940 1048576 609275 1048576 100150171 4626069848064 1568908105275 2199023255552 413799300835729 9701571634007113728 (@Ns78p1941 1048576 (Ns78p1955 rfl rfl rfl rfl rfl) rfl) (Ns78p1969 rfl) rfl)) 

noncomputable def Ns78p1971 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz255) (hardyZApproximantRS₀ qz255) Bool.true 38269456319305304309 9223372036854775808 5564360654681685866593 Ns78p1869 (@Eq.refl Real (hardyZApproximantRS₀ qz255)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz255) (@HSub.hSub Real Real Real qz12 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz255) qz255 7) (@HMul.hMul Real Real Real qz5 qz788 (Zeta.RiemannSiegel.correction qz257))) Bool.true 38269456319305304309 9223372036854775808 5564360654681685866593 Ns78p1869 (BSN.hardyZApproximantRS₀_eq qz255 7 (@BSN.floor_sqrt_eq_dec qz255 316604 1000 7 (@Eq.refl Real qz255) rfl rfl rfl)) (@Ns78p1871 38269456319305304309 9223372036854775808 5564360654681685866593 Ns78p1869 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz255) qz255 7) (@HAdd.hAdd Real Real Real qz351 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz255) qz255 7) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz255) qz255 7)) Bool.true 74104393 16777216 63695 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz255) qz255 7) (Ns78p1932 (Ns78p1931 rfl) rfl rfl)) (Ns78p1970 rfl) rfl rfl)) 

theorem RS079to096.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz255) Bool.true 38269456319305304309 9223372036854775808 5564360654681685866593 Ns78p1869 := Ns78p1971 

noncomputable def RS079to096.d58 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz266 := (RS079to096.d3 qz335 qz367 (@Enclosure.dec_le_dec qz335 qz367 287396 1000 289039 1000 (@Eq.refl Real qz335) qz370 rfl rfl rfl))

noncomputable abbrev qz794 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz266)

noncomputable def Ns78p1972 := @Enclosure.Real.IsNear.of_eq qz794 (hardyZApproximantRS₀ qz4) Bool.true 158074738888800874987 147573952589676412928 94949651305736089811723 Ns78p62 

noncomputable abbrev qz267 := (@Enclosure.dec_le_dec qz335 qz367 287396 1000 289039 1000 (@Eq.refl Real qz335) qz370 rfl rfl rfl)

noncomputable def Ns78p1973 := @Enclosure.Real.IsNear.neg_val qz794 158074738888800874987 147573952589676412928 94949651305736089811723 Ns78p62 (Ns78p1972 (RS079to096.d4 qz4 qz29 qz267) RS079to096.d33) rfl 

noncomputable abbrev qz795 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz266)

noncomputable def Ns78p1974 := @Enclosure.Real.IsNear.of_eq qz795 (hardyZApproximantRS₀ qz29) Bool.false 597130383470892242549 295147905179352825856 175633941352234453268851 Ns78p174 

noncomputable def Ns78p1975 := @Enclosure.Real.IsNear.pos_val qz795 597130383470892242549 295147905179352825856 175633941352234453268851 Ns78p174 (Ns78p1974 (RS079to096.d34 qz4 qz29 qz267) RS079to096.d35) rfl 

noncomputable def Ns78p1976 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz794 qz4 qz4 287396 1000 287396 1000 

noncomputable def Ns78p1977 := @Enclosure.norm_gt_of_isNear qz794 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 158074738888800874987 147573952589676412928 94949651305736089811723 

noncomputable def Ns78p1978 := @Ns78p1977 Ns78p62 169724753 1342177280 1213 1342177280 (Ns78p1972 (RS079to096.d4 qz4 qz29 qz267) RS079to096.d33) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p1979 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz795 qz4 qz29 287396 1000 289039 1000 

noncomputable def Ns78p1980 := @Enclosure.norm_gt_of_isNear qz795 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 597130383470892242549 295147905179352825856 175633941352234453268851 

noncomputable def Ns78p1981 := @Ns78p1980 Ns78p174 169724753 1342177280 1213 1342177280 (Ns78p1974 (RS079to096.d34 qz4 qz29 qz267) RS079to096.d35) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p1982 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz266 (@BSN.thirtyTwoPi_le_dec qz4 287396 1000 qz11 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz794 qz795 (Ns78p1973 rfl rfl) (Ns78p1975 rfl rfl)) (Ns78p1976 qz11 qz11 rfl rfl rfl rfl (Ns78p1978 rfl)) (Ns78p1979 qz11 qz32 rfl rfl rfl rfl (Ns78p1981 rfl)) 

noncomputable abbrev qz268 := (RS079to096.d3 qz367 qz386 (@Enclosure.dec_le_dec qz367 qz386 289039 1000 290679 1000 qz370 qz389 rfl rfl rfl))

noncomputable abbrev qz796 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz268)

noncomputable def Ns78p1983 := @Enclosure.Real.IsNear.of_eq qz796 (hardyZApproximantRS₀ qz29) Bool.false 597130383470892242549 295147905179352825856 175633941352234453268851 Ns78p174 

noncomputable abbrev qz269 := (@Enclosure.dec_le_dec qz367 qz386 289039 1000 290679 1000 qz370 qz389 rfl rfl rfl)

noncomputable def Ns78p1984 := @Enclosure.Real.IsNear.pos_val qz796 597130383470892242549 295147905179352825856 175633941352234453268851 Ns78p174 (Ns78p1983 (RS079to096.d4 qz29 qz48 qz269) RS079to096.d35) rfl 

noncomputable abbrev qz797 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz268)

noncomputable def Ns78p1985 := @Enclosure.Real.IsNear.of_eq qz797 (hardyZApproximantRS₀ qz48) Bool.true 329713144771858419035 73786976294838206464 12358783019591542135547 Ns78p310 

noncomputable def Ns78p1986 := @Enclosure.Real.IsNear.neg_val qz797 329713144771858419035 73786976294838206464 12358783019591542135547 Ns78p310 (Ns78p1985 (RS079to096.d34 qz29 qz48 qz269) RS079to096.d37) rfl 

noncomputable def Ns78p1987 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz796 qz4 qz29 287396 1000 289039 1000 

noncomputable def Ns78p1988 := @Enclosure.norm_gt_of_isNear qz796 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 597130383470892242549 295147905179352825856 175633941352234453268851 

noncomputable def Ns78p1989 := @Ns78p1988 Ns78p174 169724753 1342177280 1213 1342177280 (Ns78p1983 (RS079to096.d4 qz29 qz48 qz269) RS079to096.d35) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p1990 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz797 qz4 qz48 287396 1000 290679 1000 

noncomputable def Ns78p1991 := @Enclosure.norm_gt_of_isNear qz797 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 329713144771858419035 73786976294838206464 12358783019591542135547 

noncomputable def Ns78p1992 := @Ns78p1991 Ns78p310 169724753 1342177280 1213 1342177280 (Ns78p1985 (RS079to096.d34 qz29 qz48 qz269) RS079to096.d37) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p1993 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz268 (@BSN.thirtyTwoPi_le_dec qz29 289039 1000 qz32 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz796 qz797 (Ns78p1984 rfl rfl) (Ns78p1986 rfl rfl)) (Ns78p1987 qz11 qz32 rfl rfl rfl rfl (Ns78p1989 rfl)) (Ns78p1990 qz11 qz51 rfl rfl rfl rfl (Ns78p1992 rfl)) 

noncomputable abbrev qz270 := (RS079to096.d3 qz386 qz401 (@Enclosure.dec_le_dec qz386 qz401 290679 1000 292316 1000 qz389 qz404 rfl rfl rfl))

noncomputable abbrev qz798 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz270)

noncomputable def Ns78p1994 := @Enclosure.Real.IsNear.of_eq qz798 (hardyZApproximantRS₀ qz48) Bool.true 329713144771858419035 73786976294838206464 12358783019591542135547 Ns78p310 

noncomputable abbrev qz271 := (@Enclosure.dec_le_dec qz386 qz401 290679 1000 292316 1000 qz389 qz404 rfl rfl rfl)

noncomputable def Ns78p1995 := @Enclosure.Real.IsNear.neg_val qz798 329713144771858419035 73786976294838206464 12358783019591542135547 Ns78p310 (Ns78p1994 (RS079to096.d4 qz48 qz61 qz271) RS079to096.d37) rfl 

noncomputable abbrev qz799 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz270)

noncomputable def Ns78p1996 := @Enclosure.Real.IsNear.of_eq qz799 (hardyZApproximantRS₀ qz61) Bool.false 33274465139920088745 18446744073709551616 3587024965240770556173 Ns78p414 

noncomputable def Ns78p1997 := @Enclosure.Real.IsNear.pos_val qz799 33274465139920088745 18446744073709551616 3587024965240770556173 Ns78p414 (Ns78p1996 (RS079to096.d34 qz48 qz61 qz271) RS079to096.d38) rfl 

noncomputable def Ns78p1998 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz798 qz4 qz48 287396 1000 290679 1000 

noncomputable def Ns78p1999 := @Enclosure.norm_gt_of_isNear qz798 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 329713144771858419035 73786976294838206464 12358783019591542135547 

noncomputable def Ns78p2000 := @Ns78p1999 Ns78p310 169724753 1342177280 1213 1342177280 (Ns78p1994 (RS079to096.d4 qz48 qz61 qz271) RS079to096.d37) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2001 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz799 qz4 qz61 287396 1000 292316 1000 

noncomputable def Ns78p2002 := @Enclosure.norm_gt_of_isNear qz799 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 33274465139920088745 18446744073709551616 3587024965240770556173 

noncomputable def Ns78p2003 := @Ns78p2002 Ns78p414 169724753 1342177280 1213 1342177280 (Ns78p1996 (RS079to096.d34 qz48 qz61 qz271) RS079to096.d38) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2004 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz270 (@BSN.thirtyTwoPi_le_dec qz48 290679 1000 qz51 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz798 qz799 (Ns78p1995 rfl rfl) (Ns78p1997 rfl rfl)) (Ns78p1998 qz11 qz51 rfl rfl rfl rfl (Ns78p2000 rfl)) (Ns78p2001 qz11 qz64 rfl rfl rfl rfl (Ns78p2003 rfl)) 

noncomputable abbrev qz272 := (RS079to096.d3 qz401 qz414 (@Enclosure.dec_le_dec qz401 qz414 292316 1000 294360 1000 qz404 qz417 rfl rfl rfl))

noncomputable abbrev qz800 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz272)

noncomputable def Ns78p2005 := @Enclosure.Real.IsNear.of_eq qz800 (hardyZApproximantRS₀ qz61) Bool.false 33274465139920088745 18446744073709551616 3587024965240770556173 Ns78p414 

noncomputable abbrev qz273 := (@Enclosure.dec_le_dec qz401 qz414 292316 1000 294360 1000 qz404 qz417 rfl rfl rfl)

noncomputable def Ns78p2006 := @Enclosure.Real.IsNear.pos_val qz800 33274465139920088745 18446744073709551616 3587024965240770556173 Ns78p414 (Ns78p2005 (RS079to096.d4 qz61 qz74 qz273) RS079to096.d38) rfl 

noncomputable abbrev qz801 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz272)

noncomputable def Ns78p2007 := @Enclosure.Real.IsNear.of_eq qz801 (hardyZApproximantRS₀ qz74) Bool.true 240778162067263299389 295147905179352825856 171991608233731118648407 Ns78p174 

noncomputable def Ns78p2008 := @Enclosure.Real.IsNear.neg_val qz801 240778162067263299389 295147905179352825856 171991608233731118648407 Ns78p174 (Ns78p2007 (RS079to096.d34 qz61 qz74 qz273) RS079to096.d39) rfl 

noncomputable def Ns78p2009 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz800 qz4 qz61 287396 1000 292316 1000 

noncomputable def Ns78p2010 := @Enclosure.norm_gt_of_isNear qz800 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 33274465139920088745 18446744073709551616 3587024965240770556173 

noncomputable def Ns78p2011 := @Ns78p2010 Ns78p414 169724753 1342177280 1213 1342177280 (Ns78p2005 (RS079to096.d4 qz61 qz74 qz273) RS079to096.d38) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2012 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz801 qz4 qz74 287396 1000 294360 1000 

noncomputable def Ns78p2013 := @Enclosure.norm_gt_of_isNear qz801 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 240778162067263299389 295147905179352825856 171991608233731118648407 

noncomputable def Ns78p2014 := @Ns78p2013 Ns78p174 169724753 1342177280 1213 1342177280 (Ns78p2007 (RS079to096.d34 qz61 qz74 qz273) RS079to096.d39) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2015 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz272 (@BSN.thirtyTwoPi_le_dec qz61 292316 1000 qz64 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz800 qz801 (Ns78p2006 rfl rfl) (Ns78p2008 rfl rfl)) (Ns78p2009 qz11 qz64 rfl rfl rfl rfl (Ns78p2011 rfl)) (Ns78p2012 qz11 qz77 rfl rfl rfl rfl (Ns78p2014 rfl)) 

noncomputable abbrev qz274 := (RS079to096.d3 qz414 qz427 (@Enclosure.dec_le_dec qz414 qz427 294360 1000 295176 1000 qz417 qz430 rfl rfl rfl))

noncomputable abbrev qz802 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz274)

noncomputable def Ns78p2016 := @Enclosure.Real.IsNear.of_eq qz802 (hardyZApproximantRS₀ qz74) Bool.true 240778162067263299389 295147905179352825856 171991608233731118648407 Ns78p174 

noncomputable abbrev qz275 := (@Enclosure.dec_le_dec qz414 qz427 294360 1000 295176 1000 qz417 qz430 rfl rfl rfl)

noncomputable def Ns78p2017 := @Enclosure.Real.IsNear.neg_val qz802 240778162067263299389 295147905179352825856 171991608233731118648407 Ns78p174 (Ns78p2016 (RS079to096.d4 qz74 qz87 qz275) RS079to096.d39) rfl 

noncomputable abbrev qz803 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz274)

noncomputable def Ns78p2018 := @Enclosure.Real.IsNear.of_eq qz803 (hardyZApproximantRS₀ qz87) Bool.false 28287918745940017749 147573952589676412928 258228364968443225547265 Ns78p603 

noncomputable def Ns78p2019 := @Enclosure.Real.IsNear.pos_val qz803 28287918745940017749 147573952589676412928 258228364968443225547265 Ns78p603 (Ns78p2018 (RS079to096.d34 qz74 qz87 qz275) RS079to096.d40) rfl 

noncomputable def Ns78p2020 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz802 qz4 qz74 287396 1000 294360 1000 

noncomputable def Ns78p2021 := @Enclosure.norm_gt_of_isNear qz802 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 240778162067263299389 295147905179352825856 171991608233731118648407 

noncomputable def Ns78p2022 := @Ns78p2021 Ns78p174 169724753 1342177280 1213 1342177280 (Ns78p2016 (RS079to096.d4 qz74 qz87 qz275) RS079to096.d39) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2023 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz803 qz4 qz87 287396 1000 295176 1000 

noncomputable def Ns78p2024 := @Enclosure.norm_gt_of_isNear qz803 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 28287918745940017749 147573952589676412928 258228364968443225547265 

noncomputable def Ns78p2025 := @Ns78p2024 Ns78p603 169724753 1342177280 1213 1342177280 (Ns78p2018 (RS079to096.d34 qz74 qz87 qz275) RS079to096.d40) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2026 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz274 (@BSN.thirtyTwoPi_le_dec qz74 294360 1000 qz77 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz802 qz803 (Ns78p2017 rfl rfl) (Ns78p2019 rfl rfl)) (Ns78p2020 qz11 qz77 rfl rfl rfl rfl (Ns78p2022 rfl)) (Ns78p2023 qz11 qz90 rfl rfl rfl rfl (Ns78p2025 rfl)) 

noncomputable abbrev qz276 := (RS079to096.d3 qz427 qz440 (@Enclosure.dec_le_dec qz427 qz440 295176 1000 296399 1000 qz430 qz443 rfl rfl rfl))

noncomputable abbrev qz804 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz276)

noncomputable def Ns78p2027 := @Enclosure.Real.IsNear.of_eq qz804 (hardyZApproximantRS₀ qz87) Bool.false 28287918745940017749 147573952589676412928 258228364968443225547265 Ns78p603 

noncomputable abbrev qz277 := (@Enclosure.dec_le_dec qz427 qz440 295176 1000 296399 1000 qz430 qz443 rfl rfl rfl)

noncomputable def Ns78p2028 := @Enclosure.Real.IsNear.pos_val qz804 28287918745940017749 147573952589676412928 258228364968443225547265 Ns78p603 (Ns78p2027 (RS079to096.d4 qz87 qz100 qz277) RS079to096.d40) rfl 

noncomputable abbrev qz805 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz276)

noncomputable def Ns78p2029 := @Enclosure.Real.IsNear.of_eq qz805 (hardyZApproximantRS₀ qz100) Bool.true 46983466899740965687 18446744073709551616 64753251295676680114549 Ns78p694 

noncomputable def Ns78p2030 := @Enclosure.Real.IsNear.neg_val qz805 46983466899740965687 18446744073709551616 64753251295676680114549 Ns78p694 (Ns78p2029 (RS079to096.d34 qz87 qz100 qz277) RS079to096.d41) rfl 

noncomputable def Ns78p2031 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz804 qz4 qz87 287396 1000 295176 1000 

noncomputable def Ns78p2032 := @Enclosure.norm_gt_of_isNear qz804 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 28287918745940017749 147573952589676412928 258228364968443225547265 

noncomputable def Ns78p2033 := @Ns78p2032 Ns78p603 169724753 1342177280 1213 1342177280 (Ns78p2027 (RS079to096.d4 qz87 qz100 qz277) RS079to096.d40) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2034 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz805 qz4 qz100 287396 1000 296399 1000 

noncomputable def Ns78p2035 := @Enclosure.norm_gt_of_isNear qz805 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 46983466899740965687 18446744073709551616 64753251295676680114549 

noncomputable def Ns78p2036 := @Ns78p2035 Ns78p694 169724753 1342177280 1213 1342177280 (Ns78p2029 (RS079to096.d34 qz87 qz100 qz277) RS079to096.d41) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2037 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz276 (@BSN.thirtyTwoPi_le_dec qz87 295176 1000 qz90 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz804 qz805 (Ns78p2028 rfl rfl) (Ns78p2030 rfl rfl)) (Ns78p2031 qz11 qz90 rfl rfl rfl rfl (Ns78p2033 rfl)) (Ns78p2034 qz11 qz103 rfl rfl rfl rfl (Ns78p2036 rfl)) 

noncomputable abbrev qz606 := (@Enclosure.dec_le_dec qz677 qz684 296399 1000 298842 1000 (@Eq.refl Real qz677) (@Eq.refl Real qz684) rfl rfl rfl)

noncomputable abbrev qz278 := (RS079to096.d3 qz440 qz453 qz606)

noncomputable abbrev qz806 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz278)

noncomputable def Ns78p2038 := @Enclosure.Real.IsNear.of_eq qz806 (hardyZApproximantRS₀ qz100) Bool.true 46983466899740965687 18446744073709551616 64753251295676680114549 Ns78p694 

noncomputable abbrev qz279 := qz606

noncomputable def Ns78p2039 := @Enclosure.Real.IsNear.neg_val qz806 46983466899740965687 18446744073709551616 64753251295676680114549 Ns78p694 (Ns78p2038 (RS079to096.d4 qz100 qz113 qz279) RS079to096.d41) rfl 

noncomputable abbrev qz807 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz278)

noncomputable def Ns78p2040 := @Enclosure.Real.IsNear.of_eq qz807 (hardyZApproximantRS₀ qz113) Bool.false 489445846483293468957 147573952589676412928 28935310280385915097593 Ns78p794 

noncomputable def Ns78p2041 := @Enclosure.Real.IsNear.pos_val qz807 489445846483293468957 147573952589676412928 28935310280385915097593 Ns78p794 (Ns78p2040 (RS079to096.d34 qz100 qz113 qz279) RS079to096.d42) rfl 

noncomputable def Ns78p2042 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz806 qz4 qz100 287396 1000 296399 1000 

noncomputable def Ns78p2043 := @Enclosure.norm_gt_of_isNear qz806 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 46983466899740965687 18446744073709551616 64753251295676680114549 

noncomputable def Ns78p2044 := @Ns78p2043 Ns78p694 169724753 1342177280 1213 1342177280 (Ns78p2038 (RS079to096.d4 qz100 qz113 qz279) RS079to096.d41) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2045 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz807 qz4 qz113 287396 1000 298842 1000 

noncomputable def Ns78p2046 := @Enclosure.norm_gt_of_isNear qz807 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 489445846483293468957 147573952589676412928 28935310280385915097593 

noncomputable def Ns78p2047 := @Ns78p2046 Ns78p794 169724753 1342177280 1213 1342177280 (Ns78p2040 (RS079to096.d34 qz100 qz113 qz279) RS079to096.d42) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2048 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz278 (@BSN.thirtyTwoPi_le_dec qz100 296399 1000 qz103 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz806 qz807 (Ns78p2039 rfl rfl) (Ns78p2041 rfl rfl)) (Ns78p2042 qz11 qz103 rfl rfl rfl rfl (Ns78p2044 rfl)) (Ns78p2045 qz11 qz116 rfl rfl rfl rfl (Ns78p2047 rfl)) 

noncomputable abbrev qz607 := (@Enclosure.dec_le_dec qz684 qz693 298842 1000 300468 1000 (@Eq.refl Real qz684) qz697 rfl rfl rfl)

noncomputable abbrev qz280 := (RS079to096.d3 qz453 qz465 qz607)

noncomputable abbrev qz808 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz280)

noncomputable def Ns78p2049 := @Enclosure.Real.IsNear.of_eq qz808 (hardyZApproximantRS₀ qz113) Bool.false 489445846483293468957 147573952589676412928 28935310280385915097593 Ns78p794 

noncomputable abbrev qz281 := qz607

noncomputable def Ns78p2050 := @Enclosure.Real.IsNear.pos_val qz808 489445846483293468957 147573952589676412928 28935310280385915097593 Ns78p794 (Ns78p2049 (RS079to096.d4 qz113 qz126 qz281) RS079to096.d42) rfl 

noncomputable abbrev qz809 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz280)

noncomputable def Ns78p2051 := @Enclosure.Real.IsNear.of_eq qz809 (hardyZApproximantRS₀ qz126) Bool.true 42049582948904985227 18446744073709551616 65378615707795649619635 Ns78p694 

noncomputable def Ns78p2052 := @Enclosure.Real.IsNear.neg_val qz809 42049582948904985227 18446744073709551616 65378615707795649619635 Ns78p694 (Ns78p2051 (RS079to096.d34 qz113 qz126 qz281) RS079to096.d43) rfl 

noncomputable def Ns78p2053 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz808 qz4 qz113 287396 1000 298842 1000 

noncomputable def Ns78p2054 := @Enclosure.norm_gt_of_isNear qz808 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 489445846483293468957 147573952589676412928 28935310280385915097593 

noncomputable def Ns78p2055 := @Ns78p2054 Ns78p794 169724753 1342177280 1213 1342177280 (Ns78p2049 (RS079to096.d4 qz113 qz126 qz281) RS079to096.d42) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2056 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz809 qz4 qz126 287396 1000 300468 1000 

noncomputable def Ns78p2057 := @Enclosure.norm_gt_of_isNear qz809 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 42049582948904985227 18446744073709551616 65378615707795649619635 

noncomputable def Ns78p2058 := @Ns78p2057 Ns78p694 169724753 1342177280 1213 1342177280 (Ns78p2051 (RS079to096.d34 qz113 qz126 qz281) RS079to096.d43) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2059 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz280 (@BSN.thirtyTwoPi_le_dec qz113 298842 1000 qz116 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz808 qz809 (Ns78p2050 rfl rfl) (Ns78p2052 rfl rfl)) (Ns78p2053 qz11 qz116 rfl rfl rfl rfl (Ns78p2055 rfl)) (Ns78p2056 qz11 qz129 rfl rfl rfl rfl (Ns78p2058 rfl)) 

noncomputable abbrev qz608 := (@Enclosure.dec_le_dec qz693 qz702 300468 1000 302092 1000 qz697 qz706 rfl rfl rfl)

noncomputable abbrev qz282 := (RS079to096.d3 qz465 qz477 qz608)

noncomputable abbrev qz810 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz282)

noncomputable def Ns78p2060 := @Enclosure.Real.IsNear.of_eq qz810 (hardyZApproximantRS₀ qz126) Bool.true 42049582948904985227 18446744073709551616 65378615707795649619635 Ns78p694 

noncomputable abbrev qz283 := qz608

noncomputable def Ns78p2061 := @Enclosure.Real.IsNear.neg_val qz810 42049582948904985227 18446744073709551616 65378615707795649619635 Ns78p694 (Ns78p2060 (RS079to096.d4 qz126 qz139 qz283) RS079to096.d43) rfl 

noncomputable abbrev qz811 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz282)

noncomputable def Ns78p2062 := @Enclosure.Real.IsNear.of_eq qz811 (hardyZApproximantRS₀ qz139) Bool.false 29263275716852497 36028797018963968 262686494916515945556389 Ns78p603 

noncomputable def Ns78p2063 := @Enclosure.Real.IsNear.pos_val qz811 29263275716852497 36028797018963968 262686494916515945556389 Ns78p603 (Ns78p2062 (RS079to096.d34 qz126 qz139 qz283) RS079to096.d44) rfl 

noncomputable def Ns78p2064 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz810 qz4 qz126 287396 1000 300468 1000 

noncomputable def Ns78p2065 := @Enclosure.norm_gt_of_isNear qz810 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 42049582948904985227 18446744073709551616 65378615707795649619635 

noncomputable def Ns78p2066 := @Ns78p2065 Ns78p694 169724753 1342177280 1213 1342177280 (Ns78p2060 (RS079to096.d4 qz126 qz139 qz283) RS079to096.d43) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2067 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz811 qz4 qz139 287396 1000 302092 1000 

noncomputable def Ns78p2068 := @Enclosure.norm_gt_of_isNear qz811 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 29263275716852497 36028797018963968 262686494916515945556389 

noncomputable def Ns78p2069 := @Ns78p2068 Ns78p603 169724753 1342177280 1213 1342177280 (Ns78p2062 (RS079to096.d34 qz126 qz139 qz283) RS079to096.d44) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2070 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz282 (@BSN.thirtyTwoPi_le_dec qz126 300468 1000 qz129 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz810 qz811 (Ns78p2061 rfl rfl) (Ns78p2063 rfl rfl)) (Ns78p2064 qz11 qz129 rfl rfl rfl rfl (Ns78p2066 rfl)) (Ns78p2067 qz11 qz142 rfl rfl rfl rfl (Ns78p2069 rfl)) 

noncomputable abbrev qz812 := (@Enclosure.dec_le_dec qz879 qz883 302092 1000 303713 1000 (@Eq.refl Real qz879) qz886 rfl rfl rfl)

noncomputable abbrev qz609 := qz812

noncomputable abbrev qz284 := (RS079to096.d3 qz477 qz489 qz609)

noncomputable abbrev qz813 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz284)

noncomputable def Ns78p2071 := @Enclosure.Real.IsNear.of_eq qz813 (hardyZApproximantRS₀ qz139) Bool.false 29263275716852497 36028797018963968 262686494916515945556389 Ns78p603 

noncomputable abbrev qz285 := qz609

noncomputable def Ns78p2072 := @Enclosure.Real.IsNear.pos_val qz813 29263275716852497 36028797018963968 262686494916515945556389 Ns78p603 (Ns78p2071 (RS079to096.d4 qz139 qz152 qz285) RS079to096.d44) rfl 

noncomputable abbrev qz814 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz284)

noncomputable def Ns78p2073 := @Enclosure.Real.IsNear.of_eq qz814 (hardyZApproximantRS₀ qz152) Bool.true 179535632830138606199 73786976294838206464 65991542380937117929343 Ns78p694 

noncomputable def Ns78p2074 := @Enclosure.Real.IsNear.neg_val qz814 179535632830138606199 73786976294838206464 65991542380937117929343 Ns78p694 (Ns78p2073 (RS079to096.d34 qz139 qz152 qz285) RS079to096.d45) rfl 

noncomputable def Ns78p2075 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz813 qz4 qz139 287396 1000 302092 1000 

noncomputable def Ns78p2076 := @Enclosure.norm_gt_of_isNear qz813 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 29263275716852497 36028797018963968 262686494916515945556389 

noncomputable def Ns78p2077 := @Ns78p2076 Ns78p603 169724753 1342177280 1213 1342177280 (Ns78p2071 (RS079to096.d4 qz139 qz152 qz285) RS079to096.d44) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2078 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz814 qz4 qz152 287396 1000 303713 1000 

noncomputable def Ns78p2079 := @Enclosure.norm_gt_of_isNear qz814 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 179535632830138606199 73786976294838206464 65991542380937117929343 

noncomputable def Ns78p2080 := @Ns78p2079 Ns78p694 169724753 1342177280 1213 1342177280 (Ns78p2073 (RS079to096.d34 qz139 qz152 qz285) RS079to096.d45) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2081 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz139 302092 1000 qz142 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz813 qz814 (Ns78p2072 rfl rfl) (Ns78p2074 rfl rfl)) (Ns78p2075 qz11 qz142 rfl rfl rfl rfl (Ns78p2077 rfl)) (Ns78p2078 qz11 qz155 rfl rfl rfl rfl (Ns78p2080 rfl)) 

noncomputable abbrev qz923 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 303713 1000) (Enclosure.sfrac Bool.false 305332 1000) 303713 1000 305332 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 303713 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 305332 1000)) rfl rfl rfl)

noncomputable abbrev qz815 := qz923

noncomputable abbrev qz610 := qz815

noncomputable abbrev qz286 := (RS079to096.d3 qz489 qz501 qz610)

noncomputable abbrev qz816 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz286)

noncomputable def Ns78p2082 := @Enclosure.Real.IsNear.of_eq qz816 (hardyZApproximantRS₀ qz152) Bool.true 179535632830138606199 73786976294838206464 65991542380937117929343 Ns78p694 

noncomputable abbrev qz287 := qz610

noncomputable def Ns78p2083 := @Enclosure.Real.IsNear.neg_val qz816 179535632830138606199 73786976294838206464 65991542380937117929343 Ns78p694 (Ns78p2082 (RS079to096.d4 qz152 qz165 qz287) RS079to096.d45) rfl 

noncomputable abbrev qz817 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz286)

noncomputable def Ns78p2084 := @Enclosure.Real.IsNear.of_eq qz817 (hardyZApproximantRS₀ qz165) Bool.false 18828719724302971019 36893488147419103232 132658520829759371754301 Ns78p1188 

noncomputable def Ns78p2085 := @Enclosure.Real.IsNear.pos_val qz817 18828719724302971019 36893488147419103232 132658520829759371754301 Ns78p1188 (Ns78p2084 (RS079to096.d34 qz152 qz165 qz287) RS079to096.d46) rfl 

noncomputable def Ns78p2086 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz816 qz4 qz152 287396 1000 303713 1000 

noncomputable def Ns78p2087 := @Enclosure.norm_gt_of_isNear qz816 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 179535632830138606199 73786976294838206464 65991542380937117929343 

noncomputable def Ns78p2088 := @Ns78p2087 Ns78p694 169724753 1342177280 1213 1342177280 (Ns78p2082 (RS079to096.d4 qz152 qz165 qz287) RS079to096.d45) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2089 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz817 qz4 qz165 287396 1000 305332 1000 

noncomputable def Ns78p2090 := @Enclosure.norm_gt_of_isNear qz817 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 18828719724302971019 36893488147419103232 132658520829759371754301 

noncomputable def Ns78p2091 := @Ns78p2090 Ns78p1188 169724753 1342177280 1213 1342177280 (Ns78p2084 (RS079to096.d34 qz152 qz165 qz287) RS079to096.d46) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2092 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz286 (@BSN.thirtyTwoPi_le_dec qz152 303713 1000 qz155 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz816 qz817 (Ns78p2083 rfl rfl) (Ns78p2085 rfl rfl)) (Ns78p2086 qz11 qz155 rfl rfl rfl rfl (Ns78p2088 rfl)) (Ns78p2089 qz11 qz168 rfl rfl rfl rfl (Ns78p2091 rfl)) 

noncomputable abbrev qz288 := (RS079to096.d3 qz501 qz513 (@Enclosure.dec_le_dec qz501 qz513 305332 1000 306949 1000 qz504 qz516 rfl rfl rfl))

noncomputable abbrev qz818 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz288)

noncomputable def Ns78p2093 := @Enclosure.Real.IsNear.of_eq qz818 (hardyZApproximantRS₀ qz165) Bool.false 18828719724302971019 36893488147419103232 132658520829759371754301 Ns78p1188 

noncomputable abbrev qz289 := (@Enclosure.dec_le_dec qz501 qz513 305332 1000 306949 1000 qz504 qz516 rfl rfl rfl)

noncomputable def Ns78p2094 := @Enclosure.Real.IsNear.pos_val qz818 18828719724302971019 36893488147419103232 132658520829759371754301 Ns78p1188 (Ns78p2093 (RS079to096.d4 qz165 qz178 qz289) RS079to096.d46) rfl 

noncomputable abbrev qz819 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz288)

noncomputable def Ns78p2095 := @Enclosure.Real.IsNear.of_eq qz819 (hardyZApproximantRS₀ qz178) Bool.true 40541092795099593667 36893488147419103232 3175229093235416535137 Ns78p1287 

noncomputable def Ns78p2096 := @Enclosure.Real.IsNear.neg_val qz819 40541092795099593667 36893488147419103232 3175229093235416535137 Ns78p1287 (Ns78p2095 (RS079to096.d34 qz165 qz178 qz289) RS079to096.d47) rfl 

noncomputable def Ns78p2097 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz818 qz4 qz165 287396 1000 305332 1000 

noncomputable def Ns78p2098 := @Enclosure.norm_gt_of_isNear qz818 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 18828719724302971019 36893488147419103232 132658520829759371754301 

noncomputable def Ns78p2099 := @Ns78p2098 Ns78p1188 169724753 1342177280 1213 1342177280 (Ns78p2093 (RS079to096.d4 qz165 qz178 qz289) RS079to096.d46) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2100 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz819 qz4 qz178 287396 1000 306949 1000 

noncomputable def Ns78p2101 := @Enclosure.norm_gt_of_isNear qz819 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 40541092795099593667 36893488147419103232 3175229093235416535137 

noncomputable def Ns78p2102 := @Ns78p2101 Ns78p1287 169724753 1342177280 1213 1342177280 (Ns78p2095 (RS079to096.d34 qz165 qz178 qz289) RS079to096.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2103 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz165 305332 1000 qz168 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz818 qz819 (Ns78p2094 rfl rfl) (Ns78p2096 rfl rfl)) (Ns78p2097 qz11 qz168 rfl rfl rfl rfl (Ns78p2099 rfl)) (Ns78p2100 qz11 qz181 rfl rfl rfl rfl (Ns78p2102 rfl)) 

noncomputable abbrev qz290 := (RS079to096.d3 qz513 qz529 (@Enclosure.dec_le_dec qz513 qz529 306949 1000 308563 1000 qz516 qz532 rfl rfl rfl))

noncomputable abbrev qz820 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz290)

noncomputable def Ns78p2104 := @Enclosure.Real.IsNear.of_eq qz820 (hardyZApproximantRS₀ qz178) Bool.true 40541092795099593667 36893488147419103232 3175229093235416535137 Ns78p1287 

noncomputable abbrev qz291 := (@Enclosure.dec_le_dec qz513 qz529 306949 1000 308563 1000 qz516 qz532 rfl rfl rfl)

noncomputable def Ns78p2105 := @Enclosure.Real.IsNear.neg_val qz820 40541092795099593667 36893488147419103232 3175229093235416535137 Ns78p1287 (Ns78p2104 (RS079to096.d4 qz178 qz192 qz291) RS079to096.d47) rfl 

noncomputable abbrev qz821 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz290)

noncomputable def Ns78p2106 := @Enclosure.Real.IsNear.of_eq qz821 (hardyZApproximantRS₀ qz192) Bool.false 985214334753048456035 147573952589676412928 14445505225828379058533 Ns78p310 

noncomputable def Ns78p2107 := @Enclosure.Real.IsNear.pos_val qz821 985214334753048456035 147573952589676412928 14445505225828379058533 Ns78p310 (Ns78p2106 (RS079to096.d34 qz178 qz192 qz291) RS079to096.d52) rfl 

noncomputable def Ns78p2108 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz820 qz4 qz178 287396 1000 306949 1000 

noncomputable def Ns78p2109 := @Enclosure.norm_gt_of_isNear qz820 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 40541092795099593667 36893488147419103232 3175229093235416535137 

noncomputable def Ns78p2110 := @Ns78p2109 Ns78p1287 169724753 1342177280 1213 1342177280 (Ns78p2104 (RS079to096.d4 qz178 qz192 qz291) RS079to096.d47) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2111 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz821 qz4 qz192 287396 1000 308563 1000 

noncomputable def Ns78p2112 := @Enclosure.norm_gt_of_isNear qz821 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 985214334753048456035 147573952589676412928 14445505225828379058533 

noncomputable def Ns78p2113 := @Ns78p2112 Ns78p310 169724753 1342177280 1213 1342177280 (Ns78p2106 (RS079to096.d34 qz178 qz192 qz291) RS079to096.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2114 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz290 (@BSN.thirtyTwoPi_le_dec qz178 306949 1000 qz181 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz820 qz821 (Ns78p2105 rfl rfl) (Ns78p2107 rfl rfl)) (Ns78p2108 qz11 qz181 rfl rfl rfl rfl (Ns78p2110 rfl)) (Ns78p2111 qz11 qz196 rfl rfl rfl rfl (Ns78p2113 rfl)) 

noncomputable abbrev qz611 := (@Enclosure.dec_le_dec qz739 qz747 308563 1000 310176 1000 (@Eq.refl Real qz739) (@Eq.refl Real qz747) rfl rfl rfl)

noncomputable abbrev qz292 := (RS079to096.d3 qz529 qz543 qz611)

noncomputable abbrev qz822 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz292)

noncomputable def Ns78p2115 := @Enclosure.Real.IsNear.of_eq qz822 (hardyZApproximantRS₀ qz192) Bool.false 985214334753048456035 147573952589676412928 14445505225828379058533 Ns78p310 

noncomputable abbrev qz293 := qz611

noncomputable def Ns78p2116 := @Enclosure.Real.IsNear.pos_val qz822 985214334753048456035 147573952589676412928 14445505225828379058533 Ns78p310 (Ns78p2115 (RS079to096.d4 qz192 qz206 qz293) RS079to096.d52) rfl 

noncomputable abbrev qz823 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz292)

noncomputable def Ns78p2117 := @Enclosure.Real.IsNear.of_eq qz823 (hardyZApproximantRS₀ qz206) Bool.true 32599617434901818761 147573952589676412928 101664088963357617528359 Ns78p62 

noncomputable def Ns78p2118 := @Enclosure.Real.IsNear.neg_val qz823 32599617434901818761 147573952589676412928 101664088963357617528359 Ns78p62 (Ns78p2117 (RS079to096.d34 qz192 qz206 qz293) RS079to096.d53) rfl 

noncomputable def Ns78p2119 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz822 qz4 qz192 287396 1000 308563 1000 

noncomputable def Ns78p2120 := @Enclosure.norm_gt_of_isNear qz822 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 985214334753048456035 147573952589676412928 14445505225828379058533 

noncomputable def Ns78p2121 := @Ns78p2120 Ns78p310 169724753 1342177280 1213 1342177280 (Ns78p2115 (RS079to096.d4 qz192 qz206 qz293) RS079to096.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2122 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz823 qz4 qz206 287396 1000 310176 1000 

noncomputable def Ns78p2123 := @Enclosure.norm_gt_of_isNear qz823 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 32599617434901818761 147573952589676412928 101664088963357617528359 

noncomputable def Ns78p2124 := @Ns78p2123 Ns78p62 169724753 1342177280 1213 1342177280 (Ns78p2117 (RS079to096.d34 qz192 qz206 qz293) RS079to096.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2125 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz192 308563 1000 qz196 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz822 qz823 (Ns78p2116 rfl rfl) (Ns78p2118 rfl rfl)) (Ns78p2119 qz11 qz196 rfl rfl rfl rfl (Ns78p2121 rfl)) (Ns78p2122 qz11 qz209 rfl rfl rfl rfl (Ns78p2124 rfl)) 

noncomputable abbrev qz612 := (@Enclosure.dec_le_dec qz747 qz755 310176 1000 311786 1000 (@Eq.refl Real qz747) qz759 rfl rfl rfl)

noncomputable abbrev qz294 := (RS079to096.d3 qz543 qz555 qz612)

noncomputable abbrev qz824 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz294)

noncomputable def Ns78p2126 := @Enclosure.Real.IsNear.of_eq qz824 (hardyZApproximantRS₀ qz206) Bool.true 32599617434901818761 147573952589676412928 101664088963357617528359 Ns78p62 

noncomputable abbrev qz295 := qz612

noncomputable def Ns78p2127 := @Enclosure.Real.IsNear.neg_val qz824 32599617434901818761 147573952589676412928 101664088963357617528359 Ns78p62 (Ns78p2126 (RS079to096.d4 qz206 qz219 qz295) RS079to096.d53) rfl 

noncomputable abbrev qz825 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz294)

noncomputable def Ns78p2128 := @Enclosure.Real.IsNear.of_eq qz825 (hardyZApproximantRS₀ qz219) Bool.false 2014439825793107357 2305843009213693952 153278462271582327845509 Ns78p1188 

noncomputable def Ns78p2129 := @Enclosure.Real.IsNear.pos_val qz825 2014439825793107357 2305843009213693952 153278462271582327845509 Ns78p1188 (Ns78p2128 (RS079to096.d34 qz206 qz219 qz295) RS079to096.d54) rfl 

noncomputable def Ns78p2130 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz824 qz4 qz206 287396 1000 310176 1000 

noncomputable def Ns78p2131 := @Enclosure.norm_gt_of_isNear qz824 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 32599617434901818761 147573952589676412928 101664088963357617528359 

noncomputable def Ns78p2132 := @Ns78p2131 Ns78p62 169724753 1342177280 1213 1342177280 (Ns78p2126 (RS079to096.d4 qz206 qz219 qz295) RS079to096.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2133 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz825 qz4 qz219 287396 1000 311786 1000 

noncomputable def Ns78p2134 := @Enclosure.norm_gt_of_isNear qz825 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2014439825793107357 2305843009213693952 153278462271582327845509 

noncomputable def Ns78p2135 := @Ns78p2134 Ns78p1188 169724753 1342177280 1213 1342177280 (Ns78p2128 (RS079to096.d34 qz206 qz219 qz295) RS079to096.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2136 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz294 (@BSN.thirtyTwoPi_le_dec qz206 310176 1000 qz209 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz824 qz825 (Ns78p2127 rfl rfl) (Ns78p2129 rfl rfl)) (Ns78p2130 qz11 qz209 rfl rfl rfl rfl (Ns78p2132 rfl)) (Ns78p2133 qz11 qz222 rfl rfl rfl rfl (Ns78p2135 rfl)) 

noncomputable abbrev qz613 := (@Enclosure.dec_le_dec qz755 qz765 311786 1000 313394 1000 qz759 qz769 rfl rfl rfl)

noncomputable abbrev qz296 := (RS079to096.d3 qz555 qz568 qz613)

noncomputable abbrev qz826 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz296)

noncomputable def Ns78p2137 := @Enclosure.Real.IsNear.of_eq qz826 (hardyZApproximantRS₀ qz219) Bool.false 2014439825793107357 2305843009213693952 153278462271582327845509 Ns78p1188 

noncomputable abbrev qz297 := qz613

noncomputable def Ns78p2138 := @Enclosure.Real.IsNear.pos_val qz826 2014439825793107357 2305843009213693952 153278462271582327845509 Ns78p1188 (Ns78p2137 (RS079to096.d4 qz219 qz231 qz297) RS079to096.d54) rfl 

noncomputable abbrev qz827 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz296)

noncomputable def Ns78p2139 := @Enclosure.Real.IsNear.of_eq qz827 (hardyZApproximantRS₀ qz231) Bool.true 12749899263849220527 9223372036854775808 154101093488866441910821 Ns78p1188 

noncomputable def Ns78p2140 := @Enclosure.Real.IsNear.neg_val qz827 12749899263849220527 9223372036854775808 154101093488866441910821 Ns78p1188 (Ns78p2139 (RS079to096.d34 qz219 qz231 qz297) RS079to096.d55) rfl 

noncomputable def Ns78p2141 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz826 qz4 qz219 287396 1000 311786 1000 

noncomputable def Ns78p2142 := @Enclosure.norm_gt_of_isNear qz826 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2014439825793107357 2305843009213693952 153278462271582327845509 

noncomputable def Ns78p2143 := @Ns78p2142 Ns78p1188 169724753 1342177280 1213 1342177280 (Ns78p2137 (RS079to096.d4 qz219 qz231 qz297) RS079to096.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2144 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz827 qz4 qz231 287396 1000 313394 1000 

noncomputable def Ns78p2145 := @Enclosure.norm_gt_of_isNear qz827 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 12749899263849220527 9223372036854775808 154101093488866441910821 

noncomputable def Ns78p2146 := @Ns78p2145 Ns78p1188 169724753 1342177280 1213 1342177280 (Ns78p2139 (RS079to096.d34 qz219 qz231 qz297) RS079to096.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2147 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz296 (@BSN.thirtyTwoPi_le_dec qz219 311786 1000 qz222 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz826 qz827 (Ns78p2138 rfl rfl) (Ns78p2140 rfl rfl)) (Ns78p2141 qz11 qz222 rfl rfl rfl rfl (Ns78p2143 rfl)) (Ns78p2144 qz11 qz234 rfl rfl rfl rfl (Ns78p2146 rfl)) 

noncomputable abbrev qz828 := (@Enclosure.dec_le_dec qz910 qz914 313394 1000 315000 1000 (@Eq.refl Real qz910) qz917 rfl rfl rfl)

noncomputable abbrev qz614 := qz828

noncomputable abbrev qz298 := (RS079to096.d3 qz568 qz581 qz614)

noncomputable abbrev qz829 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz298)

noncomputable def Ns78p2148 := @Enclosure.Real.IsNear.of_eq qz829 (hardyZApproximantRS₀ qz231) Bool.true 12749899263849220527 9223372036854775808 154101093488866441910821 Ns78p1188 

noncomputable abbrev qz299 := qz614

noncomputable def Ns78p2149 := @Enclosure.Real.IsNear.neg_val qz829 12749899263849220527 9223372036854775808 154101093488866441910821 Ns78p1188 (Ns78p2148 (RS079to096.d4 qz231 qz243 qz299) RS079to096.d55) rfl 

noncomputable abbrev qz830 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz298)

noncomputable def Ns78p2150 := @Enclosure.Real.IsNear.of_eq qz830 (hardyZApproximantRS₀ qz243) Bool.false 120506069167500549577 73786976294838206464 154939870678065578127205 Ns78p1188 

noncomputable def Ns78p2151 := @Enclosure.Real.IsNear.pos_val qz830 120506069167500549577 73786976294838206464 154939870678065578127205 Ns78p1188 (Ns78p2150 (RS079to096.d34 qz231 qz243 qz299) RS079to096.d56) rfl 

noncomputable def Ns78p2152 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz829 qz4 qz231 287396 1000 313394 1000 

noncomputable def Ns78p2153 := @Enclosure.norm_gt_of_isNear qz829 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 12749899263849220527 9223372036854775808 154101093488866441910821 

noncomputable def Ns78p2154 := @Ns78p2153 Ns78p1188 169724753 1342177280 1213 1342177280 (Ns78p2148 (RS079to096.d4 qz231 qz243 qz299) RS079to096.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2155 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz830 qz4 qz243 287396 1000 315000 1000 

noncomputable def Ns78p2156 := @Enclosure.norm_gt_of_isNear qz830 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 120506069167500549577 73786976294838206464 154939870678065578127205 

noncomputable def Ns78p2157 := @Ns78p2156 Ns78p1188 169724753 1342177280 1213 1342177280 (Ns78p2150 (RS079to096.d34 qz231 qz243 qz299) RS079to096.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2158 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz298 (@BSN.thirtyTwoPi_le_dec qz231 313394 1000 qz234 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz829 qz830 (Ns78p2149 rfl rfl) (Ns78p2151 rfl rfl)) (Ns78p2152 qz11 qz234 rfl rfl rfl rfl (Ns78p2154 rfl)) (Ns78p2155 qz11 qz246 rfl rfl rfl rfl (Ns78p2157 rfl)) 

noncomputable abbrev qz924 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 315000 1000) (Enclosure.sfrac Bool.false 316604 1000) 315000 1000 316604 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 315000 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 316604 1000)) rfl rfl rfl)

noncomputable abbrev qz831 := qz924

noncomputable abbrev qz615 := qz831

noncomputable abbrev qz300 := (RS079to096.d3 qz581 qz594 qz615)

noncomputable abbrev qz832 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz300)

noncomputable def Ns78p2159 := @Enclosure.Real.IsNear.of_eq qz832 (hardyZApproximantRS₀ qz243) Bool.false 120506069167500549577 73786976294838206464 154939870678065578127205 Ns78p1188 

noncomputable abbrev qz301 := qz615

noncomputable def Ns78p2160 := @Enclosure.Real.IsNear.pos_val qz832 120506069167500549577 73786976294838206464 154939870678065578127205 Ns78p1188 (Ns78p2159 (RS079to096.d4 qz243 qz255 qz301) RS079to096.d56) rfl 

noncomputable abbrev qz833 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz300)

noncomputable def Ns78p2161 := @Enclosure.Real.IsNear.of_eq qz833 (hardyZApproximantRS₀ qz255) Bool.true 38269456319305304309 9223372036854775808 5564360654681685866593 Ns78p1869 

noncomputable def Ns78p2162 := @Enclosure.Real.IsNear.neg_val qz833 38269456319305304309 9223372036854775808 5564360654681685866593 Ns78p1869 (Ns78p2161 (RS079to096.d34 qz243 qz255 qz301) RS079to096.d57) rfl 

noncomputable def Ns78p2163 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz832 qz4 qz243 287396 1000 315000 1000 

noncomputable def Ns78p2164 := @Enclosure.norm_gt_of_isNear qz832 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 120506069167500549577 73786976294838206464 154939870678065578127205 

noncomputable def Ns78p2165 := @Ns78p2164 Ns78p1188 169724753 1342177280 1213 1342177280 (Ns78p2159 (RS079to096.d4 qz243 qz255 qz301) RS079to096.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2166 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz833 qz4 qz255 287396 1000 316604 1000 

noncomputable def Ns78p2167 := @Enclosure.norm_gt_of_isNear qz833 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 38269456319305304309 9223372036854775808 5564360654681685866593 

noncomputable def Ns78p2168 := @Ns78p2167 Ns78p1869 169724753 1342177280 1213 1342177280 (Ns78p2161 (RS079to096.d34 qz243 qz255 qz301) RS079to096.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 169724753 1342177280 1213 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS079to096.d36) rfl rfl rfl rfl 

noncomputable def Ns78p2169 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz243 315000 1000 qz246 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz832 qz833 (Ns78p2160 rfl rfl) (Ns78p2162 rfl rfl)) (Ns78p2163 qz11 qz246 rfl rfl rfl rfl (Ns78p2165 rfl)) (Ns78p2166 qz11 (@Eq.refl Real qz255) rfl rfl rfl rfl (Ns78p2168 rfl)) 

noncomputable def Ns78p2170 := @List.cons RS079to096.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz298 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz298) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz298) Ns78p2158)) (@List.cons RS079to096.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns78p2169)) (@List.nil RS079to096.d0)) 

noncomputable def Ns78p2171 := @List.cons RS079to096.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz294 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz294) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz294) Ns78p2136)) (@List.cons RS079to096.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns78p2147)) Ns78p2170) 

noncomputable def Ns78p2172 := @List.cons RS079to096.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz290 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz290) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz290) Ns78p2114)) (@List.cons RS079to096.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns78p2125)) Ns78p2171) 

noncomputable def Ns78p2173 := @List.cons RS079to096.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz286 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz286) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz286) Ns78p2092)) (@List.cons RS079to096.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns78p2103)) Ns78p2172) 

noncomputable def Ns78p2174 := @List.cons RS079to096.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz282 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz282) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz282) Ns78p2070)) (@List.cons RS079to096.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns78p2081)) Ns78p2173) 

noncomputable def Ns78p2175 := @List.cons RS079to096.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz278 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz278) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz278) Ns78p2048)) (@List.cons RS079to096.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz280 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz280) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz280) Ns78p2059)) Ns78p2174) 

noncomputable def Ns78p2176 := @List.cons RS079to096.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz274 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz274) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz274) Ns78p2026)) (@List.cons RS079to096.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz276 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz276) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz276) Ns78p2037)) Ns78p2175) 

noncomputable def Ns78p2177 := @List.cons RS079to096.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz270 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz270) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz270) Ns78p2004)) (@List.cons RS079to096.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz272 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz272) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz272) Ns78p2015)) Ns78p2176) 

noncomputable def Ns78p2178 := @List.cons RS079to096.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz266 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz266) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz266) Ns78p1982)) (@List.cons RS079to096.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz268 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz268) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz268) Ns78p1993)) Ns78p2177) 

noncomputable abbrev qz834 := (RS079to096.d2 qz910 qz914 (@Enclosure.dec_le_dec qz910 qz914 313394 1000 315000 1000 (@Eq.refl Real qz910) qz917 rfl rfl rfl))

noncomputable abbrev qz835 := (@List.cons RS079to096.d1 (RS079to096.d2 qz914 qz919 qz924) (@List.nil RS079to096.d1))

noncomputable abbrev qz616 := (@List.cons RS079to096.d1 (RS079to096.d2 qz755 qz765 (@Enclosure.dec_le_dec qz755 qz765 311786 1000 313394 1000 qz759 qz769 rfl rfl rfl)) (@List.cons RS079to096.d1 qz834 qz835))

noncomputable abbrev qz302 := (@List.cons RS079to096.d1 (RS079to096.d2 qz529 qz543 qz611) (@List.cons RS079to096.d1 (RS079to096.d2 qz543 qz555 qz612) qz616))

noncomputable def Ns78p2179 := @List.cons RS079to096.d1 (RS079to096.d2 qz165 qz178 qz289) (@List.cons RS079to096.d1 (RS079to096.d2 qz178 qz192 qz291) qz302) 

noncomputable abbrev qz836 := (RS079to096.d2 qz879 qz883 (@Enclosure.dec_le_dec qz879 qz883 302092 1000 303713 1000 (@Eq.refl Real qz879) qz886 rfl rfl rfl))

noncomputable abbrev qz837 := (@List.cons RS079to096.d1 (RS079to096.d2 qz883 qz888 qz923) Ns78p2179)

noncomputable abbrev qz617 := (@List.cons RS079to096.d1 (RS079to096.d2 qz693 qz702 (@Enclosure.dec_le_dec qz693 qz702 300468 1000 302092 1000 qz697 qz706 rfl rfl rfl)) (@List.cons RS079to096.d1 qz836 qz837))

noncomputable abbrev qz303 := (@List.cons RS079to096.d1 (RS079to096.d2 qz440 qz453 qz606) (@List.cons RS079to096.d1 (RS079to096.d2 qz453 qz465 qz607) qz617))

noncomputable def Ns78p2180 := @List.cons RS079to096.d1 (RS079to096.d2 qz74 qz87 qz275) (@List.cons RS079to096.d1 (RS079to096.d2 qz87 qz100 qz277) qz303) 

noncomputable def Ns78p2181 := @List.IsChain.cons_cons RS079to096.d1 RS079to096.d58 (RS079to096.d2 qz61 qz74 qz273) (RS079to096.d2 qz74 qz87 qz275) (@List.cons RS079to096.d1 (RS079to096.d2 qz87 qz100 qz277) qz303) 

noncomputable def Ns78p2182 := @List.IsChain.cons_cons RS079to096.d1 RS079to096.d58 (RS079to096.d2 qz74 qz87 qz275) (RS079to096.d2 qz87 qz100 qz277) qz303 (@Enclosure.dec_le_dec qz87 qz87 295176 1000 295176 1000 qz90 qz90 rfl rfl rfl) 

noncomputable abbrev qz838 := (RS079to096.d2 qz883 qz888 qz923)

noncomputable abbrev qz618 := qz838

noncomputable abbrev qz304 := qz618

noncomputable def Ns78p2183 := @List.IsChain.cons_cons RS079to096.d1 RS079to096.d58 qz304 (RS079to096.d2 qz165 qz178 qz289) (@List.cons RS079to096.d1 (RS079to096.d2 qz178 qz192 qz291) qz302) 

noncomputable def Ns78p2184 := @List.IsChain.cons_cons RS079to096.d1 RS079to096.d58 (RS079to096.d2 qz165 qz178 qz289) (RS079to096.d2 qz178 qz192 qz291) qz302 (@Enclosure.dec_le_dec qz178 qz178 306949 1000 306949 1000 qz181 qz181 rfl rfl rfl) 

noncomputable abbrev qz305 := qz616

noncomputable abbrev qz619 := (@List.cons RS079to096.d1 qz834 qz835)

noncomputable abbrev qz306 := qz619

noncomputable abbrev qz620 := qz834

noncomputable abbrev qz307 := qz620

noncomputable abbrev qz621 := qz835

noncomputable abbrev qz308 := qz621

noncomputable abbrev qz839 := (RS079to096.d2 qz914 qz919 qz924)

noncomputable abbrev qz622 := qz839

noncomputable abbrev qz309 := qz622

noncomputable def Ns78p2185 := @List.IsChain.cons_cons RS079to096.d1 RS079to096.d58 (RS079to096.d2 qz192 qz206 qz293) (RS079to096.d2 qz206 qz219 qz295) qz305 (@Enclosure.dec_le_dec qz206 qz206 310176 1000 310176 1000 qz209 qz209 rfl rfl rfl) (@List.IsChain.cons_cons RS079to096.d1 RS079to096.d58 (RS079to096.d2 qz206 qz219 qz295) (RS079to096.d2 qz219 qz231 qz297) qz306 (@Enclosure.dec_le_dec qz219 qz219 311786 1000 311786 1000 qz222 qz222 rfl rfl rfl) (@List.IsChain.cons_cons RS079to096.d1 RS079to096.d58 (RS079to096.d2 qz219 qz231 qz297) qz307 qz308 (@Enclosure.dec_le_dec qz231 qz231 313394 1000 313394 1000 qz234 qz234 rfl rfl rfl) (@List.IsChain.cons_cons RS079to096.d1 RS079to096.d58 qz307 qz309 (@List.nil RS079to096.d1) (@Enclosure.dec_le_dec qz243 qz243 315000 1000 315000 1000 qz246 qz246 rfl rfl rfl) (@List.IsChain.singleton RS079to096.d1 RS079to096.d58 qz309)))) 

noncomputable abbrev qz310 := (@List.cons RS079to096.d1 (RS079to096.d2 qz543 qz555 qz612) qz616)

noncomputable def Ns78p2186 := @List.IsChain.cons_cons RS079to096.d1 RS079to096.d58 (RS079to096.d2 qz178 qz192 qz291) (RS079to096.d2 qz192 qz206 qz293) qz310 (@Enclosure.dec_le_dec qz192 qz192 308563 1000 308563 1000 qz196 qz196 rfl rfl rfl) Ns78p2185 

noncomputable abbrev qz311 := qz617

noncomputable abbrev qz623 := (@List.cons RS079to096.d1 qz836 qz837)

noncomputable abbrev qz312 := qz623

noncomputable abbrev qz624 := qz836

noncomputable abbrev qz313 := qz624

noncomputable abbrev qz625 := qz837

noncomputable abbrev qz314 := qz625

noncomputable def Ns78p2187 := @List.IsChain.cons_cons RS079to096.d1 RS079to096.d58 (RS079to096.d2 qz100 qz113 qz279) (RS079to096.d2 qz113 qz126 qz281) qz311 (@Enclosure.dec_le_dec qz113 qz113 298842 1000 298842 1000 qz116 qz116 rfl rfl rfl) (@List.IsChain.cons_cons RS079to096.d1 RS079to096.d58 (RS079to096.d2 qz113 qz126 qz281) (RS079to096.d2 qz126 qz139 qz283) qz312 (@Enclosure.dec_le_dec qz126 qz126 300468 1000 300468 1000 qz129 qz129 rfl rfl rfl) (@List.IsChain.cons_cons RS079to096.d1 RS079to096.d58 (RS079to096.d2 qz126 qz139 qz283) qz313 qz314 (@Enclosure.dec_le_dec qz139 qz139 302092 1000 302092 1000 qz142 qz142 rfl rfl rfl) (@List.IsChain.cons_cons RS079to096.d1 RS079to096.d58 qz313 qz304 Ns78p2179 (@Enclosure.dec_le_dec qz152 qz152 303713 1000 303713 1000 qz155 qz155 rfl rfl rfl) (Ns78p2183 (@Enclosure.dec_le_dec qz165 qz165 305332 1000 305332 1000 qz168 qz168 rfl rfl rfl) (Ns78p2184 Ns78p2186))))) 

noncomputable abbrev qz315 := (@List.cons RS079to096.d1 (RS079to096.d2 qz453 qz465 qz607) qz617)

noncomputable def Ns78p2188 := @List.IsChain.cons_cons RS079to096.d1 RS079to096.d58 (RS079to096.d2 qz87 qz100 qz277) (RS079to096.d2 qz100 qz113 qz279) qz315 (@Enclosure.dec_le_dec qz100 qz100 296399 1000 296399 1000 qz103 qz103 rfl rfl rfl) Ns78p2187 

noncomputable def Ns78p2189 := Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns78p2178 (@List.IsChain.cons_cons RS079to096.d1 RS079to096.d58 (RS079to096.d2 qz4 qz29 qz267) (RS079to096.d2 qz29 qz48 qz269) (@List.cons RS079to096.d1 (RS079to096.d2 qz48 qz61 qz271) (@List.cons RS079to096.d1 (RS079to096.d2 qz61 qz74 qz273) Ns78p2180)) (@Enclosure.dec_le_dec qz29 qz29 289039 1000 289039 1000 qz32 qz32 rfl rfl rfl) (@List.IsChain.cons_cons RS079to096.d1 RS079to096.d58 (RS079to096.d2 qz29 qz48 qz269) (RS079to096.d2 qz48 qz61 qz271) (@List.cons RS079to096.d1 (RS079to096.d2 qz61 qz74 qz273) Ns78p2180) (@Enclosure.dec_le_dec qz48 qz48 290679 1000 290679 1000 qz51 qz51 rfl rfl rfl) (@List.IsChain.cons_cons RS079to096.d1 RS079to096.d58 (RS079to096.d2 qz48 qz61 qz271) (RS079to096.d2 qz61 qz74 qz273) Ns78p2180 (@Enclosure.dec_le_dec qz61 qz61 292316 1000 292316 1000 qz64 qz64 rfl rfl rfl) (Ns78p2181 (@Enclosure.dec_le_dec qz74 qz74 294360 1000 294360 1000 qz77 qz77 rfl rfl rfl) (Ns78p2182 Ns78p2188))))) 

noncomputable abbrev qz626 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz627 := (Zeta.Certificates.CertifiedZeroIntervals.intervals Ns78p2189)

theorem RS079to096.d59 : Zeta.Certificates.BatchSpec 18 287396 1000 316604 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz626 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 18) (And (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz626 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz626 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz255)))) Ns78p2189 (@And.intro (@Eq Nat (@List.length qz626 qz627) 18) (And (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz626 qz627)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz626 qz627)) (@Option.some Real qz255))) (@Eq.refl Nat 18) (@And.intro (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz626 qz627)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz626 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz626 qz627)) (@Option.some Real qz255)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz255))))

theorem solution : Zeta.Certificates.BatchSpec 18 287396 1000 316604 1000 := RS079to096.d59
#print axioms solution
#check solution
