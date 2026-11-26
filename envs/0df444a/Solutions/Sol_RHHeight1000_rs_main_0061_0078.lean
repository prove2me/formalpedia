-- Prove2me | solution 1 for RHHeight1000.rs_main_0061_0078
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T21:47:22.396116+00:00
-- url     : https://prove2.me/submissions/4ed63f51-4e3f-4e92-b08d-e4165527c387

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

noncomputable abbrev RSCompact.c2 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) Real.pi Real.pi) 

noncomputable abbrev RSCompact.c3 := (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup) (@RCLike.toInnerProductSpaceReal Real Real.instRCLike)) 

noncomputable abbrev RSCompact.c4 := (@DenselyNormedField.toNontriviallyNormedField Real Real.denselyNormedField) 

noncomputable abbrev RSCompact.c5 := (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup) (@RCLike.toInnerProductSpaceReal Real Real.instRCLike)) 

noncomputable abbrev RSCompact.c6 := (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup) (@RCLike.toInnerProductSpaceReal Real Real.instRCLike)) 

noncomputable abbrev RSCompact.c7 := (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup) (@RCLike.toInnerProductSpaceReal Real Real.instRCLike)) 

noncomputable abbrev RSCompact.c8 := (@InnerProductSpace.toNormedSpace Real Real Real.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup Real Real.normedAddCommGroup) (@RCLike.toInnerProductSpaceReal Real Real.instRCLike)) 

noncomputable abbrev RSCompact.c9 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) RSCompact.c2 Real.pi) 

noncomputable abbrev RSCompact.c10 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) RSCompact.c2 Real.pi) 

noncomputable abbrev RSCompact.c11 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) RSCompact.c2 Real.pi) 

noncomputable def RS061to078.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS061to078.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS061to078.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS061to078.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS061to078.d2 a b h 

theorem RS061to078.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS061to078.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS061to078.d3 a b h)) 

noncomputable def Ns60p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns60p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns60p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns60p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns60p0 Ns60p1 Ns60p2 Ns60p1 76821522 67108864 1 17475728 76821522 67108864 1 17475728 38410761 33554432 2 33554432 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns60p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns60p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns60p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns60p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns60p8 := nat_lit 4564579050430662680769181008104061220617401457132102377181523838895616693352443067851710738206186456870068891932464934433532008760270543541307416978974983178670584632435273151991067990877911260800542253584783113678675870571765297427794279500566373840368605043192397583789219721854001914445657820861544585749419999617014263230075963405112904900127091763553068379337562290951837345169106631254289648555755847509739637528572205479767112592191328488981867735095152085893116377698979776390335134938272744697179058821035388170748994050345731998297589980525805272027148669105172128531226596705145339433394591280230580530674088894892093599627198529211479716891686479023042798211193766875 

noncomputable def Ns60p9 := nat_lit 487897090127139370915718269131278067469793404735814825511781216300711748025172292443098109798278438646340651351778930478625246708087138935333656000353278407183834741097045313633566773106147391845370902603761794798142555380136213880615811008223525988937457841388015247818375543397617608528881621312159551521324412657167692163397240217814307445909713899850058291308690066733028125556419716734774904437710284132364898181426902860503703874999414246848733477446908396851600224567407637334679631394476122651438668110771117818686943497967108192010818356995023330089079080278635386063923383437486637555787861728490935630579993241432729945572572039527546968749899721199864050991936636425 

noncomputable def Ns60p10 := nat_lit 6037312065319767048564142443281100833094517501602298457411621838401909436348967513970575877459259771623941548258204445821942291045664120860093665600098153114527011142424471743215189638406506367790367599859596104992621477169994698594142049192256667252266301439715334971326182286325870243632349119406725171166047972624848379242642987691741446913322611634487665631123884299676351857591585933871955560195724863436092564725843702568563820604138142931407752731605404492259322164906548421338089777140624840599546449293504664341809058329304227251421882253537858630692969727217927909816425536009981778974686700833928275616694615814871054602955126209568752228017149733267081250625 

noncomputable def Ns60p11 := BSN.log_dyadic_bound Ns60p6 Ns60p7 14 13 Ns60p8 67108864 17475728 Ns60p9 Ns60p10 76821522 Ns60p4 Ns60p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP Ns60p6) (BSN.artanhQ Ns60p7) 0 13 Ns60p9 Ns60p8 Ns60p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns60p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns60p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns60p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns60p15 := nat_lit 4564579050430719991598727864173574027249459620864950728835381976489772818715667160654947079996042508112007609792086902604246591277951902079645511578729044446029890641532783292129843149875777032317116470385319181253925715321425403083930304095443896121595862314424397722115177325385869596477930511910402142030838288588290691454497602943515837117442179176528567975378491450565217634156690207739385924001994080445739653712153122146143735369275124802705327973995316801123426696765469161725178407791303143690561306079033018690304653273985689879967765287476386100315971524212560669782530460797364817008851488910076252022325883262600059844010859170953904690437223359663042798211193766875 

noncomputable def Ns60p16 := nat_lit 487897090127146028016094362581487656757614504303373888298359177917068925336311225982425876767220472971199663852495703606478044548245204650969304786130313739004418091807374551157966311600460925549125369213480618028519005676490156484647720769146106466452899814849266557198964140238149260938822380107756357944282785296375303842904282420173433118269847736574242174913483374429734863225743639963757643848706968740179283875896315642693907130861939137742544595612595383386022728925244773380688186919137495322289344312028838765525860232491884325012249877491080249836360703014994786844727995613684463741175252463635603207543937219860925630575346787413234983278028650172664050991936636425 

noncomputable def Ns60p17 := nat_lit 6037312065319913640506765330482094651728996212510072186683329349665034025528265882310343281188309943135362157762326025787898903072857099500666458772539172249805276355211909724494669715550462680374559205875381267976760313571991112548079805305194151041203595124480241065931717334103047325628819416103687949050116922196393250525830281764599302835242983634853487222885409728030646963007168165596579721200854339637057218394652367706804217404799249814690071011337988816707639904852988452679974011323771101001271418584434659185032723127441286381829860978672625319259709832419206399165424340759332155638209605427889981579187342651500575472600628768480466654897149733267081250625 

noncomputable def Ns60p18 := BSN.log_dyadic_bound Ns60p13 Ns60p14 14 13 Ns60p15 67108864 17475728 Ns60p16 Ns60p17 76821522 Ns60p12 Ns60p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP Ns60p13) (BSN.artanhQ Ns60p14) 0 13 Ns60p16 Ns60p15 Ns60p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns60p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 38410761 33554432 2 33554432 38410761 33554432 1 16777216 (Ns60p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns60p0 Ns60p1 76821522 67108864 1 17475728 Bool.false (BSN.logfrac_isNear Ns60p4 Ns60p5 1 Ns60p0 Ns60p1 76821522 67108864 17475728 rfl rfl rfl (Ns60p11 rfl))) (BSN.isNear_log_sfrac Ns60p2 Ns60p1 76821522 67108864 1 17475728 Bool.false (BSN.logfrac_isNear Ns60p12 Ns60p5 1 Ns60p2 Ns60p1 76821522 67108864 17475728 rfl rfl rfl (Ns60p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS061to078.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 1 16777216 := Ns60p19 

noncomputable def Ns60p20 := BSN.log_dyadic_bound 1 3 7 6 71816279535 4194304 1092233 2852596872 10395 2907269 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1) (BSN.artanhQ 3) 0 6 2852596872 71816279535 10395 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz913 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz624 := qz913

noncomputable abbrev qz316 := qz624

noncomputable abbrev qz0 := qz316

theorem RS061to078.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 2907269 4194304 1 1092233 := BSN.isNear_log_sfrac 2 1 2907269 4194304 1 1092233 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 2907269 4194304 1092233 rfl rfl rfl (Ns60p20 rfl)) 

theorem RS061to078.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 46516304 67108864 62 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 2907269 4194304 1 1092233 46516304 67108864 62 67108864 RS061to078.d6 rfl 

noncomputable abbrev qz625 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz626 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz627 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def Ns60p21 := @Enclosure.Real.IsNear.inv_image qz625 11863283 8388608 1 8388608 2965820 2965822 4194304 (@Enclosure.Real.IsNear.of_eq qz625 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz626 qz627)) Bool.false 11863283 8388608 1 8388608 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz626 qz627)) Bool.false 11863283 8388608 1 8388608 11863283 8388608 1 8388608 (BSN.sqrt_enclosure 2 1 5931641 5931642 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz628 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS061to078.d8 : Enclosure.Real.IsNear qz628 Bool.false 2965821 4194304 1 4194304 := @Enclosure.Real.IsNear.recentre' qz628 Bool.false 5931642 8388608 2 8388608 2965821 4194304 1 4194304 (Ns60p21 rfl rfl) rfl 

theorem RS061to078.d9 : Enclosure.Real.IsNear qz628 Bool.false 47453136 67108864 16 67108864 := @Enclosure.Real.IsNear.recentre' qz628 Bool.false 2965821 4194304 1 4194304 47453136 67108864 16 67108864 RS061to078.d8 rfl 

noncomputable def Ns60p22 := BSN.log_dyadic_bound 1 2 12 11 1326382131865190400 4194304 1092233 130797573554866995 13749310575 4607913 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base11 (BSN.artanhP 1) (BSN.artanhQ 2) 0 11 130797573554866995 1326382131865190400 13749310575 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz317 := (Enclosure.sfrac Bool.false 3 1)

theorem RS061to078.d10 : Enclosure.Real.IsNear (Real.log qz317) Bool.false 4607913 4194304 1 1092233 := BSN.isNear_log_sfrac 3 1 4607913 4194304 1 1092233 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 4607913 4194304 1092233 rfl rfl rfl (Ns60p22 rfl)) 

theorem RS061to078.d11 : Enclosure.Real.IsNear (Real.log qz317) Bool.false 73726608 67108864 62 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log qz317) Bool.false 4607913 4194304 1 1092233 73726608 67108864 62 67108864 RS061to078.d10 rfl 

noncomputable abbrev qz629 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz630 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns60p23 := @Enclosure.Real.IsNear.inv_image qz629 14529495 8388608 1 8388608 2421582 2421583 4194304 (@Enclosure.Real.IsNear.of_eq qz629 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz630 qz627)) Bool.false 14529495 8388608 1 8388608 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz630 qz627)) Bool.false 14529495 8388608 1 8388608 14529495 8388608 1 8388608 (BSN.sqrt_enclosure 3 1 7264747 7264748 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz631 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS061to078.d12 : Enclosure.Real.IsNear qz631 Bool.false 4843165 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz631 Bool.false 4843165 8388608 1 8388608 4843165 8388608 1 8388608 (Ns60p23 rfl rfl) rfl 

theorem RS061to078.d13 : Enclosure.Real.IsNear qz631 Bool.false 38745320 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz631 Bool.false 4843165 8388608 1 8388608 38745320 67108864 8 67108864 RS061to078.d12 rfl 

noncomputable def Ns60p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns60p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns60p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns60p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns60p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns60p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns60p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns60p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns60p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns60p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns60p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns60p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns60p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns60p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns60p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns60p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns60p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns60p25 Ns60p26 Ns60p27 Ns60p28 200200021673987500790625 Ns60p29 Ns60p30 Ns60p31 Ns60p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns60p32 Ns60p33 151412625 Ns60p34 Ns60p35 1322214852783825 Ns60p27 Ns60p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns60p32 Ns60p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns60p34 Ns60p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns60p36 Ns60p37 1267389585 Ns60p38 Ns60p39 1927077560082675 Ns60p29 Ns60p30 Ns60p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns60p36 Ns60p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns60p38 Ns60p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz632 := (@Nat.cast Real Real.instNatCast 5)

theorem RS061to078.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz627 qz632)) Bool.false Ns60p24 Ns60p25 1 Ns60p26 := Ns60p40 rfl rfl rfl 

noncomputable def Ns60p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns60p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns60p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns60p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns60p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns60p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns60p25 Ns60p26 Ns60p42 Ns60p43 9945 Ns60p44 Ns60p45 65835 Ns60p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns60p42 Ns60p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns60p44 Ns60p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS061to078.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz627 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns60p41 Ns60p25 1 Ns60p26 := Ns60p46 rfl 

noncomputable def Ns60p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns60p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS061to078.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns60p47 Ns60p25 1 Ns60p48 := BSN.pi_combine Ns60p24 Ns60p41 Ns60p25 Ns60p26 Ns60p48 Ns60p47 rfl rfl rfl rfl RS061to078.d14 RS061to078.d15 

theorem RS061to078.d17 : Enclosure.Real.IsNear Real.pi Bool.false 3537118876014220 1125899906842624 1 1125899906842624 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns60p47 Ns60p25 1 Ns60p48 3537118876014220 1125899906842624 1 1125899906842624 RS061to078.d16 rfl 

noncomputable def Ns60p49 := nat_lit 178719669545544893480837345123291015625 

noncomputable def Ns60p50 := nat_lit 27745388228251122714770036239987464375 

noncomputable def Ns60p51 := nat_lit 1274524447665412456340166714375 

noncomputable def Ns60p52 := BSN.log_dyadic_bound 3 5 16 15 Ns60p49 4194304 1092233 Ns60p50 Ns60p51 5814539 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP 3) (BSN.artanhQ 5) 0 15 Ns60p50 Ns60p49 Ns60p51 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz318 := (Enclosure.sfrac Bool.false 4 1)

theorem RS061to078.d18 : Enclosure.Real.IsNear (Real.log qz318) Bool.false 5814539 4194304 1 1092233 := BSN.isNear_log_sfrac 4 1 5814539 4194304 1 1092233 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 5814539 4194304 1092233 rfl rfl rfl (Ns60p52 rfl)) 

theorem RS061to078.d19 : Enclosure.Real.IsNear (Real.log qz318) Bool.false 93032624 67108864 62 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log qz318) Bool.false 5814539 4194304 1 1092233 93032624 67108864 62 67108864 RS061to078.d18 rfl 

noncomputable abbrev qz633 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz634 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns60p53 := @Enclosure.Real.IsNear.inv_image qz633 16777217 8388608 1 8388608 2097151 2097152 4194304 (@Enclosure.Real.IsNear.of_eq qz633 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz634 qz627)) Bool.false 16777217 8388608 1 8388608 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz634 qz627)) Bool.false 16777217 8388608 1 8388608 16777217 8388608 1 8388608 (BSN.sqrt_enclosure 4 1 8388608 8388609 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz635 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS061to078.d20 : Enclosure.Real.IsNear qz635 Bool.false 4194303 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz635 Bool.false 4194303 8388608 1 8388608 4194303 8388608 1 8388608 (Ns60p53 rfl rfl) rfl 

theorem RS061to078.d21 : Enclosure.Real.IsNear qz635 Bool.false 33554424 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz635 Bool.false 4194303 8388608 1 8388608 33554424 67108864 8 67108864 RS061to078.d20 rfl 

noncomputable def Ns60p54 := nat_lit 432044237847189949652629901200995702590625 

noncomputable def Ns60p55 := nat_lit 89467042677079332529401996239971435345500 

noncomputable def Ns60p56 := nat_lit 2254217236409302326906244300800000 

noncomputable def Ns60p57 := nat_lit 1703271991756449094855875 

noncomputable def Ns60p58 := BSN.log_dyadic_bound 2 3 20 19 Ns60p54 4194304 1092233 Ns60p55 Ns60p56 6750471 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 19 9 52520441922763380 253655458399017675 9033331507200 1156268355358836200013540 Ns60p57 249544393960587264000 Ns60p55 Ns60p54 Ns60p56 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 2) (BSN.artanhQ 3) 0 9 52520441922763380 253655458399017675 9033331507200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 9 19 1156268355358836200013540 Ns60p57 249544393960587264000 rfl rfl rfl rfl)) rfl rfl 

theorem RS061to078.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 6750471 4194304 1 1092233 := BSN.isNear_log_sfrac 5 1 6750471 4194304 1 1092233 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 6750471 4194304 1092233 rfl rfl rfl (Ns60p58 rfl rfl)) 

theorem RS061to078.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 108007536 67108864 62 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 6750471 4194304 1 1092233 108007536 67108864 62 67108864 RS061to078.d22 rfl 

noncomputable abbrev qz636 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns60p59 := @Enclosure.Real.IsNear.inv_image qz636 18757497 8388608 1 8388608 1875749 1875750 4194304 (@Enclosure.Real.IsNear.of_eq qz636 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz632 qz627)) Bool.false 18757497 8388608 1 8388608 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz632 qz627)) Bool.false 18757497 8388608 1 8388608 18757497 8388608 1 8388608 (BSN.sqrt_enclosure 5 1 9378748 9378749 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz637 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS061to078.d24 : Enclosure.Real.IsNear qz637 Bool.false 3751499 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz637 Bool.false 3751499 8388608 1 8388608 3751499 8388608 1 8388608 (Ns60p59 rfl rfl) rfl 

theorem RS061to078.d25 : Enclosure.Real.IsNear qz637 Bool.false 30011992 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz637 Bool.false 3751499 8388608 1 8388608 30011992 67108864 8 67108864 RS061to078.d24 rfl 

noncomputable def Ns60p60 := BSN.log_dyadic_bound 2 10 5 4 94500000000 4194304 1092233 1291130880 26880 1700643 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 2) (BSN.artanhQ 10) 0 4 1291130880 94500000000 26880 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz914 := (Enclosure.sfrac Bool.false 6 1)

noncomputable abbrev qz638 := qz914

noncomputable abbrev qz319 := qz638

noncomputable abbrev qz1 := qz319

noncomputable abbrev qz639 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) (@Nat.cast Real Real.instNatCast 1))

theorem RS061to078.d26 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 4034683142479095 2251799813685248 500000001092233 546116500000000000000 := BSN.isNear_log_sfrac 6 1 4034683142479095 2251799813685248 500000001092233 546116500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz639) Bool.false 270763002291722209198080 151115727451828646838272 1000000002184466 1092233000000000000000 4034683142479095 2251799813685248 500000001092233 546116500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 1700643 4194304 24973259072661432 36028797018963968 1092233 1000000000000000 rfl rfl rfl rfl (Ns60p60 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS061to078.d27 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 120242927 67108864 63 67108864 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 4034683142479095 2251799813685248 500000001092233 546116500000000000000 120242927 67108864 63 67108864 RS061to078.d26 rfl 

noncomputable abbrev qz640 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns60p61 := @Enclosure.Real.IsNear.inv_image qz640 20547809 8388608 1 8388608 1712317 1712318 4194304 (@Enclosure.Real.IsNear.of_eq qz640 (Real.sqrt qz639) Bool.false 20547809 8388608 1 8388608 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz639) Bool.false 20547809 8388608 1 8388608 20547809 8388608 1 8388608 (BSN.sqrt_enclosure 6 1 10273904 10273905 4194304 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz641 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS061to078.d28 : Enclosure.Real.IsNear qz641 Bool.false 3424635 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz641 Bool.false 3424635 8388608 1 8388608 3424635 8388608 1 8388608 (Ns60p61 rfl rfl) rfl 

theorem RS061to078.d29 : Enclosure.Real.IsNear qz641 Bool.false 27397080 67108864 8 67108864 := @Enclosure.Real.IsNear.recentre' qz641 Bool.false 3424635 8388608 1 8388608 27397080 67108864 8 67108864 RS061to078.d28 rfl 

theorem RS061to078.d30 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz915 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz642 := qz915

noncomputable abbrev qz320 := qz642

noncomputable abbrev qz2 := qz320

noncomputable abbrev qz916 := (Enclosure.Real.IsNear.const Bool.false 2 1)

noncomputable abbrev qz321 := qz916

theorem RS061to078.d31 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 qz321 RS061to078.d30 rfl 

noncomputable abbrev qz3 := (@Inv.inv Real Real.instInv qz320)

theorem RS061to078.d32 : Enclosure.Real.IsNear qz3 Bool.false 1335089 8388608 1 8388608 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 1335089 8388608 1 8388608 1335089 8388608 1 8388608 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 667544 667545 4194304 RS061to078.d31 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns60p62 := nat_lit 161185140958880037521588224 

noncomputable def Ns60p63 := nat_lit 1604922329545832668206202880 

noncomputable abbrev qz917 := (Enclosure.sfrac Bool.false 257388 1000)

noncomputable abbrev qz643 := qz917

noncomputable abbrev qz322 := qz643

noncomputable abbrev qz4 := qz322

noncomputable abbrev qz918 := (@instHMul Real Real.instMul)

noncomputable abbrev qz644 := qz918

noncomputable abbrev qz323 := qz644

noncomputable abbrev qz5 := qz323

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 6)

noncomputable abbrev qz919 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 257388 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz645 := qz919

noncomputable abbrev qz324 := qz645

noncomputable abbrev qz7 := qz324

noncomputable abbrev qz8 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz920 := (@instHSub Real Real.instSub)

noncomputable abbrev qz921 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 257388 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz646 := (@HSub.hSub Real Real Real qz920 qz921 qz914)

noncomputable abbrev qz325 := qz646

noncomputable abbrev qz9 := qz325

noncomputable abbrev qz326 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz922 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz326 qz7 qz8))

noncomputable def Ns60p64 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 6) (@HMul.hMul Real Real Real qz5 qz922 (Zeta.RiemannSiegel.correction qz9)) 40847173 16777216 46093 33554432 5836941994116011559 36893488147419103232 2859597304046158417377 Ns60p62 Ns60p63 

noncomputable def Ns60p65 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin BSN.quadSignPos 5 6 257388 1000 71 67108864 33554432 1125899906842624 Bool.false 23401973128 1025 120242927 63 27397080 8 

noncomputable def Ns60p66 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 257388 1000 5 41 67108864 33554432 1125899906842624 Bool.false 23401973128 1025 

noncomputable def Ns60p67 := Ns60p66 93032624 62 33554424 8 108007536 62 30011992 8 Bool.true 68436536 22937 Bool.true 16436112 Bool.true 75881908 3537118876014220 1 Bool.false 16272285 Bool.true Bool.false 60714918 Bool.true Bool.true 103725210 

noncomputable def Ns60p68 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 257388 1000 108 41 67108864 33554432 1125899906842624 Bool.false 23401973128 1025 

noncomputable def Ns60p69 := Ns60p68 46516304 62 47453136 16 73726608 62 38745320 8 Bool.true 67108856 1094 Bool.false 44484110 Bool.false 103640308 3537118876014220 1 Bool.false 52897386 Bool.false Bool.false 67085416 Bool.true Bool.true 68436536 

noncomputable def Ns60p70 := nat_lit 1393532548392248539401728754579124411967313493047 

noncomputable def Ns60p71 := nat_lit 3996175269314940222011866564998438033607884800 

noncomputable def Ns60p72 := nat_lit 279611648000000000000000000 

noncomputable def Ns60p73 := nat_lit 542234149346914222339095920640000 

noncomputable def Ns60p74 := nat_lit 837388854097446007609991335426129920 

noncomputable abbrev qz10 := (@Eq.refl Real qz322)

noncomputable def Ns60p75 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 257388 1000 264995330176 16000000 514776 4000 2000 Ns60p73 Ns60p74 qz10 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns60p76 := nat_lit 131510230691665536400653641750540396346273394195672596480 

noncomputable abbrev qz647 := qz920

noncomputable abbrev qz327 := qz647

noncomputable abbrev qz11 := qz327

noncomputable abbrev qz12 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz13 := (@HMul.hMul Real Real Real qz323 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz14 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz923 := (Real.log (Enclosure.sfrac Bool.false 264995330176 16000000))

noncomputable abbrev qz924 := (@HSub.hSub Real Real Real qz11 qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 514776))))

noncomputable abbrev qz648 := (@HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 257388 4000) qz923) (@HMul.hMul Real Real Real qz5 qz12 qz924))

noncomputable abbrev qz925 := (Enclosure.sfrac Bool.false 257388 2000)

noncomputable abbrev qz328 := (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 qz648 qz925) (@HMul.hMul Real Real Real qz5 qz925 (Real.log Real.pi)))

noncomputable def Ns60p77 := @Enclosure.Real.IsNear.addLit_ft_p qz328 (Enclosure.sfrac Bool.true Ns60p73 Ns60p74) 157048274823243710919 450359962737049600 4267938140200487934359 Ns60p72 Ns60p73 Ns60p74 0 1 Ns60p76 

noncomputable def Ns60p78 := nat_lit 13174164145684607793648107520000 

noncomputable abbrev qz329 := (@HSub.hSub Real Real Real qz11 qz648 qz925)

noncomputable def Ns60p79 := @Enclosure.Real.IsNear.subLit_ff_p qz329 (@HMul.hMul Real Real Real qz5 qz925 (Real.log Real.pi)) 1116976224295206406371 2251799813685248000 8293375984083365039 1092233000000000000000000 2471617238067 16777216000 64347 8388608000 Ns60p78 157048274823243710919 450359962737049600 

noncomputable def Ns60p80 := nat_lit 2233952448590412812742000 

noncomputable abbrev qz330 := qz648

noncomputable def Ns60p81 := @Enclosure.Real.IsNear.subLit_ff_p qz330 qz925 1406769349517615712483 2251799813685248000 8293375984083365039 1092233000000000000000000 257388 2000 0 1 Ns60p80 1116976224295206406371 2251799813685248000 8293375984083365039 1092233000000000000000000 

noncomputable def Ns60p82 := nat_lit 3167762959141884584793328297426550784 

noncomputable def Ns60p83 := nat_lit 11744567744497102008352768 

noncomputable def Ns60p84 := nat_lit 1208925819614629174706176 

noncomputable def Ns60p85 := BSN.log_dyadic_bound 2851330176 527139330176 2 1 833627620255205832572928 33554432 8737864 8130083772568190976 8130083772568190976 362999 529990660352 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2851330176) (BSN.artanhQ 527139330176) 0 1 8130083772568190976 833627620255205832572928 8130083772568190976 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz649 := qz923

noncomputable abbrev qz650 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns60p86 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 257388 4000) qz649 257388 4000 0 1 21875962139101889 2251799813685248 62500007645631 546116500000000000000 1407652535764789251483 2251799813685248000 4021687991973417957 546116500000000000000000 (Enclosure.Real.IsNear.const Bool.false 257388 4000) (BSN.isNear_log_sfrac 264995330176 16000000 21875962139101889 2251799813685248 62500007645631 546116500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 264995330176) qz650)) Bool.false Ns60p83 Ns60p84 1000000122330096 8737864000000000000000 21875962139101889 2251799813685248 62500007645631 546116500000000000000 (BSN.log_rat_reduce_isNear 264995330176 16000000 14 529990660352 524288000000 362999 33554432 24973259072661432 36028797018963968 8737864 1000000000000000 rfl rfl rfl rfl (Ns60p85 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p87 := BSN.arctan_dyadic_bound_f 1000 514776 1 0 4194304 1092233 0 1 1 0 1 1 8147 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 514776) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 514776) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz15 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz926 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 514776)))

noncomputable abbrev qz651 := qz926

noncomputable abbrev qz331 := qz651

noncomputable def Ns60p88 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz331 884279719003555 562949953421312 1 2000000000000000 8147 4194304 1 1092233 3704351609264963321856 883186247173539 562949953421312 2000000001092233 2184466000000000000000 qz15 (Ns60p87 rfl) rfl rfl 

noncomputable abbrev qz652 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 257388 4000) qz923)

noncomputable abbrev qz332 := qz652

noncomputable abbrev qz653 := (@HMul.hMul Real Real Real qz5 qz12 qz924)

noncomputable abbrev qz333 := qz653

noncomputable abbrev qz654 := qz924

noncomputable abbrev qz334 := qz654

noncomputable abbrev qz335 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns60p89 := @Enclosure.Real.IsNear.subLit_ff_p qz332 qz333 1407652535764789251483 2251799813685248000 4021687991973417957 546116500000000000000000 883186247173539 2251799813685248 2000000001092233 8737864000000000000000 Ns60p82 1406769349517615712483 2251799813685248000 8293375984083365039 1092233000000000000000000 (Ns60p86 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz12 qz334 1 4 0 1 883186247173539 562949953421312 2000000001092233 2184466000000000000000 883186247173539 2251799813685248 2000000001092233 8737864000000000000000 qz335 Ns60p88 rfl) 

noncomputable def Ns60p90 := @Ns60p77 Ns60p70 Ns60p71 4267938140200487934359 Ns60p72 (@Ns60p79 4267938140200487934359 Ns60p72 (Ns60p81 (Ns60p89 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 257388 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz925 (Real.log Real.pi) 257388 2000 0 1 38410761 33554432 1 16777216 2471617238067 16777216000 64347 8388608000 (Enclosure.Real.IsNear.const Bool.false 257388 2000) RS061to078.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns60p73 Ns60p74) 

noncomputable abbrev qz336 := (@instHAdd Real Real.instAdd)

noncomputable def Ns60p91 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns60p70 Ns60p71 4267938140200487934359 Ns60p72 2925246641 8388608 129 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz336 qz328 (Enclosure.sfrac Bool.true Ns60p73 Ns60p74)) Bool.false Ns60p70 Ns60p71 4267938140200487934359 Ns60p72 Ns60p75 (Ns60p90 rfl rfl)) 

noncomputable def Ns60p92 := nat_lit 1898721499165245950656512 

noncomputable def Ns60p93 := nat_lit 139913642447306588647730345615241017910231960874198359914810175933192563201188732094785 

noncomputable def Ns60p94 := nat_lit 2753733154729970958028337252922338050165611694356407771374444090804896824278383046164480 

noncomputable def Ns60p95 := nat_lit 280964686945859506463954438917968525435004030278776226158259103378746311004304722241 

noncomputable def Ns60p96 := nat_lit 365985596916462054876447359900716431199903224335782447791675184133843504832915900221761 

noncomputable def Ns60p97 := nat_lit 50485107836716134230519516303576197586369547729867475808531474998089775111770355846348800 

noncomputable abbrev qz655 := (BSN.sinEvenQ 17179869184)

noncomputable abbrev qz656 := (BSN.sinOddQ 17179869184)

noncomputable def Ns60p98 := BSN.sin_dyadic_bound_f 26982455369 17179869184 3 2 8388608 2186600 Ns60p93 Ns60p94 Ns60p95 Ns60p96 Ns60p97 Ns60p95 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26982455369) qz655 0 2 Ns60p93 Ns60p94 Ns60p95 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26982455369) qz656 0 2 Ns60p96 Ns60p97 Ns60p95 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz337 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable abbrev qz657 := (@Nat.cast Real Real.instNatCast Ns60p84)

noncomputable def Ns60p99 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2925246641) qz337) Bool.false 2925246641 8388608 129 8388608 Bool.true 8388607 8388608 1 1092233 (Ns60p91 rfl) (Enclosure.sfrac_false_div 2925246641 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2925246641) qz337) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns60p92) qz657) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 55 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q1 2925246641 8388608 226375608064910080 72057594037927936 55 Ns60p92 Ns60p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns60p92 Ns60p84 26982455369 17179869184 2186600 2184466 (Ns60p98 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p100 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns60p70 Ns60p71 4267938140200487934359 Ns60p72 23401973128 67108864 1025 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz336 qz328 (Enclosure.sfrac Bool.true Ns60p73 Ns60p74)) Bool.false Ns60p70 Ns60p71 4267938140200487934359 Ns60p72 Ns60p75 (Ns60p90 rfl rfl)) 

noncomputable def Ns60p101 := Ns60p69 22937 BSN.abs_quadSignPos (BSN.cos_quad_nat0 108 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 52897386 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 41 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 67085416 67108864) qz10 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 8388607 8388608 149286665 9162314481664 67108856 67108864 1094 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 8388607 8388608 149286665 9162314481664 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 8388607 8388608 149286665 9162314481664 8388607 8388608 149286665 9162314481664 (Ns60p99 rfl rfl) rfl)) rfl) (Ns60p100 rfl) RS061to078.d7 

noncomputable def Ns60p102 := nat_lit 133443787666118966474070403132251796579715190852489988322480800000 

noncomputable def Ns60p103 := nat_lit 16586685937797756904922089360178093090225977525586485022553978961920 

noncomputable def Ns60p104 := nat_lit 15333427637800767341878338717909323366459344146265008100000000 

noncomputable def Ns60p105 := nat_lit 400300696143081297887527452719319571092412653869177434951242400000 

noncomputable def Ns60p106 := nat_lit 746400867200899060721494021208014189060168988651391826014929053286400 

noncomputable abbrev qz338 := (BSN.cosEvenQ 67108864)

noncomputable def Ns60p107 := BSN.cos_dyadic_bound_f 44484110 67108864 3 2 67108864 33554432 Ns60p102 Ns60p103 Ns60p104 Ns60p105 Ns60p106 Ns60p104 52897386 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 44484110) qz338 0 2 Ns60p102 Ns60p103 Ns60p104 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 44484110) (BSN.cosOddQ 67108864) 0 2 Ns60p105 Ns60p106 Ns60p104 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p108 := nat_lit 2467569567481073659239182783394810917444689587893677906499872174984066898072150813206357794845397876736 

noncomputable def Ns60p109 := nat_lit 51956389457850993117201226487380036501230565613159928972022824181150019275806034930923536691271355596800 

noncomputable def Ns60p110 := nat_lit 1535834218633523851247494684734725195378708629715546196911920845713471254168864726367261673127936 

noncomputable def Ns60p111 := nat_lit 12323521377321117296220008835872062994720199099605490803377978994125934679842362143221628579852316573696 

noncomputable def Ns60p112 := nat_lit 1818473631024784759102042927058301277543069796460597514020798846340250674653211222582323784194497445888000 

noncomputable abbrev qz339 := (BSN.sinEvenQ 67108864)

noncomputable def Ns60p113 := BSN.sin_dyadic_bound_f 103640308 67108864 4 3 67108864 33554432 Ns60p108 Ns60p109 Ns60p110 Ns60p111 Ns60p112 Ns60p110 67085416 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 103640308) qz339 0 3 Ns60p108 Ns60p109 Ns60p110 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 103640308) (BSN.sinOddQ 67108864) 0 3 Ns60p111 Ns60p112 Ns60p110 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p114 := nat_lit 72978741196464738567087783936 

noncomputable def Ns60p115 := nat_lit 2433889152438200450873670154321920 

noncomputable def Ns60p116 := nat_lit 17037224067067403156115691080253440 

noncomputable def Ns60p117 := BSN.sin_dyadic_bound_f 16436112 67108864 2 1 67108864 33554432 Ns60p114 Ns60p115 Ns60p114 Ns60p114 Ns60p116 Ns60p114 16272285 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 16436112) qz339 0 1 Ns60p114 Ns60p115 Ns60p114 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 16436112) (BSN.sinOddQ 67108864) 0 1 Ns60p114 Ns60p116 Ns60p114 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p118 := nat_lit 2034646700375307301190545882896313085350782280163087332529085153280 

noncomputable def Ns60p119 := nat_lit 149280173440179812144298804241602837812033797730278365202985810657280 

noncomputable def Ns60p120 := nat_lit 1099273957031826229616913396581586658701238362575892347439087616 

noncomputable def Ns60p121 := nat_lit 5327056819338229498746335643038735511804627776411534426156512116736 

noncomputable def Ns60p122 := nat_lit 2736803179736629889312144744429385359887286291721770028721406528716800 

noncomputable def Ns60p123 := BSN.sin_dyadic_bound_f 75881908 67108864 3 2 67108864 33554432 Ns60p118 Ns60p119 Ns60p120 Ns60p121 Ns60p122 Ns60p120 60714918 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 75881908) qz339 0 2 Ns60p118 Ns60p119 Ns60p120 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 75881908) (BSN.sinOddQ 67108864) 0 2 Ns60p121 Ns60p122 Ns60p120 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p124 := Ns60p67 39044 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 5 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 16272285 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 41 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 60714918 67108864) qz10 rfl rfl (Ns60p101 RS061to078.d9 RS061to078.d11 RS061to078.d13 RS061to078.d17 (Ns60p107 rfl rfl) (Ns60p113 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns60p100 rfl) RS061to078.d19 RS061to078.d21 RS061to078.d23 RS061to078.d25 RS061to078.d17 (Ns60p117 rfl rfl) (Ns60p123 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns60p125 := nat_lit 947796325621210611842456965686546981894882801183310564323600236800 

noncomputable def Ns60p126 := nat_lit 238675923884604426743475286339427437057106643048730924321997056 

noncomputable def Ns60p127 := nat_lit 2481937282274024147658374045382121117683743449486591627922431672576 

noncomputable def Ns60p128 := BSN.sin_dyadic_bound_f 62694014 67108864 3 2 67108864 33554432 Ns60p125 Ns60p119 Ns60p126 Ns60p127 Ns60p122 Ns60p126 53964375 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 62694014) qz339 0 2 Ns60p125 Ns60p119 Ns60p126 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 62694014) (BSN.sinOddQ 67108864) 0 2 Ns60p127 Ns60p122 Ns60p126 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz927 := (BSN.cos_quad_nat3 71 rfl)

noncomputable def Ns60p129 := Ns60p65 Bool.true 103725210 39044 Bool.true 62694014 3537118876014220 1 Bool.false 53964375 Bool.false Bool.true 81694346 46093 BSN.abs_quadSignPos qz927 (BSN.sfrac_eq_quadSignPos_mul Bool.false 53964375 67108864) qz10 rfl (Ns60p124 rfl rfl) (Ns60p100 rfl) RS061to078.d27 RS061to078.d29 RS061to078.d17 (Ns60p128 rfl rfl) rfl 

noncomputable def Ns60p130 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 6) 81694346 67108864 46093 67108864 81694346 67108864 46093 67108864 10964829510565888 40847173 16777216 46093 33554432 (Ns60p129 rfl rfl rfl rfl) 

noncomputable def Ns60p131 := @Enclosure.Real.IsNear.mulLit_ff qz922 (Zeta.RiemannSiegel.correction qz9) 828949 2097152 1 4194304 7041376482891 17592186044416 1715554238542929 38429532279701241856 5836941994116011559 36893488147419103232 

noncomputable abbrev qz928 := (@HPow.hPow Real Real Real qz326 qz7 qz8)

noncomputable def Ns60p132 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz928 1 1 0 1 828949 2097152 1 4194304 828949 2097152 1 4194304 

noncomputable abbrev qz340 := (@Enclosure.Real.IsNear.of_eq qz7 (@HMul.hMul Real Real Real qz5 qz4 qz3) Bool.false 85908971883 2097152000 64347 2097152000 (BSN.t_div_two_pi_mk qz4 257388 1000 qz10) (@Enclosure.Real.IsNear.mulLit_ff qz4 qz3 257388 1000 0 1 1335089 8388608 1 8388608 85908971883 2097152000 64347 2097152000 (Enclosure.Real.IsNear.const Bool.false 257388 1000) RS061to078.d32 rfl))

noncomputable def Ns60p133 := @Enclosure.Real.IsNear.sqrt_image qz7 85908971883 2097152000 64347 2097152000 26845039 26845060 4194304 qz340 

noncomputable abbrev qz658 := qz921

noncomputable abbrev qz341 := qz658

noncomputable abbrev qz16 := qz341

noncomputable def Ns60p134 := @Enclosure.Real.IsNear.sqrt_image qz16 53690099 8388608 21 8388608 10611138 10611143 4194304 (@Enclosure.Real.IsNear.recentre' qz16 Bool.false 53690099 8388608 21 8388608 53690099 8388608 21 8388608 (Ns60p133 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz929 := (Real.sqrt (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 257388 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))))

noncomputable abbrev qz659 := qz929

noncomputable abbrev qz342 := qz659

noncomputable abbrev qz17 := qz342

noncomputable def Ns60p135 := @Enclosure.Real.IsNear.inv_image qz17 21222281 8388608 5 8388608 1657897 1657899 4194304 (@Enclosure.Real.IsNear.recentre' qz17 Bool.false 21222281 8388608 5 8388608 21222281 8388608 5 8388608 (Ns60p134 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns60p136 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz17) Bool.false 3315796 8388608 2 8388608 828949 2097152 1 4194304 (Ns60p135 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz18 := (Real.cos (@HMul.hMul Real Real Real qz323 qz320 qz325))

noncomputable abbrev qz343 := (@HSub.hSub Real Real Real qz647 (@HMul.hMul Real Real Real qz644 qz646 qz646) qz646)

noncomputable abbrev qz930 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz344 := qz930

noncomputable abbrev qz19 := (@HMul.hMul Real Real Real qz323 qz320 (@HSub.hSub Real Real Real qz327 qz343 qz344))

noncomputable def Ns60p137 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz9) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz18) (Real.cos qz19)) Bool.false 7041376482891 

noncomputable def Ns60p138 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz18) (Real.cos qz19) 5175987 4194304 27 

noncomputable abbrev qz931 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz18))

noncomputable def Ns60p139 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz18) (@Neg.neg Real Real.instNeg qz931) Bool.true 5175987 4194304 27 1048576 (BSN.inv_eq_neg_inv_neg qz18) 

noncomputable def Ns60p140 := @Enclosure.Real.IsNear.recentre' qz931 Bool.false 10351974 8388608 216 8388608 5175987 4194304 

noncomputable def Ns60p141 := @Enclosure.Real.IsNear.recentre' qz18 Bool.true 6797616 8388608 153655597 9162314481664 424851 524288 153655597 9162314481664 

noncomputable abbrev qz20 := (@HMul.hMul Real Real Real qz323 qz320 qz325)

noncomputable def Ns60p142 := @Enclosure.Real.IsNear.cos_image qz20 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21101769) qz337) Bool.false 21101769 8388608 133 8388608 Bool.true 6797616 8388608 1 

noncomputable def Ns60p143 := nat_lit 566707583618773828978985299 

noncomputable def Ns60p144 := nat_lit 36028797018963968000000000000000 

noncomputable def Ns60p145 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz9 884279719003555 140737488355328 1 500000000000000 3358451 8388608 21 8388608 2969810106567208293305 1180591620717411303424 Ns60p143 

noncomputable def Ns60p146 := @Enclosure.Real.IsNear.subLit_ff_p qz16 qz1 53690099 8388608 21 8388608 6 1 0 1 3358451 3358451 8388608 21 

noncomputable abbrev qz345 := (Enclosure.Real.IsNear.const Bool.false 6 1)

noncomputable def Ns60p147 := @Ns60p146 8388608 (@Enclosure.Real.IsNear.recentre' qz16 Bool.false 53690099 8388608 21 8388608 53690099 8388608 21 8388608 (Ns60p133 rfl rfl rfl rfl rfl rfl) rfl) qz345 

noncomputable def Ns60p148 := @Enclosure.Real.IsNear.recentre' qz20 Bool.false 2969810106567208293305 1180591620717411303424 Ns60p143 Ns60p144 21101769 8388608 133 8388608 (@Ns60p145 Ns60p144 RS061to078.d31 (Ns60p147 rfl rfl) rfl) 

noncomputable def Ns60p149 := nat_lit 18284658691831308898218918671864899324586580235602518213774471400267769546853889818880 

noncomputable def Ns60p150 := nat_lit 4815291108803850789902548873987989187626404057063575880465495954409606215075840256 

noncomputable def Ns60p151 := nat_lit 47880595626334412308342087632897803391422981677152301913221909531060828498364350546176 

noncomputable def Ns60p152 := BSN.sin_dyadic_bound_f 16230347502 17179869184 3 2 8388608 2186600 Ns60p149 Ns60p94 Ns60p150 Ns60p151 Ns60p97 Ns60p150 6797616 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 16230347502) qz655 0 2 Ns60p149 Ns60p94 Ns60p150 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 16230347502) qz656 0 2 Ns60p151 Ns60p97 Ns60p150 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p153 := @Ns60p142 1092233 (Ns60p148 rfl) (Enclosure.sfrac_false_div 21101769 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21101769) qz337) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1142109171350095871868928) qz657) 226375608064910080 72057594037927936 Bool.false 6797616 8388608 0 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q1 21101769 8388608 226375608064910080 72057594037927936 0 1142109171350095871868928 Ns60p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 6797616 8388608 1142109171350095871868928 Ns60p84 16230347502 17179869184 2186600 2184466 (Ns60p152 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p154 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz18) 424851 524288 153655597 9162314481664 5175879 5176095 4194304 (@Enclosure.Real.IsNear.neg qz18 Bool.true 424851 524288 153655597 9162314481664 (Ns60p141 (Ns60p153 rfl rfl) rfl)) 

noncomputable def Ns60p155 := Ns60p139 (@Enclosure.Real.IsNear.neg qz931 Bool.false 5175987 4194304 27 1048576 (@Ns60p140 27 1048576 (Ns60p154 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p156 := @Enclosure.Real.IsNear.recentre' (Real.cos qz19) Bool.true 1360393 4194304 

noncomputable abbrev qz660 := (@Nat.cast Real Real.instNatCast 4194304)

noncomputable def Ns60p157 := @Enclosure.Real.IsNear.cos_image qz19 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7973847)) qz660) Bool.true 7973847 4194304 

noncomputable def Ns60p158 := nat_lit 18827714429223399322149173605 

noncomputable def Ns60p159 := nat_lit 9903520314283042199192993792 

noncomputable def Ns60p160 := nat_lit 8560418972035595988228782006463329 

noncomputable def Ns60p161 := @Enclosure.Real.IsNear.recentre' qz19 Bool.true Ns60p158 Ns60p159 Ns60p160 

noncomputable def Ns60p162 := nat_lit 302231454903657293676544000000000000000 

noncomputable abbrev qz21 := (@HSub.hSub Real Real Real qz327 qz343 qz344)

noncomputable def Ns60p163 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz21 884279719003555 140737488355328 1 500000000000000 21291582317911 

noncomputable abbrev qz22 := qz343

noncomputable abbrev qz23 := qz344

noncomputable def Ns60p164 := @Enclosure.Real.IsNear.subLit_tf qz22 qz23 16893535806807 70368744177664 317216151 70368744177664 1 16 

noncomputable abbrev qz346 := (@HMul.hMul Real Real Real qz644 qz646 qz646)

noncomputable abbrev qz24 := qz346

noncomputable def Ns60p165 := @Enclosure.Real.IsNear.subLit_ff_n qz24 qz9 11279193119401 70368744177664 141055383 70368744177664 3358451 8388608 21 8388608 

noncomputable def Ns60p166 := @Enclosure.Real.IsNear.mulLit_ff qz9 qz9 3358451 8388608 21 8388608 3358451 8388608 21 8388608 11279193119401 70368744177664 

noncomputable def Ns60p167 := nat_lit 7788323624354878046268106278979001611536246550968162274276388901212952303003339996583521 

noncomputable def Ns60p168 := nat_lit 14198936579076412752333613960380805571166435299025227571149477343212749250185412581785600 

noncomputable def Ns60p169 := nat_lit 66071593231572687082325835491003832340771351428707300511130322564501766096195475041 

noncomputable def Ns60p170 := nat_lit 47005799547348141961639937754840227184537103180189766873909299125038243134235633835365985 

noncomputable def Ns60p171 := nat_lit 1292103228695953560462358870394653306976145612211295708974602438232360181766872544942489600 

noncomputable def Ns60p172 := BSN.cos_dyadic_bound_t 7973847 4194304 4 3 4194304 1092233 Ns60p167 Ns60p168 Ns60p169 Ns60p170 Ns60p171 Ns60p169 1360393 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 7973847) (BSN.cosEvenQ 4194304) 0 3 Ns60p167 Ns60p168 Ns60p169 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 7973847) (BSN.cosOddQ 4194304) 0 3 Ns60p170 Ns60p171 Ns60p169 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz347 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns60p173 := @Ns60p156 269432295 9162314481664 1360393 4194304 269432295 9162314481664 (@Ns60p157 239 8388608 Bool.true 1360393 4194304 1 1092233 (@Ns60p161 Ns60p162 7973847 4194304 239 8388608 (@Ns60p163 70368744177664 317216151 70368744177664 Ns60p158 Ns60p159 Ns60p160 Ns60p162 RS061to078.d31 (@Ns60p164 0 1 340665317086576 21291582317911 70368744177664 317216151 70368744177664 (@Ns60p165 141713249617267654656 16893535806807 70368744177664 317216151 70368744177664 (@Ns60p166 141055383 70368744177664 (Ns60p147 rfl rfl) (Ns60p147 rfl rfl) rfl) (Ns60p147 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7973847 4194304) (BSN.cos_neg_of_bound 7973847 4194304 Bool.true 1360393 4194304 1 1092233 (Ns60p172 rfl rfl)) rfl rfl) 

noncomputable abbrev qz932 := (Enclosure.sfrac Bool.false 1 1)

noncomputable abbrev qz661 := qz932

noncomputable abbrev qz348 := qz661

noncomputable abbrev qz933 := (Enclosure.Real.IsNear.const Bool.false 1 1)

noncomputable abbrev qz349 := qz933

noncomputable abbrev qz25 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 6) qz348 Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 6 rfl) qz349)

noncomputable def Ns60p174 := @Ns60p131 2859597304046158417377 Ns60p62 (Ns60p132 qz25 (@Enclosure.Real.IsNear.of_eq qz928 (@Inv.inv Real Real.instInv qz17) Bool.false 828949 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz7 (BSN.t_div_two_pi_nonneg qz4 257388 1000 qz10)) Ns60p136) rfl) (@Ns60p137 17592186044416 1715554238542929 38429532279701241856 (BSN.correction_mk qz9 (BSN.cos_two_pi_p_ne_zero_mk qz4 257388 1000 6 qz10 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 257388 1000 6 qz10 rfl rfl rfl))) (@Ns60p138 1048576 1360393 4194304 269432295 9162314481664 7041376482891 17592186044416 1715554238542929 38429532279701241856 Ns60p155 (Ns60p173 rfl) rfl)) 

noncomputable def Ns60p175 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 95660825344671766055 36893488147419103232 224276151225079826025953 Ns60p62 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 6) (@HMul.hMul Real Real Real qz5 qz922 (Zeta.RiemannSiegel.correction qz9))) Bool.true 95660825344671766055 36893488147419103232 224276151225079826025953 Ns60p62 (BSN.hardyZApproximantRS₀_eq qz4 6 (@BSN.floor_sqrt_eq_dec qz4 257388 1000 6 qz10 rfl rfl rfl)) (@Ns60p64 95660825344671766055 36893488147419103232 224276151225079826025953 Ns60p62 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 6) (@HAdd.hAdd Real Real Real qz336 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 6)) Bool.true 40847173 16777216 46093 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 6) (Ns60p130 (Ns60p129 rfl rfl rfl rfl) rfl rfl)) (Ns60p174 rfl) rfl rfl)) 

theorem RS061to078.d33 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 95660825344671766055 36893488147419103232 224276151225079826025953 Ns60p62 := Ns60p175 

theorem RS061to078.d34 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS061to078.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS061to078.d3 a b h)) 

noncomputable def Ns60p176 := nat_lit 10074071309930002345099264 

noncomputable def Ns60p177 := nat_lit 122859491252471637164949504 

noncomputable abbrev qz934 := (Enclosure.sfrac Bool.false 259079 1000)

noncomputable abbrev qz662 := qz934

noncomputable abbrev qz350 := qz662

noncomputable abbrev qz26 := qz350

noncomputable abbrev qz935 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 259079 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz663 := qz935

noncomputable abbrev qz351 := qz663

noncomputable abbrev qz27 := qz351

noncomputable abbrev qz936 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 259079 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz664 := qz936

noncomputable abbrev qz352 := qz664

noncomputable abbrev qz28 := (Zeta.RiemannSiegel.correction qz352)

noncomputable abbrev qz665 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz326 qz27 qz8))

noncomputable def Ns60p178 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz26) qz26 6) (@HMul.hMul Real Real Real qz5 qz665 qz28) 3981567 4194304 46395 33554432 5730248372598504885 36893488147419103232 166319294129303990991 Ns60p176 Ns60p177 

noncomputable def Ns60p179 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz26) qz26 Real.sin BSN.quadSignPos 5 6 259079 1000 71 67108864 33554432 1125899906842624 Bool.false 23612820206 1031 120242927 63 27397080 8 

noncomputable def Ns60p180 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz26) qz26 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 259079 1000 4 41 67108864 33554432 1125899906842624 Bool.false 23612820206 1031 

noncomputable def Ns60p181 := Ns60p180 93032624 62 33554424 8 108007536 62 30011992 8 Bool.false 13736020 23088 Bool.true 68321559 Bool.true 47675573 3537118876014220 1 Bool.false 35232761 Bool.false Bool.false 43765266 Bool.true Bool.false 11779977 

noncomputable def Ns60p182 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz26) qz26 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 259079 1000 109 42 67108864 33554432 1125899906842624 Bool.false 23612820206 1031 

noncomputable def Ns60p183 := Ns60p182 46516304 62 47453136 16 73726608 62 38745320 8 Bool.false 67108856 1102 Bool.false 71257761 Bool.false 84401335 3537118876014220 1 Bool.false 58602508 Bool.true Bool.false 20671337 Bool.true Bool.false 13736020 

noncomputable def Ns60p184 := nat_lit 8625780010696668646886520856551288377621371315740593503 

noncomputable def Ns60p185 := nat_lit 24514915735651859135614452096472349768553477439488000 

noncomputable def Ns60p186 := nat_lit 1118446592000000000000000000 

noncomputable def Ns60p187 := nat_lit 560281645652955746022392671520000 

noncomputable def Ns60p188 := nat_lit 870944764686920050266907796884380480 

noncomputable abbrev qz29 := (@Eq.refl Real qz350)

noncomputable def Ns60p189 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz26 259079 1000 268488712964 16000000 518158 4000 2000 Ns60p187 Ns60p188 qz29 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns60p190 := nat_lit 2760249603422933967003686674096412280838838821036989920960 

noncomputable abbrev qz937 := (Real.log (Enclosure.sfrac Bool.false 268488712964 16000000))

noncomputable abbrev qz938 := (@HSub.hSub Real Real Real qz11 qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 518158))))

noncomputable abbrev qz666 := (@HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 259079 4000) qz937) (@HMul.hMul Real Real Real qz5 qz12 qz938))

noncomputable abbrev qz939 := (Enclosure.sfrac Bool.false 259079 2000)

noncomputable abbrev qz353 := (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 qz666 qz939) (@HMul.hMul Real Real Real qz5 qz939 (Real.log Real.pi)))

noncomputable def Ns60p191 := @Enclosure.Real.IsNear.addLit_ft_p qz353 (Enclosure.sfrac Bool.true Ns60p187 Ns60p188) 3169264874086002945127 9007199254740992000 17182229496712249376563 Ns60p186 Ns60p187 Ns60p188 0 1 Ns60p190 

noncomputable def Ns60p192 := nat_lit 2184466000000000000000000 

noncomputable def Ns60p193 := nat_lit 212685765415014695948127305728000 

noncomputable abbrev qz354 := (@HSub.hSub Real Real Real qz11 qz666 qz939)

noncomputable def Ns60p194 := @Enclosure.Real.IsNear.subLit_ff_p qz354 (@HMul.hMul Real Real Real qz5 qz939 (Real.log Real.pi)) 4504922064778995526759 9007199254740992000 16692439481095492099 Ns60p192 9951421549119 67108864000 259079 33554432000 Ns60p193 3169264874086002945127 9007199254740992000 

noncomputable def Ns60p195 := nat_lit 9009844129557991053518000 

noncomputable abbrev qz355 := qz666

noncomputable def Ns60p196 := @Enclosure.Real.IsNear.subLit_ff_p qz355 qz939 5671710152638516259943 9007199254740992000 16692439481095492099 Ns60p192 259079 2000 0 1 Ns60p195 4504922064778995526759 9007199254740992000 16692439481095492099 Ns60p192 

noncomputable def Ns60p197 := nat_lit 12771555864988140409412344780752420864 

noncomputable def Ns60p198 := nat_lit 11760400671404679762018304 

noncomputable def Ns60p199 := BSN.log_dyadic_bound 6344712964 530632712964 2 1 844713228202604440995888 33554432 8737864 40255382595549665296 40255382595549665296 802451 536977425928 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 6344712964) (BSN.artanhQ 530632712964) 0 1 40255382595549665296 844713228202604440995888 40255382595549665296 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz667 := qz937

noncomputable def Ns60p200 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 259079 4000) qz667 259079 4000 0 1 21905453263604417 2251799813685248 62500007645631 546116500000000000000 5675242926081368751943 9007199254740992000 16192439480822433849 Ns60p192 (Enclosure.Real.IsNear.const Bool.false 259079 4000) (BSN.isNear_log_sfrac 268488712964 16000000 21905453263604417 2251799813685248 62500007645631 546116500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 268488712964) qz650)) Bool.false Ns60p198 Ns60p84 1000000122330096 8737864000000000000000 21905453263604417 2251799813685248 62500007645631 546116500000000000000 (BSN.log_rat_reduce_isNear 268488712964 16000000 14 536977425928 524288000000 802451 33554432 24973259072661432 36028797018963968 8737864 1000000000000000 rfl rfl rfl rfl (Ns60p199 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p201 := BSN.arctan_dyadic_bound_f 1000 518158 1 0 4194304 1092233 0 1 1 0 1 1 8094 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 518158) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 518158) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz940 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 518158)))

noncomputable abbrev qz668 := qz940

noncomputable abbrev qz356 := qz668

noncomputable def Ns60p202 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz356 884279719003555 562949953421312 1 2000000000000000 8094 4194304 1 1092233 3704381445612494651392 883193360713123 562949953421312 2000000001092233 2184466000000000000000 qz15 (Ns60p201 rfl) rfl rfl 

noncomputable abbrev qz669 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 259079 4000) qz937)

noncomputable abbrev qz357 := qz669

noncomputable abbrev qz670 := (@HMul.hMul Real Real Real qz5 qz12 qz938)

noncomputable abbrev qz358 := qz670

noncomputable abbrev qz671 := qz938

noncomputable abbrev qz359 := qz671

noncomputable def Ns60p203 := @Enclosure.Real.IsNear.subLit_ff_p qz357 qz358 5675242926081368751943 9007199254740992000 16192439480822433849 Ns60p192 883193360713123 2251799813685248 2000000001092233 8737864000000000000000 Ns60p197 5671710152638516259943 9007199254740992000 16692439481095492099 Ns60p192 (Ns60p200 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz12 qz359 1 4 0 1 883193360713123 562949953421312 2000000001092233 2184466000000000000000 883193360713123 2251799813685248 2000000001092233 8737864000000000000000 qz335 Ns60p202 rfl) 

noncomputable def Ns60p204 := @Ns60p191 Ns60p184 Ns60p185 17182229496712249376563 Ns60p186 (@Ns60p194 17182229496712249376563 Ns60p186 (Ns60p196 (Ns60p203 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 259079 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz939 (Real.log Real.pi) 259079 2000 0 1 38410761 33554432 1 16777216 9951421549119 67108864000 259079 33554432000 (Enclosure.Real.IsNear.const Bool.false 259079 2000) RS061to078.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns60p187 Ns60p188) 

noncomputable def Ns60p205 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz26) Bool.false Ns60p184 Ns60p185 17182229496712249376563 Ns60p186 2951602525 8388608 65 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz26) (@HAdd.hAdd Real Real Real qz336 qz353 (Enclosure.sfrac Bool.true Ns60p187 Ns60p188)) Bool.false Ns60p184 Ns60p185 17182229496712249376563 Ns60p186 Ns60p189 (Ns60p204 rfl rfl)) 

noncomputable def Ns60p206 := nat_lit 1899052205094348081070080 

noncomputable def Ns60p207 := nat_lit 140011340540875852264031978483693142750366031857704594089116913505142206035350061608385 

noncomputable def Ns60p208 := nat_lit 281356417283860013195258269978474418975042487219353622543838202800255158747313237441 

noncomputable def Ns60p209 := nat_lit 366240838645739077813005715972564510524999062267061650082616178280362507454611654208961 

noncomputable def Ns60p210 := BSN.sin_dyadic_bound_f 26987154983 17179869184 3 2 8388608 2186600 Ns60p207 Ns60p94 Ns60p208 Ns60p209 Ns60p97 Ns60p208 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26987154983) qz655 0 2 Ns60p207 Ns60p94 Ns60p208 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26987154983) qz656 0 2 Ns60p209 Ns60p97 Ns60p208 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p211 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz26) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2951602525) qz337) Bool.false 2951602525 8388608 65 4194304 Bool.false 8388607 8388608 1 1092233 (Ns60p205 rfl) (Enclosure.sfrac_false_div 2951602525 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2951602525) qz337) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns60p206) qz657) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 55 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q3 2951602525 8388608 226375608064910080 72057594037927936 55 Ns60p206 Ns60p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns60p206 Ns60p84 26987154983 17179869184 2186600 2184466 (Ns60p210 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p212 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz26) Bool.false Ns60p184 Ns60p185 17182229496712249376563 Ns60p186 23612820206 67108864 1031 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz26) (@HAdd.hAdd Real Real Real qz336 qz353 (Enclosure.sfrac Bool.true Ns60p187 Ns60p188)) Bool.false Ns60p184 Ns60p185 17182229496712249376563 Ns60p186 Ns60p189 (Ns60p204 rfl rfl)) 

noncomputable def Ns60p213 := Ns60p183 23088 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 109 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 58602508 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 42 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 20671337 67108864) qz29 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz26) qz26 1) Bool.false 8388607 8388608 75189449 4581157240832 67108856 67108864 1102 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz26) qz26 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz26)) Bool.false 8388607 8388608 75189449 4581157240832 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz26) qz26) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz26)) Bool.false 8388607 8388608 75189449 4581157240832 8388607 8388608 75189449 4581157240832 (Ns60p211 rfl rfl) rfl)) rfl) (Ns60p212 rfl) RS061to078.d7 

noncomputable def Ns60p214 := nat_lit 1582022110214214189588021299233313194637926541281699798280959649025 

noncomputable def Ns60p215 := nat_lit 664748517747682927128368185110890888153163198704744750413210881 

noncomputable def Ns60p216 := nat_lit 4142314981532302819419943187597069305470892962939882265901844358401 

noncomputable def Ns60p217 := BSN.sin_dyadic_bound_f 71257761 67108864 3 2 67108864 33554432 Ns60p214 Ns60p119 Ns60p215 Ns60p216 Ns60p122 Ns60p215 58602508 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 71257761) qz339 0 2 Ns60p214 Ns60p119 Ns60p215 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 71257761) (BSN.sinOddQ 67108864) 0 2 Ns60p216 Ns60p122 Ns60p215 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p218 := nat_lit 417261691049558138454165197869857972267727976217400159248316413731598321496833283354743492927624390625 

noncomputable def Ns60p219 := nat_lit 3996645342911614855169325114413848961633120431781532997847909552396155328908156533147964360867027353600 

noncomputable def Ns60p220 := nat_lit 130674784474552576710668079012819609053532807255490964684396302552005354722509703121035400390625 

noncomputable def Ns60p221 := nat_lit 2528877417614391316316967613972708567687795593934748524287784123137501227264367451428717633403425990625 

noncomputable def Ns60p222 := nat_lit 363694726204956951820408585411660255508613959292119502804159769268050134930642244516464756838899489177600 

noncomputable def Ns60p223 := BSN.cos_dyadic_bound_f 84401335 67108864 4 3 67108864 33554432 Ns60p218 Ns60p219 Ns60p220 Ns60p221 Ns60p222 Ns60p220 20671337 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 84401335) qz338 0 3 Ns60p218 Ns60p219 Ns60p220 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 84401335) (BSN.cosOddQ 67108864) 0 3 Ns60p221 Ns60p222 Ns60p220 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p224 := nat_lit 742912250647315831039113172032116673843767950352546900355589736001 

noncomputable def Ns60p225 := nat_lit 474746905035065674420569110681503018295135273539263033591072321 

noncomputable def Ns60p226 := nat_lit 2227787258131877361768498377874987015494713580510562174999587063361 

noncomputable def Ns60p227 := BSN.cos_dyadic_bound_f 68321559 67108864 3 2 67108864 33554432 Ns60p224 Ns60p103 Ns60p225 Ns60p226 Ns60p106 Ns60p225 35232761 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 68321559) qz338 0 2 Ns60p224 Ns60p103 Ns60p225 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 68321559) (BSN.cosOddQ 67108864) 0 2 Ns60p226 Ns60p106 Ns60p225 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p228 := nat_lit 316899535014786996693777678304098080326977183996528420545462454625 

noncomputable def Ns60p229 := nat_lit 26691155248047468392205568979537568172729125967367901387082081 

noncomputable def Ns60p230 := nat_lit 829931758406421485915830348446670959079327253786960601016822581601 

noncomputable def Ns60p231 := BSN.sin_dyadic_bound_f 47675573 67108864 3 2 67108864 33554432 Ns60p228 Ns60p119 Ns60p229 Ns60p230 Ns60p122 Ns60p229 43765266 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 47675573) qz339 0 2 Ns60p228 Ns60p119 Ns60p229 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 47675573) (BSN.sinOddQ 67108864) 0 2 Ns60p230 Ns60p122 Ns60p229 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p232 := Ns60p181 39300 BSN.abs_quadSignPos (BSN.cos_quad_nat0 4 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 35232761 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 41 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 43765266 67108864) qz29 rfl rfl (Ns60p213 RS061to078.d9 RS061to078.d11 RS061to078.d13 RS061to078.d17 (Ns60p217 rfl rfl) (Ns60p223 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns60p212 rfl) RS061to078.d19 RS061to078.d21 RS061to078.d23 RS061to078.d25 RS061to078.d17 (Ns60p227 rfl rfl) (Ns60p231 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns60p233 := nat_lit 568620037055310907344852953201397860181194577762826032265865724160 

noncomputable def Ns60p234 := nat_lit 85923188736148359214567517405788322352878449454189106018386176 

noncomputable def Ns60p235 := nat_lit 1489103840458336707607315101451670738428843043317809016429428080896 

noncomputable def Ns60p236 := BSN.sin_dyadic_bound_f 55177726 67108864 3 2 67108864 33554432 Ns60p233 Ns60p119 Ns60p234 Ns60p235 Ns60p122 Ns60p234 49167526 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 55177726) qz339 0 2 Ns60p233 Ns60p119 Ns60p234 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 55177726) (BSN.sinOddQ 67108864) 0 2 Ns60p235 Ns60p122 Ns60p234 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p237 := Ns60p179 Bool.false 11779977 39300 Bool.true 55177726 3537118876014220 1 Bool.false 49167526 Bool.false Bool.false 31852536 46395 BSN.abs_quadSignPos qz927 (BSN.sfrac_eq_quadSignPos_mul Bool.false 49167526 67108864) qz29 rfl (Ns60p232 rfl rfl) (Ns60p212 rfl) RS061to078.d27 RS061to078.d29 RS061to078.d17 (Ns60p236 rfl rfl) rfl 

noncomputable def Ns60p238 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz26) qz26 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz26) qz26 6) 31852536 67108864 46395 67108864 31852536 67108864 46395 67108864 4275175012958208 3981567 4194304 46395 33554432 (Ns60p237 rfl rfl rfl rfl) 

noncomputable def Ns60p239 := @Enclosure.Real.IsNear.mulLit_ff qz665 qz28 827593 2097152 1 4194304 6923993282445 17592186044416 799300465191889 19214766139850620928 5730248372598504885 36893488147419103232 

noncomputable abbrev qz672 := (@HPow.hPow Real Real Real qz326 qz27 qz8)

noncomputable def Ns60p240 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz672 1 1 0 1 827593 2097152 1 4194304 827593 2097152 1 4194304 

noncomputable def Ns60p241 := @Enclosure.Real.IsNear.sqrt_image qz27 345893523031 8388608000 259079 8388608000 26933079 26933100 4194304 (@Enclosure.Real.IsNear.of_eq qz27 (@HMul.hMul Real Real Real qz5 qz26 qz3) Bool.false 345893523031 8388608000 259079 8388608000 (BSN.t_div_two_pi_mk qz26 259079 1000 qz29) (@Enclosure.Real.IsNear.mulLit_ff qz26 qz3 259079 1000 0 1 1335089 8388608 1 8388608 345893523031 8388608000 259079 8388608000 (Enclosure.Real.IsNear.const Bool.false 259079 1000) RS061to078.d32 rfl)) 

noncomputable abbrev qz941 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 259079 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz673 := qz941

noncomputable abbrev qz360 := qz673

noncomputable abbrev qz30 := qz360

noncomputable abbrev qz674 := (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 53866179 8388608 21 8388608 53866179 8388608 21 8388608 (Ns60p241 rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns60p242 := @Enclosure.Real.IsNear.sqrt_image qz30 53866179 8388608 21 8388608 10628523 10628529 4194304 qz674 rfl 

noncomputable def Ns60p243 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz30) 5314263 2097152 3 4194304 1655185 1655187 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz30) Bool.false 21257052 8388608 6 8388608 5314263 2097152 3 4194304 (Ns60p242 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns60p244 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz30)) Bool.false 3310372 8388608 2 8388608 827593 2097152 1 4194304 (Ns60p243 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz675 := (@HMul.hMul Real Real Real qz918 qz915 qz936)

noncomputable abbrev qz361 := (Real.cos qz675)

noncomputable abbrev qz31 := (@Inv.inv Real Real.instInv qz361)

noncomputable abbrev qz676 := (@HSub.hSub Real Real Real qz920 (@HMul.hMul Real Real Real qz918 qz936 qz936) qz936)

noncomputable abbrev qz362 := (@HMul.hMul Real Real Real qz644 qz642 (@HSub.hSub Real Real Real qz647 qz676 qz930))

noncomputable abbrev qz32 := (Real.cos qz362)

noncomputable def Ns60p245 := @Enclosure.Real.IsNear.of_eq qz28 (@HMul.hMul Real Real Real qz5 qz31 qz32) Bool.false 6923993282445 

noncomputable def Ns60p246 := @Enclosure.Real.IsNear.mulLit_tt qz31 qz32 4764315 4194304 91 

noncomputable abbrev qz33 := (@Neg.neg Real Real.instNeg qz361)

noncomputable abbrev qz34 := qz361

noncomputable abbrev qz942 := (@Inv.inv Real Real.instInv qz33)

noncomputable def Ns60p247 := @Enclosure.Real.IsNear.of_eq qz31 (@Neg.neg Real Real.instNeg qz942) Bool.true 4764315 4194304 91 4194304 (BSN.inv_eq_neg_inv_neg qz34) 

noncomputable def Ns60p248 := @Enclosure.Real.IsNear.recentre' qz942 Bool.false 9528630 8388608 182 8388608 4764315 4194304 

noncomputable def Ns60p249 := @Enclosure.Real.IsNear.recentre' qz34 Bool.true 7384980 8388608 153655597 9162314481664 1846245 2097152 153655597 9162314481664 

noncomputable abbrev qz363 := qz675

noncomputable abbrev qz35 := qz363

noncomputable def Ns60p250 := @Enclosure.Real.IsNear.cos_image qz35 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 22208113) qz337) Bool.false 22208113 8388608 133 8388608 Bool.true 7384980 8388608 1 

noncomputable def Ns60p251 := nat_lit 566707583620286344661944659 

noncomputable abbrev qz36 := qz352

noncomputable def Ns60p252 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz36 884279719003555 140737488355328 1 500000000000000 3534531 8388608 21 8388608 3125514079489354257705 1180591620717411303424 Ns60p251 

noncomputable def Ns60p253 := @Enclosure.Real.IsNear.subLit_ff_p qz30 qz1 53866179 8388608 21 8388608 6 1 0 1 3534531 3534531 8388608 21 

noncomputable def Ns60p254 := @Ns60p253 8388608 qz674 qz345 

noncomputable def Ns60p255 := @Enclosure.Real.IsNear.recentre' qz35 Bool.false 3125514079489354257705 1180591620717411303424 Ns60p251 Ns60p144 22208113 8388608 133 8388608 (@Ns60p252 Ns60p144 RS061to078.d31 (Ns60p254 rfl rfl) rfl) 

noncomputable def Ns60p256 := nat_lit 1301550144986690560720896 

noncomputable def Ns60p257 := nat_lit 30844555980325830323618641796646293156062322744866059351417729693351569828952612225280 

noncomputable def Ns60p258 := nat_lit 13697737352367317525254796909223523291634745397050687318079059362351807821272269056 

noncomputable def Ns60p259 := nat_lit 80761183611806675190626982653363453513881531886863501950436211672191256148879543582976 

noncomputable def Ns60p260 := BSN.sin_dyadic_bound_f 18496140014 17179869184 3 2 8388608 2186600 Ns60p257 Ns60p94 Ns60p258 Ns60p259 Ns60p97 Ns60p258 7384980 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 18496140014) qz655 0 2 Ns60p257 Ns60p94 Ns60p258 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 18496140014) qz656 0 2 Ns60p259 Ns60p97 Ns60p258 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p261 := @Ns60p250 1092233 (Ns60p255 rfl) (Enclosure.sfrac_false_div 22208113 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 22208113) qz337) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns60p256) qz657) 226375608064910080 72057594037927936 Bool.false 7384980 8388608 0 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q1 22208113 8388608 226375608064910080 72057594037927936 0 Ns60p256 Ns60p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 7384980 8388608 Ns60p256 Ns60p84 18496140014 17179869184 2186600 2184466 (Ns60p260 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p262 := @Enclosure.Real.IsNear.inv_image qz33 1846245 2097152 153655597 9162314481664 4764224 4764406 4194304 (@Enclosure.Real.IsNear.neg qz34 Bool.true 1846245 2097152 153655597 9162314481664 (Ns60p249 (Ns60p261 rfl rfl) rfl)) 

noncomputable def Ns60p263 := Ns60p247 (@Enclosure.Real.IsNear.neg qz942 Bool.false 4764315 4194304 91 4194304 (@Ns60p248 91 4194304 (Ns60p262 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p264 := @Enclosure.Real.IsNear.recentre' qz32 Bool.true 1453303 4194304 

noncomputable abbrev qz37 := qz362

noncomputable def Ns60p265 := @Enclosure.Real.IsNear.cos_image qz37 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16144947)) qz337) Bool.true 16144947 8388608 

noncomputable def Ns60p266 := nat_lit 19060589339429056802300888005 

noncomputable def Ns60p267 := nat_lit 8759990714674886118006962154015809 

noncomputable def Ns60p268 := @Enclosure.Real.IsNear.recentre' qz37 Bool.true Ns60p266 Ns60p159 Ns60p267 

noncomputable abbrev qz364 := (@HSub.hSub Real Real Real qz647 qz676 qz930)

noncomputable abbrev qz38 := qz364

noncomputable def Ns60p269 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz38 884279719003555 140737488355328 1 500000000000000 21554932143991 

noncomputable abbrev qz365 := qz676

noncomputable abbrev qz39 := qz365

noncomputable def Ns60p270 := @Enclosure.Real.IsNear.subLit_tf qz39 qz23 17156885632887 70368744177664 324611511 70368744177664 1 16 

noncomputable abbrev qz677 := (@HMul.hMul Real Real Real qz918 qz936 qz936)

noncomputable abbrev qz366 := qz677

noncomputable abbrev qz40 := qz366

noncomputable def Ns60p271 := @Enclosure.Real.IsNear.subLit_ff_n qz40 qz36 12492909389961 70368744177664 148450743 70368744177664 3534531 8388608 21 8388608 

noncomputable def Ns60p272 := @Enclosure.Real.IsNear.mulLit_ff qz36 qz36 3534531 8388608 21 8388608 3534531 8388608 21 8388608 12492909389961 70368744177664 

noncomputable def Ns60p273 := nat_lit 33521858025536998736351785813330067338188452246953950111334770108322911867387539059858758321 

noncomputable def Ns60p274 := nat_lit 58158844227896986633558482781719779619497718984807332131428259197799420928759449934993817600 

noncomputable def Ns60p275 := nat_lit 313645805582196830838571932657624867949850828389717974815638659125978868155561573374641 

noncomputable def Ns60p276 := nat_lit 202266032044868701594305722898380677625051601399987107290542607031731588062208566705609005745 

noncomputable def Ns60p277 := nat_lit 5292454824738625783653821933136499945374292427617467223959971586999747304517109944084437401600 

noncomputable def Ns60p278 := BSN.cos_dyadic_bound_t 16144947 8388608 4 3 4194304 1092233 Ns60p273 Ns60p274 Ns60p275 Ns60p276 Ns60p277 Ns60p275 1453303 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16144947) (BSN.cosEvenQ 8388608) 0 3 Ns60p273 Ns60p274 Ns60p275 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16144947) (BSN.cosOddQ 8388608) 0 3 Ns60p276 Ns60p277 Ns60p275 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p279 := @Ns60p264 68723365 2290578620416 1453303 4194304 68723365 2290578620416 (@Ns60p265 61 2097152 Bool.true 1453303 4194304 1 1092233 (@Ns60p268 Ns60p162 16144947 8388608 61 2097152 (@Ns60p269 70368744177664 324611511 70368744177664 Ns60p266 Ns60p159 Ns60p267 Ns60p162 RS061to078.d31 (@Ns60p270 0 1 344878914303856 21554932143991 70368744177664 324611511 70368744177664 (@Ns60p271 143922388075120951296 17156885632887 70368744177664 324611511 70368744177664 (@Ns60p272 148450743 70368744177664 (Ns60p254 rfl rfl) (Ns60p254 rfl rfl) rfl) (Ns60p254 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16144947 8388608) (BSN.cos_neg_of_bound 16144947 8388608 Bool.true 1453303 4194304 1 1092233 (Ns60p278 rfl rfl)) rfl rfl) 

noncomputable abbrev qz943 := (@BSN.floor_sqrt_eq_dec qz26 259079 1000 6 qz29 rfl rfl rfl)

noncomputable abbrev qz367 := (BSN.cos_two_pi_p_ne_zero_mk qz26 259079 1000 6 qz29 rfl rfl qz943)

noncomputable def Ns60p280 := @Ns60p239 166319294129303990991 Ns60p176 (Ns60p240 qz25 (@Enclosure.Real.IsNear.of_eq qz672 (@Inv.inv Real Real.instInv (Real.sqrt qz30)) Bool.false 827593 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz27 (BSN.t_div_two_pi_nonneg qz26 259079 1000 qz29)) Ns60p244) rfl) (@Ns60p245 17592186044416 799300465191889 19214766139850620928 (BSN.correction_mk qz36 qz367) (@Ns60p246 4194304 1453303 4194304 68723365 2290578620416 6923993282445 17592186044416 799300465191889 19214766139850620928 Ns60p263 (Ns60p279 rfl) rfl)) 

noncomputable def Ns60p281 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz26) (hardyZApproximantRS₀ qz26) Bool.false 29291985333555135051 36893488147419103232 14095523591916328334031 Ns60p176 (@Eq.refl Real (hardyZApproximantRS₀ qz26)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz26) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz26) qz26 6) (@HMul.hMul Real Real Real qz5 qz665 qz28)) Bool.false 29291985333555135051 36893488147419103232 14095523591916328334031 Ns60p176 (BSN.hardyZApproximantRS₀_eq qz26 6 qz943) (@Ns60p178 29291985333555135051 36893488147419103232 14095523591916328334031 Ns60p176 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz26) qz26 6) (@HAdd.hAdd Real Real Real qz336 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz26) qz26 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz26) qz26 6)) Bool.false 3981567 4194304 46395 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz26) qz26 6) (Ns60p238 (Ns60p237 rfl rfl rfl rfl) rfl rfl)) (Ns60p280 rfl) rfl rfl)) 

theorem RS061to078.d35 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz26) Bool.false 29291985333555135051 36893488147419103232 14095523591916328334031 Ns60p176 := Ns60p281 

noncomputable abbrev qz944 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Real.sqrt (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 257388 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))) (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 257388 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz678 := qz944

noncomputable abbrev qz368 := qz678

noncomputable abbrev qz679 := (@HMul.hMul Real Real Real qz918 qz944 qz944)

noncomputable abbrev qz369 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz644 qz679 qz678))

noncomputable abbrev qz41 := (@HAdd.hAdd Real Real Real qz336 (@HMul.hMul Real Real Real qz323 (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz368)) (@HMul.hMul Real Real Real qz323 (Enclosure.sfrac Bool.false 1 32) qz369))

noncomputable abbrev qz680 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz17 qz17) qz17))

noncomputable def Ns60p282 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz336 qz41 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz680)) Bool.false 

noncomputable def Ns60p283 := @Enclosure.Real.IsNear.addLit_ff qz41 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz680) 16188607 268435456 

noncomputable abbrev qz42 := qz368

noncomputable abbrev qz43 := (@HMul.hMul Real Real Real qz323 (Enclosure.sfrac Bool.false 1 32) qz369)

noncomputable def Ns60p284 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz42)) qz43 2023575 33554432 25 33554432 

noncomputable def Ns60p285 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv qz42) 25 4 0 1 80943 8388608 1 8388608 2023575 

noncomputable def Ns60p286 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz42) Bool.false 80943 8388608 1 8388608 80943 8388608 1 8388608 

noncomputable def Ns60p287 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz7 21222281 8388608 5 8388608 85908971883 2097152000 64347 2097152000 1823184341722125123 17592186044416000 1795135296657 

noncomputable def Ns60p288 := @Enclosure.Real.IsNear.sqrt_image qz7 85908971883 2097152000 64347 2097152000 26845039 26845060 4194304 qz340 

noncomputable def Ns60p289 := @Enclosure.Real.IsNear.sqrt_image qz16 53690099 8388608 21 8388608 10611138 10611143 4194304 (@Enclosure.Real.IsNear.recentre' qz16 Bool.false 53690099 8388608 21 8388608 53690099 8388608 21 8388608 (Ns60p288 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz681 := (@Enclosure.Real.IsNear.recentre' qz17 Bool.false 21222281 8388608 5 8388608 21222281 8388608 5 8388608 (Ns60p289 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns60p290 := @Ns60p287 17592186044416000 qz681 

noncomputable def Ns60p291 := Ns60p290 qz340 

noncomputable def Ns60p292 := @Enclosure.Real.IsNear.inv_image qz42 1823184341722125123 17592186044416000 1795135296657 17592186044416000 40471 40472 4194304 (Ns60p291 rfl) rfl rfl 

noncomputable abbrev qz44 := qz369

noncomputable def Ns60p293 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz44 1 32 0 1 7 

noncomputable def Ns60p294 := @Enclosure.Real.IsNear.recentre' qz44 Bool.false 7 8388608 1 8388608 

noncomputable def Ns60p295 := nat_lit 6060266837426259217525969962824389954542077132714235867 

noncomputable def Ns60p296 := nat_lit 5444517870735015415413993718908291383296000000000 

noncomputable def Ns60p297 := nat_lit 17901112964332494631081301569090668829197509516133 

noncomputable abbrev qz370 := (@HMul.hMul Real Real Real qz644 qz679 qz678)

noncomputable abbrev qz45 := qz370

noncomputable def Ns60p298 := @Enclosure.Real.IsNear.inv_image qz45 Ns60p295 Ns60p296 Ns60p297 Ns60p296 3 4 

noncomputable def Ns60p299 := nat_lit 3324001143900738714514062579267765129 

noncomputable def Ns60p300 := nat_lit 309485009821345068724781056000000 

noncomputable def Ns60p301 := nat_lit 6545728350786221993689550603271 

noncomputable abbrev qz371 := qz679

noncomputable abbrev qz46 := qz371

noncomputable def Ns60p302 := @Enclosure.Real.IsNear.mulLit_ff qz46 qz42 Ns60p299 Ns60p300 Ns60p301 Ns60p300 1823184341722125123 17592186044416000 1795135296657 

noncomputable def Ns60p303 := @Enclosure.Real.IsNear.mulLit_ff qz42 qz42 1823184341722125123 17592186044416000 1795135296657 17592186044416000 1823184341722125123 17592186044416000 1795135296657 17592186044416000 Ns60p299 

noncomputable def Ns60p304 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz680 13 10 0 1 32379 524288 1 

noncomputable def Ns60p305 := @Enclosure.Real.IsNear.recentre' qz680 Bool.false 518064 8388608 2 8388608 32379 524288 

noncomputable def Ns60p306 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz17 qz17) qz17 450385210842961 70368744177664 212222835 70368744177664 21222281 8388608 5 8388608 9558201502753565214041 

noncomputable def Ns60p307 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz17 21222281 8388608 5 8388608 21222281 8388608 5 8388608 450385210842961 70368744177664 212222835 

noncomputable def Ns60p308 := @Ns60p307 70368744177664 qz681 

noncomputable def Ns60p309 := Ns60p308 qz681 

noncomputable def Ns60p310 := @Ns60p306 590295810358705651712 6755779754315615 590295810358705651712 (Ns60p309 rfl) qz681 

noncomputable abbrev qz682 := (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz17 qz17) qz17)

noncomputable def Ns60p311 := @Enclosure.Real.IsNear.inv_image qz682 9558201502753565214041 590295810358705651712 6755779754315615 590295810358705651712 259031 259033 4194304 (Ns60p310 rfl) 

noncomputable def Ns60p312 := @Ns60p283 201 268435456 420927 5242880 13 41943040 197866655055872 188700347 1342177280 1421 1342177280 (@Ns60p284 7 268435456 1 268435456 543199512756224 16188607 268435456 201 268435456 (@Ns60p285 33554432 25 33554432 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns60p286 (Ns60p292 rfl rfl rfl rfl) rfl) rfl) (@Ns60p293 8388608 1 8388608 7 268435456 1 268435456 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns60p294 7 8388608 1 8388608 (@Ns60p298 4194304 (@Ns60p302 17592186044416000 Ns60p295 Ns60p296 Ns60p297 Ns60p296 (@Ns60p303 Ns60p300 Ns60p301 Ns60p300 (Ns60p291 rfl) (Ns60p291 rfl) rfl) (Ns60p291 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns60p304 4194304 420927 5242880 13 41943040 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns60p305 1 4194304 (Ns60p311 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS061to078.d36 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 := @Ns60p282 188700347 1342177280 1421 1342177280 (BSN.hardyZErrorBoundRS₀_mk qz4 257388 1000 qz10 rfl rfl) (Ns60p312 rfl rfl) 

theorem RS061to078.d37 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal (RS061to078.d3 a b h)) (hardyZApproximantRS a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal (RS061to078.d3 a b h)) 

theorem RS061to078.d38 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

theorem RS061to078.d39 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 qz321 RS061to078.d38 rfl 

theorem RS061to078.d40 : Enclosure.Real.IsNear qz3 Bool.false 21361415 134217728 1 134217728 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 21361415 134217728 1 134217728 21361415 134217728 1 134217728 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 10680707 10680708 67108864 RS061to078.d39 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz372 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 4 1) Real.pi)

theorem RS061to078.d41 : Enclosure.Real.IsNear qz372 Bool.false 884279719003555 70368744177664 1 250000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz318 Real.pi 4 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 70368744177664 1 250000000000000 (Enclosure.Real.IsNear.const Bool.false 4 1) RS061to078.d38 rfl 

noncomputable def Ns60p313 := nat_lit 781950621441006189802102638025 

noncomputable def Ns60p314 := nat_lit 79228162514264337593543950336 

noncomputable def Ns60p315 := nat_lit 26986075409044041160201671 

noncomputable def Ns60p316 := nat_lit 4294967296000000000000000000000000000000 

theorem RS061to078.d42 : Enclosure.Real.IsNear RSCompact.c2 Bool.false Ns60p313 Ns60p314 Ns60p315 Ns60p316 := @Enclosure.Real.IsNear.mulLit_ff Real.pi Real.pi 226375608064910080 72057594037927936 1 1000000000000000 226375608064910080 72057594037927936 1 1000000000000000 Ns60p313 Ns60p314 Ns60p315 Ns60p316 RS061to078.d38 RS061to078.d38 rfl 

noncomputable def Ns60p317 := nat_lit 19807040628566084398385987584 

noncomputable def Ns60p318 := nat_lit 1073741824000000000000000000000000000000 

noncomputable abbrev qz683 := (@HMul.hMul Real Real Real qz323 qz318 RSCompact.c2)

noncomputable abbrev qz47 := qz683

theorem RS061to078.d43 : Enclosure.Real.IsNear qz47 Bool.false Ns60p313 Ns60p317 Ns60p315 Ns60p318 := @Enclosure.Real.IsNear.mulLit_ff qz318 RSCompact.c2 4 1 0 1 Ns60p313 Ns60p314 Ns60p315 Ns60p316 Ns60p313 Ns60p317 Ns60p315 Ns60p318 (Enclosure.Real.IsNear.const Bool.false 4 1) RS061to078.d42 rfl 

noncomputable def Ns60p319 := nat_lit 691463075802508163054686763366652189853178875 

noncomputable def Ns60p320 := nat_lit 2787593149816327892691964784081045188247552 

noncomputable def Ns60p321 := nat_lit 2184744797947834540264818678394244808492865883128339 

noncomputable def Ns60p322 := nat_lit 9223372036854775808000000000000000000000000000000000000000000000 

noncomputable def Ns60p323 := nat_lit 22300745198530623141535718272648361505980416 

noncomputable def Ns60p324 := nat_lit 73786976294838206464000000000000000000000000000000000000000000000 

noncomputable abbrev qz684 := (Enclosure.sfrac Bool.false 8 1)

noncomputable def Ns60p325 := @Enclosure.Real.IsNear.mulLit_ff qz684 (@HMul.hMul Real Real Real qz5 RSCompact.c2 Real.pi) 8 1 0 1 Ns60p319 Ns60p323 Ns60p321 Ns60p324 Ns60p319 Ns60p320 Ns60p321 Ns60p322 (Enclosure.Real.IsNear.const Bool.false 8 1) (@Enclosure.Real.IsNear.mulLit_ff RSCompact.c2 Real.pi Ns60p313 Ns60p314 Ns60p315 Ns60p316 226375608064910080 72057594037927936 1 1000000000000000 Ns60p319 Ns60p323 Ns60p321 Ns60p324 RS061to078.d42 RS061to078.d38 rfl) rfl 

noncomputable abbrev qz685 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 8 1) RSCompact.c10)

theorem RS061to078.d44 : Enclosure.Real.IsNear qz685 Bool.false Ns60p319 Ns60p320 Ns60p321 Ns60p322 := Ns60p325 

noncomputable def Ns60p326 := nat_lit 2345851864323018569406307914075 

noncomputable def Ns60p327 := nat_lit 2475880078570760549798248448 

noncomputable def Ns60p328 := nat_lit 80958226227132123480605013 

noncomputable def Ns60p329 := nat_lit 134217728000000000000000000000000000000 

noncomputable abbrev qz373 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 96 1) RSCompact.c2)

noncomputable def Ns60p330 := @Enclosure.Real.IsNear.inv_image qz373 Ns60p326 Ns60p327 Ns60p328 Ns60p329 70828 70829 67108864 (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 1) RSCompact.c2 96 1 0 1 Ns60p313 Ns60p314 Ns60p315 Ns60p316 Ns60p326 Ns60p327 Ns60p328 Ns60p329 (Enclosure.Real.IsNear.const Bool.false 96 1) RS061to078.d42 rfl) rfl rfl 

noncomputable abbrev qz374 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 96 1) RSCompact.c2))

theorem RS061to078.d45 : Enclosure.Real.IsNear qz374 Bool.false 141657 134217728 1 134217728 := @Enclosure.Real.IsNear.recentre' qz374 Bool.false 141657 134217728 1 134217728 141657 134217728 1 134217728 (Ns60p330 rfl rfl rfl rfl) rfl 

noncomputable def Ns60p331 := nat_lit 34385655512837632236814975778813654552693762720339673034595137517813344581012879108402349691118207252249141032236796373438419613 

noncomputable def Ns60p332 := nat_lit 43322963970637732180912721627235682866194329302747133987038743447103457934462900359999600095377180907771737671271930809827721216 

noncomputable def Ns60p333 := nat_lit 2087261912670520323719885412575674513224536466137363445098200949195661267142477605776362678186904725329260971254715034881280570742736951261639505782147722187303091190543859358631 

noncomputable def Ns60p334 := nat_lit 1491391506916068166207680141516730240672688644105268424692277679906774267981354299825772529667870190631942677424919895374338432014074511360000000000000000000000000000000000000000000 

noncomputable abbrev qz686 := (@HAdd.hAdd Real Real Real qz336 qz28 (@HMul.hMul Real Real Real qz5 (Zeta.RiemannSiegel.correctionLinear qz36) (@Inv.inv Real Real.instInv qz30)))

noncomputable def Ns60p335 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz26) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz26) qz26 6) (@HMul.hMul Real Real Real qz5 qz665 qz686)) Bool.false Ns60p331 Ns60p332 Ns60p333 Ns60p334 

noncomputable def Ns60p336 := nat_lit 6739948088541801253547220740844409365063452097411018862647382011160562340790034270709542950175946928137877706651268902395981155 

noncomputable def Ns60p337 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz26) qz26 6) (@HMul.hMul Real Real Real qz5 qz665 qz686) 3981567 4194304 46395 33554432 Ns60p336 Ns60p332 

noncomputable def Ns60p338 := nat_lit 25146572337208093275772391509822481635702250637487644381376925493671849977110814873249893743382108276199828120801799637351197916727351261639505782147722187303091190543859358631 

noncomputable def Ns60p339 := nat_lit 144223892460116932241402000168981226544981659752971571967694523671514582429520642895888408918855861150937581228074923976298257136484352 

noncomputable def Ns60p340 := nat_lit 8144037091350218348327282542076128441230716182242985214528617341085004755707254980056069771223230414150286078605388037835 

noncomputable def Ns60p341 := nat_lit 20657999024695268717247353376024094994637646342633788102645274852325180976134729557037162826241102651487225375781979947008 

noncomputable def Ns60p342 := nat_lit 30215792224530412587135500035944668480101911384931653929524504225455010822591529598764811543417864827262726481316101208496566331030802797948019925581223099195819944538351 

noncomputable def Ns60p343 := @Enclosure.Real.IsNear.mulLit_ff qz665 qz686 827593 2097152 1 4194304 Ns60p340 Ns60p341 Ns60p342 

noncomputable def Ns60p344 := nat_lit 711150887926134188751068182714810486160606691410669529291285362199198850622822904503713860353407950702639902794322917639893737799680000000000000000000000000000000000000000000 

noncomputable def Ns60p345 := nat_lit 13390558019192526012535303551358835053550664248974238054320532198498246284679400666505054709423711551189639538366889675 

noncomputable def Ns60p346 := nat_lit 633166477027924345253116186792601281403994456208864250487422995217656612196157607975851540451311122760522723406993647724818491030802797948019925581223099195819944538351 

noncomputable abbrev qz687 := (@HMul.hMul Real Real Real qz5 (Zeta.RiemannSiegel.correctionLinear qz36) (@Inv.inv Real Real.instInv qz30))

noncomputable def Ns60p347 := @Enclosure.Real.IsNear.addLit_ff qz28 qz687 6923993282445 17592186044416 799300465191889 19214766139850620928 Ns60p345 Ns60p341 Ns60p346 Ns60p344 

noncomputable def Ns60p348 := nat_lit 143271415663657583773797641514060659086874148836931983039741769875695913294918162388066107038506911925239866722935713431105272398479360 

noncomputable def Ns60p349 := nat_lit 20500532041183877076239669481137441311903843266987616073217886310989214757746169387206692646331892004191241843175 

noncomputable def Ns60p350 := nat_lit 4925250774549309901534880012517951725634967408808180833493536675530715221437151326426783281860614455100828498788352 

noncomputable def Ns60p351 := nat_lit 968276448119134572317916774093552211742400360475449600522603656268914308833805196270499637236881575945040643345857775573567844196715362653269162905880544206241243 

noncomputable def Ns60p352 := nat_lit 169551584226163432300345464400007840671683953144709951708623257207679474502282835126808610046722400355968452166157464418385920000000000000000000000000000000000000000000 

noncomputable abbrev qz688 := (Zeta.RiemannSiegel.correctionLinear qz36)

noncomputable def Ns60p353 := @Enclosure.Real.IsNear.mulLit_ff qz688 (@Inv.inv Real Real.instInv qz30) Ns60p349 Ns60p350 Ns60p351 Ns60p352 653181 4194304 1 4194304 Ns60p345 

noncomputable def Ns60p354 := nat_lit 144719512916296950212412160931951413003973282414477336617448388085228507999930602703761145911122584864787775 

noncomputable def Ns60p355 := nat_lit 36695977855841144185773134324833391052745039826692497979801421430190766017415756929120296849762010984873984 

noncomputable def Ns60p356 := nat_lit 319606663566850463602853400240237630887806152713087117935687266219293546149873622796879305331047692806752626213513892547089092405809402974746913236168921989437 

noncomputable def Ns60p357 := nat_lit 59373113949818024919303035935762289997705413384745774643907644515938574832732180140614544393092042332369962720642990080000000000000000000000000000000000000000000 

noncomputable def Ns60p358 := @Enclosure.Real.IsNear.mulLit_tf (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz36) qz374 Ns60p354 Ns60p355 Ns60p356 Ns60p357 141657 134217728 1 134217728 Ns60p349 

noncomputable abbrev qz945 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 259079 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 6 1)))

noncomputable abbrev qz689 := (@HMul.hMul Real Real Real qz918 qz915 (@HSub.hSub Real Real Real qz920 qz945 qz932))

noncomputable abbrev qz375 := (@HMul.hMul Real Real Real qz644 qz689 qz689)

noncomputable abbrev qz376 := qz689

noncomputable abbrev qz48 := (@HMul.hMul Real Real Real qz323 qz375 qz376)

noncomputable abbrev qz49 := (Real.sin qz362)

noncomputable abbrev qz50 := qz376

noncomputable abbrev qz946 := (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz317 qz50) qz372)

noncomputable def Ns60p359 := @HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 qz48 qz49) (@HMul.hMul Real Real Real qz5 qz946 qz32) 

noncomputable abbrev qz377 := (Real.sin qz675)

noncomputable abbrev qz51 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz323 qz320 qz377))

noncomputable abbrev qz52 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz323 qz683 qz361))

noncomputable abbrev qz53 := qz377

noncomputable abbrev qz690 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 8 1) RSCompact.c9)

noncomputable abbrev qz947 := (@HMul.hMul Real Real Real qz5 qz317 qz51)

noncomputable abbrev qz948 := (@HMul.hMul Real Real Real qz5 qz317 qz52)

noncomputable def Ns60p360 := @HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns60p359 (@HMul.hMul Real Real Real qz5 qz947 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz36))) (@HMul.hMul Real Real Real qz5 qz948 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz36))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz690 qz53) qz28) 

noncomputable def Ns60p361 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz36) (@HMul.hMul Real Real Real qz5 qz31 Ns60p360) Bool.true Ns60p354 Ns60p355 Ns60p356 Ns60p357 (BSN.iteratedDeriv_three_correction_mk qz36 qz367) 

noncomputable def Ns60p362 := nat_lit 949236818547956696344948842030171553185335383179781385915268168700995462990410273273102195474496825 

noncomputable def Ns60p363 := nat_lit 273406340597876490546562778389702670669146178861651554553221325801244124899921990402939147127881728 

noncomputable def Ns60p364 := nat_lit 10472508209288698854383813327209958332531978523301875955367325679430262312984405847862705000743655200796404454868505045779142769108332140235828703983319 

noncomputable def Ns60p365 := @Enclosure.Real.IsNear.mulLit_tf qz31 Ns60p360 152458807 134217728 183 134217728 Ns60p362 Ns60p363 Ns60p364 

noncomputable def Ns60p366 := nat_lit 2211820853867308233652376977196421101603858671514159986522333492187357501414871966116672172885091689689828556800000000000000000000000000000000000000000000 

noncomputable def Ns60p367 := @Enclosure.Real.IsNear.of_eq qz31 (@Neg.neg Real Real.instNeg qz942) Bool.true 152458807 134217728 183 134217728 (BSN.inv_eq_neg_inv_neg qz34) 

noncomputable def Ns60p368 := @Enclosure.Real.IsNear.recentre' qz942 Bool.false 152458807 134217728 183 134217728 152458807 134217728 

noncomputable def Ns60p369 := @Enclosure.Real.IsNear.recentre' qz34 Bool.true 118159120 134217728 2458489552 2345552507305984 7384945 8388608 153655597 146597031706624 

noncomputable abbrev qz949 := (@Nat.cast Real Real.instNatCast 134217728)

noncomputable abbrev qz691 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 355328611) qz949)

noncomputable def Ns60p370 := @Enclosure.Real.IsNear.cos_image qz35 qz691 Bool.false 355328611 134217728 133 134217728 Bool.true 118159120 134217728 1 

noncomputable def Ns60p371 := nat_lit 566707584075705555535382867 

noncomputable def Ns60p372 := nat_lit 576460752303423488000000000000000 

noncomputable def Ns60p373 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz36 884279719003555 140737488355328 1 500000000000000 56552305 134217728 21 134217728 50008056374403338444275 18889465931478580854784 Ns60p371 

noncomputable def Ns60p374 := @Enclosure.Real.IsNear.subLit_ff_p qz30 qz1 861858673 134217728 21 134217728 6 1 0 1 56552305 56552305 134217728 21 

noncomputable def Ns60p375 := @Enclosure.Real.IsNear.sqrt_image qz27 1106858807357 26843545600 259079 134217728000 430929326 430929347 67108864 (@Enclosure.Real.IsNear.of_eq qz27 (@HMul.hMul Real Real Real qz5 qz26 qz3) Bool.false 1106858807357 26843545600 259079 134217728000 (BSN.t_div_two_pi_mk qz26 259079 1000 qz29) (@Enclosure.Real.IsNear.mulLit_ff qz26 qz3 259079 1000 0 1 21361415 134217728 1 134217728 1106858807357 26843545600 259079 134217728000 (Enclosure.Real.IsNear.const Bool.false 259079 1000) RS061to078.d40 rfl)) 

noncomputable def Ns60p376 := @Ns60p374 134217728 (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 861858673 134217728 21 134217728 861858673 134217728 21 134217728 (Ns60p375 rfl rfl rfl rfl rfl rfl) rfl) qz345 

noncomputable def Ns60p377 := @Enclosure.Real.IsNear.recentre' qz35 Bool.false 50008056374403338444275 18889465931478580854784 Ns60p371 Ns60p372 355328611 134217728 133 134217728 (@Ns60p373 Ns60p372 RS061to078.d39 (Ns60p376 rfl rfl) rfl) 

noncomputable def Ns60p378 := nat_lit 20824629813906922172055552 

noncomputable def Ns60p379 := nat_lit 19342813113834066795298816 

noncomputable def Ns60p380 := nat_lit 132471967763226321841144896150286895881734321977246194887166859741490862156448000454995961373825 

noncomputable def Ns60p381 := nat_lit 11827193841476132975761497142559922353317709611095919146093482340187486176929913983037299836846080 

noncomputable def Ns60p382 := nat_lit 58827435377621295129934072681494778437184535548191749373028591302311951731539899465259738241 

noncomputable def Ns60p383 := nat_lit 346855147341648027487073882371171831001358258787614390443594967317986610106941317544902811640961 

noncomputable def Ns60p384 := nat_lit 216831887093729104555627447613598576477491342870091851011713842903437246577048423022350497008844800 

noncomputable def Ns60p385 := BSN.sin_dyadic_bound_f 295935788783 274877906944 3 2 134217728 34985589 Ns60p380 Ns60p381 Ns60p382 Ns60p383 Ns60p384 Ns60p382 118159120 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 295935788783) (BSN.sinEvenQ 274877906944) 0 2 Ns60p380 Ns60p381 Ns60p382 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 295935788783) (BSN.sinOddQ 274877906944) 0 2 Ns60p383 Ns60p384 Ns60p382 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz692 := (@Nat.cast Real Real.instNatCast Ns60p379)

noncomputable def Ns60p386 := @Ns60p370 17475728 (Ns60p377 rfl) (Enclosure.sfrac_false_div 355328611 134217728) (BSN.cos_reduce1 qz691 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns60p378) qz692) 226375608064910080 72057594037927936 Bool.false 118159120 134217728 0 1000000000000000 34951456 17475728 (BSN.sin_reduce_arg_pos_rat_q1 355328611 134217728 226375608064910080 72057594037927936 0 Ns60p378 Ns60p379 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 118159120 134217728 Ns60p378 Ns60p379 295935788783 274877906944 34985589 34951456 (Ns60p385 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p387 := @Enclosure.Real.IsNear.inv_image qz33 7384945 8388608 153655597 146597031706624 76229312 76229495 67108864 (@Enclosure.Real.IsNear.neg qz34 Bool.true 7384945 8388608 153655597 146597031706624 (Ns60p369 (Ns60p386 rfl rfl) rfl)) 

noncomputable def Ns60p388 := Ns60p367 (@Enclosure.Real.IsNear.neg qz942 Bool.false 152458807 134217728 183 134217728 (@Ns60p368 183 134217728 (Ns60p387 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p389 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns60p359 (@HMul.hMul Real Real Real qz5 qz947 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz36))) (@HMul.hMul Real Real Real qz5 qz948 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz36))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz690 qz53) qz28) 

noncomputable def Ns60p390 := nat_lit 13609832419224068139243930960539936673438270442956293112956994866116114663510224223086778870906944825 

noncomputable def Ns60p391 := nat_lit 1913787537362899964524523354293764267830293679194569705295505709552703224205297100765321232611073967012951570646177793199317138293465236992197974490667 

noncomputable def Ns60p392 := nat_lit 442364170773461646730475395439284220320771734302831997304466698437471500282974393223334434577018337937965711360000000000000000000000000000000000000000000 

noncomputable def Ns60p393 := nat_lit 78026944579582163875151268205114215033374925493270731517426985737875 

noncomputable def Ns60p394 := nat_lit 1684996666696914987166688442938726917102321526408785780068975640576 

noncomputable def Ns60p395 := nat_lit 4667904158427440296678114429730736530067318555283118338749675824155932903453819595696050806913512740054877 

noncomputable def Ns60p396 := nat_lit 11426410561947645101604991809802925496454736456799118771460925030400000000000000000000000000000000000000000000 

noncomputable def Ns60p397 := nat_lit 1599460875159291359670110591935072464557199645800050885922603192405288928013338095973945160510581738453817988100636330114252830002030817356973040838713886775653171200 

noncomputable def Ns60p398 := nat_lit 5650009326613023853211778591940915713410370432038954355388369496697310885784356224844635621539904825 

noncomputable def Ns60p399 := @Enclosure.Real.IsNear.subLit_ft (@HSub.hSub Real Real Real qz11 Ns60p359 (@HMul.hMul Real Real Real qz5 qz947 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 2 Zeta.RiemannSiegel.correction qz36))) (@HMul.hMul Real Real Real qz5 qz948 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz36)) Ns60p398 Ns60p363 

noncomputable def Ns60p400 := nat_lit 1147121352683608314008816323464056529290059262077570606108931816974554741616908136117727744710391088871972554770386615847844081415227599848845425704491 

noncomputable def Ns60p401 := nat_lit 55232367933498756937483689437300294900106550986233341621116542173716727604822679375 

noncomputable def Ns60p402 := nat_lit 1897137590064188545819787018382342682267975428761855001222473056385648716020711424 

noncomputable def Ns60p403 := nat_lit 4870586509657692235123998678839709607563769754975263477588358674272871361510699166117513528088514946237177353459443646863787751 

noncomputable def Ns60p404 := nat_lit 2810314326601511896896277997364678060993346542069526173821242369980285153160925135503360000000000000000000000000000000000000000000 

noncomputable def Ns60p405 := nat_lit 25819724676984213651522002507083090413920178537345225471701837919003513486694346648028079330777976064797058601962593037006525008383703088918134977698308742201749093233689698815180800 

noncomputable def Ns60p406 := nat_lit 84843472157317093484630908681627439302970268931607170451434324691090558025 

noncomputable def Ns60p407 := nat_lit 7067388259113537318333190002971674063309935587502475832486424805170479104 

noncomputable def Ns60p408 := nat_lit 7215015289016220245499937959156846071643737515779351048462977709540918231723867238004180048861255826849 

noncomputable def Ns60p409 := nat_lit 70206030435805189025040955280162602113625333700334446675189112504320000000000000000000000000000000000000000 

noncomputable def Ns60p410 := @Enclosure.Real.IsNear.subLit_tt_p Ns60p359 (@HMul.hMul Real Real Real qz5 qz947 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 2 Zeta.RiemannSiegel.correction qz36)) Ns60p406 Ns60p407 Ns60p408 Ns60p409 

noncomputable def Ns60p411 := nat_lit 8932232178348561048567465382640297960408032514101998971115689528760590443044677120401768013663501625 

noncomputable def Ns60p412 := nat_lit 1101659955199215661867147613094165750499856731321595615644712309577170242594229833221658700309476566441413711763433076125859930373973073589125594152491 

noncomputable def Ns60p413 := nat_lit 39930809578786867924177018837678650353010638916474364338205699515204132308887574157471173361448026540237869563039289224621691175227242843269159497074627424185790199811276800 

noncomputable def Ns60p414 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz5 qz48 qz49) (@HMul.hMul Real Real Real qz5 qz946 qz32) 

noncomputable def Ns60p415 := nat_lit 6401079090681244996730227272637663747930308549530344003070370657397224375 

noncomputable def Ns60p416 := nat_lit 506590008538706437034883583420454169348137207707222067236022387404296460147311166060407479261255826849 

noncomputable def Ns60p417 := nat_lit 287917037175923886952823899762744835870857725 

noncomputable def Ns60p418 := nat_lit 433521822872781746815283721050250090227457001331383013578491839007 

noncomputable def Ns60p419 := nat_lit 4536958379750456308154199677722442491494400000000000000000000000000000 

noncomputable def Ns60p420 := nat_lit 1892072654338955782825613664211592382709254546897256567376633165831465346185423763197200287856356301968719068161638400 

noncomputable def Ns60p421 := nat_lit 813459867375178152210837051760705677936944429029057098823207231125 

noncomputable def Ns60p422 := nat_lit 842498333348457493583344221469363458551160763204392890034487820288 

noncomputable def Ns60p423 := @Enclosure.Real.IsNear.mulLit_tt qz48 qz49 Ns60p421 Ns60p422 

noncomputable def Ns60p424 := nat_lit 1103812601601517040942868706661380726887851651618268646508024992444627966135824453059031123 

noncomputable def Ns60p425 := nat_lit 191561942608236107294793378393788647952342390272950272000000000000000000000000000000000000000000 

noncomputable def Ns60p426 := nat_lit 87141310660888709988984981146907067776890025 

noncomputable def Ns60p427 := nat_lit 89202980794122492566142873090593446023921664 

noncomputable def Ns60p428 := nat_lit 12915509769674514448635026580219251232191347225000268681559 

noncomputable def Ns60p429 := nat_lit 3323069989462289682259517650700861440000000000000000000000000000 

noncomputable abbrev qz54 := qz375

noncomputable def Ns60p430 := @Enclosure.Real.IsNear.mulLit_ft qz54 qz50 Ns60p426 Ns60p427 Ns60p428 Ns60p429 

noncomputable def Ns60p431 := nat_lit 113341516736121021177027447 

noncomputable def Ns60p432 := nat_lit 57646075230342348800000000000000 

noncomputable def Ns60p433 := @Enclosure.Real.IsNear.mulLit_tt qz50 qz50 9334951026164449567245 9444732965739290427392 Ns60p431 Ns60p432 9334951026164449567245 9444732965739290427392 

noncomputable abbrev qz693 := (@HSub.hSub Real Real Real qz920 qz945 qz932)

noncomputable abbrev qz378 := qz693

noncomputable abbrev qz55 := qz378

noncomputable def Ns60p434 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz55 884279719003555 140737488355328 1 500000000000000 10556559 67108864 21 67108864 

noncomputable abbrev qz694 := qz945

noncomputable abbrev qz379 := qz694

noncomputable abbrev qz56 := qz379

noncomputable def Ns60p435 := @Enclosure.Real.IsNear.subLit_ff_n qz56 qz348 56552305 67108864 21 67108864 1 1 0 1 10556559 

noncomputable def Ns60p436 := @Enclosure.Real.IsNear.mulLit_ff qz0 qz36 2 1 0 1 56552305 134217728 21 134217728 56552305 67108864 21 

noncomputable def Ns60p437 := @Enclosure.Real.IsNear.recentre' qz49 Bool.true 62951640 67108864 

noncomputable abbrev qz695 := qz949

noncomputable def Ns60p438 := @Enclosure.Real.IsNear.sin_image qz37 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 258318965)) qz695) Bool.true 258318965 134217728 

noncomputable def Ns60p439 := nat_lit 4879507304974805954998261331645 

noncomputable def Ns60p440 := nat_lit 2535301200456458802993406410752 

noncomputable def Ns60p441 := nat_lit 140159456484049690811365073603764501 

noncomputable def Ns60p442 := @Enclosure.Real.IsNear.recentre' qz37 Bool.true Ns60p439 Ns60p440 Ns60p441 

noncomputable def Ns60p443 := nat_lit 77371252455336267181195264000000000000000 

noncomputable def Ns60p444 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz38 884279719003555 140737488355328 1 500000000000000 5518058596292639 

noncomputable def Ns60p445 := @Enclosure.Real.IsNear.subLit_tf qz39 qz23 4392158689450015 18014398509481984 5193769539 18014398509481984 1 16 

noncomputable def Ns60p446 := @Enclosure.Real.IsNear.subLit_ff_n qz40 qz36 3198163200813025 18014398509481984 2375197251 18014398509481984 56552305 134217728 21 134217728 

noncomputable def Ns60p447 := @Enclosure.Real.IsNear.mulLit_ff qz36 qz36 56552305 134217728 21 134217728 56552305 134217728 21 134217728 3198163200813025 18014398509481984 

noncomputable def Ns60p448 := nat_lit 24443926328112380993521503766118457396354909545597552634303872237589786453809741483584529066763097755540625 

noncomputable def Ns60p449 := nat_lit 212813371219357667808056223692308629509040396751503069069405487845990478953701519077062806287447472524492800 

noncomputable def Ns60p450 := nat_lit 88282678912716897778203426963278217130760422156760604066664985301091710600733479986179737890869140625 

noncomputable def Ns60p451 := nat_lit 121878012226569034976790696566261037472487673147264504859487744410721219391566741651454921795079221301140625 

noncomputable def Ns60p452 := nat_lit 7448467992677518373281967829230802032816413886302607417429192074609666763379553167697198220060661538357248000 

noncomputable def Ns60p453 := BSN.sin_dyadic_bound_f 258318965 134217728 4 3 67108864 17475728 Ns60p448 Ns60p449 Ns60p450 Ns60p451 Ns60p452 Ns60p450 62951640 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 258318965) (BSN.sinEvenQ 134217728) 0 3 Ns60p448 Ns60p449 Ns60p450 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 258318965) (BSN.sinOddQ 134217728) 0 3 Ns60p451 Ns60p452 Ns60p450 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p454 := @Ns60p437 1099573840 586388126826496 7868955 8388608 68723365 36649257926656 (@Ns60p438 61 33554432 Bool.true 62951640 67108864 1 17475728 (@Ns60p442 Ns60p443 258318965 134217728 61 33554432 (@Ns60p444 18014398509481984 5193769539 18014398509481984 Ns60p439 Ns60p440 Ns60p441 Ns60p443 RS061to078.d39 (@Ns60p445 0 1 88288937540682224 5518058596292639 18014398509481984 5193769539 18014398509481984 (@Ns60p446 589505560313438582865920 4392158689450015 18014398509481984 5193769539 18014398509481984 (@Ns60p447 2375197251 18014398509481984 (Ns60p376 rfl rfl) (Ns60p376 rfl rfl) rfl) (Ns60p376 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 258318965 134217728) (BSN.sin_neg_of_bound 258318965 134217728 Bool.false 62951640 67108864 1 17475728 (Ns60p453 rfl rfl)) rfl rfl) 

noncomputable def Ns60p455 := nat_lit 24764123610985940586033284467099667925 

noncomputable def Ns60p456 := nat_lit 664613997892457936451903530140172288 

noncomputable def Ns60p457 := nat_lit 9175928154317429672064308574141253347107466544911747 

noncomputable def Ns60p458 := @Enclosure.Real.IsNear.mulLit_tt qz946 qz32 Ns60p455 Ns60p456 Ns60p457 

noncomputable def Ns60p459 := nat_lit 123794003928538027489912422400000000000000000000000000000 

noncomputable def Ns60p460 := nat_lit 340024550208363063531082341 

noncomputable abbrev qz950 := (@HMul.hMul Real Real Real qz5 qz317 qz50)

noncomputable def Ns60p461 := @Enclosure.Real.IsNear.mulLit_tf qz950 qz372 28004853078493348701735 9444732965739290427392 Ns60p460 Ns60p432 884279719003555 

noncomputable def Ns60p462 := @Enclosure.Real.IsNear.mulLit_ft qz317 qz50 3 1 0 1 9334951026164449567245 9444732965739290427392 Ns60p431 

noncomputable def Ns60p463 := @Enclosure.Real.IsNear.recentre' qz32 Bool.true 23252754 67108864 

noncomputable def Ns60p464 := @Enclosure.Real.IsNear.cos_image qz37 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 258318965)) qz695) Bool.true 258318965 134217728 

noncomputable def Ns60p465 := nat_lit 9435536663194494726961046442080771969452039948651435209454841218160343820273937141058887896626606133140625 

noncomputable def Ns60p466 := nat_lit 16370259324565974446773555668639125346849261288577159159185037526614652227207809159774062022111344040345600 

noncomputable def Ns60p467 := nat_lit 56932661354132119587888904015597306328286798637573897690372703357803370249082139589189884409763678670740625 

noncomputable def Ns60p468 := nat_lit 1489693598535503674656393565846160406563282777260521483485838414921933352675910633539439644012132307671449600 

noncomputable def Ns60p469 := BSN.cos_dyadic_bound_t 258318965 134217728 4 3 67108864 17475728 Ns60p465 Ns60p466 Ns60p450 Ns60p467 Ns60p468 Ns60p450 23252754 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 258318965) (BSN.cosEvenQ 134217728) 0 3 Ns60p465 Ns60p466 Ns60p450 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 258318965) (BSN.cosOddQ 134217728) 0 3 Ns60p467 Ns60p468 Ns60p450 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p470 := @Ns60p463 1099573840 586388126826496 11626377 33554432 68723365 36649257926656 (@Ns60p464 61 33554432 Bool.true 23252754 67108864 1 17475728 (@Ns60p442 Ns60p443 258318965 134217728 61 33554432 (@Ns60p444 18014398509481984 5193769539 18014398509481984 Ns60p439 Ns60p440 Ns60p441 Ns60p443 RS061to078.d39 (@Ns60p445 0 1 88288937540682224 5518058596292639 18014398509481984 5193769539 18014398509481984 (@Ns60p446 589505560313438582865920 4392158689450015 18014398509481984 5193769539 18014398509481984 (@Ns60p447 2375197251 18014398509481984 (Ns60p376 rfl rfl) (Ns60p376 rfl rfl) rfl) (Ns60p376 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 258318965 134217728) (BSN.cos_neg_of_bound 258318965 134217728 Bool.true 23252754 67108864 1 17475728 (Ns60p469 rfl rfl)) rfl rfl) 

noncomputable abbrev qz380 := (@Ns60p434 9334951026164449567245 9444732965739290427392 Ns60p431 Ns60p432 RS061to078.d39 (@Ns60p435 10556559 67108864 21 67108864 (@Ns60p436 67108864 qz916 (Ns60p376 rfl rfl) rfl) qz933 rfl rfl) rfl)

noncomputable abbrev qz696 := (Enclosure.Real.IsNear.const Bool.false 3 1)

noncomputable def Ns60p471 := @Ns60p414 Ns60p415 Ns60p407 Ns60p416 Ns60p409 Ns60p417 Ns60p323 Ns60p418 Ns60p419 Ns60p420 Ns60p406 Ns60p407 Ns60p408 Ns60p409 (@Ns60p423 Ns60p424 Ns60p425 7868955 8388608 68723365 36649257926656 Ns60p415 Ns60p407 Ns60p416 Ns60p409 (@Ns60p430 9334951026164449567245 9444732965739290427392 Ns60p431 Ns60p432 Ns60p421 Ns60p422 Ns60p424 Ns60p425 (@Ns60p433 Ns60p431 Ns60p432 Ns60p426 Ns60p427 Ns60p428 Ns60p429 qz380 qz380 rfl) qz380 rfl) (Ns60p454 rfl) rfl) (@Ns60p458 Ns60p459 11626377 33554432 68723365 36649257926656 Ns60p417 Ns60p323 Ns60p418 Ns60p419 (@Ns60p461 70368744177664 1 250000000000000 Ns60p455 Ns60p456 Ns60p457 Ns60p459 (@Ns60p462 Ns60p432 28004853078493348701735 9444732965739290427392 Ns60p460 Ns60p432 qz696 qz380 rfl) RS061to078.d41 rfl) (Ns60p470 rfl) rfl) rfl rfl 

noncomputable def Ns60p472 := nat_lit 12439684584782910217603925294139633 

noncomputable def Ns60p473 := nat_lit 629629456870625146568704000000000000000 

noncomputable def Ns60p474 := nat_lit 52889613732600443566339722166812863512801404057313172455395681665654323729575 

noncomputable def Ns60p475 := @Enclosure.Real.IsNear.mulLit_tf qz947 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz36) 168884428302089371745055 18889465931478580854784 Ns60p472 Ns60p473 Ns60p474 

noncomputable def Ns60p476 := nat_lit 14474011154664524427946373126085988481658748083205070504932198000989141204992 

noncomputable def Ns60p477 := nat_lit 190027142639463000038760062097775365574507596341486137491143562600478047509011872018802353056464579645158616577 

noncomputable def Ns60p478 := nat_lit 702578581650377974224069499341169515248336635517381543455310592495071288290231283875840000000000000000000000000000 

noncomputable def Ns60p479 := nat_lit 4146561528260970072534641764713211 

noncomputable def Ns60p480 := @Enclosure.Real.IsNear.mulLit_ft qz317 qz51 3 1 0 1 56294809434029790581685 18889465931478580854784 Ns60p479 

noncomputable def Ns60p481 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz53 884279719003555 140737488355328 1 500000000000000 63661767 134217728 153655597 146597031706624 56294809434029790581685 

noncomputable def Ns60p482 := @Enclosure.Real.IsNear.recentre' qz53 Bool.false 63661767 134217728 2458489552 2345552507305984 63661767 134217728 153655597 146597031706624 

noncomputable def Ns60p483 := @Enclosure.Real.IsNear.sin_image qz35 qz691 Bool.false 355328611 134217728 133 134217728 Bool.false 63661767 134217728 1 

noncomputable def Ns60p484 := nat_lit 73621683173071343820693801893573384280268927558713749048147379230295950954351795763648982869121 

noncomputable def Ns60p485 := nat_lit 1314132649052903663973499682506658039257523290121768794010386926687498464103323775893033315205120 

noncomputable def Ns60p486 := nat_lit 220747394648458788871821537535357163283932413605044863645696080508283228959592307492016429130881 

noncomputable def Ns60p487 := nat_lit 59135969207380664878807485712799611766588548055479595730467411700937430884649569915186499184230400 

noncomputable def Ns60p488 := BSN.cos_dyadic_bound_f 295935788783 274877906944 3 2 134217728 34985589 Ns60p484 Ns60p485 Ns60p382 Ns60p486 Ns60p487 Ns60p382 63661767 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 295935788783) (BSN.cosEvenQ 274877906944) 0 2 Ns60p484 Ns60p485 Ns60p382 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 295935788783) (BSN.cosOddQ 274877906944) 0 2 Ns60p486 Ns60p487 Ns60p382 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p489 := @Ns60p483 17475728 (Ns60p377 rfl) (Enclosure.sfrac_false_div 355328611 134217728) (BSN.sin_reduce1 qz691 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns60p378) qz692) 226375608064910080 72057594037927936 Bool.false 63661767 134217728 0 1000000000000000 34951456 17475728 (BSN.sin_reduce_arg_pos_rat_q1 355328611 134217728 226375608064910080 72057594037927936 0 Ns60p378 Ns60p379 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 63661767 134217728 Ns60p378 Ns60p379 295935788783 274877906944 34985589 34951456 (Ns60p488 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable abbrev qz57 := (@HMul.hMul Real Real Real qz323 qz320 qz377)

noncomputable abbrev qz697 := (@Enclosure.Real.IsNear.neg qz57 Bool.false 56294809434029790581685 18889465931478580854784 Ns60p479 Ns60p473 (@Ns60p481 18889465931478580854784 Ns60p479 Ns60p473 RS061to078.d39 (Ns60p482 (Ns60p489 rfl rfl) rfl) rfl))

noncomputable def Ns60p490 := @Ns60p480 Ns60p473 168884428302089371745055 18889465931478580854784 Ns60p472 Ns60p473 qz696 qz697 rfl 

noncomputable abbrev qz58 := (@HMul.hMul Real Real Real qz323 qz375 (Real.cos qz362))

noncomputable def Ns60p491 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz58) (@HMul.hMul Real Real Real qz5 qz372 qz49) 

noncomputable abbrev qz951 := (@HMul.hMul Real Real Real qz5 qz0 qz51)

noncomputable def Ns60p492 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz36) (@HMul.hMul Real Real Real qz5 qz31 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns60p491 (@HMul.hMul Real Real Real qz5 qz951 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c8 1 Zeta.RiemannSiegel.correction qz36))) (@HMul.hMul Real Real Real qz5 qz52 qz28))) 

noncomputable def Ns60p493 := @Enclosure.Real.IsNear.mulLit_tt qz31 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns60p491 (@HMul.hMul Real Real Real qz5 qz951 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 1 Zeta.RiemannSiegel.correction qz36))) (@HMul.hMul Real Real Real qz5 qz52 qz28)) 152458807 

noncomputable def Ns60p494 := nat_lit 346910846105469286312464206589343595695336931616637748289580159614225 

noncomputable def Ns60p495 := nat_lit 107839786668602559178668060348078522694548577690162289924414440996864 

noncomputable def Ns60p496 := nat_lit 6131011094344972575581728788284806273637080509960300314121501339902469056064928510152241720947301950499 

noncomputable def Ns60p497 := nat_lit 26173091741292848222854342287077364148510122132203785458777494448984834860646400000000000000000000000000000 

noncomputable def Ns60p498 := nat_lit 1128229242634240015932173876819978009512953755882678599829358521729775 

noncomputable def Ns60p499 := @Enclosure.Real.IsNear.subLit_ff_n (@HSub.hSub Real Real Real qz11 Ns60p491 (@HMul.hMul Real Real Real qz5 qz951 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz36))) (@HMul.hMul Real Real Real qz5 qz52 qz28) Ns60p498 Ns60p495 

noncomputable def Ns60p500 := nat_lit 667489716447468959271730652938384427877569832125629590851711391277760213171289101869156976303730119687 

noncomputable def Ns60p501 := nat_lit 5234618348258569644570868457415472829702024426440757091755498889796966972129280000000000000000000000000000 

noncomputable def Ns60p502 := nat_lit 10235840569165136780848111032536107459280724004536375 

noncomputable def Ns60p503 := nat_lit 748288838313422294120286634350736906063837462003712 

noncomputable def Ns60p504 := nat_lit 70989372727055056065001733040724683352112745838379611456308742803444662006667081 

noncomputable def Ns60p505 := nat_lit 665104631447911093803413201228420104392264996236138905600000000000000000000000000000 

noncomputable def Ns60p506 := nat_lit 259589514030588030941029033825720541111656407067248431413176867011947909135576589539716802505092027844827944649438003200 

noncomputable def Ns60p507 := nat_lit 36296201044213037190072546232554290080906091517767025 

noncomputable def Ns60p508 := nat_lit 2993155353253689176481146537402947624255349848014848 

noncomputable def Ns60p509 := nat_lit 3256919736867143601383022717111698200304743046689076308950306859254056279 

noncomputable def Ns60p510 := nat_lit 121788049152133490528744910880447689163807538544640000000000000000000000000000 

noncomputable def Ns60p511 := @Enclosure.Real.IsNear.subLit_ff_p Ns60p491 (@HMul.hMul Real Real Real qz5 qz951 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz36)) Ns60p507 Ns60p508 Ns60p509 Ns60p510 

noncomputable def Ns60p512 := nat_lit 179479217347219520866422929121180983723805506831391967737571771825425 

noncomputable def Ns60p513 := nat_lit 527502813528008230054680460511074996136122080736289267005014078403981467058597017422306276984199631879 

noncomputable def Ns60p514 := nat_lit 3376965397288030872220019536848754493442638147645104946684992176996887890283984051714926736480965742616069058654843699200 

noncomputable def Ns60p515 := @Enclosure.Real.IsNear.subLit_ft (@Neg.neg Real Real.instNeg qz58) (@HMul.hMul Real Real Real qz5 qz372 qz49) 

noncomputable def Ns60p516 := nat_lit 1013137730017611297375605238151833953938675318189425 

noncomputable def Ns60p517 := nat_lit 387105612264469480915542874115764720414887363025436437462306859254056279 

noncomputable def Ns60p518 := nat_lit 74182956421942839638968616201659 

noncomputable def Ns60p519 := nat_lit 3148147284353125732843520000000000000 

noncomputable def Ns60p520 := nat_lit 21425495408336233050908210068539948945191063760307332179016585929608396800 

noncomputable def Ns60p521 := @Enclosure.Real.IsNear.neg qz58 Bool.true Ns60p516 

noncomputable def Ns60p522 := @Enclosure.Real.IsNear.mulLit_ft qz54 qz32 Ns60p426 Ns60p427 Ns60p428 

noncomputable def Ns60p523 := @Enclosure.Real.IsNear.mulLit_ft qz372 qz49 884279719003555 70368744177664 1 

noncomputable def Ns60p524 := nat_lit 314814728435312573284352000000000000000 

noncomputable def Ns60p525 := nat_lit 3188201881339448651056403815855376093080868205 

noncomputable def Ns60p526 := @Enclosure.Real.IsNear.mulLit_tt qz951 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz36) 56294809434029790581685 9444732965739290427392 Ns60p479 Ns60p524 Ns60p525 

noncomputable def Ns60p527 := nat_lit 11417981541647679048466287755595961091061972992 

noncomputable def Ns60p528 := nat_lit 270859117440826139413912483476482725034362817038787916094641439 

noncomputable def Ns60p529 := nat_lit 16627615786197777345085330030710502609806624905903472640000000000000 

noncomputable def Ns60p530 := @Enclosure.Real.IsNear.mulLit_ft qz0 qz51 2 1 0 1 56294809434029790581685 18889465931478580854784 Ns60p479 

noncomputable def Ns60p531 := @Ns60p530 Ns60p473 56294809434029790581685 9444732965739290427392 Ns60p479 Ns60p524 qz321 qz697 rfl 

noncomputable abbrev qz59 := (@HMul.hMul Real Real Real qz323 qz376 (Real.sin qz362))

noncomputable def Ns60p532 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz59) (@HMul.hMul Real Real Real qz5 qz51 qz28) 

noncomputable def Ns60p533 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz36) (@HMul.hMul Real Real Real qz5 qz31 Ns60p532) Bool.true Ns60p525 Ns60p527 Ns60p528 Ns60p529 (BSN.deriv_correction_mk qz36 qz367) 

noncomputable def Ns60p534 := nat_lit 20911890523578927461083988515372392315 

noncomputable def Ns60p535 := nat_lit 85070591730234615865843651857942052864 

noncomputable def Ns60p536 := nat_lit 8700246831318858056074052513753720918810339029409373293 

noncomputable def Ns60p537 := @Enclosure.Real.IsNear.mulLit_tf qz31 Ns60p532 152458807 134217728 183 134217728 Ns60p534 Ns60p535 Ns60p536 

noncomputable def Ns60p538 := nat_lit 619426957748747518103023247074727066226550374400000000000000 

noncomputable def Ns60p539 := @Enclosure.Real.IsNear.subLit_tt_p (@Neg.neg Real Real.instNeg qz59) (@HMul.hMul Real Real Real qz5 qz51 qz28) 

noncomputable def Ns60p540 := nat_lit 73456309552091876244420378975 

noncomputable def Ns60p541 := nat_lit 19530378903032472755979868659585449109 

noncomputable def Ns60p542 := nat_lit 5281714698940581069507402924032000000000000 

noncomputable def Ns60p543 := nat_lit 99785002326350681675350196058760142715 

noncomputable def Ns60p544 := nat_lit 6409770371086672564400889097764364725296816013250960493 

noncomputable def Ns60p545 := nat_lit 1656810660882615612610037046006514001771754124070355751759868067840 

noncomputable def Ns60p546 := @Enclosure.Real.IsNear.neg qz59 Bool.false Ns60p540 

noncomputable def Ns60p547 := @Enclosure.Real.IsNear.mulLit_tt qz50 qz49 9334951026164449567245 9444732965739290427392 Ns60p431 

noncomputable def Ns60p548 := @Enclosure.Real.IsNear.mulLit_tf qz51 qz28 56294809434029790581685 18889465931478580854784 Ns60p479 Ns60p473 1772543567152239 4503599627370496 

noncomputable def Ns60p549 := @Enclosure.Real.IsNear.of_eq qz28 (@HMul.hMul Real Real Real qz5 qz31 qz32) Bool.false 1772543567152239 

noncomputable def Ns60p550 := @Enclosure.Real.IsNear.mulLit_tt qz31 qz32 152458807 134217728 183 

noncomputable abbrev qz381 := (@Ns60p549 4503599627370496 12801359228562253 4918980131801758957568 (BSN.correction_mk qz36 (BSN.cos_two_pi_p_ne_zero_mk qz26 259079 1000 6 qz29 rfl rfl qz943)) (@Ns60p550 134217728 11626377 33554432 68723365 36649257926656 1772543567152239 4503599627370496 12801359228562253 4918980131801758957568 Ns60p388 (Ns60p470 rfl) rfl))

noncomputable def Ns60p551 := @Ns60p548 12801359228562253 4918980131801758957568 Ns60p543 Ns60p535 Ns60p544 Ns60p538 qz697 qz381 

noncomputable def Ns60p552 := @Ns60p526 Ns60p527 Ns60p528 Ns60p529 Ns60p512 Ns60p495 Ns60p513 Ns60p501 Ns60p531 (Ns60p533 (@Ns60p537 Ns60p538 Ns60p525 Ns60p527 Ns60p528 Ns60p529 Ns60p388 (@Ns60p539 Ns60p540 Ns60p314 Ns60p541 Ns60p542 Ns60p543 Ns60p535 Ns60p544 Ns60p538 Ns60p545 Ns60p534 Ns60p535 Ns60p536 Ns60p538 (@Ns60p546 Ns60p314 Ns60p541 Ns60p542 (@Ns60p547 Ns60p432 7868955 8388608 68723365 36649257926656 Ns60p540 Ns60p314 Ns60p541 Ns60p542 qz380 (Ns60p454 rfl) rfl)) (Ns60p551 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns60p553 := @Ns60p511 Ns60p512 Ns60p495 Ns60p513 Ns60p501 Ns60p514 Ns60p498 Ns60p495 Ns60p500 Ns60p501 (@Ns60p515 Ns60p516 Ns60p508 Ns60p517 Ns60p510 6958357316251619135025 590295810358705651712 Ns60p518 Ns60p519 Ns60p520 Ns60p507 Ns60p508 Ns60p509 Ns60p510 (@Ns60p521 Ns60p508 Ns60p517 Ns60p510 (@Ns60p522 Ns60p429 11626377 33554432 68723365 36649257926656 Ns60p516 Ns60p508 Ns60p517 Ns60p510 (@Ns60p433 Ns60p431 Ns60p432 Ns60p426 Ns60p427 Ns60p428 Ns60p429 qz380 qz380 rfl) (Ns60p470 rfl) rfl)) (@Ns60p523 250000000000000 7868955 8388608 68723365 36649257926656 6958357316251619135025 590295810358705651712 Ns60p518 Ns60p519 RS061to078.d41 (Ns60p454 rfl) rfl) rfl rfl) Ns60p552 

noncomputable def Ns60p554 := nat_lit 5774662332057651456348088866169533625 

noncomputable def Ns60p555 := nat_lit 166153499473114484112975882535043072 

noncomputable def Ns60p556 := nat_lit 111899422133606184663729100863998513555746280871683584108573 

noncomputable def Ns60p557 := nat_lit 2704237925857577507587790297104384000000000000000000000000000000 

noncomputable def Ns60p558 := @Enclosure.Real.IsNear.mulLit_ff qz52 qz28 Ns60p554 Ns60p555 Ns60p556 Ns60p557 1772543567152239 4503599627370496 

noncomputable def Ns60p559 := @Enclosure.Real.IsNear.mulLit_ft qz47 qz34 Ns60p313 Ns60p317 Ns60p315 Ns60p318 7384945 8388608 153655597 146597031706624 Ns60p554 

noncomputable abbrev qz60 := (@HMul.hMul Real Real Real qz323 qz683 qz361)

noncomputable def Ns60p560 := @Ns60p558 12801359228562253 4918980131801758957568 Ns60p502 Ns60p503 Ns60p504 Ns60p505 (@Enclosure.Real.IsNear.neg qz60 Bool.true Ns60p554 Ns60p555 Ns60p556 Ns60p557 (@Ns60p559 Ns60p555 Ns60p556 Ns60p557 RS061to078.d43 (Ns60p369 (Ns60p386 rfl rfl) rfl) rfl)) qz381 

noncomputable def Ns60p561 := nat_lit 17323986996172954369044266598508600875 

noncomputable def Ns60p562 := nat_lit 335698266400818553991187302591995540667238842615050752325719 

noncomputable def Ns60p563 := @Enclosure.Real.IsNear.mulLit_ft qz948 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz36) Ns60p561 Ns60p555 Ns60p562 Ns60p557 Ns60p525 

noncomputable def Ns60p564 := @Enclosure.Real.IsNear.mulLit_ff qz317 qz52 3 1 0 1 Ns60p554 Ns60p555 Ns60p556 

noncomputable def Ns60p565 := @Ns60p564 Ns60p557 Ns60p561 Ns60p555 Ns60p562 Ns60p557 qz696 (@Enclosure.Real.IsNear.neg qz60 Bool.true Ns60p554 Ns60p555 Ns60p556 Ns60p557 (@Ns60p559 Ns60p555 Ns60p556 Ns60p557 RS061to078.d43 (Ns60p369 (Ns60p386 rfl rfl) rfl) rfl)) rfl 

noncomputable def Ns60p566 := @Ns60p563 Ns60p527 Ns60p528 Ns60p529 Ns60p401 Ns60p402 Ns60p403 Ns60p404 Ns60p565 (Ns60p533 (@Ns60p537 Ns60p538 Ns60p525 Ns60p527 Ns60p528 Ns60p529 Ns60p388 (@Ns60p539 Ns60p540 Ns60p314 Ns60p541 Ns60p542 Ns60p543 Ns60p535 Ns60p544 Ns60p538 Ns60p545 Ns60p534 Ns60p535 Ns60p536 Ns60p538 (@Ns60p546 Ns60p314 Ns60p541 Ns60p542 (@Ns60p547 Ns60p432 7868955 8388608 68723365 36649257926656 Ns60p540 Ns60p314 Ns60p541 Ns60p542 qz380 (Ns60p454 rfl) rfl)) (Ns60p551 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns60p567 := @Ns60p399 Ns60p400 Ns60p392 Ns60p401 Ns60p402 Ns60p403 Ns60p404 Ns60p405 Ns60p390 Ns60p363 Ns60p391 Ns60p392 (@Ns60p410 Ns60p411 Ns60p363 Ns60p412 Ns60p392 Ns60p413 Ns60p398 Ns60p363 Ns60p400 Ns60p392 Ns60p471 (@Ns60p475 Ns60p476 Ns60p477 Ns60p478 Ns60p411 Ns60p363 Ns60p412 Ns60p392 Ns60p490 (@Ns60p492 Bool.false Ns60p474 Ns60p476 Ns60p477 Ns60p478 (BSN.iteratedDeriv_two_correction_mk qz36 qz367) (@Ns60p493 134217728 183 134217728 Ns60p494 Ns60p495 Ns60p496 Ns60p497 Ns60p474 Ns60p476 Ns60p477 Ns60p478 Ns60p388 (@Ns60p499 Ns60p500 Ns60p501 Ns60p502 Ns60p503 Ns60p504 Ns60p505 Ns60p506 Ns60p494 Ns60p495 Ns60p496 Ns60p497 (Ns60p553 rfl rfl) (Ns60p560 rfl) rfl rfl) rfl)) rfl) rfl rfl) Ns60p566 

noncomputable def Ns60p568 := nat_lit 44019761220842612691985476987431947280472837749572125 

noncomputable def Ns60p569 := nat_lit 374144419156711147060143317175368453031918731001856 

noncomputable def Ns60p570 := nat_lit 3019726243616207983357885274590505397821395750866698882246155155480919941583658192779 

noncomputable def Ns60p571 := nat_lit 11614613452161168148874751174969452778225664000000000000000000000000000000000000000000000 

noncomputable def Ns60p572 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz684 RSCompact.c11) qz53) qz28 Ns60p568 Ns60p569 Ns60p570 Ns60p571 1772543567152239 4503599627370496 12801359228562253 

noncomputable def Ns60p573 := @Enclosure.Real.IsNear.mulLit_ff qz685 qz53 Ns60p319 Ns60p320 Ns60p321 Ns60p322 63661767 134217728 153655597 146597031706624 Ns60p568 

noncomputable def Ns60p574 := Ns60p361 (@Ns60p365 Ns60p366 Ns60p354 Ns60p355 Ns60p356 Ns60p357 Ns60p388 (@Ns60p389 Ns60p390 Ns60p363 Ns60p391 Ns60p392 Ns60p393 Ns60p394 Ns60p395 Ns60p396 Ns60p397 Ns60p362 Ns60p363 Ns60p364 Ns60p366 (Ns60p567 rfl rfl) (@Ns60p572 4918980131801758957568 Ns60p393 Ns60p394 Ns60p395 Ns60p396 (@Ns60p573 Ns60p569 Ns60p570 Ns60p571 RS061to078.d44 (Ns60p482 (Ns60p489 rfl rfl) rfl) rfl) qz381 rfl) rfl rfl) rfl) 

noncomputable def Ns60p575 := @Enclosure.Real.IsNear.of_eq qz688 (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz36) qz374)) Bool.false Ns60p349 Ns60p350 Ns60p351 Ns60p352 (BSN.correctionLinear_mk qz36) (@Enclosure.Real.IsNear.neg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz36) qz374) Bool.true Ns60p349 Ns60p350 Ns60p351 Ns60p352 (@Ns60p358 Ns60p350 Ns60p351 Ns60p352 Ns60p574 RS061to078.d45 rfl)) 

noncomputable def Ns60p576 := @Enclosure.Real.IsNear.inv_image qz30 53866179 8388608 21 8388608 653180 653182 4194304 qz674 rfl 

noncomputable def Ns60p577 := @Ns60p353 Ns60p341 Ns60p346 Ns60p344 Ns60p575 (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz30) Bool.false 1306362 8388608 2 8388608 653181 4194304 1 4194304 (Ns60p576 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns60p578 := @Ns60p343 Ns60p344 Ns60p336 Ns60p332 Ns60p338 Ns60p334 (Ns60p240 qz25 (@Enclosure.Real.IsNear.of_eq qz672 (@Inv.inv Real Real.instInv (Real.sqrt qz30)) Bool.false 827593 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz27 (BSN.t_div_two_pi_nonneg qz26 259079 1000 qz29)) Ns60p244) rfl) (@Ns60p347 Ns60p348 Ns60p340 Ns60p341 Ns60p342 Ns60p344 (@Ns60p245 17592186044416 799300465191889 19214766139850620928 (BSN.correction_mk qz36 qz367) (@Ns60p246 4194304 1453303 4194304 68723365 2290578620416 6923993282445 17592186044416 799300465191889 19214766139850620928 Ns60p263 (Ns60p279 rfl) rfl)) (Ns60p577 rfl) rfl rfl) 

noncomputable def Ns60p579 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz26) (hardyZApproximantRS qz26) Bool.false Ns60p331 Ns60p332 Ns60p333 Ns60p334 (@Eq.refl Real (hardyZApproximantRS qz26)) (Ns60p335 (BSN.hardyZApproximantRS_eq qz26 6 qz943) (@Ns60p337 Ns60p338 Ns60p334 Ns60p339 Ns60p331 Ns60p332 Ns60p333 Ns60p334 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz26) qz26 6) (@HAdd.hAdd Real Real Real qz336 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz26) qz26 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz26) qz26 6)) Bool.false 3981567 4194304 46395 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz26) qz26 6) (Ns60p238 (Ns60p237 rfl rfl rfl rfl) rfl rfl)) (Ns60p578 rfl) rfl rfl)) 

theorem RS061to078.d46 : Enclosure.Real.IsNear (hardyZApproximantRS qz26) Bool.false Ns60p331 Ns60p332 Ns60p333 Ns60p334 := Ns60p579 

theorem RS061to078.d47 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal (RS061to078.d3 a b h)) (hardyZApproximantRS b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal (RS061to078.d3 a b h)) 

noncomputable def Ns60p580 := nat_lit 16332213164019627723821444042595674046927113504058592928124114517359787697672488934917486977915079709551978000308194562191155 

noncomputable def Ns60p581 := nat_lit 169230328010303641331690318856389386196071598838855992136870091590247882556495704531248437872567112920983350278405979725889536 

noncomputable def Ns60p582 := nat_lit 141883035829991008244234468831261834688582092172758631585453791073535440561016594914043624514041310002808808019902097304521847381103390739877715347064946575141444199265731763 

noncomputable def Ns60p583 := nat_lit 100791489167662478793230978422140614232312976055989702144536499777436626025989017883986573425867092251834361309534486873806392734515200000000000000000000000000000000000000000000 

noncomputable abbrev qz952 := (Enclosure.sfrac Bool.false 260767 1000)

noncomputable abbrev qz698 := qz952

noncomputable abbrev qz382 := qz698

noncomputable abbrev qz61 := qz382

noncomputable abbrev qz953 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 260767 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz699 := qz953

noncomputable abbrev qz383 := qz699

noncomputable abbrev qz62 := qz383

noncomputable abbrev qz954 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 260767 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz700 := qz954

noncomputable abbrev qz384 := qz700

noncomputable abbrev qz63 := (Zeta.RiemannSiegel.correction qz384)

noncomputable abbrev qz64 := qz384

noncomputable abbrev qz955 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 260767 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz701 := qz955

noncomputable abbrev qz385 := qz701

noncomputable abbrev qz65 := qz385

noncomputable abbrev qz702 := (@HAdd.hAdd Real Real Real qz336 qz63 (@HMul.hMul Real Real Real qz5 (Zeta.RiemannSiegel.correctionLinear qz64) (@Inv.inv Real Real.instInv qz65)))

noncomputable abbrev qz956 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz326 qz62 qz8))

noncomputable def Ns60p584 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz61) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz61) qz61 6) (@HMul.hMul Real Real Real qz5 qz956 qz702)) Bool.true Ns60p580 Ns60p581 Ns60p582 Ns60p583 

noncomputable def Ns60p585 := nat_lit 25937799407786649151847686311944784022358523237679681307988981522692760349193745054074939854135064922034184033169725532843827 

noncomputable def Ns60p586 := @Enclosure.Real.IsNear.subLit_ff_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz61) qz61 6) (@HMul.hMul Real Real Real qz5 qz956 qz702) 476141 8388608 23349 16777216 Ns60p585 Ns60p581 

noncomputable def Ns60p587 := nat_lit 1610628263935280205497284117268690551302362452922899878072618100417148403317869537127543626689633956670968332058730799822529928303390739877715347064946575141444199265731763 

noncomputable def Ns60p588 := nat_lit 137004534005400361281070356067270412075445159757053945105605372033240453958997022059360310602834260972185399069209323369953220362240 

noncomputable def Ns60p589 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.sin BSN.quadSignPos 5 6 260767 1000 71 67108864 33554432 1125899906842624 Bool.false 23823662455 1038 120242927 63 27397080 8 

noncomputable def Ns60p590 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 260767 1000 4 41 67108864 33554432 1125899906842624 Bool.false 23823662455 1038 

noncomputable def Ns60p591 := Ns60p590 93032624 62 33554424 8 108007536 62 30011992 8 Bool.true 40171589 23239 Bool.true 14518379 Bool.true 19150045 3537118876014220 1 Bool.false 65544521 Bool.false Bool.false 18891205 Bool.true Bool.true 15847739 

noncomputable def Ns60p592 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz61) qz61 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 260767 1000 110 43 67108864 33554432 1125899906842624 Bool.false 23823662455 1038 

noncomputable def Ns60p593 := Ns60p592 46516304 62 47453136 16 73726608 62 38745320 8 Bool.true 67108856 1110 Bool.false 98166132 Bool.false 65378712 3537118876014220 1 Bool.false 7234140 Bool.true Bool.false 55516694 Bool.false Bool.true 40171589 

noncomputable def Ns60p594 := nat_lit 9048602152339136443897529348687512914642685019568598151 

noncomputable def Ns60p595 := nat_lit 25489003312379803931532045937583022622820146348032000 

noncomputable def Ns60p596 := nat_lit 578773230244427139608775331360000 

noncomputable def Ns60p597 := nat_lit 905551307268830069984206188052518720 

noncomputable abbrev qz66 := (@Eq.refl Real qz382)

noncomputable def Ns60p598 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz61 260767 1000 271998713156 16000000 521534 4000 2000 Ns60p596 Ns60p597 qz66 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns60p599 := nat_lit 2895552688748523662047209391580004132685659206261951408320 

noncomputable abbrev qz957 := (Real.log (Enclosure.sfrac Bool.false 271998713156 16000000))

noncomputable abbrev qz958 := (@HSub.hSub Real Real Real qz11 qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 521534))))

noncomputable abbrev qz703 := (@HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 260767 4000) qz957) (@HMul.hMul Real Real Real qz5 qz12 qz958))

noncomputable abbrev qz959 := (Enclosure.sfrac Bool.false 260767 2000)

noncomputable abbrev qz386 := (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 qz703 qz959) (@HMul.hMul Real Real Real qz5 qz959 (Real.log Real.pi)))

noncomputable def Ns60p600 := @Enclosure.Real.IsNear.addLit_ft_p qz386 (Enclosure.sfrac Bool.true Ns60p596 Ns60p597) 3197563604217436722431 9007199254740992000 17292510435693078717099 Ns60p186 Ns60p596 Ns60p597 0 1 Ns60p599 

noncomputable def Ns60p601 := nat_lit 214584861046777787434227728384000 

noncomputable abbrev qz387 := (@HSub.hSub Real Real Real qz11 qz703 qz959)

noncomputable def Ns60p602 := @Enclosure.Real.IsNear.subLit_ff_p qz387 (@HMul.hMul Real Real Real qz5 qz959 (Real.log Real.pi)) 4541923118672253965567 9007199254740992000 16797939494001317227 Ns60p192 10016258913687 67108864000 260767 33554432000 Ns60p601 3197563604217436722431 9007199254740992000 

noncomputable def Ns60p603 := nat_lit 9083846237344507931134000 

noncomputable abbrev qz388 := qz703

noncomputable def Ns60p604 := @Enclosure.Real.IsNear.subLit_ff_p qz388 qz959 5716313282702776095999 9007199254740992000 16797939494001317227 Ns60p192 260767 2000 0 1 Ns60p603 4541923118672253965567 9007199254740992000 16797939494001317227 Ns60p192 

noncomputable def Ns60p605 := nat_lit 12871993184956619591896930162418122752 

noncomputable def Ns60p606 := nat_lit 11776102741721484638552064 

noncomputable def Ns60p607 := BSN.log_dyadic_bound 9854713156 534142713156 2 1 855925314052958686441008 33554432 8737864 97115371387039480336 97115371387039480336 1238271 543997426312 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 9854713156) (BSN.artanhQ 534142713156) 0 1 97115371387039480336 855925314052958686441008 97115371387039480336 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz704 := qz957

noncomputable def Ns60p608 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 260767 4000) qz704 260767 4000 0 1 21934700648712897 2251799813685248 62500007645631 546116500000000000000 5719846084062916011999 9007199254740992000 16297939493728258977 Ns60p192 (Enclosure.Real.IsNear.const Bool.false 260767 4000) (BSN.isNear_log_sfrac 271998713156 16000000 21934700648712897 2251799813685248 62500007645631 546116500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 271998713156) qz650)) Bool.false Ns60p606 Ns60p84 1000000122330096 8737864000000000000000 21934700648712897 2251799813685248 62500007645631 546116500000000000000 (BSN.log_rat_reduce_isNear 271998713156 16000000 14 543997426312 524288000000 1238271 33554432 24973259072661432 36028797018963968 8737864 1000000000000000 rfl rfl rfl rfl (Ns60p607 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p609 := BSN.arctan_dyadic_bound_f 1000 521534 1 0 4194304 1092233 0 1 1 0 1 1 8042 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 521534) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 521534) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz960 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 521534)))

noncomputable abbrev qz705 := qz960

noncomputable abbrev qz389 := qz705

noncomputable def Ns60p610 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz389 884279719003555 562949953421312 1 2000000000000000 8042 4194304 1 1092233 3704410719010072559616 883200340034979 562949953421312 2000000001092233 2184466000000000000000 qz15 (Ns60p609 rfl) rfl rfl 

noncomputable abbrev qz706 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 260767 4000) qz957)

noncomputable abbrev qz390 := qz706

noncomputable abbrev qz707 := (@HMul.hMul Real Real Real qz5 qz12 qz958)

noncomputable abbrev qz391 := qz707

noncomputable abbrev qz708 := qz958

noncomputable abbrev qz392 := qz708

noncomputable def Ns60p611 := @Enclosure.Real.IsNear.subLit_ff_p qz390 qz391 5719846084062916011999 9007199254740992000 16297939493728258977 Ns60p192 883200340034979 2251799813685248 2000000001092233 8737864000000000000000 Ns60p605 5716313282702776095999 9007199254740992000 16797939494001317227 Ns60p192 (Ns60p608 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz12 qz392 1 4 0 1 883200340034979 562949953421312 2000000001092233 2184466000000000000000 883200340034979 2251799813685248 2000000001092233 8737864000000000000000 qz335 Ns60p610 rfl) 

noncomputable def Ns60p612 := @Ns60p600 Ns60p594 Ns60p595 17292510435693078717099 Ns60p186 (@Ns60p602 17292510435693078717099 Ns60p186 (Ns60p604 (Ns60p611 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 260767 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz959 (Real.log Real.pi) 260767 2000 0 1 38410761 33554432 1 16777216 10016258913687 67108864000 260767 33554432000 (Enclosure.Real.IsNear.const Bool.false 260767 2000) RS061to078.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns60p596 Ns60p597) 

noncomputable def Ns60p613 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz61) Bool.false Ns60p594 Ns60p595 17292510435693078717099 Ns60p186 1488978903 4194304 131 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz61) (@HAdd.hAdd Real Real Real qz336 qz386 (Enclosure.sfrac Bool.true Ns60p596 Ns60p597)) Bool.false Ns60p594 Ns60p595 17292510435693078717099 Ns60p186 Ns60p598 (Ns60p612 rfl rfl)) 

noncomputable def Ns60p614 := nat_lit 140083398823590360615013605256827131885406424900067821665153442478714821052943705560545 

noncomputable def Ns60p615 := nat_lit 281645516381242153890832888749497222222635851369126892420968420163451189095668372961 

noncomputable def Ns60p616 := nat_lit 366429094654309885742545712900381397530561130978913327487672686192559896070602432435681 

noncomputable def Ns60p617 := BSN.sin_dyadic_bound_f 26990619653 17179869184 3 2 8388608 2186600 Ns60p614 Ns60p94 Ns60p615 Ns60p616 Ns60p97 Ns60p615 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26990619653) qz655 0 2 Ns60p614 Ns60p94 Ns60p615 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26990619653) qz656 0 2 Ns60p616 Ns60p97 Ns60p615 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz709 := (@Nat.cast Real Real.instNatCast 604462909807314587353088)

noncomputable def Ns60p618 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz61) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1488978903) qz660) Bool.false 1488978903 4194304 131 8388608 Bool.true 8388607 8388608 1 1092233 (Ns60p613 rfl) (Enclosure.sfrac_false_div 1488978903 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1488978903) qz660) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949648004782520235196416) qz709) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 56 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q1 1488978903 4194304 226375608064910080 72057594037927936 56 949648004782520235196416 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 949648004782520235196416 604462909807314587353088 26990619653 17179869184 2186600 2184466 (Ns60p617 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p619 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz61) Bool.false Ns60p594 Ns60p595 17292510435693078717099 Ns60p186 23823662455 67108864 1038 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz61) (@HAdd.hAdd Real Real Real qz336 qz386 (Enclosure.sfrac Bool.true Ns60p596 Ns60p597)) Bool.false Ns60p594 Ns60p595 17292510435693078717099 Ns60p186 Ns60p598 (Ns60p612 rfl rfl)) 

noncomputable def Ns60p620 := Ns60p593 23239 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 110 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 7234140 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 43 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 55516694 67108864) qz66 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 1) Bool.true 8388607 8388608 151471131 9162314481664 67108856 67108864 1110 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz61)) Bool.true 8388607 8388608 151471131 9162314481664 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz61) qz61) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz61)) Bool.true 8388607 8388608 151471131 9162314481664 8388607 8388608 151471131 9162314481664 (Ns60p618 rfl rfl) rfl)) rfl) (Ns60p619 rfl) RS061to078.d7 

noncomputable def Ns60p621 := nat_lit 764529018170592474188103309126193942765930867895328810988832444631126329408494761383346361098678829056 

noncomputable def Ns60p622 := nat_lit 800829657211492848905628873804112181470102223661149862653869354131854111354282116852078740504576 

noncomputable def Ns60p623 := nat_lit 4629734609115650634208075671314820476787095366423798878841606346193570462555509256155148141985708113920 

noncomputable def Ns60p624 := BSN.cos_dyadic_bound_f 98166132 67108864 4 3 67108864 33554432 Ns60p621 Ns60p219 Ns60p622 Ns60p623 Ns60p222 Ns60p622 7234140 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 98166132) qz338 0 3 Ns60p621 Ns60p219 Ns60p622 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 98166132) (BSN.cosOddQ 67108864) 0 3 Ns60p623 Ns60p222 Ns60p622 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p625 := nat_lit 1120923894284993955512806240103761584370759438024910079586436382720 

noncomputable def Ns60p626 := nat_lit 333803498224558164808513107627454131494206737228893913398378496 

noncomputable def Ns60p627 := nat_lit 2935212612701668217885754940954645414281950764871631999247545532416 

noncomputable def Ns60p628 := BSN.sin_dyadic_bound_f 65378712 67108864 3 2 67108864 33554432 Ns60p625 Ns60p119 Ns60p626 Ns60p627 Ns60p122 Ns60p626 55516694 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 65378712) qz339 0 2 Ns60p625 Ns60p119 Ns60p626 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 65378712) (BSN.sinOddQ 67108864) 0 2 Ns60p627 Ns60p122 Ns60p626 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p629 := nat_lit 44429611694798767118874344881 

noncomputable def Ns60p630 := nat_lit 486777830487640090174734030864384 

noncomputable def Ns60p631 := nat_lit 7301667457314601352621010462965760 

noncomputable def Ns60p632 := BSN.cos_dyadic_bound_f 14518379 67108864 2 1 67108864 33554432 Ns60p629 Ns60p630 Ns60p629 Ns60p629 Ns60p631 Ns60p629 65544521 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 14518379) qz338 0 1 Ns60p629 Ns60p630 Ns60p629 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 14518379) (BSN.cosOddQ 67108864) 0 1 Ns60p629 Ns60p631 Ns60p629 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p633 := nat_lit 134486656103163185355179100625 

noncomputable def Ns60p634 := BSN.sin_dyadic_bound_f 19150045 67108864 2 1 67108864 33554432 Ns60p633 Ns60p115 Ns60p633 Ns60p633 Ns60p116 Ns60p633 18891205 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 19150045) qz339 0 1 Ns60p633 Ns60p115 Ns60p633 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 19150045) (BSN.sinOddQ 67108864) 0 1 Ns60p633 Ns60p116 Ns60p633 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p635 := Ns60p591 39557 BSN.abs_quadSignPos (BSN.cos_quad_nat0 4 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 65544521 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 41 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 18891205 67108864) qz66 rfl rfl (Ns60p620 RS061to078.d9 RS061to078.d11 RS061to078.d13 RS061to078.d17 (Ns60p624 rfl rfl) (Ns60p628 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns60p619 rfl) RS061to078.d19 RS061to078.d21 RS061to078.d23 RS061to078.d25 RS061to078.d17 (Ns60p632 rfl rfl) (Ns60p634 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns60p636 := nat_lit 307174201427396245634048977900636954934912000209554100802731966720 

noncomputable def Ns60p637 := nat_lit 25078172664548669850109709584619544533600323550652005086986496 

noncomputable def Ns60p638 := nat_lit 804463258125533278814180478781388355090762742882131113141776220416 

noncomputable def Ns60p639 := BSN.sin_dyadic_bound_f 47305538 67108864 3 2 67108864 33554432 Ns60p636 Ns60p119 Ns60p637 Ns60p638 Ns60p122 Ns60p637 43484083 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 47305538) qz339 0 2 Ns60p636 Ns60p119 Ns60p637 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 47305538) (BSN.sinOddQ 67108864) 0 2 Ns60p638 Ns60p122 Ns60p637 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p640 := Ns60p589 Bool.true 15847739 39557 Bool.true 47305538 3537118876014220 1 Bool.false 43484083 Bool.false Bool.false 1904564 46698 BSN.abs_quadSignPos qz927 (BSN.sfrac_eq_quadSignPos_mul Bool.false 43484083 67108864) qz66 rfl (Ns60p635 rfl rfl) (Ns60p619 rfl) RS061to078.d27 RS061to078.d29 RS061to078.d17 (Ns60p639 rfl rfl) rfl 

noncomputable def Ns60p641 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 6) 1904564 67108864 46698 67108864 1904564 67108864 46698 67108864 255626252910592 476141 8388608 23349 16777216 (Ns60p640 rfl rfl rfl rfl) 

noncomputable def Ns60p642 := nat_lit 15696086966232788453288491996037995754531176221787267486064445057941120973115141869248454224315183423207722133402476327 

noncomputable def Ns60p643 := nat_lit 40347654345107946713373737062547060536401653012956617387979052445947619094013143666088208645002153616185987062074179584 

noncomputable def Ns60p644 := nat_lit 280041949768185107497675306166786989193462386741661503306068678555169837787587670709969962741791129712341848906867288494252027754197941620413330924294230639082269293191 

noncomputable def Ns60p645 := @Enclosure.Real.IsNear.mulLit_ff qz956 qz702 1652501 4194304 1 4194304 Ns60p642 Ns60p643 Ns60p644 

noncomputable def Ns60p646 := nat_lit 6944832889903654187022150221824321153912174720807319621985208615226551275613504926794080667513749518580467800725809742577087283200000000000000000000000000000000000000000000 

noncomputable abbrev qz961 := (@HPow.hPow Real Real Real qz326 qz62 qz8)

noncomputable def Ns60p647 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz961 1 1 0 1 1652501 4194304 1 4194304 1652501 4194304 1 4194304 

noncomputable def Ns60p648 := @Enclosure.Real.IsNear.sqrt_image qz62 348147153263 8388608000 260767 8388608000 27020676 27020697 4194304 (@Enclosure.Real.IsNear.of_eq qz62 (@HMul.hMul Real Real Real qz5 qz61 qz3) Bool.false 348147153263 8388608000 260767 8388608000 (BSN.t_div_two_pi_mk qz61 260767 1000 qz66) (@Enclosure.Real.IsNear.mulLit_ff qz61 qz3 260767 1000 0 1 1335089 8388608 1 8388608 348147153263 8388608000 260767 8388608000 (Enclosure.Real.IsNear.const Bool.false 260767 1000) RS061to078.d32 rfl)) 

noncomputable abbrev qz710 := (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 54041373 8388608 21 8388608 54041373 8388608 21 8388608 (Ns60p648 rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns60p649 := @Enclosure.Real.IsNear.sqrt_image qz65 54041373 8388608 21 8388608 10645793 10645799 4194304 qz710 rfl 

noncomputable def Ns60p650 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz65) 2661449 1048576 3 4194304 1652500 1652502 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz65) Bool.false 21291592 8388608 6 8388608 2661449 1048576 3 4194304 (Ns60p649 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns60p651 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz65)) Bool.false 3305002 8388608 2 8388608 1652501 4194304 1 4194304 (Ns60p650 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns60p652 := nat_lit 19272460435657936932710580721861158600480617945988651235684944874476515632694796968144799423682294098850016255598375 

noncomputable def Ns60p653 := nat_lit 4010406913163540100271005742617677751198702565464865783185597299508788954270230093754865622062311835300330562692671158034427754197941620413330924294230639082269293191 

noncomputable abbrev qz711 := (@HMul.hMul Real Real Real qz5 (Zeta.RiemannSiegel.correctionLinear qz64) (@Inv.inv Real Real.instInv qz65))

noncomputable def Ns60p654 := @Enclosure.Real.IsNear.addLit_ff qz63 qz711 3417663825149 8796093022208 763716222875879 19214766139850620928 Ns60p652 Ns60p643 Ns60p653 Ns60p646 

noncomputable def Ns60p655 := nat_lit 138064241039650166230549497397536672438473207162857792556750699053559684450527702161044314095588886116185075666163681341192605270016 

noncomputable abbrev qz712 := (@HMul.hMul Real Real Real qz918 qz915 qz954)

noncomputable abbrev qz393 := (Real.cos qz712)

noncomputable abbrev qz67 := (@Inv.inv Real Real.instInv qz393)

noncomputable abbrev qz713 := (@HSub.hSub Real Real Real qz920 (@HMul.hMul Real Real Real qz918 qz954 qz954) qz954)

noncomputable abbrev qz394 := (@HMul.hMul Real Real Real qz644 qz642 (@HSub.hSub Real Real Real qz647 qz713 qz930))

noncomputable abbrev qz68 := (Real.cos qz394)

noncomputable def Ns60p656 := @Enclosure.Real.IsNear.of_eq qz63 (@HMul.hMul Real Real Real qz5 qz67 qz68) Bool.false 3417663825149 

noncomputable def Ns60p657 := @Enclosure.Real.IsNear.mulLit_tt qz67 qz68 4486601 4194304 81 

noncomputable abbrev qz69 := (@Neg.neg Real Real.instNeg qz393)

noncomputable abbrev qz70 := qz393

noncomputable abbrev qz962 := (@Inv.inv Real Real.instInv qz69)

noncomputable def Ns60p658 := @Enclosure.Real.IsNear.of_eq qz67 (@Neg.neg Real Real.instNeg qz962) Bool.true 4486601 4194304 81 4194304 (BSN.inv_eq_neg_inv_neg qz70) 

noncomputable def Ns60p659 := @Enclosure.Real.IsNear.recentre' qz962 Bool.false 8973202 8388608 162 8388608 4486601 4194304 

noncomputable def Ns60p660 := @Enclosure.Real.IsNear.recentre' qz70 Bool.true 7842100 8388608 153655597 9162314481664 1960525 2097152 153655597 9162314481664 

noncomputable abbrev qz395 := qz712

noncomputable abbrev qz71 := qz395

noncomputable def Ns60p661 := @Enclosure.Real.IsNear.cos_image qz71 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23308889) qz337) Bool.false 23308889 8388608 133 8388608 Bool.true 7842100 8388608 1 

noncomputable def Ns60p662 := nat_lit 566707583621791249662855507 

noncomputable def Ns60p663 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz64 884279719003555 140737488355328 1 500000000000000 3709725 8388608 21 8388608 3280434580580463072375 1180591620717411303424 Ns60p662 

noncomputable def Ns60p664 := @Enclosure.Real.IsNear.subLit_ff_p qz65 qz1 54041373 8388608 21 8388608 6 1 0 1 3709725 3709725 8388608 21 

noncomputable def Ns60p665 := @Ns60p664 8388608 qz710 qz345 

noncomputable def Ns60p666 := @Enclosure.Real.IsNear.recentre' qz71 Bool.false 3280434580580463072375 1180591620717411303424 Ns60p662 Ns60p144 23308889 8388608 133 8388608 (@Ns60p663 Ns60p144 RS061to078.d31 (Ns60p665 rfl rfl) rfl) 

noncomputable def Ns60p667 := nat_lit 1460188685256078884077568 

noncomputable def Ns60p668 := nat_lit 48874627858546403994600094071246010811351171330332175333709959782805130068184860934400 

noncomputable def Ns60p669 := nat_lit 34374265438074654384968642163901240017551238112638486451707486839769262549013053696 

noncomputable def Ns60p670 := nat_lit 127949324152150365783519820956426569164938937193925711181651892071510952324928614646016 

noncomputable def Ns60p671 := BSN.sin_dyadic_bound_f 20750529262 17179869184 3 2 8388608 2186600 Ns60p668 Ns60p94 Ns60p669 Ns60p670 Ns60p97 Ns60p669 7842100 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 20750529262) qz655 0 2 Ns60p668 Ns60p94 Ns60p669 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 20750529262) qz656 0 2 Ns60p670 Ns60p97 Ns60p669 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p672 := @Ns60p661 1092233 (Ns60p666 rfl) (Enclosure.sfrac_false_div 23308889 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 23308889) qz337) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns60p667) qz657) 226375608064910080 72057594037927936 Bool.false 7842100 8388608 0 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q1 23308889 8388608 226375608064910080 72057594037927936 0 Ns60p667 Ns60p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 7842100 8388608 Ns60p667 Ns60p84 20750529262 17179869184 2186600 2184466 (Ns60p671 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p673 := @Enclosure.Real.IsNear.inv_image qz69 1960525 2097152 153655597 9162314481664 4486520 4486682 4194304 (@Enclosure.Real.IsNear.neg qz70 Bool.true 1960525 2097152 153655597 9162314481664 (Ns60p660 (Ns60p672 rfl rfl) rfl)) 

noncomputable def Ns60p674 := Ns60p658 (@Enclosure.Real.IsNear.neg qz962 Bool.false 4486601 4194304 81 4194304 (@Ns60p659 81 4194304 (Ns60p673 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p675 := @Enclosure.Real.IsNear.recentre' qz68 Bool.true 1523498 4194304 

noncomputable abbrev qz72 := qz394

noncomputable abbrev qz714 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable def Ns60p676 := @Enclosure.Real.IsNear.cos_image qz72 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 2036889)) qz714) Bool.true 2036889 1048576 

noncomputable def Ns60p677 := nat_lit 19237872924693669356586131845 

noncomputable def Ns60p678 := nat_lit 8958558251475514884032425108939421 

noncomputable def Ns60p679 := @Enclosure.Real.IsNear.recentre' qz72 Bool.true Ns60p677 Ns60p159 Ns60p678 

noncomputable abbrev qz396 := (@HSub.hSub Real Real Real qz647 qz713 qz930)

noncomputable abbrev qz73 := qz396

noncomputable def Ns60p680 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz73 884279719003555 140737488355328 1 500000000000000 21755415748279 

noncomputable abbrev qz397 := qz713

noncomputable abbrev qz74 := qz397

noncomputable def Ns60p681 := @Enclosure.Real.IsNear.subLit_tf qz74 qz23 17357369237175 70368744177664 331969659 70368744177664 1 16 

noncomputable abbrev qz715 := (@HMul.hMul Real Real Real qz918 qz954 qz954)

noncomputable abbrev qz398 := qz715

noncomputable abbrev qz75 := qz398

noncomputable def Ns60p682 := @Enclosure.Real.IsNear.subLit_ff_n qz75 qz64 13762059575625 70368744177664 155808891 70368744177664 3709725 8388608 21 8388608 

noncomputable def Ns60p683 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz64 3709725 8388608 21 8388608 3709725 8388608 21 8388608 13762059575625 70368744177664 

noncomputable def Ns60p684 := nat_lit 506365567006507090988392293477858769690327605498481146139899295407921237857309601 

noncomputable def Ns60p685 := nat_lit 846322570984149739285326836131859157750990110577656481930582364989086940895641600 

noncomputable def Ns60p686 := nat_lit 5100448348509812507655969548179982967391032398613444848162807252934800085921 

noncomputable def Ns60p687 := nat_lit 3054713956468268594961344409546577142779902927407137958197982955629374265285841825 

noncomputable def Ns60p688 := nat_lit 77015353959557626274964742087999183355340100062566739855682995214006911621503385600 

noncomputable def Ns60p689 := BSN.cos_dyadic_bound_t 2036889 1048576 4 3 4194304 1092233 Ns60p684 Ns60p685 Ns60p686 Ns60p687 Ns60p688 Ns60p686 1523498 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 2036889) (BSN.cosEvenQ 1048576) 0 3 Ns60p684 Ns60p685 Ns60p686 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 2036889) (BSN.cosOddQ 1048576) 0 3 Ns60p687 Ns60p688 Ns60p686 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p690 := @Ns60p675 280354625 9162314481664 761749 2097152 280354625 9162314481664 (@Ns60p676 249 8388608 Bool.true 1523498 4194304 1 1092233 (@Ns60p679 Ns60p162 2036889 1048576 249 8388608 (@Ns60p680 70368744177664 331969659 70368744177664 Ns60p677 Ns60p159 Ns60p678 Ns60p162 RS061to078.d31 (@Ns60p681 0 1 348086651972464 21755415748279 70368744177664 331969659 70368744177664 (@Ns60p682 145604166441920102400 17357369237175 70368744177664 331969659 70368744177664 (@Ns60p683 155808891 70368744177664 (Ns60p665 rfl rfl) (Ns60p665 rfl rfl) rfl) (Ns60p665 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 2036889 1048576) (BSN.cos_neg_of_bound 2036889 1048576 Bool.true 1523498 4194304 1 1092233 (Ns60p689 rfl rfl)) rfl rfl) 

noncomputable def Ns60p691 := nat_lit 14800753256524084772614791584738784005308712549535222935769663692156383849420829894583861193019032781633447625 

noncomputable def Ns60p692 := nat_lit 4809815209520810450717656262224562232065397860164239095208531909697964083434718092213655548692006303809402830848 

noncomputable def Ns60p693 := nat_lit 3077930384815459461589717539790745725104386206505976416940019720099892567841219442731637140702748975263597933698882285063785805458230388036106084135622492225897 

noncomputable def Ns60p694 := nat_lit 827888594854313634279030587890663284529706802464404061077261998084372434093177905892620166243761720488127207842565744230400000000000000000000000000000000000000000000 

noncomputable abbrev qz716 := (Zeta.RiemannSiegel.correctionLinear qz64)

noncomputable def Ns60p695 := @Enclosure.Real.IsNear.mulLit_ff qz716 (@Inv.inv Real Real.instInv qz65) Ns60p691 Ns60p692 Ns60p693 Ns60p694 1302127 8388608 1 8388608 Ns60p652 

noncomputable def Ns60p696 := nat_lit 104483034770777898533886723456933183713538424148014026386056909945547229218611363325383575771186971216625 

noncomputable def Ns60p697 := nat_lit 35835915874844867368919076489095108449946327955754392558399825615420669938882575126094039892345713852416 

noncomputable def Ns60p698 := nat_lit 1015244280317974619095570048872324392793846410886830952171944851273331283161209061046475779416523254212441728966837800963348848336114826952418203859700849823 

noncomputable def Ns60p699 := nat_lit 289907782958095824801284355155089306629420963792703977753455295487981322425450098342844455044394737951025208596889600000000000000000000000000000000000000000000 

noncomputable def Ns60p700 := @Enclosure.Real.IsNear.mulLit_tf (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz64) qz374 Ns60p696 Ns60p697 Ns60p698 Ns60p699 141657 134217728 1 134217728 Ns60p691 

noncomputable abbrev qz963 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 260767 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 6 1)))

noncomputable abbrev qz717 := (@HMul.hMul Real Real Real qz918 qz915 (@HSub.hSub Real Real Real qz920 qz963 qz932))

noncomputable abbrev qz399 := (@HMul.hMul Real Real Real qz644 qz717 qz717)

noncomputable abbrev qz400 := qz717

noncomputable abbrev qz76 := (@HMul.hMul Real Real Real qz323 qz399 qz400)

noncomputable abbrev qz77 := (Real.sin qz394)

noncomputable abbrev qz78 := qz400

noncomputable abbrev qz964 := (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz317 qz78) qz372)

noncomputable def Ns60p701 := @HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 qz76 qz77) (@HMul.hMul Real Real Real qz5 qz964 qz68) 

noncomputable abbrev qz401 := (Real.sin qz712)

noncomputable abbrev qz79 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz323 qz320 qz401))

noncomputable abbrev qz80 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz323 qz683 qz393))

noncomputable abbrev qz81 := qz401

noncomputable abbrev qz965 := (@HMul.hMul Real Real Real qz5 qz317 qz79)

noncomputable abbrev qz966 := (@HMul.hMul Real Real Real qz5 qz317 qz80)

noncomputable def Ns60p702 := @HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns60p701 (@HMul.hMul Real Real Real qz5 qz965 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz64))) (@HMul.hMul Real Real Real qz5 qz966 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz64))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz690 qz81) qz63) 

noncomputable abbrev qz967 := (@BSN.floor_sqrt_eq_dec qz61 260767 1000 6 qz66 rfl rfl rfl)

noncomputable abbrev qz402 := (BSN.cos_two_pi_p_ne_zero_mk qz61 260767 1000 6 qz66 rfl rfl qz967)

noncomputable def Ns60p703 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz64) (@HMul.hMul Real Real Real qz5 qz67 Ns60p702) Bool.true Ns60p696 Ns60p697 Ns60p698 Ns60p699 (BSN.iteratedDeriv_three_correction_mk qz64 qz402) 

noncomputable def Ns60p704 := nat_lit 2910964944056180285073112981162307289327007521845715103155212972094058023826240369943242450821625 

noncomputable def Ns60p705 := nat_lit 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468288 

noncomputable def Ns60p706 := nat_lit 28258758556956991966146072559048748692640177904434861699150773691427961599034604242259029136588895613242009727154007860864050953163071783664900616727 

noncomputable def Ns60p707 := @Enclosure.Real.IsNear.mulLit_tf qz67 Ns60p702 35892921 33554432 81 67108864 Ns60p704 Ns60p705 Ns60p706 

noncomputable def Ns60p708 := nat_lit 8639925210419172787704597567173519928140072935602187447352865203856865239901843617643250675332389412850892800000000000000000000000000000000000000000000 

noncomputable def Ns60p709 := @Enclosure.Real.IsNear.of_eq qz67 (@Neg.neg Real Real.instNeg qz962) Bool.true 35892921 33554432 81 67108864 (BSN.inv_eq_neg_inv_neg qz70) 

noncomputable def Ns60p710 := @Enclosure.Real.IsNear.recentre' qz962 Bool.false 143571684 134217728 162 134217728 35892921 33554432 

noncomputable def Ns60p711 := @Enclosure.Real.IsNear.recentre' qz70 Bool.true 125473200 134217728 2458489552 2345552507305984 7842075 8388608 153655597 146597031706624 

noncomputable abbrev qz718 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 372941083) qz949)

noncomputable def Ns60p712 := @Enclosure.Real.IsNear.cos_image qz71 qz718 Bool.false 372941083 134217728 133 134217728 Bool.true 125473200 134217728 1 

noncomputable def Ns60p713 := nat_lit 566707584099784104269433171 

noncomputable def Ns60p714 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz64 884279719003555 140737488355328 1 500000000000000 59355417 134217728 21 134217728 52486791466098831507435 18889465931478580854784 Ns60p713 

noncomputable def Ns60p715 := @Enclosure.Real.IsNear.subLit_ff_p qz65 qz1 864661785 134217728 21 134217728 6 1 0 1 59355417 59355417 134217728 21 

noncomputable def Ns60p716 := @Enclosure.Real.IsNear.sqrt_image qz62 1114070421061 26843545600 260767 134217728000 432330882 432330903 67108864 (@Enclosure.Real.IsNear.of_eq qz62 (@HMul.hMul Real Real Real qz5 qz61 qz3) Bool.false 1114070421061 26843545600 260767 134217728000 (BSN.t_div_two_pi_mk qz61 260767 1000 qz66) (@Enclosure.Real.IsNear.mulLit_ff qz61 qz3 260767 1000 0 1 21361415 134217728 1 134217728 1114070421061 26843545600 260767 134217728000 (Enclosure.Real.IsNear.const Bool.false 260767 1000) RS061to078.d40 rfl)) 

noncomputable def Ns60p717 := @Ns60p715 134217728 (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 864661785 134217728 21 134217728 864661785 134217728 21 134217728 (Ns60p716 rfl rfl rfl rfl rfl rfl) rfl) qz345 

noncomputable def Ns60p718 := @Enclosure.Real.IsNear.recentre' qz71 Bool.false 52486791466098831507435 18889465931478580854784 Ns60p713 Ns60p372 372941083 134217728 133 134217728 (@Ns60p714 Ns60p372 RS061to078.d39 (Ns60p717 rfl rfl) rfl) 

noncomputable def Ns60p719 := nat_lit 23362854528667667593691136 

noncomputable def Ns60p720 := nat_lit 209909014441973357746426933894324115510757809120567102964700824982028902091613414992624102204545 

noncomputable def Ns60p721 := nat_lit 147628033293161472993201312354485919094368219996155749673450987674962868666354353540873905281 

noncomputable def Ns60p722 := nat_lit 549522687675074627903414881884179706278212903911967684169983240020506708452575322693996948022401 

noncomputable def Ns60p723 := BSN.sin_dyadic_bound_f 332006131439 274877906944 3 2 134217728 34985589 Ns60p720 Ns60p381 Ns60p721 Ns60p722 Ns60p384 Ns60p721 125473200 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 332006131439) (BSN.sinEvenQ 274877906944) 0 2 Ns60p720 Ns60p381 Ns60p721 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 332006131439) (BSN.sinOddQ 274877906944) 0 2 Ns60p722 Ns60p384 Ns60p721 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p724 := @Ns60p712 17475728 (Ns60p718 rfl) (Enclosure.sfrac_false_div 372941083 134217728) (BSN.cos_reduce1 qz718 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns60p719) qz692) 226375608064910080 72057594037927936 Bool.false 125473200 134217728 0 1000000000000000 34951456 17475728 (BSN.sin_reduce_arg_pos_rat_q1 372941083 134217728 226375608064910080 72057594037927936 0 Ns60p719 Ns60p379 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 125473200 134217728 Ns60p719 Ns60p379 332006131439 274877906944 34985589 34951456 (Ns60p723 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p725 := @Enclosure.Real.IsNear.inv_image qz69 7842075 8388608 153655597 146597031706624 71785761 71785923 67108864 (@Enclosure.Real.IsNear.neg qz70 Bool.true 7842075 8388608 153655597 146597031706624 (Ns60p711 (Ns60p724 rfl rfl) rfl)) 

noncomputable def Ns60p726 := Ns60p709 (@Enclosure.Real.IsNear.neg qz962 Bool.false 35892921 33554432 81 67108864 (@Ns60p710 81 67108864 (Ns60p725 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p727 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns60p701 (@HMul.hMul Real Real Real qz5 qz965 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz64))) (@HMul.hMul Real Real Real qz5 qz966 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz64))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz690 qz81) qz63) 

noncomputable def Ns60p728 := nat_lit 39456514404503681835586492628499991594152997237350299669134513464153035621488719132155194484613625 

noncomputable def Ns60p729 := nat_lit 25489692105087471933979516375085636263230202421548722221076304269160803141089089872446220273315693293740354467660657864678012101243246270929281462807 

noncomputable def Ns60p730 := nat_lit 3603669403645984455518001619430974926037684083753953177588060770875 

noncomputable def Ns60p731 := nat_lit 105312291668557186697918027683670432318895095400549111254310977536 

noncomputable def Ns60p732 := nat_lit 45776568346651392494300003271283393619070704708037239404313813937156434617627684517036294811213864454557 

noncomputable def Ns60p733 := nat_lit 142830132024345563770062397622536568705684205709988984643261562880000000000000000000000000000000000000000000 

noncomputable def Ns60p734 := nat_lit 306560389225389712104544860257196025913531794788710480783122890090162258011116105840556731804410943986283434150144655727244748284227384051410373831274860118016000 

noncomputable def Ns60p735 := nat_lit 15369947229103178696324507137247893623494877225463140740568215409578036566453531681226763380613625 

noncomputable def Ns60p736 := @Enclosure.Real.IsNear.subLit_ft (@HSub.hSub Real Real Real qz11 Ns60p701 (@HMul.hMul Real Real Real qz5 qz965 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 2 Zeta.RiemannSiegel.correction qz64))) (@HMul.hMul Real Real Real qz5 qz966 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz64)) Ns60p735 Ns60p705 

noncomputable def Ns60p737 := nat_lit 13443494293343255524369704967785191716946973684613386461972794999844169222267949678013768241313052989682326048246384118261212121135976042694646411799 

noncomputable def Ns60p738 := nat_lit 668536536557754000311192973705967600735414757881146489386822663730097744822921875 

noncomputable def Ns60p739 := nat_lit 29642774844752946028434172162224104410437116074403984394101141506025761187823616 

noncomputable def Ns60p740 := nat_lit 2448921827080413429375630300396871273220045972214508785487868768335690301004456944493689903229950869197876866628540661106784831 

noncomputable def Ns60p741 := nat_lit 1756446454125944935560173748352923788120841588793453858638276481237678220725578209689600000000000000000000000000000000000000000000 

noncomputable def Ns60p742 := nat_lit 1169600572651454006038029780396601471934491863952645493031697596730109185787367180682329512082067513959862056185801374785722571635873903928318915714046946435507882877012410368000 

noncomputable def Ns60p743 := nat_lit 541873313175565045939043046706059180124356622980628637867965020788188303775 

noncomputable def Ns60p744 := nat_lit 56539106072908298546665520023773392506479484700019806659891398441363832832 

noncomputable def Ns60p745 := nat_lit 29168842162760646454672344646724200043452134859172772563961431544985516076704027464514651793005339429215303 

noncomputable def Ns60p746 := nat_lit 351030152179025945125204776400813010568126668501672233375945562521600000000000000000000000000000000000000000000 

noncomputable def Ns60p747 := @Enclosure.Real.IsNear.subLit_tt_p Ns60p701 (@HMul.hMul Real Real Real qz5 qz965 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 2 Zeta.RiemannSiegel.correction qz64)) Ns60p743 Ns60p744 Ns60p745 Ns60p746 

noncomputable def Ns60p748 := nat_lit 25605644717510438246668710719892139726975261436565941884582198017440746588803496358583153934623225 

noncomputable def Ns60p749 := nat_lit 509022396522925590560320001916028870342496415532515069617684018353285475650582118654366102102949130120017085049418675518177489518992400773817354671 

noncomputable def Ns60p750 := nat_lit 345597008416766911508183902686940797125602917424087497894114608154274609596073744705730027013295576514035712000000000000000000000000000000000000000000 

noncomputable def Ns60p751 := nat_lit 869003076721267606474382139305137980881602693065288544188257683876769800561431020654145941009711658028188272984114856033095513834205003011552991754066204503321174081536000 

noncomputable def Ns60p752 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz5 qz76 qz77) (@HMul.hMul Real Real Real qz5 qz964 qz68) 

noncomputable def Ns60p753 := nat_lit 20151592090707992493130804974774393031533162139023412164500590669791702625 

noncomputable def Ns60p754 := nat_lit 1274416127479931762609466664375822593123743698978939180417945079666264032465631300312037828205339429215303 

noncomputable def Ns60p755 := nat_lit 55419934440638194259244895437435462707810175 

noncomputable def Ns60p756 := nat_lit 5575186299632655785383929568162090376495104 

noncomputable def Ns60p757 := nat_lit 901317516198383779021161868850613391231952783491165451446013077083 

noncomputable def Ns60p758 := nat_lit 11342395949376140770385499194306106228736000000000000000000000000000000 

noncomputable def Ns60p759 := nat_lit 3021044671752965712228337517250020407763653383899993402213222892713252790216108618340498693043374731370007151352217600 

noncomputable def Ns60p760 := nat_lit 322294920803168298900920485933312309820566957525755721710304814125 

noncomputable def Ns60p761 := @Enclosure.Real.IsNear.mulLit_tt qz76 qz77 Ns60p760 Ns60p422 

noncomputable def Ns60p762 := nat_lit 74430435427210034723956118257264903982042364884111092489479792146081420090323786742543854991 

noncomputable def Ns60p763 := nat_lit 23945242826029513411849172299223580994042798784118784000000000000000000000000000000000000000000000 

noncomputable def Ns60p764 := nat_lit 47007696940066026467540946383503624621687225 

noncomputable def Ns60p765 := nat_lit 237150563177155574716474547049699493395371122139903996342511 

noncomputable def Ns60p766 := nat_lit 83076749736557242056487941267521536000000000000000000000000000000 

noncomputable abbrev qz82 := qz399

noncomputable def Ns60p767 := @Enclosure.Real.IsNear.mulLit_ft qz82 qz78 Ns60p764 Ns60p427 Ns60p765 Ns60p766 

noncomputable def Ns60p768 := nat_lit 566707583656526557151086931 

noncomputable def Ns60p769 := nat_lit 288230376151711744000000000000000 

noncomputable def Ns60p770 := @Enclosure.Real.IsNear.mulLit_tt qz78 qz78 6856215934468956504085 9444732965739290427392 Ns60p768 Ns60p769 6856215934468956504085 9444732965739290427392 

noncomputable abbrev qz719 := (@HSub.hSub Real Real Real qz920 qz963 qz932)

noncomputable abbrev qz403 := qz719

noncomputable abbrev qz83 := qz403

noncomputable def Ns60p771 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz83 884279719003555 140737488355328 1 500000000000000 7753447 67108864 21 67108864 

noncomputable abbrev qz720 := qz963

noncomputable abbrev qz404 := qz720

noncomputable abbrev qz84 := qz404

noncomputable def Ns60p772 := @Enclosure.Real.IsNear.subLit_ff_n qz84 qz348 59355417 67108864 21 67108864 1 1 0 1 7753447 

noncomputable def Ns60p773 := @Enclosure.Real.IsNear.mulLit_ff qz0 qz64 2 1 0 1 59355417 134217728 21 134217728 59355417 67108864 21 

noncomputable def Ns60p774 := @Enclosure.Real.IsNear.recentre' qz77 Bool.true 62525317 67108864 

noncomputable def Ns60p775 := @Enclosure.Real.IsNear.sin_image qz72 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 130360831)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true 130360831 67108864 

noncomputable def Ns60p776 := nat_lit 4924892959376160983157679310605 

noncomputable def Ns60p777 := nat_lit 143336546140594412621601869998169093 

noncomputable def Ns60p778 := @Enclosure.Real.IsNear.recentre' qz72 Bool.true Ns60p776 Ns60p440 Ns60p777 

noncomputable def Ns60p779 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz73 884279719003555 140737488355328 1 500000000000000 5569383593831311 

noncomputable def Ns60p780 := @Enclosure.Real.IsNear.subLit_tf qz74 qz23 4443483686988687 18014398509481984 5311500243 18014398509481984 1 16 

noncomputable def Ns60p781 := @Enclosure.Real.IsNear.subLit_ff_n qz75 qz64 3523065527243889 18014398509481984 2492927955 18014398509481984 59355417 134217728 21 134217728 

noncomputable def Ns60p782 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz64 59355417 134217728 21 134217728 59355417 134217728 21 134217728 3523065527243889 18014398509481984 

noncomputable def Ns60p783 := nat_lit 6193960567797066632497635526729842544927074595938657123626710706422093324966176168679804371178529372161 

noncomputable def Ns60p784 := nat_lit 24086042211974442574543304360740679598967862801619648214165885160603832368217844926647473395087361 

noncomputable def Ns60p785 := nat_lit 30879984271565338190378043501470535101537113417474353821646376980769943985174466291396246845159767685121 

noncomputable def Ns60p786 := BSN.sin_dyadic_bound_f 130360831 67108864 4 3 67108864 17475728 Ns60p783 Ns60p109 Ns60p784 Ns60p785 Ns60p112 Ns60p784 62525317 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 130360831) qz339 0 3 Ns60p783 Ns60p109 Ns60p784 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 130360831) (BSN.sinOddQ 67108864) 0 3 Ns60p785 Ns60p112 Ns60p784 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p787 := @Ns60p774 2251574864 1172776253652992 62525317 67108864 140723429 73298515853312 (@Ns60p775 125 67108864 Bool.true 62525317 67108864 1 17475728 (@Ns60p778 Ns60p443 130360831 67108864 125 67108864 (@Ns60p779 18014398509481984 5311500243 18014398509481984 Ns60p776 Ns60p440 Ns60p777 Ns60p443 RS061to078.d39 (@Ns60p780 0 1 89110137501300976 5569383593831311 18014398509481984 5311500243 18014398509481984 (@Ns60p781 596394284872684730843136 4443483686988687 18014398509481984 5311500243 18014398509481984 (@Ns60p782 2492927955 18014398509481984 (Ns60p717 rfl rfl) (Ns60p717 rfl rfl) rfl) (Ns60p717 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 130360831 67108864) (BSN.sin_neg_of_bound 130360831 67108864 Bool.false 62525317 67108864 1 17475728 (Ns60p786 rfl rfl)) rfl rfl) 

noncomputable def Ns60p788 := nat_lit 18188438099879715357907629877461066525 

noncomputable def Ns60p789 := nat_lit 45879640767688435169057002248912700408207788931410831 

noncomputable def Ns60p790 := @Enclosure.Real.IsNear.mulLit_tt qz964 qz68 Ns60p788 Ns60p456 Ns60p789 

noncomputable def Ns60p791 := nat_lit 618970019642690137449562112000000000000000000000000000000 

noncomputable def Ns60p792 := nat_lit 1700122750969579671453260793 

noncomputable abbrev qz968 := (@HMul.hMul Real Real Real qz5 qz317 qz78)

noncomputable def Ns60p793 := @Enclosure.Real.IsNear.mulLit_tf qz968 qz372 20568647803406869512255 9444732965739290427392 Ns60p792 Ns60p769 884279719003555 

noncomputable def Ns60p794 := @Enclosure.Real.IsNear.mulLit_ft qz317 qz78 3 1 0 1 6856215934468956504085 9444732965739290427392 Ns60p768 

noncomputable def Ns60p795 := @Enclosure.Real.IsNear.recentre' qz68 Bool.true 24375896 67108864 

noncomputable def Ns60p796 := @Enclosure.Real.IsNear.cos_image qz72 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 130360831)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true 130360831 67108864 

noncomputable def Ns60p797 := nat_lit 2391238972289668452135590718364601084070514938828130465041188118270846785875655063069687334230865623041 

noncomputable def Ns60p798 := nat_lit 14425449950566918628633138920944151347259985220866798385880931068861177042269392615251891263943704459265 

noncomputable def Ns60p799 := BSN.cos_dyadic_bound_t 130360831 67108864 4 3 67108864 17475728 Ns60p797 Ns60p219 Ns60p784 Ns60p798 Ns60p222 Ns60p784 24375896 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 130360831) qz338 0 3 Ns60p797 Ns60p219 Ns60p784 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 130360831) (BSN.cosOddQ 67108864) 0 3 Ns60p798 Ns60p222 Ns60p784 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p800 := @Ns60p795 2251574864 1172776253652992 3046987 8388608 140723429 73298515853312 (@Ns60p796 125 67108864 Bool.true 24375896 67108864 1 17475728 (@Ns60p778 Ns60p443 130360831 67108864 125 67108864 (@Ns60p779 18014398509481984 5311500243 18014398509481984 Ns60p776 Ns60p440 Ns60p777 Ns60p443 RS061to078.d39 (@Ns60p780 0 1 89110137501300976 5569383593831311 18014398509481984 5311500243 18014398509481984 (@Ns60p781 596394284872684730843136 4443483686988687 18014398509481984 5311500243 18014398509481984 (@Ns60p782 2492927955 18014398509481984 (Ns60p717 rfl rfl) (Ns60p717 rfl rfl) rfl) (Ns60p717 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 130360831 67108864) (BSN.cos_neg_of_bound 130360831 67108864 Bool.true 24375896 67108864 1 17475728 (Ns60p799 rfl rfl)) rfl rfl) 

noncomputable abbrev qz405 := (@Ns60p771 6856215934468956504085 9444732965739290427392 Ns60p768 Ns60p769 RS061to078.d39 (@Ns60p772 7753447 67108864 21 67108864 (@Ns60p773 67108864 qz916 (Ns60p717 rfl rfl) rfl) qz933 rfl rfl) rfl)

noncomputable def Ns60p801 := @Ns60p752 Ns60p753 Ns60p744 Ns60p754 Ns60p746 Ns60p755 Ns60p756 Ns60p757 Ns60p758 Ns60p759 Ns60p743 Ns60p744 Ns60p745 Ns60p746 (@Ns60p761 Ns60p762 Ns60p763 62525317 67108864 140723429 73298515853312 Ns60p753 Ns60p744 Ns60p754 Ns60p746 (@Ns60p767 6856215934468956504085 9444732965739290427392 Ns60p768 Ns60p769 Ns60p760 Ns60p422 Ns60p762 Ns60p763 (@Ns60p770 Ns60p768 Ns60p769 Ns60p764 Ns60p427 Ns60p765 Ns60p766 qz405 qz405 rfl) qz405 rfl) (Ns60p787 rfl) rfl) (@Ns60p790 Ns60p791 3046987 8388608 140723429 73298515853312 Ns60p755 Ns60p756 Ns60p757 Ns60p758 (@Ns60p793 70368744177664 1 250000000000000 Ns60p788 Ns60p456 Ns60p789 Ns60p791 (@Ns60p794 Ns60p769 20568647803406869512255 9444732965739290427392 Ns60p792 Ns60p769 qz696 qz405 rfl) RS061to078.d41 rfl) (Ns60p800 rfl) rfl) rfl rfl 

noncomputable def Ns60p802 := nat_lit 497587383373293472960663533144729 

noncomputable def Ns60p803 := nat_lit 25185178274825005862748160000000000000 

noncomputable def Ns60p804 := nat_lit 202548136357325479606339148070810506905298573206991315335149552492869783715 

noncomputable def Ns60p805 := @Enclosure.Real.IsNear.mulLit_tf qz965 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz64) 126417577460886713614515 18889465931478580854784 Ns60p802 Ns60p803 Ns60p804 

noncomputable def Ns60p806 := nat_lit 2874847063526909283488880123569308338915590062324411985119646567775842285083447668843925277920081112770809849 

noncomputable def Ns60p807 := nat_lit 13722237922858944809063857409007217094694074912448858270611535009669361099418579763200000000000000000000000000000 

noncomputable def Ns60p808 := nat_lit 165862461124431157653554511048243 

noncomputable def Ns60p809 := @Enclosure.Real.IsNear.mulLit_ft qz317 qz79 3 1 0 1 42139192486962237871505 18889465931478580854784 Ns60p808 

noncomputable def Ns60p810 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz81 884279719003555 140737488355328 1 500000000000000 47653691 134217728 153655597 146597031706624 42139192486962237871505 

noncomputable def Ns60p811 := @Enclosure.Real.IsNear.recentre' qz81 Bool.false 47653691 134217728 2458489552 2345552507305984 47653691 134217728 153655597 146597031706624 

noncomputable def Ns60p812 := @Enclosure.Real.IsNear.sin_image qz71 qz718 Bool.false 372941083 134217728 133 134217728 Bool.false 47653691 134217728 1 

noncomputable def Ns60p813 := nat_lit 7913684747763327849826038089350745115445220544926150785923078132611473798033691480166049851667567961361557078731270507870700610580082543586897601 

noncomputable def Ns60p814 := nat_lit 89128169441165970827302651621490378947238189464423027349434945482712296455469718197740245810578915820879397137775633729548228565880070657907097600 

noncomputable def Ns60p815 := nat_lit 1793714220212841362070422427800474870669247663353858155884291792197666433931228889990353115387707293238957145321890156302984963250975600321 

noncomputable def Ns60p816 := nat_lit 47969183187052214170230503910755734252753603566736090784025600653837908057472684179357661273205697607912854837981911712506665395225940619669991105 

noncomputable def Ns60p817 := nat_lit 8110663419146103345284541297555624484198675241262495488798580038926818977447744355994362368762681339700025139537582669388888799495086429869545881600 

noncomputable def Ns60p818 := BSN.cos_dyadic_bound_f 332006131439 274877906944 4 3 134217728 34985589 Ns60p813 Ns60p814 Ns60p815 Ns60p816 Ns60p817 Ns60p815 47653691 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 332006131439) (BSN.cosEvenQ 274877906944) 0 3 Ns60p813 Ns60p814 Ns60p815 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 332006131439) (BSN.cosOddQ 274877906944) 0 3 Ns60p816 Ns60p817 Ns60p815 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p819 := @Ns60p812 17475728 (Ns60p718 rfl) (Enclosure.sfrac_false_div 372941083 134217728) (BSN.sin_reduce1 qz718 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns60p719) qz692) 226375608064910080 72057594037927936 Bool.false 47653691 134217728 0 1000000000000000 34951456 17475728 (BSN.sin_reduce_arg_pos_rat_q1 372941083 134217728 226375608064910080 72057594037927936 0 Ns60p719 Ns60p379 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 47653691 134217728 Ns60p719 Ns60p379 332006131439 274877906944 34985589 34951456 (Ns60p818 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable abbrev qz85 := (@HMul.hMul Real Real Real qz323 qz320 qz401)

noncomputable abbrev qz721 := (@Enclosure.Real.IsNear.neg qz85 Bool.false 42139192486962237871505 18889465931478580854784 Ns60p808 Ns60p803 (@Ns60p810 18889465931478580854784 Ns60p808 Ns60p803 RS061to078.d39 (Ns60p811 (Ns60p819 rfl rfl) rfl) rfl))

noncomputable def Ns60p820 := @Ns60p809 Ns60p803 126417577460886713614515 18889465931478580854784 Ns60p802 Ns60p803 qz696 qz721 rfl 

noncomputable abbrev qz86 := (@HMul.hMul Real Real Real qz323 qz399 (Real.cos qz394))

noncomputable def Ns60p821 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz86) (@HMul.hMul Real Real Real qz5 qz372 qz77) 

noncomputable abbrev qz969 := (@HMul.hMul Real Real Real qz5 qz0 qz79)

noncomputable def Ns60p822 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz64) (@HMul.hMul Real Real Real qz5 qz67 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns60p821 (@HMul.hMul Real Real Real qz5 qz969 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c8 1 Zeta.RiemannSiegel.correction qz64))) (@HMul.hMul Real Real Real qz5 qz80 qz63))) 

noncomputable def Ns60p823 := @Enclosure.Real.IsNear.mulLit_tt qz67 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns60p821 (@HMul.hMul Real Real Real qz5 qz969 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 1 Zeta.RiemannSiegel.correction qz64))) (@HMul.hMul Real Real Real qz5 qz80 qz63)) 35892921 

noncomputable def Ns60p824 := nat_lit 5643122117515191355040152571333230497046996348026155779719058041915 

noncomputable def Ns60p825 := nat_lit 78549607707984364990484934348069428544256849988486250804335425702924272930877767581029764884285932801 

noncomputable def Ns60p826 := nat_lit 408954558457700753482099098235583814820470658315684147793398350765388044697600000000000000000000000000000 

noncomputable def Ns60p827 := nat_lit 18519245439408899786633274988122105233544525887055447333600079238085 

noncomputable def Ns60p828 := @Enclosure.Real.IsNear.subLit_ff_n (@HSub.hSub Real Real Real qz11 Ns60p821 (@HMul.hMul Real Real Real qz5 qz969 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz64))) (@HMul.hMul Real Real Real qz5 qz80 qz63) Ns60p827 Ns60p394 

noncomputable def Ns60p829 := nat_lit 171807336875609306024151366122139166459644565335899097399455756435527845117582286657641118747145787653 

noncomputable def Ns60p830 := nat_lit 2044772792288503767410495491177919074102353291578420738966991753826940223488000000000000000000000000000000 

noncomputable def Ns60p831 := nat_lit 670640419778825467902278677485998096568828925475625 

noncomputable def Ns60p832 := nat_lit 46768052394588893382517914646921056628989841375232 

noncomputable def Ns60p833 := nat_lit 1437310634281483323572673082136963164844116073654129659967873491249285974085606923 

noncomputable def Ns60p834 := nat_lit 13302092628958221876068264024568402087845299924722778112000000000000000000000000000000 

noncomputable def Ns60p835 := nat_lit 263917830861013891655198889502338390277505448421624885159034397106881086732841199310097698500215890229428772698849280 

noncomputable def Ns60p836 := nat_lit 8904261412950311170347093831391212673717556716441395 

noncomputable def Ns60p837 := nat_lit 19923279630258685534430987083249750629802189057308428620085629515810944599 

noncomputable def Ns60p838 := nat_lit 761175307200834315804655693002798057273797115904000000000000000000000000000000 

noncomputable def Ns60p839 := @Enclosure.Real.IsNear.subLit_ff_p Ns60p821 (@HMul.hMul Real Real Real qz5 qz969 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz64)) Ns60p836 Ns60p503 Ns60p837 Ns60p838 

noncomputable def Ns60p840 := nat_lit 1531368751277354009747496875356086348749064044083788257687088802875 

noncomputable def Ns60p841 := nat_lit 946293674561194262246724253735089469583695531804113346629223541994121360540292587980340154254682409 

noncomputable def Ns60p842 := nat_lit 16358182338308030139283963929423352592818826332627365911735934030615521787904000000000000000000000000000 

noncomputable def Ns60p843 := nat_lit 13857744656296429419194454352760795863865349319513666408673189342165026523560443600155206580355216467070563634401771520 

noncomputable def Ns60p844 := @Enclosure.Real.IsNear.subLit_ft (@Neg.neg Real Real.instNeg qz86) (@HMul.hMul Real Real Real qz5 qz372 qz77) 

noncomputable def Ns60p845 := nat_lit 143231841476320961788253185598232558675160892641075 

noncomputable def Ns60p846 := nat_lit 1559343098047313712542565280800634458147697351240418349365629515810944599 

noncomputable def Ns60p847 := nat_lit 759514613479976268944209734603111 

noncomputable def Ns60p848 := nat_lit 31481472843531257328435200000000000000 

noncomputable def Ns60p849 := nat_lit 42049185651226058521587528475037016433190166711268510198739067031435345920 

noncomputable def Ns60p850 := @Enclosure.Real.IsNear.neg qz86 Bool.true Ns60p845 

noncomputable def Ns60p851 := @Enclosure.Real.IsNear.mulLit_ft qz82 qz68 Ns60p764 Ns60p427 Ns60p765 

noncomputable def Ns60p852 := @Enclosure.Real.IsNear.mulLit_ft qz372 qz77 884279719003555 70368744177664 1 

noncomputable def Ns60p853 := nat_lit 12592589137412502931374080000000000000 

noncomputable def Ns60p854 := nat_lit 36340723703975953525386019285621583151288075 

noncomputable def Ns60p855 := @Enclosure.Real.IsNear.mulLit_tt qz969 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz64) 42139192486962237871505 9444732965739290427392 Ns60p808 Ns60p853 Ns60p854 

noncomputable def Ns60p856 := nat_lit 178405961588244985132285746181186892047843328 

noncomputable def Ns60p857 := nat_lit 16061594543611614008326187625885072884652378172834785577849263 

noncomputable def Ns60p858 := nat_lit 1299032483296701355084791408649258016391142570773708800000000000000 

noncomputable def Ns60p859 := @Enclosure.Real.IsNear.mulLit_ft qz0 qz79 2 1 0 1 42139192486962237871505 18889465931478580854784 Ns60p808 

noncomputable def Ns60p860 := @Ns60p859 Ns60p803 42139192486962237871505 9444732965739290427392 Ns60p808 Ns60p853 qz321 qz721 rfl 

noncomputable abbrev qz87 := (@HMul.hMul Real Real Real qz323 qz400 (Real.sin qz394))

noncomputable def Ns60p861 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz87) (@HMul.hMul Real Real Real qz5 qz79 qz63) 

noncomputable def Ns60p862 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz64) (@HMul.hMul Real Real Real qz5 qz67 Ns60p861) Bool.true Ns60p854 Ns60p856 Ns60p857 Ns60p858 (BSN.deriv_correction_mk qz64 qz402) 

noncomputable def Ns60p863 := nat_lit 1012476073038913537446172722627439075 

noncomputable def Ns60p864 := nat_lit 5316911983139663491615228241121378304 

noncomputable def Ns60p865 := nat_lit 439167484312791950088225436051006266319230160894557537 

noncomputable def Ns60p866 := @Enclosure.Real.IsNear.mulLit_tf qz67 Ns60p861 35892921 33554432 81 67108864 Ns60p863 Ns60p864 Ns60p865 

noncomputable def Ns60p867 := nat_lit 38714184859296719881438952942170441639159398400000000000000 

noncomputable def Ns60p868 := @Enclosure.Real.IsNear.subLit_tt_p (@Neg.neg Real Real.instNeg qz87) (@HMul.hMul Real Real Real qz5 qz79 qz63) 

noncomputable def Ns60p869 := nat_lit 428687074723122732077126419945 

noncomputable def Ns60p870 := nat_lit 633825300114114700748351602688 

noncomputable def Ns60p871 := nat_lit 13629215429734090267722849035501243135823 

noncomputable def Ns60p872 := nat_lit 4225371759152464855605922339225600000000000000 

noncomputable def Ns60p873 := nat_lit 4608563897557898672730212025989425635 

noncomputable def Ns60p874 := nat_lit 62858465281444171560712754700137674296560882539901613 

noncomputable def Ns60p875 := nat_lit 7742836971859343976287790588434088327831879680000000000000 

noncomputable def Ns60p876 := nat_lit 641732950852249688635583458364685618672513781321815014101326233600 

noncomputable def Ns60p877 := @Enclosure.Real.IsNear.neg qz87 Bool.false Ns60p869 

noncomputable def Ns60p878 := @Enclosure.Real.IsNear.mulLit_tt qz78 qz77 6856215934468956504085 9444732965739290427392 Ns60p768 

noncomputable def Ns60p879 := @Enclosure.Real.IsNear.mulLit_tf qz79 qz63 42139192486962237871505 18889465931478580854784 Ns60p808 Ns60p803 109365263679027 281474976710656 

noncomputable def Ns60p880 := @Enclosure.Real.IsNear.of_eq qz63 (@HMul.hMul Real Real Real qz5 qz67 qz68) Bool.false 109365263679027 

noncomputable def Ns60p881 := @Enclosure.Real.IsNear.mulLit_tt qz67 qz68 35892921 33554432 81 

noncomputable abbrev qz406 := (@Ns60p880 281474976710656 12258518037767175 4918980131801758957568 (BSN.correction_mk qz64 (BSN.cos_two_pi_p_ne_zero_mk qz61 260767 1000 6 qz66 rfl rfl qz967)) (@Ns60p881 67108864 3046987 8388608 140723429 73298515853312 109365263679027 281474976710656 12258518037767175 4918980131801758957568 Ns60p726 (Ns60p800 rfl) rfl))

noncomputable def Ns60p882 := @Ns60p879 12258518037767175 4918980131801758957568 Ns60p873 Ns60p864 Ns60p874 Ns60p875 qz721 qz406 

noncomputable def Ns60p883 := @Ns60p855 Ns60p856 Ns60p857 Ns60p858 Ns60p840 Ns60p394 Ns60p841 Ns60p842 Ns60p860 (Ns60p862 (@Ns60p866 Ns60p867 Ns60p854 Ns60p856 Ns60p857 Ns60p858 Ns60p726 (@Ns60p868 Ns60p869 Ns60p870 Ns60p871 Ns60p872 Ns60p873 Ns60p864 Ns60p874 Ns60p875 Ns60p876 Ns60p863 Ns60p864 Ns60p865 Ns60p867 (@Ns60p877 Ns60p870 Ns60p871 Ns60p872 (@Ns60p878 Ns60p769 62525317 67108864 140723429 73298515853312 Ns60p869 Ns60p870 Ns60p871 Ns60p872 qz405 (Ns60p787 rfl) rfl)) (Ns60p882 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns60p884 := @Ns60p839 Ns60p840 Ns60p394 Ns60p841 Ns60p842 Ns60p843 Ns60p827 Ns60p394 Ns60p829 Ns60p830 (@Ns60p844 Ns60p845 Ns60p503 Ns60p846 Ns60p838 55289869747368200501935 4722366482869645213696 Ns60p847 Ns60p848 Ns60p849 Ns60p836 Ns60p503 Ns60p837 Ns60p838 (@Ns60p850 Ns60p503 Ns60p846 Ns60p838 (@Ns60p851 Ns60p766 3046987 8388608 140723429 73298515853312 Ns60p845 Ns60p503 Ns60p846 Ns60p838 (@Ns60p770 Ns60p768 Ns60p769 Ns60p764 Ns60p427 Ns60p765 Ns60p766 qz405 qz405 rfl) (Ns60p800 rfl) rfl)) (@Ns60p852 250000000000000 62525317 67108864 140723429 73298515853312 55289869747368200501935 4722366482869645213696 Ns60p847 Ns60p848 RS061to078.d41 (Ns60p787 rfl) rfl) rfl rfl) Ns60p883 

noncomputable def Ns60p885 := nat_lit 6132115419636978615892324045089901875 

noncomputable def Ns60p886 := nat_lit 111899422137309874266080382681639103421666533289632582805533 

noncomputable def Ns60p887 := @Enclosure.Real.IsNear.mulLit_ff qz80 qz63 Ns60p885 Ns60p555 Ns60p886 Ns60p557 109365263679027 281474976710656 

noncomputable def Ns60p888 := @Enclosure.Real.IsNear.mulLit_ft qz47 qz70 Ns60p313 Ns60p317 Ns60p315 Ns60p318 7842075 8388608 153655597 146597031706624 Ns60p885 

noncomputable abbrev qz88 := (@HMul.hMul Real Real Real qz323 qz683 qz393)

noncomputable def Ns60p889 := @Ns60p887 12258518037767175 4918980131801758957568 Ns60p831 Ns60p832 Ns60p833 Ns60p834 (@Enclosure.Real.IsNear.neg qz88 Bool.true Ns60p885 Ns60p555 Ns60p886 Ns60p557 (@Ns60p888 Ns60p555 Ns60p886 Ns60p557 RS061to078.d43 (Ns60p711 (Ns60p724 rfl rfl) rfl) rfl)) qz406 

noncomputable def Ns60p890 := nat_lit 18396346258910935847676972135269705625 

noncomputable def Ns60p891 := nat_lit 335698266411929622798241148044917310264999599868897748416599 

noncomputable def Ns60p892 := @Enclosure.Real.IsNear.mulLit_ft qz966 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz64) Ns60p890 Ns60p555 Ns60p891 Ns60p557 Ns60p854 

noncomputable def Ns60p893 := @Enclosure.Real.IsNear.mulLit_ff qz317 qz80 3 1 0 1 Ns60p885 Ns60p555 Ns60p886 

noncomputable def Ns60p894 := @Ns60p893 Ns60p557 Ns60p890 Ns60p555 Ns60p891 Ns60p557 qz696 (@Enclosure.Real.IsNear.neg qz88 Bool.true Ns60p885 Ns60p555 Ns60p886 Ns60p557 (@Ns60p888 Ns60p555 Ns60p886 Ns60p557 RS061to078.d43 (Ns60p711 (Ns60p724 rfl rfl) rfl) rfl)) rfl 

noncomputable def Ns60p895 := @Ns60p892 Ns60p856 Ns60p857 Ns60p858 Ns60p738 Ns60p739 Ns60p740 Ns60p741 Ns60p894 (Ns60p862 (@Ns60p866 Ns60p867 Ns60p854 Ns60p856 Ns60p857 Ns60p858 Ns60p726 (@Ns60p868 Ns60p869 Ns60p870 Ns60p871 Ns60p872 Ns60p873 Ns60p864 Ns60p874 Ns60p875 Ns60p876 Ns60p863 Ns60p864 Ns60p865 Ns60p867 (@Ns60p877 Ns60p870 Ns60p871 Ns60p872 (@Ns60p878 Ns60p769 62525317 67108864 140723429 73298515853312 Ns60p869 Ns60p870 Ns60p871 Ns60p872 qz405 (Ns60p787 rfl) rfl)) (Ns60p882 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns60p896 := @Ns60p736 Ns60p737 Ns60p708 Ns60p738 Ns60p739 Ns60p740 Ns60p741 Ns60p742 Ns60p728 Ns60p705 Ns60p729 Ns60p708 (@Ns60p747 Ns60p748 Ns60p705 Ns60p749 Ns60p750 Ns60p751 Ns60p735 Ns60p705 Ns60p737 Ns60p708 Ns60p801 (@Ns60p805 Ns60p744 Ns60p806 Ns60p807 Ns60p748 Ns60p705 Ns60p749 Ns60p750 Ns60p820 (@Ns60p822 Bool.false Ns60p804 Ns60p744 Ns60p806 Ns60p807 (BSN.iteratedDeriv_two_correction_mk qz64 qz402) (@Ns60p823 33554432 81 67108864 Ns60p824 Ns60p394 Ns60p825 Ns60p826 Ns60p804 Ns60p744 Ns60p806 Ns60p807 Ns60p726 (@Ns60p828 Ns60p829 Ns60p830 Ns60p831 Ns60p832 Ns60p833 Ns60p834 Ns60p835 Ns60p824 Ns60p394 Ns60p825 Ns60p826 (Ns60p884 rfl rfl) (Ns60p889 rfl) rfl rfl) rfl)) rfl) rfl rfl) Ns60p895 

noncomputable def Ns60p897 := nat_lit 32950767752202301027185659123264563159736721476977625 

noncomputable def Ns60p898 := nat_lit 120789049731523147631200255971952519202674975556680606036426611196043217021462114627 

noncomputable def Ns60p899 := nat_lit 464584538086446725954990046998778111129026560000000000000000000000000000000000000000000 

noncomputable def Ns60p900 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz684 RSCompact.c11) qz81) qz63 Ns60p897 Ns60p569 Ns60p898 Ns60p899 109365263679027 281474976710656 12258518037767175 

noncomputable def Ns60p901 := @Enclosure.Real.IsNear.mulLit_ff qz685 qz81 Ns60p319 Ns60p320 Ns60p321 Ns60p322 47653691 134217728 153655597 146597031706624 Ns60p897 

noncomputable def Ns60p902 := Ns60p703 (@Ns60p707 Ns60p708 Ns60p696 Ns60p697 Ns60p698 Ns60p699 Ns60p726 (@Ns60p727 Ns60p728 Ns60p705 Ns60p729 Ns60p708 Ns60p730 Ns60p731 Ns60p732 Ns60p733 Ns60p734 Ns60p704 Ns60p705 Ns60p706 Ns60p708 (Ns60p896 rfl rfl) (@Ns60p900 4918980131801758957568 Ns60p730 Ns60p731 Ns60p732 Ns60p733 (@Ns60p901 Ns60p569 Ns60p898 Ns60p899 RS061to078.d44 (Ns60p811 (Ns60p819 rfl rfl) rfl) rfl) qz406 rfl) rfl rfl) rfl) 

noncomputable def Ns60p903 := @Enclosure.Real.IsNear.of_eq qz716 (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz64) qz374)) Bool.false Ns60p691 Ns60p692 Ns60p693 Ns60p694 (BSN.correctionLinear_mk qz64) (@Enclosure.Real.IsNear.neg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz64) qz374) Bool.true Ns60p691 Ns60p692 Ns60p693 Ns60p694 (@Ns60p700 Ns60p692 Ns60p693 Ns60p694 Ns60p902 RS061to078.d45 rfl)) 

noncomputable def Ns60p904 := @Enclosure.Real.IsNear.inv_image qz65 54041373 8388608 21 8388608 651063 651064 4194304 qz710 rfl 

noncomputable def Ns60p905 := @Ns60p695 Ns60p643 Ns60p653 Ns60p646 Ns60p903 (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz65) Bool.false 1302127 8388608 1 8388608 1302127 8388608 1 8388608 (Ns60p904 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns60p906 := @Ns60p645 Ns60p646 Ns60p585 Ns60p581 Ns60p587 Ns60p583 (Ns60p647 qz25 (@Enclosure.Real.IsNear.of_eq qz961 (@Inv.inv Real Real.instInv (Real.sqrt qz65)) Bool.false 1652501 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz62 (BSN.t_div_two_pi_nonneg qz61 260767 1000 qz66)) Ns60p651) rfl) (@Ns60p654 Ns60p655 Ns60p642 Ns60p643 Ns60p644 Ns60p646 (@Ns60p656 8796093022208 763716222875879 19214766139850620928 (BSN.correction_mk qz64 qz402) (@Ns60p657 4194304 761749 2097152 280354625 9162314481664 3417663825149 8796093022208 763716222875879 19214766139850620928 Ns60p674 (Ns60p690 rfl) rfl)) (Ns60p905 rfl) rfl rfl) 

noncomputable def Ns60p907 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz61) (hardyZApproximantRS qz61) Bool.true Ns60p580 Ns60p581 Ns60p582 Ns60p583 (@Eq.refl Real (hardyZApproximantRS qz61)) (Ns60p584 (BSN.hardyZApproximantRS_eq qz61 6 qz967) (@Ns60p586 Ns60p587 Ns60p583 Ns60p588 Ns60p580 Ns60p581 Ns60p582 Ns60p583 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz61) qz61 6) (@HAdd.hAdd Real Real Real qz336 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz61) qz61 6)) Bool.false 476141 8388608 23349 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz61) qz61 6) (Ns60p641 (Ns60p640 rfl rfl rfl rfl) rfl rfl)) (Ns60p906 rfl) rfl rfl)) 

theorem RS061to078.d48 : Enclosure.Real.IsNear (hardyZApproximantRS qz61) Bool.true Ns60p580 Ns60p581 Ns60p582 Ns60p583 := Ns60p907 

noncomputable def Ns60p908 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) qz41 Bool.false 16188607 268435456 

theorem RS061to078.d49 : Enclosure.Real.IsNear (hardyZErrorBoundRS qz4) Bool.false 16188607 268435456 201 268435456 := @Ns60p908 201 268435456 (BSN.hardyZErrorBoundRS_mk qz4 257388 1000 qz10 rfl rfl) (@Ns60p284 7 268435456 1 268435456 543199512756224 16188607 268435456 201 268435456 (@Ns60p285 33554432 25 33554432 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns60p286 (Ns60p292 rfl rfl rfl rfl) rfl) rfl) (@Ns60p293 8388608 1 8388608 7 268435456 1 268435456 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns60p294 7 8388608 1 8388608 (@Ns60p298 4194304 (@Ns60p302 17592186044416000 Ns60p295 Ns60p296 Ns60p297 Ns60p296 (@Ns60p303 Ns60p300 Ns60p301 Ns60p300 (Ns60p291 rfl) (Ns60p291 rfl) rfl) (Ns60p291 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) 

noncomputable def Ns60p909 := nat_lit 952807701979977590676009436833121607873478776074997756509426003607196479720536826940925320839422505060658801014874348387801207233 

noncomputable def Ns60p910 := nat_lit 173291855882550928723650886508942731464777317210988535948154973788413831737851601439998400381508723631086950685087723239310884864 

noncomputable def Ns60p911 := nat_lit 8448852287609617191389991137835750994104823393900258848130927020195103507197873894169874121709562252652012180731475627680053572920716650926463379507263492534826943903739663852371 

noncomputable def Ns60p912 := nat_lit 5965566027664272664830720566066920962690754576421073698769110719627097071925417199303090118671480762527770709699679581497353728056298045440000000000000000000000000000000000000000000 

noncomputable abbrev qz970 := (Enclosure.sfrac Bool.false 262452 1000)

noncomputable abbrev qz722 := qz970

noncomputable abbrev qz407 := qz722

noncomputable abbrev qz89 := qz407

noncomputable abbrev qz971 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 262452 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz723 := qz971

noncomputable abbrev qz408 := qz723

noncomputable abbrev qz90 := qz408

noncomputable abbrev qz972 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 262452 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz724 := qz972

noncomputable abbrev qz409 := qz724

noncomputable abbrev qz91 := (Zeta.RiemannSiegel.correction qz409)

noncomputable abbrev qz92 := qz409

noncomputable abbrev qz973 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 262452 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz725 := qz973

noncomputable abbrev qz410 := qz725

noncomputable abbrev qz93 := qz410

noncomputable abbrev qz726 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz326 qz90 qz8))

noncomputable abbrev qz727 := (@HAdd.hAdd Real Real Real qz336 qz91 (@HMul.hMul Real Real Real qz5 (Zeta.RiemannSiegel.correctionLinear qz92) (@Inv.inv Real Real.instInv qz93)))

noncomputable def Ns60p913 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz89) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz89) qz89 6) (@HMul.hMul Real Real Real qz5 qz726 qz727)) Bool.false Ns60p909 Ns60p910 Ns60p911 Ns60p912 

noncomputable def Ns60p914 := nat_lit 26269790141349912420281211933584740632875895427950278272818201021121567863778101815698022000039220899728730472229055553269427775 

noncomputable def Ns60p915 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz89) qz89 6) (@HMul.hMul Real Real Real qz5 qz726 qz727) 189578379 33554432 47001 33554432 Ns60p914 Ns60p910 

noncomputable def Ns60p916 := nat_lit 92651566755558940017752223891049079096154618152039211576001193013967212667049060525110334091930479908317662922482764681892180340026730926463379507263492534826943903739663852371 

noncomputable def Ns60p917 := nat_lit 31970921245163423427861992679575274339121308195251739120948092197069428989422131963085046695184585365327531613855132311522785237617606656 

noncomputable def Ns60p918 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz89) qz89 Real.sin BSN.quadSignPos 5 6 262452 1000 71 67108864 33554432 1125899906842624 Bool.false 24034495669 1045 120242927 63 27397080 8 

noncomputable def Ns60p919 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz89) qz89 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 262452 1000 3 40 67108864 33554432 1125899906842624 Bool.false 24034495669 1045 

noncomputable def Ns60p920 := Ns60p919 93032624 62 33554424 8 108007536 62 30011992 8 Bool.false 142298691 23390 Bool.true 65859493 Bool.true 95723886 3537118876014220 1 Bool.false 55785376 Bool.false Bool.false 9656829 Bool.false Bool.false 174510036 

noncomputable def Ns60p921 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz89) qz89 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 262452 1000 112 44 67108864 33554432 1125899906842624 Bool.false 24034495669 1045 

noncomputable def Ns60p922 := Ns60p921 46516304 62 47453136 16 73726608 62 38745320 8 Bool.false 67108856 1118 Bool.false 19790660 Bool.false 46568235 3537118876014220 1 Bool.false 64211781 Bool.false Bool.false 51589561 Bool.false Bool.false 142298691 

noncomputable def Ns60p923 := nat_lit 8043387996172515523745547777189969878433428039933 

noncomputable def Ns60p924 := nat_lit 22458662688689253660830853468964046717845504000 

noncomputable def Ns60p925 := nat_lit 597715700308537448159806095360000 

noncomputable def Ns60p926 := nat_lit 941231680094279735104542603812536320 

noncomputable abbrev qz94 := (@Eq.refl Real qz407)

noncomputable def Ns60p927 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz89 262452 1000 275525209216 16000000 524904 4000 2000 Ns60p925 Ns60p926 qz94 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns60p928 := nat_lit 759069325032713247404431035541327486972338921636070686720 

noncomputable abbrev qz974 := (Real.log (Enclosure.sfrac Bool.false 275525209216 16000000))

noncomputable abbrev qz975 := (@HSub.hSub Real Real Real qz11 qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 524904))))

noncomputable abbrev qz728 := (@HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 262452 4000) qz974) (@HMul.hMul Real Real Real qz5 qz12 qz975))

noncomputable abbrev qz976 := (Enclosure.sfrac Bool.false 262452 2000)

noncomputable abbrev qz411 := (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 qz728 qz976) (@HMul.hMul Real Real Real qz5 qz976 (Real.log Real.pi)))

noncomputable def Ns60p929 := @Enclosure.Real.IsNear.addLit_ft_p qz411 (Enclosure.sfrac Bool.true Ns60p925 Ns60p926) 806465280570223163221 2251799813685248000 4350648844436109939761 Ns60p72 Ns60p925 Ns60p926 0 1 Ns60p928 

noncomputable def Ns60p930 := nat_lit 108241937669017897420495781888 

noncomputable abbrev qz412 := (@HSub.hSub Real Real Real qz11 qz728 qz976)

noncomputable def Ns60p931 := @Enclosure.Real.IsNear.subLit_ff_p qz412 (@HMul.hMul Real Real Real qz5 qz976 (Real.log Real.pi)) 9157814988564636089 18014398509481984 8451626003442102731 1092233000000000000000000 2520245261493 16777216000 65613 8388608000 Ns60p930 806465280570223163221 2251799813685248000 

noncomputable def Ns60p932 := nat_lit 2289453747141159022250000 

noncomputable abbrev qz413 := qz728

noncomputable def Ns60p933 := @Enclosure.Real.IsNear.subLit_ff_p qz413 qz976 1440221555921239865173 2251799813685248000 8451626003442102731 1092233000000000000000000 262452 2000 0 1 Ns60p932 9157814988564636089 18014398509481984 8451626003442102731 1092233000000000000000000 

noncomputable def Ns60p934 := nat_lit 3243090631288925911876624387779067904 

noncomputable def Ns60p935 := nat_lit 11791675864973758643044352 

noncomputable def Ns60p936 := BSN.log_dyadic_bound 13381209216 537669209216 2 1 867264535616876338003968 33554432 8737864 179056760082363334656 179056760082363334656 1670512 551050418432 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 13381209216) (BSN.artanhQ 537669209216) 0 1 179056760082363334656 867264535616876338003968 179056760082363334656 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz729 := qz974

noncomputable def Ns60p937 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 262452 4000) qz729 262452 4000 0 1 21963707851197121 2251799813685248 62500007645631 546116500000000000000 1441104763240596700173 2251799813685248000 4100813001652786803 546116500000000000000000 (Enclosure.Real.IsNear.const Bool.false 262452 4000) (BSN.isNear_log_sfrac 275525209216 16000000 21963707851197121 2251799813685248 62500007645631 546116500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 275525209216) qz650)) Bool.false Ns60p935 Ns60p84 1000000122330096 8737864000000000000000 21963707851197121 2251799813685248 62500007645631 546116500000000000000 (BSN.log_rat_reduce_isNear 275525209216 16000000 14 551050418432 524288000000 1670512 33554432 24973259072661432 36028797018963968 8737864 1000000000000000 rfl rfl rfl rfl (Ns60p936 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p938 := BSN.arctan_dyadic_bound_f 1000 524904 1 0 4194304 1092233 0 1 1 0 1 1 7990 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 524904) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 524904) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz977 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 524904)))

noncomputable abbrev qz730 := qz977

noncomputable abbrev qz414 := qz730

noncomputable def Ns60p939 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz414 884279719003555 562949953421312 1 2000000000000000 7990 4194304 1 1092233 3704439992407650467840 883207319356835 562949953421312 2000000001092233 2184466000000000000000 qz15 (Ns60p938 rfl) rfl rfl 

noncomputable abbrev qz731 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 262452 4000) qz974)

noncomputable abbrev qz415 := qz731

noncomputable abbrev qz732 := (@HMul.hMul Real Real Real qz5 qz12 qz975)

noncomputable abbrev qz416 := qz732

noncomputable abbrev qz733 := qz975

noncomputable abbrev qz417 := qz733

noncomputable def Ns60p940 := @Enclosure.Real.IsNear.subLit_ff_p qz415 qz416 1441104763240596700173 2251799813685248000 4100813001652786803 546116500000000000000000 883207319356835 2251799813685248 2000000001092233 8737864000000000000000 Ns60p934 1440221555921239865173 2251799813685248000 8451626003442102731 1092233000000000000000000 (Ns60p937 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz12 qz417 1 4 0 1 883207319356835 562949953421312 2000000001092233 2184466000000000000000 883207319356835 2251799813685248 2000000001092233 8737864000000000000000 qz335 Ns60p939 rfl) 

noncomputable def Ns60p941 := @Ns60p929 Ns60p923 Ns60p924 4350648844436109939761 Ns60p72 (@Ns60p931 4350648844436109939761 Ns60p72 (Ns60p933 (Ns60p940 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 262452 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz976 (Real.log Real.pi) 262452 2000 0 1 38410761 33554432 1 16777216 2520245261493 16777216000 65613 8388608000 (Enclosure.Real.IsNear.const Bool.false 262452 2000) RS061to078.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns60p925 Ns60p926) 

noncomputable def Ns60p942 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz89) Bool.false Ns60p923 Ns60p924 4350648844436109939761 Ns60p72 1502155979 4194304 33 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz89) (@HAdd.hAdd Real Real Real qz336 qz411 (Enclosure.sfrac Bool.true Ns60p925 Ns60p926)) Bool.false Ns60p923 Ns60p924 4350648844436109939761 Ns60p72 Ns60p927 (Ns60p941 rfl rfl)) 

noncomputable def Ns60p943 := nat_lit 140107374270529369033716140981830721387899081804634468894522847788734063298715604954785 

noncomputable def Ns60p944 := nat_lit 281741739077528739882316540650482778683118821079131171192764594825769351830597742241 

noncomputable def Ns60p945 := nat_lit 366491731702403777128494713886598726755201117111343110922771553912204634450815140441761 

noncomputable def Ns60p946 := BSN.sin_dyadic_bound_f 26991772131 17179869184 3 2 8388608 2186600 Ns60p943 Ns60p94 Ns60p944 Ns60p945 Ns60p97 Ns60p944 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26991772131) qz655 0 2 Ns60p943 Ns60p94 Ns60p944 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26991772131) qz656 0 2 Ns60p945 Ns60p97 Ns60p944 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p947 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz89) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1502155979) qz660) Bool.false 1502155979 4194304 33 2097152 Bool.false 8388607 8388608 1 1092233 (Ns60p942 rfl) (Enclosure.sfrac_false_div 1502155979 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1502155979) qz660) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949688553994197609218048) qz709) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 56 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q3 1502155979 4194304 226375608064910080 72057594037927936 56 949688553994197609218048 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 949688553994197609218048 604462909807314587353088 26991772131 17179869184 2186600 2184466 (Ns60p946 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p948 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz89) Bool.false Ns60p923 Ns60p924 4350648844436109939761 Ns60p72 24034495669 67108864 1045 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz89) (@HAdd.hAdd Real Real Real qz336 qz411 (Enclosure.sfrac Bool.true Ns60p925 Ns60p926)) Bool.false Ns60p923 Ns60p924 4350648844436109939761 Ns60p72 Ns60p927 (Ns60p941 rfl rfl)) 

noncomputable def Ns60p949 := Ns60p922 23390 BSN.abs_quadSignPos (BSN.cos_quad_nat0 112 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 64211781 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 44 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 51589561 67108864) qz94 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz89) qz89 1) Bool.false 8388607 8388608 38140841 2290578620416 67108856 67108864 1118 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz89) qz89 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz89)) Bool.false 8388607 8388608 38140841 2290578620416 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz89) qz89) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz89)) Bool.false 8388607 8388608 38140841 2290578620416 8388607 8388608 38140841 2290578620416 (Ns60p947 rfl rfl) rfl)) rfl) (Ns60p948 rfl) RS061to078.d7 

noncomputable def Ns60p950 := nat_lit 153405563769424738133107360000 

noncomputable def Ns60p951 := BSN.cos_dyadic_bound_f 19790660 67108864 2 1 67108864 33554432 Ns60p950 Ns60p630 Ns60p950 Ns60p950 Ns60p631 Ns60p950 64211781 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 19790660) qz338 0 1 Ns60p950 Ns60p630 Ns60p950 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 19790660) (BSN.cosOddQ 67108864) 0 1 Ns60p950 Ns60p631 Ns60p950 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p952 := nat_lit 160268391372511090897095659120081752709863582842953778268351190625 

noncomputable def Ns60p953 := nat_lit 22116592856511263969738052123274959793487354007251467250390625 

noncomputable def Ns60p954 := nat_lit 480760940931820250163347501255998708210003773820846831870552790625 

noncomputable def Ns60p955 := BSN.cos_dyadic_bound_f 46568235 67108864 3 2 67108864 33554432 Ns60p952 Ns60p103 Ns60p953 Ns60p954 Ns60p106 Ns60p953 51589561 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 46568235) qz338 0 2 Ns60p952 Ns60p103 Ns60p953 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 46568235) (BSN.cosOddQ 67108864) 0 2 Ns60p954 Ns60p106 Ns60p953 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p956 := nat_lit 1154271742450634812202817602007565909217092326080675793490975874785 

noncomputable def Ns60p957 := nat_lit 353954195754987398441924838284008394386609514629257945787096801 

noncomputable def Ns60p958 := nat_lit 3022519590101392623790854412662593748644330152901893993897471991521 

noncomputable def Ns60p959 := BSN.sin_dyadic_bound_f 65859493 67108864 3 2 67108864 33554432 Ns60p956 Ns60p119 Ns60p957 Ns60p958 Ns60p122 Ns60p957 55785376 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 65859493) qz339 0 2 Ns60p956 Ns60p119 Ns60p957 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 65859493) (BSN.sinOddQ 67108864) 0 2 Ns60p958 Ns60p122 Ns60p957 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p960 := nat_lit 691059259218513590477794565592052709487217542787358941308674578634965038748059348300574480484848766976 

noncomputable def Ns60p961 := nat_lit 591893881523968698887594519876751912138040404454597061506663086659717939009457155998282858500096 

noncomputable def Ns60p962 := nat_lit 4185553162685968867543474998428562852605382087737036156588343717629490140566574314761318351508955074560 

noncomputable def Ns60p963 := BSN.cos_dyadic_bound_f 95723886 67108864 4 3 67108864 33554432 Ns60p960 Ns60p219 Ns60p961 Ns60p962 Ns60p222 Ns60p961 9656829 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 95723886) qz338 0 3 Ns60p960 Ns60p219 Ns60p961 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 95723886) (BSN.cosOddQ 67108864) 0 3 Ns60p962 Ns60p222 Ns60p961 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p964 := Ns60p920 39813 BSN.abs_quadSignPos (BSN.cos_quad_nat3 3 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 55785376 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 40 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 9656829 67108864) qz94 rfl rfl (Ns60p949 RS061to078.d9 RS061to078.d11 RS061to078.d13 RS061to078.d17 (Ns60p951 rfl rfl) (Ns60p955 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns60p948 rfl) RS061to078.d19 RS061to078.d21 RS061to078.d23 RS061to078.d25 RS061to078.d17 (Ns60p959 rfl rfl) (Ns60p963 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns60p965 := nat_lit 143090132260358649675781193268253967123367465717599686475256954880 

noncomputable def Ns60p966 := nat_lit 5442314833455157058630738306196854746343956874784730110754816 

noncomputable def Ns60p967 := nat_lit 374751058838828012229903437364359880891611186663535241681684135936 

noncomputable def Ns60p968 := BSN.sin_dyadic_bound_f 39081656 67108864 3 2 67108864 33554432 Ns60p965 Ns60p119 Ns60p966 Ns60p967 Ns60p122 Ns60p966 36909752 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 39081656) qz339 0 2 Ns60p965 Ns60p119 Ns60p966 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 39081656) (BSN.sinOddQ 67108864) 0 2 Ns60p967 Ns60p122 Ns60p966 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p969 := Ns60p918 Bool.false 174510036 39813 Bool.true 39081656 3537118876014220 1 Bool.false 36909752 Bool.false Bool.false 189578379 47001 BSN.abs_quadSignPos qz927 (BSN.sfrac_eq_quadSignPos_mul Bool.false 36909752 67108864) qz94 rfl (Ns60p964 rfl rfl) (Ns60p948 rfl) RS061to078.d27 RS061to078.d29 RS061to078.d17 (Ns60p968 rfl rfl) rfl 

noncomputable def Ns60p970 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz89) qz89 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz89) qz89 6) 189578379 67108864 47001 67108864 189578379 67108864 47001 67108864 25444779307302912 189578379 33554432 47001 33554432 (Ns60p969 rfl rfl rfl rfl) 

noncomputable def Ns60p971 := nat_lit 31845219289301536050459634235987131656093002151660920588539024974660080012241295609759021773041565070750690638532726834775 

noncomputable def Ns60p972 := nat_lit 82631996098781074868989413504096379978550585370535152410581099409300723904538918228148651304964410605948901503127919788032 

noncomputable def Ns60p973 := nat_lit 111651146781904162090038629776730174121299174345233740675237623885452262171921097768315351686292235130075203696408171332390186422151081788714693338361746226200098759502219 

noncomputable def Ns60p974 := @Enclosure.Real.IsNear.mulLit_ff qz726 qz727 824921 2097152 1 4194304 Ns60p971 Ns60p972 Ns60p973 

noncomputable def Ns60p975 := nat_lit 2844603551704536755004272730859241944642426765642678117165141448796795402491291618014855441413631802810559611177291670559574951198720000000000000000000000000000000000000000000 

noncomputable abbrev qz734 := (@HPow.hPow Real Real Real qz326 qz90 qz8)

noncomputable def Ns60p976 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz734 1 1 0 1 824921 2097152 1 4194304 824921 2097152 1 4194304 

noncomputable def Ns60p977 := @Enclosure.Real.IsNear.sqrt_image qz90 87599194557 2097152000 65613 2097152000 27107835 27107856 4194304 (@Enclosure.Real.IsNear.of_eq qz90 (@HMul.hMul Real Real Real qz5 qz89 qz3) Bool.false 87599194557 2097152000 65613 2097152000 (BSN.t_div_two_pi_mk qz89 262452 1000 qz94) (@Enclosure.Real.IsNear.mulLit_ff qz89 qz3 262452 1000 0 1 1335089 8388608 1 8388608 87599194557 2097152000 65613 2097152000 (Enclosure.Real.IsNear.const Bool.false 262452 1000) RS061to078.d32 rfl)) 

noncomputable abbrev qz735 := (@Enclosure.Real.IsNear.recentre' qz93 Bool.false 54215691 8388608 21 8388608 54215691 8388608 21 8388608 (Ns60p977 rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns60p978 := @Enclosure.Real.IsNear.sqrt_image qz93 54215691 8388608 21 8388608 10662949 10662955 4194304 qz735 rfl 

noncomputable def Ns60p979 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz93) 1332869 524288 3 4194304 1649841 1649843 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz93) Bool.false 21325904 8388608 6 8388608 1332869 524288 3 4194304 (Ns60p978 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns60p980 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz93)) Bool.false 3299684 8388608 2 8388608 824921 2097152 1 4194304 (Ns60p979 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns60p981 := nat_lit 25298563783221923145979961304768650151433649689575089689196280179538901605492612580076079953703062511584339296643532375 

noncomputable def Ns60p982 := nat_lit 1052495643585612195688946319938208925683742694226647077043666244667648258880035198031714785365847358182009719542913951569112502151081788714693338361746226200098759502219 

noncomputable abbrev qz736 := (@HMul.hMul Real Real Real qz5 (Zeta.RiemannSiegel.correctionLinear qz92) (@Inv.inv Real Real.instInv qz93))

noncomputable def Ns60p983 := @Enclosure.Real.IsNear.addLit_ff qz91 qz736 6774397228075 17592186044416 373536624415079 9607383069925310464 Ns60p981 Ns60p972 Ns60p982 Ns60p975 

noncomputable def Ns60p984 := nat_lit 560227022362617692239008296188668627926080566787445907492979444473414747624733263071573512012453709527163463523989172965622663243366400 

noncomputable abbrev qz737 := (@HMul.hMul Real Real Real qz918 qz915 qz972)

noncomputable abbrev qz418 := (Real.cos qz737)

noncomputable abbrev qz95 := (@Inv.inv Real Real.instInv qz418)

noncomputable abbrev qz738 := (@HSub.hSub Real Real Real qz920 (@HMul.hMul Real Real Real qz918 qz972 qz972) qz972)

noncomputable abbrev qz419 := (@HMul.hMul Real Real Real qz644 qz642 (@HSub.hSub Real Real Real qz647 qz738 qz930))

noncomputable abbrev qz96 := (Real.cos qz419)

noncomputable def Ns60p985 := @Enclosure.Real.IsNear.of_eq qz91 (@HMul.hMul Real Real Real qz5 qz95 qz96) Bool.false 6774397228075 

noncomputable def Ns60p986 := @Enclosure.Real.IsNear.mulLit_tt qz95 qz96 4310167 4194304 75 

noncomputable abbrev qz97 := (@Neg.neg Real Real.instNeg qz418)

noncomputable abbrev qz98 := qz418

noncomputable abbrev qz978 := (@Inv.inv Real Real.instInv qz97)

noncomputable def Ns60p987 := @Enclosure.Real.IsNear.of_eq qz95 (@Neg.neg Real Real.instNeg qz978) Bool.true 4310167 4194304 75 4194304 (BSN.inv_eq_neg_inv_neg qz98) 

noncomputable def Ns60p988 := @Enclosure.Real.IsNear.recentre' qz978 Bool.false 8620334 8388608 150 8388608 4310167 4194304 

noncomputable def Ns60p989 := @Enclosure.Real.IsNear.recentre' qz98 Bool.true 8163111 8388608 153655597 9162314481664 8163111 8388608 153655597 9162314481664 

noncomputable abbrev qz420 := qz737

noncomputable abbrev qz99 := qz420

noncomputable def Ns60p990 := @Enclosure.Real.IsNear.cos_image qz99 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24404161) qz337) Bool.false 24404161 8388608 133 8388608 Bool.true 8163111 8388608 1 

noncomputable def Ns60p991 := nat_lit 566707583623288629881063763 

noncomputable def Ns60p992 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz92 884279719003555 140737488355328 1 500000000000000 3884043 8388608 21 8388608 3434580452637724772865 1180591620717411303424 Ns60p991 

noncomputable def Ns60p993 := @Enclosure.Real.IsNear.subLit_ff_p qz93 qz1 54215691 8388608 21 8388608 6 1 0 1 3884043 3884043 8388608 21 

noncomputable def Ns60p994 := @Ns60p993 8388608 qz735 qz345 

noncomputable def Ns60p995 := @Enclosure.Real.IsNear.recentre' qz99 Bool.false 3434580452637724772865 1180591620717411303424 Ns60p991 Ns60p144 24404161 8388608 133 8388608 (@Ns60p992 Ns60p144 RS061to078.d31 (Ns60p994 rfl rfl) rfl) 

noncomputable def Ns60p996 := nat_lit 1618034015530297696714752 

noncomputable def Ns60p997 := nat_lit 73714544267570839232173159569215920227979667920317608745845411815732465170209261175040 

noncomputable def Ns60p998 := nat_lit 78138087094178832571571844464883660749864141808863775994092888386778163180041093376 

noncomputable def Ns60p999 := nat_lit 192935392369294956069623349218812836574923159752188910125604690079054053657780379402496 

noncomputable def Ns60p1000 := BSN.sin_dyadic_bound_f 22993646318 17179869184 3 2 8388608 2186600 Ns60p997 Ns60p94 Ns60p998 Ns60p999 Ns60p97 Ns60p998 8163111 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 22993646318) qz655 0 2 Ns60p997 Ns60p94 Ns60p998 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 22993646318) qz656 0 2 Ns60p999 Ns60p97 Ns60p998 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1001 := @Ns60p990 1092233 (Ns60p995 rfl) (Enclosure.sfrac_false_div 24404161 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24404161) qz337) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns60p996) qz657) 226375608064910080 72057594037927936 Bool.false 8163111 8388608 0 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q1 24404161 8388608 226375608064910080 72057594037927936 0 Ns60p996 Ns60p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8163111 8388608 Ns60p996 Ns60p84 22993646318 17179869184 2186600 2184466 (Ns60p1000 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p1002 := @Enclosure.Real.IsNear.inv_image qz97 8163111 8388608 153655597 9162314481664 4310092 4310242 4194304 (@Enclosure.Real.IsNear.neg qz98 Bool.true 8163111 8388608 153655597 9162314481664 (Ns60p989 (Ns60p1001 rfl rfl) rfl)) 

noncomputable def Ns60p1003 := Ns60p987 (@Enclosure.Real.IsNear.neg qz978 Bool.false 4310167 4194304 75 4194304 (@Ns60p988 75 4194304 (Ns60p1002 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p1004 := @Enclosure.Real.IsNear.recentre' qz96 Bool.true 1571725 4194304 

noncomputable abbrev qz100 := qz419

noncomputable def Ns60p1005 := @Enclosure.Real.IsNear.cos_image qz100 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16398891)) qz337) Bool.true 16398891 8388608 

noncomputable def Ns60p1006 := nat_lit 19360394229639663246603603445 

noncomputable def Ns60p1007 := nat_lit 9156132916589162138182539806697713 

noncomputable def Ns60p1008 := @Enclosure.Real.IsNear.recentre' qz100 Bool.true Ns60p1006 Ns60p159 Ns60p1007 

noncomputable abbrev qz421 := (@HSub.hSub Real Real Real qz647 qz738 qz930)

noncomputable abbrev qz101 := qz421

noncomputable def Ns60p1009 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz101 884279719003555 140737488355328 1 500000000000000 21893970667399 

noncomputable abbrev qz422 := qz738

noncomputable abbrev qz102 := qz422

noncomputable def Ns60p1010 := @Enclosure.Real.IsNear.subLit_tf qz102 qz23 17495924156295 70368744177664 339291015 70368744177664 1 16 

noncomputable abbrev qz739 := (@HMul.hMul Real Real Real qz918 qz972 qz972)

noncomputable abbrev qz423 := qz739

noncomputable abbrev qz103 := qz423

noncomputable def Ns60p1011 := @Enclosure.Real.IsNear.subLit_ff_n qz103 qz92 15085790025849 70368744177664 163130247 70368744177664 3884043 8388608 21 8388608 

noncomputable def Ns60p1012 := @Enclosure.Real.IsNear.mulLit_ff qz92 qz92 3884043 8388608 21 8388608 3884043 8388608 21 8388608 15085790025849 70368744177664 

noncomputable def Ns60p1013 := nat_lit 35699868518293299331424650905311693967021912591419678199336050663871518232543813588798079761 

noncomputable def Ns60p1014 := nat_lit 378245483159351791711354159510623785114944219250093768993956955486942395466008829035281 

noncomputable def Ns60p1015 := nat_lit 215332912412580981284508695818957147222373362893174622679175909500087201472425372417170801425 

noncomputable def Ns60p1016 := BSN.cos_dyadic_bound_t 16398891 8388608 4 3 4194304 1092233 Ns60p1013 Ns60p274 Ns60p1014 Ns60p1015 Ns60p277 Ns60p1014 1571725 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16398891) (BSN.cosEvenQ 8388608) 0 3 Ns60p1013 Ns60p274 Ns60p1014 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16398891) (BSN.cosOddQ 8388608) 0 3 Ns60p1015 Ns60p277 Ns60p1014 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1017 := @Ns60p1004 286908023 9162314481664 1571725 4194304 286908023 9162314481664 (@Ns60p1005 255 8388608 Bool.true 1571725 4194304 1 1092233 (@Ns60p1008 Ns60p162 16398891 8388608 255 8388608 (@Ns60p1009 70368744177664 339291015 70368744177664 Ns60p1006 Ns60p159 Ns60p1007 Ns60p162 RS061to078.d31 (@Ns60p1010 0 1 350303530678384 21893970667399 70368744177664 339291015 70368744177664 (@Ns60p1011 146766449344889487360 17495924156295 70368744177664 339291015 70368744177664 (@Ns60p1012 163130247 70368744177664 (Ns60p994 rfl rfl) (Ns60p994 rfl rfl) rfl) (Ns60p994 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16398891 8388608) (BSN.cos_neg_of_bound 16398891 8388608 Bool.true 1571725 4194304 1 1092233 (Ns60p1016 rfl rfl)) rfl rfl) 

noncomputable def Ns60p1018 := nat_lit 19491304907713003245894814405869488791427075413732280349566182268330302845424108322393760543586389914167392274875 

noncomputable def Ns60p1019 := nat_lit 9850501549098619803069760025035903451269934817616361666987073351061430442874302652853566563721228910201656997576704 

noncomputable def Ns60p1020 := nat_lit 810378781256419785526642722672023027286790195674307071895265971166844004009142909916226480630466948678493235044392351013865663803904530596008059609781189411103007 

noncomputable def Ns60p1021 := nat_lit 339103168452326864600690928800015681343367906289419903417246514415358949004565670253617220093444800711936904332314928836771840000000000000000000000000000000000000000000 

noncomputable abbrev qz740 := (Zeta.RiemannSiegel.correctionLinear qz92)

noncomputable def Ns60p1022 := @Enclosure.Real.IsNear.mulLit_ff qz740 (@Inv.inv Real Real.instInv qz93) Ns60p1018 Ns60p1019 Ns60p1020 Ns60p1021 1297941 8388608 1 8388608 Ns60p981 

noncomputable def Ns60p1023 := nat_lit 137595070541611097551796341909467861040591537401838810292228285706532701140247981549755822469672447631725875 

noncomputable def Ns60p1024 := nat_lit 73391955711682288371546268649666782105490079653384995959602842860381532034831513858240593699524021969747968 

noncomputable def Ns60p1025 := nat_lit 267299958794054230462029599197693688856276767832341841383385934427957545103053245867780271651743381309019154166410685012394452660599837050411829524709730796313 

noncomputable def Ns60p1026 := nat_lit 118746227899636049838606071871524579995410826769491549287815289031877149665464360281229088786184084664739925441285980160000000000000000000000000000000000000000000 

noncomputable def Ns60p1027 := @Enclosure.Real.IsNear.mulLit_tf (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz92) qz374 Ns60p1023 Ns60p1024 Ns60p1025 Ns60p1026 141657 134217728 1 134217728 Ns60p1018 

noncomputable abbrev qz979 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 262452 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 6 1)))

noncomputable abbrev qz741 := (@HMul.hMul Real Real Real qz918 qz915 (@HSub.hSub Real Real Real qz920 qz979 qz932))

noncomputable abbrev qz424 := (@HMul.hMul Real Real Real qz644 qz741 qz741)

noncomputable abbrev qz425 := qz741

noncomputable abbrev qz104 := (@HMul.hMul Real Real Real qz323 qz424 qz425)

noncomputable abbrev qz105 := (Real.sin qz419)

noncomputable abbrev qz106 := qz425

noncomputable abbrev qz980 := (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz317 qz106) qz372)

noncomputable def Ns60p1028 := @HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 qz104 qz105) (@HMul.hMul Real Real Real qz5 qz980 qz96) 

noncomputable abbrev qz426 := (Real.sin qz737)

noncomputable abbrev qz107 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz323 qz320 qz426))

noncomputable abbrev qz108 := (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz323 qz683 qz418))

noncomputable abbrev qz109 := qz426

noncomputable abbrev qz981 := (@HMul.hMul Real Real Real qz5 qz317 qz107)

noncomputable abbrev qz982 := (@HMul.hMul Real Real Real qz5 qz317 qz108)

noncomputable def Ns60p1029 := @HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns60p1028 (@HMul.hMul Real Real Real qz5 qz981 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz92))) (@HMul.hMul Real Real Real qz5 qz982 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz92))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz690 qz109) qz91) 

noncomputable abbrev qz983 := (@BSN.floor_sqrt_eq_dec qz89 262452 1000 6 qz94 rfl rfl rfl)

noncomputable abbrev qz427 := (BSN.cos_two_pi_p_ne_zero_mk qz89 262452 1000 6 qz94 rfl rfl qz983)

noncomputable def Ns60p1030 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 3 Zeta.RiemannSiegel.correction qz92) (@HMul.hMul Real Real Real qz5 qz95 Ns60p1029) Bool.true Ns60p1023 Ns60p1024 Ns60p1025 Ns60p1026 (BSN.iteratedDeriv_three_correction_mk qz92 qz427) 

noncomputable def Ns60p1031 := nat_lit 997603603171776040203388949741111220441655788411417114366831520331905772385814116297673557033938825 

noncomputable def Ns60p1032 := nat_lit 546812681195752981093125556779405341338292357723303109106442651602488249799843980805878294255763456 

noncomputable def Ns60p1033 := nat_lit 1936255341023463819977644952220435330349631583685719435194993948020493443969349316079199860870707635372210970506242534517712458766510070578209738502427 

noncomputable def Ns60p1034 := @Enclosure.Real.IsNear.mulLit_tf qz95 Ns60p1029 137925595 134217728 149 134217728 Ns60p1031 Ns60p1032 Ns60p1033 

noncomputable def Ns60p1035 := nat_lit 884728341546923293460950790878568440641543468605663994608933396874943000565948786446668869154036675875931422720000000000000000000000000000000000000000000 

noncomputable def Ns60p1036 := @Enclosure.Real.IsNear.of_eq qz95 (@Neg.neg Real Real.instNeg qz978) Bool.true 137925595 134217728 149 134217728 (BSN.inv_eq_neg_inv_neg qz98) 

noncomputable def Ns60p1037 := @Enclosure.Real.IsNear.recentre' qz978 Bool.false 137925595 134217728 149 134217728 137925595 134217728 

noncomputable def Ns60p1038 := @Enclosure.Real.IsNear.recentre' qz98 Bool.true 130609540 134217728 2458489552 2345552507305984 32652385 33554432 153655597 146597031706624 

noncomputable abbrev qz742 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 390465503) qz949)

noncomputable def Ns60p1039 := @Enclosure.Real.IsNear.cos_image qz99 qz742 Bool.false 390465503 134217728 133 134217728 Bool.true 130609540 134217728 1 

noncomputable def Ns60p1040 := nat_lit 566707584123742273660111187 

noncomputable def Ns60p1041 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz92 884279719003555 140737488355328 1 500000000000000 62144515 134217728 21 134217728 54953134261812208750825 18889465931478580854784 Ns60p1040 

noncomputable def Ns60p1042 := @Enclosure.Real.IsNear.subLit_ff_p qz93 qz1 867450883 134217728 21 134217728 6 1 0 1 62144515 62144515 134217728 21 

noncomputable def Ns60p1043 := @Enclosure.Real.IsNear.sqrt_image qz90 280317304479 6710886400 65613 33554432000 433725431 433725452 67108864 (@Enclosure.Real.IsNear.of_eq qz90 (@HMul.hMul Real Real Real qz5 qz89 qz3) Bool.false 280317304479 6710886400 65613 33554432000 (BSN.t_div_two_pi_mk qz89 262452 1000 qz94) (@Enclosure.Real.IsNear.mulLit_ff qz89 qz3 262452 1000 0 1 21361415 134217728 1 134217728 280317304479 6710886400 65613 33554432000 (Enclosure.Real.IsNear.const Bool.false 262452 1000) RS061to078.d40 rfl)) 

noncomputable def Ns60p1044 := @Ns60p1042 134217728 (@Enclosure.Real.IsNear.recentre' qz93 Bool.false 867450883 134217728 21 134217728 867450883 134217728 21 134217728 (Ns60p1043 rfl rfl rfl rfl rfl rfl) rfl) qz345 

noncomputable def Ns60p1045 := @Enclosure.Real.IsNear.recentre' qz99 Bool.false 54953134261812208750825 18889465931478580854784 Ns60p1040 Ns60p372 390465503 134217728 133 134217728 (@Ns60p1041 Ns60p372 RS061to078.d39 (Ns60p1044 rfl rfl) rfl) 

noncomputable def Ns60p1046 := nat_lit 25888389612887957754085376 

noncomputable def Ns60p1047 := nat_lit 316593984563244894047660639003182667831151361990329949718920043064250291188001331974543173477505 

noncomputable def Ns60p1048 := nat_lit 335584492406041952430887772012352137907338147290040249074501341048089067220601767667881731201 

noncomputable def Ns60p1049 := nat_lit 828631394201745892678032617186982226572594067260013612670098539187530047002598704690436502971521 

noncomputable def Ns60p1050 := BSN.sin_dyadic_bound_f 367896143599 274877906944 3 2 134217728 34985589 Ns60p1047 Ns60p381 Ns60p1048 Ns60p1049 Ns60p384 Ns60p1048 130609540 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 367896143599) (BSN.sinEvenQ 274877906944) 0 2 Ns60p1047 Ns60p381 Ns60p1048 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 367896143599) (BSN.sinOddQ 274877906944) 0 2 Ns60p1049 Ns60p384 Ns60p1048 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1051 := @Ns60p1039 17475728 (Ns60p1045 rfl) (Enclosure.sfrac_false_div 390465503 134217728) (BSN.cos_reduce1 qz742 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns60p1046) qz692) 226375608064910080 72057594037927936 Bool.false 130609540 134217728 0 1000000000000000 34951456 17475728 (BSN.sin_reduce_arg_pos_rat_q1 390465503 134217728 226375608064910080 72057594037927936 0 Ns60p1046 Ns60p379 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 130609540 134217728 Ns60p1046 Ns60p379 367896143599 274877906944 34985589 34951456 (Ns60p1050 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p1052 := @Enclosure.Real.IsNear.inv_image qz97 32652385 33554432 153655597 146597031706624 68962723 68962872 67108864 (@Enclosure.Real.IsNear.neg qz98 Bool.true 32652385 33554432 153655597 146597031706624 (Ns60p1038 (Ns60p1051 rfl rfl) rfl)) 

noncomputable def Ns60p1053 := Ns60p1036 (@Enclosure.Real.IsNear.neg qz978 Bool.false 137925595 134217728 149 134217728 (@Ns60p1037 149 134217728 (Ns60p1052 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p1054 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns60p1028 (@HMul.hMul Real Real Real qz5 qz981 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 2 Zeta.RiemannSiegel.correction qz92))) (@HMul.hMul Real Real Real qz5 qz982 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz92))) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz690 qz109) qz91) 

noncomputable def Ns60p1055 := nat_lit 13027037667141326589989589222880421665389058291995189515576875328704491362379645396637681583801298825 

noncomputable def Ns60p1056 := nat_lit 8624992727675742020855324667635721398135817142726206356187483572207525074480275484604141934324599442385031280033491224327694653336534589726862704080263 

noncomputable def Ns60p1057 := nat_lit 4423641707734616467304753954392842203207717343028319973044666984374715002829743932233344345770183379379657113600000000000000000000000000000000000000000000 

noncomputable def Ns60p1058 := nat_lit 74137111289058550622709741908976356802703065022771092067909796541875 

noncomputable def Ns60p1059 := nat_lit 3369993333393829974333376885877453834204643052817571560137951281152 

noncomputable def Ns60p1060 := nat_lit 5456831811288538056792001248472454449330255950419062246184729781801299604183460371816531841112521833118141 

noncomputable def Ns60p1061 := nat_lit 22852821123895290203209983619605850992909472913598237542921850060800000000000000000000000000000000000000000000 

noncomputable def Ns60p1062 := nat_lit 3361917492058549110686585582646074436508385129533776356390384317803989011534799842724972407891558618167689170678042018549943578822703914098071028289721802053543526400 

noncomputable def Ns60p1063 := nat_lit 4846480329427924886504015509578553370933656559235172071930146273395623086226301950949777973330898825 

noncomputable def Ns60p1064 := @Enclosure.Real.IsNear.subLit_ft (@HSub.hSub Real Real Real qz11 Ns60p1028 (@HMul.hMul Real Real Real qz5 qz981 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 2 Zeta.RiemannSiegel.correction qz92))) (@HMul.hMul Real Real Real qz5 qz982 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz92)) Ns60p1063 Ns60p1032 

noncomputable def Ns60p1065 := nat_lit 776344842759428369750273405932279324809795021863754385141767220772631832390193652289459270829655011815408164601217007105101264007843124552192024949019 

noncomputable def Ns60p1066 := nat_lit 227056077764892275213814246495654622216992017190718074028019908697475178653661471875 

noncomputable def Ns60p1067 := nat_lit 15177100720513508366558296147058741458143803430094840009779784451085189728165691392 

noncomputable def Ns60p1068 := nat_lit 120534856484092011191679401454925927696351506130417256734758059612603035683714655583722326100054577591940041550536881851039232197 

noncomputable def Ns60p1069 := nat_lit 112412573064060475875851119894587122439733861682781046952849694799211406126437005420134400000000000000000000000000000000000000000000 

noncomputable def Ns60p1070 := nat_lit 197712662764127240964233278832534692378054380176053720882638574272440122950223073604330432732931095174154064698757412039533629178836010557591587119072671809249501509221271453722214400 

noncomputable def Ns60p1071 := nat_lit 91494896036126114926897325307668337348769911098488675649730573383067024525 

noncomputable def Ns60p1072 := nat_lit 14134776518227074636666380005943348126619871175004951664972849610340958208 

noncomputable def Ns60p1073 := nat_lit 111359620911314202355670755934155071459980662327658281639572213163761459958856687345038728372327902244129 

noncomputable def Ns60p1074 := nat_lit 1755150760895129725626023882004065052840633342508361166879727812608000000000000000000000000000000000000000000 

noncomputable def Ns60p1075 := @Enclosure.Real.IsNear.subLit_tt_p Ns60p1028 (@HMul.hMul Real Real Real qz5 qz981 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 2 Zeta.RiemannSiegel.correction qz92)) Ns60p1071 Ns60p1072 Ns60p1073 Ns60p1074 

noncomputable def Ns60p1076 := nat_lit 8386017679220854471009584853803761066325915281295761129280493750493160942622580966463353380081823625 

noncomputable def Ns60p1077 := nat_lit 720211196055532576072240068194050887381918033579294082098353224997115590512554532771338136693430270222827701583601125753770174187805941679944834789659 

noncomputable def Ns60p1078 := nat_lit 68503916356447249819140377260065481270732756327451551975094196535406192802047867449926444464334829332823839980112790137282277492697846597104284973403690318635483304401305600 

noncomputable def Ns60p1079 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz5 qz104 qz105) (@HMul.hMul Real Real Real qz5 qz980 qz96) 

noncomputable def Ns60p1080 := nat_lit 1315887295225129409223371799764336906515990366707194959195758255210709875 

noncomputable def Ns60p1081 := nat_lit 2418521235117764532318174020872071510353526218557396994000112424347479491245127475964091572327902244129 

noncomputable def Ns60p1082 := nat_lit 292859194212163745062427998291644249751728225 

noncomputable def Ns60p1083 := nat_lit 44601490397061246283071436545296723011960832 

noncomputable def Ns60p1084 := nat_lit 56321228476472883951751266848026034817235739871565747393345212123 

noncomputable def Ns60p1085 := nat_lit 907391675950091261630839935544488498298880000000000000000000000000000 

noncomputable def Ns60p1086 := nat_lit 4080808726935396002295149649258561382585387148715933654418397826449647839119204127769154868585358296341667900083404800 

noncomputable def Ns60p1087 := nat_lit 84597184564187176708591406296275643967070256374387394762520202375 

noncomputable def Ns60p1088 := @Enclosure.Real.IsNear.mulLit_tt qz104 qz105 Ns60p1087 Ns60p422 

noncomputable def Ns60p1089 := nat_lit 244104717824200689466903438432147389792321059352247104073358441493785859092508216246956937 

noncomputable def Ns60p1090 := nat_lit 19270986174367761244880659441012402771883025 

noncomputable def Ns60p1091 := nat_lit 6073680812407062607909659302271927863316152538637764990339 

noncomputable abbrev qz110 := qz424

noncomputable def Ns60p1092 := @Enclosure.Real.IsNear.mulLit_ft qz110 qz106 Ns60p1090 Ns60p427 Ns60p1091 Ns60p429 

noncomputable def Ns60p1093 := nat_lit 113341516726513677552081783 

noncomputable def Ns60p1094 := @Enclosure.Real.IsNear.mulLit_tt qz106 qz106 4389873138755579260695 9444732965739290427392 Ns60p1093 Ns60p432 4389873138755579260695 9444732965739290427392 

noncomputable abbrev qz743 := (@HSub.hSub Real Real Real qz920 qz979 qz932)

noncomputable abbrev qz428 := qz743

noncomputable abbrev qz111 := qz428

noncomputable def Ns60p1095 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz111 884279719003555 140737488355328 1 500000000000000 4964349 67108864 21 67108864 

noncomputable abbrev qz744 := qz979

noncomputable abbrev qz429 := qz744

noncomputable abbrev qz112 := qz429

noncomputable def Ns60p1096 := @Enclosure.Real.IsNear.subLit_ff_n qz112 qz348 62144515 67108864 21 67108864 1 1 0 1 4964349 

noncomputable def Ns60p1097 := @Enclosure.Real.IsNear.mulLit_ff qz0 qz92 2 1 0 1 62144515 134217728 21 134217728 62144515 67108864 21 

noncomputable def Ns60p1098 := @Enclosure.Real.IsNear.recentre' qz105 Bool.true 62218964 67108864 

noncomputable def Ns60p1099 := @Enclosure.Real.IsNear.sin_image qz100 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 65595547)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true 65595547 33554432 

noncomputable def Ns60p1100 := nat_lit 4956259403918113389410155679045 

noncomputable def Ns60p1101 := nat_lit 146497752116850092754264633239256001 

noncomputable def Ns60p1102 := @Enclosure.Real.IsNear.recentre' qz100 Bool.true Ns60p1100 Ns60p440 Ns60p1101 

noncomputable def Ns60p1103 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz101 884279719003555 140737488355328 1 500000000000000 5604854773219319 

noncomputable def Ns60p1104 := @Enclosure.Real.IsNear.subLit_tf qz102 qz23 4478954866376695 18014398509481984 5428642359 18014398509481984 1 16 

noncomputable def Ns60p1105 := @Enclosure.Real.IsNear.subLit_ff_n qz103 qz92 3861940744585225 18014398509481984 2610070071 18014398509481984 62144515 134217728 21 134217728 

noncomputable def Ns60p1106 := @Enclosure.Real.IsNear.mulLit_ff qz92 qz92 62144515 134217728 21 134217728 62144515 134217728 21 134217728 3861940744585225 18014398509481984 

noncomputable def Ns60p1107 := nat_lit 1551278792226392936050727464046001621764913786038649602525438918809666046833573581951053166318713041 

noncomputable def Ns60p1108 := nat_lit 12684665394983152616504205685395516723933243557900373284185259809851078924757332746807504075017420800 

noncomputable def Ns60p1109 := nat_lit 6345886436461968862805359839938120579746032336902768381335021908106382740042730992309094316241 

noncomputable def Ns60p1110 := nat_lit 7733322450857393396111852665321840956203937890820057473101059782945465343745037526157013929999726801 

noncomputable def Ns60p1111 := nat_lit 443963288824410341577647198988843085337663524526513064946484093344787762366506646138262642625609728000 

noncomputable def Ns60p1112 := BSN.sin_dyadic_bound_f 65595547 33554432 4 3 67108864 17475728 Ns60p1107 Ns60p1108 Ns60p1109 Ns60p1110 Ns60p1111 Ns60p1109 62218964 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 65595547) (BSN.sinEvenQ 33554432) 0 3 Ns60p1107 Ns60p1108 Ns60p1109 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 65595547) (BSN.sinOddQ 33554432) 0 3 Ns60p1110 Ns60p1111 Ns60p1109 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1113 := @Ns60p1098 4590528368 2345552507305984 15554741 16777216 286908023 146597031706624 (@Ns60p1099 255 134217728 Bool.true 62218964 67108864 1 17475728 (@Ns60p1102 Ns60p443 65595547 33554432 255 134217728 (@Ns60p1103 18014398509481984 5428642359 18014398509481984 Ns60p1100 Ns60p440 Ns60p1101 Ns60p443 RS061to078.d39 (@Ns60p1104 0 1 89677676371509104 5604854773219319 18014398509481984 5428642359 18014398509481984 (@Ns60p1105 601155145979623595048960 4478954866376695 18014398509481984 5428642359 18014398509481984 (@Ns60p1106 2610070071 18014398509481984 (Ns60p1044 rfl rfl) (Ns60p1044 rfl rfl) rfl) (Ns60p1044 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 65595547 33554432) (BSN.sin_neg_of_bound 65595547 33554432 Bool.false 62218964 67108864 1 17475728 (Ns60p1112 rfl rfl)) rfl rfl) 

noncomputable def Ns60p1114 := nat_lit 11645627356800112912013635286930312175 

noncomputable def Ns60p1115 := nat_lit 9175928152761842674804015249393601483653166602884483 

noncomputable def Ns60p1116 := @Enclosure.Real.IsNear.mulLit_tt qz980 qz96 Ns60p1114 Ns60p456 Ns60p1115 

noncomputable def Ns60p1117 := nat_lit 340024550179541032656245349 

noncomputable abbrev qz984 := (@HMul.hMul Real Real Real qz5 qz317 qz106)

noncomputable def Ns60p1118 := @Enclosure.Real.IsNear.mulLit_tf qz984 qz372 13169619416266737782085 9444732965739290427392 Ns60p1117 Ns60p432 884279719003555 

noncomputable def Ns60p1119 := @Enclosure.Real.IsNear.mulLit_ft qz317 qz106 3 1 0 1 4389873138755579260695 9444732965739290427392 Ns60p1093 

noncomputable def Ns60p1120 := @Enclosure.Real.IsNear.recentre' qz96 Bool.true 25147567 67108864 

noncomputable def Ns60p1121 := @Enclosure.Real.IsNear.cos_image qz100 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 65595547)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true 65595547 33554432 

noncomputable def Ns60p1122 := nat_lit 598943779039967954705595074702091096097101278230984522249409855312833622970712873104473718591322321 

noncomputable def Ns60p1123 := nat_lit 975743491921780970500323514261193594148711042915413329552712293065467609596717903600577236539801600 

noncomputable def Ns60p1124 := nat_lit 3612683027510571926620634560423243985013633571718533572825629700063253497643806511201645033905453265 

noncomputable def Ns60p1125 := nat_lit 88792657764882068315529439797768617067532704905302612989296818668957552473301329227652528525121945600 

noncomputable def Ns60p1126 := BSN.cos_dyadic_bound_t 65595547 33554432 4 3 67108864 17475728 Ns60p1122 Ns60p1123 Ns60p1109 Ns60p1124 Ns60p1125 Ns60p1109 25147567 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 65595547) (BSN.cosEvenQ 33554432) 0 3 Ns60p1122 Ns60p1123 Ns60p1109 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 65595547) (BSN.cosOddQ 33554432) 0 3 Ns60p1124 Ns60p1125 Ns60p1109 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1127 := @Ns60p1120 4590528368 2345552507305984 25147567 67108864 286908023 146597031706624 (@Ns60p1121 255 134217728 Bool.true 25147567 67108864 1 17475728 (@Ns60p1102 Ns60p443 65595547 33554432 255 134217728 (@Ns60p1103 18014398509481984 5428642359 18014398509481984 Ns60p1100 Ns60p440 Ns60p1101 Ns60p443 RS061to078.d39 (@Ns60p1104 0 1 89677676371509104 5604854773219319 18014398509481984 5428642359 18014398509481984 (@Ns60p1105 601155145979623595048960 4478954866376695 18014398509481984 5428642359 18014398509481984 (@Ns60p1106 2610070071 18014398509481984 (Ns60p1044 rfl rfl) (Ns60p1044 rfl rfl) rfl) (Ns60p1044 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 65595547 33554432) (BSN.cos_neg_of_bound 65595547 33554432 Bool.true 25147567 67108864 1 17475728 (Ns60p1126 rfl rfl)) rfl rfl) 

noncomputable abbrev qz430 := (@Ns60p1095 4389873138755579260695 9444732965739290427392 Ns60p1093 Ns60p432 RS061to078.d39 (@Ns60p1096 4964349 67108864 21 67108864 (@Ns60p1097 67108864 qz916 (Ns60p1044 rfl rfl) rfl) qz933 rfl rfl) rfl)

noncomputable def Ns60p1128 := @Ns60p1079 Ns60p1080 Ns60p1072 Ns60p1081 Ns60p1074 Ns60p1082 Ns60p1083 Ns60p1084 Ns60p1085 Ns60p1086 Ns60p1071 Ns60p1072 Ns60p1073 Ns60p1074 (@Ns60p1088 Ns60p1089 Ns60p425 15554741 16777216 286908023 146597031706624 Ns60p1080 Ns60p1072 Ns60p1081 Ns60p1074 (@Ns60p1092 4389873138755579260695 9444732965739290427392 Ns60p1093 Ns60p432 Ns60p1087 Ns60p422 Ns60p1089 Ns60p425 (@Ns60p1094 Ns60p1093 Ns60p432 Ns60p1090 Ns60p427 Ns60p1091 Ns60p429 qz430 qz430 rfl) qz430 rfl) (Ns60p1113 rfl) rfl) (@Ns60p1116 Ns60p459 25147567 67108864 286908023 146597031706624 Ns60p1082 Ns60p1083 Ns60p1084 Ns60p1085 (@Ns60p1118 70368744177664 1 250000000000000 Ns60p1114 Ns60p456 Ns60p1115 Ns60p459 (@Ns60p1119 Ns60p432 13169619416266737782085 9444732965739290427392 Ns60p1117 Ns60p432 qz696 qz430 rfl) RS061to078.d41 rfl) (Ns60p1127 rfl) rfl) rfl rfl 

noncomputable def Ns60p1129 := nat_lit 12439684583861112079054146031536369 

noncomputable def Ns60p1130 := nat_lit 102263117503955270104767100359885446546341154664960042379590804695311651630925 

noncomputable def Ns60p1131 := @Enclosure.Real.IsNear.mulLit_tf qz981 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz92) 82004322613150388509485 18889465931478580854784 Ns60p1129 Ns60p473 Ns60p1130 

noncomputable def Ns60p1132 := nat_lit 28948022309329048855892746252171976963317496166410141009864396001978282409984 

noncomputable def Ns60p1133 := nat_lit 240894201248476009651724462811541326126963545950089346454480724131506140303914356468328956605283458041844818411 

noncomputable def Ns60p1134 := nat_lit 1405157163300755948448138998682339030496673271034763086910621184990142576580462567751680000000000000000000000000000 

noncomputable def Ns60p1135 := nat_lit 4146561527953704026351382010512123 

noncomputable def Ns60p1136 := @Enclosure.Real.IsNear.mulLit_ft qz317 qz107 3 1 0 1 27334774204383462836495 18889465931478580854784 Ns60p1135 

noncomputable def Ns60p1137 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz109 884279719003555 140737488355328 1 500000000000000 30911909 134217728 153655597 146597031706624 27334774204383462836495 

noncomputable def Ns60p1138 := @Enclosure.Real.IsNear.recentre' qz109 Bool.false 30911909 134217728 2458489552 2345552507305984 30911909 134217728 153655597 146597031706624 

noncomputable def Ns60p1139 := @Enclosure.Real.IsNear.sin_image qz99 qz742 Bool.false 390465503 134217728 133 134217728 Bool.false 30911909 134217728 1 

noncomputable def Ns60p1140 := nat_lit 11939173926467586414990156706742541038105771748069960819986158893930961480999322790868881942895152787788593572283309030222408570128554664117759681 

noncomputable def Ns60p1141 := nat_lit 6147560696732867693285374270751456580053951683818686326971540344330039695328555252647769656306557088773643941222781456624087726509109636801 

noncomputable def Ns60p1142 := nat_lit 72338904637895939116024900392882536438610930146551646085650024305647917984717195312073225039877671719114822645948217400601513981538024589486812865 

noncomputable def Ns60p1143 := BSN.cos_dyadic_bound_f 367896143599 274877906944 4 3 134217728 34985589 Ns60p1140 Ns60p814 Ns60p1141 Ns60p1142 Ns60p817 Ns60p1141 30911909 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 367896143599) (BSN.cosEvenQ 274877906944) 0 3 Ns60p1140 Ns60p814 Ns60p1141 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 367896143599) (BSN.cosOddQ 274877906944) 0 3 Ns60p1142 Ns60p817 Ns60p1141 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1144 := @Ns60p1139 17475728 (Ns60p1045 rfl) (Enclosure.sfrac_false_div 390465503 134217728) (BSN.sin_reduce1 qz742 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns60p1046) qz692) 226375608064910080 72057594037927936 Bool.false 30911909 134217728 0 1000000000000000 34951456 17475728 (BSN.sin_reduce_arg_pos_rat_q1 390465503 134217728 226375608064910080 72057594037927936 0 Ns60p1046 Ns60p379 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 30911909 134217728 Ns60p1046 Ns60p379 367896143599 274877906944 34985589 34951456 (Ns60p1143 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable abbrev qz113 := (@HMul.hMul Real Real Real qz323 qz320 qz426)

noncomputable abbrev qz745 := (@Enclosure.Real.IsNear.neg qz113 Bool.false 27334774204383462836495 18889465931478580854784 Ns60p1135 Ns60p473 (@Ns60p1137 18889465931478580854784 Ns60p1135 Ns60p473 RS061to078.d39 (Ns60p1138 (Ns60p1144 rfl rfl) rfl) rfl))

noncomputable def Ns60p1145 := @Ns60p1136 Ns60p473 82004322613150388509485 18889465931478580854784 Ns60p1129 Ns60p473 qz696 qz745 rfl 

noncomputable abbrev qz114 := (@HMul.hMul Real Real Real qz323 qz424 (Real.cos qz419))

noncomputable def Ns60p1146 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz114) (@HMul.hMul Real Real Real qz5 qz372 qz105) 

noncomputable abbrev qz985 := (@HMul.hMul Real Real Real qz5 qz0 qz107)

noncomputable def Ns60p1147 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 2 Zeta.RiemannSiegel.correction qz92) (@HMul.hMul Real Real Real qz5 qz95 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns60p1146 (@HMul.hMul Real Real Real qz5 qz985 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c8 1 Zeta.RiemannSiegel.correction qz92))) (@HMul.hMul Real Real Real qz5 qz108 qz91))) 

noncomputable def Ns60p1148 := @Enclosure.Real.IsNear.mulLit_tt qz95 (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 Ns60p1146 (@HMul.hMul Real Real Real qz5 qz985 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c6 1 Zeta.RiemannSiegel.correction qz92))) (@HMul.hMul Real Real Real qz5 qz108 qz91)) 137925595 

noncomputable def Ns60p1149 := nat_lit 741436841392312065826267418747662074949476597617433097748034399962615 

noncomputable def Ns60p1150 := nat_lit 215679573337205118357336120696157045389097155380324579848828881993728 

noncomputable def Ns60p1151 := nat_lit 1707670411497620605278314619694650080561831763888396649533162017739220093295019636588402736960716888369 

noncomputable def Ns60p1152 := nat_lit 10469236696517139289141736914830945659404048852881514183510997779593933944258560000000000000000000000000000 

noncomputable def Ns60p1153 := nat_lit 2449254834122323737260268880540156600922425174110021075623456231717385 

noncomputable def Ns60p1154 := @Enclosure.Real.IsNear.subLit_ff_n (@HSub.hSub Real Real Real qz11 Ns60p1146 (@HMul.hMul Real Real Real qz5 qz985 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 1 Zeta.RiemannSiegel.correction qz92))) (@HMul.hMul Real Real Real qz5 qz108 qz91) Ns60p1153 Ns60p1150 

noncomputable def Ns60p1155 := nat_lit 2823194618160471928568326838284170060641203303377631311134748791052565318968739940904737184902689111541 

noncomputable def Ns60p1156 := nat_lit 52346183482585696445708684574154728297020244264407570917554988897969669721292800000000000000000000000000000 

noncomputable def Ns60p1157 := nat_lit 88559484065904187174615333469013774721820313799088125 

noncomputable def Ns60p1158 := nat_lit 145232275954381692755305135063201242270064531331727478265304333758608978179204541 

noncomputable def Ns60p1159 := nat_lit 1330209262895822187606826402456840208784529992472277811200000000000000000000000000000 

noncomputable def Ns60p1160 := nat_lit 4438471301825810669159957604174540518315803644293916536608413216357997140731483902681347762062019552082695521406329815040 

noncomputable def Ns60p1161 := nat_lit 70229446228425222358366163438000282696908631097249695 

noncomputable def Ns60p1162 := nat_lit 1252059645861901180592761284655931683910107299089306149942925009691279543 

noncomputable def Ns60p1163 := nat_lit 48715219660853396211497964352179075665523015417856000000000000000000000000000 

noncomputable def Ns60p1164 := @Enclosure.Real.IsNear.subLit_ff_p Ns60p1146 (@HMul.hMul Real Real Real qz5 qz985 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c7 1 Zeta.RiemannSiegel.correction qz92)) Ns60p1161 Ns60p25 Ns60p1162 Ns60p1163 

noncomputable def Ns60p1165 := nat_lit 81027628795853199702743480833318126028115768295804422895506872272375 

noncomputable def Ns60p1166 := nat_lit 1477813351079879135430733897076631721994191834837005653530305179103455171557751482263695108903783153141 

noncomputable def Ns60p1167 := nat_lit 14662000436471419585680997657548544577066227950239386488532710574747626683294024055219817897213380744355568233672039464960 

noncomputable def Ns60p1168 := @Enclosure.Real.IsNear.subLit_ft (@Neg.neg Real Real.instNeg qz114) (@HMul.hMul Real Real Real qz5 qz372 qz105) 

noncomputable def Ns60p1169 := nat_lit 484618415975986958545639790297041946536914087350175 

noncomputable def Ns60p1170 := nat_lit 53962467616516224721831034735205284197365499736787447936653009691279543 

noncomputable def Ns60p1171 := nat_lit 7742521545305246177562109496766849 

noncomputable def Ns60p1172 := nat_lit 82912295744902821870403989057486019852715325600754089935469382991536455680 

noncomputable def Ns60p1173 := @Enclosure.Real.IsNear.neg qz114 Bool.true Ns60p1169 

noncomputable def Ns60p1174 := @Enclosure.Real.IsNear.mulLit_ft qz110 qz96 Ns60p1090 Ns60p427 Ns60p1091 

noncomputable def Ns60p1175 := @Enclosure.Real.IsNear.mulLit_ft qz372 qz105 884279719003555 70368744177664 1 

noncomputable def Ns60p1176 := nat_lit 2964269182909856848281216961918673608754128025 

noncomputable def Ns60p1177 := @Enclosure.Real.IsNear.mulLit_tt qz985 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz92) 27334774204383462836495 9444732965739290427392 Ns60p1135 Ns60p524 Ns60p1176 

noncomputable def Ns60p1178 := nat_lit 22835963083295358096932575511191922182123945984 

noncomputable def Ns60p1179 := nat_lit 1523719767076099891341026368731280330568166096293485852059648367 

noncomputable def Ns60p1180 := nat_lit 166276157861977773450853300307105026098066249059034726400000000000000 

noncomputable def Ns60p1181 := @Enclosure.Real.IsNear.mulLit_ft qz0 qz107 2 1 0 1 27334774204383462836495 18889465931478580854784 Ns60p1135 

noncomputable def Ns60p1182 := @Ns60p1181 Ns60p473 27334774204383462836495 9444732965739290427392 Ns60p1135 Ns60p524 qz321 qz745 rfl 

noncomputable abbrev qz115 := (@HMul.hMul Real Real Real qz323 qz425 (Real.sin qz419))

noncomputable def Ns60p1183 := @HSub.hSub Real Real Real qz11 (@Neg.neg Real Real.instNeg qz115) (@HMul.hMul Real Real Real qz5 qz107 qz91) 

noncomputable def Ns60p1184 := @Enclosure.Real.IsNear.of_eq (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz92) (@HMul.hMul Real Real Real qz5 qz95 Ns60p1183) Bool.true Ns60p1176 Ns60p1178 Ns60p1179 Ns60p1180 (BSN.deriv_correction_mk qz92 qz427) 

noncomputable def Ns60p1185 := nat_lit 21491799132059983850576950289166224795 

noncomputable def Ns60p1186 := nat_lit 170141183460469231731687303715884105728 

noncomputable def Ns60p1187 := nat_lit 10878338471951046238613153128847394315537127564024409293 

noncomputable def Ns60p1188 := @Enclosure.Real.IsNear.mulLit_tf qz95 Ns60p1183 137925595 134217728 149 134217728 Ns60p1185 Ns60p1186 Ns60p1187 

noncomputable def Ns60p1189 := nat_lit 1238853915497495036206046494149454132453100748800000000000000 

noncomputable def Ns60p1190 := @Enclosure.Real.IsNear.subLit_tt_p (@Neg.neg Real Real.instNeg qz115) (@HMul.hMul Real Real Real qz5 qz107 qz91) 

noncomputable def Ns60p1191 := nat_lit 68283339696200097705082204995 

noncomputable def Ns60p1192 := nat_lit 158456325028528675187087900672 

noncomputable def Ns60p1193 := nat_lit 11546092271696894264329936589819686404513 

noncomputable def Ns60p1194 := nat_lit 94810476846269482629410131150439435675 

noncomputable def Ns60p1195 := nat_lit 7493092762267934365678664886599978385342293790413221069 

noncomputable def Ns60p1196 := nat_lit 3405511508717547277146449613588739741813022188745708967144183562240 

noncomputable def Ns60p1197 := @Enclosure.Real.IsNear.neg qz115 Bool.false Ns60p1191 

noncomputable def Ns60p1198 := @Enclosure.Real.IsNear.mulLit_tt qz106 qz105 4389873138755579260695 9444732965739290427392 Ns60p1093 

noncomputable def Ns60p1199 := @Enclosure.Real.IsNear.mulLit_tf qz107 qz91 27334774204383462836495 18889465931478580854784 Ns60p1135 Ns60p473 3468493141277365 9007199254740992 

noncomputable def Ns60p1200 := @Enclosure.Real.IsNear.of_eq qz91 (@HMul.hMul Real Real Real qz5 qz95 qz96) Bool.false 3468493141277365 

noncomputable def Ns60p1201 := @Enclosure.Real.IsNear.mulLit_tt qz95 qz96 137925595 134217728 149 

noncomputable abbrev qz431 := (@Ns60p1200 9007199254740992 23878584645441595 9837960263603517915136 (BSN.correction_mk qz92 (BSN.cos_two_pi_p_ne_zero_mk qz89 262452 1000 6 qz94 rfl rfl qz983)) (@Ns60p1201 134217728 25147567 67108864 286908023 146597031706624 3468493141277365 9007199254740992 23878584645441595 9837960263603517915136 Ns60p1053 (Ns60p1127 rfl) rfl))

noncomputable def Ns60p1202 := @Ns60p1199 23878584645441595 9837960263603517915136 Ns60p1194 Ns60p1186 Ns60p1195 Ns60p1189 qz745 qz431 

noncomputable def Ns60p1203 := @Ns60p1177 Ns60p1178 Ns60p1179 Ns60p1180 Ns60p1165 Ns60p1150 Ns60p1166 Ns60p1156 Ns60p1182 (Ns60p1184 (@Ns60p1188 Ns60p1189 Ns60p1176 Ns60p1178 Ns60p1179 Ns60p1180 Ns60p1053 (@Ns60p1190 Ns60p1191 Ns60p1192 Ns60p1193 Ns60p872 Ns60p1194 Ns60p1186 Ns60p1195 Ns60p1189 Ns60p1196 Ns60p1185 Ns60p1186 Ns60p1187 Ns60p1189 (@Ns60p1197 Ns60p1192 Ns60p1193 Ns60p872 (@Ns60p1198 Ns60p432 15554741 16777216 286908023 146597031706624 Ns60p1191 Ns60p1192 Ns60p1193 Ns60p872 qz430 (Ns60p1113 rfl) rfl)) (Ns60p1202 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns60p1204 := @Ns60p1164 Ns60p1165 Ns60p1150 Ns60p1166 Ns60p1156 Ns60p1167 Ns60p1153 Ns60p1150 Ns60p1155 Ns60p1156 (@Ns60p1168 Ns60p1169 Ns60p25 Ns60p1170 Ns60p1163 13754742000653076104255 1180591620717411303424 Ns60p1171 Ns60p524 Ns60p1172 Ns60p1161 Ns60p25 Ns60p1162 Ns60p1163 (@Ns60p1173 Ns60p25 Ns60p1170 Ns60p1163 (@Ns60p1174 Ns60p429 25147567 67108864 286908023 146597031706624 Ns60p1169 Ns60p25 Ns60p1170 Ns60p1163 (@Ns60p1094 Ns60p1093 Ns60p432 Ns60p1090 Ns60p427 Ns60p1091 Ns60p429 qz430 qz430 rfl) (Ns60p1127 rfl) rfl)) (@Ns60p1175 250000000000000 15554741 16777216 286908023 146597031706624 13754742000653076104255 1180591620717411303424 Ns60p1171 Ns60p524 RS061to078.d41 (Ns60p1113 rfl) rfl) rfl rfl) Ns60p1203 

noncomputable def Ns60p1205 := nat_lit 25532552742280988896801329146307939625 

noncomputable def Ns60p1206 := nat_lit 111899422139910804123580024858265564624158279251449812035613 

noncomputable def Ns60p1207 := @Enclosure.Real.IsNear.mulLit_ff qz108 qz91 Ns60p1205 Ns60p456 Ns60p1206 Ns60p557 3468493141277365 9007199254740992 

noncomputable def Ns60p1208 := @Enclosure.Real.IsNear.mulLit_ft qz47 qz98 Ns60p313 Ns60p317 Ns60p315 Ns60p318 32652385 33554432 153655597 146597031706624 Ns60p1205 

noncomputable abbrev qz116 := (@HMul.hMul Real Real Real qz323 qz683 qz418)

noncomputable def Ns60p1209 := @Ns60p1207 23878584645441595 9837960263603517915136 Ns60p1157 Ns60p25 Ns60p1158 Ns60p1159 (@Enclosure.Real.IsNear.neg qz116 Bool.true Ns60p1205 Ns60p456 Ns60p1206 Ns60p557 (@Ns60p1208 Ns60p456 Ns60p1206 Ns60p557 RS061to078.d43 (Ns60p1038 (Ns60p1051 rfl rfl) rfl) rfl)) qz431 

noncomputable def Ns60p1210 := nat_lit 76597658226842966690403987438923818875 

noncomputable def Ns60p1211 := nat_lit 335698266419732412370740074574796693872474837754349436106839 

noncomputable def Ns60p1212 := @Enclosure.Real.IsNear.mulLit_ft qz982 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c3 1 Zeta.RiemannSiegel.correction qz92) Ns60p1210 Ns60p456 Ns60p1211 Ns60p557 Ns60p1176 

noncomputable def Ns60p1213 := @Enclosure.Real.IsNear.mulLit_ff qz317 qz108 3 1 0 1 Ns60p1205 Ns60p456 Ns60p1206 

noncomputable def Ns60p1214 := @Ns60p1213 Ns60p557 Ns60p1210 Ns60p456 Ns60p1211 Ns60p557 qz696 (@Enclosure.Real.IsNear.neg qz116 Bool.true Ns60p1205 Ns60p456 Ns60p1206 Ns60p557 (@Ns60p1208 Ns60p456 Ns60p1206 Ns60p557 RS061to078.d43 (Ns60p1038 (Ns60p1051 rfl rfl) rfl) rfl)) rfl 

noncomputable def Ns60p1215 := @Ns60p1212 Ns60p1178 Ns60p1179 Ns60p1180 Ns60p1066 Ns60p1067 Ns60p1068 Ns60p1069 Ns60p1214 (Ns60p1184 (@Ns60p1188 Ns60p1189 Ns60p1176 Ns60p1178 Ns60p1179 Ns60p1180 Ns60p1053 (@Ns60p1190 Ns60p1191 Ns60p1192 Ns60p1193 Ns60p872 Ns60p1194 Ns60p1186 Ns60p1195 Ns60p1189 Ns60p1196 Ns60p1185 Ns60p1186 Ns60p1187 Ns60p1189 (@Ns60p1197 Ns60p1192 Ns60p1193 Ns60p872 (@Ns60p1198 Ns60p432 15554741 16777216 286908023 146597031706624 Ns60p1191 Ns60p1192 Ns60p1193 Ns60p872 qz430 (Ns60p1113 rfl) rfl)) (Ns60p1202 rfl) rfl rfl) rfl)) rfl 

noncomputable def Ns60p1216 := @Ns60p1064 Ns60p1065 Ns60p1035 Ns60p1066 Ns60p1067 Ns60p1068 Ns60p1069 Ns60p1070 Ns60p1055 Ns60p1032 Ns60p1056 Ns60p1057 (@Ns60p1075 Ns60p1076 Ns60p1032 Ns60p1077 Ns60p1035 Ns60p1078 Ns60p1063 Ns60p1032 Ns60p1065 Ns60p1035 Ns60p1128 (@Ns60p1131 Ns60p1132 Ns60p1133 Ns60p1134 Ns60p1076 Ns60p1032 Ns60p1077 Ns60p1035 Ns60p1145 (@Ns60p1147 Bool.false Ns60p1130 Ns60p1132 Ns60p1133 Ns60p1134 (BSN.iteratedDeriv_two_correction_mk qz92 qz427) (@Ns60p1148 134217728 149 134217728 Ns60p1149 Ns60p1150 Ns60p1151 Ns60p1152 Ns60p1130 Ns60p1132 Ns60p1133 Ns60p1134 Ns60p1053 (@Ns60p1154 Ns60p1155 Ns60p1156 Ns60p1157 Ns60p25 Ns60p1158 Ns60p1159 Ns60p1160 Ns60p1149 Ns60p1150 Ns60p1151 Ns60p1152 (Ns60p1204 rfl rfl) (Ns60p1209 rfl) rfl rfl) rfl)) rfl) rfl rfl) Ns60p1215 

noncomputable def Ns60p1217 := nat_lit 21374443676067234308103639252694486127392188744722375 

noncomputable def Ns60p1218 := nat_lit 3019726242944910087373009446477080944992882601515162486107890707856020371308540759947 

noncomputable def Ns60p1219 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz684 RSCompact.c11) qz109) qz91 Ns60p1217 Ns60p569 Ns60p1218 Ns60p571 3468493141277365 9007199254740992 23878584645441595 

noncomputable def Ns60p1220 := @Enclosure.Real.IsNear.mulLit_ff qz685 qz109 Ns60p319 Ns60p320 Ns60p321 Ns60p322 30911909 134217728 153655597 146597031706624 Ns60p1217 

noncomputable def Ns60p1221 := Ns60p1030 (@Ns60p1034 Ns60p1035 Ns60p1023 Ns60p1024 Ns60p1025 Ns60p1026 Ns60p1053 (@Ns60p1054 Ns60p1055 Ns60p1032 Ns60p1056 Ns60p1057 Ns60p1058 Ns60p1059 Ns60p1060 Ns60p1061 Ns60p1062 Ns60p1031 Ns60p1032 Ns60p1033 Ns60p1035 (Ns60p1216 rfl rfl) (@Ns60p1219 9837960263603517915136 Ns60p1058 Ns60p1059 Ns60p1060 Ns60p1061 (@Ns60p1220 Ns60p569 Ns60p1218 Ns60p571 RS061to078.d44 (Ns60p1138 (Ns60p1144 rfl rfl) rfl) rfl) qz431 rfl) rfl rfl) rfl) 

noncomputable def Ns60p1222 := @Enclosure.Real.IsNear.of_eq qz740 (@Neg.neg Real Real.instNeg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz92) qz374)) Bool.false Ns60p1018 Ns60p1019 Ns60p1020 Ns60p1021 (BSN.correctionLinear_mk qz92) (@Enclosure.Real.IsNear.neg (@HMul.hMul Real Real Real qz5 (@iteratedDeriv Real RSCompact.c4 Real Real.normedAddCommGroup RSCompact.c5 3 Zeta.RiemannSiegel.correction qz92) qz374) Bool.true Ns60p1018 Ns60p1019 Ns60p1020 Ns60p1021 (@Ns60p1027 Ns60p1019 Ns60p1020 Ns60p1021 Ns60p1221 RS061to078.d45 rfl)) 

noncomputable def Ns60p1223 := @Enclosure.Real.IsNear.inv_image qz93 54215691 8388608 21 8388608 648970 648971 4194304 qz735 rfl 

noncomputable def Ns60p1224 := @Ns60p1022 Ns60p972 Ns60p982 Ns60p975 Ns60p1222 (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz93) Bool.false 1297941 8388608 1 8388608 1297941 8388608 1 8388608 (Ns60p1223 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns60p1225 := @Ns60p974 Ns60p975 Ns60p914 Ns60p910 Ns60p916 Ns60p912 (Ns60p976 qz25 (@Enclosure.Real.IsNear.of_eq qz734 (@Inv.inv Real Real.instInv (Real.sqrt qz93)) Bool.false 824921 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz90 (BSN.t_div_two_pi_nonneg qz89 262452 1000 qz94)) Ns60p980) rfl) (@Ns60p983 Ns60p984 Ns60p971 Ns60p972 Ns60p973 Ns60p975 (@Ns60p985 17592186044416 373536624415079 9607383069925310464 (BSN.correction_mk qz92 qz427) (@Ns60p986 4194304 1571725 4194304 286908023 9162314481664 6774397228075 17592186044416 373536624415079 9607383069925310464 Ns60p1003 (Ns60p1017 rfl) rfl)) (Ns60p1224 rfl) rfl rfl) 

noncomputable def Ns60p1226 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS qz89) (hardyZApproximantRS qz89) Bool.false Ns60p909 Ns60p910 Ns60p911 Ns60p912 (@Eq.refl Real (hardyZApproximantRS qz89)) (Ns60p913 (BSN.hardyZApproximantRS_eq qz89 6 qz983) (@Ns60p915 Ns60p916 Ns60p912 Ns60p917 Ns60p909 Ns60p910 Ns60p911 Ns60p912 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz89) qz89 6) (@HAdd.hAdd Real Real Real qz336 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz89) qz89 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz89) qz89 6)) Bool.false 189578379 33554432 47001 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz89) qz89 6) (Ns60p970 (Ns60p969 rfl rfl rfl rfl) rfl rfl)) (Ns60p1225 rfl) rfl rfl)) 

theorem RS061to078.d50 : Enclosure.Real.IsNear (hardyZApproximantRS qz89) Bool.false Ns60p909 Ns60p910 Ns60p911 Ns60p912 := Ns60p1226 

noncomputable def Ns60p1227 := nat_lit 80592570479440018760794112 

noncomputable def Ns60p1228 := nat_lit 6806694019033860288731414528 

noncomputable def Ns60p1229 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz89) qz89 6) (@HMul.hMul Real Real Real qz5 qz726 qz91) 189578379 33554432 47001 33554432 5588342535780857075 36893488147419103232 1239952790277306406669 Ns60p1227 Ns60p1228 

noncomputable def Ns60p1230 := @Enclosure.Real.IsNear.mulLit_ff qz726 qz91 824921 2097152 1 4194304 6774397228075 17592186044416 373536624415079 9607383069925310464 5588342535780857075 36893488147419103232 

noncomputable def Ns60p1231 := @Ns60p1230 1239952790277306406669 Ns60p1227 (Ns60p976 qz25 (@Enclosure.Real.IsNear.of_eq qz734 (@Inv.inv Real Real.instInv (Real.sqrt qz93)) Bool.false 824921 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz90 (BSN.t_div_two_pi_nonneg qz89 262452 1000 qz94)) Ns60p980) rfl) (@Ns60p985 17592186044416 373536624415079 9607383069925310464 (BSN.correction_mk qz92 qz427) (@Ns60p986 4194304 1571725 4194304 286908023 9162314481664 6774397228075 17592186044416 373536624415079 9607383069925310464 Ns60p1003 (Ns60p1017 rfl) rfl)) 

noncomputable def Ns60p1232 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz89) (hardyZApproximantRS₀ qz89) Bool.false 202855289549644598029 36893488147419103232 114129105707667185686285 Ns60p1227 (@Eq.refl Real (hardyZApproximantRS₀ qz89)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz89) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz89) qz89 6) (@HMul.hMul Real Real Real qz5 qz726 qz91)) Bool.false 202855289549644598029 36893488147419103232 114129105707667185686285 Ns60p1227 (BSN.hardyZApproximantRS₀_eq qz89 6 qz983) (@Ns60p1229 202855289549644598029 36893488147419103232 114129105707667185686285 Ns60p1227 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz89) qz89 6) (@HAdd.hAdd Real Real Real qz336 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz89) qz89 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz89) qz89 6)) Bool.false 189578379 33554432 47001 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz89) qz89 6) (Ns60p970 (Ns60p969 rfl rfl rfl rfl) rfl rfl)) (Ns60p1231 rfl) rfl rfl)) 

theorem RS061to078.d51 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz89) Bool.false 202855289549644598029 36893488147419103232 114129105707667185686285 Ns60p1227 := Ns60p1232 

noncomputable def Ns60p1233 := nat_lit 40296285239720009380397056 

noncomputable def Ns60p1234 := nat_lit 1553581036577266910330093568 

noncomputable abbrev qz746 := (Enclosure.sfrac Bool.false 264134 1000)

noncomputable abbrev qz432 := qz746

noncomputable abbrev qz117 := qz432

noncomputable abbrev qz986 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 264134 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz747 := qz986

noncomputable abbrev qz433 := qz747

noncomputable abbrev qz118 := qz433

noncomputable abbrev qz748 := (@HSub.hSub Real Real Real qz920 (Real.sqrt qz986) qz914)

noncomputable abbrev qz434 := qz748

noncomputable abbrev qz119 := qz434

noncomputable abbrev qz987 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz326 qz118 qz8))

noncomputable def Ns60p1235 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz117) qz117 6) (@HMul.hMul Real Real Real qz5 qz987 (Zeta.RiemannSiegel.correction qz119)) 39585393 16777216 5913 4194304 5551446027805791687 36893488147419103232 614880495272941710939 Ns60p1233 Ns60p1234 

noncomputable def Ns60p1236 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz117) qz117 Real.sin BSN.quadSignPos 5 6 264134 1000 71 67108864 33554432 1125899906842624 Bool.false 24245315597 1052 120242927 63 27397080 8 

noncomputable def Ns60p1237 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz117) qz117 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 264134 1000 3 40 67108864 33554432 1125899906842624 Bool.false 24245315597 1052 

noncomputable def Ns60p1238 := Ns60p1237 93032624 62 33554424 8 108007536 62 30011992 8 Bool.true 113350681 23541 Bool.true 11520439 Bool.true 66572634 3537118876014220 1 Bool.false 11463938 Bool.false Bool.false 36709133 Bool.false Bool.true 91201893 

noncomputable def Ns60p1239 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz117) qz117 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 264134 1000 113 45 67108864 33554432 1125899906842624 Bool.false 24245315597 1052 

noncomputable def Ns60p1240 := Ns60p1239 46516304 62 47453136 16 73726608 62 38745320 8 Bool.true 67108856 1126 Bool.false 46955807 Bool.false 27965651 3537118876014220 1 Bool.false 43217114 Bool.true Bool.false 27163248 Bool.true Bool.true 113350681 

noncomputable def Ns60p1241 := nat_lit 77699957781841008798673975991839674870683759594523143 

noncomputable def Ns60p1242 := nat_lit 215066530215756769705446132315722563370316988416000 

noncomputable def Ns60p1243 := nat_lit 559223296000000000000000000 

noncomputable def Ns60p1244 := nat_lit 617115878876659846648987243520000 

noncomputable def Ns60p1245 := nat_lit 978009348799590814930734869975470080 

noncomputable def Ns60p1246 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz117 264134 1000 279068079824 16000000 528268 4000 2000 Ns60p1244 Ns60p1245 (@Eq.refl Real qz117) rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns60p1247 := nat_lit 1591295135372103860196843028312876541351603396495833968640 

noncomputable abbrev qz988 := (Real.log (Enclosure.sfrac Bool.false 279068079824 16000000))

noncomputable abbrev qz989 := (@HSub.hSub Real Real Real qz11 qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 528268))))

noncomputable abbrev qz749 := (@HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 264134 4000) qz988) (@HMul.hMul Real Real Real qz5 qz12 qz989))

noncomputable abbrev qz990 := (Enclosure.sfrac Bool.false 264134 2000)

noncomputable abbrev qz435 := (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 qz749 qz990) (@HMul.hMul Real Real Real qz5 qz990 (Real.log Real.pi)))

noncomputable def Ns60p1248 := @Enclosure.Real.IsNear.addLit_ft_p qz435 (Enclosure.sfrac Bool.true Ns60p1244 Ns60p1245) 1627078428818810274483 4503599627370496000 8756242161433166251199 Ns60p1243 Ns60p1244 Ns60p1245 0 1 Ns60p1247 

noncomputable def Ns60p1249 := nat_lit 54595692498467609676041158656000 

noncomputable abbrev qz436 := (@HSub.hSub Real Real Real qz11 qz749 qz990)

noncomputable def Ns60p1250 := @Enclosure.Real.IsNear.subLit_ff_p qz436 (@HMul.hMul Real Real Real qz5 qz990 (Real.log Real.pi)) 2307937310485218788019 4503599627370496000 4252094254936039201 546116500000000000000000 5072793972987 33554432000 132067 16777216000 Ns60p1249 1627078428818810274483 4503599627370496000 

noncomputable def Ns60p1251 := nat_lit 4615874620970437576038000 

noncomputable abbrev qz437 := qz749

noncomputable def Ns60p1252 := @Enclosure.Real.IsNear.subLit_ff_p qz437 qz990 2902714202473158083251 4503599627370496000 4252094254936039201 546116500000000000000000 264134 2000 0 1 Ns60p1251 2307937310485218788019 4503599627370496000 4252094254936039201 546116500000000000000000 

noncomputable def Ns60p1253 := nat_lit 6536331300310580611200366862294581248 

noncomputable def Ns60p1254 := nat_lit 11807121878630149742657536 

noncomputable def Ns60p1255 := nat_lit 1286948550016365294912239229540187993271147888640 

noncomputable def Ns60p1256 := nat_lit 419729824077696700821212061451630618681540608 

noncomputable def Ns60p1257 := nat_lit 246116944602171627766721451130040085577728 

noncomputable def Ns60p1258 := BSN.log_dyadic_bound 16924079824 541212079824 3 2 Ns60p1255 33554432 8737864 Ns60p1256 Ns60p1257 2099225 558136159648 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 16924079824) (BSN.artanhQ 541212079824) 0 2 Ns60p1256 Ns60p1255 Ns60p1257 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz750 := qz988

noncomputable def Ns60p1259 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 264134 4000) qz750 264134 4000 0 1 21992478293609153 2251799813685248 62500007645631 546116500000000000000 2904480630802080009251 4503599627370496000 8254188509735549277 1092233000000000000000000 (Enclosure.Real.IsNear.const Bool.false 264134 4000) (BSN.isNear_log_sfrac 279068079824 16000000 21992478293609153 2251799813685248 62500007645631 546116500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 279068079824) qz650)) Bool.false Ns60p1254 Ns60p84 1000000122330096 8737864000000000000000 21992478293609153 2251799813685248 62500007645631 546116500000000000000 (BSN.log_rat_reduce_isNear 279068079824 16000000 14 558136159648 524288000000 2099225 33554432 24973259072661432 36028797018963968 8737864 1000000000000000 rfl rfl rfl rfl (Ns60p1258 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p1260 := BSN.arctan_dyadic_bound_f 1000 528268 1 0 4194304 1092233 0 1 1 0 1 1 7939 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 528268) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 528268) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz991 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 528268)))

noncomputable abbrev qz751 := qz991

noncomputable abbrev qz438 := qz751

noncomputable def Ns60p1261 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz438 884279719003555 562949953421312 1 2000000000000000 7939 4194304 1 1092233 3704468702855274954752 883214164460963 562949953421312 2000000001092233 2184466000000000000000 qz15 (Ns60p1260 rfl) rfl rfl 

noncomputable abbrev qz752 := (@HMul.hMul Real Real Real qz5 qz12 qz989)

noncomputable abbrev qz439 := qz752

noncomputable abbrev qz753 := qz989

noncomputable abbrev qz440 := qz753

noncomputable abbrev qz754 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 264134 4000) qz988)

noncomputable def Ns60p1262 := @Enclosure.Real.IsNear.subLit_ff_p qz754 qz439 2904480630802080009251 4503599627370496000 8254188509735549277 1092233000000000000000000 883214164460963 2251799813685248 2000000001092233 8737864000000000000000 Ns60p1253 2902714202473158083251 4503599627370496000 4252094254936039201 546116500000000000000000 (Ns60p1259 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz12 qz440 1 4 0 1 883214164460963 562949953421312 2000000001092233 2184466000000000000000 883214164460963 2251799813685248 2000000001092233 8737864000000000000000 qz335 Ns60p1261 rfl) 

noncomputable def Ns60p1263 := @Ns60p1248 Ns60p1241 Ns60p1242 8756242161433166251199 Ns60p1243 (@Ns60p1250 8756242161433166251199 Ns60p1243 (Ns60p1252 (Ns60p1262 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 264134 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz990 (Real.log Real.pi) 264134 2000 0 1 38410761 33554432 1 16777216 5072793972987 33554432000 132067 16777216000 (Enclosure.Real.IsNear.const Bool.false 264134 2000) RS061to078.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns60p1244 Ns60p1245) 

noncomputable def Ns60p1264 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz117) Bool.false Ns60p1241 Ns60p1242 8756242161433166251199 Ns60p1243 3030664449 8388608 133 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz117) (@HAdd.hAdd Real Real Real qz336 qz435 (Enclosure.sfrac Bool.true Ns60p1244 Ns60p1245)) Bool.false Ns60p1241 Ns60p1242 8756242161433166251199 Ns60p1243 Ns60p1246 (Ns60p1263 rfl rfl)) 

noncomputable def Ns60p1265 := nat_lit 1899218831084355969875968 

noncomputable def Ns60p1266 := nat_lit 140060585096573176378898705599599487877766342829762986703847907856263051513734103040000 

noncomputable def Ns60p1267 := nat_lit 281553971311907369871759344539032062776282584232666189392600357120643799449600000000 

noncomputable def Ns60p1268 := nat_lit 366369492632710469060180428107792606816321678465383505632013643807255521146385203200000 

noncomputable def Ns60p1269 := BSN.sin_dyadic_bound_f 26989522880 17179869184 3 2 8388608 2186600 Ns60p1266 Ns60p94 Ns60p1267 Ns60p1268 Ns60p97 Ns60p1267 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26989522880) qz655 0 2 Ns60p1266 Ns60p94 Ns60p1267 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26989522880) qz656 0 2 Ns60p1268 Ns60p97 Ns60p1267 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1270 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz117) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3030664449) qz337) Bool.false 3030664449 8388608 133 8388608 Bool.true 8388607 8388608 1 1092233 (Ns60p1264 rfl) (Enclosure.sfrac_false_div 3030664449 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3030664449) qz337) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns60p1265) qz657) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 57 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q1 3030664449 8388608 226375608064910080 72057594037927936 57 Ns60p1265 Ns60p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 Ns60p1265 Ns60p84 26989522880 17179869184 2186600 2184466 (Ns60p1269 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p1271 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz117) Bool.false Ns60p1241 Ns60p1242 8756242161433166251199 Ns60p1243 24245315597 67108864 1052 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz117) (@HAdd.hAdd Real Real Real qz336 qz435 (Enclosure.sfrac Bool.true Ns60p1244 Ns60p1245)) Bool.false Ns60p1241 Ns60p1242 8756242161433166251199 Ns60p1243 Ns60p1246 (Ns60p1263 rfl rfl)) 

noncomputable def Ns60p1272 := Ns60p1240 23541 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 113 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 43217114 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 45 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 27163248 67108864) (@Eq.refl Real qz117) rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz117) qz117 1) Bool.true 8388607 8388608 153655597 9162314481664 67108856 67108864 1126 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz117) qz117 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz117)) Bool.true 8388607 8388608 153655597 9162314481664 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz117) qz117) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz117)) Bool.true 8388607 8388608 153655597 9162314481664 8388607 8388608 153655597 9162314481664 (Ns60p1270 rfl rfl) rfl)) rfl) (Ns60p1271 rfl) RS061to078.d7 

noncomputable def Ns60p1273 := nat_lit 298189943296028383559011023856760970942424741241769201319723632385 

noncomputable def Ns60p1274 := nat_lit 23632761447081020401285489317987833588426464474149975059040001 

noncomputable def Ns60p1275 := nat_lit 780935398447255254335807743118335324547207346119294522544418686721 

noncomputable def Ns60p1276 := BSN.sin_dyadic_bound_f 46955807 67108864 3 2 67108864 33554432 Ns60p1273 Ns60p119 Ns60p1274 Ns60p1275 Ns60p122 Ns60p1274 43217114 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 46955807) qz339 0 2 Ns60p1273 Ns60p119 Ns60p1274 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 46955807) (BSN.sinOddQ 67108864) 0 2 Ns60p1275 Ns60p122 Ns60p1274 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1277 := nat_lit 611645428502670559410246147601 

noncomputable def Ns60p1278 := BSN.sin_dyadic_bound_f 27965651 67108864 2 1 67108864 33554432 Ns60p1277 Ns60p115 Ns60p1277 Ns60p1277 Ns60p116 Ns60p1277 27163248 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 27965651) qz339 0 1 Ns60p1277 Ns60p115 Ns60p1277 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 27965651) (BSN.sinOddQ 67108864) 0 1 Ns60p1277 Ns60p116 Ns60p1277 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1279 := nat_lit 17614735036227232603776903841 

noncomputable def Ns60p1280 := BSN.sin_dyadic_bound_f 11520439 67108864 2 1 67108864 33554432 Ns60p1279 Ns60p115 Ns60p1279 Ns60p1279 Ns60p116 Ns60p1279 11463938 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 11520439) qz339 0 1 Ns60p1279 Ns60p115 Ns60p1279 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 11520439) (BSN.sinOddQ 67108864) 0 1 Ns60p1279 Ns60p116 Ns60p1279 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1281 := nat_lit 669671883710592913118559094309677475697993834541306989428426219776 

noncomputable def Ns60p1282 := nat_lit 385803287500721895504101750541958049714380944287279064442020096 

noncomputable def Ns60p1283 := nat_lit 2008244044556777295564669079427948510994552741735346410156394619136 

noncomputable def Ns60p1284 := BSN.cos_dyadic_bound_f 66572634 67108864 3 2 67108864 33554432 Ns60p1281 Ns60p103 Ns60p1282 Ns60p1283 Ns60p106 Ns60p1282 36709133 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 66572634) qz338 0 2 Ns60p1281 Ns60p103 Ns60p1282 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 66572634) (BSN.cosOddQ 67108864) 0 2 Ns60p1283 Ns60p106 Ns60p1282 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1285 := Ns60p1238 40070 BSN.abs_quadSignPos (BSN.cos_quad_nat3 3 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 11463938 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 40 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 36709133 67108864) (@Eq.refl Real qz117) rfl rfl (Ns60p1272 RS061to078.d9 RS061to078.d11 RS061to078.d13 RS061to078.d17 (Ns60p1276 rfl rfl) (Ns60p1278 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns60p1271 rfl) RS061to078.d19 RS061to078.d21 RS061to078.d23 RS061to078.d25 RS061to078.d17 (Ns60p1280 rfl rfl) (Ns60p1284 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns60p1286 := nat_lit 866538128701076130251493252721 

noncomputable def Ns60p1287 := BSN.sin_dyadic_bound_f 30510331 67108864 2 1 67108864 33554432 Ns60p1286 Ns60p115 Ns60p1286 Ns60p1286 Ns60p116 Ns60p1286 29470074 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 30510331) qz339 0 1 Ns60p1286 Ns60p115 Ns60p1286 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 30510331) (BSN.sinOddQ 67108864) 0 1 Ns60p1286 Ns60p116 Ns60p1286 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1288 := Ns60p1236 Bool.true 91201893 40070 Bool.true 30510331 3537118876014220 1 Bool.false 29470074 Bool.false Bool.true 79170786 47304 BSN.abs_quadSignPos qz927 (BSN.sfrac_eq_quadSignPos_mul Bool.false 29470074 67108864) (@Eq.refl Real qz117) rfl (Ns60p1285 rfl rfl) (Ns60p1271 rfl) RS061to078.d27 RS061to078.d29 RS061to078.d17 (Ns60p1287 rfl rfl) rfl 

noncomputable def Ns60p1289 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz117) qz117 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz117) qz117 6) 79170786 67108864 47304 67108864 79170786 67108864 47304 67108864 10626123020894208 39585393 16777216 5913 4194304 (Ns60p1288 rfl rfl rfl rfl) 

noncomputable def Ns60p1290 := @Enclosure.Real.IsNear.mulLit_ff qz987 (Zeta.RiemannSiegel.correction qz119) 1647209 4194304 1 4194304 3370213511343 8796093022208 185525657584281 4803691534962655232 5551446027805791687 36893488147419103232 

noncomputable abbrev qz992 := (@HPow.hPow Real Real Real qz326 qz118 qz8)

noncomputable def Ns60p1291 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz992 1 1 0 1 1647209 4194304 1 4194304 1647209 4194304 1 4194304 

noncomputable def Ns60p1292 := @Enclosure.Real.IsNear.sqrt_image qz118 176321198963 4194304000 132067 4194304000 27194561 27194582 4194304 (@Enclosure.Real.IsNear.of_eq qz118 (@HMul.hMul Real Real Real qz5 qz117 qz3) Bool.false 176321198963 4194304000 132067 4194304000 (BSN.t_div_two_pi_mk qz117 264134 1000 (@Eq.refl Real qz117)) (@Enclosure.Real.IsNear.mulLit_ff qz117 qz3 264134 1000 0 1 1335089 8388608 1 8388608 176321198963 4194304000 132067 4194304000 (Enclosure.Real.IsNear.const Bool.false 264134 1000) RS061to078.d32 rfl)) 

noncomputable abbrev qz755 := (Real.sqrt qz986)

noncomputable abbrev qz441 := qz755

noncomputable abbrev qz120 := qz441

noncomputable def Ns60p1293 := @Enclosure.Real.IsNear.sqrt_image qz120 54389143 8388608 21 8388608 10679993 10679998 4194304 (@Enclosure.Real.IsNear.recentre' qz120 Bool.false 54389143 8388608 21 8388608 54389143 8388608 21 8388608 (Ns60p1292 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns60p1294 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz120) 21359991 8388608 5 8388608 1647208 1647210 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz120) Bool.false 21359991 8388608 5 8388608 21359991 8388608 5 8388608 (Ns60p1293 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns60p1295 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz120)) Bool.false 3294418 8388608 2 8388608 1647209 4194304 1 4194304 (Ns60p1294 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz121 := (Real.cos (@HMul.hMul Real Real Real qz323 qz320 qz434))

noncomputable abbrev qz442 := (@HSub.hSub Real Real Real qz647 (@HMul.hMul Real Real Real qz644 qz748 qz748) qz748)

noncomputable abbrev qz122 := (@HMul.hMul Real Real Real qz323 qz320 (@HSub.hSub Real Real Real qz327 qz442 qz344))

noncomputable def Ns60p1296 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz119) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz121) (Real.cos qz122)) Bool.false 3370213511343 

noncomputable def Ns60p1297 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz121) (Real.cos qz122) 2108211 2097152 9 

noncomputable abbrev qz993 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz121))

noncomputable def Ns60p1298 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz121) (@Neg.neg Real Real.instNeg qz993) Bool.true 2108211 2097152 9 524288 (BSN.inv_eq_neg_inv_neg qz121) 

noncomputable def Ns60p1299 := @Enclosure.Real.IsNear.recentre' qz993 Bool.false 8432844 8388608 144 8388608 2108211 2097152 

noncomputable def Ns60p1300 := @Enclosure.Real.IsNear.recentre' qz121 Bool.true 8344604 8388608 153655597 9162314481664 2086151 2097152 153655597 9162314481664 

noncomputable abbrev qz123 := (@HMul.hMul Real Real Real qz323 qz320 qz434)

noncomputable def Ns60p1301 := @Enclosure.Real.IsNear.cos_image qz123 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3186749) qz714) Bool.false 3186749 1048576 133 8388608 Bool.true 8344604 8388608 1 

noncomputable def Ns60p1302 := nat_lit 566707583624778571215915347 

noncomputable def Ns60p1303 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz119 884279719003555 140737488355328 1 500000000000000 4057495 8388608 21 8388608 3587960538458329394725 1180591620717411303424 Ns60p1302 

noncomputable def Ns60p1304 := @Enclosure.Real.IsNear.subLit_ff_p qz120 qz1 54389143 8388608 21 8388608 6 1 0 1 4057495 4057495 8388608 21 

noncomputable def Ns60p1305 := @Ns60p1304 8388608 (@Enclosure.Real.IsNear.recentre' qz120 Bool.false 54389143 8388608 21 8388608 54389143 8388608 21 8388608 (Ns60p1292 rfl rfl rfl rfl rfl rfl) rfl) qz345 

noncomputable def Ns60p1306 := @Enclosure.Real.IsNear.recentre' qz123 Bool.false 3587960538458329394725 1180591620717411303424 Ns60p1302 Ns60p144 3186749 1048576 133 8388608 (@Ns60p1303 Ns60p144 RS061to078.d31 (Ns60p1305 rfl rfl) rfl) 

noncomputable def Ns60p1307 := nat_lit 106830597148089451294544755493167680034000949701763879765103278931662487641172606664960 

noncomputable def Ns60p1308 := nat_lit 163958834342962796881478903431190031925298179846950992579655966368118655406498857216 

noncomputable def Ns60p1309 := nat_lit 279528963941774242195523393781312473370694861689629383492046287542139085046698685972736 

noncomputable def Ns60p1310 := BSN.sin_dyadic_bound_f 25225620206 17179869184 3 2 8388608 2186600 Ns60p1307 Ns60p94 Ns60p1308 Ns60p1309 Ns60p97 Ns60p1308 8344604 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 25225620206) qz655 0 2 Ns60p1307 Ns60p94 Ns60p1308 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 25225620206) qz656 0 2 Ns60p1309 Ns60p97 Ns60p1308 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz756 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable def Ns60p1311 := @Ns60p1301 1092233 (Ns60p1306 rfl) (Enclosure.sfrac_false_div 3186749 1048576) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3186749) qz714) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 221886901883274472194048) qz756) 226375608064910080 72057594037927936 Bool.false 8344604 8388608 0 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q1 3186749 1048576 226375608064910080 72057594037927936 0 221886901883274472194048 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8344604 8388608 221886901883274472194048 151115727451828646838272 25225620206 17179869184 2186600 2184466 (Ns60p1310 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p1312 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz121) 2086151 2097152 153655597 9162314481664 4216350 4216494 4194304 (@Enclosure.Real.IsNear.neg qz121 Bool.true 2086151 2097152 153655597 9162314481664 (Ns60p1300 (Ns60p1311 rfl rfl) rfl)) 

noncomputable def Ns60p1313 := Ns60p1298 (@Enclosure.Real.IsNear.neg qz993 Bool.false 2108211 2097152 9 524288 (@Ns60p1299 9 524288 (Ns60p1312 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p1314 := @Enclosure.Real.IsNear.recentre' (Real.cos qz122) Bool.true 1598613 4194304 

noncomputable def Ns60p1315 := @Enclosure.Real.IsNear.cos_image qz122 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8228487)) qz660) Bool.true 8228487 4194304 

noncomputable def Ns60p1316 := nat_lit 19428965864607480954898553645 

noncomputable def Ns60p1317 := nat_lit 9352726044167507572691290546248121 

noncomputable def Ns60p1318 := @Enclosure.Real.IsNear.recentre' qz122 Bool.true Ns60p1316 Ns60p159 Ns60p1317 

noncomputable abbrev qz124 := (@HSub.hSub Real Real Real qz327 qz442 qz344)

noncomputable def Ns60p1319 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz124 884279719003555 140737488355328 1 500000000000000 21971515853039 

noncomputable abbrev qz125 := qz442

noncomputable def Ns60p1320 := @Enclosure.Real.IsNear.subLit_tf qz125 qz23 17573469341935 70368744177664 346575999 70368744177664 1 16 

noncomputable abbrev qz443 := (@HMul.hMul Real Real Real qz644 qz748 qz748)

noncomputable abbrev qz126 := qz443

noncomputable def Ns60p1321 := @Enclosure.Real.IsNear.subLit_ff_n qz126 qz119 16463265675025 70368744177664 170415231 70368744177664 4057495 8388608 21 8388608 

noncomputable def Ns60p1322 := @Enclosure.Real.IsNear.mulLit_ff qz119 qz119 4057495 8388608 21 8388608 4057495 8388608 21 8388608 16463265675025 70368744177664 

noncomputable def Ns60p1323 := nat_lit 8841014906197207526244519909374240653922705945056973356790918761572832101453718966921761 

noncomputable def Ns60p1324 := nat_lit 96347366435918807482189449335735035541960574338095172600461725511106943048800168481 

noncomputable def Ns60p1325 := nat_lit 53322484417944206247011401186795835615818192387935637910525034067944259377416234007685665 

noncomputable def Ns60p1326 := BSN.cos_dyadic_bound_t 8228487 4194304 4 3 4194304 1092233 Ns60p1323 Ns60p168 Ns60p1324 Ns60p1325 Ns60p171 Ns60p1324 1598613 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 8228487) (BSN.cosEvenQ 4194304) 0 3 Ns60p1323 Ns60p168 Ns60p1324 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 8228487) (BSN.cosOddQ 4194304) 0 3 Ns60p1325 Ns60p171 Ns60p1324 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1327 := @Ns60p1314 73092297 2290578620416 1598613 4194304 73092297 2290578620416 (@Ns60p1315 65 2097152 Bool.true 1598613 4194304 1 1092233 (@Ns60p1318 Ns60p162 8228487 4194304 65 2097152 (@Ns60p1319 70368744177664 346575999 70368744177664 Ns60p1316 Ns60p159 Ns60p1317 Ns60p162 RS061to078.d31 (@Ns60p1320 0 1 351544253648624 21971515853039 70368744177664 346575999 70368744177664 (@Ns60p1321 147416945509510676480 17573469341935 70368744177664 346575999 70368744177664 (@Ns60p1322 170415231 70368744177664 (Ns60p1305 rfl rfl) (Ns60p1305 rfl rfl) rfl) (Ns60p1305 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 8228487 4194304) (BSN.cos_neg_of_bound 8228487 4194304 Bool.true 1598613 4194304 1 1092233 (Ns60p1326 rfl rfl)) rfl rfl) 

noncomputable def Ns60p1328 := @Ns60p1290 614880495272941710939 Ns60p1233 (Ns60p1291 qz25 (@Enclosure.Real.IsNear.of_eq qz992 (@Inv.inv Real Real.instInv (Real.sqrt qz120)) Bool.false 1647209 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz118 (BSN.t_div_two_pi_nonneg qz117 264134 1000 (@Eq.refl Real qz117))) Ns60p1295) rfl) (@Ns60p1296 8796093022208 185525657584281 4803691534962655232 (BSN.correction_mk qz119 (BSN.cos_two_pi_p_ne_zero_mk qz117 264134 1000 6 (@Eq.refl Real qz117) rfl rfl (@BSN.floor_sqrt_eq_dec qz117 264134 1000 6 (@Eq.refl Real qz117) rfl rfl rfl))) (@Ns60p1297 524288 1598613 4194304 73092297 2290578620416 3370213511343 8796093022208 185525657584281 4803691534962655232 Ns60p1313 (Ns60p1327 rfl) rfl)) 

noncomputable def Ns60p1329 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz117) (hardyZApproximantRS₀ qz117) Bool.true 92600645814971143623 36893488147419103232 57423336587741302484571 Ns60p1233 (@Eq.refl Real (hardyZApproximantRS₀ qz117)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz117) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz117) qz117 6) (@HMul.hMul Real Real Real qz5 qz987 (Zeta.RiemannSiegel.correction qz119))) Bool.true 92600645814971143623 36893488147419103232 57423336587741302484571 Ns60p1233 (BSN.hardyZApproximantRS₀_eq qz117 6 (@BSN.floor_sqrt_eq_dec qz117 264134 1000 6 (@Eq.refl Real qz117) rfl rfl rfl)) (@Ns60p1235 92600645814971143623 36893488147419103232 57423336587741302484571 Ns60p1233 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz117) qz117 6) (@HAdd.hAdd Real Real Real qz336 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz117) qz117 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz117) qz117 6)) Bool.true 39585393 16777216 5913 4194304 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz117) qz117 6) (Ns60p1289 (Ns60p1288 rfl rfl rfl rfl) rfl rfl)) (Ns60p1328 rfl) rfl rfl)) 

theorem RS061to078.d52 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz117) Bool.true 92600645814971143623 36893488147419103232 57423336587741302484571 Ns60p1233 := Ns60p1329 

noncomputable def Ns60p1330 := nat_lit 38221521116675961320898560 

noncomputable abbrev qz757 := (Enclosure.sfrac Bool.false 265813 1000)

noncomputable abbrev qz444 := qz757

noncomputable abbrev qz127 := qz444

noncomputable abbrev qz994 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 265813 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz758 := qz994

noncomputable abbrev qz445 := qz758

noncomputable abbrev qz128 := qz445

noncomputable abbrev qz759 := (@HSub.hSub Real Real Real qz920 (Real.sqrt qz994) qz914)

noncomputable abbrev qz446 := qz759

noncomputable abbrev qz129 := qz446

noncomputable abbrev qz995 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz326 qz128 qz8))

noncomputable def Ns60p1331 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz127) qz127 6) (@HMul.hMul Real Real Real qz5 qz995 (Zeta.RiemannSiegel.correction qz129)) 10805629 16777216 23799 16777216 692048493798825491 4611686018427387904 621685860516557279947 Ns60p1233 Ns60p1330 

noncomputable def Ns60p1332 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz127) qz127 Real.sin BSN.quadSignPos 5 6 265813 1000 71 67108864 33554432 1125899906842624 Bool.false 24456117921 1059 120242927 63 27397080 8 

noncomputable def Ns60p1333 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz127) qz127 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 265813 1000 2 40 67108864 33554432 1125899906842624 Bool.false 24456117921 1059 

noncomputable def Ns60p1334 := Ns60p1333 93032624 62 33554424 8 108007536 62 30011992 8 Bool.false 7499083 23684 Bool.true 62334248 Bool.true 37114963 3537118876014220 1 Bool.false 40181654 Bool.true Bool.false 57104488 Bool.false Bool.false 12946160 

noncomputable def Ns60p1335 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz127) qz127 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 265813 1000 114 46 67108864 33554432 1125899906842624 Bool.false 24456117921 1059 

noncomputable def Ns60p1336 := Ns60p1335 46516304 62 47453136 16 73726608 62 38745320 8 Bool.false 67108856 1126 Bool.false 74242900 Bool.false 9566643 3537118876014220 1 Bool.false 30062603 Bool.true Bool.false 66428135 Bool.true Bool.false 7499083 

noncomputable def Ns60p1337 := nat_lit 416832732413545173901679988565628276599504757763533789 

noncomputable def Ns60p1338 := nat_lit 1143810773224252012544894126803578992457743943598080 

noncomputable def Ns60p1339 := nat_lit 636980613892420306608083340640000 

noncomputable def Ns60p1340 := nat_lit 1015908044998294468315064633049241920 

noncomputable def Ns60p1341 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz127 265813 1000 282627203876 16000000 531626 4000 2000 Ns60p1339 Ns60p1340 (@Eq.refl Real qz127) rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns60p1342 := nat_lit 133386474372334455648537596341001048511841522484330812480 

noncomputable abbrev qz996 := (Real.log (Enclosure.sfrac Bool.false 282627203876 16000000))

noncomputable abbrev qz997 := (@HSub.hSub Real Real Real qz11 qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 531626))))

noncomputable abbrev qz760 := (@HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 265813 4000) qz996) (@HMul.hMul Real Real Real qz5 qz12 qz997))

noncomputable abbrev qz998 := (Enclosure.sfrac Bool.false 265813 2000)

noncomputable abbrev qz447 := (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 qz760 qz998) (@HMul.hMul Real Real Real qz5 qz998 (Real.log Real.pi)))

noncomputable def Ns60p1343 := @Enclosure.Real.IsNear.addLit_ft_p qz447 (Enclosure.sfrac Bool.true Ns60p1339 Ns60p1340) 131298009229773171069 360287970189639680 17622177271058756947161 Ns60p186 Ns60p1339 Ns60p1340 0 1 Ns60p1342 

noncomputable def Ns60p1344 := nat_lit 220281506121789812202956390400000 

noncomputable abbrev qz448 := (@HSub.hSub Real Real Real qz11 qz760 qz998)

noncomputable def Ns60p1345 := @Enclosure.Real.IsNear.subLit_ff_p qz448 (@HMul.hMul Real Real Real qz5 qz998 (Real.log Real.pi)) 4652823919193321426229 9007199254740992000 17113314532581171253 Ns60p192 10210079613693 67108864000 265813 33554432000 Ns60p1344 131298009229773171069 360287970189639680 

noncomputable def Ns60p1346 := nat_lit 9305647838386642852458000 

noncomputable abbrev qz449 := qz760

noncomputable def Ns60p1347 := @Enclosure.Real.IsNear.subLit_ff_p qz449 qz998 5849939246943555079477 9007199254740992000 17113314532581171253 Ns60p192 265813 2000 0 1 Ns60p1346 4652823919193321426229 9007199254740992000 17113314532581171253 Ns60p192 

noncomputable def Ns60p1348 := nat_lit 13172892106337517318611085968902455296 

noncomputable def Ns60p1349 := nat_lit 11822442548101711866626048 

noncomputable def Ns60p1350 := nat_lit 1321136926236792075972765185002655279725668560640 

noncomputable def Ns60p1351 := nat_lit 623106520134648889318404279816468063353899008 

noncomputable def Ns60p1352 := nat_lit 528095911860740020795695965469877677712128 

noncomputable def Ns60p1353 := BSN.log_dyadic_bound 20483203876 544771203876 3 2 Ns60p1350 33554432 8737864 Ns60p1351 Ns60p1352 2524459 565254407752 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 20483203876) (BSN.artanhQ 544771203876) 0 2 Ns60p1351 Ns60p1350 Ns60p1352 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz761 := qz996

noncomputable def Ns60p1354 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 265813 4000) qz761 265813 4000 0 1 22021015264283329 2251799813685248 62500007645631 546116500000000000000 5853472130444944531477 9007199254740992000 16613314532308113003 Ns60p192 (Enclosure.Real.IsNear.const Bool.false 265813 4000) (BSN.isNear_log_sfrac 282627203876 16000000 22021015264283329 2251799813685248 62500007645631 546116500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 282627203876) qz650)) Bool.false Ns60p1349 Ns60p84 1000000122330096 8737864000000000000000 22021015264283329 2251799813685248 62500007645631 546116500000000000000 (BSN.log_rat_reduce_isNear 282627203876 16000000 14 565254407752 524288000000 2524459 33554432 24973259072661432 36028797018963968 8737864 1000000000000000 rfl rfl rfl rfl (Ns60p1353 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p1355 := BSN.arctan_dyadic_bound_f 1000 531626 1 0 4194304 1092233 0 1 1 0 1 1 7889 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 531626) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 531626) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz999 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 531626)))

noncomputable abbrev qz762 := qz999

noncomputable abbrev qz450 := qz762

noncomputable def Ns60p1356 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz450 884279719003555 562949953421312 1 2000000000000000 7889 4194304 1 1092233 3704496850352946020352 883220875347363 562949953421312 2000000001092233 2184466000000000000000 qz15 (Ns60p1355 rfl) rfl rfl 

noncomputable abbrev qz763 := (@HMul.hMul Real Real Real qz5 qz12 qz997)

noncomputable abbrev qz451 := qz763

noncomputable abbrev qz764 := qz997

noncomputable abbrev qz452 := qz764

noncomputable abbrev qz765 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 265813 4000) qz996)

noncomputable def Ns60p1357 := @Enclosure.Real.IsNear.subLit_ff_p qz765 qz451 5853472130444944531477 9007199254740992000 16613314532308113003 Ns60p192 883220875347363 2251799813685248 2000000001092233 8737864000000000000000 Ns60p1348 5849939246943555079477 9007199254740992000 17113314532581171253 Ns60p192 (Ns60p1354 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz12 qz452 1 4 0 1 883220875347363 562949953421312 2000000001092233 2184466000000000000000 883220875347363 2251799813685248 2000000001092233 8737864000000000000000 qz335 Ns60p1356 rfl) 

noncomputable def Ns60p1358 := @Ns60p1343 Ns60p1337 Ns60p1338 17622177271058756947161 Ns60p186 (@Ns60p1345 17622177271058756947161 Ns60p186 (Ns60p1347 (Ns60p1357 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 265813 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz998 (Real.log Real.pi) 265813 2000 0 1 38410761 33554432 1 16777216 10210079613693 67108864000 265813 33554432000 (Enclosure.Real.IsNear.const Bool.false 265813 2000) RS061to078.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns60p1339 Ns60p1340) 

noncomputable def Ns60p1359 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz127) Bool.false Ns60p1337 Ns60p1338 17622177271058756947161 Ns60p186 764253685 2097152 133 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz127) (@HAdd.hAdd Real Real Real qz336 qz447 (Enclosure.sfrac Bool.true Ns60p1339 Ns60p1340)) Bool.false Ns60p1337 Ns60p1338 17622177271058756947161 Ns60p186 Ns60p1341 (Ns60p1358 rfl rfl)) 

noncomputable def Ns60p1360 := nat_lit 139920140618273302408799967379724303184687119425916701249431438053652370936290183840000 

noncomputable def Ns60p1361 := nat_lit 280990733578493806342877563013001225702706077174988622377342122319202177936100000000 

noncomputable def Ns60p1362 := nat_lit 366002573764922040146111446130590220642090455323879474074185688609144167973625367200000 

noncomputable def Ns60p1363 := BSN.sin_dyadic_bound_f 26982768030 17179869184 3 2 8388608 2186600 Ns60p1360 Ns60p94 Ns60p1361 Ns60p1362 Ns60p97 Ns60p1361 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26982768030) qz655 0 2 Ns60p1360 Ns60p94 Ns60p1361 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26982768030) qz656 0 2 Ns60p1362 Ns60p97 Ns60p1361 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz766 := (@Nat.cast Real Real.instNatCast 2097152)

noncomputable abbrev qz767 := (@Nat.cast Real Real.instNatCast 302231454903657293676544)

noncomputable def Ns60p1364 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz127) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 764253685) qz766) Bool.false 764253685 2097152 133 8388608 Bool.false 8388607 8388608 1 1092233 (Ns60p1359 rfl) (Enclosure.sfrac_false_div 764253685 2097152) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 764253685) qz766) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474685875191637459599360) qz767) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 57 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q3 764253685 2097152 226375608064910080 72057594037927936 57 474685875191637459599360 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 474685875191637459599360 302231454903657293676544 26982768030 17179869184 2186600 2184466 (Ns60p1363 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p1365 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz127) Bool.false Ns60p1337 Ns60p1338 17622177271058756947161 Ns60p186 24456117921 67108864 1059 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz127) (@HAdd.hAdd Real Real Real qz336 qz447 (Enclosure.sfrac Bool.true Ns60p1339 Ns60p1340)) Bool.false Ns60p1337 Ns60p1338 17622177271058756947161 Ns60p186 Ns60p1341 (Ns60p1358 rfl rfl)) 

noncomputable def Ns60p1366 := Ns60p1336 23684 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 114 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 30062603 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 46 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66428135 67108864) (@Eq.refl Real qz127) rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 1) Bool.false 8388607 8388608 153655597 9162314481664 67108856 67108864 1126 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz127)) Bool.false 8388607 8388608 153655597 9162314481664 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz127) qz127) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz127)) Bool.false 8388607 8388608 153655597 9162314481664 8388607 8388608 153655597 9162314481664 (Ns60p1364 rfl rfl) rfl)) rfl) (Ns60p1365 rfl) RS061to078.d7 

noncomputable def Ns60p1367 := nat_lit 1036180950476411370165001846357839704315500262757452326528000000000 

noncomputable def Ns60p1368 := nat_lit 923080167220828947975530727985643390732637057610000000000000000 

noncomputable def Ns60p1369 := nat_lit 3106696691094792452599054477617547826165035514157136979584000000000 

noncomputable def Ns60p1370 := BSN.cos_dyadic_bound_f 74242900 67108864 3 2 67108864 33554432 Ns60p1367 Ns60p103 Ns60p1368 Ns60p1369 Ns60p106 Ns60p1368 30062603 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 74242900) qz338 0 2 Ns60p1367 Ns60p103 Ns60p1368 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 74242900) (BSN.cosOddQ 67108864) 0 2 Ns60p1369 Ns60p106 Ns60p1368 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1371 := nat_lit 8376030893734089958664723601 

noncomputable def Ns60p1372 := BSN.cos_dyadic_bound_f 9566643 67108864 2 1 67108864 33554432 Ns60p1371 Ns60p630 Ns60p1371 Ns60p1371 Ns60p631 Ns60p1371 66428135 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 9566643) qz338 0 1 Ns60p1371 Ns60p630 Ns60p1371 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 9566643) (BSN.cosOddQ 67108864) 0 1 Ns60p1371 Ns60p631 Ns60p1371 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1373 := nat_lit 514669120169982086793551752792426262231373077188859447976537358336 

noncomputable def Ns60p1374 := nat_lit 227936458443666334838706887849445587960171861058917271397728256 

noncomputable def Ns60p1375 := nat_lit 1543551487593058927710977844601579895518198887844460509386816618496 

noncomputable def Ns60p1376 := BSN.cos_dyadic_bound_f 62334248 67108864 3 2 67108864 33554432 Ns60p1373 Ns60p103 Ns60p1374 Ns60p1375 Ns60p106 Ns60p1374 40181654 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 62334248) qz338 0 2 Ns60p1373 Ns60p103 Ns60p1374 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 62334248) (BSN.cosOddQ 67108864) 0 2 Ns60p1375 Ns60p106 Ns60p1374 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1377 := nat_lit 64662001478712401482097094365685120051058965706049726069249421601 

noncomputable def Ns60p1378 := nat_lit 3600744081503788656745503294656974851849488893661326849093921 

noncomputable def Ns60p1379 := nat_lit 193978802947974196868977792090466046203473198140361855554050076961 

noncomputable def Ns60p1380 := BSN.cos_dyadic_bound_f 37114963 67108864 3 2 67108864 33554432 Ns60p1377 Ns60p103 Ns60p1378 Ns60p1379 Ns60p106 Ns60p1378 57104488 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 37114963) qz338 0 2 Ns60p1377 Ns60p103 Ns60p1378 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 37114963) (BSN.cosOddQ 67108864) 0 2 Ns60p1379 Ns60p106 Ns60p1378 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1381 := Ns60p1334 40318 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 2 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 40181654 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 40 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 57104488 67108864) (@Eq.refl Real qz127) rfl rfl (Ns60p1366 RS061to078.d9 RS061to078.d11 RS061to078.d13 RS061to078.d17 (Ns60p1370 rfl rfl) (Ns60p1372 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns60p1365 rfl) RS061to078.d19 RS061to078.d21 RS061to078.d23 RS061to078.d25 RS061to078.d17 (Ns60p1376 rfl rfl) (Ns60p1380 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns60p1382 := nat_lit 217512240969058800288081477921 

noncomputable def Ns60p1383 := BSN.sin_dyadic_bound_f 21595881 67108864 2 1 67108864 33554432 Ns60p1382 Ns60p115 Ns60p1382 Ns60p1382 Ns60p116 Ns60p1382 21225069 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 21595881) qz339 0 1 Ns60p1382 Ns60p115 Ns60p1382 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 21595881) (BSN.sinOddQ 67108864) 0 1 Ns60p1382 Ns60p116 Ns60p1382 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1384 := Ns60p1332 Bool.false 12946160 40318 Bool.true 21595881 3537118876014220 1 Bool.false 21225069 Bool.false Bool.false 21611258 47598 BSN.abs_quadSignPos qz927 (BSN.sfrac_eq_quadSignPos_mul Bool.false 21225069 67108864) (@Eq.refl Real qz127) rfl (Ns60p1381 rfl rfl) (Ns60p1365 rfl) RS061to078.d27 RS061to078.d29 RS061to078.d17 (Ns60p1383 rfl rfl) rfl 

noncomputable def Ns60p1385 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 6) 21611258 67108864 47598 67108864 21611258 67108864 47598 67108864 2900613947981824 10805629 16777216 23799 16777216 (Ns60p1384 rfl rfl rfl rfl) 

noncomputable def Ns60p1386 := @Enclosure.Real.IsNear.mulLit_ff qz995 (Zeta.RiemannSiegel.correction qz129) 822301 2097152 1 4194304 841599966191 2199023255552 375780031711645 9607383069925310464 692048493798825491 4611686018427387904 

noncomputable abbrev qz1000 := (@HPow.hPow Real Real Real qz326 qz128 qz8)

noncomputable def Ns60p1387 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz1000 1 1 0 1 822301 2097152 1 4194304 822301 2097152 1 4194304 

noncomputable def Ns60p1388 := @Enclosure.Real.IsNear.sqrt_image qz128 354884012357 8388608000 265813 8388608000 27280857 27280878 4194304 (@Enclosure.Real.IsNear.of_eq qz128 (@HMul.hMul Real Real Real qz5 qz127 qz3) Bool.false 354884012357 8388608000 265813 8388608000 (BSN.t_div_two_pi_mk qz127 265813 1000 (@Eq.refl Real qz127)) (@Enclosure.Real.IsNear.mulLit_ff qz127 qz3 265813 1000 0 1 1335089 8388608 1 8388608 354884012357 8388608000 265813 8388608000 (Enclosure.Real.IsNear.const Bool.false 265813 1000) RS061to078.d32 rfl)) 

noncomputable abbrev qz768 := (Real.sqrt qz994)

noncomputable abbrev qz453 := qz768

noncomputable abbrev qz130 := qz453

noncomputable def Ns60p1389 := @Enclosure.Real.IsNear.sqrt_image qz130 54561735 8388608 21 8388608 10696925 10696930 4194304 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 54561735 8388608 21 8388608 54561735 8388608 21 8388608 (Ns60p1388 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns60p1390 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz130) 21393855 8388608 5 8388608 1644601 1644603 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz130) Bool.false 21393855 8388608 5 8388608 21393855 8388608 5 8388608 (Ns60p1389 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns60p1391 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz130)) Bool.false 3289204 8388608 2 8388608 822301 2097152 1 4194304 (Ns60p1390 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz131 := (Real.cos (@HMul.hMul Real Real Real qz323 qz320 qz446))

noncomputable abbrev qz454 := (@HSub.hSub Real Real Real qz647 (@HMul.hMul Real Real Real qz644 qz759 qz759) qz759)

noncomputable abbrev qz132 := (@HMul.hMul Real Real Real qz323 qz320 (@HSub.hSub Real Real Real qz327 qz454 qz344))

noncomputable def Ns60p1392 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz129) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz131) (Real.cos qz132)) Bool.false 841599966191 

noncomputable def Ns60p1393 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz131) (Real.cos qz132) 4195811 4194304 71 

noncomputable abbrev qz1001 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz131))

noncomputable def Ns60p1394 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz131) (@Neg.neg Real Real.instNeg qz1001) Bool.true 4195811 4194304 71 4194304 (BSN.inv_eq_neg_inv_neg qz131) 

noncomputable def Ns60p1395 := @Enclosure.Real.IsNear.recentre' qz1001 Bool.false 8391622 8388608 142 8388608 4195811 4194304 

noncomputable def Ns60p1396 := @Enclosure.Real.IsNear.recentre' qz131 Bool.true 8385595 8388608 153655597 9162314481664 8385595 8388608 153655597 9162314481664 

noncomputable abbrev qz133 := (@HMul.hMul Real Real Real qz323 qz320 qz446)

noncomputable def Ns60p1397 := @Enclosure.Real.IsNear.cos_image qz133 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6644605) qz766) Bool.false 6644605 2097152 133 8388608 Bool.true 8385595 8388608 1 

noncomputable def Ns60p1398 := nat_lit 566707583626261125207017811 

noncomputable def Ns60p1399 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz129 884279719003555 140737488355328 1 500000000000000 4230087 8388608 21 8388608 3740580143720590959285 1180591620717411303424 Ns60p1398 

noncomputable def Ns60p1400 := @Enclosure.Real.IsNear.subLit_ff_p qz130 qz1 54561735 8388608 21 8388608 6 1 0 1 4230087 4230087 8388608 21 

noncomputable def Ns60p1401 := @Ns60p1400 8388608 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 54561735 8388608 21 8388608 54561735 8388608 21 8388608 (Ns60p1388 rfl rfl rfl rfl rfl rfl) rfl) qz345 

noncomputable def Ns60p1402 := @Enclosure.Real.IsNear.recentre' qz133 Bool.false 3740580143720590959285 1180591620717411303424 Ns60p1398 Ns60p144 6644605 2097152 133 8388608 (@Ns60p1399 Ns60p144 RS061to078.d31 (Ns60p1401 rfl rfl) rfl) 

noncomputable abbrev qz769 := (BSN.cosEvenQ 17179869184)

noncomputable abbrev qz770 := (BSN.cosOddQ 17179869184)

noncomputable def Ns60p1403 := BSN.cos_dyadic_bound_f 460453341 17179869184 1 0 8388608 2186600 0 1 1 0 1 1 8385595 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 460453341) qz769 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 460453341) qz770 0 0 rfl) rfl rfl 

noncomputable def Ns60p1404 := @Ns60p1397 1092233 (Ns60p1402 rfl) (Enclosure.sfrac_false_div 6644605 2097152) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6644605) qz766) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8100380855687698186240) qz767) 226375608064910080 72057594037927936 Bool.false 8385595 8388608 0 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q2 6644605 2097152 226375608064910080 72057594037927936 0 8100380855687698186240 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 8385595 8388608 8100380855687698186240 302231454903657293676544 460453341 17179869184 2186600 2184466 (Ns60p1403 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p1405 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz131) 8385595 8388608 153655597 9162314481664 4195740 4195882 4194304 (@Enclosure.Real.IsNear.neg qz131 Bool.true 8385595 8388608 153655597 9162314481664 (Ns60p1396 (Ns60p1404 rfl rfl) rfl)) 

noncomputable def Ns60p1406 := Ns60p1394 (@Enclosure.Real.IsNear.neg qz1001 Bool.false 4195811 4194304 71 4194304 (@Ns60p1395 71 4194304 (Ns60p1405 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p1407 := @Enclosure.Real.IsNear.recentre' (Real.cos qz132) Bool.true 1604648 4194304 

noncomputable def Ns60p1408 := @Enclosure.Real.IsNear.cos_image qz132 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8235017)) qz660) Bool.true 8235017 4194304 

noncomputable def Ns60p1409 := nat_lit 19444384412848706191719792205 

noncomputable def Ns60p1410 := nat_lit 9548344434701562004705133602579673 

noncomputable def Ns60p1411 := @Enclosure.Real.IsNear.recentre' qz132 Bool.true Ns60p1409 Ns60p159 Ns60p1410 

noncomputable abbrev qz134 := (@HSub.hSub Real Real Real qz327 qz454 qz344)

noncomputable def Ns60p1412 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz134 884279719003555 140737488355328 1 500000000000000 21988952132431 

noncomputable abbrev qz135 := qz454

noncomputable def Ns60p1413 := @Enclosure.Real.IsNear.subLit_tf qz135 qz23 17590905621327 70368744177664 353824863 70368744177664 1 16 

noncomputable abbrev qz455 := (@HMul.hMul Real Real Real qz644 qz759 qz759)

noncomputable abbrev qz136 := qz455

noncomputable def Ns60p1414 := @Enclosure.Real.IsNear.subLit_ff_n qz136 qz129 17893636027569 70368744177664 177664095 70368744177664 4230087 8388608 21 8388608 

noncomputable def Ns60p1415 := @Enclosure.Real.IsNear.mulLit_ff qz129 qz129 4230087 8388608 21 8388608 4230087 8388608 21 8388608 17893636027569 70368744177664 

noncomputable def Ns60p1416 := nat_lit 8869359673627055996881737208357684479027943563133847932769686973738608278405198078908641 

noncomputable def Ns60p1417 := nat_lit 97268899105849545153835381818456073469676467480769180079284458278865654620180289761 

noncomputable def Ns60p1418 := nat_lit 53492448410301309666532337076822483130553407855909178414891442617967737535373585411840225 

noncomputable def Ns60p1419 := BSN.cos_dyadic_bound_t 8235017 4194304 4 3 4194304 1092233 Ns60p1416 Ns60p168 Ns60p1417 Ns60p1418 Ns60p171 Ns60p1417 1604648 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 8235017) (BSN.cosEvenQ 4194304) 0 3 Ns60p1416 Ns60p168 Ns60p1417 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 8235017) (BSN.cosOddQ 4194304) 0 3 Ns60p1418 Ns60p171 Ns60p1417 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1420 := @Ns60p1407 149461293 4581157240832 200581 524288 149461293 4581157240832 (@Ns60p1408 133 4194304 Bool.true 1604648 4194304 1 1092233 (@Ns60p1411 Ns60p162 8235017 4194304 133 4194304 (@Ns60p1412 70368744177664 353824863 70368744177664 Ns60p1409 Ns60p159 Ns60p1410 Ns60p162 RS061to078.d31 (@Ns60p1413 0 1 351823234118896 21988952132431 70368744177664 353824863 70368744177664 (@Ns60p1414 147563211622308642816 17590905621327 70368744177664 353824863 70368744177664 (@Ns60p1415 177664095 70368744177664 (Ns60p1401 rfl rfl) (Ns60p1401 rfl rfl) rfl) (Ns60p1401 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 8235017 4194304) (BSN.cos_neg_of_bound 8235017 4194304 Bool.true 1604648 4194304 1 1092233 (Ns60p1419 rfl rfl)) rfl rfl) 

noncomputable def Ns60p1421 := @Ns60p1386 621685860516557279947 Ns60p1233 (Ns60p1387 qz25 (@Enclosure.Real.IsNear.of_eq qz1000 (@Inv.inv Real Real.instInv (Real.sqrt qz130)) Bool.false 822301 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz128 (BSN.t_div_two_pi_nonneg qz127 265813 1000 (@Eq.refl Real qz127))) Ns60p1391) rfl) (@Ns60p1392 2199023255552 375780031711645 9607383069925310464 (BSN.correction_mk qz129 (BSN.cos_two_pi_p_ne_zero_mk qz127 265813 1000 6 (@Eq.refl Real qz127) rfl rfl (@BSN.floor_sqrt_eq_dec qz127 265813 1000 6 (@Eq.refl Real qz127) rfl rfl rfl))) (@Ns60p1393 4194304 200581 524288 149461293 4581157240832 841599966191 2199023255552 375780031711645 9607383069925310464 Ns60p1406 (Ns60p1420 rfl) rfl)) 

noncomputable def Ns60p1422 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz127) (hardyZApproximantRS₀ qz127) Bool.false 2278180188934562285 4611686018427387904 57783213280804673213131 Ns60p1233 (@Eq.refl Real (hardyZApproximantRS₀ qz127)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz127) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz127) qz127 6) (@HMul.hMul Real Real Real qz5 qz995 (Zeta.RiemannSiegel.correction qz129))) Bool.false 2278180188934562285 4611686018427387904 57783213280804673213131 Ns60p1233 (BSN.hardyZApproximantRS₀_eq qz127 6 (@BSN.floor_sqrt_eq_dec qz127 265813 1000 6 (@Eq.refl Real qz127) rfl rfl rfl)) (@Ns60p1331 2278180188934562285 4611686018427387904 57783213280804673213131 Ns60p1233 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz127) qz127 6) (@HAdd.hAdd Real Real Real qz336 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz127) qz127 6)) Bool.false 10805629 16777216 23799 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz127) qz127 6) (Ns60p1385 (Ns60p1384 rfl rfl rfl rfl) rfl rfl)) (Ns60p1421 rfl) rfl rfl)) 

theorem RS061to078.d53 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz127) Bool.false 2278180188934562285 4611686018427387904 57783213280804673213131 Ns60p1233 := Ns60p1422 

noncomputable def Ns60p1423 := nat_lit 65130910573831176738308096 

noncomputable abbrev qz771 := (Enclosure.sfrac Bool.false 267489 1000)

noncomputable abbrev qz456 := qz771

noncomputable abbrev qz137 := qz456

noncomputable abbrev qz1002 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 267489 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz772 := qz1002

noncomputable abbrev qz457 := qz772

noncomputable abbrev qz138 := qz457

noncomputable abbrev qz773 := (@HSub.hSub Real Real Real qz920 (Real.sqrt qz1002) qz914)

noncomputable abbrev qz458 := qz773

noncomputable abbrev qz139 := qz458

noncomputable abbrev qz1003 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz326 qz138 qz8))

noncomputable def Ns60p1424 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz137) qz137 6) (@HMul.hMul Real Real Real qz5 qz1003 (Zeta.RiemannSiegel.correction qz139)) 2900621 4194304 5987 4194304 2771353085518766265 18446744073709551616 2550228738321532867959 Ns60p62 Ns60p1423 

noncomputable def Ns60p1425 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz137) qz137 Real.sin BSN.quadSignPos 5 6 267489 1000 71 67108864 33554432 1125899906842624 Bool.false 24666898520 1065 120242927 63 27397080 8 

noncomputable def Ns60p1426 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz137) qz137 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 267489 1000 2 40 67108864 33554432 1125899906842624 Bool.false 24666898520 1065 

noncomputable def Ns60p1427 := Ns60p1426 93032624 62 33554424 8 108007536 62 30011992 8 Bool.true 24700896 23833 Bool.true 7476327 Bool.true 7354994 3537118876014220 1 Bool.false 66692840 Bool.true Bool.false 66706221 Bool.false Bool.true 28215384 

noncomputable def Ns60p1428 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz137) qz137 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 267489 1000 115 46 67108864 33554432 1125899906842624 Bool.false 24666898520 1065 

noncomputable def Ns60p1429 := Ns60p1428 46516304 62 47453136 16 73726608 62 38745320 8 Bool.true 67108832 1134 Bool.false 101647816 Bool.false 96781447 3537118876014220 1 Bool.false 67003191 Bool.false Bool.false 8609119 Bool.true Bool.true 24700896 

noncomputable def Ns60p1430 := nat_lit 1212731184518103908446507476271665893581344747350851249 

noncomputable def Ns60p1431 := nat_lit 3299361371431187792956087374402294310846450368512000 

noncomputable def Ns60p1432 := nat_lit 657316777275514242584820695520000 

noncomputable def Ns60p1433 := nat_lit 1054951764803060503673918417519695680 

noncomputable def Ns60p1434 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz137 267489 1000 286202460484 16000000 534978 4000 2000 Ns60p1432 Ns60p1433 (@Eq.refl Real qz137) rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns60p1435 := nat_lit 3492665811412139256325941531662397773514272872370451597120 

noncomputable abbrev qz1004 := (Real.log (Enclosure.sfrac Bool.false 286202460484 16000000))

noncomputable abbrev qz1005 := (@HSub.hSub Real Real Real qz11 qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 534978))))

noncomputable abbrev qz774 := (@HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 267489 4000) qz1004) (@HMul.hMul Real Real Real qz5 qz12 qz1005))

noncomputable abbrev qz1006 := (Enclosure.sfrac Bool.false 267489 2000)

noncomputable abbrev qz459 := (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 qz774 qz1006) (@HMul.hMul Real Real Real qz5 qz1006 (Real.log Real.pi)))

noncomputable def Ns60p1436 := @Enclosure.Real.IsNear.addLit_ft_p qz459 (Enclosure.sfrac Bool.true Ns60p1432 Ns60p1433) 3310740688364402390209 9007199254740992000 17731674222321713093333 Ns60p186 Ns60p1432 Ns60p1433 0 1 Ns60p1435 

noncomputable def Ns60p1437 := nat_lit 222180046594713062445810712576000 

noncomputable abbrev qz460 := (@HSub.hSub Real Real Real qz11 qz774 qz1006)

noncomputable def Ns60p1438 := @Enclosure.Real.IsNear.subLit_ff_p qz460 (@HMul.hMul Real Real Real qz5 qz1006 (Real.log Real.pi)) 4689754835714353149121 9007199254740992000 17218064545395248809 Ns60p192 10274456049129 67108864000 267489 33554432000 Ns60p1437 3310740688364402390209 9007199254740992000 

noncomputable def Ns60p1439 := nat_lit 1875901934285741259648400 

noncomputable abbrev qz461 := qz774

noncomputable def Ns60p1440 := @Enclosure.Real.IsNear.subLit_ff_p qz461 qz1006 1178883639288011950733 1801439850948198400 17218064545395248809 Ns60p192 267489 2000 0 1 Ns60p1439 4689754835714353149121 9007199254740992000 17218064545395248809 Ns60p192 

noncomputable def Ns60p1441 := nat_lit 2654609959305332419857166226144886784 

noncomputable def Ns60p1442 := nat_lit 11837639638799498944184320 

noncomputable def Ns60p1443 := nat_lit 1356161581100043079507718981778275084499528503040 

noncomputable def Ns60p1444 := nat_lit 871198410287467004076703815799925269337868288 

noncomputable def Ns60p1445 := nat_lit 1005061384315206481353069104027919681700608 

noncomputable def Ns60p1446 := BSN.log_dyadic_bound 24058460484 548346460484 3 2 Ns60p1443 33554432 8737864 Ns60p1444 Ns60p1445 2946263 572404920968 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 24058460484) (BSN.artanhQ 548346460484) 0 2 Ns60p1444 Ns60p1443 Ns60p1445 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz775 := qz1004

noncomputable def Ns60p1447 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 267489 4000) qz775 267489 4000 0 1 22049322051553985 2251799813685248 62500007645631 546116500000000000000 1179590221249624778733 1801439850948198400 16718064545122190559 Ns60p192 (Enclosure.Real.IsNear.const Bool.false 267489 4000) (BSN.isNear_log_sfrac 286202460484 16000000 22049322051553985 2251799813685248 62500007645631 546116500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 286202460484) qz650)) Bool.false Ns60p1442 Ns60p84 1000000122330096 8737864000000000000000 22049322051553985 2251799813685248 62500007645631 546116500000000000000 (BSN.log_rat_reduce_isNear 286202460484 16000000 14 572404920968 524288000000 2946263 33554432 24973259072661432 36028797018963968 8737864 1000000000000000 rfl rfl rfl rfl (Ns60p1446 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p1448 := BSN.arctan_dyadic_bound_f 1000 534978 1 0 4194304 1092233 0 1 1 0 1 1 7840 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 534978) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 534978) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz1007 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 534978)))

noncomputable abbrev qz776 := qz1007

noncomputable abbrev qz462 := qz776

noncomputable def Ns60p1449 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz462 884279719003555 562949953421312 1 2000000000000000 7840 4194304 1 1092233 3704524434900663664640 883227452016035 562949953421312 2000000001092233 2184466000000000000000 qz15 (Ns60p1448 rfl) rfl rfl 

noncomputable abbrev qz777 := (@HMul.hMul Real Real Real qz5 qz12 qz1005)

noncomputable abbrev qz463 := qz777

noncomputable abbrev qz778 := qz1005

noncomputable abbrev qz464 := qz778

noncomputable abbrev qz779 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 267489 4000) qz1004)

noncomputable def Ns60p1450 := @Enclosure.Real.IsNear.subLit_ff_p qz779 qz463 1179590221249624778733 1801439850948198400 16718064545122190559 Ns60p192 883227452016035 2251799813685248 2000000001092233 8737864000000000000000 Ns60p1441 1178883639288011950733 1801439850948198400 17218064545395248809 Ns60p192 (Ns60p1447 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz12 qz464 1 4 0 1 883227452016035 562949953421312 2000000001092233 2184466000000000000000 883227452016035 2251799813685248 2000000001092233 8737864000000000000000 qz335 Ns60p1449 rfl) 

noncomputable def Ns60p1451 := @Ns60p1436 Ns60p1430 Ns60p1431 17731674222321713093333 Ns60p186 (@Ns60p1438 17731674222321713093333 Ns60p186 (Ns60p1440 (Ns60p1450 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 267489 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz1006 (Real.log Real.pi) 267489 2000 0 1 38410761 33554432 1 16777216 10274456049129 67108864000 267489 33554432000 (Enclosure.Real.IsNear.const Bool.false 267489 2000) RS061to078.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns60p1432 Ns60p1433) 

noncomputable def Ns60p1452 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz137) Bool.false Ns60p1430 Ns60p1431 17731674222321713093333 Ns60p186 3083362315 8388608 67 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz137) (@HAdd.hAdd Real Real Real qz336 qz459 (Enclosure.sfrac Bool.true Ns60p1432 Ns60p1433)) Bool.false Ns60p1430 Ns60p1431 17731674222321713093333 Ns60p186 Ns60p1434 (Ns60p1451 rfl rfl)) 

noncomputable def Ns60p1453 := nat_lit 1897876753597929682370560 

noncomputable def Ns60p1454 := nat_lit 139664318161654360900771582668250101956281923210721545431347962478992127631975686144000 

noncomputable def Ns60p1455 := nat_lit 279966228013030900773331098454613685655329701514863816605319359698103195879719632896 

noncomputable def Ns60p1456 := nat_lit 365334221292311752329340180447918987727772598416103791855217003719753881480892965257216 

noncomputable def Ns60p1457 := BSN.sin_dyadic_bound_f 26970450812 17179869184 3 2 8388608 2186600 Ns60p1454 Ns60p94 Ns60p1455 Ns60p1456 Ns60p97 Ns60p1455 8388604 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26970450812) qz655 0 2 Ns60p1454 Ns60p94 Ns60p1455 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26970450812) qz656 0 2 Ns60p1456 Ns60p97 Ns60p1455 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1458 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz137) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3083362315) qz337) Bool.false 3083362315 8388608 67 4194304 Bool.true 8388604 8388608 1 1092233 (Ns60p1452 rfl) (Enclosure.sfrac_false_div 3083362315 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3083362315) qz337) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns60p1453) qz657) 226375608064910080 72057594037927936 Bool.false 8388604 8388608 58 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q1 3083362315 8388608 226375608064910080 72057594037927936 58 Ns60p1453 Ns60p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388604 8388608 Ns60p1453 Ns60p84 26970450812 17179869184 2186600 2184466 (Ns60p1457 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p1459 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz137) Bool.false Ns60p1430 Ns60p1431 17731674222321713093333 Ns60p186 24666898520 67108864 1065 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz137) (@HAdd.hAdd Real Real Real qz336 qz459 (Enclosure.sfrac Bool.true Ns60p1432 Ns60p1433)) Bool.false Ns60p1430 Ns60p1431 17731674222321713093333 Ns60p186 Ns60p1434 (Ns60p1451 rfl rfl)) 

noncomputable def Ns60p1460 := Ns60p1429 23833 BSN.abs_quadSignPos (BSN.cos_quad_nat3 115 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 67003191 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 46 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 8609119 67108864) (@Eq.refl Real qz137) rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz137) qz137 1) Bool.true 2097151 2097152 77373915 4581157240832 67108832 67108864 1134 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz137) qz137 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz137)) Bool.true 2097151 2097152 77373915 4581157240832 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz137) qz137) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz137)) Bool.true 8388604 8388608 77373915 4581157240832 2097151 2097152 77373915 4581157240832 (Ns60p1458 rfl rfl) rfl)) rfl) (Ns60p1459 rfl) RS061to078.d7 

noncomputable def Ns60p1461 := nat_lit 2282894643287207921173337159019725223095502002025299012867682393604985046158103138569562898355722387456 

noncomputable def Ns60p1462 := nat_lit 1216680708864654371707267622406761208307218996857898339412852857199313179014458692048438486368256 

noncomputable def Ns60p1463 := nat_lit 11402207869544302552194253826438029610788694639316056130453792192809945203982058170931250129675082530816 

noncomputable def Ns60p1464 := BSN.sin_dyadic_bound_f 101647816 67108864 4 3 67108864 33554432 Ns60p1461 Ns60p109 Ns60p1462 Ns60p1463 Ns60p112 Ns60p1462 67003191 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 101647816) qz339 0 3 Ns60p1461 Ns60p109 Ns60p1462 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 101647816) (BSN.sinOddQ 67108864) 0 3 Ns60p1463 Ns60p112 Ns60p1462 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1465 := nat_lit 722188294773813498211623463679382392998078694245397674458799110784338335010668137356096747344655589921 

noncomputable def Ns60p1466 := nat_lit 675313345964236633056013755829944705430524268795133053481046333407929819137652030349382121988641 

noncomputable def Ns60p1467 := nat_lit 4373771015974202187869040510551020018875270128752160143649028665922889068785098502063490425151037153825 

noncomputable def Ns60p1468 := BSN.cos_dyadic_bound_f 96781447 67108864 4 3 67108864 33554432 Ns60p1465 Ns60p219 Ns60p1466 Ns60p1467 Ns60p222 Ns60p1466 8609119 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 96781447) qz338 0 3 Ns60p1465 Ns60p219 Ns60p1466 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 96781447) (BSN.cosOddQ 67108864) 0 3 Ns60p1467 Ns60p222 Ns60p1466 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1469 := nat_lit 3124303053504360242832643041 

noncomputable def Ns60p1470 := BSN.cos_dyadic_bound_f 7476327 67108864 2 1 67108864 33554432 Ns60p1469 Ns60p630 Ns60p1469 Ns60p1469 Ns60p631 Ns60p1469 66692840 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 7476327) qz338 0 1 Ns60p1469 Ns60p630 Ns60p1469 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 7476327) (BSN.cosOddQ 67108864) 0 1 Ns60p1469 Ns60p631 Ns60p1469 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1471 := nat_lit 2926370371781976735045281296 

noncomputable def Ns60p1472 := BSN.cos_dyadic_bound_f 7354994 67108864 2 1 67108864 33554432 Ns60p1471 Ns60p630 Ns60p1471 Ns60p1471 Ns60p631 Ns60p1471 66706221 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 7354994) qz338 0 1 Ns60p1471 Ns60p630 Ns60p1471 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 7354994) (BSN.cosOddQ 67108864) 0 1 Ns60p1471 Ns60p631 Ns60p1471 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1473 := Ns60p1427 40571 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 2 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66692840 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 40 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66706221 67108864) (@Eq.refl Real qz137) rfl rfl (Ns60p1460 RS061to078.d9 RS061to078.d11 RS061to078.d13 RS061to078.d17 (Ns60p1464 rfl rfl) (Ns60p1468 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns60p1459 rfl) RS061to078.d19 RS061to078.d21 RS061to078.d23 RS061to078.d25 RS061to078.d17 (Ns60p1470 rfl rfl) (Ns60p1472 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns60p1474 := nat_lit 23206113375962281708873113856 

noncomputable def Ns60p1475 := BSN.sin_dyadic_bound_f 12342428 67108864 2 1 67108864 33554432 Ns60p1474 Ns60p115 Ns60p1474 Ns60p1474 Ns60p116 Ns60p1474 12272964 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 12342428) qz339 0 1 Ns60p1474 Ns60p115 Ns60p1474 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 12342428) (BSN.sinOddQ 67108864) 0 1 Ns60p1474 Ns60p116 Ns60p1474 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1476 := Ns60p1425 Bool.true 28215384 40571 Bool.true 12342428 3537118876014220 1 Bool.false 12272964 Bool.false Bool.true 23204968 47896 BSN.abs_quadSignPos qz927 (BSN.sfrac_eq_quadSignPos_mul Bool.false 12272964 67108864) (@Eq.refl Real qz137) rfl (Ns60p1473 rfl rfl) (Ns60p1459 rfl) RS061to078.d27 RS061to078.d29 RS061to078.d17 (Ns60p1475 rfl rfl) rfl 

noncomputable def Ns60p1477 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz137) qz137 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz137) qz137 6) 23204968 67108864 47896 67108864 23204968 67108864 47896 67108864 3114518083272704 2900621 4194304 5987 4194304 (Ns60p1476 rfl rfl rfl rfl) 

noncomputable def Ns60p1478 := @Enclosure.Real.IsNear.mulLit_ff qz1003 (Zeta.RiemannSiegel.correction qz139) 410505 1048576 1 4194304 6751082411953 17592186044416 1544122290963041 38429532279701241856 2771353085518766265 18446744073709551616 

noncomputable abbrev qz1008 := (@HPow.hPow Real Real Real qz326 qz138 qz8)

noncomputable def Ns60p1479 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz1008 1 1 0 1 410505 1048576 1 4194304 410505 1048576 1 4194304 

noncomputable def Ns60p1480 := @Enclosure.Real.IsNear.sqrt_image qz138 357121621521 8388608000 267489 8388608000 27366727 27366748 4194304 (@Enclosure.Real.IsNear.of_eq qz138 (@HMul.hMul Real Real Real qz5 qz137 qz3) Bool.false 357121621521 8388608000 267489 8388608000 (BSN.t_div_two_pi_mk qz137 267489 1000 (@Eq.refl Real qz137)) (@Enclosure.Real.IsNear.mulLit_ff qz137 qz3 267489 1000 0 1 1335089 8388608 1 8388608 357121621521 8388608000 267489 8388608000 (Enclosure.Real.IsNear.const Bool.false 267489 1000) RS061to078.d32 rfl)) 

noncomputable abbrev qz780 := (Real.sqrt qz1002)

noncomputable abbrev qz465 := qz780

noncomputable abbrev qz140 := qz465

noncomputable def Ns60p1481 := @Enclosure.Real.IsNear.sqrt_image qz140 54733475 8388608 21 8388608 10713746 10713752 4194304 (@Enclosure.Real.IsNear.recentre' qz140 Bool.false 54733475 8388608 21 8388608 54733475 8388608 21 8388608 (Ns60p1480 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns60p1482 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz140) 10713749 4194304 3 4194304 1642019 1642021 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz140) Bool.false 21427498 8388608 6 8388608 10713749 4194304 3 4194304 (Ns60p1481 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns60p1483 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz140)) Bool.false 3284040 8388608 2 8388608 410505 1048576 1 4194304 (Ns60p1482 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz141 := (Real.cos (@HMul.hMul Real Real Real qz323 qz320 qz458))

noncomputable abbrev qz466 := (@HSub.hSub Real Real Real qz647 (@HMul.hMul Real Real Real qz644 qz773 qz773) qz773)

noncomputable abbrev qz142 := (@HMul.hMul Real Real Real qz323 qz320 (@HSub.hSub Real Real Real qz327 qz466 qz344))

noncomputable def Ns60p1484 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz139) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz141) (Real.cos qz142)) Bool.false 6751082411953 

noncomputable def Ns60p1485 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz141) (Real.cos qz142) 8490977 8388608 145 

noncomputable abbrev qz1009 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz141))

noncomputable def Ns60p1486 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz141) (@Neg.neg Real Real.instNeg qz1009) Bool.true 8490977 8388608 145 8388608 (BSN.inv_eq_neg_inv_neg qz141) 

noncomputable def Ns60p1487 := @Enclosure.Real.IsNear.recentre' qz1009 Bool.false 8490977 8388608 145 8388608 8490977 8388608 

noncomputable def Ns60p1488 := @Enclosure.Real.IsNear.recentre' qz141 Bool.true 8287473 8388608 153655597 9162314481664 8287473 8388608 153655597 9162314481664 

noncomputable abbrev qz143 := (@HMul.hMul Real Real Real qz323 qz320 qz458)

noncomputable def Ns60p1489 := @Enclosure.Real.IsNear.cos_image qz143 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13828747) qz660) Bool.false 13828747 4194304 133 8388608 Bool.true 8287473 8388608 1 

noncomputable def Ns60p1490 := nat_lit 566707583627736360573847891 

noncomputable def Ns60p1491 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz139 884279719003555 140737488355328 1 500000000000000 4401827 8388608 21 8388608 3892446342662261494985 1180591620717411303424 Ns60p1490 

noncomputable def Ns60p1492 := @Enclosure.Real.IsNear.subLit_ff_p qz140 qz1 54733475 8388608 21 8388608 6 1 0 1 4401827 4401827 8388608 21 

noncomputable def Ns60p1493 := @Ns60p1492 8388608 (@Enclosure.Real.IsNear.recentre' qz140 Bool.false 54733475 8388608 21 8388608 54733475 8388608 21 8388608 (Ns60p1480 rfl rfl rfl rfl rfl rfl) rfl) qz345 

noncomputable def Ns60p1494 := @Enclosure.Real.IsNear.recentre' qz143 Bool.false 3892446342662261494985 1180591620717411303424 Ns60p1490 Ns60p144 13828747 4194304 133 8388608 (@Ns60p1491 Ns60p144 RS061to078.d31 (Ns60p1493 rfl rfl) rfl) 

noncomputable def Ns60p1495 := nat_lit 50851440052729324282758317664168795601 

noncomputable def Ns60p1496 := nat_lit 2090694862362245919518973588060783891185664 

noncomputable def Ns60p1497 := nat_lit 31360422935433688792784603820911758367784960 

noncomputable def Ns60p1498 := BSN.cos_dyadic_bound_f 2670396893 17179869184 2 1 8388608 2186600 Ns60p1495 Ns60p1496 Ns60p1495 Ns60p1495 Ns60p1497 Ns60p1495 8287473 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 2670396893) qz769 0 1 Ns60p1495 Ns60p1496 Ns60p1495 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 2670396893) qz770 0 1 Ns60p1495 Ns60p1497 Ns60p1495 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1499 := @Ns60p1489 1092233 (Ns60p1494 rfl) (Enclosure.sfrac_false_div 13828747 4194304) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13828747) qz660) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 93956237940258445983744) qz709) 226375608064910080 72057594037927936 Bool.false 8287473 8388608 0 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q2 13828747 4194304 226375608064910080 72057594037927936 0 93956237940258445983744 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 8287473 8388608 93956237940258445983744 604462909807314587353088 2670396893 17179869184 2186600 2184466 (Ns60p1498 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p1500 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz141) 8287473 8388608 153655597 9162314481664 4245416 4245561 4194304 (@Enclosure.Real.IsNear.neg qz141 Bool.true 8287473 8388608 153655597 9162314481664 (Ns60p1488 (Ns60p1499 rfl rfl) rfl)) 

noncomputable def Ns60p1501 := Ns60p1486 (@Enclosure.Real.IsNear.neg qz1009 Bool.false 8490977 8388608 145 8388608 (@Ns60p1487 145 8388608 (Ns60p1500 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p1502 := @Enclosure.Real.IsNear.recentre' (Real.cos qz142) Bool.true 1590178 4194304 

noncomputable def Ns60p1503 := @Enclosure.Real.IsNear.cos_image qz142 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 1027421)) (@Nat.cast Real Real.instNatCast 524288)) Bool.true 1027421 524288 

noncomputable def Ns60p1504 := nat_lit 19407434455449004100360768005 

noncomputable def Ns60p1505 := nat_lit 9742997155512670494480741815623553 

noncomputable def Ns60p1506 := @Enclosure.Real.IsNear.recentre' qz142 Bool.true Ns60p1504 Ns60p159 Ns60p1505 

noncomputable abbrev qz144 := (@HSub.hSub Real Real Real qz327 qz466 qz344)

noncomputable def Ns60p1507 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz144 884279719003555 140737488355328 1 500000000000000 21947166759991 

noncomputable abbrev qz145 := qz466

noncomputable def Ns60p1508 := @Enclosure.Real.IsNear.subLit_tf qz145 qz23 17549120248887 70368744177664 361037943 70368744177664 1 16 

noncomputable abbrev qz467 := (@HMul.hMul Real Real Real qz644 qz773 qz773)

noncomputable abbrev qz146 := qz467

noncomputable def Ns60p1509 := @Enclosure.Real.IsNear.subLit_ff_n qz146 qz139 19376080937929 70368744177664 184877175 70368744177664 4401827 8388608 21 8388608 

noncomputable def Ns60p1510 := @Enclosure.Real.IsNear.mulLit_ff qz139 qz139 4401827 8388608 21 8388608 4401827 8388608 21 8388608 19376080937929 70368744177664 

noncomputable def Ns60p1511 := nat_lit 128079372199695442246127095507598651796233065536015610705155424061505081886321 

noncomputable def Ns60p1512 := nat_lit 206621721431677182442706747102504677185300319965248164533833585202413803929600 

noncomputable def Ns60p1513 := nat_lit 1383506675689615729196516840468724319325815886259462101495001420987811441 

noncomputable def Ns60p1514 := nat_lit 772500278124457912065115851468359631394026425184742376428363988832628586235505 

noncomputable def Ns60p1515 := nat_lit 18802576650282623602286313986327925623862329116837582972578856253419656157593600 

noncomputable def Ns60p1516 := BSN.cos_dyadic_bound_t 1027421 524288 4 3 4194304 1092233 Ns60p1511 Ns60p1512 Ns60p1513 Ns60p1514 Ns60p1515 Ns60p1513 1590178 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 1027421) (BSN.cosEvenQ 524288) 0 3 Ns60p1511 Ns60p1512 Ns60p1513 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 1027421) (BSN.cosOddQ 524288) 0 3 Ns60p1514 Ns60p1515 Ns60p1513 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1517 := @Ns60p1502 304383751 9162314481664 795089 2097152 304383751 9162314481664 (@Ns60p1503 271 8388608 Bool.true 1590178 4194304 1 1092233 (@Ns60p1506 Ns60p162 1027421 524288 271 8388608 (@Ns60p1507 70368744177664 361037943 70368744177664 Ns60p1504 Ns60p159 Ns60p1505 Ns60p162 RS061to078.d31 (@Ns60p1508 0 1 351154668159856 21947166759991 70368744177664 361037943 70368744177664 (@Ns60p1509 147212690512775479296 17549120248887 70368744177664 361037943 70368744177664 (@Ns60p1510 184877175 70368744177664 (Ns60p1493 rfl rfl) (Ns60p1493 rfl rfl) rfl) (Ns60p1493 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 1027421 524288) (BSN.cos_neg_of_bound 1027421 524288 Bool.true 1590178 4194304 1 1092233 (Ns60p1516 rfl rfl)) rfl rfl) 

noncomputable def Ns60p1518 := @Ns60p1478 2550228738321532867959 Ns60p62 (Ns60p1479 qz25 (@Enclosure.Real.IsNear.of_eq qz1008 (@Inv.inv Real Real.instInv (Real.sqrt qz140)) Bool.false 410505 1048576 1 4194304 (BSN.rpow_neg_quarter_mk qz138 (BSN.t_div_two_pi_nonneg qz137 267489 1000 (@Eq.refl Real qz137))) Ns60p1483) rfl) (@Ns60p1484 17592186044416 1544122290963041 38429532279701241856 (BSN.correction_mk qz139 (BSN.cos_two_pi_p_ne_zero_mk qz137 267489 1000 6 (@Eq.refl Real qz137) rfl rfl (@BSN.floor_sqrt_eq_dec qz137 267489 1000 6 (@Eq.refl Real qz137) rfl rfl rfl))) (@Ns60p1485 8388608 795089 2097152 304383751 9162314481664 6751082411953 17592186044416 1544122290963041 38429532279701241856 Ns60p1501 (Ns60p1517 rfl) rfl)) 

noncomputable def Ns60p1519 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz137) (hardyZApproximantRS₀ qz137) Bool.true 15528419154603761849 18446744073709551616 232627838496892867859831 Ns60p62 (@Eq.refl Real (hardyZApproximantRS₀ qz137)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz137) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz137) qz137 6) (@HMul.hMul Real Real Real qz5 qz1003 (Zeta.RiemannSiegel.correction qz139))) Bool.true 15528419154603761849 18446744073709551616 232627838496892867859831 Ns60p62 (BSN.hardyZApproximantRS₀_eq qz137 6 (@BSN.floor_sqrt_eq_dec qz137 267489 1000 6 (@Eq.refl Real qz137) rfl rfl rfl)) (@Ns60p1424 15528419154603761849 18446744073709551616 232627838496892867859831 Ns60p62 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz137) qz137 6) (@HAdd.hAdd Real Real Real qz336 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz137) qz137 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz137) qz137 6)) Bool.true 2900621 4194304 5987 4194304 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz137) qz137 6) (Ns60p1477 (Ns60p1476 rfl rfl rfl rfl) rfl rfl)) (Ns60p1518 rfl) rfl rfl)) 

theorem RS061to078.d54 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz137) Bool.true 15528419154603761849 18446744073709551616 232627838496892867859831 Ns60p62 := Ns60p1519 

noncomputable def Ns60p1520 := nat_lit 9481478879934119854211072 

noncomputable def Ns60p1521 := nat_lit 6292421238128656699084505088 

noncomputable abbrev qz781 := (Enclosure.sfrac Bool.false 269163 1000)

noncomputable abbrev qz468 := qz781

noncomputable abbrev qz147 := qz468

noncomputable abbrev qz1010 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 269163 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz782 := qz1010

noncomputable abbrev qz469 := qz782

noncomputable abbrev qz148 := qz469

noncomputable abbrev qz783 := (@HSub.hSub Real Real Real qz920 (Real.sqrt qz1010) qz914)

noncomputable abbrev qz470 := qz783

noncomputable abbrev qz149 := qz470

noncomputable abbrev qz1011 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz326 qz148 qz8))

noncomputable def Ns60p1522 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz147) qz147 6) (@HMul.hMul Real Real Real qz5 qz1011 (Zeta.RiemannSiegel.correction qz149)) 45172095 16777216 48197 33554432 22280416952234640417 147573952589676412928 164237598956209509287 Ns60p1520 Ns60p1521 

noncomputable def Ns60p1523 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz147) qz147 Real.sin BSN.quadSignPos 5 6 269163 1000 71 67108864 33554432 1125899906842624 Bool.false 24877779362 1072 120242927 63 27397080 8 

noncomputable def Ns60p1524 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz147) qz147 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 269163 1000 1 39 67108864 33554432 1125899906842624 Bool.false 24877779362 1072 

noncomputable def Ns60p1525 := Ns60p1524 93032624 62 33554424 8 108007536 62 30011992 8 Bool.false 86354015 23983 Bool.true 57746454 Bool.true 82693124 3537118876014220 1 Bool.false 50879367 Bool.true Bool.false 63299071 Bool.false Bool.false 89222538 

noncomputable def Ns60p1526 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz147) qz147 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 269163 1000 117 47 67108864 33554432 1125899906842624 Bool.false 24877779362 1072 

noncomputable def Ns60p1527 := Ns60p1526 46516304 62 47453136 16 73726608 62 38745320 8 Bool.false 67108856 1142 Bool.false 23831651 Bool.false 78829590 3537118876014220 1 Bool.false 23333899 Bool.true Bool.false 61911670 Bool.false Bool.false 86354015 

noncomputable def Ns60p1528 := nat_lit 50789991819501154458705072663011991876821581418974283 

noncomputable def Ns60p1529 := nat_lit 137008155105068055834207856918807318230836833157120 

noncomputable def Ns60p1530 := nat_lit 678143861114977692444125780640000 

noncomputable def Ns60p1531 := nat_lit 1095189180185240920291419108662425920 

noncomputable def Ns60p1532 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz147 269163 1000 289795882276 16000000 538326 4000 2000 Ns60p1530 Ns60p1531 (@Eq.refl Real qz147) rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns60p1533 := nat_lit 146275176440163324841070609269474536605246154486645935040 

noncomputable abbrev qz1012 := (Real.log (Enclosure.sfrac Bool.false 289795882276 16000000))

noncomputable abbrev qz1013 := (@HSub.hSub Real Real Real qz11 qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 538326))))

noncomputable abbrev qz784 := (@HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 269163 4000) qz1012) (@HMul.hMul Real Real Real qz5 qz12 qz1013))

noncomputable abbrev qz1014 := (Enclosure.sfrac Bool.false 269163 2000)

noncomputable abbrev qz471 := (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 qz784 qz1014) (@HMul.hMul Real Real Real qz5 qz1014 (Real.log Real.pi)))

noncomputable def Ns60p1534 := @Enclosure.Real.IsNear.addLit_ft_p qz471 (Enclosure.sfrac Bool.true Ns60p1530 Ns60p1531) 133561784040358611587 360287970189639680 17841040508965023707111 Ns60p186 Ns60p1530 Ns60p1531 0 1 Ns60p1533 

noncomputable def Ns60p1535 := nat_lit 224079490019044914405520179200000 

noncomputable abbrev qz472 := (@HSub.hSub Real Real Real qz11 qz784 qz1014)

noncomputable def Ns60p1536 := @Enclosure.Real.IsNear.subLit_ff_p qz472 (@HMul.hMul Real Real Real qz5 qz1014 (Real.log Real.pi)) 4726688896449730315979 9007199254740992000 17322689558194035103 Ns60p192 10338755663043 67108864000 269163 33554432000 Ns60p1535 133561784040358611587 360287970189639680 

noncomputable def Ns60p1537 := nat_lit 9453377792899460631958000 

noncomputable abbrev qz473 := qz784

noncomputable def Ns60p1538 := @Enclosure.Real.IsNear.subLit_ff_p qz473 qz1014 5938891282951655130827 9007199254740992000 17322689558194035103 Ns60p192 269163 2000 0 1 Ns60p1537 4726688896449730315979 9007199254740992000 17322689558194035103 Ns60p192 

noncomputable def Ns60p1539 := nat_lit 13373194284447480485496784910439940096 

noncomputable def Ns60p1540 := nat_lit 11852723851276225607630848 

noncomputable def Ns60p1541 := nat_lit 1392061317509237846953266101721006625075603664640 

noncomputable def Ns60p1542 := nat_lit 1166424141674928505017588917983623676119287808 

noncomputable def Ns60p1543 := nat_lit 1753961482029905754568556893068816464732928 

noncomputable def Ns60p1544 := BSN.log_dyadic_bound 27651882276 551939882276 3 2 Ns60p1541 33554432 8737864 Ns60p1542 Ns60p1543 3364934 579591764552 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 27651882276) (BSN.artanhQ 551939882276) 0 2 Ns60p1542 Ns60p1541 Ns60p1543 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz785 := qz1012

noncomputable def Ns60p1545 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 269163 4000) qz785 269163 4000 0 1 22077418586753729 2251799813685248 62500007645631 546116500000000000000 5942424219066393958827 9007199254740992000 16822689557920976853 Ns60p192 (Enclosure.Real.IsNear.const Bool.false 269163 4000) (BSN.isNear_log_sfrac 289795882276 16000000 22077418586753729 2251799813685248 62500007645631 546116500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 289795882276) qz650)) Bool.false Ns60p1540 Ns60p84 1000000122330096 8737864000000000000000 22077418586753729 2251799813685248 62500007645631 546116500000000000000 (BSN.log_rat_reduce_isNear 289795882276 16000000 14 579591764552 524288000000 3364934 33554432 24973259072661432 36028797018963968 8737864 1000000000000000 rfl rfl rfl rfl (Ns60p1544 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p1546 := BSN.arctan_dyadic_bound_f 1000 538326 1 0 4194304 1092233 0 1 1 0 1 1 7791 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 538326) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 538326) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz1015 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 538326)))

noncomputable abbrev qz786 := qz1015

noncomputable abbrev qz474 := qz786

noncomputable def Ns60p1547 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz474 884279719003555 562949953421312 1 2000000000000000 7791 4194304 1 1092233 3704552019448381308928 883234028684707 562949953421312 2000000001092233 2184466000000000000000 qz15 (Ns60p1546 rfl) rfl rfl 

noncomputable abbrev qz787 := (@HMul.hMul Real Real Real qz5 qz12 qz1013)

noncomputable abbrev qz475 := qz787

noncomputable abbrev qz788 := qz1013

noncomputable abbrev qz476 := qz788

noncomputable abbrev qz789 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 269163 4000) qz1012)

noncomputable def Ns60p1548 := @Enclosure.Real.IsNear.subLit_ff_p qz789 qz475 5942424219066393958827 9007199254740992000 16822689557920976853 Ns60p192 883234028684707 2251799813685248 2000000001092233 8737864000000000000000 Ns60p1539 5938891282951655130827 9007199254740992000 17322689558194035103 Ns60p192 (Ns60p1545 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz12 qz476 1 4 0 1 883234028684707 562949953421312 2000000001092233 2184466000000000000000 883234028684707 2251799813685248 2000000001092233 8737864000000000000000 qz335 Ns60p1547 rfl) 

noncomputable def Ns60p1549 := @Ns60p1534 Ns60p1528 Ns60p1529 17841040508965023707111 Ns60p186 (@Ns60p1536 17841040508965023707111 Ns60p186 (Ns60p1538 (Ns60p1548 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 269163 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz1014 (Real.log Real.pi) 269163 2000 0 1 38410761 33554432 1 16777216 10338755663043 67108864000 269163 33554432000 (Enclosure.Real.IsNear.const Bool.false 269163 2000) RS061to078.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns60p1530 Ns60p1531) 

noncomputable def Ns60p1550 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz147) Bool.false Ns60p1528 Ns60p1529 17841040508965023707111 Ns60p186 777430605 2097152 135 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz147) (@HAdd.hAdd Real Real Real qz336 qz471 (Enclosure.sfrac Bool.true Ns60p1530 Ns60p1531)) Bool.false Ns60p1528 Ns60p1529 17841040508965023707111 Ns60p186 Ns60p1532 (Ns60p1549 rfl rfl)) 

noncomputable def Ns60p1551 := nat_lit 139941486891900248625128141298965075039153708621485965975412037336884839203707031200000 

noncomputable def Ns60p1552 := nat_lit 281076304355517604053250772186461450998912409592728438980250284601620192964325744896 

noncomputable def Ns60p1553 := nat_lit 366058342128877432183058916437559020848547188202646445796301597326295765221099982889216 

noncomputable def Ns60p1554 := BSN.sin_dyadic_bound_f 26983795034 17179869184 3 2 8388608 2186600 Ns60p1551 Ns60p94 Ns60p1552 Ns60p1553 Ns60p97 Ns60p1552 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26983795034) qz655 0 2 Ns60p1551 Ns60p94 Ns60p1552 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26983795034) qz656 0 2 Ns60p1553 Ns60p97 Ns60p1552 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1555 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz147) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 777430605) qz766) Bool.false 777430605 2097152 135 8388608 Bool.false 8388607 8388608 1 1092233 (Ns60p1550 rfl) (Enclosure.sfrac_false_div 777430605 2097152) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 777430605) qz766) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474703942433975000104960) qz767) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 58 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q3 777430605 2097152 226375608064910080 72057594037927936 58 474703942433975000104960 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 474703942433975000104960 302231454903657293676544 26983795034 17179869184 2186600 2184466 (Ns60p1554 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p1556 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz147) Bool.false Ns60p1528 Ns60p1529 17841040508965023707111 Ns60p186 24877779362 67108864 1072 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz147) (@HAdd.hAdd Real Real Real qz336 qz471 (Enclosure.sfrac Bool.true Ns60p1530 Ns60p1531)) Bool.false Ns60p1528 Ns60p1529 17841040508965023707111 Ns60p186 Ns60p1532 (Ns60p1549 rfl rfl)) 

noncomputable def Ns60p1557 := Ns60p1527 23983 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 117 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 23333899 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 47 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 61911670 67108864) (@Eq.refl Real qz147) rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz147) qz147 1) Bool.false 8388607 8388608 155840063 9162314481664 67108856 67108864 1142 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz147) qz147 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz147)) Bool.false 8388607 8388608 155840063 9162314481664 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz147) qz147) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz147)) Bool.false 8388607 8388608 155840063 9162314481664 8388607 8388608 155840063 9162314481664 (Ns60p1555 rfl rfl) rfl)) rfl) (Ns60p1556 rfl) RS061to078.d7 

noncomputable def Ns60p1558 := nat_lit 322564464289142416716420411601 

noncomputable def Ns60p1559 := BSN.sin_dyadic_bound_f 23831651 67108864 2 1 67108864 33554432 Ns60p1558 Ns60p115 Ns60p1558 Ns60p1558 Ns60p116 Ns60p1558 23333899 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 23831651) qz339 0 1 Ns60p1558 Ns60p115 Ns60p1558 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 23831651) (BSN.sinOddQ 67108864) 0 1 Ns60p1558 Ns60p116 Ns60p1558 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1560 := nat_lit 2369909419090504197361222962886378064350402608272214231530862240000 

noncomputable def Ns60p1561 := nat_lit 1491125310766882926281658061942231755271593287026584512100000000 

noncomputable def Ns60p1562 := nat_lit 6204491418543412230255889837364036079028233775391089469561239200000 

noncomputable def Ns60p1563 := BSN.sin_dyadic_bound_f 78829590 67108864 3 2 67108864 33554432 Ns60p1560 Ns60p119 Ns60p1561 Ns60p1562 Ns60p122 Ns60p1561 61911670 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 78829590) qz339 0 2 Ns60p1560 Ns60p119 Ns60p1561 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 78829590) (BSN.sinOddQ 67108864) 0 2 Ns60p1562 Ns60p122 Ns60p1561 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1564 := nat_lit 682152304235730393182240272690875109283773501547515971748403831040 

noncomputable def Ns60p1565 := nat_lit 123652404948905692509603712119958232006223859387494695550279936 

noncomputable def Ns60p1566 := nat_lit 1786389169104614706260851831989812020510444332090200172691119104256 

noncomputable def Ns60p1567 := BSN.sin_dyadic_bound_f 57746454 67108864 3 2 67108864 33554432 Ns60p1564 Ns60p119 Ns60p1565 Ns60p1566 Ns60p122 Ns60p1565 50879367 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 57746454) qz339 0 2 Ns60p1564 Ns60p119 Ns60p1565 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 57746454) (BSN.sinOddQ 67108864) 0 2 Ns60p1566 Ns60p122 Ns60p1565 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1568 := nat_lit 2870185111285825223900685963321882470139581122984709218029193461760 

noncomputable def Ns60p1569 := nat_lit 2186528754093492019764494224899642403836293676729618342441189376 

noncomputable def Ns60p1570 := nat_lit 7513611387765771837422177865669378476949834656150009522283935236096 

noncomputable def Ns60p1571 := BSN.sin_dyadic_bound_f 82693124 67108864 3 2 67108864 33554432 Ns60p1568 Ns60p119 Ns60p1569 Ns60p1570 Ns60p122 Ns60p1569 63299071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 82693124) qz339 0 2 Ns60p1568 Ns60p119 Ns60p1569 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 82693124) (BSN.sinOddQ 67108864) 0 2 Ns60p1570 Ns60p122 Ns60p1569 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1572 := Ns60p1525 40826 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 1 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 50879367 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 39 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 63299071 67108864) (@Eq.refl Real qz147) rfl rfl (Ns60p1557 RS061to078.d9 RS061to078.d11 RS061to078.d13 RS061to078.d17 (Ns60p1559 rfl rfl) (Ns60p1563 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns60p1556 rfl) RS061to078.d19 RS061to078.d21 RS061to078.d23 RS061to078.d25 RS061to078.d17 (Ns60p1567 rfl rfl) (Ns60p1571 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns60p1573 := BSN.sin_dyadic_bound_f 2748246 67108864 1 0 67108864 33554432 0 1 1 0 1 1 2747477 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 2748246) qz339 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 2748246) (BSN.sinOddQ 67108864) 0 0 rfl) rfl rfl 

noncomputable def Ns60p1574 := Ns60p1523 Bool.false 89222538 40826 Bool.true 2748246 3537118876014220 1 Bool.false 2747477 Bool.false Bool.false 90344190 48197 BSN.abs_quadSignPos qz927 (BSN.sfrac_eq_quadSignPos_mul Bool.false 2747477 67108864) (@Eq.refl Real qz147) rfl (Ns60p1572 rfl rfl) (Ns60p1556 rfl) RS061to078.d27 RS061to078.d29 RS061to078.d17 (Ns60p1573 rfl rfl) rfl 

noncomputable def Ns60p1575 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz147) qz147 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz147) qz147 6) 90344190 67108864 48197 67108864 90344190 67108864 48197 67108864 12125791919800320 45172095 16777216 48197 33554432 (Ns60p1574 rfl rfl rfl rfl) 

noncomputable def Ns60p1576 := @Enclosure.Real.IsNear.mulLit_ff qz1011 (Zeta.RiemannSiegel.correction qz149) 1639461 4194304 1 4194304 13590086590797 35184372088832 99645157669307 2260560722335367168 22280416952234640417 147573952589676412928 

noncomputable abbrev qz1016 := (@HPow.hPow Real Real Real qz326 qz148 qz8)

noncomputable def Ns60p1577 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz1016 1 1 0 1 1639461 4194304 1 4194304 1639461 4194304 1 4194304 

noncomputable def Ns60p1578 := @Enclosure.Real.IsNear.sqrt_image qz148 359356560507 8388608000 269163 8388608000 27452226 27452248 4194304 (@Enclosure.Real.IsNear.of_eq qz148 (@HMul.hMul Real Real Real qz5 qz147 qz3) Bool.false 359356560507 8388608000 269163 8388608000 (BSN.t_div_two_pi_mk qz147 269163 1000 (@Eq.refl Real qz147)) (@Enclosure.Real.IsNear.mulLit_ff qz147 qz3 269163 1000 0 1 1335089 8388608 1 8388608 359356560507 8388608000 269163 8388608000 (Enclosure.Real.IsNear.const Bool.false 269163 1000) RS061to078.d32 rfl)) 

noncomputable abbrev qz790 := (Real.sqrt qz1010)

noncomputable abbrev qz477 := qz790

noncomputable abbrev qz150 := qz477

noncomputable def Ns60p1579 := @Enclosure.Real.IsNear.sqrt_image qz150 27452237 4194304 11 4194304 10730469 10730475 4194304 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 54904474 8388608 22 8388608 27452237 4194304 11 4194304 (Ns60p1578 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns60p1580 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz150) 1341309 524288 3 4194304 1639460 1639462 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz150) Bool.false 21460944 8388608 6 8388608 1341309 524288 3 4194304 (Ns60p1579 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns60p1581 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz150)) Bool.false 3278922 8388608 2 8388608 1639461 4194304 1 4194304 (Ns60p1580 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz151 := (Real.cos (@HMul.hMul Real Real Real qz323 qz320 qz470))

noncomputable abbrev qz478 := (@HSub.hSub Real Real Real qz647 (@HMul.hMul Real Real Real qz644 qz783 qz783) qz783)

noncomputable abbrev qz152 := (@HMul.hMul Real Real Real qz323 qz320 (@HSub.hSub Real Real Real qz327 qz478 qz344))

noncomputable def Ns60p1582 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz149) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz151) (Real.cos qz152)) Bool.false 13590086590797 

noncomputable def Ns60p1583 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz151) (Real.cos qz152) 8737431 8388608 161 

noncomputable abbrev qz1017 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz151))

noncomputable def Ns60p1584 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz151) (@Neg.neg Real Real.instNeg qz1017) Bool.true 8737431 8388608 161 8388608 (BSN.inv_eq_neg_inv_neg qz151) 

noncomputable def Ns60p1585 := @Enclosure.Real.IsNear.recentre' qz1017 Bool.false 8737431 8388608 161 8388608 8737431 8388608 

noncomputable def Ns60p1586 := @Enclosure.Real.IsNear.recentre' qz151 Bool.true 8053711 8388608 160208995 9162314481664 8053711 8388608 160208995 9162314481664 

noncomputable abbrev qz153 := (@HMul.hMul Real Real Real qz323 qz320 qz470)

noncomputable def Ns60p1587 := @Enclosure.Real.IsNear.cos_image qz153 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 28731913) qz337) Bool.false 28731913 8388608 139 8388608 Bool.true 8053711 8388608 1 

noncomputable def Ns60p1588 := nat_lit 296846829519124638127157133 

noncomputable def Ns60p1589 := nat_lit 18014398509481984000000000000000 

noncomputable def Ns60p1590 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz149 884279719003555 140737488355328 1 500000000000000 2286413 4194304 11 4194304 2021828645166075198215 590295810358705651712 Ns60p1588 

noncomputable def Ns60p1591 := @Enclosure.Real.IsNear.subLit_ff_p qz150 qz1 27452237 4194304 11 4194304 6 1 0 1 2286413 2286413 4194304 11 

noncomputable def Ns60p1592 := @Ns60p1591 4194304 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 54904474 8388608 22 8388608 27452237 4194304 11 4194304 (Ns60p1578 rfl rfl rfl rfl rfl rfl) rfl) qz345 

noncomputable def Ns60p1593 := @Enclosure.Real.IsNear.recentre' qz153 Bool.false 2021828645166075198215 590295810358705651712 Ns60p1588 Ns60p1589 28731913 8388608 139 8388608 (@Ns60p1590 Ns60p1589 RS061to078.d31 (Ns60p1592 rfl rfl) rfl) 

noncomputable def Ns60p1594 := nat_lit 562864278811141367617083086982753500625 

noncomputable def Ns60p1595 := BSN.cos_dyadic_bound_f 4870807005 17179869184 2 1 8388608 2186600 Ns60p1594 Ns60p1496 Ns60p1594 Ns60p1594 Ns60p1497 Ns60p1594 8053711 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 4870807005) qz769 0 1 Ns60p1594 Ns60p1496 Ns60p1594 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 4870807005) qz770 0 1 Ns60p1594 Ns60p1497 Ns60p1594 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1596 := @Ns60p1587 1092233 (Ns60p1593 rfl) (Enclosure.sfrac_false_div 28731913 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 28731913) qz337) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 342752572137789882105856) qz657) 226375608064910080 72057594037927936 Bool.false 8053711 8388608 0 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q2 28731913 8388608 226375608064910080 72057594037927936 0 342752572137789882105856 Ns60p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 8053711 8388608 342752572137789882105856 Ns60p84 4870807005 17179869184 2186600 2184466 (Ns60p1595 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p1597 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz151) 8053711 8388608 160208995 9162314481664 4368635 4368796 4194304 (@Enclosure.Real.IsNear.neg qz151 Bool.true 8053711 8388608 160208995 9162314481664 (Ns60p1586 (Ns60p1596 rfl rfl) rfl)) 

noncomputable def Ns60p1598 := Ns60p1584 (@Enclosure.Real.IsNear.neg qz1017 Bool.false 8737431 8388608 161 8388608 (@Ns60p1585 161 8388608 (Ns60p1597 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p1599 := @Enclosure.Real.IsNear.recentre' (Real.cos qz152) Bool.true 1555387 4194304 

noncomputable def Ns60p1600 := @Enclosure.Real.IsNear.cos_image qz152 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16363675)) qz337) Bool.true 16363675 8388608 

noncomputable def Ns60p1601 := nat_lit 4829704508905451014778358245 

noncomputable def Ns60p1602 := nat_lit 520499601934371202919768869181229 

noncomputable def Ns60p1603 := @Enclosure.Real.IsNear.recentre' qz152 Bool.true Ns60p1601 Ns60p327 Ns60p1602 

noncomputable def Ns60p1604 := nat_lit 15111572745182864683827200000000000000 

noncomputable abbrev qz154 := (@HSub.hSub Real Real Real qz327 qz478 qz344)

noncomputable def Ns60p1605 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz154 884279719003555 140737488355328 1 500000000000000 5461738412759 

noncomputable abbrev qz155 := qz478

noncomputable def Ns60p1606 := @Enclosure.Real.IsNear.subLit_tf qz155 qz23 4362226784983 17592186044416 96438551 17592186044416 1 16 

noncomputable abbrev qz479 := (@HMul.hMul Real Real Real qz644 qz783 qz783)

noncomputable abbrev qz156 := qz479

noncomputable def Ns60p1607 := @Enclosure.Real.IsNear.subLit_ff_n qz156 qz149 5227684406569 17592186044416 50301207 17592186044416 2286413 4194304 11 4194304 

noncomputable def Ns60p1608 := @Enclosure.Real.IsNear.mulLit_ff qz149 qz149 2286413 4194304 11 4194304 2286413 4194304 11 4194304 5227684406569 17592186044416 

noncomputable def Ns60p1609 := nat_lit 35391580202384522131216809886962072214428270235563109445275646781293140151090297846494140625 

noncomputable def Ns60p1610 := nat_lit 368612572879437417348954652170073547275441866377490296453905461123004019260406494140625 

noncomputable def Ns60p1611 := nat_lit 213483896739565452476394348864149385030751008198011484076268618765967135164836887542494140625 

noncomputable def Ns60p1612 := BSN.cos_dyadic_bound_t 16363675 8388608 4 3 4194304 1092233 Ns60p1609 Ns60p274 Ns60p1610 Ns60p1611 Ns60p277 Ns60p1610 1555387 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16363675) (BSN.cosEvenQ 8388608) 0 3 Ns60p1609 Ns60p274 Ns60p1610 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16363675) (BSN.cosOddQ 8388608) 0 3 Ns60p1611 Ns60p277 Ns60p1610 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1613 := @Ns60p1599 162568089 4581157240832 1555387 4194304 162568089 4581157240832 (@Ns60p1600 145 4194304 Bool.true 1555387 4194304 1 1092233 (@Ns60p1603 Ns60p1604 16363675 8388608 145 4194304 (@Ns60p1605 17592186044416 96438551 17592186044416 Ns60p1601 Ns60p327 Ns60p1602 Ns60p1604 RS061to078.d31 (@Ns60p1606 0 1 87387814604144 5461738412759 17592186044416 96438551 17592186044416 (@Ns60p1607 18296505253161336832 4362226784983 17592186044416 96438551 17592186044416 (@Ns60p1608 50301207 17592186044416 (Ns60p1592 rfl rfl) (Ns60p1592 rfl rfl) rfl) (Ns60p1592 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16363675 8388608) (BSN.cos_neg_of_bound 16363675 8388608 Bool.true 1555387 4194304 1 1092233 (Ns60p1612 rfl rfl)) rfl rfl) 

noncomputable def Ns60p1614 := @Ns60p1576 164237598956209509287 Ns60p1520 (Ns60p1577 qz25 (@Enclosure.Real.IsNear.of_eq qz1016 (@Inv.inv Real Real.instInv (Real.sqrt qz150)) Bool.false 1639461 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz148 (BSN.t_div_two_pi_nonneg qz147 269163 1000 (@Eq.refl Real qz147))) Ns60p1581) rfl) (@Ns60p1582 35184372088832 99645157669307 2260560722335367168 (BSN.correction_mk qz149 (BSN.cos_two_pi_p_ne_zero_mk qz147 269163 1000 6 (@Eq.refl Real qz147) rfl rfl (@BSN.floor_sqrt_eq_dec qz147 269163 1000 6 (@Eq.refl Real qz147) rfl rfl rfl))) (@Ns60p1583 8388608 1555387 4194304 162568089 4581157240832 13590086590797 35184372088832 99645157669307 2260560722335367168 Ns60p1598 (Ns60p1613 rfl) rfl)) 

noncomputable def Ns60p1615 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz147) (hardyZApproximantRS₀ qz147) Bool.false 375057532675782245343 147573952589676412928 13783268240755920933799 Ns60p1520 (@Eq.refl Real (hardyZApproximantRS₀ qz147)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz147) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz147) qz147 6) (@HMul.hMul Real Real Real qz5 qz1011 (Zeta.RiemannSiegel.correction qz149))) Bool.false 375057532675782245343 147573952589676412928 13783268240755920933799 Ns60p1520 (BSN.hardyZApproximantRS₀_eq qz147 6 (@BSN.floor_sqrt_eq_dec qz147 269163 1000 6 (@Eq.refl Real qz147) rfl rfl rfl)) (@Ns60p1522 375057532675782245343 147573952589676412928 13783268240755920933799 Ns60p1520 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz147) qz147 6) (@HAdd.hAdd Real Real Real qz336 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz147) qz147 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz147) qz147 6)) Bool.false 45172095 16777216 48197 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz147) qz147 6) (Ns60p1575 (Ns60p1574 rfl rfl rfl rfl) rfl rfl)) (Ns60p1614 rfl) rfl rfl)) 

theorem RS061to078.d55 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz147) Bool.false 375057532675782245343 147573952589676412928 13783268240755920933799 Ns60p1520 := Ns60p1615 

noncomputable def Ns60p1616 := nat_lit 604803999525962590961270784 

noncomputable abbrev qz791 := (Enclosure.sfrac Bool.false 270834 1000)

noncomputable abbrev qz480 := qz791

noncomputable abbrev qz157 := qz480

noncomputable abbrev qz1018 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 270834 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz792 := qz1018

noncomputable abbrev qz481 := qz792

noncomputable abbrev qz158 := qz481

noncomputable abbrev qz793 := (@HSub.hSub Real Real Real qz920 (Real.sqrt qz1018) qz914)

noncomputable abbrev qz482 := qz793

noncomputable abbrev qz159 := qz482

noncomputable abbrev qz1019 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz326 qz158 qz8))

noncomputable def Ns60p1617 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz157) qz157 6) (@HMul.hMul Real Real Real qz5 qz1019 (Zeta.RiemannSiegel.correction qz159)) 15115773 8388608 3031 2097152 5618382395670996981 36893488147419103232 742158486256751856655 Ns60p1233 Ns60p1616 

noncomputable def Ns60p1618 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz157) qz157 Real.cos BSN.quadSignNeg 5 6 270834 1000 70 67108864 33554432 1125899906842624 Bool.false 25088630566 1078 120242927 63 27397080 8 

noncomputable def Ns60p1619 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz157) qz157 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 270834 1000 1 39 67108864 33554432 1125899906842624 Bool.false 25088630566 1078 

noncomputable def Ns60p1620 := Ns60p1619 93032624 62 33554424 8 108007536 62 30011992 8 Bool.true 77462216 24132 Bool.true 2352765 Bool.true 52322513 3537118876014220 1 Bool.false 2352283 Bool.true Bool.false 47180355 Bool.false Bool.true 57538665 

noncomputable def Ns60p1621 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz157) qz157 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 270834 1000 118 48 67108864 33554432 1125899906842624 Bool.false 25088630566 1078 

noncomputable def Ns60p1622 := Ns60p1621 46516304 62 47453136 16 73726608 62 38745320 8 Bool.true 67108856 1150 Bool.false 51539754 Bool.false 61069275 3537118876014220 1 Bool.false 48271405 Bool.true Bool.false 41187615 Bool.false Bool.true 77462216 

noncomputable def Ns60p1623 := nat_lit 10382463526928354878849116651106930835471114196823957 

noncomputable def Ns60p1624 := nat_lit 27771756252858215525034971670637825413584257024000 

noncomputable def Ns60p1625 := nat_lit 32895488000000000000000000 

noncomputable def Ns60p1626 := nat_lit 699456816620972424321206123520000 

noncomputable def Ns60p1627 := nat_lit 1136621932690668198689830865240494080 

noncomputable abbrev qz160 := (@Eq.refl Real qz480)

noncomputable def Ns60p1628 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz157 270834 1000 293405222224 16000000 541668 4000 2000 Ns60p1626 Ns60p1627 qz160 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns60p1629 := nat_lit 1913695677283434371269469181132029491594035768758591754240 

noncomputable abbrev qz1020 := (Real.log (Enclosure.sfrac Bool.false 293405222224 16000000))

noncomputable abbrev qz1021 := (@HSub.hSub Real Real Real qz11 qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 541668))))

noncomputable abbrev qz794 := (@HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 270834 4000) qz1020) (@HMul.hMul Real Real Real qz5 qz12 qz1021))

noncomputable abbrev qz1022 := (Enclosure.sfrac Bool.false 270834 2000)

noncomputable abbrev qz483 := (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 qz794 qz1022) (@HMul.hMul Real Real Real qz5 qz1022 (Real.log Real.pi)))

noncomputable def Ns60p1630 := @Enclosure.Real.IsNear.addLit_ft_p qz483 (Enclosure.sfrac Bool.true Ns60p1626 Ns60p1627) 1683672268074829102153 4503599627370496000 527947376431731353597 Ns60p1625 Ns60p1626 Ns60p1627 0 1 Ns60p1629 

noncomputable def Ns60p1631 := nat_lit 56494666629402624019813892096000 

noncomputable abbrev qz484 := (@HSub.hSub Real Real Real qz11 qz794 qz1022)

noncomputable def Ns60p1632 := @Enclosure.Real.IsNear.subLit_ff_p qz484 (@HMul.hMul Real Real Real qz5 qz1022 (Real.log Real.pi)) 2381801756733010492489 4503599627370496000 128140640227719739 16062250000000000000000 5201470022337 33554432000 135417 16777216000 Ns60p1631 1683672268074829102153 4503599627370496000 

noncomputable def Ns60p1633 := nat_lit 4763603513466020984978000 

noncomputable abbrev qz485 := qz794

noncomputable def Ns60p1634 := @Enclosure.Real.IsNear.subLit_ff_p qz485 qz1022 2991665707472640949321 4503599627370496000 128140640227719739 16062250000000000000000 270834 2000 0 1 Ns60p1633 2381801756733010492489 4503599627370496000 128140640227719739 16062250000000000000000 

noncomputable def Ns60p1635 := nat_lit 6736632282695438535011382542213316608 

noncomputable def Ns60p1636 := nat_lit 11867687727570908931424256 

noncomputable def Ns60p1637 := nat_lit 1428832877218440838028608660887364134392012144640 

noncomputable def Ns60p1638 := nat_lit 1510954229698060542611303177408775570609143808 

noncomputable def Ns60p1639 := nat_lit 2865134864680045004088946750650821058428928 

noncomputable def Ns60p1640 := BSN.log_dyadic_bound 31261222224 555549222224 3 2 Ns60p1637 33554432 8737864 Ns60p1638 Ns60p1639 3780265 586810444448 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 31261222224) (BSN.artanhQ 555549222224) 0 2 Ns60p1638 Ns60p1637 Ns60p1639 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz795 := qz1020

noncomputable def Ns60p1641 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 270834 4000) qz795 270834 4000 0 1 22105290978347713 2251799813685248 62500007645631 546116500000000000000 2993432188414912251321 4503599627370496000 8463563535348413127 1092233000000000000000000 (Enclosure.Real.IsNear.const Bool.false 270834 4000) (BSN.isNear_log_sfrac 293405222224 16000000 22105290978347713 2251799813685248 62500007645631 546116500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 293405222224) qz650)) Bool.false Ns60p1636 Ns60p84 1000000122330096 8737864000000000000000 22105290978347713 2251799813685248 62500007645631 546116500000000000000 (BSN.log_rat_reduce_isNear 293405222224 16000000 14 586810444448 524288000000 3780265 33554432 24973259072661432 36028797018963968 8737864 1000000000000000 rfl rfl rfl rfl (Ns60p1640 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p1642 := BSN.arctan_dyadic_bound_f 1000 541668 1 0 4194304 1092233 0 1 1 0 1 1 7743 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 541668) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 541668) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz1023 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 541668)))

noncomputable abbrev qz796 := qz1023

noncomputable abbrev qz486 := qz796

noncomputable def Ns60p1643 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz486 884279719003555 562949953421312 1 2000000000000000 7743 4194304 1 1092233 3704579041046145531904 883240471135651 562949953421312 2000000001092233 2184466000000000000000 qz15 (Ns60p1642 rfl) rfl rfl 

noncomputable abbrev qz797 := (@HMul.hMul Real Real Real qz5 qz12 qz1021)

noncomputable abbrev qz487 := qz797

noncomputable abbrev qz798 := qz1021

noncomputable abbrev qz488 := qz798

noncomputable abbrev qz799 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 270834 4000) qz1020)

noncomputable def Ns60p1644 := @Enclosure.Real.IsNear.subLit_ff_p qz799 qz487 2993432188414912251321 4503599627370496000 8463563535348413127 1092233000000000000000000 883240471135651 2251799813685248 2000000001092233 8737864000000000000000 Ns60p1635 2991665707472640949321 4503599627370496000 128140640227719739 16062250000000000000000 (Ns60p1641 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz12 qz488 1 4 0 1 883240471135651 562949953421312 2000000001092233 2184466000000000000000 883240471135651 2251799813685248 2000000001092233 8737864000000000000000 qz335 Ns60p1643 rfl) 

noncomputable def Ns60p1645 := @Ns60p1630 Ns60p1623 Ns60p1624 527947376431731353597 Ns60p1625 (@Ns60p1632 527947376431731353597 Ns60p1625 (Ns60p1634 (Ns60p1644 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 270834 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz1022 (Real.log Real.pi) 270834 2000 0 1 38410761 33554432 1 16777216 5201470022337 33554432000 135417 16777216000 (Enclosure.Real.IsNear.const Bool.false 270834 2000) RS061to078.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns60p1626 Ns60p1627) 

noncomputable def Ns60p1646 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz157) Bool.false Ns60p1623 Ns60p1624 527947376431731353597 Ns60p1625 784019705 2097152 17 1048576 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz157) (@HAdd.hAdd Real Real Real qz336 qz483 (Enclosure.sfrac Bool.true Ns60p1626 Ns60p1627)) Bool.false Ns60p1623 Ns60p1624 527947376431731353597 Ns60p1625 Ns60p1628 (Ns60p1645 rfl rfl)) 

noncomputable def Ns60p1647 := nat_lit 140061178632025232159535439698908788300761548831441825159681533106578782559209835724800 

noncomputable def Ns60p1648 := nat_lit 281556352814949985842906498101979112247432097499363992979715061737039404310248554496 

noncomputable def Ns60p1649 := nat_lit 366371043274556165202656683928786479367879642591158190858151143274417795286190119714816 

noncomputable def Ns60p1650 := BSN.sin_dyadic_bound_f 26989551416 17179869184 3 2 8388608 2186600 Ns60p1647 Ns60p94 Ns60p1648 Ns60p1649 Ns60p97 Ns60p1648 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26989551416) qz655 0 2 Ns60p1647 Ns60p94 Ns60p1648 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26989551416) qz656 0 2 Ns60p1649 Ns60p97 Ns60p1648 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1651 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz157) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 784019705) qz766) Bool.false 784019705 2097152 17 1048576 Bool.true 8388607 8388608 1 1092233 (Ns60p1646 rfl) (Enclosure.sfrac_false_div 784019705 2097152) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 784019705) qz766) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474805209775512318115840) qz767) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 59 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q1 784019705 2097152 226375608064910080 72057594037927936 59 474805209775512318115840 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 474805209775512318115840 302231454903657293676544 26989551416 17179869184 2186600 2184466 (Ns60p1650 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p1652 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz157) Bool.false Ns60p1623 Ns60p1624 527947376431731353597 Ns60p1625 25088630566 67108864 1078 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz157) (@HAdd.hAdd Real Real Real qz336 qz483 (Enclosure.sfrac Bool.true Ns60p1626 Ns60p1627)) Bool.false Ns60p1623 Ns60p1624 527947376431731353597 Ns60p1625 Ns60p1628 (Ns60p1645 rfl rfl)) 

noncomputable def Ns60p1653 := Ns60p1622 24132 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 118 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 48271405 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 48 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 41187615 67108864) qz160 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz157) qz157 1) Bool.true 8388607 8388608 19616537 1145289310208 67108856 67108864 1150 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz157) qz157 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz157)) Bool.true 8388607 8388608 19616537 1145289310208 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz157) qz157) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz157)) Bool.true 8388607 8388608 19616537 1145289310208 8388607 8388608 19616537 1145289310208 (Ns60p1651 rfl rfl) rfl)) rfl) (Ns60p1652 rfl) RS061to078.d7 

noncomputable def Ns60p1654 := nat_lit 240485070920247694762777304418189612384523688268291888336826818816 

noncomputable def Ns60p1655 := nat_lit 49789610702731958909200746759128190999038139546006760126177536 

noncomputable def Ns60p1656 := nat_lit 721355633539337620370513511761050580771572988525783651490228101376 

noncomputable def Ns60p1657 := BSN.cos_dyadic_bound_f 51539754 67108864 3 2 67108864 33554432 Ns60p1654 Ns60p103 Ns60p1655 Ns60p1656 Ns60p106 Ns60p1655 48271405 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 51539754) qz338 0 2 Ns60p1654 Ns60p103 Ns60p1655 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 51539754) (BSN.cosOddQ 67108864) 0 2 Ns60p1656 Ns60p106 Ns60p1655 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1658 := nat_lit 474129661908387526079136899246911036500657887174985836210900390625 

noncomputable def Ns60p1659 := nat_lit 193455959756191648147157288471312113331610570576684722900390625 

noncomputable def Ns60p1660 := nat_lit 1422002073805650194941116383163790485275310440383804139186900390625 

noncomputable def Ns60p1661 := BSN.cos_dyadic_bound_f 61069275 67108864 3 2 67108864 33554432 Ns60p1658 Ns60p103 Ns60p1659 Ns60p1660 Ns60p106 Ns60p1659 41187615 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 61069275) qz338 0 2 Ns60p1658 Ns60p103 Ns60p1659 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 61069275) (BSN.cosOddQ 67108864) 0 2 Ns60p1660 Ns60p106 Ns60p1659 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1662 := BSN.sin_dyadic_bound_f 2352765 67108864 1 0 67108864 33554432 0 1 1 0 1 1 2352283 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 2352765) qz339 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 2352765) (BSN.sinOddQ 67108864) 0 0 rfl) rfl rfl 

noncomputable def Ns60p1663 := nat_lit 459736282216258455930571673093922697732030343750907557423113110145 

noncomputable def Ns60p1664 := nat_lit 56170560369063105321769421687129060093009398250205604636590721 

noncomputable def Ns60p1665 := nat_lit 1203980272516269853838119136182304094629452694607590888938741760641 

noncomputable def Ns60p1666 := BSN.sin_dyadic_bound_f 52322513 67108864 3 2 67108864 33554432 Ns60p1663 Ns60p119 Ns60p1664 Ns60p1665 Ns60p122 Ns60p1664 47180355 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 52322513) qz339 0 2 Ns60p1663 Ns60p119 Ns60p1664 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 52322513) (BSN.sinOddQ 67108864) 0 2 Ns60p1665 Ns60p122 Ns60p1664 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1667 := Ns60p1620 41079 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 1 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 2352283 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 39 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 47180355 67108864) qz160 rfl rfl (Ns60p1653 RS061to078.d9 RS061to078.d11 RS061to078.d13 RS061to078.d17 (Ns60p1657 rfl rfl) (Ns60p1661 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns60p1652 rfl) RS061to078.d19 RS061to078.d21 RS061to078.d23 RS061to078.d25 RS061to078.d17 (Ns60p1662 rfl rfl) (Ns60p1666 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns60p1668 := nat_lit 766755481944803879329277116006631611142134517352222157834871862423458657307730678806625448363584000000 

noncomputable def Ns60p1669 := nat_lit 807827443277585339131795753011214569791448691673424504742335425022930779931380399761000000000000 

noncomputable def Ns60p1670 := nat_lit 4643192900937472275213042908311285535094832338006464071950339045327831573352620531993511528603609600000 

noncomputable def Ns60p1671 := BSN.cos_dyadic_bound_f 98237330 67108864 4 3 67108864 33554432 Ns60p1668 Ns60p219 Ns60p1669 Ns60p1670 Ns60p222 Ns60p1669 7163353 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 98237330) qz338 0 3 Ns60p1668 Ns60p219 Ns60p1669 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 98237330) (BSN.cosOddQ 67108864) 0 3 Ns60p1670 Ns60p222 Ns60p1669 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz1024 := (BSN.cos_quad_nat2 70 rfl)

noncomputable def Ns60p1672 := Ns60p1618 Bool.true 57538665 41079 Bool.true 98237330 3537118876014220 1 Bool.false 7163353 Bool.true Bool.true 60463092 48496 BSN.abs_quadSignNeg qz1024 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 7163353 67108864) qz160 rfl (Ns60p1667 rfl rfl) (Ns60p1652 rfl) RS061to078.d27 RS061to078.d29 RS061to078.d17 (Ns60p1671 rfl rfl) rfl 

noncomputable def Ns60p1673 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz157) qz157 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz157) qz157 6) 60463092 67108864 48496 67108864 60463092 67108864 48496 67108864 8115218836094976 15115773 8388608 3031 2097152 (Ns60p1672 rfl rfl rfl rfl) 

noncomputable def Ns60p1674 := @Enclosure.Real.IsNear.mulLit_ff qz1019 (Zeta.RiemannSiegel.correction qz159) 818463 2097152 1 4194304 6864552698987 17592186044416 902190068051557 19214766139850620928 5618382395670996981 36893488147419103232 

noncomputable abbrev qz1025 := (@HPow.hPow Real Real Real qz326 qz158 qz8)

noncomputable def Ns60p1675 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz1025 1 1 0 1 818463 2097152 1 4194304 818463 2097152 1 4194304 

noncomputable def Ns60p1676 := @Enclosure.Real.IsNear.sqrt_image qz158 180793747113 4194304000 135417 4194304000 27537308 27537330 4194304 (@Enclosure.Real.IsNear.of_eq qz158 (@HMul.hMul Real Real Real qz5 qz157 qz3) Bool.false 180793747113 4194304000 135417 4194304000 (BSN.t_div_two_pi_mk qz157 270834 1000 qz160) (@Enclosure.Real.IsNear.mulLit_ff qz157 qz3 270834 1000 0 1 1335089 8388608 1 8388608 180793747113 4194304000 135417 4194304000 (Enclosure.Real.IsNear.const Bool.false 270834 1000) RS061to078.d32 rfl)) 

noncomputable abbrev qz800 := (Real.sqrt qz1018)

noncomputable abbrev qz489 := qz800

noncomputable abbrev qz161 := qz489

noncomputable def Ns60p1677 := @Enclosure.Real.IsNear.sqrt_image qz161 27537319 4194304 11 4194304 10747085 10747090 4194304 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 55074638 8388608 22 8388608 27537319 4194304 11 4194304 (Ns60p1676 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns60p1678 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz161) 21494175 8388608 5 8388608 1636925 1636927 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz161) Bool.false 21494175 8388608 5 8388608 21494175 8388608 5 8388608 (Ns60p1677 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns60p1679 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 3273852 8388608 2 8388608 818463 2097152 1 4194304 (Ns60p1678 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz162 := (Real.cos (@HMul.hMul Real Real Real qz323 qz320 qz482))

noncomputable abbrev qz490 := (@HSub.hSub Real Real Real qz647 (@HMul.hMul Real Real Real qz644 qz793 qz793) qz793)

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz323 qz320 (@HSub.hSub Real Real Real qz327 qz490 qz344))

noncomputable def Ns60p1680 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz159) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz162) (Real.cos qz163)) Bool.false 6864552698987 

noncomputable def Ns60p1681 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz162) (Real.cos qz163) 9150553 8388608 175 

noncomputable abbrev qz1026 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz162))

noncomputable def Ns60p1682 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz162) (@Neg.neg Real Real.instNeg qz1026) Bool.true 9150553 8388608 175 8388608 (BSN.inv_eq_neg_inv_neg qz162) 

noncomputable def Ns60p1683 := @Enclosure.Real.IsNear.recentre' qz1026 Bool.false 9150553 8388608 175 8388608 9150553 8388608 

noncomputable def Ns60p1684 := @Enclosure.Real.IsNear.recentre' qz162 Bool.true 7690108 8388608 160208995 9162314481664 1922527 2097152 160208995 9162314481664 

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz323 qz320 qz482)

noncomputable def Ns60p1685 := @Enclosure.Real.IsNear.cos_image qz164 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 29801085) qz337) Bool.false 29801085 8388608 139 8388608 Bool.true 7690108 8388608 1 

noncomputable def Ns60p1686 := nat_lit 296846829519855486942113677 

noncomputable def Ns60p1687 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz159 884279719003555 140737488355328 1 500000000000000 2371495 4194304 11 4194304 2097064932218335664725 590295810358705651712 Ns60p1686 

noncomputable def Ns60p1688 := @Enclosure.Real.IsNear.subLit_ff_p qz161 qz1 27537319 4194304 11 4194304 6 1 0 1 2371495 2371495 4194304 11 

noncomputable def Ns60p1689 := @Ns60p1688 4194304 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 55074638 8388608 22 8388608 27537319 4194304 11 4194304 (Ns60p1676 rfl rfl rfl rfl rfl rfl) rfl) qz345 

noncomputable def Ns60p1690 := @Enclosure.Real.IsNear.recentre' qz164 Bool.false 2097064932218335664725 590295810358705651712 Ns60p1686 Ns60p1589 29801085 8388608 139 8388608 (@Ns60p1687 Ns60p1589 RS061to078.d31 (Ns60p1689 rfl rfl) rfl) 

noncomputable def Ns60p1691 := nat_lit 2485047866477204238460885383457377074641 

noncomputable def Ns60p1692 := BSN.cos_dyadic_bound_f 7060471261 17179869184 2 1 8388608 2186600 Ns60p1691 Ns60p1496 Ns60p1691 Ns60p1691 Ns60p1497 Ns60p1691 7690108 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 7060471261) qz769 0 1 Ns60p1691 Ns60p1496 Ns60p1691 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 7060471261) qz770 0 1 Ns60p1691 Ns60p1497 Ns60p1691 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1693 := @Ns60p1685 1092233 (Ns60p1690 rfl) (Enclosure.sfrac_false_div 29801085 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 29801085) qz337) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 496836496003228856483840) qz657) 226375608064910080 72057594037927936 Bool.false 7690108 8388608 0 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q2 29801085 8388608 226375608064910080 72057594037927936 0 496836496003228856483840 Ns60p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 7690108 8388608 496836496003228856483840 Ns60p84 7060471261 17179869184 2186600 2184466 (Ns60p1692 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p1694 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz162) 1922527 2097152 160208995 9162314481664 4575189 4575364 4194304 (@Enclosure.Real.IsNear.neg qz162 Bool.true 1922527 2097152 160208995 9162314481664 (Ns60p1684 (Ns60p1693 rfl rfl) rfl)) 

noncomputable def Ns60p1695 := Ns60p1682 (@Enclosure.Real.IsNear.neg qz1026 Bool.false 9150553 8388608 175 8388608 (@Ns60p1683 175 8388608 (Ns60p1694 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p1696 := @Enclosure.Real.IsNear.recentre' (Real.cos qz163) Bool.true 1500358 4194304 

noncomputable def Ns60p1697 := @Enclosure.Real.IsNear.cos_image qz163 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16245497)) qz337) Bool.true 16245497 8388608 

noncomputable def Ns60p1698 := nat_lit 4794824665282874853462456205 

noncomputable def Ns60p1699 := nat_lit 2653010653566467470624002325388037 

noncomputable def Ns60p1700 := @Enclosure.Real.IsNear.recentre' qz163 Bool.true Ns60p1698 Ns60p327 Ns60p1699 

noncomputable def Ns60p1701 := nat_lit 75557863725914323419136000000000000000 

noncomputable abbrev qz165 := (@HSub.hSub Real Real Real qz327 qz490 qz344)

noncomputable def Ns60p1702 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz165 884279719003555 140737488355328 1 500000000000000 5422294057231 

noncomputable abbrev qz166 := qz490

noncomputable def Ns60p1703 := @Enclosure.Real.IsNear.subLit_tf qz166 qz23 4322782429455 17592186044416 98310355 17592186044416 1 16 

noncomputable abbrev qz491 := (@HMul.hMul Real Real Real qz644 qz793 qz793)

noncomputable abbrev qz167 := qz491

noncomputable def Ns60p1704 := @Enclosure.Real.IsNear.subLit_ff_n qz167 qz159 5623988535025 17592186044416 52173011 17592186044416 2371495 4194304 11 4194304 

noncomputable def Ns60p1705 := @Enclosure.Real.IsNear.mulLit_ff qz159 qz159 2371495 4194304 11 4194304 2371495 4194304 11 4194304 5623988535025 17592186044416 

noncomputable def Ns60p1706 := nat_lit 34371798937664616490279338209588478357887790483591724934493771979152268065571530377551449121 

noncomputable def Ns60p1707 := nat_lit 337906096627677584229110709027804288325480018642790257131863165060873457909167389969441 

noncomputable def Ns60p1708 := nat_lit 207366287352930602191175520708683294444900653814524889406785061430098634142985567515649805345 

noncomputable def Ns60p1709 := BSN.cos_dyadic_bound_t 16245497 8388608 4 3 4194304 1092233 Ns60p1706 Ns60p274 Ns60p1707 Ns60p1708 Ns60p277 Ns60p1707 1500358 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16245497) (BSN.cosEvenQ 8388608) 0 3 Ns60p1706 Ns60p274 Ns60p1707 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16245497) (BSN.cosOddQ 8388608) 0 3 Ns60p1708 Ns60p277 Ns60p1707 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1710 := @Ns60p1696 41461197 1145289310208 750179 2097152 41461197 1145289310208 (@Ns60p1697 37 1048576 Bool.true 1500358 4194304 1 1092233 (@Ns60p1700 Ns60p1701 16245497 8388608 37 1048576 (@Ns60p1702 17592186044416 98310355 17592186044416 Ns60p1698 Ns60p327 Ns60p1699 Ns60p1701 RS061to078.d31 (@Ns60p1703 0 1 86756704915696 5422294057231 17592186044416 98310355 17592186044416 (@Ns60p1704 18131063634992824320 4322782429455 17592186044416 98310355 17592186044416 (@Ns60p1705 52173011 17592186044416 (Ns60p1689 rfl rfl) (Ns60p1689 rfl rfl) rfl) (Ns60p1689 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16245497 8388608) (BSN.cos_neg_of_bound 16245497 8388608 Bool.true 1500358 4194304 1 1092233 (Ns60p1709 rfl rfl)) rfl rfl) 

noncomputable def Ns60p1711 := @Ns60p1674 742158486256751856655 Ns60p1233 (Ns60p1675 qz25 (@Enclosure.Real.IsNear.of_eq qz1025 (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 818463 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz158 (BSN.t_div_two_pi_nonneg qz157 270834 1000 qz160)) Ns60p1679) rfl) (@Ns60p1680 17592186044416 902190068051557 19214766139850620928 (BSN.correction_mk qz159 (BSN.cos_two_pi_p_ne_zero_mk qz157 270834 1000 6 qz160 rfl rfl (@BSN.floor_sqrt_eq_dec qz157 270834 1000 6 qz160 rfl rfl rfl))) (@Ns60p1681 8388608 750179 2097152 41461197 1145289310208 6864552698987 17592186044416 902190068051557 19214766139850620928 Ns60p1695 (Ns60p1710 rfl) rfl)) 

noncomputable def Ns60p1712 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz157) (hardyZApproximantRS₀ qz157) Bool.true 72098255100961040373 36893488147419103232 58982114656143983889423 Ns60p1233 (@Eq.refl Real (hardyZApproximantRS₀ qz157)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz157) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz157) qz157 6) (@HMul.hMul Real Real Real qz5 qz1019 (Zeta.RiemannSiegel.correction qz159))) Bool.true 72098255100961040373 36893488147419103232 58982114656143983889423 Ns60p1233 (BSN.hardyZApproximantRS₀_eq qz157 6 (@BSN.floor_sqrt_eq_dec qz157 270834 1000 6 qz160 rfl rfl rfl)) (@Ns60p1617 72098255100961040373 36893488147419103232 58982114656143983889423 Ns60p1233 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz157) qz157 6) (@HAdd.hAdd Real Real Real qz336 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz157) qz157 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz157) qz157 6)) Bool.true 15115773 8388608 3031 2097152 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz157) qz157 6) (Ns60p1673 (Ns60p1672 rfl rfl rfl rfl) rfl rfl)) (Ns60p1711 rfl) rfl rfl)) 

theorem RS061to078.d56 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz157) Bool.true 72098255100961040373 36893488147419103232 58982114656143983889423 Ns60p1233 := Ns60p1712 

noncomputable def Ns60p1713 := nat_lit 251059070167039790830059520 

noncomputable abbrev qz1027 := (Enclosure.sfrac Bool.false 272502 1000)

noncomputable abbrev qz801 := qz1027

noncomputable abbrev qz492 := qz801

noncomputable abbrev qz168 := qz492

noncomputable abbrev qz1028 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 272502 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz802 := qz1028

noncomputable abbrev qz493 := qz802

noncomputable abbrev qz169 := qz493

noncomputable abbrev qz803 := (@HSub.hSub Real Real Real qz920 (Real.sqrt qz1028) qz914)

noncomputable abbrev qz494 := qz803

noncomputable abbrev qz170 := qz494

noncomputable abbrev qz1029 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz326 qz169 qz8))

noncomputable def Ns60p1714 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 6) (@HMul.hMul Real Real Real qz5 qz1029 (Zeta.RiemannSiegel.correction qz170)) 57026125 16777216 48787 33554432 710935186180635405 4611686018427387904 2048876274012062757 107170971382234067501056 Ns60p1713 

noncomputable def Ns60p1715 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.cos BSN.quadSignNeg 5 6 272502 1000 70 67108864 33554432 1125899906842624 Bool.false 25299448291 1085 120242927 63 27397080 8 

noncomputable def Ns60p1716 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 272502 1000 0 39 67108864 33554432 1125899906842624 Bool.false 25299448291 1085 

noncomputable def Ns60p1717 := Ns60p1716 93032624 62 33554424 8 108007536 62 30011992 8 Bool.false 87637685 24274 Bool.true 52127814 Bool.true 21661358 3537118876014220 1 Bool.false 47861031 Bool.false Bool.false 21287175 Bool.false Bool.false 121088107 

noncomputable def Ns60p1718 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz168) qz168 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 272502 1000 119 49 67108864 33554432 1125899906842624 Bool.false 25299448291 1085 

noncomputable def Ns60p1719 := Ns60p1718 46516304 62 47453136 16 73726608 62 38745320 8 Bool.false 67108856 1150 Bool.false 79353927 Bool.false 43496661 3537118876014220 1 Bool.false 62112101 Bool.false Bool.false 40514508 Bool.true Bool.false 87637685 

noncomputable def Ns60p1720 := nat_lit 10862593175829177377331036851780389176715887951824791 

noncomputable def Ns60p1721 := nat_lit 28813920356170235994731985654023378642975850496000 

noncomputable def Ns60p1722 := nat_lit 721262597921363409532896015360000 

noncomputable def Ns60p1723 := nat_lit 1179274855555977974075121305241784320 

noncomputable abbrev qz171 := (@Eq.refl Real qz492)

noncomputable def Ns60p1724 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz168 272502 1000 297030360016 16000000 545004 4000 2000 Ns60p1722 Ns60p1723 qz171 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns60p1725 := nat_lit 2002193174168833974189656712520161333052272467280345477120 

noncomputable abbrev qz1030 := (Real.log (Enclosure.sfrac Bool.false 297030360016 16000000))

noncomputable abbrev qz1031 := (@HSub.hSub Real Real Real qz11 qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 545004))))

noncomputable abbrev qz804 := (@HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 272502 4000) qz1030) (@HMul.hMul Real Real Real qz5 qz12 qz1031))

noncomputable abbrev qz1032 := (Enclosure.sfrac Bool.false 272502 2000)

noncomputable abbrev qz495 := (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 qz804 qz1032) (@HMul.hMul Real Real Real qz5 qz1032 (Real.log Real.pi)))

noncomputable def Ns60p1726 := @Enclosure.Real.IsNear.addLit_ft_p qz495 (Enclosure.sfrac Bool.true Ns60p1722 Ns60p1723) 1697819989134637057291 4503599627370496000 9029592545731620019447 Ns60p1243 Ns60p1722 Ns60p1723 0 1 Ns60p1725 

noncomputable def Ns60p1727 := nat_lit 56969385373658917983550963712000 

noncomputable abbrev qz496 := (@HSub.hSub Real Real Real qz11 qz804 qz1032)

noncomputable def Ns60p1728 := @Enclosure.Real.IsNear.subLit_ff_p qz496 (@HMul.hMul Real Real Real qz5 qz1032 (Real.log Real.pi)) 2400249085623009068299 4503599627370496000 4382844270930699253 546116500000000000000000 5233504597011 33554432000 136251 16777216000 Ns60p1727 1697819989134637057291 4503599627370496000 

noncomputable abbrev qz497 := qz804

noncomputable def Ns60p1729 := @Enclosure.Real.IsNear.subLit_ff_p qz497 qz1032 602773807690373303759 900719925474099200 4382844270930699253 546116500000000000000000 272502 2000 0 1 960099634249203627319600 2400249085623009068299 4503599627370496000 4382844270930699253 546116500000000000000000 

noncomputable def Ns60p1730 := nat_lit 1357325947851530113476921322721247232 

noncomputable def Ns60p1731 := nat_lit 11882532961037008806871040 

noncomputable def Ns60p1732 := nat_lit 1466493885385654109674026200232146859874714583040 

noncomputable def Ns60p1733 := nat_lit 1907167793857298464742607921294983346258444288 

noncomputable def Ns60p1734 := nat_lit 4443691367073983169811821734807291166916608 

noncomputable def Ns60p1735 := BSN.log_dyadic_bound 34886360016 559174360016 3 2 Ns60p1732 33554432 8737864 Ns60p1733 Ns60p1734 4192303 594060720032 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 34886360016) (BSN.artanhQ 559174360016) 0 2 Ns60p1733 Ns60p1732 Ns60p1734 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz805 := qz1030

noncomputable def Ns60p1736 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 272502 4000) qz805 272502 4000 0 1 22132942380452545 2251799813685248 62500007645631 546116500000000000000 603127106455807941759 900719925474099200 8515688541724869381 1092233000000000000000000 (Enclosure.Real.IsNear.const Bool.false 272502 4000) (BSN.isNear_log_sfrac 297030360016 16000000 22132942380452545 2251799813685248 62500007645631 546116500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 297030360016) qz650)) Bool.false Ns60p1731 Ns60p84 1000000122330096 8737864000000000000000 22132942380452545 2251799813685248 62500007645631 546116500000000000000 (BSN.log_rat_reduce_isNear 297030360016 16000000 14 594060720032 524288000000 4192303 33554432 24973259072661432 36028797018963968 8737864 1000000000000000 rfl rfl rfl rfl (Ns60p1735 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p1737 := BSN.arctan_dyadic_bound_f 1000 545004 1 0 4194304 1092233 0 1 1 0 1 1 7695 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 545004) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 545004) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz1033 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 545004)))

noncomputable abbrev qz806 := qz1033

noncomputable abbrev qz498 := qz806

noncomputable def Ns60p1738 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz498 884279719003555 562949953421312 1 2000000000000000 7695 4194304 1 1092233 3704606062643909754880 883246913586595 562949953421312 2000000001092233 2184466000000000000000 qz15 (Ns60p1737 rfl) rfl rfl 

noncomputable abbrev qz807 := (@HMul.hMul Real Real Real qz5 qz12 qz1031)

noncomputable abbrev qz499 := qz807

noncomputable abbrev qz808 := qz1031

noncomputable abbrev qz500 := qz808

noncomputable abbrev qz809 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 272502 4000) qz1030)

noncomputable def Ns60p1739 := @Enclosure.Real.IsNear.subLit_ff_p qz809 qz499 603127106455807941759 900719925474099200 8515688541724869381 1092233000000000000000000 883246913586595 2251799813685248 2000000001092233 8737864000000000000000 Ns60p1730 602773807690373303759 900719925474099200 4382844270930699253 546116500000000000000000 (Ns60p1736 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz12 qz500 1 4 0 1 883246913586595 562949953421312 2000000001092233 2184466000000000000000 883246913586595 2251799813685248 2000000001092233 8737864000000000000000 qz335 Ns60p1738 rfl) 

noncomputable def Ns60p1740 := @Ns60p1726 Ns60p1720 Ns60p1721 9029592545731620019447 Ns60p1243 (@Ns60p1728 9029592545731620019447 Ns60p1243 (Ns60p1729 (Ns60p1739 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 272502 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz1032 (Real.log Real.pi) 272502 2000 0 1 38410761 33554432 1 16777216 5233504597011 33554432000 136251 16777216000 (Enclosure.Real.IsNear.const Bool.false 272502 2000) RS061to078.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns60p1722 Ns60p1723) 

noncomputable def Ns60p1741 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz168) Bool.false Ns60p1720 Ns60p1721 9029592545731620019447 Ns60p1243 790607759 2097152 17 1048576 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz168) (@HAdd.hAdd Real Real Real qz336 qz495 (Enclosure.sfrac Bool.true Ns60p1722 Ns60p1723)) Bool.false Ns60p1720 Ns60p1721 9029592545731620019447 Ns60p1243 Ns60p1724 (Ns60p1740 rfl rfl)) 

noncomputable def Ns60p1742 := nat_lit 140002690086215248605699042908623336070006675159898987359645238349967285305441875616000 

noncomputable def Ns60p1743 := nat_lit 281321721447955353397579971803397175891750876850172909024818229250024735869278576896 

noncomputable def Ns60p1744 := nat_lit 366218238867267056728472840044427046660478457332454210755887823307319040513321318441216 

noncomputable def Ns60p1745 := BSN.sin_dyadic_bound_f 26986738966 17179869184 3 2 8388608 2186600 Ns60p1742 Ns60p94 Ns60p1743 Ns60p1744 Ns60p97 Ns60p1743 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26986738966) qz655 0 2 Ns60p1742 Ns60p94 Ns60p1743 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26986738966) qz656 0 2 Ns60p1744 Ns60p97 Ns60p1743 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1746 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz168) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 790607759) qz766) Bool.false 790607759 2097152 17 1048576 Bool.false 8388607 8388608 1 1092233 (Ns60p1741 rfl) (Enclosure.sfrac_false_div 790607759 2097152) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 790607759) qz766) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474755732630322290884608) qz767) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 59 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q3 790607759 2097152 226375608064910080 72057594037927936 59 474755732630322290884608 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 474755732630322290884608 302231454903657293676544 26986738966 17179869184 2186600 2184466 (Ns60p1745 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p1747 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz168) Bool.false Ns60p1720 Ns60p1721 9029592545731620019447 Ns60p1243 25299448291 67108864 1085 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz168) (@HAdd.hAdd Real Real Real qz336 qz495 (Enclosure.sfrac Bool.true Ns60p1722 Ns60p1723)) Bool.false Ns60p1720 Ns60p1721 9029592545731620019447 Ns60p1243 Ns60p1724 (Ns60p1740 rfl rfl)) 

noncomputable def Ns60p1748 := Ns60p1719 24274 BSN.abs_quadSignPos (BSN.cos_quad_nat3 119 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 62112101 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 49 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 40514508 67108864) qz171 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 1) Bool.false 8388607 8388608 19616537 1145289310208 67108856 67108864 1150 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz168)) Bool.false 8388607 8388608 19616537 1145289310208 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz168) qz168) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz168)) Bool.false 8388607 8388608 19616537 1145289310208 8388607 8388608 19616537 1145289310208 (Ns60p1746 rfl rfl) rfl)) rfl) (Ns60p1747 rfl) RS061to078.d7 

noncomputable def Ns60p1749 := nat_lit 2433636517586164788489967726080970183306963906123281266571770258625 

noncomputable def Ns60p1750 := nat_lit 1572343352685649478825828971325030855893605363809565521777190081 

noncomputable def Ns60p1751 := nat_lit 6371264228249892918317530797591824239656315821638616401605092369601 

noncomputable def Ns60p1752 := BSN.sin_dyadic_bound_f 79353927 67108864 3 2 67108864 33554432 Ns60p1749 Ns60p119 Ns60p1750 Ns60p1751 Ns60p122 Ns60p1750 62112101 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 79353927) qz339 0 2 Ns60p1749 Ns60p119 Ns60p1750 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 79353927) (BSN.sinOddQ 67108864) 0 2 Ns60p1751 Ns60p122 Ns60p1750 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1753 := nat_lit 219558553201303361341047097812400042390467816107829897472471766625 

noncomputable def Ns60p1754 := nat_lit 12812897698429090515306556889205050856849239202331324025706081 

noncomputable def Ns60p1755 := nat_lit 575013561311901823080003331273703302845076048180845956950908245601 

noncomputable def Ns60p1756 := BSN.sin_dyadic_bound_f 43496661 67108864 3 2 67108864 33554432 Ns60p1753 Ns60p119 Ns60p1754 Ns60p1755 Ns60p122 Ns60p1754 40514508 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 43496661) qz339 0 2 Ns60p1753 Ns60p119 Ns60p1754 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 43496661) (BSN.sinOddQ 67108864) 0 2 Ns60p1755 Ns60p122 Ns60p1754 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1757 := nat_lit 251652345244146333937440897564511540570054924387387973457990164736 

noncomputable def Ns60p1758 := nat_lit 54520032244749417480477128155769777331262014659908721936998656 

noncomputable def Ns60p1759 := nat_lit 754847995667949502977361738437223082155502249132844102930096496896 

noncomputable def Ns60p1760 := BSN.cos_dyadic_bound_f 52127814 67108864 3 2 67108864 33554432 Ns60p1757 Ns60p103 Ns60p1758 Ns60p1759 Ns60p106 Ns60p1758 47861031 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 52127814) qz338 0 2 Ns60p1757 Ns60p103 Ns60p1758 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 52127814) (BSN.cosOddQ 67108864) 0 2 Ns60p1759 Ns60p106 Ns60p1758 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1761 := nat_lit 220162181699504061936388538896 

noncomputable def Ns60p1762 := BSN.sin_dyadic_bound_f 21661358 67108864 2 1 67108864 33554432 Ns60p1761 Ns60p115 Ns60p1761 Ns60p1761 Ns60p116 Ns60p1761 21287175 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 21661358) qz339 0 1 Ns60p1761 Ns60p115 Ns60p1761 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 21661358) (BSN.sinOddQ 67108864) 0 1 Ns60p1761 Ns60p116 Ns60p1761 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1763 := Ns60p1717 41325 BSN.abs_quadSignPos (BSN.cos_quad_nat0 0 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 47861031 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 39 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 21287175 67108864) qz171 rfl rfl (Ns60p1748 RS061to078.d9 RS061to078.d11 RS061to078.d13 RS061to078.d17 (Ns60p1752 rfl rfl) (Ns60p1756 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns60p1747 rfl) RS061to078.d19 RS061to078.d21 RS061to078.d23 RS061to078.d25 RS061to078.d17 (Ns60p1760 rfl rfl) (Ns60p1762 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns60p1764 := nat_lit 492900085702255870878977058639097854095912282763949618737376041174487160840958762125769549701415224481 

noncomputable def Ns60p1765 := nat_lit 215224758243965546761786771311246777648381018793799752923798885640123383969056121368885842724001 

noncomputable def Ns60p1766 := nat_lit 2986759523701534753119499172907241425627779026715716284052248989121024176432835460181824265936000042145 

noncomputable def Ns60p1767 := BSN.cos_dyadic_bound_f 87984807 67108864 4 3 67108864 33554432 Ns60p1764 Ns60p219 Ns60p1765 Ns60p1766 Ns60p222 Ns60p1765 17234258 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 87984807) qz338 0 3 Ns60p1764 Ns60p219 Ns60p1765 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 87984807) (BSN.cosOddQ 67108864) 0 3 Ns60p1766 Ns60p222 Ns60p1765 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1768 := Ns60p1715 Bool.false 121088107 41325 Bool.true 87984807 3537118876014220 1 Bool.false 17234258 Bool.true Bool.false 114052250 48787 BSN.abs_quadSignNeg qz1024 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 17234258 67108864) qz171 rfl (Ns60p1763 rfl rfl) (Ns60p1747 rfl) RS061to078.d27 RS061to078.d29 RS061to078.d17 (Ns60p1767 rfl rfl) rfl 

noncomputable def Ns60p1769 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 6) 114052250 67108864 48787 67108864 114052250 67108864 48787 67108864 15307833868288000 57026125 16777216 48787 33554432 (Ns60p1768 rfl rfl rfl rfl) 

noncomputable def Ns60p1770 := @Enclosure.Real.IsNear.mulLit_ff qz1029 (Zeta.RiemannSiegel.correction qz170) 1634415 4194304 1 4194304 434978378307 1099511627776 1247398343799 25551550717886464 710935186180635405 4611686018427387904 

noncomputable abbrev qz1034 := (@HPow.hPow Real Real Real qz326 qz169 qz8)

noncomputable def Ns60p1771 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz1034 1 1 0 1 1634415 4194304 1 4194304 1634415 4194304 1 4194304 

noncomputable def Ns60p1772 := @Enclosure.Real.IsNear.sqrt_image qz169 181907211339 4194304000 136251 4194304000 27621976 27621997 4194304 (@Enclosure.Real.IsNear.of_eq qz169 (@HMul.hMul Real Real Real qz5 qz168 qz3) Bool.false 181907211339 4194304000 136251 4194304000 (BSN.t_div_two_pi_mk qz168 272502 1000 qz171) (@Enclosure.Real.IsNear.mulLit_ff qz168 qz3 272502 1000 0 1 1335089 8388608 1 8388608 181907211339 4194304000 136251 4194304000 (Enclosure.Real.IsNear.const Bool.false 272502 1000) RS061to078.d32 rfl)) 

noncomputable abbrev qz810 := (Real.sqrt qz1028)

noncomputable abbrev qz501 := qz810

noncomputable abbrev qz172 := qz501

noncomputable def Ns60p1773 := @Enclosure.Real.IsNear.sqrt_image qz172 55243973 8388608 21 8388608 10763594 10763599 4194304 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 55243973 8388608 21 8388608 55243973 8388608 21 8388608 (Ns60p1772 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns60p1774 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz172) 21527193 8388608 5 8388608 1634414 1634416 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz172) Bool.false 21527193 8388608 5 8388608 21527193 8388608 5 8388608 (Ns60p1773 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns60p1775 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz172)) Bool.false 3268830 8388608 2 8388608 1634415 4194304 1 4194304 (Ns60p1774 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz173 := (Real.cos (@HMul.hMul Real Real Real qz323 qz320 qz494))

noncomputable abbrev qz502 := (@HSub.hSub Real Real Real qz647 (@HMul.hMul Real Real Real qz644 qz803 qz803) qz803)

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz323 qz320 (@HSub.hSub Real Real Real qz327 qz502 qz344))

noncomputable def Ns60p1776 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz170) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz173) (Real.cos qz174)) Bool.false 434978378307 

noncomputable def Ns60p1777 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz173) (Real.cos qz174) 4883721 4194304 3 

noncomputable abbrev qz1035 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz173))

noncomputable def Ns60p1778 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz173) (@Neg.neg Real Real.instNeg qz1035) Bool.true 4883721 4194304 3 131072 (BSN.inv_eq_neg_inv_neg qz173) 

noncomputable def Ns60p1779 := @Enclosure.Real.IsNear.recentre' qz1035 Bool.false 9767442 8388608 192 8388608 4883721 4194304 

noncomputable def Ns60p1780 := @Enclosure.Real.IsNear.recentre' qz173 Bool.true 7204419 8388608 153655597 9162314481664 7204419 8388608 153655597 9162314481664 

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz323 qz320 qz494)

noncomputable def Ns60p1781 := @Enclosure.Real.IsNear.cos_image qz175 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3858131) qz714) Bool.false 3858131 1048576 133 8388608 Bool.true 7204419 8388608 1 

noncomputable def Ns60p1782 := nat_lit 566707583632121505003194707 

noncomputable def Ns60p1783 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz170 884279719003555 140737488355328 1 500000000000000 4912325 8388608 21 8388608 4343869370654138315375 1180591620717411303424 Ns60p1782 

noncomputable def Ns60p1784 := @Enclosure.Real.IsNear.subLit_ff_p qz172 qz1 55243973 8388608 21 8388608 6 1 0 1 4912325 4912325 8388608 21 

noncomputable def Ns60p1785 := @Ns60p1784 8388608 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 55243973 8388608 21 8388608 55243973 8388608 21 8388608 (Ns60p1772 rfl rfl rfl rfl rfl rfl) rfl) qz345 

noncomputable def Ns60p1786 := @Enclosure.Real.IsNear.recentre' qz175 Bool.false 4343869370654138315375 1180591620717411303424 Ns60p1782 Ns60p144 3858131 1048576 133 8388608 (@Ns60p1783 Ns60p144 RS061to078.d31 (Ns60p1785 rfl rfl) rfl) 

noncomputable def Ns60p1787 := nat_lit 1066591414905057658501936561118364400449547319264066527536879940481323617682672190625 

noncomputable def Ns60p1788 := nat_lit 305970350525552328669815250324704227796179077150711974597160454533877424919820338462720 

noncomputable def Ns60p1789 := nat_lit 53109905867709202892289116674384637099508155738903339427058146473149347875390625 

noncomputable def Ns60p1790 := nat_lit 3199668024903437557100025105121744432074442941480721775931785705151024554352265790625 

noncomputable def Ns60p1791 := nat_lit 13768665773649854790141686264611690250828058471782038856872220454024484121391915230822400 

noncomputable def Ns60p1792 := BSN.cos_dyadic_bound_f 9239467485 17179869184 3 2 8388608 2186600 Ns60p1787 Ns60p1788 Ns60p1789 Ns60p1790 Ns60p1791 Ns60p1789 7204419 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 9239467485) qz769 0 2 Ns60p1787 Ns60p1788 Ns60p1789 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 9239467485) qz770 0 2 Ns60p1790 Ns60p1791 Ns60p1789 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1793 := @Ns60p1781 1092233 (Ns60p1786 rfl) (Enclosure.sfrac_false_div 3858131 1048576) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3858131) qz714) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 81271215481747587203072) qz756) 226375608064910080 72057594037927936 Bool.false 7204419 8388608 0 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q2 3858131 1048576 226375608064910080 72057594037927936 0 81271215481747587203072 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 7204419 8388608 81271215481747587203072 151115727451828646838272 9239467485 17179869184 2186600 2184466 (Ns60p1792 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p1794 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz173) 7204419 8388608 153655597 9162314481664 4883625 4883817 4194304 (@Enclosure.Real.IsNear.neg qz173 Bool.true 7204419 8388608 153655597 9162314481664 (Ns60p1780 (Ns60p1793 rfl rfl) rfl)) 

noncomputable def Ns60p1795 := Ns60p1778 (@Enclosure.Real.IsNear.neg qz1035 Bool.false 4883721 4194304 3 131072 (@Ns60p1779 3 131072 (Ns60p1794 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p1796 := @Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.true 1425072 4194304 

noncomputable def Ns60p1797 := @Enclosure.Real.IsNear.cos_image qz174 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16084835)) qz337) Bool.true 16084835 8388608 

noncomputable def Ns60p1798 := nat_lit 18989622580429290460509725845 

noncomputable def Ns60p1799 := nat_lit 10321603331523590869269486033409421 

noncomputable def Ns60p1800 := @Enclosure.Real.IsNear.recentre' qz174 Bool.true Ns60p1798 Ns60p159 Ns60p1799 

noncomputable abbrev qz176 := (@HSub.hSub Real Real Real qz327 qz502 qz344)

noncomputable def Ns60p1801 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz176 884279719003555 140737488355328 1 500000000000000 21474678399079 

noncomputable abbrev qz177 := qz502

noncomputable def Ns60p1802 := @Enclosure.Real.IsNear.subLit_tf qz177 qz23 17076631887975 70368744177664 382478859 70368744177664 1 16 

noncomputable abbrev qz503 := (@HMul.hMul Real Real Real qz644 qz803 qz803)

noncomputable abbrev qz178 := qz503

noncomputable def Ns60p1803 := @Enclosure.Real.IsNear.subLit_ff_n qz178 qz170 24130936905625 70368744177664 206318091 70368744177664 4912325 8388608 21 8388608 

noncomputable def Ns60p1804 := @Enclosure.Real.IsNear.mulLit_ff qz170 qz170 4912325 8388608 21 8388608 4912325 8388608 21 8388608 24130936905625 70368744177664 

noncomputable def Ns60p1805 := nat_lit 33021424216130036548714033376035241578232271568861952782477016013504827300882976840620640625 

noncomputable def Ns60p1806 := nat_lit 299915784129795947468192017712041470112800298948244581571885730177408285038320556640625 

noncomputable def Ns60p1807 := nat_lit 199262428003088590224918061236202515151378786543835498038148752619261429261704073393478240625 

noncomputable def Ns60p1808 := BSN.cos_dyadic_bound_t 16084835 8388608 4 3 4194304 1092233 Ns60p1805 Ns60p274 Ns60p1806 Ns60p1807 Ns60p277 Ns60p1806 1425072 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 16084835) (BSN.cosEvenQ 8388608) 0 3 Ns60p1805 Ns60p274 Ns60p1806 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 16084835) (BSN.cosOddQ 8388608) 0 3 Ns60p1807 Ns60p277 Ns60p1806 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1809 := @Ns60p1796 10092241 286322327552 89067 262144 10092241 286322327552 (@Ns60p1797 9 262144 Bool.true 1425072 4194304 1 1092233 (@Ns60p1800 Ns60p162 16084835 8388608 9 262144 (@Ns60p1801 70368744177664 382478859 70368744177664 Ns60p1798 Ns60p159 Ns60p1799 Ns60p162 RS061to078.d31 (@Ns60p1802 0 1 343594854385264 21474678399079 70368744177664 382478859 70368744177664 (@Ns60p1803 143249170868522188800 17076631887975 70368744177664 382478859 70368744177664 (@Ns60p1804 206318091 70368744177664 (Ns60p1785 rfl rfl) (Ns60p1785 rfl rfl) rfl) (Ns60p1785 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 16084835 8388608) (BSN.cos_neg_of_bound 16084835 8388608 Bool.true 1425072 4194304 1 1092233 (Ns60p1808 rfl rfl)) rfl rfl) 

noncomputable def Ns60p1810 := @Ns60p1770 2048876274012062757 107170971382234067501056 (Ns60p1771 qz25 (@Enclosure.Real.IsNear.of_eq qz1034 (@Inv.inv Real Real.instInv (Real.sqrt qz172)) Bool.false 1634415 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz169 (BSN.t_div_two_pi_nonneg qz168 272502 1000 qz171)) Ns60p1775) rfl) (@Ns60p1776 1099511627776 1247398343799 25551550717886464 (BSN.correction_mk qz170 (BSN.cos_two_pi_p_ne_zero_mk qz168 272502 1000 6 qz171 rfl rfl (@BSN.floor_sqrt_eq_dec qz168 272502 1000 6 qz171 rfl rfl rfl))) (@Ns60p1777 131072 89067 262144 10092241 286322327552 434978378307 1099511627776 1247398343799 25551550717886464 Ns60p1795 (Ns60p1809 rfl) rfl)) 

noncomputable def Ns60p1811 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz168) (hardyZApproximantRS₀ qz168) Bool.false 14964286694946276595 4611686018427387904 157871814383202927653 107170971382234067501056 (@Eq.refl Real (hardyZApproximantRS₀ qz168)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz168) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 6) (@HMul.hMul Real Real Real qz5 qz1029 (Zeta.RiemannSiegel.correction qz170))) Bool.false 14964286694946276595 4611686018427387904 157871814383202927653 107170971382234067501056 (BSN.hardyZApproximantRS₀_eq qz168 6 (@BSN.floor_sqrt_eq_dec qz168 272502 1000 6 qz171 rfl rfl rfl)) (@Ns60p1714 14964286694946276595 4611686018427387904 157871814383202927653 107170971382234067501056 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz168) qz168 6) (@HAdd.hAdd Real Real Real qz336 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz168) qz168 6)) Bool.false 57026125 16777216 48787 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz168) qz168 6) (Ns60p1769 (Ns60p1768 rfl rfl rfl rfl) rfl rfl)) (Ns60p1810 rfl) rfl rfl)) 

theorem RS061to078.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz168) Bool.false 14964286694946276595 4611686018427387904 157871814383202927653 107170971382234067501056 := Ns60p1811 

noncomputable def Ns60p1812 := nat_lit 841793437758330643190644736 

noncomputable abbrev qz1036 := (Enclosure.sfrac Bool.false 274167 1000)

noncomputable abbrev qz811 := qz1036

noncomputable abbrev qz504 := qz811

noncomputable abbrev qz179 := qz504

noncomputable abbrev qz1037 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 274167 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz812 := qz1037

noncomputable abbrev qz505 := qz812

noncomputable abbrev qz180 := qz505

noncomputable abbrev qz813 := (@HSub.hSub Real Real Real qz920 (Real.sqrt qz1037) qz914)

noncomputable abbrev qz506 := qz813

noncomputable abbrev qz181 := qz506

noncomputable abbrev qz1038 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz326 qz180 qz8))

noncomputable def Ns60p1813 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz179) qz179 6) (@HMul.hMul Real Real Real qz5 qz1038 (Zeta.RiemannSiegel.correction qz181)) 86012875 33554432 49085 33554432 1444360365684193923 9223372036854775808 3564488222625413940011 Ns60p62 Ns60p1812 

noncomputable def Ns60p1814 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz179) qz179 Real.cos BSN.quadSignNeg 5 6 274167 1000 70 67108864 33554432 1125899906842624 Bool.false 25510228483 1091 120242927 63 27397080 8 

noncomputable def Ns60p1815 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz179) qz179 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 274167 1000 0 38 67108864 33554432 1125899906842624 Bool.false 25510228483 1091 

noncomputable def Ns60p1816 := Ns60p1815 93032624 62 33554424 8 108007536 62 30011992 8 Bool.true 104270989 24422 Bool.false 3753058 Bool.true 96128070 3537118876014220 1 Bool.false 67003946 Bool.false Bool.false 9256679 Bool.true Bool.true 74908737 

noncomputable def Ns60p1817 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz179) qz179 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 274167 1000 121 50 67108864 33554432 1125899906842624 Bool.false 25510228483 1091 

noncomputable def Ns60p1818 := Ns60p1817 46516304 62 47453136 16 73726608 62 38745320 8 Bool.true 67108840 1158 Bool.false 1855759 Bool.false 26107694 3537118876014220 1 Bool.false 1855522 Bool.true Bool.false 62094189 Bool.true Bool.true 104270989 

noncomputable def Ns60p1819 := nat_lit 1454184944916697034118297730586146641438637115182964151 

noncomputable def Ns60p1820 := nat_lit 3825473368938990714378704176405133113145371394048000 

noncomputable def Ns60p1821 := nat_lit 743568179498955276811994691360000 

noncomputable def Ns60p1822 := nat_lit 1223173040914492888099414983132582720 

noncomputable abbrev qz182 := (@Eq.refl Real qz504)

noncomputable def Ns60p1823 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz179 274167 1000 300671175556 16000000 548334 4000 2000 Ns60p1821 Ns60p1822 qz182 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns60p1824 := nat_lit 4188052641360087458260697464088102327343274891726936754880 

noncomputable abbrev qz1039 := (Real.log (Enclosure.sfrac Bool.false 300671175556 16000000))

noncomputable abbrev qz1040 := (@HSub.hSub Real Real Real qz11 qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 548334))))

noncomputable abbrev qz814 := (@HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 274167 4000) qz1039) (@HMul.hMul Real Real Real qz5 qz12 qz1040))

noncomputable abbrev qz1041 := (Enclosure.sfrac Bool.false 274167 2000)

noncomputable abbrev qz507 := (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 qz814 qz1041) (@HMul.hMul Real Real Real qz5 qz1041 (Real.log Real.pi)))

noncomputable def Ns60p1825 := @Enclosure.Real.IsNear.addLit_ft_p qz507 (Enclosure.sfrac Bool.true Ns60p1821 Ns60p1822) 3423930383305112501079 9007199254740992000 18167963387318145756899 Ns60p186 Ns60p1821 Ns60p1822 0 1 Ns60p1824 

noncomputable def Ns60p1826 := nat_lit 45955215687738133067922092851200 

noncomputable abbrev qz508 := (@HSub.hSub Real Real Real qz11 qz814 qz1041)

noncomputable def Ns60p1827 := @Enclosure.Real.IsNear.subLit_ff_p qz508 (@HMul.hMul Real Real Real qz5 qz1041 (Real.log Real.pi)) 967474465145404250283 1801439850948198400 17635439596452772627 Ns60p192 10530963111087 67108864000 274167 33554432000 Ns60p1826 3423930383305112501079 9007199254740992000 

noncomputable def Ns60p1828 := nat_lit 9674744651454042502830000 

noncomputable abbrev qz509 := qz814

noncomputable def Ns60p1829 := @Enclosure.Real.IsNear.subLit_ff_p qz509 qz1041 6072110724764308028247 9007199254740992000 17635439596452772627 Ns60p192 274167 2000 0 1 Ns60p1828 967474465145404250283 1801439850948198400 17635439596452772627 Ns60p192 

noncomputable def Ns60p1830 := nat_lit 13673177798700465017004285865551200256 

noncomputable def Ns60p1831 := nat_lit 11897261136941594068385792 

noncomputable def Ns60p1832 := nat_lit 1505062224037133344005556313756603512011843997440 

noncomputable def Ns60p1833 := nat_lit 2357519515678116659429351582328218844674131968 

noncomputable def Ns60p1834 := nat_lit 6609824707773311683912874889894641472799488 

noncomputable def Ns60p1835 := BSN.log_dyadic_bound 38527175556 562815175556 3 2 Ns60p1832 33554432 8737864 Ns60p1833 Ns60p1834 4601092 601342351112 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 38527175556) (BSN.artanhQ 562815175556) 0 2 Ns60p1833 Ns60p1832 Ns60p1834 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz815 := qz1039

noncomputable def Ns60p1836 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 274167 4000) qz815 274167 4000 0 1 22160375745858241 2251799813685248 62500007645631 546116500000000000000 6075643737114716360247 9007199254740992000 17135439596179714377 Ns60p192 (Enclosure.Real.IsNear.const Bool.false 274167 4000) (BSN.isNear_log_sfrac 300671175556 16000000 22160375745858241 2251799813685248 62500007645631 546116500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 300671175556) qz650)) Bool.false Ns60p1831 Ns60p84 1000000122330096 8737864000000000000000 22160375745858241 2251799813685248 62500007645631 546116500000000000000 (BSN.log_rat_reduce_isNear 300671175556 16000000 14 601342351112 524288000000 4601092 33554432 24973259072661432 36028797018963968 8737864 1000000000000000 rfl rfl rfl rfl (Ns60p1835 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p1837 := BSN.arctan_dyadic_bound_f 1000 548334 1 0 4194304 1092233 0 1 1 0 1 1 7649 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 548334) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 548334) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz1042 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 548334)))

noncomputable abbrev qz816 := qz1042

noncomputable abbrev qz510 := qz816

noncomputable def Ns60p1838 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz510 884279719003555 562949953421312 1 2000000000000000 7649 4194304 1 1092233 3704631958341767135232 883253087602083 562949953421312 2000000001092233 2184466000000000000000 qz15 (Ns60p1837 rfl) rfl rfl 

noncomputable abbrev qz817 := (@HMul.hMul Real Real Real qz5 qz12 qz1040)

noncomputable abbrev qz511 := qz817

noncomputable abbrev qz818 := qz1040

noncomputable abbrev qz512 := qz818

noncomputable abbrev qz819 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 274167 4000) qz1039)

noncomputable def Ns60p1839 := @Enclosure.Real.IsNear.subLit_ff_p qz819 qz511 6075643737114716360247 9007199254740992000 17135439596179714377 Ns60p192 883253087602083 2251799813685248 2000000001092233 8737864000000000000000 Ns60p1830 6072110724764308028247 9007199254740992000 17635439596452772627 Ns60p192 (Ns60p1836 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz12 qz512 1 4 0 1 883253087602083 562949953421312 2000000001092233 2184466000000000000000 883253087602083 2251799813685248 2000000001092233 8737864000000000000000 qz335 Ns60p1838 rfl) 

noncomputable def Ns60p1840 := @Ns60p1825 Ns60p1819 Ns60p1820 18167963387318145756899 Ns60p186 (@Ns60p1827 18167963387318145756899 Ns60p186 (Ns60p1829 (Ns60p1839 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 274167 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz1041 (Real.log Real.pi) 274167 2000 0 1 38410761 33554432 1 16777216 10530963111087 67108864000 274167 33554432000 (Enclosure.Real.IsNear.const Bool.false 274167 2000) RS061to078.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns60p1821 Ns60p1822) 

noncomputable def Ns60p1841 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz179) Bool.false Ns60p1819 Ns60p1820 18167963387318145756899 Ns60p186 49824665 131072 137 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz179) (@HAdd.hAdd Real Real Real qz336 qz507 (Enclosure.sfrac Bool.true Ns60p1821 Ns60p1822)) Bool.false Ns60p1819 Ns60p1820 18167963387318145756899 Ns60p186 Ns60p1823 (Ns60p1840 rfl rfl)) 

noncomputable def Ns60p1842 := nat_lit 139744585249350484583061301698838892416636982807976541520425596155441115835622400000000 

noncomputable def Ns60p1843 := nat_lit 280287477182536798345253537945749049503893716614462901650060318596810000000000000000 

noncomputable def Ns60p1844 := nat_lit 365543924499527161948792046340284934058661984193991335474633606557950944331392000000000 

noncomputable def Ns60p1845 := BSN.sin_dyadic_bound_f 26974317300 17179869184 3 2 8388608 2186600 Ns60p1842 Ns60p94 Ns60p1843 Ns60p1844 Ns60p97 Ns60p1843 8388605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26974317300) qz655 0 2 Ns60p1842 Ns60p94 Ns60p1843 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26974317300) qz656 0 2 Ns60p1844 Ns60p97 Ns60p1843 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1846 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz179) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 49824665) (@Nat.cast Real Real.instNatCast 131072)) Bool.false 49824665 131072 137 8388608 Bool.true 8388605 8388608 1 1092233 (Ns60p1841 rfl) (Enclosure.sfrac_false_div 49824665 131072) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 49824665) (@Nat.cast Real Real.instNatCast 131072)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 29658575523094955294720) (@Nat.cast Real Real.instNatCast 18889465931478580854784)) 226375608064910080 72057594037927936 Bool.false 8388605 8388608 60 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q1 49824665 131072 226375608064910080 72057594037927936 60 29658575523094955294720 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388605 8388608 29658575523094955294720 18889465931478580854784 26974317300 17179869184 2186600 2184466 (Ns60p1845 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p1847 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz179) Bool.false Ns60p1819 Ns60p1820 18167963387318145756899 Ns60p186 25510228483 67108864 1091 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz179) (@HAdd.hAdd Real Real Real qz336 qz507 (Enclosure.sfrac Bool.true Ns60p1821 Ns60p1822)) Bool.false Ns60p1819 Ns60p1820 18167963387318145756899 Ns60p186 Ns60p1823 (Ns60p1840 rfl rfl)) 

noncomputable def Ns60p1848 := Ns60p1818 24422 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 121 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 1855522 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 50 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 62094189 67108864) qz182 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz179) qz179 1) Bool.true 8388605 8388608 158024529 9162314481664 67108840 67108864 1158 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz179) qz179 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz179)) Bool.true 8388605 8388608 158024529 9162314481664 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz179) qz179) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz179)) Bool.true 8388605 8388608 158024529 9162314481664 8388605 8388608 158024529 9162314481664 (Ns60p1846 rfl rfl) rfl)) rfl) (Ns60p1847 rfl) RS061to078.d7 

noncomputable def Ns60p1849 := BSN.sin_dyadic_bound_f 1855759 67108864 1 0 67108864 33554432 0 1 1 0 1 1 1855522 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 1855759) qz339 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 1855759) (BSN.sinOddQ 67108864) 0 0 rfl) rfl rfl 

noncomputable def Ns60p1850 := nat_lit 15831016717597132944838960657237906927714548491043041203568394496 

noncomputable def Ns60p1851 := nat_lit 215848040592306025012013994701717808429822560420426551542016 

noncomputable def Ns60p1852 := nat_lit 47492618456710214222466857943724317347526785828008282757602099456 

noncomputable def Ns60p1853 := BSN.cos_dyadic_bound_f 26107694 67108864 3 2 67108864 33554432 Ns60p1850 Ns60p103 Ns60p1851 Ns60p1852 Ns60p106 Ns60p1851 62094189 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 26107694) qz338 0 2 Ns60p1850 Ns60p103 Ns60p1851 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 26107694) (BSN.cosOddQ 67108864) 0 2 Ns60p1852 Ns60p106 Ns60p1851 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1854 := nat_lit 198399742575372014688660496 

noncomputable def Ns60p1855 := BSN.cos_dyadic_bound_f 3753058 67108864 2 1 67108864 33554432 Ns60p1854 Ns60p630 Ns60p1854 Ns60p1854 Ns60p631 Ns60p1854 67003946 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 3753058) qz338 0 1 Ns60p1854 Ns60p630 Ns60p1854 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 3753058) (BSN.cosOddQ 67108864) 0 1 Ns60p1854 Ns60p631 Ns60p1854 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1856 := nat_lit 702834472985696190430151111991554863886486299406179773934417388283280772211076168284135408765504000000 

noncomputable def Ns60p1857 := nat_lit 622590765592188409010487000369756806895834133608821246392321113018509953618489172001000000000000 

noncomputable def Ns60p1858 := nat_lit 4256753782209726431220128016852856339640215550051320458652205579283540005268776998799354685367257600000 

noncomputable def Ns60p1859 := BSN.cos_dyadic_bound_f 96128070 67108864 4 3 67108864 33554432 Ns60p1856 Ns60p219 Ns60p1857 Ns60p1858 Ns60p222 Ns60p1857 9256679 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 96128070) qz338 0 3 Ns60p1856 Ns60p219 Ns60p1857 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 96128070) (BSN.cosOddQ 67108864) 0 3 Ns60p1858 Ns60p222 Ns60p1857 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1860 := Ns60p1816 41577 BSN.abs_quadSignPos (BSN.cos_quad_nat0 0 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 67003946 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 38 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 9256679 67108864) qz182 rfl rfl (Ns60p1848 RS061to078.d9 RS061to078.d11 RS061to078.d13 RS061to078.d17 (Ns60p1849 rfl rfl) (Ns60p1853 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns60p1847 rfl) RS061to078.d19 RS061to078.d21 RS061to078.d23 RS061to078.d25 RS061to078.d17 (Ns60p1855 rfl rfl) (Ns60p1859 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns60p1861 := nat_lit 295114203892859650867745988150438096954590496125026802414833038329915399064942746216245394757309638401 

noncomputable def Ns60p1862 := nat_lit 46291737008643327854064580065057922176636827682948185899530438308361658020476462294847242315521 

noncomputable def Ns60p1863 := nat_lit 1789102861585957621816407162162187677247090465271212047281005965568233340656078001766879408564743382785 

noncomputable def Ns60p1864 := BSN.cos_dyadic_bound_f 77409089 67108864 4 3 67108864 33554432 Ns60p1861 Ns60p219 Ns60p1862 Ns60p1863 Ns60p222 Ns60p1862 27199470 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 77409089) qz338 0 3 Ns60p1861 Ns60p219 Ns60p1862 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 77409089) (BSN.cosOddQ 67108864) 0 3 Ns60p1863 Ns60p222 Ns60p1862 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1865 := Ns60p1814 Bool.true 74908737 41577 Bool.true 77409089 3537118876014220 1 Bool.false 27199470 Bool.true Bool.true 86012875 49085 BSN.abs_quadSignNeg qz1024 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 27199470 67108864) qz182 rfl (Ns60p1860 rfl rfl) (Ns60p1847 rfl) RS061to078.d27 RS061to078.d29 RS061to078.d17 (Ns60p1864 rfl rfl) rfl 

noncomputable def Ns60p1866 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz179) qz179 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz179) qz179 6) 86012875 67108864 49085 67108864 86012875 67108864 49085 67108864 11544452661248000 86012875 33554432 49085 33554432 (Ns60p1865 rfl rfl rfl rfl) 

noncomputable def Ns60p1867 := @Enclosure.Real.IsNear.mulLit_ff qz1038 (Zeta.RiemannSiegel.correction qz181) 203991 524288 1 4194304 7080510246453 17592186044416 2174739886802297 38429532279701241856 1444360365684193923 9223372036854775808 

noncomputable abbrev qz1043 := (@HPow.hPow Real Real Real qz326 qz180 qz8)

noncomputable def Ns60p1868 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz1043 1 1 0 1 203991 524288 1 4194304 203991 524288 1 4194304 

noncomputable def Ns60p1869 := @Enclosure.Real.IsNear.sqrt_image qz180 366037345863 8388608000 274167 8388608000 27706233 27706255 4194304 (@Enclosure.Real.IsNear.of_eq qz180 (@HMul.hMul Real Real Real qz5 qz179 qz3) Bool.false 366037345863 8388608000 274167 8388608000 (BSN.t_div_two_pi_mk qz179 274167 1000 qz182) (@Enclosure.Real.IsNear.mulLit_ff qz179 qz3 274167 1000 0 1 1335089 8388608 1 8388608 366037345863 8388608000 274167 8388608000 (Enclosure.Real.IsNear.const Bool.false 274167 1000) RS061to078.d32 rfl)) 

noncomputable abbrev qz820 := (Real.sqrt qz1037)

noncomputable abbrev qz513 := qz820

noncomputable abbrev qz183 := qz513

noncomputable def Ns60p1870 := @Enclosure.Real.IsNear.sqrt_image qz183 6926561 1048576 11 4194304 10779998 10780003 4194304 (@Enclosure.Real.IsNear.recentre' qz183 Bool.false 55412488 8388608 22 8388608 6926561 1048576 11 4194304 (Ns60p1869 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns60p1871 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz183) 21560001 8388608 5 8388608 1631927 1631929 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz183) Bool.false 21560001 8388608 5 8388608 21560001 8388608 5 8388608 (Ns60p1870 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns60p1872 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz183)) Bool.false 3263856 8388608 2 8388608 203991 524288 1 4194304 (Ns60p1871 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz184 := (Real.cos (@HMul.hMul Real Real Real qz323 qz320 qz506))

noncomputable abbrev qz514 := (@HSub.hSub Real Real Real qz647 (@HMul.hMul Real Real Real qz644 qz813 qz813) qz813)

noncomputable abbrev qz185 := (@HMul.hMul Real Real Real qz323 qz320 (@HSub.hSub Real Real Real qz327 qz514 qz344))

noncomputable def Ns60p1873 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz181) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz184) (Real.cos qz185)) Bool.false 7080510246453 

noncomputable def Ns60p1874 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz184) (Real.cos qz185) 10651981 8388608 237 

noncomputable abbrev qz1044 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz184))

noncomputable def Ns60p1875 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz184) (@Neg.neg Real Real.instNeg qz1044) Bool.true 10651981 8388608 237 8388608 (BSN.inv_eq_neg_inv_neg qz184) 

noncomputable def Ns60p1876 := @Enclosure.Real.IsNear.recentre' qz1044 Bool.false 10651981 8388608 237 8388608 10651981 8388608 

noncomputable def Ns60p1877 := @Enclosure.Real.IsNear.recentre' qz184 Bool.true 6606165 8388608 160208995 9162314481664 6606165 8388608 160208995 9162314481664 

noncomputable abbrev qz186 := (@HMul.hMul Real Real Real qz323 qz320 qz506)

noncomputable def Ns60p1878 := @Enclosure.Real.IsNear.cos_image qz186 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 31923859) qz337) Bool.false 31923859 8388608 139 8388608 Bool.true 6606165 8388608 1 

noncomputable def Ns60p1879 := nat_lit 296846829521306541643067277 

noncomputable def Ns60p1880 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz181 884279719003555 140737488355328 1 500000000000000 635105 1048576 11 4194304 561610470937752798275 147573952589676412928 Ns60p1879 

noncomputable def Ns60p1881 := @Enclosure.Real.IsNear.subLit_ff_p qz183 qz1 6926561 1048576 11 4194304 6 1 0 1 635105 635105 1048576 11 

noncomputable def Ns60p1882 := @Ns60p1881 4194304 (@Enclosure.Real.IsNear.recentre' qz183 Bool.false 55412488 8388608 22 8388608 6926561 1048576 11 4194304 (Ns60p1869 rfl rfl rfl rfl rfl rfl) rfl) qz345 

noncomputable def Ns60p1883 := @Enclosure.Real.IsNear.recentre' qz186 Bool.false 561610470937752798275 147573952589676412928 Ns60p1879 Ns60p1589 31923859 8388608 139 8388608 (@Ns60p1880 Ns60p1589 RS061to078.d31 (Ns60p1882 rfl rfl) rfl) 

noncomputable def Ns60p1884 := nat_lit 2478926563887017672136640430589895058460066361983176133480922179479112904741853578401 

noncomputable def Ns60p1885 := nat_lit 286846414015603960788884293876527506386475759300336842887519916560214984826537121 

noncomputable def Ns60p1886 := nat_lit 7436205998833021808488343523181932120367426134430927726756991498604218284255907660961 

noncomputable def Ns60p1887 := BSN.cos_dyadic_bound_f 11407912413 17179869184 3 2 8388608 2186600 Ns60p1884 Ns60p1788 Ns60p1885 Ns60p1886 Ns60p1791 Ns60p1885 6606165 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 11407912413) qz769 0 2 Ns60p1884 Ns60p1788 Ns60p1885 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 11407912413) qz770 0 2 Ns60p1886 Ns60p1791 Ns60p1885 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1888 := @Ns60p1878 1092233 (Ns60p1883 rfl) (Enclosure.sfrac_false_div 31923859 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 31923859) qz337) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 802760470255765729312768) qz657) 226375608064910080 72057594037927936 Bool.false 6606165 8388608 0 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q2 31923859 8388608 226375608064910080 72057594037927936 0 802760470255765729312768 Ns60p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 6606165 8388608 802760470255765729312768 Ns60p84 11407912413 17179869184 2186600 2184466 (Ns60p1887 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p1889 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz184) 6606165 8388608 160208995 9162314481664 5325872 5326109 4194304 (@Enclosure.Real.IsNear.neg qz184 Bool.true 6606165 8388608 160208995 9162314481664 (Ns60p1877 (Ns60p1888 rfl rfl) rfl)) 

noncomputable def Ns60p1890 := Ns60p1875 (@Enclosure.Real.IsNear.neg qz1044 Bool.false 10651981 8388608 237 8388608 (@Ns60p1876 237 8388608 (Ns60p1889 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p1891 := @Enclosure.Real.IsNear.recentre' (Real.cos qz185) Bool.true 1329426 4194304 

noncomputable def Ns60p1892 := @Enclosure.Real.IsNear.cos_image qz185 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 3970577)) qz766) Bool.true 3970577 2097152 

noncomputable def Ns60p1893 := nat_lit 292976882607285002179359005 

noncomputable def Ns60p1894 := nat_lit 154742504910672534362390528 

noncomputable def Ns60p1895 := nat_lit 2753300354911827016136313502048887 

noncomputable def Ns60p1896 := @Enclosure.Real.IsNear.recentre' qz185 Bool.true Ns60p1893 Ns60p1894 Ns60p1895 

noncomputable abbrev qz187 := (@HSub.hSub Real Real Real qz327 qz514 qz344)

noncomputable def Ns60p1897 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz187 884279719003555 140737488355328 1 500000000000000 331316976191 

noncomputable abbrev qz188 := qz514

noncomputable def Ns60p1898 := @Enclosure.Real.IsNear.subLit_tf qz188 qz23 262597499455 1099511627776 102026705 17592186044416 1 16 

noncomputable abbrev qz515 := (@HMul.hMul Real Real Real qz644 qz813 qz813)

noncomputable abbrev qz189 := qz515

noncomputable def Ns60p1899 := @Enclosure.Real.IsNear.subLit_ff_n qz189 qz181 403358361025 1099511627776 55889361 17592186044416 635105 1048576 11 4194304 

noncomputable def Ns60p1900 := @Enclosure.Real.IsNear.mulLit_ff qz181 qz181 635105 1048576 11 4194304 635105 1048576 11 4194304 403358361025 1099511627776 

noncomputable def Ns60p1901 := nat_lit 1870217787101573699772685897720627587162876580288120018604870946218022546609543940801 

noncomputable def Ns60p1902 := nat_lit 3466537250751077332112698720796095110148055492926080949987665366995300109908547993600 

noncomputable def Ns60p1903 := nat_lit 15354775487074108005974069539544450942657513603894162428513803748799962285705921 

noncomputable def Ns60p1904 := nat_lit 11288495301002990658177720524130690560983064635471171044449257662367850720882527406785 

noncomputable def Ns60p1905 := nat_lit 315454889818348037222255583592444655023473049856273366448877548396572310001677867417600 

noncomputable def Ns60p1906 := BSN.cos_dyadic_bound_t 3970577 2097152 4 3 4194304 1092233 Ns60p1901 Ns60p1902 Ns60p1903 Ns60p1904 Ns60p1905 Ns60p1903 1329426 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 3970577) (BSN.cosEvenQ 2097152) 0 3 Ns60p1901 Ns60p1902 Ns60p1903 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 3970577) (BSN.cosOddQ 2097152) 0 3 Ns60p1904 Ns60p1905 Ns60p1903 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1907 := @Ns60p1891 343704139 9162314481664 664713 2097152 343704139 9162314481664 (@Ns60p1892 307 8388608 Bool.true 1329426 4194304 1 1092233 (@Ns60p1896 Ns60p1701 3970577 2097152 307 8388608 (@Ns60p1897 1099511627776 102026705 17592186044416 Ns60p1893 Ns60p1894 Ns60p1895 Ns60p1701 RS061to078.d31 (@Ns60p1898 0 1 5301071619056 331316976191 1099511627776 102026705 17592186044416 (@Ns60p1899 275353435588526080 262597499455 1099511627776 102026705 17592186044416 (@Ns60p1900 55889361 17592186044416 (Ns60p1882 rfl rfl) (Ns60p1882 rfl rfl) rfl) (Ns60p1882 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 3970577 2097152) (BSN.cos_neg_of_bound 3970577 2097152 Bool.true 1329426 4194304 1 1092233 (Ns60p1906 rfl rfl)) rfl rfl) 

noncomputable def Ns60p1908 := @Ns60p1867 3564488222625413940011 Ns60p62 (Ns60p1868 qz25 (@Enclosure.Real.IsNear.of_eq qz1043 (@Inv.inv Real Real.instInv (Real.sqrt qz183)) Bool.false 203991 524288 1 4194304 (BSN.rpow_neg_quarter_mk qz180 (BSN.t_div_two_pi_nonneg qz179 274167 1000 qz182)) Ns60p1872) rfl) (@Ns60p1873 17592186044416 2174739886802297 38429532279701241856 (BSN.correction_mk qz181 (BSN.cos_two_pi_p_ne_zero_mk qz179 274167 1000 6 qz182 rfl rfl (@BSN.floor_sqrt_eq_dec qz179 274167 1000 6 qz182 rfl rfl rfl))) (@Ns60p1874 8388608 664713 2097152 343704139 9162314481664 7080510246453 17592186044416 2174739886802297 38429532279701241856 Ns60p1890 (Ns60p1907 rfl) rfl)) 

noncomputable def Ns60p1909 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz179) (hardyZApproximantRS₀ qz179) Bool.true 25087399415920097923 9223372036854775808 239353687216267346002731 Ns60p62 (@Eq.refl Real (hardyZApproximantRS₀ qz179)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz179) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz179) qz179 6) (@HMul.hMul Real Real Real qz5 qz1038 (Zeta.RiemannSiegel.correction qz181))) Bool.true 25087399415920097923 9223372036854775808 239353687216267346002731 Ns60p62 (BSN.hardyZApproximantRS₀_eq qz179 6 (@BSN.floor_sqrt_eq_dec qz179 274167 1000 6 qz182 rfl rfl rfl)) (@Ns60p1813 25087399415920097923 9223372036854775808 239353687216267346002731 Ns60p62 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz179) qz179 6) (@HAdd.hAdd Real Real Real qz336 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz179) qz179 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz179) qz179 6)) Bool.true 86012875 33554432 49085 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz179) qz179 6) (Ns60p1866 (Ns60p1865 rfl rfl rfl rfl) rfl rfl)) (Ns60p1908 rfl) rfl rfl)) 

theorem RS061to078.d58 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz179) Bool.true 25087399415920097923 9223372036854775808 239353687216267346002731 Ns60p62 := Ns60p1909 

noncomputable def Ns60p1910 := nat_lit 1932745459524027618716286976 

noncomputable abbrev qz1045 := (Enclosure.sfrac Bool.false 275830 1000)

noncomputable abbrev qz821 := qz1045

noncomputable abbrev qz516 := qz821

noncomputable abbrev qz190 := qz516

noncomputable abbrev qz1046 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 275830 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz822 := qz1046

noncomputable abbrev qz517 := qz822

noncomputable abbrev qz191 := qz517

noncomputable abbrev qz823 := (@HSub.hSub Real Real Real qz920 (Real.sqrt qz1046) qz914)

noncomputable abbrev qz518 := qz823

noncomputable abbrev qz192 := qz518

noncomputable abbrev qz1047 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz326 qz191 qz8))

noncomputable def Ns60p1911 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz190) qz190 6) (@HMul.hMul Real Real Real qz5 qz1047 (Zeta.RiemannSiegel.correction qz192)) 18452343 33554432 6173 4194304 23553959474754923929 147573952589676412928 2967987016324789553 117911588119151453929472 Ns60p1910 

noncomputable def Ns60p1912 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz190) qz190 Real.cos BSN.quadSignNeg 5 6 275830 1000 70 67108864 33554432 1125899906842624 Bool.false 25721094245 1098 120242927 63 27397080 8 

noncomputable def Ns60p1913 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz190) qz190 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 275830 1000 0 38 67108864 33554432 1125899906842624 Bool.false 25721094245 1098 

noncomputable def Ns60p1914 := Ns60p1913 93032624 62 33554424 8 108007536 62 30011992 8 Bool.false 29456679 24572 Bool.false 59905567 Bool.true 64878841 3537118876014220 1 Bool.false 42100130 Bool.false Bool.false 38115210 Bool.true Bool.false 33461101 

noncomputable def Ns60p1915 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz190) qz190 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 275830 1000 122 51 67108864 33554432 1125899906842624 Bool.false 25721094245 1098 

noncomputable def Ns60p1916 := Ns60p1915 46516304 62 47453136 16 73726608 62 38745320 8 Bool.false 67108856 1166 Bool.false 29950550 Bool.false 8951749 3537118876014220 1 Bool.false 60535630 Bool.true Bool.false 8925225 Bool.false Bool.false 29456679 

noncomputable def Ns60p1917 := nat_lit 1368343428439663304867575394145358887009122173547 

noncomputable def Ns60p1918 := nat_lit 3570142551726386507105007183678872646529843200 

noncomputable def Ns60p1919 := nat_lit 111844659200000000000000000 

noncomputable def Ns60p1920 := nat_lit 766394447602679995798864000000000 

noncomputable def Ns60p1921 := nat_lit 1268369427878605828789562502720000000 

noncomputable abbrev qz193 := (@Eq.refl Real qz516)

noncomputable def Ns60p1922 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz190 275830 1000 304329755600 16000000 551660 4000 2000 Ns60p1920 Ns60p1921 qz193 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns60p1923 := nat_lit 437869897100692257557624126126514843842919095535040000000 

noncomputable abbrev qz1048 := (Real.log (Enclosure.sfrac Bool.false 304329755600 16000000))

noncomputable abbrev qz1049 := (@HSub.hSub Real Real Real qz11 qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 551660))))

noncomputable abbrev qz824 := (@HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 275830 4000) qz1048) (@HMul.hMul Real Real Real qz5 qz12 qz1049))

noncomputable abbrev qz1050 := (Enclosure.sfrac Bool.false 275830 2000)

noncomputable abbrev qz519 := (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 qz824 qz1050) (@HMul.hMul Real Real Real qz5 qz1050 (Real.log Real.pi)))

noncomputable def Ns60p1924 := @Enclosure.Real.IsNear.addLit_ft_p qz519 (Enclosure.sfrac Bool.true Ns60p1920 Ns60p1921) 345223227383993737807 900719925474099200 1827661101855340594251 Ns60p1919 Ns60p1920 Ns60p1921 0 1 Ns60p1923 

noncomputable def Ns60p1925 := nat_lit 2316753861615351152734162124800 

noncomputable abbrev qz520 := (@HSub.hSub Real Real Real qz11 qz824 qz1050)

noncomputable def Ns60p1926 := @Enclosure.Real.IsNear.subLit_ff_p qz520 (@HMul.hMul Real Real Real qz5 qz1050 (Real.log Real.pi)) 487424765489686651471 900719925474099200 886968855458372849 109223300000000000000000 1059484020663 6710886400 27583 3355443200 Ns60p1925 345223227383993737807 900719925474099200 

noncomputable abbrev qz521 := qz824

noncomputable def Ns60p1927 := @Enclosure.Real.IsNear.subLit_ff_p qz521 qz1050 611647554011447042639 900719925474099200 886968855458372849 109223300000000000000000 275830 2000 0 1 974849530979373302942000 487424765489686651471 900719925474099200 886968855458372849 109223300000000000000000 

noncomputable def Ns60p1928 := nat_lit 1377307848164014113565139289581289472 

noncomputable def Ns60p1929 := nat_lit 11911882631578206177591296 

noncomputable def Ns60p1930 := nat_lit 1544580100288616685298697762065009551744000000000 

noncomputable def Ns60p1931 := nat_lit 2864863869751723876629474321307451596800000000 

noncomputable def Ns60p1932 := nat_lit 9501333971983629472330699385014348800000000 

noncomputable def Ns60p1933 := BSN.log_dyadic_bound 42185755600 566473755600 3 2 Ns60p1930 33554432 8737864 Ns60p1931 Ns60p1932 5006920 608659511200 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 42185755600) (BSN.artanhQ 566473755600) 0 2 Ns60p1931 Ns60p1930 Ns60p1932 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz825 := qz1048

noncomputable def Ns60p1934 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 275830 4000) qz825 275830 4000 0 1 22187610401917633 2251799813685248 62500007645631 546116500000000000000 612000857716094071039 900719925474099200 1723937710889439873 218446600000000000000000 (Enclosure.Real.IsNear.const Bool.false 275830 4000) (BSN.isNear_log_sfrac 304329755600 16000000 22187610401917633 2251799813685248 62500007645631 546116500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 304329755600) qz650)) Bool.false Ns60p1929 Ns60p84 1000000122330096 8737864000000000000000 22187610401917633 2251799813685248 62500007645631 546116500000000000000 (BSN.log_rat_reduce_isNear 304329755600 16000000 14 608659511200 524288000000 5006920 33554432 24973259072661432 36028797018963968 8737864 1000000000000000 rfl rfl rfl rfl (Ns60p1933 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p1935 := BSN.arctan_dyadic_bound_f 1000 551660 1 0 4194304 1092233 0 1 1 0 1 1 7603 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 551660) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 551660) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz1051 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 551660)))

noncomputable abbrev qz826 := qz1051

noncomputable abbrev qz522 := qz826

noncomputable def Ns60p1936 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz522 884279719003555 562949953421312 1 2000000000000000 7603 4194304 1 1092233 3704657854039624515584 883259261617571 562949953421312 2000000001092233 2184466000000000000000 qz15 (Ns60p1935 rfl) rfl rfl 

noncomputable abbrev qz827 := (@HMul.hMul Real Real Real qz5 qz12 qz1049)

noncomputable abbrev qz523 := qz827

noncomputable abbrev qz828 := qz1049

noncomputable abbrev qz524 := qz828

noncomputable abbrev qz829 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 275830 4000) qz1048)

noncomputable def Ns60p1937 := @Enclosure.Real.IsNear.subLit_ff_p qz829 qz523 612000857716094071039 900719925474099200 1723937710889439873 218446600000000000000000 883259261617571 2251799813685248 2000000001092233 8737864000000000000000 Ns60p1928 611647554011447042639 900719925474099200 886968855458372849 109223300000000000000000 (Ns60p1934 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz12 qz524 1 4 0 1 883259261617571 562949953421312 2000000001092233 2184466000000000000000 883259261617571 2251799813685248 2000000001092233 8737864000000000000000 qz335 Ns60p1936 rfl) 

noncomputable def Ns60p1938 := @Ns60p1924 Ns60p1917 Ns60p1918 1827661101855340594251 Ns60p1919 (@Ns60p1926 1827661101855340594251 Ns60p1919 (Ns60p1927 (Ns60p1937 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 275830 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz1050 (Real.log Real.pi) 275830 2000 0 1 38410761 33554432 1 16777216 1059484020663 6710886400 27583 3355443200 (Enclosure.Real.IsNear.const Bool.false 275830 2000) RS061to078.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns60p1920 Ns60p1921) 

noncomputable def Ns60p1939 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz190) Bool.false Ns60p1917 Ns60p1918 1827661101855340594251 Ns60p1919 803784195 2097152 69 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz190) (@HAdd.hAdd Real Real Real qz336 qz519 (Enclosure.sfrac Bool.true Ns60p1920 Ns60p1921)) Bool.false Ns60p1917 Ns60p1918 1827661101855340594251 Ns60p1919 Ns60p1922 (Ns60p1938 rfl rfl)) 

noncomputable def Ns60p1940 := nat_lit 139941611775363303093522526806457007786571990638603166618785085785469669283599612002560 

noncomputable def Ns60p1941 := nat_lit 281076805013857298720572434428548582290742302156277648623236768506542288580409180416 

noncomputable def Ns60p1942 := nat_lit 366058668394024310570820929123074513164932106992850510665713793717695684418392607047936 

noncomputable def Ns60p1943 := BSN.sin_dyadic_bound_f 26983801042 17179869184 3 2 8388608 2186600 Ns60p1940 Ns60p94 Ns60p1941 Ns60p1942 Ns60p97 Ns60p1941 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26983801042) qz655 0 2 Ns60p1940 Ns60p94 Ns60p1941 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26983801042) qz656 0 2 Ns60p1942 Ns60p97 Ns60p1941 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1944 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz190) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 803784195) qz766) Bool.false 803784195 2097152 69 4194304 Bool.false 8388607 8388608 1 1092233 (Ns60p1939 rfl) (Enclosure.sfrac_false_div 803784195 2097152) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 803784195) qz766) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474704048121631117148160) qz767) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 60 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q3 803784195 2097152 226375608064910080 72057594037927936 60 474704048121631117148160 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 474704048121631117148160 302231454903657293676544 26983801042 17179869184 2186600 2184466 (Ns60p1943 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p1945 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz190) Bool.false Ns60p1917 Ns60p1918 1827661101855340594251 Ns60p1919 25721094245 67108864 1098 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz190) (@HAdd.hAdd Real Real Real qz336 qz519 (Enclosure.sfrac Bool.true Ns60p1920 Ns60p1921)) Bool.false Ns60p1917 Ns60p1918 1827661101855340594251 Ns60p1919 Ns60p1922 (Ns60p1938 rfl rfl)) 

noncomputable def Ns60p1946 := Ns60p1916 24572 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 122 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 60535630 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 51 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 8925225 67108864) qz193 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz190) qz190 1) Bool.false 8388607 8388608 79558381 4581157240832 67108856 67108864 1166 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz190) qz190 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz190)) Bool.false 8388607 8388608 79558381 4581157240832 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz190) qz190) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz190)) Bool.false 8388607 8388608 79558381 4581157240832 8388607 8388608 79558381 4581157240832 (Ns60p1944 rfl rfl) rfl)) rfl) (Ns60p1945 rfl) RS061to078.d7 

noncomputable def Ns60p1947 := nat_lit 27419421935289686826903327597456168552693330107891939750500000000 

noncomputable def Ns60p1948 := nat_lit 647497977305001288168632283927940053158038706289062500000000 

noncomputable def Ns60p1949 := nat_lit 82256970809914450478133645527800649777973674246263241126500000000 

noncomputable def Ns60p1950 := BSN.cos_dyadic_bound_f 29950550 67108864 3 2 67108864 33554432 Ns60p1947 Ns60p103 Ns60p1948 Ns60p1949 Ns60p106 Ns60p1948 60535630 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 29950550) qz338 0 2 Ns60p1947 Ns60p103 Ns60p1948 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 29950550) (BSN.cosOddQ 67108864) 0 2 Ns60p1949 Ns60p106 Ns60p1948 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1951 := nat_lit 6421427530598811872901318001 

noncomputable def Ns60p1952 := BSN.sin_dyadic_bound_f 8951749 67108864 2 1 67108864 33554432 Ns60p1951 Ns60p115 Ns60p1951 Ns60p1951 Ns60p116 Ns60p1951 8925225 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 8951749) qz339 0 1 Ns60p1951 Ns60p115 Ns60p1951 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 8951749) (BSN.sinOddQ 67108864) 0 1 Ns60p1951 Ns60p116 Ns60p1951 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1953 := nat_lit 438997124711532417435143990757472201876954822326349138754988261121 

noncomputable def Ns60p1954 := nat_lit 165858397354771866526620176434898292008437256397382875036368641 

noncomputable def Ns60p1955 := nat_lit 1316659657339887708572378731919546809046847592466252650514892046081 

noncomputable def Ns60p1956 := BSN.cos_dyadic_bound_f 59905567 67108864 3 2 67108864 33554432 Ns60p1953 Ns60p103 Ns60p1954 Ns60p1955 Ns60p106 Ns60p1954 42100130 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 59905567) qz338 0 2 Ns60p1953 Ns60p103 Ns60p1954 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 59905567) (BSN.cosOddQ 67108864) 0 2 Ns60p1955 Ns60p106 Ns60p1954 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1957 := nat_lit 604041708018765296867342081394414120360195713759330266672566763201 

noncomputable def Ns60p1958 := nat_lit 313924104495540268651082469849531852575396782494842487943331521 

noncomputable def Ns60p1959 := nat_lit 1811497275847304810064724079243543297375436347713001115041813626561 

noncomputable def Ns60p1960 := BSN.cos_dyadic_bound_f 64878841 67108864 3 2 67108864 33554432 Ns60p1957 Ns60p103 Ns60p1958 Ns60p1959 Ns60p106 Ns60p1958 38115210 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 64878841) qz338 0 2 Ns60p1957 Ns60p103 Ns60p1958 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 64878841) (BSN.cosOddQ 67108864) 0 2 Ns60p1959 Ns60p106 Ns60p1958 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1961 := Ns60p1914 41831 BSN.abs_quadSignPos (BSN.cos_quad_nat0 0 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 42100130 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 38 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 38115210 67108864) qz193 rfl rfl (Ns60p1946 RS061to078.d9 RS061to078.d11 RS061to078.d13 RS061to078.d17 (Ns60p1950 rfl rfl) (Ns60p1952 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns60p1945 rfl) RS061to078.d19 RS061to078.d21 RS061to078.d23 RS061to078.d25 RS061to078.d17 (Ns60p1956 rfl rfl) (Ns60p1960 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns60p1962 := nat_lit 667045958187526551101953759884051159382217241863573852788622868736 

noncomputable def Ns60p1963 := nat_lit 382785314964767148698475515221729717003810835369789636656742656 

noncomputable def Ns60p1964 := nat_lit 2000372303932650119008464328621710018712644103919981979092555120896 

noncomputable def Ns60p1965 := BSN.cos_dyadic_bound_f 66507314 67108864 3 2 67108864 33554432 Ns60p1962 Ns60p103 Ns60p1963 Ns60p1964 Ns60p106 Ns60p1963 36763797 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 66507314) qz338 0 2 Ns60p1962 Ns60p103 Ns60p1963 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 66507314) (BSN.cosOddQ 67108864) 0 2 Ns60p1964 Ns60p106 Ns60p1963 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1966 := Ns60p1912 Bool.false 33461101 41831 Bool.true 66507314 3537118876014220 1 Bool.false 36763797 Bool.true Bool.false 18452343 49384 BSN.abs_quadSignNeg qz1024 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 36763797 67108864) qz193 rfl (Ns60p1961 rfl rfl) (Ns60p1945 rfl) RS061to078.d27 RS061to078.d29 RS061to078.d17 (Ns60p1965 rfl rfl) rfl 

noncomputable def Ns60p1967 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz190) qz190 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz190) qz190 6) 18452343 67108864 49384 67108864 18452343 67108864 49384 67108864 2476631553736704 18452343 33554432 6173 4194304 (Ns60p1966 rfl rfl rfl rfl) 

noncomputable def Ns60p1968 := @Enclosure.Real.IsNear.mulLit_ff qz1047 (Zeta.RiemannSiegel.correction qz192) 1629463 4194304 1 4194304 14455044069583 35184372088832 620058187104277 9607383069925310464 23553959474754923929 147573952589676412928 

noncomputable abbrev qz1052 := (@HPow.hPow Real Real Real qz326 qz191 qz8)

noncomputable def Ns60p1969 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz1052 1 1 0 1 1629463 4194304 1 4194304 1629463 4194304 1 4194304 

noncomputable def Ns60p1970 := @Enclosure.Real.IsNear.sqrt_image qz191 36825759887 838860800 27583 838860800 27790134 27790156 4194304 (@Enclosure.Real.IsNear.of_eq qz191 (@HMul.hMul Real Real Real qz5 qz190 qz3) Bool.false 36825759887 838860800 27583 838860800 (BSN.t_div_two_pi_mk qz190 275830 1000 qz193) (@Enclosure.Real.IsNear.mulLit_ff qz190 qz3 275830 1000 0 1 1335089 8388608 1 8388608 36825759887 838860800 27583 838860800 (Enclosure.Real.IsNear.const Bool.false 275830 1000) RS061to078.d32 rfl)) 

noncomputable abbrev qz830 := (Real.sqrt qz1046)

noncomputable abbrev qz525 := qz830

noncomputable abbrev qz194 := qz525

noncomputable def Ns60p1971 := @Enclosure.Real.IsNear.sqrt_image qz194 27790145 4194304 11 4194304 10796308 10796313 4194304 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 55580290 8388608 22 8388608 27790145 4194304 11 4194304 (Ns60p1970 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns60p1972 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz194) 21592621 8388608 5 8388608 1629462 1629464 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz194) Bool.false 21592621 8388608 5 8388608 21592621 8388608 5 8388608 (Ns60p1971 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns60p1973 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz194)) Bool.false 3258926 8388608 2 8388608 1629463 4194304 1 4194304 (Ns60p1972 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz195 := (Real.cos (@HMul.hMul Real Real Real qz323 qz320 qz518))

noncomputable abbrev qz526 := (@HSub.hSub Real Real Real qz647 (@HMul.hMul Real Real Real qz644 qz823 qz823) qz823)

noncomputable abbrev qz196 := (@HMul.hMul Real Real Real qz323 qz320 (@HSub.hSub Real Real Real qz327 qz526 qz344))

noncomputable def Ns60p1974 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz192) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz195) (Real.cos qz196)) Bool.false 14455044069583 

noncomputable def Ns60p1975 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz195) (Real.cos qz196) 11914817 8388608 297 

noncomputable abbrev qz1053 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz195))

noncomputable def Ns60p1976 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz195) (@Neg.neg Real Real.instNeg qz1053) Bool.true 11914817 8388608 297 8388608 (BSN.inv_eq_neg_inv_neg qz195) 

noncomputable def Ns60p1977 := @Enclosure.Real.IsNear.recentre' qz1053 Bool.false 11914817 8388608 297 8388608 11914817 8388608 

noncomputable def Ns60p1978 := @Enclosure.Real.IsNear.recentre' qz195 Bool.true 5905986 8388608 160208995 9162314481664 2952993 4194304 160208995 9162314481664 

noncomputable abbrev qz197 := (@HMul.hMul Real Real Real qz323 qz320 qz518)

noncomputable def Ns60p1979 := @Enclosure.Real.IsNear.cos_image qz197 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16489095) qz660) Bool.false 16489095 4194304 139 8388608 Bool.true 5905986 8388608 1 

noncomputable def Ns60p1980 := nat_lit 296846829522027245745270669 

noncomputable def Ns60p1981 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz192 884279719003555 140737488355328 1 500000000000000 2624321 4194304 11 4194304 2320633836455128461155 590295810358705651712 Ns60p1980 

noncomputable def Ns60p1982 := @Enclosure.Real.IsNear.subLit_ff_p qz194 qz1 27790145 4194304 11 4194304 6 1 0 1 2624321 2624321 4194304 11 

noncomputable def Ns60p1983 := @Ns60p1982 4194304 (@Enclosure.Real.IsNear.recentre' qz194 Bool.false 55580290 8388608 22 8388608 27790145 4194304 11 4194304 (Ns60p1970 rfl rfl rfl rfl rfl rfl) rfl) qz345 

noncomputable def Ns60p1984 := @Enclosure.Real.IsNear.recentre' qz197 Bool.false 2320633836455128461155 590295810358705651712 Ns60p1980 Ns60p1589 16489095 4194304 139 8388608 (@Ns60p1981 Ns60p1589 RS061to078.d31 (Ns60p1983 rfl rfl) rfl) 

noncomputable def Ns60p1985 := nat_lit 4959613876154743148587955308792774867601016026202112226572384943499171887254232990881 

noncomputable def Ns60p1986 := nat_lit 1147934966700010256875887901195643445595726012635655032518310456941799846621578401 

noncomputable def Ns60p1987 := nat_lit 14876545758530829425250114150575933315911856626581065369652118209583632062069455815841 

noncomputable def Ns60p1988 := BSN.cos_dyadic_bound_f 13567182301 17179869184 3 2 8388608 2186600 Ns60p1985 Ns60p1788 Ns60p1986 Ns60p1987 Ns60p1791 Ns60p1986 5905986 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 13567182301) qz769 0 2 Ns60p1985 Ns60p1788 Ns60p1986 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 13567182301) qz770 0 2 Ns60p1987 Ns60p1791 Ns60p1986 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p1989 := @Ns60p1979 1092233 (Ns60p1984 rfl) (Enclosure.sfrac_false_div 16489095 4194304) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16489095) qz660) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 477352790307485463347200) qz709) 226375608064910080 72057594037927936 Bool.false 5905986 8388608 0 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q2 16489095 4194304 226375608064910080 72057594037927936 0 477352790307485463347200 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 5905986 8388608 477352790307485463347200 604462909807314587353088 13567182301 17179869184 2186600 2184466 (Ns60p1988 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p1990 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz195) 2952993 4194304 160208995 9162314481664 5957260 5957557 4194304 (@Enclosure.Real.IsNear.neg qz195 Bool.true 2952993 4194304 160208995 9162314481664 (Ns60p1978 (Ns60p1989 rfl rfl) rfl)) 

noncomputable def Ns60p1991 := Ns60p1976 (@Enclosure.Real.IsNear.neg qz1053 Bool.false 11914817 8388608 297 8388608 (@Ns60p1977 297 8388608 (Ns60p1990 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p1992 := @Enclosure.Real.IsNear.recentre' (Real.cos qz196) Bool.true 1213199 4194304 

noncomputable def Ns60p1993 := @Enclosure.Real.IsNear.cos_image qz196 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 15638367)) qz337) Bool.true 15638367 8388608 

noncomputable def Ns60p1994 := nat_lit 4615631505710234585610254045 

noncomputable def Ns60p1995 := nat_lit 2803111846594800116279634441932457 

noncomputable def Ns60p1996 := @Enclosure.Real.IsNear.recentre' qz196 Bool.true Ns60p1994 Ns60p327 Ns60p1995 

noncomputable abbrev qz198 := (@HSub.hSub Real Real Real qz327 qz526 qz344)

noncomputable def Ns60p1997 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz198 884279719003555 140737488355328 1 500000000000000 5219650984319 

noncomputable abbrev qz199 := qz526

noncomputable def Ns60p1998 := @Enclosure.Real.IsNear.subLit_tf qz199 qz23 4120139356543 17592186044416 103872527 17592186044416 1 16 

noncomputable abbrev qz527 := (@HMul.hMul Real Real Real qz644 qz823 qz823)

noncomputable abbrev qz200 := qz527

noncomputable def Ns60p1999 := @Enclosure.Real.IsNear.subLit_ff_n qz200 qz192 6887060711041 17592186044416 57735183 17592186044416 2624321 4194304 11 4194304 

noncomputable def Ns60p2000 := @Enclosure.Real.IsNear.mulLit_ff qz192 qz192 2624321 4194304 11 4194304 2624321 4194304 11 4194304 6887060711041 17592186044416 

noncomputable def Ns60p2001 := nat_lit 29479821903417830820952287949221175603095156318325778153122393097919345852420508930789101441 

noncomputable def Ns60p2002 := nat_lit 213942374106962307520519885642574336319189989180249356774628587822838894044630124351361 

noncomputable def Ns60p2003 := nat_lit 177992097257668426069166450727152337814549272261362297225335008728999182823276880743924518785 

noncomputable def Ns60p2004 := BSN.cos_dyadic_bound_t 15638367 8388608 4 3 4194304 1092233 Ns60p2001 Ns60p274 Ns60p2002 Ns60p2003 Ns60p277 Ns60p2002 1213199 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 15638367) (BSN.cosEvenQ 8388608) 0 3 Ns60p2001 Ns60p274 Ns60p2002 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 15638367) (BSN.cosOddQ 8388608) 0 3 Ns60p2003 Ns60p277 Ns60p2002 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2005 := @Ns60p1992 350257537 9162314481664 1213199 4194304 350257537 9162314481664 (@Ns60p1993 313 8388608 Bool.true 1213199 4194304 1 1092233 (@Ns60p1996 Ns60p1701 15638367 8388608 313 8388608 (@Ns60p1997 17592186044416 103872527 17592186044416 Ns60p1994 Ns60p327 Ns60p1995 Ns60p1701 RS061to078.d31 (@Ns60p1998 0 1 83514415749104 5219650984319 17592186044416 103872527 17592186044416 (@Ns60p1999 17281116983705731072 4120139356543 17592186044416 103872527 17592186044416 (@Ns60p2000 57735183 17592186044416 (Ns60p1983 rfl rfl) (Ns60p1983 rfl rfl) rfl) (Ns60p1983 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 15638367 8388608) (BSN.cos_neg_of_bound 15638367 8388608 Bool.true 1213199 4194304 1 1092233 (Ns60p2004 rfl rfl)) rfl rfl) 

noncomputable def Ns60p2006 := @Ns60p1968 2967987016324789553 117911588119151453929472 (Ns60p1969 qz25 (@Enclosure.Real.IsNear.of_eq qz1052 (@Inv.inv Real Real.instInv (Real.sqrt qz194)) Bool.false 1629463 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz191 (BSN.t_div_two_pi_nonneg qz190 275830 1000 qz193)) Ns60p1973) rfl) (@Ns60p1974 35184372088832 620058187104277 9607383069925310464 (BSN.correction_mk qz192 (BSN.cos_two_pi_p_ne_zero_mk qz190 275830 1000 6 qz193 rfl rfl (@BSN.floor_sqrt_eq_dec qz190 275830 1000 6 qz193 rfl rfl rfl))) (@Ns60p1975 8388608 1213199 4194304 350257537 9162314481664 14455044069583 35184372088832 620058187104277 9607383069925310464 Ns60p1991 (Ns60p2005 rfl) rfl)) 

noncomputable def Ns60p2007 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz190) (hardyZApproximantRS₀ qz190) Bool.false 57600303278089392743 147573952589676412928 176505297010908378417 117911588119151453929472 (@Eq.refl Real (hardyZApproximantRS₀ qz190)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz190) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz190) qz190 6) (@HMul.hMul Real Real Real qz5 qz1047 (Zeta.RiemannSiegel.correction qz192))) Bool.false 57600303278089392743 147573952589676412928 176505297010908378417 117911588119151453929472 (BSN.hardyZApproximantRS₀_eq qz190 6 (@BSN.floor_sqrt_eq_dec qz190 275830 1000 6 qz193 rfl rfl rfl)) (@Ns60p1911 57600303278089392743 147573952589676412928 176505297010908378417 117911588119151453929472 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz190) qz190 6) (@HAdd.hAdd Real Real Real qz336 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz190) qz190 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz190) qz190 6)) Bool.false 18452343 33554432 6173 4194304 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz190) qz190 6) (Ns60p1967 (Ns60p1966 rfl rfl rfl rfl) rfl rfl)) (Ns60p2006 rfl) rfl rfl)) 

theorem RS061to078.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz190) Bool.false 57600303278089392743 147573952589676412928 176505297010908378417 117911588119151453929472 := Ns60p2007 

noncomputable def Ns60p2008 := nat_lit 13941164302200817565302784 

noncomputable abbrev qz831 := (Enclosure.sfrac Bool.false 277490 1000)

noncomputable abbrev qz528 := qz831

noncomputable abbrev qz201 := qz528

noncomputable abbrev qz1054 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 277490 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz832 := qz1054

noncomputable abbrev qz529 := qz832

noncomputable abbrev qz202 := qz529

noncomputable abbrev qz833 := (@HSub.hSub Real Real Real qz920 (Real.sqrt qz1054) qz914)

noncomputable abbrev qz530 := qz833

noncomputable abbrev qz203 := qz530

noncomputable abbrev qz1055 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz326 qz202 qz8))

noncomputable def Ns60p2009 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz201) qz201 6) (@HMul.hMul Real Real Real qz5 qz1055 (Zeta.RiemannSiegel.correction qz203)) 21446113 16777216 3105 2097152 94075314297472665 576460752303423488 2375803584463944266125 Ns60p1227 Ns60p2008 

noncomputable def Ns60p2010 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz201) qz201 Real.cos BSN.quadSignNeg 5 6 277490 1000 70 67108864 33554432 1125899906842624 Bool.false 25931915124 1104 120242927 63 27397080 8 

noncomputable def Ns60p2011 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz201) qz201 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 277490 1000 1 38 67108864 33554432 1125899906842624 Bool.false 25931915124 1104 

noncomputable def Ns60p2012 := Ns60p2011 93032624 62 33554424 8 108007536 62 30011992 8 Bool.false 7517556 24720 Bool.false 10877933 Bool.true 33350472 3537118876014220 1 Bool.false 10830360 Bool.true Bool.false 58991080 Bool.true Bool.true 24279232 

noncomputable def Ns60p2013 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz201) qz201 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 277490 1000 123 51 67108864 33554432 1125899906842624 Bool.false 25931915124 1104 

noncomputable def Ns60p2014 := Ns60p2013 46516304 62 47453136 16 73726608 62 38745320 8 Bool.true 67108856 1174 Bool.false 58140007 Bool.false 97386459 3537118876014220 1 Bool.false 51135113 Bool.false Bool.false 66629267 Bool.false Bool.false 7517556 

noncomputable def Ns60p2015 := nat_lit 1430129073027532933924902288166196487431804677201 

noncomputable def Ns60p2016 := nat_lit 3701012324188016649299286812972103429311692800 

noncomputable def Ns60p2017 := nat_lit 789735196899033864355952000000000 

noncomputable def Ns60p2018 := nat_lit 1314863710955200079872642082880000000 

noncomputable def Ns60p2019 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz201 277490 1000 308003800400 16000000 554980 4000 2000 Ns60p2017 Ns60p2018 (@Eq.refl Real qz201) rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns60p2020 := nat_lit 457641303368810538855968732213182875978177496704320000000 

noncomputable abbrev qz1056 := (Real.log (Enclosure.sfrac Bool.false 308003800400 16000000))

noncomputable abbrev qz1057 := (@HSub.hSub Real Real Real qz11 qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 554980))))

noncomputable abbrev qz834 := (@HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 277490 4000) qz1056) (@HMul.hMul Real Real Real qz5 qz12 qz1057))

noncomputable abbrev qz1058 := (Enclosure.sfrac Bool.false 277490 2000)

noncomputable abbrev qz531 := (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 qz834 qz1058) (@HMul.hMul Real Real Real qz5 qz1058 (Real.log Real.pi)))

noncomputable def Ns60p2021 := @Enclosure.Real.IsNear.addLit_ft_p qz531 (Enclosure.sfrac Bool.true Ns60p2017 Ns60p2018) 348052814056734563189 900719925474099200 1838506265285919782953 Ns60p1919 Ns60p2017 Ns60p2018 0 1 Ns60p2020 

noncomputable def Ns60p2022 := nat_lit 2335742896335068808515000729600 

noncomputable abbrev qz532 := (@HSub.hSub Real Real Real qz11 qz834 qz1058)

noncomputable def Ns60p2023 := @Enclosure.Real.IsNear.subLit_ff_p qz532 (@HMul.hMul Real Real Real qz5 qz1058 (Real.log Real.pi)) 491110149404407864181 900719925474099200 446078178046480111 54611650000000000000000 1065860206989 6710886400 27749 3355443200 Ns60p2022 348052814056734563189 900719925474099200 

noncomputable abbrev qz533 := qz834

noncomputable def Ns60p2024 := @Enclosure.Real.IsNear.subLit_ff_p qz533 qz1058 123216107092862351537 180143985094819840 446078178046480111 54611650000000000000000 277490 2000 0 1 196444059761763145672400 491110149404407864181 900719925474099200 446078178046480111 54611650000000000000000 

noncomputable def Ns60p2025 := nat_lit 277458006994729007778926603247026176 

noncomputable def Ns60p2026 := nat_lit 11926390095072253265838080 

noncomputable def Ns60p2027 := nat_lit 3606733204860656086665325080850543435552216545210886287790080000000000000 

noncomputable def Ns60p2028 := nat_lit 7808588698154116332332507673168035725365348498259874082816000000000000 

noncomputable def Ns60p2029 := nat_lit 139535341661229987271570464629852668465363454791741440000000000000 

noncomputable def Ns60p2030 := BSN.log_dyadic_bound 45859800400 570147800400 4 3 Ns60p2027 33554432 8737864 Ns60p2028 Ns60p2029 5409583 616007600800 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 45859800400) (BSN.artanhQ 570147800400) 0 3 Ns60p2028 Ns60p2027 Ns60p2029 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz835 := qz1056

noncomputable def Ns60p2031 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 277490 4000) qz835 277490 4000 0 1 22214632658422465 2251799813685248 62500007645631 546116500000000000000 123286768327712996257 180143985094819840 1734312712158614619 218446600000000000000000 (Enclosure.Real.IsNear.const Bool.false 277490 4000) (BSN.isNear_log_sfrac 308003800400 16000000 22214632658422465 2251799813685248 62500007645631 546116500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 308003800400) qz650)) Bool.false Ns60p2026 Ns60p84 1000000122330096 8737864000000000000000 22214632658422465 2251799813685248 62500007645631 546116500000000000000 (BSN.log_rat_reduce_isNear 308003800400 16000000 14 616007600800 524288000000 5409583 33554432 24973259072661432 36028797018963968 8737864 1000000000000000 rfl rfl rfl rfl (Ns60p2030 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p2032 := BSN.arctan_dyadic_bound_f 1000 554980 1 0 4194304 1092233 0 1 1 0 1 1 7557 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 554980) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 554980) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz1059 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 554980)))

noncomputable abbrev qz836 := qz1059

noncomputable abbrev qz534 := qz836

noncomputable def Ns60p2033 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz534 884279719003555 562949953421312 1 2000000000000000 7557 4194304 1 1092233 3704683749737481895936 883265435633059 562949953421312 2000000001092233 2184466000000000000000 qz15 (Ns60p2032 rfl) rfl rfl 

noncomputable abbrev qz837 := (@HMul.hMul Real Real Real qz5 qz12 qz1057)

noncomputable abbrev qz535 := qz837

noncomputable abbrev qz838 := qz1057

noncomputable abbrev qz536 := qz838

noncomputable abbrev qz839 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 277490 4000) qz1056)

noncomputable def Ns60p2034 := @Enclosure.Real.IsNear.subLit_ff_p qz839 qz535 123286768327712996257 180143985094819840 1734312712158614619 218446600000000000000000 883265435633059 2251799813685248 2000000001092233 8737864000000000000000 Ns60p2025 123216107092862351537 180143985094819840 446078178046480111 54611650000000000000000 (Ns60p2031 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz12 qz536 1 4 0 1 883265435633059 562949953421312 2000000001092233 2184466000000000000000 883265435633059 2251799813685248 2000000001092233 8737864000000000000000 qz335 Ns60p2033 rfl) 

noncomputable def Ns60p2035 := @Ns60p2021 Ns60p2015 Ns60p2016 1838506265285919782953 Ns60p1919 (@Ns60p2023 1838506265285919782953 Ns60p1919 (Ns60p2024 (Ns60p2034 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 277490 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz1058 (Real.log Real.pi) 277490 2000 0 1 38410761 33554432 1 16777216 1065860206989 6710886400 27749 3355443200 (Enclosure.Real.IsNear.const Bool.false 277490 2000) RS061to078.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns60p2017 Ns60p2018) 

noncomputable def Ns60p2036 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz201) Bool.false Ns60p2015 Ns60p2016 1838506265285919782953 Ns60p1919 1620744695 4194304 139 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz201) (@HAdd.hAdd Real Real Real qz336 qz531 (Enclosure.sfrac Bool.true Ns60p2017 Ns60p2018)) Bool.false Ns60p2015 Ns60p2016 1838506265285919782953 Ns60p1919 Ns60p2019 (Ns60p2035 rfl rfl)) 

noncomputable def Ns60p2037 := nat_lit 139899928928419527163582191805076045128276255955854170302779247981235382025042022891520 

noncomputable def Ns60p2038 := nat_lit 280909722965026455628389490157292485499119153332074708080910913914012134822731841536 

noncomputable def Ns60p2039 := nat_lit 365949769546774433071697871743515930359439239350413753646576555614041409466349446496256 

noncomputable def Ns60p2040 := BSN.sin_dyadic_bound_f 26981795504 17179869184 3 2 8388608 2186600 Ns60p2037 Ns60p94 Ns60p2038 Ns60p2039 Ns60p97 Ns60p2038 8388607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26981795504) qz655 0 2 Ns60p2037 Ns60p94 Ns60p2038 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26981795504) qz656 0 2 Ns60p2039 Ns60p97 Ns60p2038 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2041 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz201) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1620744695) qz660) Bool.false 1620744695 4194304 139 8388608 Bool.true 8388607 8388608 1 1092233 (Ns60p2036 rfl) (Enclosure.sfrac_false_div 1620744695 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1620744695) qz660) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949337532644933123440640) qz709) 226375608064910080 72057594037927936 Bool.false 8388607 8388608 61 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q1 1620744695 4194304 226375608064910080 72057594037927936 61 949337532644933123440640 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388607 8388608 949337532644933123440640 604462909807314587353088 26981795504 17179869184 2186600 2184466 (Ns60p2040 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p2042 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz201) Bool.false Ns60p2015 Ns60p2016 1838506265285919782953 Ns60p1919 25931915124 67108864 1104 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz201) (@HAdd.hAdd Real Real Real qz336 qz531 (Enclosure.sfrac Bool.true Ns60p2017 Ns60p2018)) Bool.false Ns60p2015 Ns60p2016 1838506265285919782953 Ns60p1919 Ns60p2019 (Ns60p2035 rfl rfl)) 

noncomputable def Ns60p2043 := Ns60p2014 24720 BSN.abs_quadSignPos (BSN.cos_quad_nat3 123 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 51135113 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 51 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 66629267 67108864) (@Eq.refl Real qz201) rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz201) qz201 1) Bool.true 8388607 8388608 160208995 9162314481664 67108856 67108864 1174 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz201) qz201 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz201)) Bool.true 8388607 8388608 160208995 9162314481664 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz201) qz201) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz201)) Bool.true 8388607 8388608 160208995 9162314481664 8388607 8388608 160208995 9162314481664 (Ns60p2041 rfl rfl) rfl)) rfl) (Ns60p2042 rfl) RS061to078.d7 

noncomputable def Ns60p2044 := nat_lit 700942759062201461098329601223838800502238694160051244280307278785 

noncomputable def Ns60p2045 := nat_lit 130557142999017285147223016791063267923727947144558097525924801 

noncomputable def Ns60p2046 := nat_lit 1835591085979005417748243927844773232214939115647614450481000899521 

noncomputable def Ns60p2047 := BSN.sin_dyadic_bound_f 58140007 67108864 3 2 67108864 33554432 Ns60p2044 Ns60p119 Ns60p2045 Ns60p2046 Ns60p122 Ns60p2045 51135113 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 58140007) qz339 0 2 Ns60p2044 Ns60p119 Ns60p2045 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 58140007) (BSN.sinOddQ 67108864) 0 2 Ns60p2046 Ns60p122 Ns60p2045 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2048 := nat_lit 1922954796525003331485115753981121002651088072713358944364483479414851800968477552980602549430955171281 

noncomputable def Ns60p2049 := nat_lit 727751150293797323530213276930175716798433960132910241707492154202996837746672237003503401328081 

noncomputable def Ns60p2050 := nat_lit 9606067216270743801997572684670760354035888550192511530469661787627985597364180812308787998805356338641 

noncomputable def Ns60p2051 := BSN.sin_dyadic_bound_f 97386459 67108864 4 3 67108864 33554432 Ns60p2048 Ns60p109 Ns60p2049 Ns60p2050 Ns60p112 Ns60p2049 66629267 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 97386459) qz339 0 3 Ns60p2048 Ns60p109 Ns60p2049 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 97386459) (BSN.sinOddQ 67108864) 0 3 Ns60p2050 Ns60p112 Ns60p2049 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2052 := nat_lit 14001853140909118206876495121 

noncomputable def Ns60p2053 := BSN.sin_dyadic_bound_f 10877933 67108864 2 1 67108864 33554432 Ns60p2052 Ns60p115 Ns60p2052 Ns60p2052 Ns60p116 Ns60p2052 10830360 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 10877933) qz339 0 1 Ns60p2052 Ns60p115 Ns60p2052 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 10877933) (BSN.sinOddQ 67108864) 0 1 Ns60p2052 Ns60p116 Ns60p2052 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2054 := nat_lit 42155334232686869240091611173822025631257905199464358877767663616 

noncomputable def Ns60p2055 := nat_lit 1530438484546216018077989552059865237009517320779930414350336 

noncomputable def Ns60p2056 := nat_lit 126462941821091515288238677542361957163299696563751516772474290176 

noncomputable def Ns60p2057 := BSN.cos_dyadic_bound_f 33350472 67108864 3 2 67108864 33554432 Ns60p2054 Ns60p103 Ns60p2055 Ns60p2056 Ns60p106 Ns60p2055 58991080 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 33350472) qz338 0 2 Ns60p2054 Ns60p103 Ns60p2055 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 33350472) (BSN.cosOddQ 67108864) 0 2 Ns60p2056 Ns60p106 Ns60p2055 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2058 := Ns60p2012 42082 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 1 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 10830360 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 38 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 58991080 67108864) (@Eq.refl Real qz201) rfl rfl (Ns60p2043 RS061to078.d9 RS061to078.d11 RS061to078.d13 RS061to078.d17 (Ns60p2047 rfl rfl) (Ns60p2051 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns60p2042 rfl) RS061to078.d19 RS061to078.d21 RS061to078.d23 RS061to078.d25 RS061to078.d17 (Ns60p2053 rfl rfl) (Ns60p2057 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns60p2059 := nat_lit 318511168582517085656366440504215447752624513879707296494249738496 

noncomputable def Ns60p2060 := nat_lit 87327995335304092960353377495193944153186618858547898235126016 

noncomputable def Ns60p2061 := nat_lit 955358849756880648783178614757655955369567168401404793686278963456 

noncomputable def Ns60p2062 := BSN.cos_dyadic_bound_f 55289694 67108864 3 2 67108864 33554432 Ns60p2059 Ns60p103 Ns60p2060 Ns60p2061 Ns60p106 Ns60p2060 45592336 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 55289694) qz338 0 2 Ns60p2059 Ns60p103 Ns60p2060 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 55289694) (BSN.cosOddQ 67108864) 0 2 Ns60p2061 Ns60p106 Ns60p2060 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2063 := Ns60p2010 Bool.true 24279232 42082 Bool.true 55289694 3537118876014220 1 Bool.false 45592336 Bool.true Bool.true 42892226 49680 BSN.abs_quadSignNeg qz1024 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 45592336 67108864) (@Eq.refl Real qz201) rfl (Ns60p2058 rfl rfl) (Ns60p2042 rfl) RS061to078.d27 RS061to078.d29 RS061to078.d17 (Ns60p2062 rfl rfl) rfl 

noncomputable def Ns60p2064 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz201) qz201 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz201) qz201 6) 42892226 67108864 49680 67108864 42892226 67108864 49680 67108864 5756897122582528 21446113 16777216 3105 2097152 (Ns60p2063 rfl rfl rfl rfl) 

noncomputable def Ns60p2065 := @Enclosure.Real.IsNear.mulLit_ff qz1055 (Zeta.RiemannSiegel.correction qz203) 406755 1048576 1 4194304 231282502483 549755813888 1455248533519137 19214766139850620928 94075314297472665 576460752303423488 

noncomputable abbrev qz1060 := (@HPow.hPow Real Real Real qz326 qz202 qz8)

noncomputable def Ns60p2066 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz1060 1 1 0 1 406755 1048576 1 4194304 406755 1048576 1 4194304 

noncomputable def Ns60p2067 := @Enclosure.Real.IsNear.sqrt_image qz202 37047384661 838860800 27749 838860800 27873632 27873654 4194304 (@Enclosure.Real.IsNear.of_eq qz202 (@HMul.hMul Real Real Real qz5 qz201 qz3) Bool.false 37047384661 838860800 27749 838860800 (BSN.t_div_two_pi_mk qz201 277490 1000 (@Eq.refl Real qz201)) (@Enclosure.Real.IsNear.mulLit_ff qz201 qz3 277490 1000 0 1 1335089 8388608 1 8388608 37047384661 838860800 27749 838860800 (Enclosure.Real.IsNear.const Bool.false 277490 1000) RS061to078.d32 rfl)) 

noncomputable abbrev qz840 := (Real.sqrt qz1054)

noncomputable abbrev qz537 := qz840

noncomputable abbrev qz204 := qz537

noncomputable def Ns60p2068 := @Enclosure.Real.IsNear.sqrt_image qz204 27873643 4194304 11 4194304 10812515 10812520 4194304 (@Enclosure.Real.IsNear.recentre' qz204 Bool.false 55747286 8388608 22 8388608 27873643 4194304 11 4194304 (Ns60p2067 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns60p2069 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz204) 21625035 8388608 5 8388608 1627019 1627021 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz204) Bool.false 21625035 8388608 5 8388608 21625035 8388608 5 8388608 (Ns60p2068 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns60p2070 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz204)) Bool.false 3254040 8388608 2 8388608 406755 1048576 1 4194304 (Ns60p2069 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz205 := (Real.cos (@HMul.hMul Real Real Real qz323 qz320 qz530))

noncomputable abbrev qz538 := (@HSub.hSub Real Real Real qz647 (@HMul.hMul Real Real Real qz644 qz833 qz833) qz833)

noncomputable abbrev qz206 := (@HMul.hMul Real Real Real qz323 qz320 (@HSub.hSub Real Real Real qz327 qz538 qz344))

noncomputable def Ns60p2071 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz203) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz205) (Real.cos qz206)) Bool.false 231282502483 

noncomputable def Ns60p2072 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz205) (Real.cos qz206) 13752899 8388608 395 

noncomputable abbrev qz1061 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz205))

noncomputable def Ns60p2073 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz205) (@Neg.neg Real Real.instNeg qz1061) Bool.true 13752899 8388608 395 8388608 (BSN.inv_eq_neg_inv_neg qz205) 

noncomputable def Ns60p2074 := @Enclosure.Real.IsNear.recentre' qz1061 Bool.false 13752899 8388608 395 8388608 13752899 8388608 

noncomputable def Ns60p2075 := @Enclosure.Real.IsNear.recentre' qz205 Bool.true 5116648 8388608 160208995 9162314481664 639581 1048576 160208995 9162314481664 

noncomputable abbrev qz207 := (@HMul.hMul Real Real Real qz323 qz320 qz530)

noncomputable def Ns60p2076 := @Enclosure.Real.IsNear.cos_image qz207 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 34027457) qz337) Bool.false 34027457 8388608 139 8388608 Bool.true 5116648 8388608 1 

noncomputable def Ns60p2077 := nat_lit 59369365904548897620766697 

noncomputable def Ns60p2078 := nat_lit 3602879701896396800000000000000 

noncomputable def Ns60p2079 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz203 884279719003555 140737488355328 1 500000000000000 2707819 4194304 11 4194304 2394469424432487296545 590295810358705651712 Ns60p2077 

noncomputable def Ns60p2080 := @Enclosure.Real.IsNear.subLit_ff_p qz204 qz1 27873643 4194304 11 4194304 6 1 0 1 2707819 2707819 4194304 11 

noncomputable def Ns60p2081 := @Ns60p2080 4194304 (@Enclosure.Real.IsNear.recentre' qz204 Bool.false 55747286 8388608 22 8388608 27873643 4194304 11 4194304 (Ns60p2067 rfl rfl rfl rfl rfl rfl) rfl) qz345 

noncomputable def Ns60p2082 := @Enclosure.Real.IsNear.recentre' qz207 Bool.false 2394469424432487296545 590295810358705651712 Ns60p2077 Ns60p2078 34027457 8388608 139 8388608 (@Ns60p2079 Ns60p2078 RS061to078.d31 (Ns60p2081 rfl rfl) rfl) 

noncomputable def Ns60p2083 := nat_lit 8931959400982772501176699959921525654308474679386061966782009920690138080914692981921 

noncomputable def Ns60p2084 := nat_lit 3721809102471351883793707707393874515993679242800931695613720078613265950872519841 

noncomputable def Ns60p2085 := nat_lit 26788434584743374799762512464349789213893436679672584036954802321913187710842333906081 

noncomputable def Ns60p2086 := BSN.cos_dyadic_bound_f 15716081117 17179869184 3 2 8388608 2186600 Ns60p2083 Ns60p1788 Ns60p2084 Ns60p2085 Ns60p1791 Ns60p2084 5116648 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 15716081117) qz769 0 2 Ns60p2083 Ns60p1788 Ns60p2084 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 15716081117) qz770 0 2 Ns60p2085 Ns60p1791 Ns60p2084 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2087 := @Ns60p2076 1092233 (Ns60p2082 rfl) (Enclosure.sfrac_false_div 34027457 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 34027457) qz337) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1105920891661759989940224) qz657) 226375608064910080 72057594037927936 Bool.false 5116648 8388608 0 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q2 34027457 8388608 226375608064910080 72057594037927936 0 1105920891661759989940224 Ns60p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 5116648 8388608 1105920891661759989940224 Ns60p84 15716081117 17179869184 2186600 2184466 (Ns60p2086 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p2088 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz205) 639581 1048576 160208995 9162314481664 6876252 6876647 4194304 (@Enclosure.Real.IsNear.neg qz205 Bool.true 639581 1048576 160208995 9162314481664 (Ns60p2075 (Ns60p2087 rfl rfl) rfl)) 

noncomputable def Ns60p2089 := Ns60p2073 (@Enclosure.Real.IsNear.neg qz1061 Bool.false 13752899 8388608 395 8388608 (@Ns60p2074 395 8388608 (Ns60p2088 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p2090 := @Enclosure.Real.IsNear.recentre' (Real.cos qz206) Bool.true 1076288 4194304 

noncomputable def Ns60p2091 := @Enclosure.Real.IsNear.cos_image qz206 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 15353721)) qz337) Bool.true 15353721 8388608 

noncomputable def Ns60p2092 := nat_lit 4531618715628428517785438005 

noncomputable def Ns60p2093 := nat_lit 2852684079733079925666482126570733 

noncomputable def Ns60p2094 := @Enclosure.Real.IsNear.recentre' qz206 Bool.true Ns60p2092 Ns60p327 Ns60p2093 

noncomputable abbrev qz208 := (@HSub.hSub Real Real Real qz327 qz538 qz344)

noncomputable def Ns60p2095 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz208 884279719003555 140737488355328 1 500000000000000 5124643953991 

noncomputable abbrev qz209 := qz538

noncomputable def Ns60p2096 := @Enclosure.Real.IsNear.subLit_tf qz209 qz23 4025132326215 17592186044416 105709483 17592186044416 1 16 

noncomputable abbrev qz539 := (@HMul.hMul Real Real Real qz644 qz833 qz833)

noncomputable abbrev qz210 := qz539

noncomputable def Ns60p2097 := @Enclosure.Real.IsNear.subLit_ff_n qz210 qz203 7332283736761 17592186044416 59572139 17592186044416 2707819 4194304 11 4194304 

noncomputable def Ns60p2098 := @Enclosure.Real.IsNear.mulLit_ff qz203 qz203 2707819 4194304 11 4194304 2707819 4194304 11 4194304 7332283736761 17592186044416 

noncomputable def Ns60p2099 := nat_lit 27377496173686998362491383788944777534393473041712947750193229392795794714336836635020210721 

noncomputable def Ns60p2100 := nat_lit 171618354970541378493687082722785437986712213734974236215757836396279418608008325739041 

noncomputable def Ns60p2101 := nat_lit 165354516345162348497418977387160770767411402793515592526198467749743978017534699002637824545 

noncomputable def Ns60p2102 := BSN.cos_dyadic_bound_t 15353721 8388608 4 3 4194304 1092233 Ns60p2099 Ns60p274 Ns60p2100 Ns60p2101 Ns60p277 Ns60p2100 1076288 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 15353721) (BSN.cosEvenQ 8388608) 0 3 Ns60p2099 Ns60p274 Ns60p2100 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 15353721) (BSN.cosOddQ 8388608) 0 3 Ns60p2101 Ns60p277 Ns60p2100 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2103 := @Ns60p2090 177859351 4581157240832 16817 65536 177859351 4581157240832 (@Ns60p2091 159 4194304 Bool.true 1076288 4194304 1 1092233 (@Ns60p2094 Ns60p1701 15353721 8388608 159 4194304 (@Ns60p2095 17592186044416 105709483 17592186044416 Ns60p2092 Ns60p327 Ns60p2093 Ns60p1701 RS061to078.d31 (@Ns60p2096 0 1 81994303263856 5124643953991 17592186044416 105709483 17592186044416 (@Ns60p2097 16882628616372879360 4025132326215 17592186044416 105709483 17592186044416 (@Ns60p2098 59572139 17592186044416 (Ns60p2081 rfl rfl) (Ns60p2081 rfl rfl) rfl) (Ns60p2081 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 15353721 8388608) (BSN.cos_neg_of_bound 15353721 8388608 Bool.true 1076288 4194304 1 1092233 (Ns60p2102 rfl rfl)) rfl rfl) 

noncomputable def Ns60p2104 := @Ns60p2065 2375803584463944266125 Ns60p1227 (Ns60p2066 qz25 (@Enclosure.Real.IsNear.of_eq qz1060 (@Inv.inv Real Real.instInv (Real.sqrt qz204)) Bool.false 406755 1048576 1 4194304 (BSN.rpow_neg_quarter_mk qz202 (BSN.t_div_two_pi_nonneg qz201 277490 1000 (@Eq.refl Real qz201))) Ns60p2070) rfl) (@Ns60p2071 549755813888 1455248533519137 19214766139850620928 (BSN.correction_mk qz203 (BSN.cos_two_pi_p_ne_zero_mk qz201 277490 1000 6 (@Eq.refl Real qz201) rfl rfl (@BSN.floor_sqrt_eq_dec qz201 277490 1000 6 (@Eq.refl Real qz201) rfl rfl rfl))) (@Ns60p2072 8388608 16817 65536 177859351 4581157240832 231282502483 549755813888 1455248533519137 19214766139850620928 Ns60p2089 (Ns60p2103 rfl) rfl)) 

noncomputable def Ns60p2105 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz201) (hardyZApproximantRS₀ qz201) Bool.true 830958145988036249 576460752303423488 121699501312936300229005 Ns60p1227 (@Eq.refl Real (hardyZApproximantRS₀ qz201)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz201) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz201) qz201 6) (@HMul.hMul Real Real Real qz5 qz1055 (Zeta.RiemannSiegel.correction qz203))) Bool.true 830958145988036249 576460752303423488 121699501312936300229005 Ns60p1227 (BSN.hardyZApproximantRS₀_eq qz201 6 (@BSN.floor_sqrt_eq_dec qz201 277490 1000 6 (@Eq.refl Real qz201) rfl rfl rfl)) (@Ns60p2009 830958145988036249 576460752303423488 121699501312936300229005 Ns60p1227 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz201) qz201 6) (@HAdd.hAdd Real Real Real qz336 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz201) qz201 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz201) qz201 6)) Bool.true 21446113 16777216 3105 2097152 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz201) qz201 6) (Ns60p2064 (Ns60p2063 rfl rfl rfl rfl) rfl rfl)) (Ns60p2104 rfl) rfl rfl)) 

theorem RS061to078.d60 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz201) Bool.true 830958145988036249 576460752303423488 121699501312936300229005 Ns60p1227 := Ns60p2105 

noncomputable def Ns60p2106 := nat_lit 315253348060738555939389440 

noncomputable abbrev qz841 := (Enclosure.sfrac Bool.false 279148 1000)

noncomputable abbrev qz540 := qz841

noncomputable abbrev qz211 := qz540

noncomputable abbrev qz1062 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 279148 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz842 := qz1062

noncomputable abbrev qz541 := qz842

noncomputable abbrev qz212 := qz541

noncomputable abbrev qz843 := (@HSub.hSub Real Real Real qz920 (Real.sqrt qz1062) qz914)

noncomputable abbrev qz542 := qz843

noncomputable abbrev qz213 := qz542

noncomputable abbrev qz1063 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz326 qz212 qz8))

noncomputable def Ns60p2107 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz211) qz211 6) (@HMul.hMul Real Real Real qz5 qz1063 (Zeta.RiemannSiegel.correction qz213)) 14160961 33554432 49979 33554432 6174859367276001441 36893488147419103232 1455427472370095190047 Ns60p1233 Ns60p2106 

noncomputable def Ns60p2108 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz211) qz211 Real.cos BSN.quadSignNeg 5 6 279148 1000 70 67108864 33554432 1125899906842624 Bool.false 26142814535 1111 120242927 63 27397080 8 

noncomputable def Ns60p2109 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz211) qz211 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 279148 1000 1 38 67108864 33554432 1125899906842624 Bool.false 26142814535 1111 

noncomputable def Ns60p2110 := Ns60p2109 93032624 62 33554424 8 108007536 62 30011992 8 Bool.false 94290910 24869 Bool.false 67529253 Bool.true 1527555 3537118876014220 1 Bool.false 56696189 Bool.true Bool.false 67091479 Bool.true Bool.false 35938605 

noncomputable def Ns60p2111 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz211) qz211 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 279148 1000 124 52 67108864 33554432 1125899906842624 Bool.false 26142814535 1111 

noncomputable def Ns60p2112 := Ns60p2111 46516304 62 47453136 16 73726608 62 38745320 8 Bool.false 67108832 1182 Bool.false 86501029 Bool.false 80632797 3537118876014220 1 Bool.false 18663944 Bool.false Bool.false 24222171 Bool.false Bool.false 94290910 

noncomputable def Ns60p2113 := nat_lit 114000330850581975374595554288357755605281222507179 

noncomputable def Ns60p2114 := nat_lit 292639979086071460979902375825043237671796736000 

noncomputable def Ns60p2115 := nat_lit 813612046606768202706943344640000 

noncomputable def Ns60p2116 := nat_lit 1362711093789299302640847749193400320 

noncomputable def Ns60p2117 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz211 279148 1000 311695423616 16000000 558296 4000 2000 Ns60p2115 Ns60p2116 (@Eq.refl Real qz211) rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns60p2118 := nat_lit 1195380109219798454103919079334690219415633631716877271040 

noncomputable abbrev qz1064 := (Real.log (Enclosure.sfrac Bool.false 311695423616 16000000))

noncomputable abbrev qz1065 := (@HSub.hSub Real Real Real qz11 qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 558296))))

noncomputable abbrev qz844 := (@HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 279148 4000) qz1064) (@HMul.hMul Real Real Real qz5 qz12 qz1065))

noncomputable abbrev qz1066 := (Enclosure.sfrac Bool.false 279148 2000)

noncomputable abbrev qz543 := (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 qz844 qz1066) (@HMul.hMul Real Real Real qz5 qz1066 (Real.log Real.pi)))

noncomputable def Ns60p2119 := @Enclosure.Real.IsNear.addLit_ft_p qz543 (Enclosure.sfrac Bool.true Ns60p2115 Ns60p2116) 877208637075997773347 2251799813685248000 4623345905636336046039 Ns60p72 Ns60p2115 Ns60p2116 0 1 Ns60p2118 

noncomputable def Ns60p2120 := nat_lit 14717118781289623058961661952000 

noncomputable abbrev qz544 := (@HSub.hSub Real Real Real qz11 qz844 qz1066)

noncomputable def Ns60p2121 := @Enclosure.Real.IsNear.subLit_ff_p qz544 (@HMul.hMul Real Real Real qz5 qz1066 (Real.log Real.pi)) 1236988890847595908643 2251799813685248000 8973376067267830319 1092233000000000000000000 2680571777907 16777216000 69787 8388608000 Ns60p2120 877208637075997773347 2251799813685248000 

noncomputable abbrev qz545 := qz844

noncomputable def Ns60p2122 := @Enclosure.Real.IsNear.subLit_ff_p qz545 qz1066 310256319608580142599 450359962737049600 8973376067267830319 1092233000000000000000000 279148 2000 0 1 494795556339038363457200 1236988890847595908643 2251799813685248000 8973376067267830319 1092233000000000000000000 

noncomputable def Ns60p2123 := nat_lit 698635122689271520799081859542679552 

noncomputable def Ns60p2124 := nat_lit 11940793687544494680965120 

noncomputable def Ns60p2125 := nat_lit 3749139400973418148281621726362658473176640524497842908751672240693575680 

noncomputable def Ns60p2126 := nat_lit 9360321947406429676174838389660220232095159044905949176610270463655936 

noncomputable def Ns60p2127 := nat_lit 222038393746683485657310709890534138781616010534042806910179082240 

noncomputable def Ns60p2128 := BSN.log_dyadic_bound 49551423616 573839423616 4 3 Ns60p2125 33554432 8737864 Ns60p2126 Ns60p2127 5809363 623390847232 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 49551423616) (BSN.artanhQ 573839423616) 0 3 Ns60p2126 Ns60p2125 Ns60p2127 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz845 := qz1064

noncomputable def Ns60p2129 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 279148 4000) qz845 279148 4000 0 1 22241461440072385 2251799813685248 62500007645631 546116500000000000000 310432973903666306399 450359962737049600 4361688033565650597 546116500000000000000000 (Enclosure.Real.IsNear.const Bool.false 279148 4000) (BSN.isNear_log_sfrac 311695423616 16000000 22241461440072385 2251799813685248 62500007645631 546116500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 311695423616) qz650)) Bool.false Ns60p2124 Ns60p84 1000000122330096 8737864000000000000000 22241461440072385 2251799813685248 62500007645631 546116500000000000000 (BSN.log_rat_reduce_isNear 311695423616 16000000 14 623390847232 524288000000 5809363 33554432 24973259072661432 36028797018963968 8737864 1000000000000000 rfl rfl rfl rfl (Ns60p2128 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p2130 := BSN.arctan_dyadic_bound_f 1000 558296 1 0 4194304 1092233 0 1 1 0 1 1 7512 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 558296) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 558296) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz1067 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 558296)))

noncomputable abbrev qz846 := qz1067

noncomputable abbrev qz546 := qz846

noncomputable def Ns60p2131 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz546 884279719003555 562949953421312 1 2000000000000000 7512 4194304 1 1092233 3704709082485385854976 883271475430819 562949953421312 2000000001092233 2184466000000000000000 qz15 (Ns60p2130 rfl) rfl rfl 

noncomputable abbrev qz847 := (@HMul.hMul Real Real Real qz5 qz12 qz1065)

noncomputable abbrev qz547 := qz847

noncomputable abbrev qz848 := qz1065

noncomputable abbrev qz548 := qz848

noncomputable abbrev qz849 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 279148 4000) qz1064)

noncomputable def Ns60p2132 := @Enclosure.Real.IsNear.subLit_ff_p qz849 qz547 310432973903666306399 450359962737049600 4361688033565650597 546116500000000000000000 883271475430819 2251799813685248 2000000001092233 8737864000000000000000 Ns60p2123 310256319608580142599 450359962737049600 8973376067267830319 1092233000000000000000000 (Ns60p2129 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz12 qz548 1 4 0 1 883271475430819 562949953421312 2000000001092233 2184466000000000000000 883271475430819 2251799813685248 2000000001092233 8737864000000000000000 qz335 Ns60p2131 rfl) 

noncomputable def Ns60p2133 := @Ns60p2119 Ns60p2113 Ns60p2114 4623345905636336046039 Ns60p72 (@Ns60p2121 4623345905636336046039 Ns60p72 (Ns60p2122 (Ns60p2132 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 279148 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz1066 (Real.log Real.pi) 279148 2000 0 1 38410761 33554432 1 16777216 2680571777907 16777216000 69787 8388608000 (Enclosure.Real.IsNear.const Bool.false 279148 2000) RS061to078.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns60p2115 Ns60p2116) 

noncomputable def Ns60p2134 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz211) Bool.false Ns60p2113 Ns60p2114 4623345905636336046039 Ns60p72 408481477 1048576 35 2097152 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz211) (@HAdd.hAdd Real Real Real qz336 qz543 (Enclosure.sfrac Bool.true Ns60p2115 Ns60p2116)) Bool.false Ns60p2113 Ns60p2114 4623345905636336046039 Ns60p72 Ns60p2117 (Ns60p2133 rfl rfl)) 

noncomputable def Ns60p2135 := nat_lit 140276406198975084383062591245316476536391989292449175401976970247058078938627386425600 

noncomputable def Ns60p2136 := nat_lit 282420593756041169968876250770677203654226750032014161316128289932676281028176036096 

noncomputable def Ns60p2137 := nat_lit 366933335274091630537595272665057294503681700075410293601142142939546826098549917532416 

noncomputable def Ns60p2138 := BSN.sin_dyadic_bound_f 26999893134 17179869184 3 2 8388608 2186600 Ns60p2135 Ns60p94 Ns60p2136 Ns60p2137 Ns60p97 Ns60p2136 8388604 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26999893134) qz655 0 2 Ns60p2135 Ns60p94 Ns60p2136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26999893134) qz656 0 2 Ns60p2137 Ns60p97 Ns60p2136 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2139 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz211) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 408481477) qz714) Bool.false 408481477 1048576 35 2097152 Bool.false 8388604 8388608 1 1092233 (Ns60p2134 rfl) (Enclosure.sfrac_false_div 408481477 1048576) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 408481477) qz714) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 237493571597420078301184) qz756) 226375608064910080 72057594037927936 Bool.false 8388604 8388608 61 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q3 408481477 1048576 226375608064910080 72057594037927936 61 237493571597420078301184 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388604 8388608 237493571597420078301184 151115727451828646838272 26999893134 17179869184 2186600 2184466 (Ns60p2138 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p2140 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz211) Bool.false Ns60p2113 Ns60p2114 4623345905636336046039 Ns60p72 26142814535 67108864 1111 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz211) (@HAdd.hAdd Real Real Real qz336 qz543 (Enclosure.sfrac Bool.true Ns60p2115 Ns60p2116)) Bool.false Ns60p2113 Ns60p2114 4623345905636336046039 Ns60p72 Ns60p2117 (Ns60p2133 rfl rfl)) 

noncomputable def Ns60p2141 := Ns60p2112 24869 BSN.abs_quadSignPos (BSN.cos_quad_nat0 124 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 18663944 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 52 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 24222171 67108864) (@Eq.refl Real qz211) rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz211) qz211 1) Bool.false 2097151 2097152 40325307 2290578620416 67108832 67108864 1182 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz211) qz211 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz211)) Bool.false 2097151 2097152 40325307 2290578620416 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz211) qz211) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz211)) Bool.false 8388604 8388608 40325307 2290578620416 2097151 2097152 40325307 2290578620416 (Ns60p2139 rfl rfl) rfl)) rfl) (Ns60p2140 rfl) RS061to078.d7 

noncomputable def Ns60p2142 := nat_lit 460429426576450648986374174376090797076749839598297547522297229944731418103505544429906159964850746321 

noncomputable def Ns60p2143 := nat_lit 175491176444950084188833548203804109867350436293701152360891155377520940608895459952133443417041 

noncomputable def Ns60p2144 := nat_lit 2790216290101994384970202360774143958759158608863076252620495057352136196552522721093616913380874908625 

noncomputable def Ns60p2145 := BSN.cos_dyadic_bound_f 86501029 67108864 4 3 67108864 33554432 Ns60p2142 Ns60p219 Ns60p2143 Ns60p2144 Ns60p222 Ns60p2143 18663944 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 86501029) qz338 0 3 Ns60p2142 Ns60p219 Ns60p2143 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 86501029) (BSN.cosOddQ 67108864) 0 3 Ns60p2144 Ns60p222 Ns60p2143 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2146 := nat_lit 347496351700088738378397399167272360697840040079706806833590446352782755015696080152538935160707345521 

noncomputable def Ns60p2147 := nat_lit 75533689564600481033798339959408468938102016105905867760758365761265583760556133320624643632241 

noncomputable def Ns60p2148 := nat_lit 2106402790546197302985102982672652733545283674463980436984578643184617348062552182106009868629892263025 

noncomputable def Ns60p2149 := BSN.cos_dyadic_bound_f 80632797 67108864 4 3 67108864 33554432 Ns60p2146 Ns60p219 Ns60p2147 Ns60p2148 Ns60p222 Ns60p2147 24222171 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 80632797) qz338 0 3 Ns60p2146 Ns60p219 Ns60p2147 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 80632797) (BSN.cosOddQ 67108864) 0 3 Ns60p2148 Ns60p222 Ns60p2147 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2150 := nat_lit 1275899131852794880302989418068117343219256616656315681851822973665 

noncomputable def Ns60p2151 := nat_lit 432449665076607034273413409186742049362996884433139080296014561 

noncomputable def Ns60p2152 := nat_lit 3340940426823386370357101044658766887970512953429839798720009478881 

noncomputable def Ns60p2153 := BSN.sin_dyadic_bound_f 67529253 67108864 3 2 67108864 33554432 Ns60p2150 Ns60p119 Ns60p2151 Ns60p2152 Ns60p122 Ns60p2151 56696189 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 67529253) qz339 0 2 Ns60p2150 Ns60p119 Ns60p2151 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 67529253) (BSN.sinOddQ 67108864) 0 2 Ns60p2152 Ns60p122 Ns60p2151 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2154 := nat_lit 5444868861276492497900625 

noncomputable def Ns60p2155 := BSN.cos_dyadic_bound_f 1527555 67108864 2 1 67108864 33554432 Ns60p2154 Ns60p630 Ns60p2154 Ns60p2154 Ns60p631 Ns60p2154 67091479 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1527555) qz338 0 1 Ns60p2154 Ns60p630 Ns60p2154 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1527555) (BSN.cosOddQ 67108864) 0 1 Ns60p2154 Ns60p631 Ns60p2154 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2156 := Ns60p2110 42335 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 1 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 56696189 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 38 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 67091479 67108864) (@Eq.refl Real qz211) rfl rfl (Ns60p2141 RS061to078.d9 RS061to078.d11 RS061to078.d13 RS061to078.d17 (Ns60p2145 rfl rfl) (Ns60p2149 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns60p2140 rfl) RS061to078.d19 RS061to078.d21 RS061to078.d23 RS061to078.d25 RS061to078.d17 (Ns60p2153 rfl rfl) (Ns60p2155 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns60p2157 := nat_lit 124884662811396097604158792547273130170603354333265069948058730496 

noncomputable def Ns60p2158 := nat_lit 13429725599403298497795374168625429704572064024838066212438016 

noncomputable def Ns60p2159 := nat_lit 374627128982989486215480786893482139652400918871745533711751315456 

noncomputable def Ns60p2160 := BSN.cos_dyadic_bound_f 43753056 67108864 3 2 67108864 33554432 Ns60p2157 Ns60p103 Ns60p2158 Ns60p2159 Ns60p106 Ns60p2158 53344112 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 43753056) qz338 0 2 Ns60p2157 Ns60p103 Ns60p2158 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 43753056) (BSN.cosOddQ 67108864) 0 2 Ns60p2159 Ns60p106 Ns60p2158 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2161 := Ns60p2108 Bool.false 35938605 42335 Bool.true 43753056 3537118876014220 1 Bool.false 53344112 Bool.true Bool.false 14160961 49979 BSN.abs_quadSignNeg qz1024 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 53344112 67108864) (@Eq.refl Real qz211) rfl (Ns60p2156 rfl rfl) (Ns60p2140 rfl) RS061to078.d27 RS061to078.d29 RS061to078.d17 (Ns60p2160 rfl rfl) rfl 

noncomputable def Ns60p2162 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz211) qz211 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz211) qz211 6) 14160961 67108864 49979 67108864 14160961 67108864 49979 67108864 1900652011716608 14160961 33554432 49979 33554432 (Ns60p2161 rfl rfl rfl rfl) 

noncomputable def Ns60p2163 := @Enclosure.Real.IsNear.mulLit_ff qz1063 (Zeta.RiemannSiegel.correction qz213) 1624599 4194304 1 4194304 3800851389959 8796093022208 223328212645249 2401845767481327616 6174859367276001441 36893488147419103232 

noncomputable abbrev qz1068 := (@HPow.hPow Real Real Real qz326 qz212 qz8)

noncomputable def Ns60p2164 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz1068 1 1 0 1 1624599 4194304 1 4194304 1624599 4194304 1 4194304 

noncomputable def Ns60p2165 := @Enclosure.Real.IsNear.sqrt_image qz212 93171856043 2097152000 69787 2097152000 27956780 27956802 4194304 (@Enclosure.Real.IsNear.of_eq qz212 (@HMul.hMul Real Real Real qz5 qz211 qz3) Bool.false 93171856043 2097152000 69787 2097152000 (BSN.t_div_two_pi_mk qz211 279148 1000 (@Eq.refl Real qz211)) (@Enclosure.Real.IsNear.mulLit_ff qz211 qz3 279148 1000 0 1 1335089 8388608 1 8388608 93171856043 2097152000 69787 2097152000 (Enclosure.Real.IsNear.const Bool.false 279148 1000) RS061to078.d32 rfl)) 

noncomputable abbrev qz850 := (Real.sqrt qz1062)

noncomputable abbrev qz549 := qz850

noncomputable abbrev qz214 := qz549

noncomputable def Ns60p2166 := @Enclosure.Real.IsNear.sqrt_image qz214 27956791 4194304 11 4194304 10828630 10828635 4194304 (@Enclosure.Real.IsNear.recentre' qz214 Bool.false 55913582 8388608 22 8388608 27956791 4194304 11 4194304 (Ns60p2165 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns60p2167 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz214) 21657265 8388608 5 8388608 1624598 1624600 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz214) Bool.false 21657265 8388608 5 8388608 21657265 8388608 5 8388608 (Ns60p2166 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns60p2168 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz214)) Bool.false 3249198 8388608 2 8388608 1624599 4194304 1 4194304 (Ns60p2167 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz215 := (Real.cos (@HMul.hMul Real Real Real qz323 qz320 qz542))

noncomputable abbrev qz550 := (@HSub.hSub Real Real Real qz647 (@HMul.hMul Real Real Real qz644 qz843 qz843) qz843)

noncomputable abbrev qz216 := (@HMul.hMul Real Real Real qz323 qz320 (@HSub.hSub Real Real Real qz327 qz550 qz344))

noncomputable def Ns60p2169 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz213) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz215) (Real.cos qz216)) Bool.false 3800851389959 

noncomputable def Ns60p2170 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz215) (Real.cos qz216) 16552861 8388608 573 

noncomputable abbrev qz1069 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz215))

noncomputable def Ns60p2171 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz215) (@Neg.neg Real Real.instNeg qz1069) Bool.true 16552861 8388608 573 8388608 (BSN.inv_eq_neg_inv_neg qz215) 

noncomputable def Ns60p2172 := @Enclosure.Real.IsNear.recentre' qz1069 Bool.false 16552861 8388608 573 8388608 16552861 8388608 

noncomputable def Ns60p2173 := @Enclosure.Real.IsNear.recentre' qz215 Bool.true 4251153 8388608 160208995 9162314481664 4251153 8388608 160208995 9162314481664 

noncomputable abbrev qz217 := (@HMul.hMul Real Real Real qz323 qz320 qz542)

noncomputable def Ns60p2174 := @Enclosure.Real.IsNear.cos_image qz217 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 35072325) qz337) Bool.false 35072325 8388608 139 8388608 Bool.true 4251153 8388608 1 

noncomputable def Ns60p2175 := nat_lit 296846829523458723985289101 

noncomputable def Ns60p2176 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz213 884279719003555 140737488355328 1 500000000000000 2790967 4194304 11 4194304 2467995514508194887685 590295810358705651712 Ns60p2175 

noncomputable def Ns60p2177 := @Enclosure.Real.IsNear.subLit_ff_p qz214 qz1 27956791 4194304 11 4194304 6 1 0 1 2790967 2790967 4194304 11 

noncomputable def Ns60p2178 := @Ns60p2177 4194304 (@Enclosure.Real.IsNear.recentre' qz214 Bool.false 55913582 8388608 22 8388608 27956791 4194304 11 4194304 (Ns60p2165 rfl rfl rfl rfl rfl rfl) rfl) qz345 

noncomputable def Ns60p2179 := @Enclosure.Real.IsNear.recentre' qz217 Bool.false 2467995514508194887685 590295810358705651712 Ns60p2175 Ns60p1589 35072325 8388608 139 8388608 (@Ns60p2176 Ns60p1589 RS061to078.d31 (Ns60p2178 rfl rfl) rfl) 

noncomputable def Ns60p2180 := nat_lit 1256502239996203363205120 

noncomputable def Ns60p2181 := nat_lit 14887580466580411061593538726690663511046252459804769888408743065901049394089202959521 

noncomputable def Ns60p2182 := nat_lit 10333982761034692618426323482581564537085984839170627187446538741466503160745313441 

noncomputable def Ns60p2183 := nat_lit 44642073434219163799543763533106827404064585409735968410851336120220215175946118251681 

noncomputable def Ns60p2184 := BSN.cos_dyadic_bound_f 17855970781 17179869184 3 2 8388608 2186600 Ns60p2181 Ns60p1788 Ns60p2182 Ns60p2183 Ns60p1791 Ns60p2182 4251153 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 17855970781) qz769 0 2 Ns60p2181 Ns60p1788 Ns60p2182 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 17855970781) qz770 0 2 Ns60p2183 Ns60p1791 Ns60p2182 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2185 := @Ns60p2174 1092233 (Ns60p2179 rfl) (Enclosure.sfrac_false_div 35072325 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 35072325) qz337) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns60p2180) qz657) 226375608064910080 72057594037927936 Bool.false 4251153 8388608 0 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q2 35072325 8388608 226375608064910080 72057594037927936 0 Ns60p2180 Ns60p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 4251153 8388608 Ns60p2180 Ns60p84 17855970781 17179869184 2186600 2184466 (Ns60p2184 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p2186 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz215) 4251153 8388608 160208995 9162314481664 8276144 8276717 4194304 (@Enclosure.Real.IsNear.neg qz215 Bool.true 4251153 8388608 160208995 9162314481664 (Ns60p2173 (Ns60p2185 rfl rfl) rfl)) 

noncomputable def Ns60p2187 := Ns60p2171 (@Enclosure.Real.IsNear.neg qz1069 Bool.false 16552861 8388608 573 8388608 (@Ns60p2172 573 8388608 (Ns60p2186 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p2188 := @Enclosure.Real.IsNear.recentre' (Real.cos qz216) Bool.true 918476 4194304 

noncomputable def Ns60p2189 := @Enclosure.Real.IsNear.cos_image qz216 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 15028753)) qz337) Bool.true 15028753 8388608 

noncomputable def Ns60p2190 := nat_lit 4435705254594289327879948525 

noncomputable def Ns60p2191 := nat_lit 2902048520090594492228509705598373 

noncomputable def Ns60p2192 := @Enclosure.Real.IsNear.recentre' qz216 Bool.true Ns60p2190 Ns60p327 Ns60p2191 

noncomputable abbrev qz218 := (@HSub.hSub Real Real Real qz327 qz550 qz344)

noncomputable def Ns60p2193 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz218 884279719003555 140737488355328 1 500000000000000 5016178884655 

noncomputable abbrev qz219 := qz550

noncomputable def Ns60p2194 := @Enclosure.Real.IsNear.subLit_tf qz219 qz23 3916667256879 17592186044416 107538739 17592186044416 1 16 

noncomputable abbrev qz551 := (@HMul.hMul Real Real Real qz644 qz843 qz843)

noncomputable abbrev qz220 := qz551

noncomputable def Ns60p2195 := @Enclosure.Real.IsNear.subLit_ff_n qz220 qz213 7789496795089 17592186044416 61401395 17592186044416 2790967 4194304 11 4194304 

noncomputable def Ns60p2196 := @Enclosure.Real.IsNear.mulLit_ff qz213 qz213 2790967 4194304 11 4194304 2790967 4194304 11 4194304 7789496795089 17592186044416 

noncomputable def Ns60p2197 := nat_lit 25118522821614341260333028644856165290674592741092538986964312270832946601206498826206141121 

noncomputable def Ns60p2198 := nat_lit 132762481614537305772658033474990982271754350042386060457019096598030243892912085621441 

noncomputable def Ns60p2199 := nat_lit 151765850215376036540836099451655054570367244180901217293385064622407873073701558416311409345 

noncomputable def Ns60p2200 := BSN.cos_dyadic_bound_t 15028753 8388608 4 3 4194304 1092233 Ns60p2197 Ns60p274 Ns60p2198 Ns60p2199 Ns60p277 Ns60p2198 918476 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 15028753) (BSN.cosEvenQ 8388608) 0 3 Ns60p2197 Ns60p274 Ns60p2198 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 15028753) (BSN.cosOddQ 8388608) 0 3 Ns60p2199 Ns60p277 Ns60p2198 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2201 := @Ns60p2188 90568025 2290578620416 229619 1048576 90568025 2290578620416 (@Ns60p2189 81 2097152 Bool.true 918476 4194304 1 1092233 (@Ns60p2192 Ns60p1701 15028753 8388608 81 2097152 (@Ns60p2193 17592186044416 107538739 17592186044416 Ns60p2190 Ns60p327 Ns60p2191 Ns60p1701 RS061to078.d31 (@Ns60p2194 0 1 80258862154480 5016178884655 17592186044416 107538739 17592186044416 (@Ns60p2195 16427693142196617216 3916667256879 17592186044416 107538739 17592186044416 (@Ns60p2196 61401395 17592186044416 (Ns60p2178 rfl rfl) (Ns60p2178 rfl rfl) rfl) (Ns60p2178 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 15028753 8388608) (BSN.cos_neg_of_bound 15028753 8388608 Bool.true 918476 4194304 1 1092233 (Ns60p2200 rfl rfl)) rfl rfl) 

noncomputable def Ns60p2202 := @Ns60p2163 1455427472370095190047 Ns60p1233 (Ns60p2164 qz25 (@Enclosure.Real.IsNear.of_eq qz1068 (@Inv.inv Real Real.instInv (Real.sqrt qz214)) Bool.false 1624599 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz212 (BSN.t_div_two_pi_nonneg qz211 279148 1000 (@Eq.refl Real qz211))) Ns60p2168) rfl) (@Ns60p2169 8796093022208 223328212645249 2401845767481327616 (BSN.correction_mk qz213 (BSN.cos_two_pi_p_ne_zero_mk qz211 279148 1000 6 (@Eq.refl Real qz211) rfl rfl (@BSN.floor_sqrt_eq_dec qz211 279148 1000 6 (@Eq.refl Real qz211) rfl rfl rfl))) (@Ns60p2170 8388608 229619 1048576 90568025 2290578620416 3800851389959 8796093022208 223328212645249 2401845767481327616 Ns60p2187 (Ns60p2201 rfl) rfl)) 

noncomputable def Ns60p2203 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz211) (hardyZApproximantRS₀ qz211) Bool.false 9395281912706451295 36893488147419103232 61476352278844731650079 Ns60p1233 (@Eq.refl Real (hardyZApproximantRS₀ qz211)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz211) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz211) qz211 6) (@HMul.hMul Real Real Real qz5 qz1063 (Zeta.RiemannSiegel.correction qz213))) Bool.false 9395281912706451295 36893488147419103232 61476352278844731650079 Ns60p1233 (BSN.hardyZApproximantRS₀_eq qz211 6 (@BSN.floor_sqrt_eq_dec qz211 279148 1000 6 (@Eq.refl Real qz211) rfl rfl rfl)) (@Ns60p2107 9395281912706451295 36893488147419103232 61476352278844731650079 Ns60p1233 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz211) qz211 6) (@HAdd.hAdd Real Real Real qz336 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz211) qz211 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz211) qz211 6)) Bool.false 14160961 33554432 49979 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz211) qz211 6) (Ns60p2162 (Ns60p2161 rfl rfl rfl rfl) rfl rfl)) (Ns60p2202 rfl) rfl rfl)) 

theorem RS061to078.d61 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz211) Bool.false 9395281912706451295 36893488147419103232 61476352278844731650079 Ns60p1233 := Ns60p2203 

noncomputable def Ns60p2204 := nat_lit 10205071864913669858353217536 

noncomputable abbrev qz851 := (Enclosure.sfrac Bool.false 281629 1000)

noncomputable abbrev qz552 := qz851

noncomputable abbrev qz221 := qz552

noncomputable abbrev qz1070 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 281629 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz852 := qz1070

noncomputable abbrev qz553 := qz852

noncomputable abbrev qz222 := qz553

noncomputable abbrev qz853 := (@HSub.hSub Real Real Real qz920 (Real.sqrt qz1070) qz914)

noncomputable abbrev qz554 := qz853

noncomputable abbrev qz223 := qz554

noncomputable abbrev qz1071 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz326 qz222 qz8))

noncomputable def Ns60p2205 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz221) qz221 6) (@HMul.hMul Real Real Real qz5 qz1071 (Zeta.RiemannSiegel.correction qz223)) 132440673 33554432 25209 16777216 12894721799798350577 73786976294838206464 4446733740880513215479 Ns60p1227 Ns60p2204 

noncomputable def Ns60p2206 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz221) qz221 Real.cos BSN.quadSignNeg 5 6 281629 1000 70 67108864 33554432 1125899906842624 Bool.false 26459017158 1120 120242927 63 27397080 8 

noncomputable def Ns60p2207 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz221) qz221 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 281629 1000 2 37 67108864 33554432 1125899906842624 Bool.false 26459017158 1120 

noncomputable def Ns60p2208 := Ns60p2207 93032624 62 33554424 8 108007536 62 30011992 8 Bool.true 58530064 25086 Bool.false 47503579 Bool.true 58705986 3537118876014220 1 Bool.false 50986365 Bool.true Bool.false 51499824 Bool.true Bool.true 107054659 

noncomputable def Ns60p2209 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz221) qz221 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 281629 1000 126 54 67108864 33554432 1125899906842624 Bool.false 26459017158 1120 

noncomputable def Ns60p2210 := Ns60p2209 46516304 62 47453136 16 73726608 62 38745320 8 Bool.false 13536 1190 Bool.false 76467988 Bool.false 3090991 3537118876014220 1 Bool.false 28057105 Bool.true Bool.false 67037692 Bool.true Bool.true 58530064 

noncomputable def Ns60p2211 := nat_lit 3189513474429721072143813514275516863908911791679748777 

noncomputable def Ns60p2212 := nat_lit 8089666547332489047690883632259891656866972408217600 

noncomputable def Ns60p2213 := nat_lit 65790976000000000000000000 

noncomputable def Ns60p2214 := nat_lit 850416290110015240456124391520000 

noncomputable def Ns60p2215 := nat_lit 1437013449982147692141666729572316480 

noncomputable def Ns60p2216 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz221 281629 1000 317260574564 16000000 563258 4000 2000 Ns60p2214 Ns60p2215 (@Eq.refl Real qz221) rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns60p2217 := nat_lit 1020644311817510743086020324568165396450851773337519608640 

noncomputable abbrev qz1072 := (Real.log (Enclosure.sfrac Bool.false 317260574564 16000000))

noncomputable abbrev qz1073 := (@HSub.hSub Real Real Real qz11 qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 563258))))

noncomputable abbrev qz854 := (@HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 281629 4000) qz1072) (@HMul.hMul Real Real Real qz5 qz12 qz1073))

noncomputable abbrev qz1074 := (Enclosure.sfrac Bool.false 281629 2000)

noncomputable abbrev qz555 := (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 qz854 qz1074) (@HMul.hMul Real Real Real qz5 qz1074 (Real.log Real.pi)))

noncomputable def Ns60p2218 := @Enclosure.Real.IsNear.addLit_ft_p qz555 (Enclosure.sfrac Bool.true Ns60p2214 Ns60p2215) 710254899704651568793 1801439850948198400 1097380769600919242289 Ns60p2213 Ns60p2214 Ns60p2215 0 1 Ns60p2217 

noncomputable def Ns60p2219 := nat_lit 238321997348065511487580405760000 

noncomputable abbrev qz556 := (@HSub.hSub Real Real Real qz11 qz854 qz1074)

noncomputable def Ns60p2220 := @Enclosure.Real.IsNear.subLit_ff_p qz556 (@HMul.hMul Real Real Real qz5 qz1074 (Real.log Real.pi)) 5003186073593706655997 9007199254740992000 1064812626676733597 128498000000000000000000 10817584209669 67108864000 281629 33554432000 Ns60p2219 710254899704651568793 1801439850948198400 

noncomputable def Ns60p2221 := nat_lit 10006372147187413311994000 

noncomputable abbrev qz557 := qz854

noncomputable def Ns60p2222 := @Enclosure.Real.IsNear.subLit_ff_p qz557 qz1074 6271530333050432073981 9007199254740992000 1064812626676733597 128498000000000000000000 281629 2000 0 1 Ns60p2221 5003186073593706655997 9007199254740992000 1064812626676733597 128498000000000000000000 

noncomputable def Ns60p2223 := nat_lit 14122230835484344281421760443384332288 

noncomputable def Ns60p2224 := nat_lit 11962187983531122693767168 

noncomputable def Ns60p2225 := nat_lit 3972654695109237835590234736632335645436035654289462224507520675894497280 

noncomputable def Ns60p2226 := nat_lit 12048331261998907231859440745973566374667110706385965320974251191136256 

noncomputable def Ns60p2227 := nat_lit 420517982224653372966027357195701679558586995014960314692762071040 

noncomputable def Ns60p2228 := BSN.log_dyadic_bound 55116574564 579404574564 4 3 Ns60p2225 33554432 8737864 Ns60p2226 Ns60p2227 6403174 634521149128 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 55116574564) (BSN.artanhQ 579404574564) 0 3 Ns60p2226 Ns60p2225 Ns60p2227 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz855 := qz1072

noncomputable def Ns60p2229 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 281629 4000) qz855 281629 4000 0 1 22281311421713089 2251799813685248 62500007645631 546116500000000000000 6275063454385635541981 9007199254740992000 17601814653231412899 Ns60p192 (Enclosure.Real.IsNear.const Bool.false 281629 4000) (BSN.isNear_log_sfrac 317260574564 16000000 22281311421713089 2251799813685248 62500007645631 546116500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 317260574564) qz650)) Bool.false Ns60p2224 Ns60p84 1000000122330096 8737864000000000000000 22281311421713089 2251799813685248 62500007645631 546116500000000000000 (BSN.log_rat_reduce_isNear 317260574564 16000000 14 634521149128 524288000000 6403174 33554432 24973259072661432 36028797018963968 8737864 1000000000000000 rfl rfl rfl rfl (Ns60p2228 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p2230 := BSN.arctan_dyadic_bound_f 1000 563258 1 0 4194304 1092233 0 1 1 0 1 1 7446 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 563258) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 563258) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz1075 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 563258)))

noncomputable abbrev qz856 := qz1075

noncomputable abbrev qz558 := qz856

noncomputable def Ns60p2231 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz558 884279719003555 562949953421312 1 2000000000000000 7446 4194304 1 1092233 3704746237182311661568 883280333800867 562949953421312 2000000001092233 2184466000000000000000 qz15 (Ns60p2230 rfl) rfl rfl 

noncomputable abbrev qz857 := (@HMul.hMul Real Real Real qz5 qz12 qz1073)

noncomputable abbrev qz559 := qz857

noncomputable abbrev qz858 := qz1073

noncomputable abbrev qz560 := qz858

noncomputable abbrev qz859 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 281629 4000) qz1072)

noncomputable def Ns60p2232 := @Enclosure.Real.IsNear.subLit_ff_p qz859 qz559 6275063454385635541981 9007199254740992000 17601814653231412899 Ns60p192 883280333800867 2251799813685248 2000000001092233 8737864000000000000000 Ns60p2223 6271530333050432073981 9007199254740992000 1064812626676733597 128498000000000000000000 (Ns60p2229 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz12 qz560 1 4 0 1 883280333800867 562949953421312 2000000001092233 2184466000000000000000 883280333800867 2251799813685248 2000000001092233 8737864000000000000000 qz335 Ns60p2231 rfl) 

noncomputable def Ns60p2233 := @Ns60p2218 Ns60p2211 Ns60p2212 1097380769600919242289 Ns60p2213 (@Ns60p2220 1097380769600919242289 Ns60p2213 (Ns60p2222 (Ns60p2232 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 281629 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz1074 (Real.log Real.pi) 281629 2000 0 1 38410761 33554432 1 16777216 10817584209669 67108864000 281629 33554432000 (Enclosure.Real.IsNear.const Bool.false 281629 2000) RS061to078.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns60p2214 Ns60p2215) 

noncomputable def Ns60p2234 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz221) Bool.false Ns60p2211 Ns60p2212 1097380769600919242289 Ns60p2213 413422143 1048576 141 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz221) (@HAdd.hAdd Real Real Real qz336 qz555 (Enclosure.sfrac Bool.true Ns60p2214 Ns60p2215)) Bool.false Ns60p2211 Ns60p2212 1097380769600919242289 Ns60p2213 Ns60p2216 (Ns60p2233 rfl rfl)) 

noncomputable def Ns60p2235 := nat_lit 80656425208422598878810365898279808978671307444774341978605234512942311908777047810728225143444166589272132676745542737640000000000 

noncomputable def Ns60p2236 := nat_lit 316646866740079143295725755612190180511469568587383446887297628374512813051459112748418952103360324986451946705925428665111910809600 

noncomputable def Ns60p2237 := nat_lit 149398257196636813276136723140404520232375845327926411545759729703009561860370161771970290063322439379472900390625000000000000 

noncomputable def Ns60p2238 := nat_lit 488136419635147266434501592519164747708407499986288390810788495448601770152191675156039682001529003128937851761602366775016000000000 

noncomputable def Ns60p2239 := nat_lit 28814864873347202039911043760709306426543730741451893666744084182080665987682779260106124641405789573767127150239214008525183883673600 

noncomputable def Ns60p2240 := BSN.cos_dyadic_bound_t 26989538650 17179869184 4 3 8388608 2186600 Ns60p2235 Ns60p2236 Ns60p2237 Ns60p2238 Ns60p2239 Ns60p2237 1692 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 26989538650) qz769 0 3 Ns60p2235 Ns60p2236 Ns60p2237 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 26989538650) qz770 0 3 Ns60p2238 Ns60p2239 Ns60p2237 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2241 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz221) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 413422143) qz714) Bool.false 413422143 1048576 141 8388608 Bool.false 1692 8388608 1 1092233 (Ns60p2234 rfl) (Enclosure.sfrac_false_div 413422143 1048576) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 413422143) qz714) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 237402492600593149853696) qz756) 226375608064910080 72057594037927936 Bool.true 1692 8388608 62 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q2 413422143 1048576 226375608064910080 72057594037927936 62 237402492600593149853696 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.true 1692 8388608 237402492600593149853696 151115727451828646838272 26989538650 17179869184 2186600 2184466 (Ns60p2240 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p2242 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz221) Bool.false Ns60p2211 Ns60p2212 1097380769600919242289 Ns60p2213 26459017158 67108864 1120 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz221) (@HAdd.hAdd Real Real Real qz336 qz555 (Enclosure.sfrac Bool.true Ns60p2214 Ns60p2215)) Bool.false Ns60p2211 Ns60p2212 1097380769600919242289 Ns60p2213 Ns60p2216 (Ns60p2233 rfl rfl)) 

noncomputable def Ns60p2243 := Ns60p2210 25086 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 126 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 28057105 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 54 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 67037692 67108864) (@Eq.refl Real qz221) rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 1) Bool.false 423 2097152 162393461 9162314481664 13536 67108864 1190 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz221)) Bool.false 423 2097152 162393461 9162314481664 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz221) qz221) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz221)) Bool.false 1692 8388608 162393461 9162314481664 423 2097152 162393461 9162314481664 (Ns60p2241 rfl rfl) rfl)) rfl) (Ns60p2242 rfl) RS061to078.d7 

noncomputable def Ns60p2244 := nat_lit 281008271728224040153837182412179064081788179321594595779788902251923395148036797402879432902978830336 

noncomputable def Ns60p2245 := nat_lit 39972007474203187463591728025807334738563485843026761135453796966540049325384596915009676640256 

noncomputable def Ns60p2246 := nat_lit 1703644028174370355436107395126116812986202059777024393911978077843618979419406914234756279435138170880 

noncomputable def Ns60p2247 := BSN.cos_dyadic_bound_f 76467988 67108864 4 3 67108864 33554432 Ns60p2244 Ns60p219 Ns60p2245 Ns60p2246 Ns60p222 Ns60p2245 28057105 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 76467988) qz338 0 3 Ns60p2244 Ns60p219 Ns60p2245 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 76467988) (BSN.cosOddQ 67108864) 0 3 Ns60p2246 Ns60p222 Ns60p2245 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2248 := nat_lit 91283222269431815552650561 

noncomputable def Ns60p2249 := BSN.cos_dyadic_bound_f 3090991 67108864 2 1 67108864 33554432 Ns60p2248 Ns60p630 Ns60p2248 Ns60p2248 Ns60p631 Ns60p2248 67037692 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 3090991) qz338 0 1 Ns60p2248 Ns60p630 Ns60p2248 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 3090991) (BSN.cosOddQ 67108864) 0 1 Ns60p2248 Ns60p631 Ns60p2248 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2250 := nat_lit 173539784451444394233584714037473371959427672151626590808718895841 

noncomputable def Ns60p2251 := nat_lit 25930485649728362455545098516256874833317839785227428545358561 

noncomputable def Ns60p2252 := nat_lit 520567492383033725975843051915387602128616380775309317569065970401 

noncomputable def Ns60p2253 := BSN.cos_dyadic_bound_f 47503579 67108864 3 2 67108864 33554432 Ns60p2250 Ns60p103 Ns60p2251 Ns60p2252 Ns60p106 Ns60p2251 50986365 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 47503579) qz338 0 2 Ns60p2250 Ns60p103 Ns60p2251 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 47503579) (BSN.cosOddQ 67108864) 0 2 Ns60p2252 Ns60p106 Ns60p2251 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2254 := nat_lit 728643302973617133911343120111821992034914097441050325882537836800 

noncomputable def Ns60p2255 := nat_lit 141077934742402573755278535578546542442051494117640983637197056 

noncomputable def Ns60p2256 := nat_lit 1908123095893700032267437720759073284737011695640846101433138872576 

noncomputable def Ns60p2257 := BSN.sin_dyadic_bound_f 58705986 67108864 3 2 67108864 33554432 Ns60p2254 Ns60p119 Ns60p2255 Ns60p2256 Ns60p122 Ns60p2255 51499824 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 58705986) qz339 0 2 Ns60p2254 Ns60p119 Ns60p2255 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 58705986) (BSN.sinOddQ 67108864) 0 2 Ns60p2256 Ns60p122 Ns60p2255 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2258 := Ns60p2208 42707 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 2 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 50986365 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 37 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 51499824 67108864) (@Eq.refl Real qz221) rfl rfl (Ns60p2243 RS061to078.d9 RS061to078.d11 RS061to078.d13 RS061to078.d17 (Ns60p2247 rfl rfl) (Ns60p2249 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns60p2242 rfl) RS061to078.d19 RS061to078.d21 RS061to078.d23 RS061to078.d25 RS061to078.d17 (Ns60p2253 rfl rfl) (Ns60p2257 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns60p2259 := nat_lit 15269708995971783309716490040586609813728911472935589320531690625 

noncomputable def Ns60p2260 := nat_lit 200813283114600620738809609384436705502601135010237062890625 

noncomputable def Ns60p2261 := nat_lit 45808725361349120727907992502541060567775729216536747487469290625 

noncomputable def Ns60p2262 := BSN.cos_dyadic_bound_f 25873135 67108864 3 2 67108864 33554432 Ns60p2259 Ns60p103 Ns60p2260 Ns60p2261 Ns60p106 Ns60p2260 62182777 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 25873135) qz338 0 2 Ns60p2259 Ns60p103 Ns60p2260 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 25873135) (BSN.cosOddQ 67108864) 0 2 Ns60p2261 Ns60p106 Ns60p2260 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2263 := Ns60p2206 Bool.true 107054659 42707 Bool.true 25873135 3537118876014220 1 Bool.false 62182777 Bool.true Bool.true 132440673 50418 BSN.abs_quadSignNeg qz1024 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 62182777 67108864) (@Eq.refl Real qz221) rfl (Ns60p2258 rfl rfl) (Ns60p2242 rfl) RS061to078.d27 RS061to078.d29 RS061to078.d17 (Ns60p2262 rfl rfl) rfl 

noncomputable def Ns60p2264 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 6) 132440673 67108864 50418 67108864 132440673 67108864 50418 67108864 17775886224850944 132440673 33554432 25209 16777216 (Ns60p2263 rfl rfl rfl rfl) 

noncomputable def Ns60p2265 := @Enclosure.Real.IsNear.mulLit_ff qz1071 (Zeta.RiemannSiegel.correction qz223) 1621009 4194304 1 4194304 7954750281953 17592186044416 2737827218904143 19214766139850620928 12894721799798350577 73786976294838206464 

noncomputable abbrev qz1076 := (@HPow.hPow Real Real Real qz326 qz222 qz8)

noncomputable def Ns60p2266 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz1076 1 1 0 1 1621009 4194304 1 4194304 1621009 4194304 1 4194304 

noncomputable def Ns60p2267 := @Enclosure.Real.IsNear.sqrt_image qz222 375999779981 8388608000 281629 8388608000 28080742 28080764 4194304 (@Enclosure.Real.IsNear.of_eq qz222 (@HMul.hMul Real Real Real qz5 qz221 qz3) Bool.false 375999779981 8388608000 281629 8388608000 (BSN.t_div_two_pi_mk qz221 281629 1000 (@Eq.refl Real qz221)) (@Enclosure.Real.IsNear.mulLit_ff qz221 qz3 281629 1000 0 1 1335089 8388608 1 8388608 375999779981 8388608000 281629 8388608000 (Enclosure.Real.IsNear.const Bool.false 281629 1000) RS061to078.d32 rfl)) 

noncomputable abbrev qz860 := (Real.sqrt qz1070)

noncomputable abbrev qz561 := qz860

noncomputable abbrev qz224 := qz561

noncomputable def Ns60p2268 := @Enclosure.Real.IsNear.sqrt_image qz224 28080753 4194304 11 4194304 10852611 10852616 4194304 (@Enclosure.Real.IsNear.recentre' qz224 Bool.false 56161506 8388608 22 8388608 28080753 4194304 11 4194304 (Ns60p2267 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns60p2269 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz224) 21705227 8388608 5 8388608 1621008 1621010 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz224) Bool.false 21705227 8388608 5 8388608 21705227 8388608 5 8388608 (Ns60p2268 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns60p2270 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz224)) Bool.false 3242018 8388608 2 8388608 1621009 4194304 1 4194304 (Ns60p2269 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz225 := (Real.cos (@HMul.hMul Real Real Real qz323 qz320 qz554))

noncomputable abbrev qz562 := (@HSub.hSub Real Real Real qz647 (@HMul.hMul Real Real Real qz644 qz853 qz853) qz853)

noncomputable abbrev qz226 := (@HMul.hMul Real Real Real qz323 qz320 (@HSub.hSub Real Real Real qz327 qz562 qz344))

noncomputable def Ns60p2271 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz223) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz225) (Real.cos qz226)) Bool.false 7954750281953 

noncomputable def Ns60p2272 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz225) (Real.cos qz226) 12376369 4194304 639 

noncomputable abbrev qz1077 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz225))

noncomputable def Ns60p2273 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz225) (@Neg.neg Real Real.instNeg qz1077) Bool.true 12376369 4194304 639 4194304 (BSN.inv_eq_neg_inv_neg qz225) 

noncomputable def Ns60p2274 := @Enclosure.Real.IsNear.recentre' qz1077 Bool.false 24752738 8388608 1278 8388608 12376369 4194304 

noncomputable def Ns60p2275 := @Enclosure.Real.IsNear.recentre' qz225 Bool.true 2842867 8388608 160208995 9162314481664 2842867 8388608 160208995 9162314481664 

noncomputable abbrev qz227 := (@HMul.hMul Real Real Real qz323 qz320 qz554)

noncomputable def Ns60p2276 := @Enclosure.Real.IsNear.cos_image qz227 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 18315039) qz660) Bool.false 18315039 4194304 139 8388608 Bool.true 2842867 8388608 1 

noncomputable def Ns60p2277 := nat_lit 59369365904904709891436521 

noncomputable def Ns60p2278 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz223 884279719003555 140737488355328 1 500000000000000 2914929 4194304 11 4194304 2577612597035313572595 590295810358705651712 Ns60p2277 

noncomputable def Ns60p2279 := @Enclosure.Real.IsNear.subLit_ff_p qz224 qz1 28080753 4194304 11 4194304 6 1 0 1 2914929 2914929 4194304 11 

noncomputable def Ns60p2280 := @Ns60p2279 4194304 (@Enclosure.Real.IsNear.recentre' qz224 Bool.false 56161506 8388608 22 8388608 28080753 4194304 11 4194304 (Ns60p2267 rfl rfl rfl rfl rfl rfl) rfl) qz345 

noncomputable def Ns60p2281 := @Enclosure.Real.IsNear.recentre' qz227 Bool.false 2577612597035313572595 590295810358705651712 Ns60p2277 Ns60p2078 18315039 4194304 139 8388608 (@Ns60p2278 Ns60p2078 RS061to078.d31 (Ns60p2280 rfl rfl) rfl) 

noncomputable def Ns60p2282 := nat_lit 28752084940832172446678539408979661644474482014895202643288207357385737958090275390625 

noncomputable def Ns60p2283 := nat_lit 38494405935065044550923182458158995524373843426215778653471569027203003082275390625 

noncomputable def Ns60p2284 := nat_lit 86179266010626387250933771862022666942374698357833176372557678934102807868106275390625 

noncomputable def Ns60p2285 := BSN.cos_dyadic_bound_f 21046248925 17179869184 3 2 8388608 2186600 Ns60p2282 Ns60p1788 Ns60p2283 Ns60p2284 Ns60p1791 Ns60p2283 2842867 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 21046248925) qz769 0 2 Ns60p2282 Ns60p1788 Ns60p2283 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 21046248925) qz770 0 2 Ns60p2284 Ns60p1791 Ns60p2283 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2286 := @Ns60p2276 1092233 (Ns60p2281 rfl) (Enclosure.sfrac_false_div 18315039 4194304) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 18315039) qz660) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 740499053283466037690368) qz709) 226375608064910080 72057594037927936 Bool.false 2842867 8388608 0 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q2 18315039 4194304 226375608064910080 72057594037927936 0 740499053283466037690368 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 2842867 8388608 740499053283466037690368 604462909807314587353088 21046248925 17179869184 2186600 2184466 (Ns60p2285 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p2287 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz225) 2842867 8388608 160208995 9162314481664 12375730 12377008 4194304 (@Enclosure.Real.IsNear.neg qz225 Bool.true 2842867 8388608 160208995 9162314481664 (Ns60p2275 (Ns60p2286 rfl rfl) rfl)) 

noncomputable def Ns60p2288 := Ns60p2273 (@Enclosure.Real.IsNear.neg qz1077 Bool.false 12376369 4194304 639 4194304 (@Ns60p2274 639 4194304 (Ns60p2287 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p2289 := @Enclosure.Real.IsNear.recentre' (Real.cos qz226) Bool.true 642737 4194304 

noncomputable def Ns60p2290 := @Enclosure.Real.IsNear.cos_image qz226 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 14467353)) qz337) Bool.true 14467353 8388608 

noncomputable def Ns60p2291 := nat_lit 4270008949582956940719471805 

noncomputable def Ns60p2292 := nat_lit 2975643973445815105743499680819593 

noncomputable def Ns60p2293 := @Enclosure.Real.IsNear.recentre' qz226 Bool.true Ns60p2291 Ns60p327 Ns60p2292 

noncomputable abbrev qz228 := (@HSub.hSub Real Real Real qz327 qz562 qz344)

noncomputable def Ns60p2294 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz228 884279719003555 140737488355328 1 500000000000000 4828798917151 

noncomputable abbrev qz229 := qz562

noncomputable def Ns60p2295 := @Enclosure.Real.IsNear.subLit_tf qz229 qz23 3729287289375 17592186044416 110265903 17592186044416 1 16 

noncomputable abbrev qz563 := (@HMul.hMul Real Real Real qz644 qz853 qz853)

noncomputable abbrev qz230 := qz563

noncomputable def Ns60p2296 := @Enclosure.Real.IsNear.subLit_ff_n qz230 qz223 8496811075041 17592186044416 64128559 17592186044416 2914929 4194304 11 4194304 

noncomputable def Ns60p2297 := @Enclosure.Real.IsNear.mulLit_ff qz223 qz223 2914929 4194304 11 4194304 2914929 4194304 11 4194304 8496811075041 17592186044416 

noncomputable def Ns60p2298 := nat_lit 21551820459990211492204764302594854078695281361034062837795854166057030601589591036306479521 

noncomputable def Ns60p2299 := nat_lit 84075399437542100355874011036036212257667791754058160769163628918370849973762245351841 

noncomputable def Ns60p2300 := nat_lit 130290672575855267529128566796703179997237067304709582987998094357860094264636950672560970145 

noncomputable def Ns60p2301 := BSN.cos_dyadic_bound_t 14467353 8388608 4 3 4194304 1092233 Ns60p2298 Ns60p274 Ns60p2299 Ns60p2300 Ns60p277 Ns60p2299 642737 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 14467353) (BSN.cosEvenQ 8388608) 0 3 Ns60p2298 Ns60p274 Ns60p2299 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 14467353) (BSN.cosOddQ 8388608) 0 3 Ns60p2300 Ns60p277 Ns60p2299 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2302 := @Ns60p2289 369917731 9162314481664 642737 4194304 369917731 9162314481664 (@Ns60p2290 331 8388608 Bool.true 642737 4194304 1 1092233 (@Ns60p2293 Ns60p1701 14467353 8388608 331 8388608 (@Ns60p2294 17592186044416 110265903 17592186044416 Ns60p2291 Ns60p327 Ns60p2292 Ns60p1701 RS061to078.d31 (@Ns60p2295 0 1 77260782674416 4828798917151 17592186044416 110265903 17592186044416 (@Ns60p2296 15641764594974720000 3729287289375 17592186044416 110265903 17592186044416 (@Ns60p2297 64128559 17592186044416 (Ns60p2280 rfl rfl) (Ns60p2280 rfl rfl) rfl) (Ns60p2280 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 14467353 8388608) (BSN.cos_neg_of_bound 14467353 8388608 Bool.true 642737 4194304 1 1092233 (Ns60p2301 rfl rfl)) rfl rfl) 

noncomputable def Ns60p2303 := @Ns60p2265 4446733740880513215479 Ns60p1227 (Ns60p2266 qz25 (@Enclosure.Real.IsNear.of_eq qz1076 (@Inv.inv Real Real.instInv (Real.sqrt qz224)) Bool.false 1621009 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz222 (BSN.t_div_two_pi_nonneg qz221 281629 1000 (@Eq.refl Real qz221))) Ns60p2270) rfl) (@Ns60p2271 17592186044416 2737827218904143 19214766139850620928 (BSN.correction_mk qz223 (BSN.cos_two_pi_p_ne_zero_mk qz221 281629 1000 6 (@Eq.refl Real qz221) rfl rfl (@BSN.floor_sqrt_eq_dec qz221 281629 1000 6 (@Eq.refl Real qz221) rfl rfl rfl))) (@Ns60p2272 4194304 642737 4194304 369917731 9162314481664 7954750281953 17592186044416 2737827218904143 19214766139850620928 Ns60p2288 (Ns60p2302 rfl) rfl)) 

noncomputable def Ns60p2304 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz221) (hardyZApproximantRS₀ qz221) Bool.true 304134841707756217073 73786976294838206464 125542993645754088958967 Ns60p1227 (@Eq.refl Real (hardyZApproximantRS₀ qz221)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz221) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz221) qz221 6) (@HMul.hMul Real Real Real qz5 qz1071 (Zeta.RiemannSiegel.correction qz223))) Bool.true 304134841707756217073 73786976294838206464 125542993645754088958967 Ns60p1227 (BSN.hardyZApproximantRS₀_eq qz221 6 (@BSN.floor_sqrt_eq_dec qz221 281629 1000 6 (@Eq.refl Real qz221) rfl rfl rfl)) (@Ns60p2205 304134841707756217073 73786976294838206464 125542993645754088958967 Ns60p1227 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz221) qz221 6) (@HAdd.hAdd Real Real Real qz336 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz221) qz221 6)) Bool.true 132440673 33554432 25209 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz221) qz221 6) (Ns60p2264 (Ns60p2263 rfl rfl rfl rfl) rfl rfl)) (Ns60p2303 rfl) rfl rfl)) 

theorem RS061to078.d62 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz221) Bool.true 304134841707756217073 73786976294838206464 125542993645754088958967 Ns60p1227 := Ns60p2304 

noncomputable def Ns60p2305 := nat_lit 20148142619860004690198528 

noncomputable def Ns60p2306 := nat_lit 135741846378951040468779008 

noncomputable abbrev qz861 := (Enclosure.sfrac Bool.false 282868 1000)

noncomputable abbrev qz564 := qz861

noncomputable abbrev qz231 := qz564

noncomputable abbrev qz1078 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 282868 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz862 := qz1078

noncomputable abbrev qz565 := qz862

noncomputable abbrev qz232 := qz565

noncomputable abbrev qz863 := (@HSub.hSub Real Real Real qz920 (Real.sqrt qz1078) qz914)

noncomputable abbrev qz566 := qz863

noncomputable abbrev qz233 := qz566

noncomputable abbrev qz1079 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz326 qz232 qz8))

noncomputable def Ns60p2307 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz231) qz231 6) (@HMul.hMul Real Real Real qz5 qz1079 (Zeta.RiemannSiegel.correction qz233)) 10361207 16777216 25317 16777216 3301423039721064669 18446744073709551616 1525559362255407643035 Ns60p2305 Ns60p2306 

noncomputable def Ns60p2308 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz231) qz231 Real.cos BSN.quadSignNeg 5 6 282868 1000 70 67108864 33554432 1125899906842624 Bool.false 26617202155 1125 120242927 63 27397080 8 

noncomputable def Ns60p2309 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz231) qz231 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 282868 1000 2 37 67108864 33554432 1125899906842624 Bool.false 26617202155 1125 

noncomputable def Ns60p2310 := Ns60p2309 93032624 62 33554424 8 108007536 62 30011992 8 Bool.false 69409796 25191 Bool.false 90421155 Bool.true 34342326 3537118876014220 1 Bool.false 14868782 Bool.true Bool.false 32862911 Bool.true Bool.false 47278668 

noncomputable def Ns60p2311 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz231) qz231 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 282868 1000 127 54 67108864 33554432 1125899906842624 Bool.false 26617202155 1125 

noncomputable def Ns60p2312 := Ns60p2311 46516304 62 47453136 16 73726608 62 38745320 8 Bool.false 47398656 1190 Bool.false 71604927 Bool.false 69928721 3537118876014220 1 Bool.false 58770891 Bool.false Bool.false 33854939 Bool.true Bool.false 69409796 

noncomputable def Ns60p2313 := nat_lit 25132856667458152147686775870330414548663658804001 

noncomputable def Ns60p2314 := nat_lit 63366444382878416738487297651905137900466995200 

noncomputable def Ns60p2315 := nat_lit 869288179145569472599358832640000 

noncomputable def Ns60p2316 := nat_lit 1475365003172271343378520050363269120 

noncomputable abbrev qz234 := (@Eq.refl Real qz564)

noncomputable def Ns60p2317 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz231 282868 1000 320058221696 16000000 565736 4000 2000 Ns60p2315 Ns60p2316 qz234 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns60p2318 := nat_lit 263537103129365993464128086950075847657795446940641525760 

noncomputable abbrev qz1080 := (Real.log (Enclosure.sfrac Bool.false 320058221696 16000000))

noncomputable abbrev qz1081 := (@HSub.hSub Real Real Real qz11 qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 565736))))

noncomputable abbrev qz864 := (@HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 282868 4000) qz1080) (@HMul.hMul Real Real Real qz5 qz12 qz1081))

noncomputable abbrev qz1082 := (Enclosure.sfrac Bool.false 282868 2000)

noncomputable abbrev qz567 := (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 qz864 qz1082) (@HMul.hMul Real Real Real qz5 qz1082 (Real.log Real.pi)))

noncomputable def Ns60p2319 := @Enclosure.Real.IsNear.addLit_ft_p qz567 (Enclosure.sfrac Bool.true Ns60p2315 Ns60p2316) 178625285305880299073 450359962737049600 4684104953771508609249 Ns60p72 Ns60p2315 Ns60p2316 0 1 Ns60p2318 

noncomputable def Ns60p2320 := nat_lit 14984174973191899238461603840000 

noncomputable abbrev qz568 := (@HSub.hSub Real Real Real qz11 qz864 qz1082)

noncomputable def Ns60p2321 := @Enclosure.Real.IsNear.subLit_ff_p qz568 (@HMul.hMul Real Real Real qz5 qz1082 (Real.log Real.pi)) 1257701207018118668101 2251799813685248000 9089626081488703979 1092233000000000000000000 2716293785637 16777216000 70717 8388608000 Ns60p2320 178625285305880299073 450359962737049600 

noncomputable def Ns60p2322 := nat_lit 2515402414036237336202000 

noncomputable abbrev qz569 := qz864

noncomputable def Ns60p2323 := @Enclosure.Real.IsNear.subLit_ff_p qz569 qz1082 1576182261866878033733 2251799813685248000 9089626081488703979 1092233000000000000000000 282868 2000 0 1 Ns60p2322 1257701207018118668101 2251799813685248000 9089626081488703979 1092233000000000000000000 

noncomputable def Ns60p2324 := nat_lit 3549246923605828729833531530788470784 

noncomputable def Ns60p2325 := nat_lit 11972801706844939289100288 

noncomputable def Ns60p2326 := nat_lit 4089144421622475371007808635604320143407923959564155257730023754385326080 

noncomputable def Ns60p2327 := nat_lit 13568219672734466152441781702335202532172705383515841831966597779030016 

noncomputable def Ns60p2328 := nat_lit 565981980738204395900624789323684206241330839386023748426992189440 

noncomputable def Ns60p2329 := BSN.log_dyadic_bound 57914221696 582202221696 4 3 Ns60p2326 33554432 8737864 Ns60p2327 Ns60p2328 6697764 640116443392 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 57914221696) (BSN.artanhQ 582202221696) 0 3 Ns60p2327 Ns60p2326 Ns60p2328 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz865 := qz1080

noncomputable def Ns60p2330 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 282868 4000) qz865 282868 4000 0 1 22301081021958849 2251799813685248 62500007645631 546116500000000000000 1577065546629863924733 2251799813685248000 4419813040676087427 546116500000000000000000 (Enclosure.Real.IsNear.const Bool.false 282868 4000) (BSN.isNear_log_sfrac 320058221696 16000000 22301081021958849 2251799813685248 62500007645631 546116500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 320058221696) qz650)) Bool.false Ns60p2325 Ns60p84 1000000122330096 8737864000000000000000 22301081021958849 2251799813685248 62500007645631 546116500000000000000 (BSN.log_rat_reduce_isNear 320058221696 16000000 14 640116443392 524288000000 6697764 33554432 24973259072661432 36028797018963968 8737864 1000000000000000 rfl rfl rfl rfl (Ns60p2329 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p2331 := BSN.arctan_dyadic_bound_f 1000 565736 1 0 4194304 1092233 0 1 1 0 1 1 7413 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 565736) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 565736) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz1083 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 565736)))

noncomputable abbrev qz866 := qz1083

noncomputable abbrev qz570 := qz866

noncomputable def Ns60p2332 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz570 884279719003555 562949953421312 1 2000000000000000 7413 4194304 1 1092233 3704764814530774564864 883284762985891 562949953421312 2000000001092233 2184466000000000000000 qz15 (Ns60p2331 rfl) rfl rfl 

noncomputable abbrev qz867 := (@HMul.hMul Real Real Real qz5 qz12 qz1081)

noncomputable abbrev qz571 := qz867

noncomputable abbrev qz868 := qz1081

noncomputable abbrev qz572 := qz868

noncomputable abbrev qz869 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 282868 4000) qz1080)

noncomputable def Ns60p2333 := @Enclosure.Real.IsNear.subLit_ff_p qz869 qz571 1577065546629863924733 2251799813685248000 4419813040676087427 546116500000000000000000 883284762985891 2251799813685248 2000000001092233 8737864000000000000000 Ns60p2324 1576182261866878033733 2251799813685248000 9089626081488703979 1092233000000000000000000 (Ns60p2330 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz12 qz572 1 4 0 1 883284762985891 562949953421312 2000000001092233 2184466000000000000000 883284762985891 2251799813685248 2000000001092233 8737864000000000000000 qz335 Ns60p2332 rfl) 

noncomputable def Ns60p2334 := @Ns60p2319 Ns60p2313 Ns60p2314 4684104953771508609249 Ns60p72 (@Ns60p2321 4684104953771508609249 Ns60p72 (Ns60p2323 (Ns60p2333 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 282868 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz1082 (Real.log Real.pi) 282868 2000 0 1 38410761 33554432 1 16777216 2716293785637 16777216000 70717 8388608000 (Enclosure.Real.IsNear.const Bool.false 282868 2000) RS061to078.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns60p2315 Ns60p2316) 

noncomputable def Ns60p2335 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz231) Bool.false Ns60p2313 Ns60p2314 4684104953771508609249 Ns60p72 3327150269 8388608 141 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz231) (@HAdd.hAdd Real Real Real qz336 qz567 (Enclosure.sfrac Bool.true Ns60p2315 Ns60p2316)) Bool.false Ns60p2313 Ns60p2314 4684104953771508609249 Ns60p72 Ns60p2317 (Ns60p2334 rfl rfl)) 

noncomputable def Ns60p2336 := nat_lit 4880477438233990453722673773629658748890725812933105045711917468964686022916184211456 

noncomputable def Ns60p2337 := nat_lit 1111602149939871581960455419589325151808073990643541461365309167032098422024830976 

noncomputable def Ns60p2338 := nat_lit 14639209110402091618004100410049797596368561290818028054213021788559993871904502972416 

noncomputable def Ns60p2339 := BSN.cos_dyadic_bound_f 13512747832 17179869184 3 2 8388608 2186600 Ns60p2336 Ns60p1788 Ns60p2337 Ns60p2338 Ns60p1791 Ns60p2337 5924832 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 13512747832) qz769 0 2 Ns60p2336 Ns60p1788 Ns60p2337 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 13512747832) qz770 0 2 Ns60p2338 Ns60p1791 Ns60p2337 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2340 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz231) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3327150269) qz337) Bool.false 3327150269 8388608 141 8388608 Bool.false 5924832 8388608 1 1092233 (Ns60p2335 rfl) (Enclosure.sfrac_false_div 3327150269 8388608) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3327150269) qz337) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 950875095390814405132288) qz657) 226375608064910080 72057594037927936 Bool.false 5924832 8388608 63 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q0 3327150269 8388608 226375608064910080 72057594037927936 63 950875095390814405132288 Ns60p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 5924832 8388608 950875095390814405132288 Ns60p84 13512747832 17179869184 2186600 2184466 (Ns60p2339 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p2341 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz231) Bool.false Ns60p2313 Ns60p2314 4684104953771508609249 Ns60p72 26617202155 67108864 1125 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz231) (@HAdd.hAdd Real Real Real qz336 qz567 (Enclosure.sfrac Bool.true Ns60p2315 Ns60p2316)) Bool.false Ns60p2313 Ns60p2314 4684104953771508609249 Ns60p72 Ns60p2317 (Ns60p2334 rfl rfl)) 

noncomputable def Ns60p2342 := Ns60p2312 25191 BSN.abs_quadSignPos (BSN.cos_quad_nat3 127 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 58770891 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 54 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 33854939 67108864) qz234 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 1) Bool.false 185151 262144 162393461 9162314481664 47398656 67108864 1190 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz231)) Bool.false 185151 262144 162393461 9162314481664 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz231) qz231) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz231)) Bool.false 5924832 8388608 162393461 9162314481664 185151 262144 162393461 9162314481664 (Ns60p2340 rfl rfl) rfl)) rfl) (Ns60p2341 rfl) RS061to078.d7 

noncomputable def Ns60p2343 := nat_lit 1613091741159347359430010775912149403366905801920082421377025370625 

noncomputable def Ns60p2344 := nat_lit 691103751688161332375608235262068275459420273447881574866414081 

noncomputable def Ns60p2345 := nat_lit 4223645154105081299207134380722347945895914229347966914390044633601 

noncomputable def Ns60p2346 := BSN.sin_dyadic_bound_f 71604927 67108864 3 2 67108864 33554432 Ns60p2343 Ns60p119 Ns60p2344 Ns60p2345 Ns60p122 Ns60p2344 58770891 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 71604927) qz339 0 2 Ns60p2343 Ns60p119 Ns60p2344 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 71604927) (BSN.sinOddQ 67108864) 0 2 Ns60p2345 Ns60p122 Ns60p2344 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2347 := nat_lit 815372083295761800850542141523392420722047059404989801207226586241 

noncomputable def Ns60p2348 := nat_lit 571800696924591029447125193788244883902234068439757088908792961 

noncomputable def Ns60p2349 := nat_lit 2444972648493436220492732174182600772398336710078089889443862172801 

noncomputable def Ns60p2350 := BSN.cos_dyadic_bound_f 69928721 67108864 3 2 67108864 33554432 Ns60p2347 Ns60p103 Ns60p2348 Ns60p2349 Ns60p106 Ns60p2348 33854939 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 69928721) qz338 0 2 Ns60p2347 Ns60p103 Ns60p2348 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 69928721) (BSN.cosOddQ 67108864) 0 2 Ns60p2349 Ns60p106 Ns60p2348 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2351 := nat_lit 549916074890307430511703294616264277420903435362685882394268973801601582327046295962856304310480640625 

noncomputable def Ns60p2352 := nat_lit 298703700316434437001427558393384278183135925809131931163135958865142169770631004402383056640625 

noncomputable def Ns60p2353 := nat_lit 3331801337406430595487435471156359102297495556682545067273210744088790610029198998992569884217962240625 

noncomputable def Ns60p2354 := BSN.cos_dyadic_bound_f 90421155 67108864 4 3 67108864 33554432 Ns60p2351 Ns60p219 Ns60p2352 Ns60p2353 Ns60p222 Ns60p2352 14868782 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 90421155) qz338 0 3 Ns60p2351 Ns60p219 Ns60p2352 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 90421155) (BSN.cosOddQ 67108864) 0 3 Ns60p2353 Ns60p222 Ns60p2352 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2355 := nat_lit 1390973403608518215144109756176 

noncomputable def Ns60p2356 := BSN.sin_dyadic_bound_f 34342326 67108864 2 1 67108864 33554432 Ns60p2355 Ns60p115 Ns60p2355 Ns60p2355 Ns60p116 Ns60p2355 32862911 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 34342326) qz339 0 1 Ns60p2355 Ns60p115 Ns60p2355 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 34342326) (BSN.sinOddQ 67108864) 0 1 Ns60p2355 Ns60p116 Ns60p2355 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2357 := Ns60p2310 42889 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 2 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 14868782 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 37 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 32862911 67108864) qz234 rfl rfl (Ns60p2342 RS061to078.d9 RS061to078.d11 RS061to078.d13 RS061to078.d17 (Ns60p2346 rfl rfl) (Ns60p2350 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns60p2341 rfl) RS061to078.d19 RS061to078.d21 RS061to078.d23 RS061to078.d25 RS061to078.d17 (Ns60p2354 rfl rfl) (Ns60p2356 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns60p2358 := nat_lit 77206010065134460025914245376 

noncomputable def Ns60p2359 := BSN.cos_dyadic_bound_f 16669124 67108864 2 1 67108864 33554432 Ns60p2358 Ns60p630 Ns60p2358 Ns60p2358 Ns60p631 Ns60p2358 65049269 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 16669124) qz338 0 1 Ns60p2358 Ns60p630 Ns60p2358 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 16669124) (BSN.cosOddQ 67108864) 0 1 Ns60p2358 Ns60p631 Ns60p2358 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2360 := Ns60p2308 Bool.false 47278668 42889 Bool.true 16669124 3537118876014220 1 Bool.false 65049269 Bool.true Bool.false 20722414 50634 BSN.abs_quadSignNeg qz1024 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 65049269 67108864) qz234 rfl (Ns60p2357 rfl rfl) (Ns60p2341 rfl) RS061to078.d27 RS061to078.d29 RS061to078.d17 (Ns60p2359 rfl rfl) rfl 

noncomputable def Ns60p2361 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 6) 20722414 67108864 50634 67108864 20722414 67108864 50634 67108864 2781315325755392 10361207 16777216 25317 16777216 (Ns60p2360 rfl rfl rfl rfl) 

noncomputable def Ns60p2362 := @Enclosure.Real.IsNear.mulLit_ff qz1079 (Zeta.RiemannSiegel.correction qz233) 1619231 4194304 1 4194304 2038883296899 4398046511104 235193663822631 1200922883740663808 3301423039721064669 18446744073709551616 

noncomputable abbrev qz1084 := (@HPow.hPow Real Real Real qz326 qz232 qz8)

noncomputable def Ns60p2363 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz1084 1 1 0 1 1619231 4194304 1 4194304 1619231 4194304 1 4194304 

noncomputable def Ns60p2364 := @Enclosure.Real.IsNear.sqrt_image qz232 94413488813 2097152000 70717 2097152000 28142444 28142466 4194304 (@Enclosure.Real.IsNear.of_eq qz232 (@HMul.hMul Real Real Real qz5 qz231 qz3) Bool.false 94413488813 2097152000 70717 2097152000 (BSN.t_div_two_pi_mk qz231 282868 1000 qz234) (@Enclosure.Real.IsNear.mulLit_ff qz231 qz3 282868 1000 0 1 1335089 8388608 1 8388608 94413488813 2097152000 70717 2097152000 (Enclosure.Real.IsNear.const Bool.false 282868 1000) RS061to078.d32 rfl)) 

noncomputable abbrev qz870 := (Real.sqrt qz1078)

noncomputable abbrev qz573 := qz870

noncomputable abbrev qz235 := qz573

noncomputable def Ns60p2365 := @Enclosure.Real.IsNear.sqrt_image qz235 28142455 4194304 11 4194304 10864527 10864533 4194304 (@Enclosure.Real.IsNear.recentre' qz235 Bool.false 56284910 8388608 22 8388608 28142455 4194304 11 4194304 (Ns60p2364 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns60p2366 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz235) 5432265 2097152 3 4194304 1619230 1619232 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz235) Bool.false 21729060 8388608 6 8388608 5432265 2097152 3 4194304 (Ns60p2365 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns60p2367 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz235)) Bool.false 3238462 8388608 2 8388608 1619231 4194304 1 4194304 (Ns60p2366 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz236 := (Real.cos (@HMul.hMul Real Real Real qz323 qz320 qz566))

noncomputable abbrev qz574 := (@HSub.hSub Real Real Real qz647 (@HMul.hMul Real Real Real qz644 qz863 qz863) qz863)

noncomputable abbrev qz237 := (@HMul.hMul Real Real Real qz323 qz320 (@HSub.hSub Real Real Real qz327 qz574 qz344))

noncomputable def Ns60p2368 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz233) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz236) (Real.cos qz237)) Bool.false 2038883296899 

noncomputable def Ns60p2369 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz236) (Real.cos qz237) 4184067 1048576 73 

noncomputable abbrev qz1085 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz236))

noncomputable def Ns60p2370 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz236) (@Neg.neg Real Real.instNeg qz1085) Bool.true 4184067 1048576 73 262144 (BSN.inv_eq_neg_inv_neg qz236) 

noncomputable def Ns60p2371 := @Enclosure.Real.IsNear.recentre' qz1085 Bool.false 33472536 8388608 2336 8388608 4184067 1048576 

noncomputable def Ns60p2372 := @Enclosure.Real.IsNear.recentre' qz236 Bool.true 2102283 8388608 160208995 9162314481664 2102283 8388608 160208995 9162314481664 

noncomputable abbrev qz238 := (@HMul.hMul Real Real Real qz323 qz320 qz566)

noncomputable def Ns60p2373 := @Enclosure.Real.IsNear.cos_image qz238 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4675681) qz714) Bool.false 4675681 1048576 139 8388608 Bool.true 2102283 8388608 1 

noncomputable def Ns60p2374 := nat_lit 296846829525053565601378189 

noncomputable def Ns60p2375 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz233 884279719003555 140737488355328 1 500000000000000 2976631 4194304 11 4194304 2632174424257270923205 590295810358705651712 Ns60p2374 

noncomputable def Ns60p2376 := @Enclosure.Real.IsNear.subLit_ff_p qz235 qz1 28142455 4194304 11 4194304 6 1 0 1 2976631 2976631 4194304 11 

noncomputable def Ns60p2377 := @Ns60p2376 4194304 (@Enclosure.Real.IsNear.recentre' qz235 Bool.false 56284910 8388608 22 8388608 28142455 4194304 11 4194304 (Ns60p2364 rfl rfl rfl rfl rfl rfl) rfl) qz345 

noncomputable def Ns60p2378 := @Enclosure.Real.IsNear.recentre' qz238 Bool.false 2632174424257270923205 590295810358705651712 Ns60p2374 Ns60p1589 4675681 1048576 139 8388608 (@Ns60p2375 Ns60p1589 RS061to078.d31 (Ns60p2377 rfl rfl) rfl) 

noncomputable def Ns60p2379 := nat_lit 38479370538440985654007463797302241013220881163236374243735490816822982760641776190625 

noncomputable def Ns60p2380 := nat_lit 68884612350939453725057259510627046414686469939749566444985250737956041123875390625 

noncomputable def Ns60p2381 := nat_lit 115300342390621078054572276872885468946833270549829623598316501948993036199677577790625 

noncomputable def Ns60p2382 := BSN.cos_dyadic_bound_f 22634206685 17179869184 3 2 8388608 2186600 Ns60p2379 Ns60p1788 Ns60p2380 Ns60p2381 Ns60p1791 Ns60p2380 2102283 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 22634206685) qz769 0 2 Ns60p2379 Ns60p1788 Ns60p2380 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 22634206685) qz770 0 2 Ns60p2381 Ns60p1791 Ns60p2380 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2383 := @Ns60p2373 1092233 (Ns60p2378 rfl) (Enclosure.sfrac_false_div 4675681 1048576) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4675681) qz714) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 199092587493163555356672) qz756) 226375608064910080 72057594037927936 Bool.false 2102283 8388608 0 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q2 4675681 1048576 226375608064910080 72057594037927936 0 199092587493163555356672 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 2102283 8388608 199092587493163555356672 151115727451828646838272 22634206685 17179869184 2186600 2184466 (Ns60p2382 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p2384 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz236) 2102283 8388608 160208995 9162314481664 16735100 16737436 4194304 (@Enclosure.Real.IsNear.neg qz236 Bool.true 2102283 8388608 160208995 9162314481664 (Ns60p2372 (Ns60p2383 rfl rfl) rfl)) 

noncomputable def Ns60p2385 := Ns60p2370 (@Enclosure.Real.IsNear.neg qz1085 Bool.false 4184067 1048576 73 262144 (@Ns60p2371 73 262144 (Ns60p2384 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p2386 := @Enclosure.Real.IsNear.recentre' (Real.cos qz237) Bool.true 487297 4194304 

noncomputable def Ns60p2387 := @Enclosure.Real.IsNear.cos_image qz237 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 14153593)) qz337) Bool.true 14153593 8388608 

noncomputable def Ns60p2388 := nat_lit 4177403560959526495652545645 

noncomputable def Ns60p2389 := nat_lit 3012276059592469917901513243942437 

noncomputable def Ns60p2390 := @Enclosure.Real.IsNear.recentre' qz237 Bool.true Ns60p2388 Ns60p327 Ns60p2389 

noncomputable abbrev qz239 := (@HSub.hSub Real Real Real qz327 qz574 qz344)

noncomputable def Ns60p2391 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz239 884279719003555 140737488355328 1 500000000000000 4724074827439 

noncomputable abbrev qz240 := qz574

noncomputable def Ns60p2392 := @Enclosure.Real.IsNear.subLit_tf qz240 qz23 3624563199663 17592186044416 111623347 17592186044416 1 16 

noncomputable abbrev qz575 := (@HMul.hMul Real Real Real qz644 qz863 qz863)

noncomputable abbrev qz241 := qz575

noncomputable def Ns60p2393 := @Enclosure.Real.IsNear.subLit_ff_n qz241 qz233 8860332110161 17592186044416 65486003 17592186044416 2976631 4194304 11 4194304 

noncomputable def Ns60p2394 := @Enclosure.Real.IsNear.mulLit_ff qz233 qz233 2976631 4194304 11 4194304 2976631 4194304 11 4194304 8860332110161 17592186044416 

noncomputable def Ns60p2395 := nat_lit 19733454241841281711306003519496363193046516504366721612108983778388533755205537769249960481 

noncomputable def Ns60p2396 := nat_lit 64624981947526657319939263299343069382121349855065806135135343165127625804952029229601 

noncomputable def Ns60p2397 := nat_lit 119332811890448440223311062828431000963090226712075801981793273603763283432935628122449900065 

noncomputable def Ns60p2398 := BSN.cos_dyadic_bound_t 14153593 8388608 4 3 4194304 1092233 Ns60p2395 Ns60p274 Ns60p2396 Ns60p2397 Ns60p277 Ns60p2396 487297 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 14153593) (BSN.cosEvenQ 8388608) 0 3 Ns60p2395 Ns60p274 Ns60p2396 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 14153593) (BSN.cosOddQ 8388608) 0 3 Ns60p2397 Ns60p277 Ns60p2396 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2399 := @Ns60p2386 23461181 572644655104 487297 4194304 23461181 572644655104 (@Ns60p2387 21 524288 Bool.true 487297 4194304 1 1092233 (@Ns60p2390 Ns60p1701 14153593 8388608 21 524288 (@Ns60p2391 17592186044416 111623347 17592186044416 Ns60p2388 Ns60p327 Ns60p2389 Ns60p1701 RS061to078.d31 (@Ns60p2392 0 1 75585197239024 4724074827439 17592186044416 111623347 17592186044416 (@Ns60p2393 15202519926599319552 3624563199663 17592186044416 111623347 17592186044416 (@Ns60p2394 65486003 17592186044416 (Ns60p2377 rfl rfl) (Ns60p2377 rfl rfl) rfl) (Ns60p2377 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 14153593 8388608) (BSN.cos_neg_of_bound 14153593 8388608 Bool.true 487297 4194304 1 1092233 (Ns60p2398 rfl rfl)) rfl rfl) 

noncomputable def Ns60p2400 := @Ns60p2362 1525559362255407643035 Ns60p2305 (Ns60p2363 qz25 (@Enclosure.Real.IsNear.of_eq qz1084 (@Inv.inv Real Real.instInv (Real.sqrt qz235)) Bool.false 1619231 4194304 1 4194304 (BSN.rpow_neg_quarter_mk qz232 (BSN.t_div_two_pi_nonneg qz231 282868 1000 qz234)) Ns60p2367) rfl) (@Ns60p2368 4398046511104 235193663822631 1200922883740663808 (BSN.correction_mk qz233 (BSN.cos_two_pi_p_ne_zero_mk qz231 282868 1000 6 qz234 rfl rfl (@BSN.floor_sqrt_eq_dec qz231 282868 1000 6 qz234 rfl rfl rfl))) (@Ns60p2369 262144 487297 4194304 23461181 572644655104 2038883296899 4398046511104 235193663822631 1200922883740663808 Ns60p2385 (Ns60p2399 rfl) rfl)) 

noncomputable def Ns60p2401 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz231) (hardyZApproximantRS₀ qz231) Bool.false 8090844534573020963 18446744073709551616 31929324009917793270171 Ns60p2305 (@Eq.refl Real (hardyZApproximantRS₀ qz231)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz231) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz231) qz231 6) (@HMul.hMul Real Real Real qz5 qz1079 (Zeta.RiemannSiegel.correction qz233))) Bool.false 8090844534573020963 18446744073709551616 31929324009917793270171 Ns60p2305 (BSN.hardyZApproximantRS₀_eq qz231 6 (@BSN.floor_sqrt_eq_dec qz231 282868 1000 6 qz234 rfl rfl rfl)) (@Ns60p2307 8090844534573020963 18446744073709551616 31929324009917793270171 Ns60p2305 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz231) qz231 6) (@HAdd.hAdd Real Real Real qz336 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz231) qz231 6)) Bool.false 10361207 16777216 25317 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz231) qz231 6) (Ns60p2361 (Ns60p2360 rfl rfl rfl rfl) rfl rfl)) (Ns60p2400 rfl) rfl rfl)) 

theorem RS061to078.d63 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz231) Bool.false 8090844534573020963 18446744073709551616 31929324009917793270171 Ns60p2305 := Ns60p2401 

noncomputable def Ns60p2402 := nat_lit 20059616241384329253486592 

noncomputable abbrev qz1086 := (Enclosure.sfrac Bool.false 283692 1000)

noncomputable abbrev qz871 := qz1086

noncomputable abbrev qz576 := qz871

noncomputable abbrev qz242 := qz576

noncomputable abbrev qz1087 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 283692 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz872 := qz1087

noncomputable abbrev qz577 := qz872

noncomputable abbrev qz243 := qz577

noncomputable abbrev qz873 := (@HSub.hSub Real Real Real qz920 (Real.sqrt qz1087) qz914)

noncomputable abbrev qz578 := qz873

noncomputable abbrev qz244 := qz578

noncomputable abbrev qz1088 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz326 qz243 qz8))

noncomputable def Ns60p2403 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz242) qz242 6) (@HMul.hMul Real Real Real qz5 qz1088 (Zeta.RiemannSiegel.correction qz244)) 14345959 16777216 50785 33554432 209799504642259563 1152921504606846976 4212810087719753838147 Ns60p1233 Ns60p2402 

noncomputable def Ns60p2404 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz242) qz242 Real.cos BSN.quadSignNeg 5 6 283692 1000 70 67108864 33554432 1125899906842624 Bool.false 26722504461 1128 120242927 63 27397080 8 

noncomputable def Ns60p2405 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz242) qz242 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 283692 1000 3 37 67108864 33554432 1125899906842624 Bool.false 26722504461 1128 

noncomputable def Ns60p2406 := Ns60p2405 93032624 62 33554424 8 108007536 62 30011992 8 Bool.true 434125 25268 Bool.false 13650221 Bool.true 18038230 3537118876014220 1 Bool.false 13556289 Bool.false Bool.false 17821807 Bool.true Bool.true 1626136 

noncomputable def Ns60p2407 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz242) qz242 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 283692 1000 128 55 67108864 33554432 1125899906842624 Bool.false 26722504461 1128 

noncomputable def Ns60p2408 := Ns60p2407 46516304 62 47453136 16 73726608 62 38745320 8 Bool.true 47428328 1198 Bool.false 33163442 Bool.false 9065945 3537118876014220 1 Bool.false 59080018 Bool.false Bool.false 9038394 Bool.false Bool.true 434125 

noncomputable def Ns60p2409 := nat_lit 2852946922670615527184542592441241062072105684087 

noncomputable def Ns60p2410 := nat_lit 7164673779376559602999291747260085008387276800 

noncomputable def Ns60p2411 := nat_lit 882023385962836479964676751360000 

noncomputable def Ns60p2412 := nat_lit 1501340046860022387164496484336926720 

noncomputable abbrev qz245 := (@Eq.refl Real qz576)

noncomputable def Ns60p2413 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz242 283692 1000 321925603456 16000000 567384 4000 2000 Ns60p2411 Ns60p2412 qz245 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns60p2414 := nat_lit 269237850514763701232975304007050010911298826081748910080 

noncomputable abbrev qz1089 := (Real.log (Enclosure.sfrac Bool.false 321925603456 16000000))

noncomputable abbrev qz1090 := (@HSub.hSub Real Real Real qz11 qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 567384))))

noncomputable abbrev qz874 := (@HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 283692 4000) qz1089) (@HMul.hMul Real Real Real qz5 qz12 qz1090))

noncomputable abbrev qz1091 := (Enclosure.sfrac Bool.false 283692 2000)

noncomputable abbrev qz579 := (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 qz874 qz1091) (@HMul.hMul Real Real Real qz5 qz1091 (Real.log Real.pi)))

noncomputable def Ns60p2415 := @Enclosure.Real.IsNear.addLit_ft_p qz579 (Enclosure.sfrac Bool.true Ns60p2411 Ns60p2412) 179331956345187264439 450359962737049600 4697563409594998445831 Ns60p72 Ns60p2411 Ns60p2412 0 1 Ns60p2414 

noncomputable def Ns60p2416 := nat_lit 15043454836528886479711109120000 

noncomputable abbrev qz580 := (@HSub.hSub Real Real Real qz11 qz874 qz1091)

noncomputable def Ns60p2417 := @Enclosure.Real.IsNear.subLit_ff_p qz580 (@HMul.hMul Real Real Real qz5 qz1091 (Real.log Real.pi)) 1262296575659520722579 2251799813685248000 9115376084638703951 1092233000000000000000000 2724206402403 16777216000 70923 8388608000 Ns60p2416 179331956345187264439 450359962737049600 

noncomputable def Ns60p2418 := nat_lit 2524593151319041445158000 

noncomputable abbrev qz581 := qz874

noncomputable def Ns60p2419 := @Enclosure.Real.IsNear.subLit_ff_p qz581 qz1091 1581705372031518410387 2251799813685248000 9115376084638703951 1092233000000000000000000 283692 2000 0 1 Ns60p2418 1262296575659520722579 2251799813685248000 9115376084638703951 1092233000000000000000000 

noncomputable def Ns60p2420 := nat_lit 3561683862045529029389357785311870976 

noncomputable def Ns60p2421 := nat_lit 11979834708167026150473728 

noncomputable def Ns60p2422 := nat_lit 4168472386923843057127238681147708809518117944978992391347923518887034880 

noncomputable def Ns60p2423 := nat_lit 14648838999949296067367776624847222366290957728416674714666056365899776 

noncomputable def Ns60p2424 := nat_lit 684694147690597753260453005167026734504483448657243007268778147840 

noncomputable def Ns60p2425 := BSN.log_dyadic_bound 59781603456 584069603456 4 3 Ns60p2422 33554432 8737864 Ns60p2423 Ns60p2424 6892969 643851206912 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 59781603456) (BSN.artanhQ 584069603456) 0 3 Ns60p2423 Ns60p2422 Ns60p2424 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz875 := qz1089

noncomputable def Ns60p2426 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 283692 4000) qz875 283692 4000 0 1 22314181007755969 2251799813685248 62500007645631 546116500000000000000 1582588659613076589387 2251799813685248000 94312511537257179 11619500000000000000000 (Enclosure.Real.IsNear.const Bool.false 283692 4000) (BSN.isNear_log_sfrac 321925603456 16000000 22314181007755969 2251799813685248 62500007645631 546116500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 321925603456) qz650)) Bool.false Ns60p2421 Ns60p84 1000000122330096 8737864000000000000000 22314181007755969 2251799813685248 62500007645631 546116500000000000000 (BSN.log_rat_reduce_isNear 321925603456 16000000 14 643851206912 524288000000 6892969 33554432 24973259072661432 36028797018963968 8737864 1000000000000000 rfl rfl rfl rfl (Ns60p2425 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p2427 := BSN.arctan_dyadic_bound_f 1000 567384 1 0 4194304 1092233 0 1 1 0 1 1 7392 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 567384) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 567384) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz1092 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 567384)))

noncomputable abbrev qz876 := qz1092

noncomputable abbrev qz582 := qz876

noncomputable def Ns60p2428 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz582 884279719003555 562949953421312 1 2000000000000000 7392 4194304 1 1092233 3704776636479796412416 883287581558179 562949953421312 2000000001092233 2184466000000000000000 qz15 (Ns60p2427 rfl) rfl rfl 

noncomputable abbrev qz877 := (@HMul.hMul Real Real Real qz5 qz12 qz1090)

noncomputable abbrev qz583 := qz877

noncomputable abbrev qz878 := qz1090

noncomputable abbrev qz584 := qz878

noncomputable abbrev qz879 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 283692 4000) qz1089)

noncomputable def Ns60p2429 := @Enclosure.Real.IsNear.subLit_ff_p qz879 qz583 1582588659613076589387 2251799813685248000 94312511537257179 11619500000000000000000 883287581558179 2251799813685248 2000000001092233 8737864000000000000000 Ns60p2420 1581705372031518410387 2251799813685248000 9115376084638703951 1092233000000000000000000 (Ns60p2426 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz12 qz584 1 4 0 1 883287581558179 562949953421312 2000000001092233 2184466000000000000000 883287581558179 2251799813685248 2000000001092233 8737864000000000000000 qz335 Ns60p2428 rfl) 

noncomputable def Ns60p2430 := @Ns60p2415 Ns60p2409 Ns60p2410 4697563409594998445831 Ns60p72 (@Ns60p2417 4697563409594998445831 Ns60p72 (Ns60p2419 (Ns60p2429 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 283692 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz1091 (Real.log Real.pi) 283692 2000 0 1 38410761 33554432 1 16777216 2724206402403 16777216000 70923 8388608000 (Enclosure.Real.IsNear.const Bool.false 283692 2000) RS061to078.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns60p2411 Ns60p2412) 

noncomputable def Ns60p2431 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz242) Bool.false Ns60p2409 Ns60p2410 4697563409594998445831 Ns60p72 3340313057 8388608 71 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz242) (@HAdd.hAdd Real Real Real qz336 qz579 (Enclosure.sfrac Bool.true Ns60p2411 Ns60p2412)) Bool.false Ns60p2409 Ns60p2410 4697563409594998445831 Ns60p72 Ns60p2413 (Ns60p2430 rfl rfl)) 

noncomputable def Ns60p2432 := nat_lit 8709609622614716698081643755590714028213495199341165759969595008139467247863780945345 

noncomputable def Ns60p2433 := nat_lit 1092863671649775361275980413768472593458157829494258399405665751064997868935130561 

noncomputable def Ns60p2434 := nat_lit 22809112946617777430105096343972435403979269457026729143464187276768308985950674169281 

noncomputable def Ns60p2435 := BSN.sin_dyadic_bound_f 13484062247 17179869184 3 2 8388608 2186600 Ns60p2432 Ns60p94 Ns60p2433 Ns60p2434 Ns60p97 Ns60p2433 5928541 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 13484062247) qz655 0 2 Ns60p2432 Ns60p94 Ns60p2433 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 13484062247) qz656 0 2 Ns60p2434 Ns60p97 Ns60p2433 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2436 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz242) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3340313057) qz337) Bool.false 3340313057 8388608 71 4194304 Bool.true 5928541 8388608 1 1092233 (Ns60p2431 rfl) (Enclosure.sfrac_false_div 3340313057 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3340313057) qz337) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 948856526795263950454784) qz657) 226375608064910080 72057594037927936 Bool.false 5928541 8388608 63 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q1 3340313057 8388608 226375608064910080 72057594037927936 63 948856526795263950454784 Ns60p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 5928541 8388608 948856526795263950454784 Ns60p84 13484062247 17179869184 2186600 2184466 (Ns60p2435 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p2437 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz242) Bool.false Ns60p2409 Ns60p2410 4697563409594998445831 Ns60p72 26722504461 67108864 1128 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz242) (@HAdd.hAdd Real Real Real qz336 qz579 (Enclosure.sfrac Bool.true Ns60p2411 Ns60p2412)) Bool.false Ns60p2409 Ns60p2410 4697563409594998445831 Ns60p72 Ns60p2413 (Ns60p2430 rfl rfl)) 

noncomputable def Ns60p2438 := Ns60p2408 25268 BSN.abs_quadSignPos (BSN.cos_quad_nat0 128 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 59080018 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat3 55 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 9038394 67108864) qz245 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz242) qz242 1) Bool.true 5928541 8388608 81742847 4581157240832 47428328 67108864 1198 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz242) qz242 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz242)) Bool.true 5928541 8388608 81742847 4581157240832 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz242) qz242) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz242)) Bool.true 5928541 8388608 81742847 4581157240832 5928541 8388608 81742847 4581157240832 (Ns60p2436 rfl rfl) rfl)) rfl) (Ns60p2437 rfl) RS061to078.d7 

noncomputable def Ns60p2439 := nat_lit 41217594668503979919161647323280915264135148014136642672946954496 

noncomputable def Ns60p2440 := nat_lit 1463109376718423596182737373311308358424000082264903827702016 

noncomputable def Ns60p2441 := nat_lit 123649857786758502910292576495096123175688596042245398211185459456 

noncomputable def Ns60p2442 := BSN.cos_dyadic_bound_f 33163442 67108864 3 2 67108864 33554432 Ns60p2439 Ns60p103 Ns60p2440 Ns60p2441 Ns60p106 Ns60p2440 59080018 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 33163442) qz338 0 2 Ns60p2439 Ns60p103 Ns60p2440 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 33163442) (BSN.cosOddQ 67108864) 0 2 Ns60p2441 Ns60p106 Ns60p2440 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2443 := nat_lit 6755419452024632107986150625 

noncomputable def Ns60p2444 := BSN.sin_dyadic_bound_f 9065945 67108864 2 1 67108864 33554432 Ns60p2443 Ns60p115 Ns60p2443 Ns60p2443 Ns60p116 Ns60p2443 9038394 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 9065945) qz339 0 1 Ns60p2443 Ns60p115 Ns60p2443 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 9065945) (BSN.sinOddQ 67108864) 0 1 Ns60p2443 Ns60p116 Ns60p2443 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2445 := nat_lit 34718322339930152682196043281 

noncomputable def Ns60p2446 := BSN.sin_dyadic_bound_f 13650221 67108864 2 1 67108864 33554432 Ns60p2445 Ns60p115 Ns60p2445 Ns60p2445 Ns60p116 Ns60p2445 13556289 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 13650221) qz339 0 1 Ns60p2445 Ns60p115 Ns60p2445 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 13650221) (BSN.sinOddQ 67108864) 0 1 Ns60p2445 Ns60p116 Ns60p2445 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2447 := nat_lit 105870674685050677641782410000 

noncomputable def Ns60p2448 := BSN.sin_dyadic_bound_f 18038230 67108864 2 1 67108864 33554432 Ns60p2447 Ns60p115 Ns60p2447 Ns60p2447 Ns60p116 Ns60p2447 17821807 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 18038230) qz339 0 1 Ns60p2447 Ns60p115 Ns60p2447 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 18038230) (BSN.sinOddQ 67108864) 0 1 Ns60p2447 Ns60p116 Ns60p2447 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2449 := Ns60p2406 43017 BSN.abs_quadSignPos (BSN.cos_quad_nat3 3 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 13556289 67108864) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 37 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 17821807 67108864) qz245 rfl rfl (Ns60p2438 RS061to078.d9 RS061to078.d11 RS061to078.d13 RS061to078.d17 (Ns60p2442 rfl rfl) (Ns60p2444 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns60p2437 rfl) RS061to078.d19 RS061to078.d21 RS061to078.d23 RS061to078.d25 RS061to078.d17 (Ns60p2446 rfl rfl) (Ns60p2448 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns60p2450 := nat_lit 11911452301278579923612010000 

noncomputable def Ns60p2451 := BSN.cos_dyadic_bound_f 10446990 67108864 2 1 67108864 33554432 Ns60p2450 Ns60p630 Ns60p2450 Ns60p2450 Ns60p631 Ns60p2450 66297351 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 10446990) qz338 0 1 Ns60p2450 Ns60p630 Ns60p2450 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 10446990) (BSN.cosOddQ 67108864) 0 1 Ns60p2450 Ns60p631 Ns60p2450 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2452 := Ns60p2404 Bool.true 1626136 43017 Bool.true 10446990 3537118876014220 1 Bool.false 66297351 Bool.true Bool.true 28691918 50785 BSN.abs_quadSignNeg qz1024 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66297351 67108864) qz245 rfl (Ns60p2449 rfl rfl) (Ns60p2437 rfl) RS061to078.d27 RS061to078.d29 RS061to078.d17 (Ns60p2451 rfl rfl) rfl 

noncomputable def Ns60p2453 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz242) qz242 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz242) qz242 6) 28691918 67108864 50785 67108864 28691918 67108864 50785 67108864 3850964045922304 14345959 16777216 50785 33554432 (Ns60p2452 rfl rfl rfl rfl) 

noncomputable def Ns60p2454 := @Enclosure.Real.IsNear.mulLit_ff qz1088 (Zeta.RiemannSiegel.correction qz244) 809027 2097152 1 4194304 259323242169 549755813888 2600825203887093 9607383069925310464 209799504642259563 1152921504606846976 

noncomputable abbrev qz1093 := (@HPow.hPow Real Real Real qz326 qz243 qz8)

noncomputable def Ns60p2455 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz1093 1 1 0 1 809027 2097152 1 4194304 809027 2097152 1 4194304 

noncomputable def Ns60p2456 := @Enclosure.Real.IsNear.sqrt_image qz243 94688517147 2097152000 70923 2097152000 28183403 28183426 4194304 (@Enclosure.Real.IsNear.of_eq qz243 (@HMul.hMul Real Real Real qz5 qz242 qz3) Bool.false 94688517147 2097152000 70923 2097152000 (BSN.t_div_two_pi_mk qz242 283692 1000 qz245) (@Enclosure.Real.IsNear.mulLit_ff qz242 qz3 283692 1000 0 1 1335089 8388608 1 8388608 94688517147 2097152000 70923 2097152000 (Enclosure.Real.IsNear.const Bool.false 283692 1000) RS061to078.d32 rfl)) 

noncomputable abbrev qz880 := (Real.sqrt qz1087)

noncomputable abbrev qz585 := qz880

noncomputable abbrev qz246 := qz585

noncomputable def Ns60p2457 := @Enclosure.Real.IsNear.sqrt_image qz246 56366829 8388608 23 8388608 10872431 10872436 4194304 (@Enclosure.Real.IsNear.recentre' qz246 Bool.false 56366829 8388608 23 8388608 56366829 8388608 23 8388608 (Ns60p2456 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns60p2458 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz246) 21744867 8388608 5 8388608 1618053 1618055 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz246) Bool.false 21744867 8388608 5 8388608 21744867 8388608 5 8388608 (Ns60p2457 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns60p2459 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz246)) Bool.false 3236108 8388608 2 8388608 809027 2097152 1 4194304 (Ns60p2458 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz247 := (Real.cos (@HMul.hMul Real Real Real qz323 qz320 qz578))

noncomputable abbrev qz586 := (@HSub.hSub Real Real Real qz647 (@HMul.hMul Real Real Real qz644 qz873 qz873) qz873)

noncomputable abbrev qz248 := (@HMul.hMul Real Real Real qz323 qz320 (@HSub.hSub Real Real Real qz327 qz586 qz344))

noncomputable def Ns60p2460 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz244) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz247) (Real.cos qz248)) Bool.false 259323242169 

noncomputable def Ns60p2461 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz247) (Real.cos qz248) 5496349 1048576 33 

noncomputable abbrev qz1094 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz247))

noncomputable def Ns60p2462 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz247) (@Neg.neg Real Real.instNeg qz1094) Bool.true 5496349 1048576 33 65536 (BSN.inv_eq_neg_inv_neg qz247) 

noncomputable def Ns60p2463 := @Enclosure.Real.IsNear.recentre' qz1094 Bool.false 43970792 8388608 4224 8388608 5496349 1048576 

noncomputable def Ns60p2464 := @Enclosure.Real.IsNear.recentre' qz247 Bool.true 1600352 8388608 83927313 4581157240832 50011 262144 83927313 4581157240832 

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz323 qz320 qz578)

noncomputable def Ns60p2465 := @Enclosure.Real.IsNear.cos_image qz249 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1185005) (@Nat.cast Real Real.instNatCast 262144)) Bool.false 1185005 262144 73 4194304 Bool.true 1600352 8388608 1 

noncomputable def Ns60p2466 := nat_lit 620679734459854855509767393 

noncomputable def Ns60p2467 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz244 884279719003555 140737488355328 1 500000000000000 6035181 8388608 23 8388608 5336788158815594068455 1180591620717411303424 Ns60p2466 

noncomputable def Ns60p2468 := @Enclosure.Real.IsNear.subLit_ff_p qz246 qz1 56366829 8388608 23 8388608 6 1 0 1 6035181 6035181 8388608 23 

noncomputable def Ns60p2469 := @Ns60p2468 8388608 (@Enclosure.Real.IsNear.recentre' qz246 Bool.false 56366829 8388608 23 8388608 56366829 8388608 23 8388608 (Ns60p2456 rfl rfl rfl rfl rfl rfl) rfl) qz345 

noncomputable def Ns60p2470 := @Enclosure.Real.IsNear.recentre' qz249 Bool.false 5336788158815594068455 1180591620717411303424 Ns60p2466 Ns60p144 1185005 262144 73 4194304 (@Ns60p2467 Ns60p144 RS061to078.d31 (Ns60p2469 rfl rfl) rfl) 

noncomputable def Ns60p2471 := nat_lit 46180685142978902400802925069041119509016191915617177839492396607435960756718935475361 

noncomputable def Ns60p2472 := nat_lit 99146311651982457355181854062549585151056695769458318932937763112064867492641899681 

noncomputable def Ns60p2473 := nat_lit 138343762805632742287698411498998259356746462355312616880611314296083752535171522626721 

noncomputable def Ns60p2474 := BSN.cos_dyadic_bound_f 23688336861 17179869184 3 2 8388608 2186600 Ns60p2471 Ns60p1788 Ns60p2472 Ns60p2473 Ns60p1791 Ns60p2472 1600352 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 23688336861) qz769 0 2 Ns60p2471 Ns60p1788 Ns60p2472 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 23688336861) qz770 0 2 Ns60p2473 Ns60p1791 Ns60p2472 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2475 := @Ns60p2465 1092233 (Ns60p2470 rfl) (Enclosure.sfrac_false_div 1185005 262144) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1185005) (@Nat.cast Real Real.instNatCast 262144)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 52091203644694011576320) (@Nat.cast Real Real.instNatCast 37778931862957161709568)) 226375608064910080 72057594037927936 Bool.false 1600352 8388608 0 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q2 1185005 262144 226375608064910080 72057594037927936 0 52091203644694011576320 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1600352 8388608 52091203644694011576320 37778931862957161709568 23688336861 17179869184 2186600 2184466 (Ns60p2474 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p2476 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz247) 50011 262144 83927313 4581157240832 21983284 21987508 4194304 (@Enclosure.Real.IsNear.neg qz247 Bool.true 50011 262144 83927313 4581157240832 (Ns60p2464 (Ns60p2475 rfl rfl) rfl)) 

noncomputable def Ns60p2477 := Ns60p2462 (@Enclosure.Real.IsNear.neg qz1094 Bool.false 5496349 1048576 33 65536 (@Ns60p2463 33 65536 (Ns60p2476 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p2478 := @Enclosure.Real.IsNear.recentre' (Real.cos qz248) Bool.true 377448 4194304 

noncomputable def Ns60p2479 := @Enclosure.Real.IsNear.cos_image qz248 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 13932713)) qz337) Bool.true 13932713 8388608 

noncomputable def Ns60p2480 := nat_lit 16448844679240517656864820005 

noncomputable def Ns60p2481 := nat_lit 2539696468331036577699732658206557 

noncomputable def Ns60p2482 := @Enclosure.Real.IsNear.recentre' qz248 Bool.true Ns60p2480 Ns60p159 Ns60p2481 

noncomputable def Ns60p2483 := nat_lit 60446290980731458735308800000000000000 

noncomputable abbrev qz250 := (@HSub.hSub Real Real Real qz327 qz586 qz344)

noncomputable def Ns60p2484 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz250 884279719003555 140737488355328 1 500000000000000 18601404426391 

noncomputable abbrev qz251 := qz586

noncomputable def Ns60p2485 := @Enclosure.Real.IsNear.subLit_tf qz251 qz23 14203357915287 70368744177664 470556839 70368744177664 1 16 

noncomputable abbrev qz587 := (@HMul.hMul Real Real Real qz644 qz873 qz873)

noncomputable abbrev qz252 := qz587

noncomputable def Ns60p2486 := @Enclosure.Real.IsNear.subLit_ff_n qz252 qz244 36423409702761 70368744177664 277618855 70368744177664 6035181 8388608 23 8388608 

noncomputable def Ns60p2487 := @Enclosure.Real.IsNear.mulLit_ff qz244 qz244 6035181 8388608 23 8388608 6035181 8388608 23 8388608 36423409702761 70368744177664 

noncomputable def Ns60p2488 := nat_lit 18524723967598314883682732391085194517959878754434862369204369136004712213191587540964465761 

noncomputable def Ns60p2489 := nat_lit 53509179796064106491572231722434213371883813773146074295553083603404506842700932701281 

noncomputable def Ns60p2490 := nat_lit 112045206995847081175554441351979683286630144298896903507296464022465591267279576163215203425 

noncomputable def Ns60p2491 := BSN.cos_dyadic_bound_t 13932713 8388608 4 3 4194304 1092233 Ns60p2488 Ns60p274 Ns60p2489 Ns60p2490 Ns60p277 Ns60p2489 377448 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 13932713) (BSN.cosEvenQ 8388608) 0 3 Ns60p2488 Ns60p274 Ns60p2489 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 13932713) (BSN.cosOddQ 8388608) 0 3 Ns60p2490 Ns60p277 Ns60p2489 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2492 := @Ns60p2478 393946857 9162314481664 47181 524288 393946857 9162314481664 (@Ns60p2479 353 8388608 Bool.true 377448 4194304 1 1092233 (@Ns60p2482 Ns60p2483 13932713 8388608 353 8388608 (@Ns60p2484 70368744177664 470556839 70368744177664 Ns60p2480 Ns60p159 Ns60p2481 Ns60p2483 RS061to078.d31 (@Ns60p2485 0 1 297622470822256 18601404426391 70368744177664 470556839 70368744177664 (@Ns60p2486 119146401835039850496 14203357915287 70368744177664 470556839 70368744177664 (@Ns60p2487 277618855 70368744177664 (Ns60p2469 rfl rfl) (Ns60p2469 rfl rfl) rfl) (Ns60p2469 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 13932713 8388608) (BSN.cos_neg_of_bound 13932713 8388608 Bool.true 377448 4194304 1 1092233 (Ns60p2491 rfl rfl)) rfl rfl) 

noncomputable def Ns60p2493 := @Ns60p2454 4212810087719753838147 Ns60p1233 (Ns60p2455 qz25 (@Enclosure.Real.IsNear.of_eq qz1093 (@Inv.inv Real Real.instInv (Real.sqrt qz246)) Bool.false 809027 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz243 (BSN.t_div_two_pi_nonneg qz242 283692 1000 qz245)) Ns60p2459) rfl) (@Ns60p2460 549755813888 2600825203887093 9607383069925310464 (BSN.correction_mk qz244 (BSN.cos_two_pi_p_ne_zero_mk qz242 283692 1000 6 qz245 rfl rfl (@BSN.floor_sqrt_eq_dec qz242 283692 1000 6 qz245 rfl rfl rfl))) (@Ns60p2461 65536 47181 524288 393946857 9162314481664 259323242169 549755813888 2600825203887093 9607383069925310464 Ns60p2477 (Ns60p2492 rfl) rfl)) 

noncomputable def Ns60p2494 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz242) (hardyZApproximantRS₀ qz242) Bool.true 1195646300398369387 1152921504606846976 65201678738489365327427 Ns60p1233 (@Eq.refl Real (hardyZApproximantRS₀ qz242)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz242) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz242) qz242 6) (@HMul.hMul Real Real Real qz5 qz1088 (Zeta.RiemannSiegel.correction qz244))) Bool.true 1195646300398369387 1152921504606846976 65201678738489365327427 Ns60p1233 (BSN.hardyZApproximantRS₀_eq qz242 6 (@BSN.floor_sqrt_eq_dec qz242 283692 1000 6 qz245 rfl rfl rfl)) (@Ns60p2403 1195646300398369387 1152921504606846976 65201678738489365327427 Ns60p1233 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz242) qz242 6) (@HAdd.hAdd Real Real Real qz336 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz242) qz242 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz242) qz242 6)) Bool.true 14345959 16777216 50785 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz242) qz242 6) (Ns60p2453 (Ns60p2452 rfl rfl rfl rfl) rfl rfl)) (Ns60p2493 rfl) rfl rfl)) 

theorem RS061to078.d64 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz242) Bool.true 1195646300398369387 1152921504606846976 65201678738489365327427 Ns60p1233 := Ns60p2494 

noncomputable def Ns60p2495 := nat_lit 1225479851518615350711156736 

noncomputable abbrev qz1095 := (Enclosure.sfrac Bool.false 285752 1000)

noncomputable abbrev qz881 := qz1095

noncomputable abbrev qz588 := qz881

noncomputable abbrev qz253 := qz588

noncomputable abbrev qz1096 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 285752 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz882 := qz1096

noncomputable abbrev qz589 := qz882

noncomputable abbrev qz254 := qz589

noncomputable abbrev qz883 := (@HSub.hSub Real Real Real qz920 (Real.sqrt qz1096) qz914)

noncomputable abbrev qz590 := qz883

noncomputable abbrev qz255 := qz590

noncomputable abbrev qz1097 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz326 qz254 qz8))

noncomputable def Ns60p2496 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz253) qz253 6) (@HMul.hMul Real Real Real qz5 qz1097 (Zeta.RiemannSiegel.correction qz255)) 72815071 33554432 51153 33554432 3508363006334748375 18446744073709551616 80934755709505763625213 Ns60p62 Ns60p2495 

noncomputable def Ns60p2497 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz253) qz253 Real.sin BSN.quadSignNeg 5 6 285752 1000 69 67108864 33554432 1125899906842624 Bool.false 26986110959 1136 120242927 63 27397080 8 

noncomputable def Ns60p2498 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz253) qz253 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 285752 1000 3 36 67108864 33554432 1125899906842624 Bool.false 26986110959 1136 

noncomputable def Ns60p2499 := Ns60p2498 93032624 62 33554424 8 108007536 62 30011992 8 Bool.false 57901376 25451 Bool.false 85609514 Bool.true 82341613 3537118876014220 1 Bool.false 64207657 Bool.false Bool.false 22620867 Bool.false Bool.false 100121554 

noncomputable def Ns60p2500 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz253) qz253 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 285752 1000 129 56 67108864 33554432 1125899906842624 Bool.false 26986110959 1136 

noncomputable def Ns60p2501 := Ns60p2500 46516304 62 47453136 16 73726608 62 38745320 8 Bool.false 67108848 1206 Bool.false 95531996 Bool.false 15381274 3537118876014220 1 Bool.false 66382546 Bool.true Bool.false 65353881 Bool.false Bool.false 57901376 

noncomputable def Ns60p2502 := nat_lit 541604695153126464781106950124053220297302285013567 

noncomputable def Ns60p2503 := nat_lit 1346858607525308572355348930650364957366943744000 

noncomputable def Ns60p2504 := nat_lit 139805824000000000000000000 

noncomputable def Ns60p2505 := nat_lit 914515350258226240007004815360000 

noncomputable def Ns60p2506 := nat_lit 1567949782504360857833350229368504320 

noncomputable abbrev qz256 := (@Eq.refl Real qz588)

noncomputable def Ns60p2507 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz253 285752 1000 326617822016 16000000 571504 4000 2000 Ns60p2505 Ns60p2506 qz256 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns60p2508 := nat_lit 709892106031105919917892501666599036908080051012982538240 

noncomputable abbrev qz1098 := (Real.log (Enclosure.sfrac Bool.false 326617822016 16000000))

noncomputable abbrev qz1099 := (@HSub.hSub Real Real Real qz11 qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 571504))))

noncomputable abbrev qz884 := (@HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 285752 4000) qz1098) (@HMul.hMul Real Real Real qz5 qz12 qz1099))

noncomputable abbrev qz1100 := (Enclosure.sfrac Bool.false 285752 2000)

noncomputable abbrev qz591 := (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 qz884 qz1100) (@HMul.hMul Real Real Real qz5 qz1100 (Real.log Real.pi)))

noncomputable def Ns60p2509 := @Enclosure.Real.IsNear.addLit_ft_p qz591 (Enclosure.sfrac Bool.true Ns60p2505 Ns60p2506) 452752469246813516907 1125899906842624000 2365604774576861518643 Ns60p2504 Ns60p2505 Ns60p2506 0 1 Ns60p2508 

noncomputable def Ns60p2510 := nat_lit 3797962985543573842434195456000 

noncomputable abbrev qz592 := (@HSub.hSub Real Real Real qz11 qz884 qz1100)

noncomputable def Ns60p2511 := @Enclosure.Real.IsNear.subLit_ff_p qz592 (@HMul.hMul Real Real Real qz5 qz1100 (Real.log Real.pi)) 636898383019689751659 1125899906842624000 9179751092513703881 1092233000000000000000000 1371993972159 8388608000 35719 4194304000 Ns60p2510 452752469246813516907 1125899906842624000 

noncomputable def Ns60p2512 := nat_lit 1273796766039379503318000 

noncomputable abbrev qz593 := qz884

noncomputable def Ns60p2513 := @Enclosure.Real.IsNear.subLit_ff_p qz593 qz1100 797762458109736498283 1125899906842624000 9179751092513703881 1092233000000000000000000 285752 2000 0 1 Ns60p2512 636898383019689751659 1125899906842624000 9179751092513703881 1092233000000000000000000 

noncomputable def Ns60p2514 := nat_lit 1796401354536590109207714937054429184 

noncomputable def Ns60p2515 := nat_lit 11997328202329207953424384 

noncomputable def Ns60p2516 := nat_lit 4373479979496989677999887547705284210228587005659733202003326781808967680 

noncomputable def Ns60p2517 := nat_lit 17608956924751760920773842826496562766990765894828463076716496170254336 

noncomputable def Ns60p2518 := nat_lit 1077436676522741871561383963406204915962089340088916128804624138240 

noncomputable def Ns60p2519 := BSN.log_dyadic_bound 64473822016 588761822016 4 3 Ns60p2516 33554432 8737864 Ns60p2517 Ns60p2518 7378511 653235644032 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 64473822016) (BSN.artanhQ 588761822016) 0 3 Ns60p2517 Ns60p2516 Ns60p2518 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz885 := qz1098

noncomputable def Ns60p2520 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 285752 4000) qz885 285752 4000 0 1 22346765179800257 2251799813685248 62500007645631 546116500000000000000 798204105457285379783 1125899906842624000 2232437773094293689 273058250000000000000000 (Enclosure.Real.IsNear.const Bool.false 285752 4000) (BSN.isNear_log_sfrac 326617822016 16000000 22346765179800257 2251799813685248 62500007645631 546116500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 326617822016) qz650)) Bool.false Ns60p2515 Ns60p84 1000000122330096 8737864000000000000000 22346765179800257 2251799813685248 62500007645631 546116500000000000000 (BSN.log_rat_reduce_isNear 326617822016 16000000 14 653235644032 524288000000 7378511 33554432 24973259072661432 36028797018963968 8737864 1000000000000000 rfl rfl rfl rfl (Ns60p2519 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p2521 := BSN.arctan_dyadic_bound_f 1000 571504 1 0 4194304 1092233 0 1 1 0 1 1 7339 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 571504) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 571504) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz1101 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 571504)))

noncomputable abbrev qz886 := qz1101

noncomputable abbrev qz594 := qz886

noncomputable def Ns60p2522 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz594 884279719003555 562949953421312 1 2000000000000000 7339 4194304 1 1092233 3704806472827327741952 883294695097763 562949953421312 2000000001092233 2184466000000000000000 qz15 (Ns60p2521 rfl) rfl rfl 

noncomputable abbrev qz887 := (@HMul.hMul Real Real Real qz5 qz12 qz1099)

noncomputable abbrev qz595 := qz887

noncomputable abbrev qz888 := qz1099

noncomputable abbrev qz596 := qz888

noncomputable abbrev qz889 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 285752 4000) qz1098)

noncomputable def Ns60p2523 := @Enclosure.Real.IsNear.subLit_ff_p qz889 qz595 798204105457285379783 1125899906842624000 2232437773094293689 273058250000000000000000 883294695097763 2251799813685248 2000000001092233 8737864000000000000000 Ns60p2514 797762458109736498283 1125899906842624000 9179751092513703881 1092233000000000000000000 (Ns60p2520 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz12 qz596 1 4 0 1 883294695097763 562949953421312 2000000001092233 2184466000000000000000 883294695097763 2251799813685248 2000000001092233 8737864000000000000000 qz335 Ns60p2522 rfl) 

noncomputable def Ns60p2524 := @Ns60p2509 Ns60p2502 Ns60p2503 2365604774576861518643 Ns60p2504 (@Ns60p2511 2365604774576861518643 Ns60p2504 (Ns60p2513 (Ns60p2523 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 285752 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz1100 (Real.log Real.pi) 285752 2000 0 1 38410761 33554432 1 16777216 1371993972159 8388608000 35719 4194304000 (Enclosure.Real.IsNear.const Bool.false 285752 2000) RS061to078.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns60p2505 Ns60p2506) 

noncomputable def Ns60p2525 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz253) Bool.false Ns60p2502 Ns60p2503 2365604774576861518643 Ns60p2504 3373263869 8388608 143 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz253) (@HAdd.hAdd Real Real Real qz336 qz591 (Enclosure.sfrac Bool.true Ns60p2505 Ns60p2506)) Bool.false Ns60p2502 Ns60p2503 2365604774576861518643 Ns60p2504 Ns60p2507 (Ns60p2524 rfl rfl)) 

noncomputable def Ns60p2526 := nat_lit 1899616521791094095085568 

noncomputable def Ns60p2527 := nat_lit 140178171109982811605429204423632634164950494873642753940784662100240051440090148230625 

noncomputable def Ns60p2528 := nat_lit 282025969571049459056385974903468153976963763886016529603137062186014265904000390625 

noncomputable def Ns60p2529 := nat_lit 366676691813506616985270910483479855325574307146582233558888083590422778293534387590625 

noncomputable def Ns60p2530 := BSN.sin_dyadic_bound_f 26995174405 17179869184 3 2 8388608 2186600 Ns60p2527 Ns60p94 Ns60p2528 Ns60p2529 Ns60p97 Ns60p2528 8388606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26995174405) qz655 0 2 Ns60p2527 Ns60p94 Ns60p2528 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26995174405) qz656 0 2 Ns60p2529 Ns60p97 Ns60p2528 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2531 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz253) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3373263869) qz337) Bool.false 3373263869 8388608 143 8388608 Bool.false 8388606 8388608 1 1092233 (Ns60p2525 rfl) (Enclosure.sfrac_false_div 3373263869 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3373263869) qz337) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns60p2526) qz657) 226375608064910080 72057594037927936 Bool.false 8388606 8388608 63 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q3 3373263869 8388608 226375608064910080 72057594037927936 63 Ns60p2526 Ns60p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388606 8388608 Ns60p2526 Ns60p84 26995174405 17179869184 2186600 2184466 (Ns60p2530 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p2532 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz253) Bool.false Ns60p2502 Ns60p2503 2365604774576861518643 Ns60p2504 26986110959 67108864 1136 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz253) (@HAdd.hAdd Real Real Real qz336 qz591 (Enclosure.sfrac Bool.true Ns60p2505 Ns60p2506)) Bool.false Ns60p2502 Ns60p2503 2365604774576861518643 Ns60p2504 Ns60p2507 (Ns60p2524 rfl rfl)) 

noncomputable def Ns60p2533 := Ns60p2501 25451 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 129 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66382546 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 56 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 65353881 67108864) qz256 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz253) qz253 1) Bool.false 4194303 4194304 164577927 9162314481664 67108848 67108864 1206 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz253) qz253 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz253)) Bool.false 4194303 4194304 164577927 9162314481664 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz253) qz253) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz253)) Bool.false 8388606 8388608 164577927 9162314481664 4194303 4194304 164577927 9162314481664 (Ns60p2531 rfl rfl) rfl)) rfl) (Ns60p2532 rfl) RS061to078.d7 

noncomputable def Ns60p2534 := nat_lit 1780422527014304203998061351194418262876918074734763868456451518344425590822965136754341582465312751616 

noncomputable def Ns60p2535 := nat_lit 577811553444194429681121259616545980683719042257326086700085849823590491183306731682229404041216 

noncomputable def Ns60p2536 := nat_lit 8894647316314258859151196547010144904276323780475858479548433164642269136488022997101434513688337842176 

noncomputable def Ns60p2537 := BSN.sin_dyadic_bound_f 95531996 67108864 4 3 67108864 33554432 Ns60p2534 Ns60p109 Ns60p2535 Ns60p2536 Ns60p112 Ns60p2535 66382546 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 95531996) qz339 0 3 Ns60p2534 Ns60p109 Ns60p2535 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 95531996) (BSN.sinOddQ 67108864) 0 3 Ns60p2536 Ns60p112 Ns60p2535 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2538 := nat_lit 55971794992500157064428181776 

noncomputable def Ns60p2539 := BSN.cos_dyadic_bound_f 15381274 67108864 2 1 67108864 33554432 Ns60p2538 Ns60p630 Ns60p2538 Ns60p2538 Ns60p631 Ns60p2538 65353881 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 15381274) qz338 0 1 Ns60p2538 Ns60p630 Ns60p2538 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 15381274) (BSN.cosOddQ 67108864) 0 1 Ns60p2538 Ns60p631 Ns60p2538 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2540 := nat_lit 3297384825749756843656278950828843591567801152966172604119442284800 

noncomputable def Ns60p2541 := nat_lit 2885202187250613592436424930893766052300302972659033521113293056 

noncomputable def Ns60p2542 := nat_lit 8631336597231909787569166849901714737640516814860432670802451128576 

noncomputable def Ns60p2543 := BSN.sin_dyadic_bound_f 85609514 67108864 3 2 67108864 33554432 Ns60p2540 Ns60p119 Ns60p2541 Ns60p2542 Ns60p122 Ns60p2541 64207657 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 85609514) qz339 0 2 Ns60p2540 Ns60p119 Ns60p2541 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 85609514) (BSN.sinOddQ 67108864) 0 2 Ns60p2542 Ns60p122 Ns60p2541 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2544 := nat_lit 377944413912593929511248347336758587574709193467698316759147335312303209725049962399280746342783462961 

noncomputable def Ns60p2545 := nat_lit 97147681949313254653826710324284229475420719107803611252273657103363149184529509800467288632881 

noncomputable def Ns60p2546 := nat_lit 2290802842288506560160491368062481455861981604596745999405076772388583595012069616464921925992186195505 

noncomputable def Ns60p2547 := BSN.cos_dyadic_bound_f 82341613 67108864 4 3 67108864 33554432 Ns60p2544 Ns60p219 Ns60p2545 Ns60p2546 Ns60p222 Ns60p2545 22620867 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 82341613) qz338 0 3 Ns60p2544 Ns60p219 Ns60p2545 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 82341613) (BSN.cosOddQ 67108864) 0 3 Ns60p2546 Ns60p222 Ns60p2545 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2548 := Ns60p2499 43329 BSN.abs_quadSignPos (BSN.cos_quad_nat3 3 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 64207657 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 22620867 67108864) qz256 rfl rfl (Ns60p2533 RS061to078.d9 RS061to078.d11 RS061to078.d13 RS061to078.d17 (Ns60p2537 rfl rfl) (Ns60p2539 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns60p2532 rfl) RS061to078.d19 RS061to078.d21 RS061to078.d23 RS061to078.d25 RS061to078.d17 (Ns60p2543 rfl rfl) (Ns60p2547 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns60p2549 := nat_lit 2134359416327532877181845209069866334336438481536954983461947536241467895211936266844557560132784805441 

noncomputable def Ns60p2550 := nat_lit 994646660130612203669122725991259444269115068121778763036098931298662445468908354531474500671041 

noncomputable def Ns60p2551 := nat_lit 10661073740738763125985016956015623236567849560655665689487946041530664255082034105276945260442208360001 

noncomputable def Ns60p2552 := BSN.sin_dyadic_bound_f 99955279 67108864 4 3 67108864 33554432 Ns60p2549 Ns60p109 Ns60p2550 Ns60p2551 Ns60p112 Ns60p2550 66886947 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 99955279) qz339 0 3 Ns60p2549 Ns60p109 Ns60p2550 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 99955279) (BSN.sinOddQ 67108864) 0 3 Ns60p2551 Ns60p112 Ns60p2550 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2553 := Ns60p2497 Bool.false 100121554 43329 Bool.true 99955279 3537118876014220 1 Bool.false 66886947 Bool.true Bool.false 72815071 51153 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 69 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 66886947 67108864) qz256 rfl (Ns60p2548 rfl rfl) (Ns60p2532 rfl) RS061to078.d27 RS061to078.d29 RS061to078.d17 (Ns60p2552 rfl rfl) rfl 

noncomputable def Ns60p2554 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz253) qz253 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz253) qz253 6) 72815071 67108864 51153 67108864 72815071 67108864 51153 67108864 9773073393778688 72815071 33554432 51153 33554432 (Ns60p2553 rfl rfl rfl rfl) 

noncomputable def Ns60p2555 := @Enclosure.Real.IsNear.mulLit_ff qz1097 (Zeta.RiemannSiegel.correction qz255) 807565 2097152 1 4194304 4344372287475 8796093022208 50098583608635523 38429532279701241856 3508363006334748375 18446744073709551616 

noncomputable abbrev qz1102 := (@HPow.hPow Real Real Real qz326 qz254 qz8)

noncomputable def Ns60p2556 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz1102 1 1 0 1 807565 2097152 1 4194304 807565 2097152 1 4194304 

noncomputable def Ns60p2557 := @Enclosure.Real.IsNear.sqrt_image qz254 47688043991 1048576000 35719 1048576000 28285544 28285566 4194304 (@Enclosure.Real.IsNear.of_eq qz254 (@HMul.hMul Real Real Real qz5 qz253 qz3) Bool.false 47688043991 1048576000 35719 1048576000 (BSN.t_div_two_pi_mk qz253 285752 1000 qz256) (@Enclosure.Real.IsNear.mulLit_ff qz253 qz3 285752 1000 0 1 1335089 8388608 1 8388608 47688043991 1048576000 35719 1048576000 (Enclosure.Real.IsNear.const Bool.false 285752 1000) RS061to078.d32 rfl)) 

noncomputable abbrev qz890 := (Real.sqrt qz1096)

noncomputable abbrev qz597 := qz890

noncomputable abbrev qz257 := qz597

noncomputable def Ns60p2558 := @Enclosure.Real.IsNear.sqrt_image qz257 28285555 4194304 11 4194304 10892115 10892120 4194304 (@Enclosure.Real.IsNear.recentre' qz257 Bool.false 56571110 8388608 22 8388608 28285555 4194304 11 4194304 (Ns60p2557 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns60p2559 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz257) 21784235 8388608 5 8388608 1615129 1615131 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz257) Bool.false 21784235 8388608 5 8388608 21784235 8388608 5 8388608 (Ns60p2558 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns60p2560 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz257)) Bool.false 3230260 8388608 2 8388608 807565 2097152 1 4194304 (Ns60p2559 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz258 := (Real.cos (@HMul.hMul Real Real Real qz323 qz320 qz590))

noncomputable abbrev qz598 := (@HSub.hSub Real Real Real qz647 (@HMul.hMul Real Real Real qz644 qz883 qz883) qz883)

noncomputable abbrev qz259 := (@HMul.hMul Real Real Real qz323 qz320 (@HSub.hSub Real Real Real qz327 qz598 qz344))

noncomputable def Ns60p2561 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz255) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz258) (Real.cos qz259)) Bool.false 4344372287475 

noncomputable def Ns60p2562 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz258) (Real.cos qz259) 53863645 2097152 48711 

noncomputable abbrev qz1103 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz258))

noncomputable def Ns60p2563 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz258) (@Neg.neg Real Real.instNeg qz1103) Bool.true 53863645 2097152 48711 4194304 (BSN.inv_eq_neg_inv_neg qz258) 

noncomputable def Ns60p2564 := @Enclosure.Real.IsNear.recentre' qz1103 Bool.false 215454580 8388608 97422 8388608 53863645 2097152 

noncomputable def Ns60p2565 := @Enclosure.Real.IsNear.recentre' qz258 Bool.true 326606 8388608 40325307 2290578620416 163303 4194304 40325307 2290578620416 

noncomputable abbrev qz260 := (@HMul.hMul Real Real Real qz323 qz320 qz590)

noncomputable def Ns60p2566 := @Enclosure.Real.IsNear.cos_image qz260 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 39203695) qz337) Bool.false 39203695 8388608 35 2097152 Bool.true 326606 8388608 1 

noncomputable def Ns60p2567 := nat_lit 296846829526282785241493389 

noncomputable def Ns60p2568 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz255 884279719003555 140737488355328 1 500000000000000 3119731 4194304 11 4194304 2758714852046679643705 590295810358705651712 Ns60p2567 

noncomputable def Ns60p2569 := @Enclosure.Real.IsNear.subLit_ff_p qz257 qz1 28285555 4194304 11 4194304 6 1 0 1 3119731 3119731 4194304 11 

noncomputable def Ns60p2570 := @Ns60p2569 4194304 (@Enclosure.Real.IsNear.recentre' qz257 Bool.false 56571110 8388608 22 8388608 28285555 4194304 11 4194304 (Ns60p2557 rfl rfl rfl rfl rfl rfl) rfl) qz345 

noncomputable def Ns60p2571 := @Enclosure.Real.IsNear.recentre' qz260 Bool.false 2758714852046679643705 590295810358705651712 Ns60p2567 Ns60p1589 39203695 8388608 35 2097152 (@Ns60p2568 Ns60p1589 RS061to078.d31 (Ns60p2570 rfl rfl) rfl) 

noncomputable def Ns60p2572 := nat_lit 1851895404557152037109760 

noncomputable def Ns60p2573 := nat_lit 72887480243626715664569726982154828712288215350864394616631776785222023594823706819510632664402802898811799957550350177047917339761 

noncomputable def Ns60p2574 := nat_lit 110367153376386213264922538950783270830051758194988620479648113776390332710201712784292973650910361585124199636959527490004081 

noncomputable def Ns60p2575 := nat_lit 441220439575655869476576808735614878010827076625164745567914681138580013487551385902226832275894980424837477584882068791731793667185 

noncomputable def Ns60p2576 := BSN.cos_dyadic_bound_f 26317016541 17179869184 4 3 8388608 2186600 Ns60p2573 Ns60p2236 Ns60p2574 Ns60p2575 Ns60p2239 Ns60p2574 326606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 26317016541) qz769 0 3 Ns60p2573 Ns60p2236 Ns60p2574 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 26317016541) qz770 0 3 Ns60p2575 Ns60p2239 Ns60p2574 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2577 := @Ns60p2566 1092233 (Ns60p2571 rfl) (Enclosure.sfrac_false_div 39203695 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 39203695) qz337) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns60p2572) qz657) 226375608064910080 72057594037927936 Bool.false 326606 8388608 0 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q2 39203695 8388608 226375608064910080 72057594037927936 0 Ns60p2572 Ns60p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 326606 8388608 Ns60p2572 Ns60p84 26317016541 17179869184 2186600 2184466 (Ns60p2576 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p2578 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz258) 163303 4194304 40325307 2290578620416 107678579 107776001 4194304 (@Enclosure.Real.IsNear.neg qz258 Bool.true 163303 4194304 40325307 2290578620416 (Ns60p2565 (Ns60p2577 rfl rfl) rfl)) 

noncomputable def Ns60p2579 := Ns60p2563 (@Enclosure.Real.IsNear.neg qz1103 Bool.false 53863645 2097152 48711 4194304 (@Ns60p2564 48711 4194304 (Ns60p2578 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p2580 := @Enclosure.Real.IsNear.recentre' (Real.cos qz259) Bool.true 80655 4194304 

noncomputable def Ns60p2581 := @Enclosure.Real.IsNear.cos_image qz259 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 13338113)) qz337) Bool.true 13338113 8388608 

noncomputable def Ns60p2582 := nat_lit 3936716327959259323555756645 

noncomputable def Ns60p2583 := nat_lit 3097233622192884334753237948770237 

noncomputable def Ns60p2584 := @Enclosure.Real.IsNear.recentre' qz259 Bool.true Ns60p2582 Ns60p327 Ns60p2583 

noncomputable abbrev qz261 := (@HSub.hSub Real Real Real qz327 qz598 qz344)

noncomputable def Ns60p2585 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz261 884279719003555 140737488355328 1 500000000000000 4451890327639 

noncomputable abbrev qz262 := qz598

noncomputable def Ns60p2586 := @Enclosure.Real.IsNear.subLit_tf qz262 qz23 3352378699863 17592186044416 114771547 17592186044416 1 16 

noncomputable abbrev qz599 := (@HMul.hMul Real Real Real qz644 qz883 qz883)

noncomputable abbrev qz263 := qz599

noncomputable def Ns60p2587 := @Enclosure.Real.IsNear.subLit_ff_n qz263 qz255 9732721512361 17592186044416 68634203 17592186044416 3119731 4194304 11 4194304 

noncomputable def Ns60p2588 := @Enclosure.Real.IsNear.mulLit_ff qz255 qz255 3119731 4194304 11 4194304 3119731 4194304 11 4194304 9732721512361 17592186044416 

noncomputable def Ns60p2589 := nat_lit 15547929409708561505553931508587029977502578736654134303595855279242439514106736723918735361 

noncomputable def Ns60p2590 := nat_lit 31705361484323890738623279349987627513034333155661745090874209043425834182281318778881 

noncomputable def Ns60p2591 := nat_lit 94085608220585946462890427360137387505171910738037022099849407150519706686460205806644250625 

noncomputable def Ns60p2592 := BSN.cos_dyadic_bound_t 13338113 8388608 4 3 4194304 1092233 Ns60p2589 Ns60p274 Ns60p2590 Ns60p2591 Ns60p277 Ns60p2590 80655 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 13338113) (BSN.cosEvenQ 8388608) 0 3 Ns60p2589 Ns60p274 Ns60p2590 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 13338113) (BSN.cosOddQ 8388608) 0 3 Ns60p2591 Ns60p277 Ns60p2590 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2593 := @Ns60p2580 385208993 9162314481664 80655 4194304 385208993 9162314481664 (@Ns60p2581 345 8388608 Bool.true 80655 4194304 1 1092233 (@Ns60p2584 Ns60p1701 13338113 8388608 345 8388608 (@Ns60p2585 17592186044416 114771547 17592186044416 Ns60p2582 Ns60p327 Ns60p2583 Ns60p1701 RS061to078.d31 (@Ns60p2586 0 1 71230245242224 4451890327639 17592186044416 114771547 17592186044416 (@Ns60p2587 14060895390350180352 3352378699863 17592186044416 114771547 17592186044416 (@Ns60p2588 68634203 17592186044416 (Ns60p2570 rfl rfl) (Ns60p2570 rfl rfl) rfl) (Ns60p2570 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 13338113 8388608) (BSN.cos_neg_of_bound 13338113 8388608 Bool.true 80655 4194304 1 1092233 (Ns60p2592 rfl rfl)) rfl rfl) 

noncomputable def Ns60p2594 := @Ns60p2555 80934755709505763625213 Ns60p62 (Ns60p2556 qz25 (@Enclosure.Real.IsNear.of_eq qz1102 (@Inv.inv Real Real.instInv (Real.sqrt qz257)) Bool.false 807565 2097152 1 4194304 (BSN.rpow_neg_quarter_mk qz254 (BSN.t_div_two_pi_nonneg qz253 285752 1000 qz256)) Ns60p2560) rfl) (@Ns60p2561 8796093022208 50098583608635523 38429532279701241856 (BSN.correction_mk qz255 (BSN.cos_two_pi_p_ne_zero_mk qz253 285752 1000 6 qz256 rfl rfl (@BSN.floor_sqrt_eq_dec qz253 285752 1000 6 qz256 rfl rfl rfl))) (@Ns60p2562 4194304 80655 4194304 385208993 9162314481664 4344372287475 8796093022208 50098583608635523 38429532279701241856 Ns60p2579 (Ns60p2593 rfl) rfl)) 

noncomputable def Ns60p2595 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz253) (hardyZApproximantRS₀ qz253) Bool.false 36522145614582757673 18446744073709551616 326657988797450466707709 Ns60p62 (@Eq.refl Real (hardyZApproximantRS₀ qz253)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz253) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz253) qz253 6) (@HMul.hMul Real Real Real qz5 qz1097 (Zeta.RiemannSiegel.correction qz255))) Bool.false 36522145614582757673 18446744073709551616 326657988797450466707709 Ns60p62 (BSN.hardyZApproximantRS₀_eq qz253 6 (@BSN.floor_sqrt_eq_dec qz253 285752 1000 6 qz256 rfl rfl rfl)) (@Ns60p2496 36522145614582757673 18446744073709551616 326657988797450466707709 Ns60p62 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz253) qz253 6) (@HAdd.hAdd Real Real Real qz336 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz253) qz253 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz253) qz253 6)) Bool.false 72815071 33554432 51153 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz253) qz253 6) (Ns60p2554 (Ns60p2553 rfl rfl rfl rfl) rfl rfl)) (Ns60p2594 rfl) rfl rfl)) 

theorem RS061to078.d65 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz253) Bool.false 36522145614582757673 18446744073709551616 326657988797450466707709 Ns60p62 := Ns60p2595 

noncomputable def Ns60p2596 := nat_lit 5304108076962024521291792384 

noncomputable abbrev qz1104 := (Enclosure.sfrac Bool.false 287396 1000)

noncomputable abbrev qz891 := qz1104

noncomputable abbrev qz600 := qz891

noncomputable abbrev qz264 := qz600

noncomputable abbrev qz1105 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 287396 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz892 := qz1105

noncomputable abbrev qz601 := qz892

noncomputable abbrev qz265 := qz601

noncomputable abbrev qz893 := (@HSub.hSub Real Real Real qz920 (Real.sqrt qz1105) qz914)

noncomputable abbrev qz602 := qz893

noncomputable abbrev qz266 := qz602

noncomputable abbrev qz1106 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz326 qz265 qz8))

noncomputable def Ns60p2597 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz264) qz264 6) (@HMul.hMul Real Real Real qz5 qz1106 (Zeta.RiemannSiegel.correction qz266)) 29315225 33554432 51449 33554432 29145015855322116587 147573952589676412928 38714874801925467108989 Ns60p62 Ns60p2596 

noncomputable def Ns60p2598 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz264) qz264 Real.sin BSN.quadSignNeg 5 6 287396 1000 69 67108864 33554432 1125899906842624 Bool.false 27196841996 1143 120242927 63 27397080 8 

noncomputable def Ns60p2599 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz264) qz264 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 287396 1000 4 36 67108864 33554432 1125899906842624 Bool.false 27196841996 1143 

noncomputable def Ns60p2600 := Ns60p2599 93032624 62 33554424 8 108007536 62 30011992 8 Bool.true 53585065 25599 Bool.false 37980560 Bool.true 49174965 3537118876014220 1 Bool.false 56645061 Bool.false Bool.false 49883916 Bool.false Bool.true 2953780 

noncomputable def Ns60p2601 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz264) qz264 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 287396 1000 131 56 67108864 33554432 1125899906842624 Bool.false 27196841996 1143 

noncomputable def Ns60p2602 := Ns60p2601 46516304 62 47453136 16 73726608 62 38745320 8 Bool.true 67108824 1214 Bool.false 18961515 Bool.false 104905767 3537118876014220 1 Bool.false 18710225 Bool.false Bool.false 508585 Bool.false Bool.true 53585065 

noncomputable def Ns60p2603 := nat_lit 141237233945122601479454456409658656402080570807789 

noncomputable def Ns60p2604 := nat_lit 348506283405900874030257572159118151205781504000 

noncomputable def Ns60p2605 := nat_lit 941126850148598407642050068480000 

noncomputable def Ns60p2606 := nat_lit 1622858845656276093936793376501268480 

noncomputable def Ns60p2607 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz264 287396 1000 330386843264 16000000 574792 4000 2000 Ns60p2605 Ns60p2606 (@Eq.refl Real qz264) rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns60p2608 := nat_lit 1480979738212408769689204360842142352954680366153481584640 

noncomputable abbrev qz1107 := (Real.log (Enclosure.sfrac Bool.false 330386843264 16000000))

noncomputable abbrev qz1108 := (@HSub.hSub Real Real Real qz11 qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 574792))))

noncomputable abbrev qz894 := (@HSub.hSub Real Real Real qz11 (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 287396 4000) qz1107) (@HMul.hMul Real Real Real qz5 qz12 qz1108))

noncomputable abbrev qz1109 := (Enclosure.sfrac Bool.false 287396 2000)

noncomputable abbrev qz603 := (@HSub.hSub Real Real Real qz11 (@HSub.hSub Real Real Real qz11 qz894 qz1109) (@HMul.hMul Real Real Real qz5 qz1109 (Real.log Real.pi)))

noncomputable def Ns60p2609 := @Enclosure.Real.IsNear.addLit_ft_p qz603 (Enclosure.sfrac Bool.true Ns60p2605 Ns60p2606) 912575891246273391793 2251799813685248000 4758061128490879944253 Ns60p72 Ns60p2605 Ns60p2606 0 1 Ns60p2608 

noncomputable def Ns60p2610 := nat_lit 3062096568766247577832757657600 

noncomputable abbrev qz604 := (@HSub.hSub Real Real Real qz11 qz894 qz1109)

noncomputable def Ns60p2611 := @Enclosure.Real.IsNear.subLit_ff_p qz604 (@HMul.hMul Real Real Real qz5 qz1109 (Real.log Real.pi)) 256597318055337629117 450359962737049600 9231126098798412563 1092233000000000000000000 2759774767089 16777216000 71849 8388608000 Ns60p2610 912575891246273391793 2251799813685248000 

noncomputable def Ns60p2612 := nat_lit 2565973180553376291170000 

noncomputable abbrev qz605 := qz894

noncomputable def Ns60p2613 := @Enclosure.Real.IsNear.subLit_ff_p qz605 qz1109 1606565719903630912689 2251799813685248000 9231126098798412563 1092233000000000000000000 287396 2000 0 1 Ns60p2612 256597318055337629117 450359962737049600 9231126098798412563 1092233000000000000000000 

noncomputable def Ns60p2614 := nat_lit 3617664388752102413646632802815311872 

noncomputable def Ns60p2615 := nat_lit 12011198784778350815608832 

noncomputable def Ns60p2616 := nat_lit 4544175227393224305886959413795399936374855258995853477537665583971041280 

noncomputable def Ns60p2617 := nat_lit 20253559263429916764201556866620783342593757069803765750762391319085056 

noncomputable def Ns60p2618 := nat_lit 1515074318646139176479275121781273840883393532538827303073915863040 

noncomputable def Ns60p2619 := BSN.log_dyadic_bound 68242843264 592530843264 4 3 Ns60p2616 33554432 8737864 Ns60p2617 Ns60p2618 7763497 660773686528 524288000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 68242843264) (BSN.artanhQ 592530843264) 0 3 Ns60p2617 Ns60p2616 Ns60p2618 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz895 := qz1107

noncomputable def Ns60p2620 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 287396 4000) qz895 287396 4000 0 1 22372601152916161 2251799813685248 62500007645631 546116500000000000000 1607449020235873251689 2251799813685248000 4490563049330941719 546116500000000000000000 (Enclosure.Real.IsNear.const Bool.false 287396 4000) (BSN.isNear_log_sfrac 330386843264 16000000 22372601152916161 2251799813685248 62500007645631 546116500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 330386843264) qz650)) Bool.false Ns60p2615 Ns60p84 1000000122330096 8737864000000000000000 22372601152916161 2251799813685248 62500007645631 546116500000000000000 (BSN.log_rat_reduce_isNear 330386843264 16000000 14 660773686528 524288000000 7763497 33554432 24973259072661432 36028797018963968 8737864 1000000000000000 rfl rfl rfl rfl (Ns60p2619 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns60p2621 := BSN.arctan_dyadic_bound_f 1000 574792 1 0 4194304 1092233 0 1 1 0 1 1 7297 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 574792) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 574792) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz1110 := (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 574792)))

noncomputable abbrev qz896 := qz1110

noncomputable abbrev qz606 := qz896

noncomputable def Ns60p2622 := @Enclosure.Real.IsNear.subLit_ff_p qz13 qz606 884279719003555 562949953421312 1 2000000000000000 7297 4194304 1 1092233 3704830116725371437056 883300332242339 562949953421312 2000000001092233 2184466000000000000000 qz15 (Ns60p2621 rfl) rfl rfl 

noncomputable abbrev qz897 := (@HMul.hMul Real Real Real qz5 qz12 qz1108)

noncomputable abbrev qz607 := qz897

noncomputable abbrev qz898 := qz1108

noncomputable abbrev qz608 := qz898

noncomputable abbrev qz899 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 287396 4000) qz1107)

noncomputable def Ns60p2623 := @Enclosure.Real.IsNear.subLit_ff_p qz899 qz607 1607449020235873251689 2251799813685248000 4490563049330941719 546116500000000000000000 883300332242339 2251799813685248 2000000001092233 8737864000000000000000 Ns60p2614 1606565719903630912689 2251799813685248000 9231126098798412563 1092233000000000000000000 (Ns60p2620 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz12 qz608 1 4 0 1 883300332242339 562949953421312 2000000001092233 2184466000000000000000 883300332242339 2251799813685248 2000000001092233 8737864000000000000000 qz335 Ns60p2622 rfl) 

noncomputable def Ns60p2624 := @Ns60p2609 Ns60p2603 Ns60p2604 4758061128490879944253 Ns60p72 (@Ns60p2611 4758061128490879944253 Ns60p72 (Ns60p2613 (Ns60p2623 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 287396 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz1109 (Real.log Real.pi) 287396 2000 0 1 38410761 33554432 1 16777216 2759774767089 16777216000 71849 8388608000 (Enclosure.Real.IsNear.const Bool.false 287396 2000) RS061to078.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns60p2605 Ns60p2606) 

noncomputable def Ns60p2625 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz264) Bool.false Ns60p2603 Ns60p2604 4758061128490879944253 Ns60p72 3399605249 8388608 9 524288 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz264) (@HAdd.hAdd Real Real Real qz336 qz603 (Enclosure.sfrac Bool.true Ns60p2605 Ns60p2606)) Bool.false Ns60p2603 Ns60p2604 4758061128490879944253 Ns60p72 Ns60p2607 (Ns60p2624 rfl rfl)) 

noncomputable def Ns60p2626 := nat_lit 1897856981032344011931648 

noncomputable def Ns60p2627 := nat_lit 139658486353021164696303737114155588002644403326912269454159779364726663179079181151905 

noncomputable def Ns60p2628 := nat_lit 279942894790251112452650849237137188578479864713103729727810663417219885806656171681 

noncomputable def Ns60p2629 := nat_lit 365318985285395024784443591066880698844465422265710918722287728690656238034853745405601 

noncomputable def Ns60p2630 := BSN.sin_dyadic_bound_f 26970169827 17179869184 3 2 8388608 2186600 Ns60p2627 Ns60p94 Ns60p2628 Ns60p2629 Ns60p97 Ns60p2628 8388603 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 26970169827) qz655 0 2 Ns60p2627 Ns60p94 Ns60p2628 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 26970169827) qz656 0 2 Ns60p2629 Ns60p97 Ns60p2628 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2631 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz264) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3399605249) qz337) Bool.false 3399605249 8388608 9 524288 Bool.true 8388603 8388608 1 1092233 (Ns60p2625 rfl) (Enclosure.sfrac_false_div 3399605249 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3399605249) qz337) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns60p2626) qz657) 226375608064910080 72057594037927936 Bool.false 8388603 8388608 64 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q1 3399605249 8388608 226375608064910080 72057594037927936 64 Ns60p2626 Ns60p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 8388603 8388608 Ns60p2626 Ns60p84 26970169827 17179869184 2186600 2184466 (Ns60p2630 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p2632 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz264) Bool.false Ns60p2603 Ns60p2604 4758061128490879944253 Ns60p72 27196841996 67108864 1143 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz264) (@HAdd.hAdd Real Real Real qz336 qz603 (Enclosure.sfrac Bool.true Ns60p2605 Ns60p2606)) Bool.false Ns60p2603 Ns60p2604 4758061128490879944253 Ns60p72 Ns60p2607 (Ns60p2624 rfl rfl)) 

noncomputable def Ns60p2633 := Ns60p2602 25599 BSN.abs_quadSignPos (BSN.cos_quad_nat3 131 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 18710225 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 56 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 508585 67108864) (@Eq.refl Real qz264) rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz264) qz264 1) Bool.true 8388603 8388608 10354385 572644655104 67108824 67108864 1214 67108864 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz264) qz264 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz264)) Bool.true 8388603 8388608 10354385 572644655104 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz264) qz264) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz264)) Bool.true 8388603 8388608 10354385 572644655104 8388603 8388608 10354385 572644655104 (Ns60p2631 rfl rfl) rfl)) rfl) (Ns60p2632 rfl) RS061to078.d7 

noncomputable def Ns60p2634 := nat_lit 129268329262454813272017800625 

noncomputable def Ns60p2635 := BSN.sin_dyadic_bound_f 18961515 67108864 2 1 67108864 33554432 Ns60p2634 Ns60p115 Ns60p2634 Ns60p2634 Ns60p116 Ns60p2634 18710225 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 18961515) qz339 0 1 Ns60p2634 Ns60p115 Ns60p2634 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 18961515) (BSN.sinOddQ 67108864) 0 1 Ns60p2634 Ns60p116 Ns60p2634 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2636 := nat_lit 997938952635461765111496292767046518842676893828541158848159975365428854894931497876705309449587745441 

noncomputable def Ns60p2637 := nat_lit 1776611056697744676634319132280931317816999675156932122398323165788263891581758178579529214681761 

noncomputable def Ns60p2638 := nat_lit 6039858793126640634408267438438861613075854072669661583166382154794843276207811931474762048501594940065 

noncomputable def Ns60p2639 := BSN.cos_dyadic_bound_f 104905767 67108864 4 3 67108864 33554432 Ns60p2636 Ns60p219 Ns60p2637 Ns60p2638 Ns60p222 Ns60p2637 508585 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 104905767) qz338 0 3 Ns60p2636 Ns60p219 Ns60p2637 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 104905767) (BSN.cosOddQ 67108864) 0 3 Ns60p2638 Ns60p222 Ns60p2637 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2640 := nat_lit 70908909597407591970959124962940837942398435097510794808524800000 

noncomputable def Ns60p2641 := nat_lit 4330030054980472370453530696502712633416772308539801600000000 

noncomputable def Ns60p2642 := nat_lit 212718068732112814968136467827429508401928471747915304822374400000 

noncomputable def Ns60p2643 := BSN.cos_dyadic_bound_f 37980560 67108864 3 2 67108864 33554432 Ns60p2640 Ns60p103 Ns60p2641 Ns60p2642 Ns60p106 Ns60p2641 56645061 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 37980560) qz338 0 2 Ns60p2640 Ns60p103 Ns60p2641 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 37980560) (BSN.cosOddQ 67108864) 0 2 Ns60p2642 Ns60p106 Ns60p2641 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2644 := nat_lit 199287285852559051679210382437740175129855288516587492093387190625 

noncomputable def Ns60p2645 := nat_lit 34194202232097064163455116849847715154713247826696298750390625 

noncomputable def Ns60p2646 := nat_lit 597793469153212960909304237079520829959256439054109083682660790625 

noncomputable def Ns60p2647 := BSN.cos_dyadic_bound_f 49174965 67108864 3 2 67108864 33554432 Ns60p2644 Ns60p103 Ns60p2645 Ns60p2646 Ns60p106 Ns60p2645 49883916 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 49174965) qz338 0 2 Ns60p2644 Ns60p103 Ns60p2645 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 49174965) (BSN.cosOddQ 67108864) 0 2 Ns60p2646 Ns60p106 Ns60p2645 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2648 := Ns60p2600 43580 BSN.abs_quadSignPos (BSN.cos_quad_nat0 4 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 56645061 67108864) BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 49883916 67108864) (@Eq.refl Real qz264) rfl rfl (Ns60p2633 RS061to078.d9 RS061to078.d11 RS061to078.d13 RS061to078.d17 (Ns60p2635 rfl rfl) (Ns60p2639 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns60p2632 rfl) RS061to078.d19 RS061to078.d21 RS061to078.d23 RS061to078.d25 RS061to078.d17 (Ns60p2643 rfl rfl) (Ns60p2647 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns60p2649 := nat_lit 3501517986502480488318579029761751929560765831598771593291849990400 

noncomputable def Ns60p2650 := nat_lit 3253139599337486749433522389409051663826419779226059395293184256 

noncomputable def Ns60p2651 := nat_lit 9165375357678997728954338422650307065203429641211369124362465771776 

noncomputable def Ns60p2652 := BSN.sin_dyadic_bound_f 86903614 67108864 3 2 67108864 33554432 Ns60p2649 Ns60p119 Ns60p2650 Ns60p2651 Ns60p122 Ns60p2650 64572085 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 86903614) qz339 0 2 Ns60p2649 Ns60p119 Ns60p2650 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 86903614) (BSN.sinOddQ 67108864) 0 2 Ns60p2651 Ns60p122 Ns60p2650 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2653 := Ns60p2598 Bool.true 2953780 43580 Bool.true 86903614 3537118876014220 1 Bool.false 64572085 Bool.true Bool.true 29315225 51449 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 69 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 64572085 67108864) (@Eq.refl Real qz264) rfl (Ns60p2648 rfl rfl) (Ns60p2632 rfl) RS061to078.d27 RS061to078.d29 RS061to078.d17 (Ns60p2652 rfl rfl) rfl 

noncomputable def Ns60p2654 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz264) qz264 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz264) qz264 6) 29315225 67108864 51449 67108864 29315225 67108864 51449 67108864 3934622895308800 29315225 33554432 51449 33554432 (Ns60p2653 rfl rfl rfl rfl) 

noncomputable def Ns60p2655 := @Enclosure.Real.IsNear.mulLit_ff qz1106 (Zeta.RiemannSiegel.correction qz266) 3225631 8388608 1 8388608 9035446353077 17592186044416 11999200773444989 19214766139850620928 29145015855322116587 147573952589676412928 

noncomputable abbrev qz1111 := (@HPow.hPow Real Real Real qz326 qz265 qz8)

noncomputable def Ns60p2656 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz1111 1 1 0 1 3225631 8388608 1 8388608 3225631 8388608 1 8388608 

noncomputable def Ns60p2657 := @Enclosure.Real.IsNear.sqrt_image qz265 95924809561 2097152000 71849 2097152000 28366794 28366816 4194304 (@Enclosure.Real.IsNear.of_eq qz265 (@HMul.hMul Real Real Real qz5 qz264 qz3) Bool.false 95924809561 2097152000 71849 2097152000 (BSN.t_div_two_pi_mk qz264 287396 1000 (@Eq.refl Real qz264)) (@Enclosure.Real.IsNear.mulLit_ff qz264 qz3 287396 1000 0 1 1335089 8388608 1 8388608 95924809561 2097152000 71849 2097152000 (Enclosure.Real.IsNear.const Bool.false 287396 1000) RS061to078.d32 rfl)) 

noncomputable abbrev qz900 := (Real.sqrt qz1105)

noncomputable abbrev qz609 := qz900

noncomputable abbrev qz267 := qz609

noncomputable def Ns60p2658 := @Enclosure.Real.IsNear.sqrt_image qz267 28366805 4194304 11 4194304 10907747 10907752 4194304 (@Enclosure.Real.IsNear.recentre' qz267 Bool.false 56733610 8388608 22 8388608 28366805 4194304 11 4194304 (Ns60p2657 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns60p2659 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz267) 21815499 8388608 5 8388608 1612815 1612816 4194304 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz267) Bool.false 21815499 8388608 5 8388608 21815499 8388608 5 8388608 (Ns60p2658 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns60p2660 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz267)) Bool.false 3225631 8388608 1 8388608 3225631 8388608 1 8388608 (Ns60p2659 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz610 := (@HSub.hSub Real Real Real qz647 (@HMul.hMul Real Real Real qz644 qz893 qz893) qz893)

noncomputable abbrev qz268 := (@HMul.hMul Real Real Real qz323 qz320 (@HSub.hSub Real Real Real qz327 qz610 qz344))

noncomputable abbrev qz901 := (Real.cos (@HMul.hMul Real Real Real qz5 qz2 qz266))

noncomputable def Ns60p2661 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz266) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz901) (Real.cos qz268)) Bool.false 9035446353077 

noncomputable def Ns60p2662 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz901) (Real.cos qz268) 101463727 8388608 21461 

noncomputable def Ns60p2663 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz901) Bool.false 101463727 8388608 21461 8388608 101463727 8388608 21461 

noncomputable def Ns60p2664 := @Enclosure.Real.IsNear.recentre' qz901 Bool.false 693536 8388608 160208995 9162314481664 21673 262144 160208995 9162314481664 

noncomputable abbrev qz902 := (@HMul.hMul Real Real Real qz5 qz2 qz266)

noncomputable def Ns60p2665 := @Enclosure.Real.IsNear.cos_image qz902 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 40224713) qz337) Bool.false 40224713 8388608 139 8388608 Bool.false 693536 8388608 1 

noncomputable def Ns60p2666 := nat_lit 296846829526980717427093389 

noncomputable def Ns60p2667 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz266 884279719003555 140737488355328 1 500000000000000 3200981 4194304 11 4194304 2830562579215718487455 590295810358705651712 Ns60p2666 

noncomputable def Ns60p2668 := @Enclosure.Real.IsNear.subLit_ff_p qz267 qz1 28366805 4194304 11 4194304 6 1 0 1 3200981 3200981 4194304 11 

noncomputable def Ns60p2669 := @Ns60p2668 4194304 (@Enclosure.Real.IsNear.recentre' qz267 Bool.false 56733610 8388608 22 8388608 28366805 4194304 11 4194304 (Ns60p2657 rfl rfl rfl rfl rfl rfl) rfl) qz345 

noncomputable def Ns60p2670 := @Enclosure.Real.IsNear.recentre' qz902 Bool.false 2830562579215718487455 590295810358705651712 Ns60p2666 Ns60p1589 40224713 8388608 139 8388608 (@Ns60p2667 Ns60p1589 RS061to078.d31 (Ns60p2669 rfl rfl) rfl) 

noncomputable def Ns60p2671 := BSN.sin_dyadic_bound_f 1421985996 17179869184 1 0 8388608 2186600 0 1 1 0 1 1 693536 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 1421985996) qz655 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 1421985996) qz656 0 0 rfl) rfl rfl 

noncomputable def Ns60p2672 := @Ns60p2665 1092233 (Ns60p2670 rfl) (Enclosure.sfrac_false_div 40224713 8388608) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 40224713) qz337) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 100063368837817031458816) qz657) 226375608064910080 72057594037927936 Bool.false 693536 8388608 0 1000000000000000 2184466 1092233 (BSN.sin_reduce_arg_pos_rat_q3 40224713 8388608 226375608064910080 72057594037927936 0 100063368837817031458816 Ns60p84 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 693536 8388608 100063368837817031458816 Ns60p84 1421985996 17179869184 2186600 2184466 (Ns60p2671 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns60p2673 := @Enclosure.Real.IsNear.inv_image qz901 21673 262144 160208995 9162314481664 50721133 50742594 4194304 (Ns60p2664 (Ns60p2672 rfl rfl) rfl) rfl 

noncomputable def Ns60p2674 := @Enclosure.Real.IsNear.recentre' (Real.cos qz268) Bool.false 178102 4194304 

noncomputable def Ns60p2675 := @Enclosure.Real.IsNear.cos_image qz268 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 12820483)) qz337) Bool.true 12820483 8388608 

noncomputable def Ns60p2676 := nat_lit 3783938746125197773895006645 

noncomputable def Ns60p2677 := nat_lit 3145471231985066477421435152482737 

noncomputable def Ns60p2678 := @Enclosure.Real.IsNear.recentre' qz268 Bool.true Ns60p2676 Ns60p327 Ns60p2677 

noncomputable abbrev qz269 := (@HSub.hSub Real Real Real qz327 qz610 qz344)

noncomputable def Ns60p2679 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz269 884279719003555 140737488355328 1 500000000000000 4279119677639 

noncomputable abbrev qz270 := qz610

noncomputable def Ns60p2680 := @Enclosure.Real.IsNear.subLit_tf qz270 qz23 3179608049863 17592186044416 116559047 17592186044416 1 16 

noncomputable abbrev qz611 := (@HMul.hMul Real Real Real qz644 qz893 qz893)

noncomputable abbrev qz271 := qz611

noncomputable def Ns60p2681 := @Enclosure.Real.IsNear.subLit_ff_n qz271 qz266 10246279362361 17592186044416 70421703 17592186044416 3200981 4194304 11 4194304 

noncomputable def Ns60p2682 := @Enclosure.Real.IsNear.mulLit_ff qz266 qz266 3200981 4194304 11 4194304 3200981 4194304 11 4194304 10246279362361 17592186044416 

noncomputable def Ns60p2683 := nat_lit 13263898910658662959279069637217168093892770825257852854795395272089069601540692096022649841 

noncomputable def Ns60p2684 := nat_lit 19717536147327816950464312272135745411018501816524481377434718337395115128735019211761 

noncomputable def Ns60p2685 := nat_lit 80293905398226501000819594854862178941074881952287786370021721248538612408013479409521433585 

noncomputable def Ns60p2686 := BSN.cos_dyadic_bound_f 12820483 8388608 4 3 4194304 1092233 Ns60p2683 Ns60p274 Ns60p2684 Ns60p2685 Ns60p277 Ns60p2684 178102 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 12820483) (BSN.cosEvenQ 8388608) 0 3 Ns60p2683 Ns60p274 Ns60p2684 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 12820483) (BSN.cosOddQ 8388608) 0 3 Ns60p2685 Ns60p277 Ns60p2684 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns60p2687 := @Ns60p2674 195335079 4581157240832 89051 2097152 195335079 4581157240832 (@Ns60p2675 175 4194304 Bool.false 178102 4194304 1 1092233 (@Ns60p2678 Ns60p1701 12820483 8388608 175 4194304 (@Ns60p2679 17592186044416 116559047 17592186044416 Ns60p2676 Ns60p327 Ns60p2677 Ns60p1701 RS061to078.d31 (@Ns60p2680 0 1 68465914842224 4279119677639 17592186044416 116559047 17592186044416 (@Ns60p2681 13336242761972580352 3179608049863 17592186044416 116559047 17592186044416 (@Ns60p2682 70421703 17592186044416 (Ns60p2669 rfl rfl) (Ns60p2669 rfl rfl) rfl) (Ns60p2669 rfl rfl) rfl rfl) qz347 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 12820483 8388608) (BSN.cos_neg_of_bound 12820483 8388608 Bool.false 178102 4194304 1 1092233 (Ns60p2686 rfl rfl)) rfl rfl) 

noncomputable def Ns60p2688 := @Ns60p2655 38714874801925467108989 Ns60p62 (Ns60p2656 qz25 (@Enclosure.Real.IsNear.of_eq qz1111 (@Inv.inv Real Real.instInv (Real.sqrt qz267)) Bool.false 3225631 8388608 1 8388608 (BSN.rpow_neg_quarter_mk qz265 (BSN.t_div_two_pi_nonneg qz264 287396 1000 (@Eq.refl Real qz264))) Ns60p2660) rfl) (@Ns60p2661 17592186044416 11999200773444989 19214766139850620928 (BSN.correction_mk qz266 (BSN.cos_two_pi_p_ne_zero_mk qz264 287396 1000 6 (@Eq.refl Real qz264) rfl rfl (@BSN.floor_sqrt_eq_dec qz264 287396 1000 6 (@Eq.refl Real qz264) rfl rfl rfl))) (@Ns60p2662 8388608 89051 2097152 195335079 4581157240832 9035446353077 17592186044416 11999200773444989 19214766139850620928 (@Ns60p2663 8388608 (Ns60p2673 rfl rfl rfl rfl rfl) rfl) (Ns60p2687 rfl) rfl)) 

noncomputable def Ns60p2689 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz264) (hardyZApproximantRS₀ qz264) Bool.true 158074738888800874987 147573952589676412928 285860000584219116140157 Ns60p62 (@Eq.refl Real (hardyZApproximantRS₀ qz264)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz264) (@HSub.hSub Real Real Real qz11 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz264) qz264 6) (@HMul.hMul Real Real Real qz5 qz1106 (Zeta.RiemannSiegel.correction qz266))) Bool.true 158074738888800874987 147573952589676412928 285860000584219116140157 Ns60p62 (BSN.hardyZApproximantRS₀_eq qz264 6 (@BSN.floor_sqrt_eq_dec qz264 287396 1000 6 (@Eq.refl Real qz264) rfl rfl rfl)) (@Ns60p2597 158074738888800874987 147573952589676412928 285860000584219116140157 Ns60p62 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz264) qz264 6) (@HAdd.hAdd Real Real Real qz336 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz264) qz264 6) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz264) qz264 6)) Bool.true 29315225 33554432 51449 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz264) qz264 6) (Ns60p2654 (Ns60p2653 rfl rfl rfl rfl) rfl rfl)) (Ns60p2688 rfl) rfl rfl)) 

theorem RS061to078.d66 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz264) Bool.true 158074738888800874987 147573952589676412928 285860000584219116140157 Ns60p62 := Ns60p2689 

noncomputable def RS061to078.d67 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz272 := (RS061to078.d3 qz322 qz350 (@Enclosure.dec_le_dec qz322 qz350 257388 1000 259079 1000 (@Eq.refl Real qz322) (@Eq.refl Real qz350) rfl rfl rfl))

noncomputable abbrev qz1112 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz272)

noncomputable def Ns60p2690 := @Enclosure.Real.IsNear.of_eq qz1112 (hardyZApproximantRS₀ qz4) Bool.true 95660825344671766055 36893488147419103232 224276151225079826025953 Ns60p62 

noncomputable abbrev qz273 := (@Enclosure.dec_le_dec qz322 qz350 257388 1000 259079 1000 (@Eq.refl Real qz322) (@Eq.refl Real qz350) rfl rfl rfl)

noncomputable def Ns60p2691 := @Enclosure.Real.IsNear.neg_val qz1112 95660825344671766055 36893488147419103232 224276151225079826025953 Ns60p62 (Ns60p2690 (RS061to078.d4 qz4 qz26 qz273) RS061to078.d33) rfl 

noncomputable abbrev qz1113 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz272)

noncomputable def Ns60p2692 := @Enclosure.Real.IsNear.of_eq qz1113 (hardyZApproximantRS₀ qz26) Bool.false 29291985333555135051 36893488147419103232 14095523591916328334031 Ns60p176 

noncomputable def Ns60p2693 := @Enclosure.Real.IsNear.pos_val qz1113 29291985333555135051 36893488147419103232 14095523591916328334031 Ns60p176 (Ns60p2692 (RS061to078.d34 qz4 qz26 qz273) RS061to078.d35) rfl 

noncomputable def Ns60p2694 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1112 qz4 qz4 257388 1000 257388 1000 

noncomputable def Ns60p2695 := @Enclosure.norm_gt_of_isNear qz1112 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 95660825344671766055 36893488147419103232 224276151225079826025953 

noncomputable def Ns60p2696 := @Ns60p2695 Ns60p62 188700347 1342177280 1421 1342177280 (Ns60p2690 (RS061to078.d4 qz4 qz26 qz273) RS061to078.d33) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2697 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1113 qz4 qz26 257388 1000 259079 1000 

noncomputable def Ns60p2698 := @Enclosure.norm_gt_of_isNear qz1113 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 29291985333555135051 36893488147419103232 14095523591916328334031 

noncomputable def Ns60p2699 := @Ns60p2698 Ns60p176 188700347 1342177280 1421 1342177280 (Ns60p2692 (RS061to078.d34 qz4 qz26 qz273) RS061to078.d35) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2700 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz272 (@BSN.thirtyTwoPi_le_dec qz4 257388 1000 qz10 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz1112 qz1113 (Ns60p2691 rfl rfl) (Ns60p2693 rfl rfl)) (Ns60p2694 qz10 qz10 rfl rfl rfl rfl (Ns60p2696 rfl)) (Ns60p2697 qz10 qz29 rfl rfl rfl rfl (Ns60p2699 rfl)) 

noncomputable abbrev qz274 := (RS061to078.d3 qz350 qz382 (@Enclosure.dec_le_dec qz350 qz382 259079 1000 260767 1000 (@Eq.refl Real qz350) (@Eq.refl Real qz382) rfl rfl rfl))

noncomputable abbrev qz1114 := (Zeta.Certificates.ZIntervalRS.fstVal qz274)

noncomputable def Ns60p2701 := @Enclosure.Real.IsNear.of_eq qz1114 (hardyZApproximantRS qz26) Bool.false Ns60p331 Ns60p332 Ns60p333 Ns60p334 

noncomputable abbrev qz275 := (@Enclosure.dec_le_dec qz350 qz382 259079 1000 260767 1000 (@Eq.refl Real qz350) (@Eq.refl Real qz382) rfl rfl rfl)

noncomputable def Ns60p2702 := @Enclosure.Real.IsNear.pos_val qz1114 Ns60p331 Ns60p332 Ns60p333 Ns60p334 (Ns60p2701 (RS061to078.d37 qz26 qz61 qz275) RS061to078.d46) rfl 

noncomputable abbrev qz1115 := (Zeta.Certificates.ZIntervalRS.sndVal qz274)

noncomputable def Ns60p2703 := @Enclosure.Real.IsNear.of_eq qz1115 (hardyZApproximantRS qz61) Bool.true Ns60p580 Ns60p581 Ns60p582 Ns60p583 

noncomputable def Ns60p2704 := @Enclosure.Real.IsNear.neg_val qz1115 Ns60p580 Ns60p581 Ns60p582 Ns60p583 (Ns60p2703 (RS061to078.d47 qz26 qz61 qz275) RS061to078.d48) rfl 

noncomputable def Ns60p2705 := BSN.norm_gt_hardyZErrorBoundRS_of_le qz1114 qz4 qz26 257388 1000 259079 1000 

noncomputable def Ns60p2706 := @Enclosure.norm_gt_of_isNear qz1114 (hardyZErrorBoundRS qz4) Bool.false Bool.false Ns60p331 Ns60p332 Ns60p333 

noncomputable def Ns60p2707 := @Ns60p2706 Ns60p334 16188607 268435456 201 268435456 (Ns60p2701 (RS061to078.d37 qz26 qz61 qz275) RS061to078.d46) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) (hardyZErrorBoundRS qz4) Bool.false 16188607 268435456 201 268435456 (@Eq.refl Real (hardyZErrorBoundRS qz4)) RS061to078.d49) rfl rfl rfl rfl 

noncomputable def Ns60p2708 := BSN.norm_gt_hardyZErrorBoundRS_of_le qz1115 qz4 qz61 257388 1000 260767 1000 

noncomputable def Ns60p2709 := @Enclosure.norm_gt_of_isNear qz1115 (hardyZErrorBoundRS qz4) Bool.true Bool.false Ns60p580 Ns60p581 Ns60p582 

noncomputable def Ns60p2710 := @Ns60p2709 Ns60p583 16188607 268435456 201 268435456 (Ns60p2703 (RS061to078.d47 qz26 qz61 qz275) RS061to078.d48) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) (hardyZErrorBoundRS qz4) Bool.false 16188607 268435456 201 268435456 (@Eq.refl Real (hardyZErrorBoundRS qz4)) RS061to078.d49) rfl rfl rfl rfl 

noncomputable def Ns60p2711 := @Zeta.Certificates.ZIntervalRS.Certificate.mk qz274 (@BSN.thirtyTwoPi_le_dec qz26 259079 1000 qz29 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz1114 qz1115 (Ns60p2702 rfl rfl) (Ns60p2704 rfl rfl)) (Ns60p2705 qz10 qz29 rfl rfl rfl rfl (Ns60p2707 rfl)) (Ns60p2708 qz10 qz66 rfl rfl rfl rfl (Ns60p2710 rfl)) 

noncomputable abbrev qz276 := (RS061to078.d3 qz382 qz407 (@Enclosure.dec_le_dec qz382 qz407 260767 1000 262452 1000 (@Eq.refl Real qz382) (@Eq.refl Real qz407) rfl rfl rfl))

noncomputable abbrev qz1116 := (Zeta.Certificates.ZIntervalRS.fstVal qz276)

noncomputable def Ns60p2712 := @Enclosure.Real.IsNear.of_eq qz1116 (hardyZApproximantRS qz61) Bool.true Ns60p580 Ns60p581 Ns60p582 Ns60p583 

noncomputable abbrev qz277 := (@Enclosure.dec_le_dec qz382 qz407 260767 1000 262452 1000 (@Eq.refl Real qz382) (@Eq.refl Real qz407) rfl rfl rfl)

noncomputable def Ns60p2713 := @Enclosure.Real.IsNear.neg_val qz1116 Ns60p580 Ns60p581 Ns60p582 Ns60p583 (Ns60p2712 (RS061to078.d37 qz61 qz89 qz277) RS061to078.d48) rfl 

noncomputable abbrev qz1117 := (Zeta.Certificates.ZIntervalRS.sndVal qz276)

noncomputable def Ns60p2714 := @Enclosure.Real.IsNear.of_eq qz1117 (hardyZApproximantRS qz89) Bool.false Ns60p909 Ns60p910 Ns60p911 Ns60p912 

noncomputable def Ns60p2715 := @Enclosure.Real.IsNear.pos_val qz1117 Ns60p909 Ns60p910 Ns60p911 Ns60p912 (Ns60p2714 (RS061to078.d47 qz61 qz89 qz277) RS061to078.d50) rfl 

noncomputable def Ns60p2716 := BSN.norm_gt_hardyZErrorBoundRS_of_le qz1116 qz4 qz61 257388 1000 260767 1000 

noncomputable def Ns60p2717 := @Enclosure.norm_gt_of_isNear qz1116 (hardyZErrorBoundRS qz4) Bool.true Bool.false Ns60p580 Ns60p581 Ns60p582 

noncomputable def Ns60p2718 := @Ns60p2717 Ns60p583 16188607 268435456 201 268435456 (Ns60p2712 (RS061to078.d37 qz61 qz89 qz277) RS061to078.d48) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) (hardyZErrorBoundRS qz4) Bool.false 16188607 268435456 201 268435456 (@Eq.refl Real (hardyZErrorBoundRS qz4)) RS061to078.d49) rfl rfl rfl rfl 

noncomputable def Ns60p2719 := BSN.norm_gt_hardyZErrorBoundRS_of_le qz1117 qz4 qz89 257388 1000 262452 1000 

noncomputable def Ns60p2720 := @Enclosure.norm_gt_of_isNear qz1117 (hardyZErrorBoundRS qz4) Bool.false Bool.false Ns60p909 Ns60p910 Ns60p911 

noncomputable def Ns60p2721 := @Ns60p2720 Ns60p912 16188607 268435456 201 268435456 (Ns60p2714 (RS061to078.d47 qz61 qz89 qz277) RS061to078.d50) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS qz4) (hardyZErrorBoundRS qz4) Bool.false 16188607 268435456 201 268435456 (@Eq.refl Real (hardyZErrorBoundRS qz4)) RS061to078.d49) rfl rfl rfl rfl 

noncomputable def Ns60p2722 := @Zeta.Certificates.ZIntervalRS.Certificate.mk qz276 (@BSN.thirtyTwoPi_le_dec qz61 260767 1000 qz66 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz1116 qz1117 (Ns60p2713 rfl rfl) (Ns60p2715 rfl rfl)) (Ns60p2716 qz10 qz66 rfl rfl rfl rfl (Ns60p2718 rfl)) (Ns60p2719 qz10 qz94 rfl rfl rfl rfl (Ns60p2721 rfl)) 

noncomputable abbrev qz278 := (RS061to078.d3 qz407 qz432 (@Enclosure.dec_le_dec qz407 qz432 262452 1000 264134 1000 (@Eq.refl Real qz407) (@Eq.refl Real qz432) rfl rfl rfl))

noncomputable abbrev qz1118 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz278)

noncomputable def Ns60p2723 := @Enclosure.Real.IsNear.of_eq qz1118 (hardyZApproximantRS₀ qz89) Bool.false 202855289549644598029 36893488147419103232 114129105707667185686285 Ns60p1227 

noncomputable abbrev qz279 := (@Enclosure.dec_le_dec qz407 qz432 262452 1000 264134 1000 (@Eq.refl Real qz407) (@Eq.refl Real qz432) rfl rfl rfl)

noncomputable def Ns60p2724 := @Enclosure.Real.IsNear.pos_val qz1118 202855289549644598029 36893488147419103232 114129105707667185686285 Ns60p1227 (Ns60p2723 (RS061to078.d4 qz89 qz117 qz279) RS061to078.d51) rfl 

noncomputable abbrev qz1119 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz278)

noncomputable def Ns60p2725 := @Enclosure.Real.IsNear.of_eq qz1119 (hardyZApproximantRS₀ qz117) Bool.true 92600645814971143623 36893488147419103232 57423336587741302484571 Ns60p1233 

noncomputable def Ns60p2726 := @Enclosure.Real.IsNear.neg_val qz1119 92600645814971143623 36893488147419103232 57423336587741302484571 Ns60p1233 (Ns60p2725 (RS061to078.d34 qz89 qz117 qz279) RS061to078.d52) rfl 

noncomputable def Ns60p2727 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1118 qz4 qz89 257388 1000 262452 1000 

noncomputable def Ns60p2728 := @Enclosure.norm_gt_of_isNear qz1118 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 202855289549644598029 36893488147419103232 114129105707667185686285 

noncomputable def Ns60p2729 := @Ns60p2728 Ns60p1227 188700347 1342177280 1421 1342177280 (Ns60p2723 (RS061to078.d4 qz89 qz117 qz279) RS061to078.d51) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2730 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1119 qz4 qz117 257388 1000 264134 1000 

noncomputable def Ns60p2731 := @Enclosure.norm_gt_of_isNear qz1119 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 92600645814971143623 36893488147419103232 57423336587741302484571 

noncomputable def Ns60p2732 := @Ns60p2731 Ns60p1233 188700347 1342177280 1421 1342177280 (Ns60p2725 (RS061to078.d34 qz89 qz117 qz279) RS061to078.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2733 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz278 (@BSN.thirtyTwoPi_le_dec qz89 262452 1000 qz94 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz1118 qz1119 (Ns60p2724 rfl rfl) (Ns60p2726 rfl rfl)) (Ns60p2727 qz10 qz94 rfl rfl rfl rfl (Ns60p2729 rfl)) (Ns60p2730 qz10 (@Eq.refl Real qz117) rfl rfl rfl rfl (Ns60p2732 rfl)) 

noncomputable abbrev qz280 := (RS061to078.d3 qz432 qz444 (@Enclosure.dec_le_dec qz432 qz444 264134 1000 265813 1000 (@Eq.refl Real qz432) (@Eq.refl Real qz444) rfl rfl rfl))

noncomputable abbrev qz1120 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz280)

noncomputable def Ns60p2734 := @Enclosure.Real.IsNear.of_eq qz1120 (hardyZApproximantRS₀ qz117) Bool.true 92600645814971143623 36893488147419103232 57423336587741302484571 Ns60p1233 

noncomputable abbrev qz281 := (@Enclosure.dec_le_dec qz432 qz444 264134 1000 265813 1000 (@Eq.refl Real qz432) (@Eq.refl Real qz444) rfl rfl rfl)

noncomputable def Ns60p2735 := @Enclosure.Real.IsNear.neg_val qz1120 92600645814971143623 36893488147419103232 57423336587741302484571 Ns60p1233 (Ns60p2734 (RS061to078.d4 qz117 qz127 qz281) RS061to078.d52) rfl 

noncomputable abbrev qz1121 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz280)

noncomputable def Ns60p2736 := @Enclosure.Real.IsNear.of_eq qz1121 (hardyZApproximantRS₀ qz127) Bool.false 2278180188934562285 4611686018427387904 57783213280804673213131 Ns60p1233 

noncomputable def Ns60p2737 := @Enclosure.Real.IsNear.pos_val qz1121 2278180188934562285 4611686018427387904 57783213280804673213131 Ns60p1233 (Ns60p2736 (RS061to078.d34 qz117 qz127 qz281) RS061to078.d53) rfl 

noncomputable def Ns60p2738 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1120 qz4 qz117 257388 1000 264134 1000 

noncomputable def Ns60p2739 := @Enclosure.norm_gt_of_isNear qz1120 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 92600645814971143623 36893488147419103232 57423336587741302484571 

noncomputable def Ns60p2740 := @Ns60p2739 Ns60p1233 188700347 1342177280 1421 1342177280 (Ns60p2734 (RS061to078.d4 qz117 qz127 qz281) RS061to078.d52) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2741 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1121 qz4 qz127 257388 1000 265813 1000 

noncomputable def Ns60p2742 := @Enclosure.norm_gt_of_isNear qz1121 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2278180188934562285 4611686018427387904 57783213280804673213131 

noncomputable def Ns60p2743 := @Ns60p2742 Ns60p1233 188700347 1342177280 1421 1342177280 (Ns60p2736 (RS061to078.d34 qz117 qz127 qz281) RS061to078.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2744 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz280 (@BSN.thirtyTwoPi_le_dec qz117 264134 1000 (@Eq.refl Real qz117) rfl rfl) (BSN.mul_neg_of_neg_pos_r qz1120 qz1121 (Ns60p2735 rfl rfl) (Ns60p2737 rfl rfl)) (Ns60p2738 qz10 (@Eq.refl Real qz117) rfl rfl rfl rfl (Ns60p2740 rfl)) (Ns60p2741 qz10 (@Eq.refl Real qz127) rfl rfl rfl rfl (Ns60p2743 rfl)) 

noncomputable abbrev qz282 := (RS061to078.d3 qz444 qz456 (@Enclosure.dec_le_dec qz444 qz456 265813 1000 267489 1000 (@Eq.refl Real qz444) (@Eq.refl Real qz456) rfl rfl rfl))

noncomputable abbrev qz1122 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz282)

noncomputable def Ns60p2745 := @Enclosure.Real.IsNear.of_eq qz1122 (hardyZApproximantRS₀ qz127) Bool.false 2278180188934562285 4611686018427387904 57783213280804673213131 Ns60p1233 

noncomputable abbrev qz283 := (@Enclosure.dec_le_dec qz444 qz456 265813 1000 267489 1000 (@Eq.refl Real qz444) (@Eq.refl Real qz456) rfl rfl rfl)

noncomputable def Ns60p2746 := @Enclosure.Real.IsNear.pos_val qz1122 2278180188934562285 4611686018427387904 57783213280804673213131 Ns60p1233 (Ns60p2745 (RS061to078.d4 qz127 qz137 qz283) RS061to078.d53) rfl 

noncomputable abbrev qz1123 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz282)

noncomputable def Ns60p2747 := @Enclosure.Real.IsNear.of_eq qz1123 (hardyZApproximantRS₀ qz137) Bool.true 15528419154603761849 18446744073709551616 232627838496892867859831 Ns60p62 

noncomputable def Ns60p2748 := @Enclosure.Real.IsNear.neg_val qz1123 15528419154603761849 18446744073709551616 232627838496892867859831 Ns60p62 (Ns60p2747 (RS061to078.d34 qz127 qz137 qz283) RS061to078.d54) rfl 

noncomputable def Ns60p2749 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1122 qz4 qz127 257388 1000 265813 1000 

noncomputable def Ns60p2750 := @Enclosure.norm_gt_of_isNear qz1122 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 2278180188934562285 4611686018427387904 57783213280804673213131 

noncomputable def Ns60p2751 := @Ns60p2750 Ns60p1233 188700347 1342177280 1421 1342177280 (Ns60p2745 (RS061to078.d4 qz127 qz137 qz283) RS061to078.d53) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2752 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1123 qz4 qz137 257388 1000 267489 1000 

noncomputable def Ns60p2753 := @Enclosure.norm_gt_of_isNear qz1123 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 15528419154603761849 18446744073709551616 232627838496892867859831 

noncomputable def Ns60p2754 := @Ns60p2753 Ns60p62 188700347 1342177280 1421 1342177280 (Ns60p2747 (RS061to078.d34 qz127 qz137 qz283) RS061to078.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2755 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz282 (@BSN.thirtyTwoPi_le_dec qz127 265813 1000 (@Eq.refl Real qz127) rfl rfl) (BSN.mul_neg_of_pos_neg_r qz1122 qz1123 (Ns60p2746 rfl rfl) (Ns60p2748 rfl rfl)) (Ns60p2749 qz10 (@Eq.refl Real qz127) rfl rfl rfl rfl (Ns60p2751 rfl)) (Ns60p2752 qz10 (@Eq.refl Real qz137) rfl rfl rfl rfl (Ns60p2754 rfl)) 

noncomputable abbrev qz903 := (@Enclosure.dec_le_dec qz456 qz468 267489 1000 269163 1000 (@Eq.refl Real qz456) (@Eq.refl Real qz468) rfl rfl rfl)

noncomputable abbrev qz284 := (RS061to078.d3 qz456 qz468 qz903)

noncomputable abbrev qz1124 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz284)

noncomputable def Ns60p2756 := @Enclosure.Real.IsNear.of_eq qz1124 (hardyZApproximantRS₀ qz137) Bool.true 15528419154603761849 18446744073709551616 232627838496892867859831 Ns60p62 

noncomputable abbrev qz285 := qz903

noncomputable def Ns60p2757 := @Enclosure.Real.IsNear.neg_val qz1124 15528419154603761849 18446744073709551616 232627838496892867859831 Ns60p62 (Ns60p2756 (RS061to078.d4 qz137 qz147 qz285) RS061to078.d54) rfl 

noncomputable abbrev qz1125 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz284)

noncomputable def Ns60p2758 := @Enclosure.Real.IsNear.of_eq qz1125 (hardyZApproximantRS₀ qz147) Bool.false 375057532675782245343 147573952589676412928 13783268240755920933799 Ns60p1520 

noncomputable def Ns60p2759 := @Enclosure.Real.IsNear.pos_val qz1125 375057532675782245343 147573952589676412928 13783268240755920933799 Ns60p1520 (Ns60p2758 (RS061to078.d34 qz137 qz147 qz285) RS061to078.d55) rfl 

noncomputable def Ns60p2760 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1124 qz4 qz137 257388 1000 267489 1000 

noncomputable def Ns60p2761 := @Enclosure.norm_gt_of_isNear qz1124 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 15528419154603761849 18446744073709551616 232627838496892867859831 

noncomputable def Ns60p2762 := @Ns60p2761 Ns60p62 188700347 1342177280 1421 1342177280 (Ns60p2756 (RS061to078.d4 qz137 qz147 qz285) RS061to078.d54) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2763 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1125 qz4 qz147 257388 1000 269163 1000 

noncomputable def Ns60p2764 := @Enclosure.norm_gt_of_isNear qz1125 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 375057532675782245343 147573952589676412928 13783268240755920933799 

noncomputable def Ns60p2765 := @Ns60p2764 Ns60p1520 188700347 1342177280 1421 1342177280 (Ns60p2758 (RS061to078.d34 qz137 qz147 qz285) RS061to078.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2766 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz137 267489 1000 (@Eq.refl Real qz137) rfl rfl) (BSN.mul_neg_of_neg_pos_r qz1124 qz1125 (Ns60p2757 rfl rfl) (Ns60p2759 rfl rfl)) (Ns60p2760 qz10 (@Eq.refl Real qz137) rfl rfl rfl rfl (Ns60p2762 rfl)) (Ns60p2763 qz10 (@Eq.refl Real qz147) rfl rfl rfl rfl (Ns60p2765 rfl)) 

noncomputable abbrev qz612 := (@Enclosure.dec_le_dec qz781 qz791 269163 1000 270834 1000 (@Eq.refl Real qz781) (@Eq.refl Real qz791) rfl rfl rfl)

noncomputable abbrev qz286 := (RS061to078.d3 qz468 qz480 qz612)

noncomputable abbrev qz1126 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz286)

noncomputable def Ns60p2767 := @Enclosure.Real.IsNear.of_eq qz1126 (hardyZApproximantRS₀ qz147) Bool.false 375057532675782245343 147573952589676412928 13783268240755920933799 Ns60p1520 

noncomputable abbrev qz287 := qz612

noncomputable def Ns60p2768 := @Enclosure.Real.IsNear.pos_val qz1126 375057532675782245343 147573952589676412928 13783268240755920933799 Ns60p1520 (Ns60p2767 (RS061to078.d4 qz147 qz157 qz287) RS061to078.d55) rfl 

noncomputable abbrev qz1127 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz286)

noncomputable def Ns60p2769 := @Enclosure.Real.IsNear.of_eq qz1127 (hardyZApproximantRS₀ qz157) Bool.true 72098255100961040373 36893488147419103232 58982114656143983889423 Ns60p1233 

noncomputable def Ns60p2770 := @Enclosure.Real.IsNear.neg_val qz1127 72098255100961040373 36893488147419103232 58982114656143983889423 Ns60p1233 (Ns60p2769 (RS061to078.d34 qz147 qz157 qz287) RS061to078.d56) rfl 

noncomputable def Ns60p2771 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1126 qz4 qz147 257388 1000 269163 1000 

noncomputable def Ns60p2772 := @Enclosure.norm_gt_of_isNear qz1126 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 375057532675782245343 147573952589676412928 13783268240755920933799 

noncomputable def Ns60p2773 := @Ns60p2772 Ns60p1520 188700347 1342177280 1421 1342177280 (Ns60p2767 (RS061to078.d4 qz147 qz157 qz287) RS061to078.d55) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2774 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1127 qz4 qz157 257388 1000 270834 1000 

noncomputable def Ns60p2775 := @Enclosure.norm_gt_of_isNear qz1127 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 72098255100961040373 36893488147419103232 58982114656143983889423 

noncomputable def Ns60p2776 := @Ns60p2775 Ns60p1233 188700347 1342177280 1421 1342177280 (Ns60p2769 (RS061to078.d34 qz147 qz157 qz287) RS061to078.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2777 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz286 (@BSN.thirtyTwoPi_le_dec qz147 269163 1000 (@Eq.refl Real qz147) rfl rfl) (BSN.mul_neg_of_pos_neg_r qz1126 qz1127 (Ns60p2768 rfl rfl) (Ns60p2770 rfl rfl)) (Ns60p2771 qz10 (@Eq.refl Real qz147) rfl rfl rfl rfl (Ns60p2773 rfl)) (Ns60p2774 qz10 qz160 rfl rfl rfl rfl (Ns60p2776 rfl)) 

noncomputable abbrev qz904 := (@Eq.refl Real qz1027)

noncomputable abbrev qz613 := (@Enclosure.dec_le_dec qz791 qz801 270834 1000 272502 1000 (@Eq.refl Real qz791) qz904 rfl rfl rfl)

noncomputable abbrev qz288 := (RS061to078.d3 qz480 qz492 qz613)

noncomputable abbrev qz1128 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz288)

noncomputable def Ns60p2778 := @Enclosure.Real.IsNear.of_eq qz1128 (hardyZApproximantRS₀ qz157) Bool.true 72098255100961040373 36893488147419103232 58982114656143983889423 Ns60p1233 

noncomputable abbrev qz289 := qz613

noncomputable def Ns60p2779 := @Enclosure.Real.IsNear.neg_val qz1128 72098255100961040373 36893488147419103232 58982114656143983889423 Ns60p1233 (Ns60p2778 (RS061to078.d4 qz157 qz168 qz289) RS061to078.d56) rfl 

noncomputable abbrev qz1129 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz288)

noncomputable def Ns60p2780 := @Enclosure.Real.IsNear.of_eq qz1129 (hardyZApproximantRS₀ qz168) Bool.false 14964286694946276595 4611686018427387904 157871814383202927653 107170971382234067501056 

noncomputable def Ns60p2781 := @Enclosure.Real.IsNear.pos_val qz1129 14964286694946276595 4611686018427387904 157871814383202927653 107170971382234067501056 (Ns60p2780 (RS061to078.d34 qz157 qz168 qz289) RS061to078.d57) rfl 

noncomputable def Ns60p2782 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1128 qz4 qz157 257388 1000 270834 1000 

noncomputable def Ns60p2783 := @Enclosure.norm_gt_of_isNear qz1128 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 72098255100961040373 36893488147419103232 58982114656143983889423 

noncomputable def Ns60p2784 := @Ns60p2783 Ns60p1233 188700347 1342177280 1421 1342177280 (Ns60p2778 (RS061to078.d4 qz157 qz168 qz289) RS061to078.d56) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2785 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1129 qz4 qz168 257388 1000 272502 1000 

noncomputable def Ns60p2786 := @Enclosure.norm_gt_of_isNear qz1129 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 14964286694946276595 4611686018427387904 157871814383202927653 

noncomputable def Ns60p2787 := @Ns60p2786 107170971382234067501056 188700347 1342177280 1421 1342177280 (Ns60p2780 (RS061to078.d34 qz157 qz168 qz289) RS061to078.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2788 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz157 270834 1000 qz160 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz1128 qz1129 (Ns60p2779 rfl rfl) (Ns60p2781 rfl rfl)) (Ns60p2782 qz10 qz160 rfl rfl rfl rfl (Ns60p2784 rfl)) (Ns60p2785 qz10 qz171 rfl rfl rfl rfl (Ns60p2787 rfl)) 

noncomputable abbrev qz905 := (@Enclosure.dec_le_dec qz1027 qz1036 272502 1000 274167 1000 (@Eq.refl Real qz1027) (@Eq.refl Real qz1036) rfl rfl rfl)

noncomputable abbrev qz614 := qz905

noncomputable abbrev qz290 := (RS061to078.d3 qz492 qz504 qz614)

noncomputable abbrev qz1130 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz290)

noncomputable def Ns60p2789 := @Enclosure.Real.IsNear.of_eq qz1130 (hardyZApproximantRS₀ qz168) Bool.false 14964286694946276595 4611686018427387904 157871814383202927653 107170971382234067501056 

noncomputable abbrev qz291 := qz614

noncomputable def Ns60p2790 := @Enclosure.Real.IsNear.pos_val qz1130 14964286694946276595 4611686018427387904 157871814383202927653 107170971382234067501056 (Ns60p2789 (RS061to078.d4 qz168 qz179 qz291) RS061to078.d57) rfl 

noncomputable abbrev qz1131 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz290)

noncomputable def Ns60p2791 := @Enclosure.Real.IsNear.of_eq qz1131 (hardyZApproximantRS₀ qz179) Bool.true 25087399415920097923 9223372036854775808 239353687216267346002731 Ns60p62 

noncomputable def Ns60p2792 := @Enclosure.Real.IsNear.neg_val qz1131 25087399415920097923 9223372036854775808 239353687216267346002731 Ns60p62 (Ns60p2791 (RS061to078.d34 qz168 qz179 qz291) RS061to078.d58) rfl 

noncomputable def Ns60p2793 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1130 qz4 qz168 257388 1000 272502 1000 

noncomputable def Ns60p2794 := @Enclosure.norm_gt_of_isNear qz1130 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 14964286694946276595 4611686018427387904 157871814383202927653 

noncomputable def Ns60p2795 := @Ns60p2794 107170971382234067501056 188700347 1342177280 1421 1342177280 (Ns60p2789 (RS061to078.d4 qz168 qz179 qz291) RS061to078.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2796 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1131 qz4 qz179 257388 1000 274167 1000 

noncomputable def Ns60p2797 := @Enclosure.norm_gt_of_isNear qz1131 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 25087399415920097923 9223372036854775808 239353687216267346002731 

noncomputable def Ns60p2798 := @Ns60p2797 Ns60p62 188700347 1342177280 1421 1342177280 (Ns60p2791 (RS061to078.d34 qz168 qz179 qz291) RS061to078.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2799 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz290 (@BSN.thirtyTwoPi_le_dec qz168 272502 1000 qz171 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz1130 qz1131 (Ns60p2790 rfl rfl) (Ns60p2792 rfl rfl)) (Ns60p2793 qz10 qz171 rfl rfl rfl rfl (Ns60p2795 rfl)) (Ns60p2796 qz10 qz182 rfl rfl rfl rfl (Ns60p2798 rfl)) 

noncomputable abbrev qz906 := (@Enclosure.dec_le_dec qz1036 qz1045 274167 1000 275830 1000 (@Eq.refl Real qz1036) (@Eq.refl Real qz1045) rfl rfl rfl)

noncomputable abbrev qz615 := qz906

noncomputable abbrev qz292 := (RS061to078.d3 qz504 qz516 qz615)

noncomputable abbrev qz1132 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz292)

noncomputable def Ns60p2800 := @Enclosure.Real.IsNear.of_eq qz1132 (hardyZApproximantRS₀ qz179) Bool.true 25087399415920097923 9223372036854775808 239353687216267346002731 Ns60p62 

noncomputable abbrev qz293 := qz615

noncomputable def Ns60p2801 := @Enclosure.Real.IsNear.neg_val qz1132 25087399415920097923 9223372036854775808 239353687216267346002731 Ns60p62 (Ns60p2800 (RS061to078.d4 qz179 qz190 qz293) RS061to078.d58) rfl 

noncomputable abbrev qz1133 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz292)

noncomputable def Ns60p2802 := @Enclosure.Real.IsNear.of_eq qz1133 (hardyZApproximantRS₀ qz190) Bool.false 57600303278089392743 147573952589676412928 176505297010908378417 117911588119151453929472 

noncomputable def Ns60p2803 := @Enclosure.Real.IsNear.pos_val qz1133 57600303278089392743 147573952589676412928 176505297010908378417 117911588119151453929472 (Ns60p2802 (RS061to078.d34 qz179 qz190 qz293) RS061to078.d59) rfl 

noncomputable def Ns60p2804 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1132 qz4 qz179 257388 1000 274167 1000 

noncomputable def Ns60p2805 := @Enclosure.norm_gt_of_isNear qz1132 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 25087399415920097923 9223372036854775808 239353687216267346002731 

noncomputable def Ns60p2806 := @Ns60p2805 Ns60p62 188700347 1342177280 1421 1342177280 (Ns60p2800 (RS061to078.d4 qz179 qz190 qz293) RS061to078.d58) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2807 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1133 qz4 qz190 257388 1000 275830 1000 

noncomputable def Ns60p2808 := @Enclosure.norm_gt_of_isNear qz1133 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 57600303278089392743 147573952589676412928 176505297010908378417 

noncomputable def Ns60p2809 := @Ns60p2808 117911588119151453929472 188700347 1342177280 1421 1342177280 (Ns60p2802 (RS061to078.d34 qz179 qz190 qz293) RS061to078.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2810 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz179 274167 1000 qz182 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz1132 qz1133 (Ns60p2801 rfl rfl) (Ns60p2803 rfl rfl)) (Ns60p2804 qz10 qz182 rfl rfl rfl rfl (Ns60p2806 rfl)) (Ns60p2807 qz10 qz193 rfl rfl rfl rfl (Ns60p2809 rfl)) 

noncomputable abbrev qz294 := (RS061to078.d3 qz516 qz528 (@Enclosure.dec_le_dec qz516 qz528 275830 1000 277490 1000 (@Eq.refl Real qz516) (@Eq.refl Real qz528) rfl rfl rfl))

noncomputable abbrev qz1134 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz294)

noncomputable def Ns60p2811 := @Enclosure.Real.IsNear.of_eq qz1134 (hardyZApproximantRS₀ qz190) Bool.false 57600303278089392743 147573952589676412928 176505297010908378417 117911588119151453929472 

noncomputable abbrev qz295 := (@Enclosure.dec_le_dec qz516 qz528 275830 1000 277490 1000 (@Eq.refl Real qz516) (@Eq.refl Real qz528) rfl rfl rfl)

noncomputable def Ns60p2812 := @Enclosure.Real.IsNear.pos_val qz1134 57600303278089392743 147573952589676412928 176505297010908378417 117911588119151453929472 (Ns60p2811 (RS061to078.d4 qz190 qz201 qz295) RS061to078.d59) rfl 

noncomputable abbrev qz1135 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz294)

noncomputable def Ns60p2813 := @Enclosure.Real.IsNear.of_eq qz1135 (hardyZApproximantRS₀ qz201) Bool.true 830958145988036249 576460752303423488 121699501312936300229005 Ns60p1227 

noncomputable def Ns60p2814 := @Enclosure.Real.IsNear.neg_val qz1135 830958145988036249 576460752303423488 121699501312936300229005 Ns60p1227 (Ns60p2813 (RS061to078.d34 qz190 qz201 qz295) RS061to078.d60) rfl 

noncomputable def Ns60p2815 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1134 qz4 qz190 257388 1000 275830 1000 

noncomputable def Ns60p2816 := @Enclosure.norm_gt_of_isNear qz1134 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 57600303278089392743 147573952589676412928 176505297010908378417 

noncomputable def Ns60p2817 := @Ns60p2816 117911588119151453929472 188700347 1342177280 1421 1342177280 (Ns60p2811 (RS061to078.d4 qz190 qz201 qz295) RS061to078.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2818 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1135 qz4 qz201 257388 1000 277490 1000 

noncomputable def Ns60p2819 := @Enclosure.norm_gt_of_isNear qz1135 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 830958145988036249 576460752303423488 121699501312936300229005 

noncomputable def Ns60p2820 := @Ns60p2819 Ns60p1227 188700347 1342177280 1421 1342177280 (Ns60p2813 (RS061to078.d34 qz190 qz201 qz295) RS061to078.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2821 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz294 (@BSN.thirtyTwoPi_le_dec qz190 275830 1000 qz193 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz1134 qz1135 (Ns60p2812 rfl rfl) (Ns60p2814 rfl rfl)) (Ns60p2815 qz10 qz193 rfl rfl rfl rfl (Ns60p2817 rfl)) (Ns60p2818 qz10 (@Eq.refl Real qz201) rfl rfl rfl rfl (Ns60p2820 rfl)) 

noncomputable abbrev qz296 := (RS061to078.d3 qz528 qz540 (@Enclosure.dec_le_dec qz528 qz540 277490 1000 279148 1000 (@Eq.refl Real qz528) (@Eq.refl Real qz540) rfl rfl rfl))

noncomputable abbrev qz1136 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz296)

noncomputable def Ns60p2822 := @Enclosure.Real.IsNear.of_eq qz1136 (hardyZApproximantRS₀ qz201) Bool.true 830958145988036249 576460752303423488 121699501312936300229005 Ns60p1227 

noncomputable abbrev qz297 := (@Enclosure.dec_le_dec qz528 qz540 277490 1000 279148 1000 (@Eq.refl Real qz528) (@Eq.refl Real qz540) rfl rfl rfl)

noncomputable def Ns60p2823 := @Enclosure.Real.IsNear.neg_val qz1136 830958145988036249 576460752303423488 121699501312936300229005 Ns60p1227 (Ns60p2822 (RS061to078.d4 qz201 qz211 qz297) RS061to078.d60) rfl 

noncomputable abbrev qz1137 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz296)

noncomputable def Ns60p2824 := @Enclosure.Real.IsNear.of_eq qz1137 (hardyZApproximantRS₀ qz211) Bool.false 9395281912706451295 36893488147419103232 61476352278844731650079 Ns60p1233 

noncomputable def Ns60p2825 := @Enclosure.Real.IsNear.pos_val qz1137 9395281912706451295 36893488147419103232 61476352278844731650079 Ns60p1233 (Ns60p2824 (RS061to078.d34 qz201 qz211 qz297) RS061to078.d61) rfl 

noncomputable def Ns60p2826 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1136 qz4 qz201 257388 1000 277490 1000 

noncomputable def Ns60p2827 := @Enclosure.norm_gt_of_isNear qz1136 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 830958145988036249 576460752303423488 121699501312936300229005 

noncomputable def Ns60p2828 := @Ns60p2827 Ns60p1227 188700347 1342177280 1421 1342177280 (Ns60p2822 (RS061to078.d4 qz201 qz211 qz297) RS061to078.d60) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2829 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1137 qz4 qz211 257388 1000 279148 1000 

noncomputable def Ns60p2830 := @Enclosure.norm_gt_of_isNear qz1137 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 9395281912706451295 36893488147419103232 61476352278844731650079 

noncomputable def Ns60p2831 := @Ns60p2830 Ns60p1233 188700347 1342177280 1421 1342177280 (Ns60p2824 (RS061to078.d34 qz201 qz211 qz297) RS061to078.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2832 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz296 (@BSN.thirtyTwoPi_le_dec qz201 277490 1000 (@Eq.refl Real qz201) rfl rfl) (BSN.mul_neg_of_neg_pos_r qz1136 qz1137 (Ns60p2823 rfl rfl) (Ns60p2825 rfl rfl)) (Ns60p2826 qz10 (@Eq.refl Real qz201) rfl rfl rfl rfl (Ns60p2828 rfl)) (Ns60p2829 qz10 (@Eq.refl Real qz211) rfl rfl rfl rfl (Ns60p2831 rfl)) 

noncomputable abbrev qz907 := (@Enclosure.dec_le_dec qz540 qz552 279148 1000 281629 1000 (@Eq.refl Real qz540) (@Eq.refl Real qz552) rfl rfl rfl)

noncomputable abbrev qz298 := (RS061to078.d3 qz540 qz552 qz907)

noncomputable abbrev qz1138 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz298)

noncomputable def Ns60p2833 := @Enclosure.Real.IsNear.of_eq qz1138 (hardyZApproximantRS₀ qz211) Bool.false 9395281912706451295 36893488147419103232 61476352278844731650079 Ns60p1233 

noncomputable abbrev qz299 := qz907

noncomputable def Ns60p2834 := @Enclosure.Real.IsNear.pos_val qz1138 9395281912706451295 36893488147419103232 61476352278844731650079 Ns60p1233 (Ns60p2833 (RS061to078.d4 qz211 qz221 qz299) RS061to078.d61) rfl 

noncomputable abbrev qz1139 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz298)

noncomputable def Ns60p2835 := @Enclosure.Real.IsNear.of_eq qz1139 (hardyZApproximantRS₀ qz221) Bool.true 304134841707756217073 73786976294838206464 125542993645754088958967 Ns60p1227 

noncomputable def Ns60p2836 := @Enclosure.Real.IsNear.neg_val qz1139 304134841707756217073 73786976294838206464 125542993645754088958967 Ns60p1227 (Ns60p2835 (RS061to078.d34 qz211 qz221 qz299) RS061to078.d62) rfl 

noncomputable def Ns60p2837 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1138 qz4 qz211 257388 1000 279148 1000 

noncomputable def Ns60p2838 := @Enclosure.norm_gt_of_isNear qz1138 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 9395281912706451295 36893488147419103232 61476352278844731650079 

noncomputable def Ns60p2839 := @Ns60p2838 Ns60p1233 188700347 1342177280 1421 1342177280 (Ns60p2833 (RS061to078.d4 qz211 qz221 qz299) RS061to078.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2840 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1139 qz4 qz221 257388 1000 281629 1000 

noncomputable def Ns60p2841 := @Enclosure.norm_gt_of_isNear qz1139 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 304134841707756217073 73786976294838206464 125542993645754088958967 

noncomputable def Ns60p2842 := @Ns60p2841 Ns60p1227 188700347 1342177280 1421 1342177280 (Ns60p2835 (RS061to078.d34 qz211 qz221 qz299) RS061to078.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2843 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz298 (@BSN.thirtyTwoPi_le_dec qz211 279148 1000 (@Eq.refl Real qz211) rfl rfl) (BSN.mul_neg_of_pos_neg_r qz1138 qz1139 (Ns60p2834 rfl rfl) (Ns60p2836 rfl rfl)) (Ns60p2837 qz10 (@Eq.refl Real qz211) rfl rfl rfl rfl (Ns60p2839 rfl)) (Ns60p2840 qz10 (@Eq.refl Real qz221) rfl rfl rfl rfl (Ns60p2842 rfl)) 

noncomputable abbrev qz616 := (@Enclosure.dec_le_dec qz851 qz861 281629 1000 282868 1000 (@Eq.refl Real qz851) (@Eq.refl Real qz861) rfl rfl rfl)

noncomputable abbrev qz300 := (RS061to078.d3 qz552 qz564 qz616)

noncomputable abbrev qz1140 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz300)

noncomputable def Ns60p2844 := @Enclosure.Real.IsNear.of_eq qz1140 (hardyZApproximantRS₀ qz221) Bool.true 304134841707756217073 73786976294838206464 125542993645754088958967 Ns60p1227 

noncomputable abbrev qz301 := qz616

noncomputable def Ns60p2845 := @Enclosure.Real.IsNear.neg_val qz1140 304134841707756217073 73786976294838206464 125542993645754088958967 Ns60p1227 (Ns60p2844 (RS061to078.d4 qz221 qz231 qz301) RS061to078.d62) rfl 

noncomputable abbrev qz1141 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz300)

noncomputable def Ns60p2846 := @Enclosure.Real.IsNear.of_eq qz1141 (hardyZApproximantRS₀ qz231) Bool.false 8090844534573020963 18446744073709551616 31929324009917793270171 Ns60p2305 

noncomputable def Ns60p2847 := @Enclosure.Real.IsNear.pos_val qz1141 8090844534573020963 18446744073709551616 31929324009917793270171 Ns60p2305 (Ns60p2846 (RS061to078.d34 qz221 qz231 qz301) RS061to078.d63) rfl 

noncomputable def Ns60p2848 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1140 qz4 qz221 257388 1000 281629 1000 

noncomputable def Ns60p2849 := @Enclosure.norm_gt_of_isNear qz1140 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 304134841707756217073 73786976294838206464 125542993645754088958967 

noncomputable def Ns60p2850 := @Ns60p2849 Ns60p1227 188700347 1342177280 1421 1342177280 (Ns60p2844 (RS061to078.d4 qz221 qz231 qz301) RS061to078.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2851 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1141 qz4 qz231 257388 1000 282868 1000 

noncomputable def Ns60p2852 := @Enclosure.norm_gt_of_isNear qz1141 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 8090844534573020963 18446744073709551616 31929324009917793270171 

noncomputable def Ns60p2853 := @Ns60p2852 Ns60p2305 188700347 1342177280 1421 1342177280 (Ns60p2846 (RS061to078.d34 qz221 qz231 qz301) RS061to078.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2854 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz221 281629 1000 (@Eq.refl Real qz221) rfl rfl) (BSN.mul_neg_of_neg_pos_r qz1140 qz1141 (Ns60p2845 rfl rfl) (Ns60p2847 rfl rfl)) (Ns60p2848 qz10 (@Eq.refl Real qz221) rfl rfl rfl rfl (Ns60p2850 rfl)) (Ns60p2851 qz10 qz234 rfl rfl rfl rfl (Ns60p2853 rfl)) 

noncomputable abbrev qz908 := (@Eq.refl Real qz1086)

noncomputable abbrev qz617 := (@Enclosure.dec_le_dec qz861 qz871 282868 1000 283692 1000 (@Eq.refl Real qz861) qz908 rfl rfl rfl)

noncomputable abbrev qz302 := (RS061to078.d3 qz564 qz576 qz617)

noncomputable abbrev qz1142 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz302)

noncomputable def Ns60p2855 := @Enclosure.Real.IsNear.of_eq qz1142 (hardyZApproximantRS₀ qz231) Bool.false 8090844534573020963 18446744073709551616 31929324009917793270171 Ns60p2305 

noncomputable abbrev qz303 := qz617

noncomputable def Ns60p2856 := @Enclosure.Real.IsNear.pos_val qz1142 8090844534573020963 18446744073709551616 31929324009917793270171 Ns60p2305 (Ns60p2855 (RS061to078.d4 qz231 qz242 qz303) RS061to078.d63) rfl 

noncomputable abbrev qz1143 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz302)

noncomputable def Ns60p2857 := @Enclosure.Real.IsNear.of_eq qz1143 (hardyZApproximantRS₀ qz242) Bool.true 1195646300398369387 1152921504606846976 65201678738489365327427 Ns60p1233 

noncomputable def Ns60p2858 := @Enclosure.Real.IsNear.neg_val qz1143 1195646300398369387 1152921504606846976 65201678738489365327427 Ns60p1233 (Ns60p2857 (RS061to078.d34 qz231 qz242 qz303) RS061to078.d64) rfl 

noncomputable def Ns60p2859 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1142 qz4 qz231 257388 1000 282868 1000 

noncomputable def Ns60p2860 := @Enclosure.norm_gt_of_isNear qz1142 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 8090844534573020963 18446744073709551616 31929324009917793270171 

noncomputable def Ns60p2861 := @Ns60p2860 Ns60p2305 188700347 1342177280 1421 1342177280 (Ns60p2855 (RS061to078.d4 qz231 qz242 qz303) RS061to078.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2862 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1143 qz4 qz242 257388 1000 283692 1000 

noncomputable def Ns60p2863 := @Enclosure.norm_gt_of_isNear qz1143 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1195646300398369387 1152921504606846976 65201678738489365327427 

noncomputable def Ns60p2864 := @Ns60p2863 Ns60p1233 188700347 1342177280 1421 1342177280 (Ns60p2857 (RS061to078.d34 qz231 qz242 qz303) RS061to078.d64) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2865 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz302 (@BSN.thirtyTwoPi_le_dec qz231 282868 1000 qz234 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz1142 qz1143 (Ns60p2856 rfl rfl) (Ns60p2858 rfl rfl)) (Ns60p2859 qz10 qz234 rfl rfl rfl rfl (Ns60p2861 rfl)) (Ns60p2862 qz10 qz245 rfl rfl rfl rfl (Ns60p2864 rfl)) 

noncomputable abbrev qz909 := (@Enclosure.dec_le_dec qz1086 qz1095 283692 1000 285752 1000 (@Eq.refl Real qz1086) (@Eq.refl Real qz1095) rfl rfl rfl)

noncomputable abbrev qz618 := qz909

noncomputable abbrev qz304 := (RS061to078.d3 qz576 qz588 qz618)

noncomputable abbrev qz1144 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz304)

noncomputable def Ns60p2866 := @Enclosure.Real.IsNear.of_eq qz1144 (hardyZApproximantRS₀ qz242) Bool.true 1195646300398369387 1152921504606846976 65201678738489365327427 Ns60p1233 

noncomputable abbrev qz305 := qz618

noncomputable def Ns60p2867 := @Enclosure.Real.IsNear.neg_val qz1144 1195646300398369387 1152921504606846976 65201678738489365327427 Ns60p1233 (Ns60p2866 (RS061to078.d4 qz242 qz253 qz305) RS061to078.d64) rfl 

noncomputable abbrev qz1145 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz304)

noncomputable def Ns60p2868 := @Enclosure.Real.IsNear.of_eq qz1145 (hardyZApproximantRS₀ qz253) Bool.false 36522145614582757673 18446744073709551616 326657988797450466707709 Ns60p62 

noncomputable def Ns60p2869 := @Enclosure.Real.IsNear.pos_val qz1145 36522145614582757673 18446744073709551616 326657988797450466707709 Ns60p62 (Ns60p2868 (RS061to078.d34 qz242 qz253 qz305) RS061to078.d65) rfl 

noncomputable def Ns60p2870 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1144 qz4 qz242 257388 1000 283692 1000 

noncomputable def Ns60p2871 := @Enclosure.norm_gt_of_isNear qz1144 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 1195646300398369387 1152921504606846976 65201678738489365327427 

noncomputable def Ns60p2872 := @Ns60p2871 Ns60p1233 188700347 1342177280 1421 1342177280 (Ns60p2866 (RS061to078.d4 qz242 qz253 qz305) RS061to078.d64) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2873 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1145 qz4 qz253 257388 1000 285752 1000 

noncomputable def Ns60p2874 := @Enclosure.norm_gt_of_isNear qz1145 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 36522145614582757673 18446744073709551616 326657988797450466707709 

noncomputable def Ns60p2875 := @Ns60p2874 Ns60p62 188700347 1342177280 1421 1342177280 (Ns60p2868 (RS061to078.d34 qz242 qz253 qz305) RS061to078.d65) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2876 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz304 (@BSN.thirtyTwoPi_le_dec qz242 283692 1000 qz245 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz1144 qz1145 (Ns60p2867 rfl rfl) (Ns60p2869 rfl rfl)) (Ns60p2870 qz10 qz245 rfl rfl rfl rfl (Ns60p2872 rfl)) (Ns60p2873 qz10 qz256 rfl rfl rfl rfl (Ns60p2875 rfl)) 

noncomputable abbrev qz910 := (@Enclosure.dec_le_dec qz1095 qz1104 285752 1000 287396 1000 (@Eq.refl Real qz1095) (@Eq.refl Real qz1104) rfl rfl rfl)

noncomputable abbrev qz619 := qz910

noncomputable abbrev qz306 := (RS061to078.d3 qz588 qz600 qz619)

noncomputable abbrev qz1146 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz306)

noncomputable def Ns60p2877 := @Enclosure.Real.IsNear.of_eq qz1146 (hardyZApproximantRS₀ qz253) Bool.false 36522145614582757673 18446744073709551616 326657988797450466707709 Ns60p62 

noncomputable abbrev qz307 := qz619

noncomputable def Ns60p2878 := @Enclosure.Real.IsNear.pos_val qz1146 36522145614582757673 18446744073709551616 326657988797450466707709 Ns60p62 (Ns60p2877 (RS061to078.d4 qz253 qz264 qz307) RS061to078.d65) rfl 

noncomputable abbrev qz1147 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz306)

noncomputable def Ns60p2879 := @Enclosure.Real.IsNear.of_eq qz1147 (hardyZApproximantRS₀ qz264) Bool.true 158074738888800874987 147573952589676412928 285860000584219116140157 Ns60p62 

noncomputable def Ns60p2880 := @Enclosure.Real.IsNear.neg_val qz1147 158074738888800874987 147573952589676412928 285860000584219116140157 Ns60p62 (Ns60p2879 (RS061to078.d34 qz253 qz264 qz307) RS061to078.d66) rfl 

noncomputable def Ns60p2881 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1146 qz4 qz253 257388 1000 285752 1000 

noncomputable def Ns60p2882 := @Enclosure.norm_gt_of_isNear qz1146 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 36522145614582757673 18446744073709551616 326657988797450466707709 

noncomputable def Ns60p2883 := @Ns60p2882 Ns60p62 188700347 1342177280 1421 1342177280 (Ns60p2877 (RS061to078.d4 qz253 qz264 qz307) RS061to078.d65) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2884 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz1147 qz4 qz264 257388 1000 287396 1000 

noncomputable def Ns60p2885 := @Enclosure.norm_gt_of_isNear qz1147 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 158074738888800874987 147573952589676412928 285860000584219116140157 

noncomputable def Ns60p2886 := @Ns60p2885 Ns60p62 188700347 1342177280 1421 1342177280 (Ns60p2879 (RS061to078.d34 qz253 qz264 qz307) RS061to078.d66) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 188700347 1342177280 1421 1342177280 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS061to078.d36) rfl rfl rfl rfl 

noncomputable def Ns60p2887 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz306 (@BSN.thirtyTwoPi_le_dec qz253 285752 1000 qz256 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz1146 qz1147 (Ns60p2878 rfl rfl) (Ns60p2880 rfl rfl)) (Ns60p2881 qz10 qz256 rfl rfl rfl rfl (Ns60p2883 rfl)) (Ns60p2884 qz10 (@Eq.refl Real qz264) rfl rfl rfl rfl (Ns60p2886 rfl)) 

noncomputable def Ns60p2888 := @List.cons RS061to078.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz304 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz304) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz304) Ns60p2876)) (@List.cons RS061to078.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz306 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz306) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz306) Ns60p2887)) (@List.nil RS061to078.d0)) 

noncomputable def Ns60p2889 := @List.cons RS061to078.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns60p2854)) (@List.cons RS061to078.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz302 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz302) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz302) Ns60p2865)) Ns60p2888) 

noncomputable def Ns60p2890 := @List.cons RS061to078.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns60p2832)) (@List.cons RS061to078.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz298 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz298) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz298) Ns60p2843)) Ns60p2889) 

noncomputable def Ns60p2891 := @List.cons RS061to078.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns60p2810)) (@List.cons RS061to078.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz294 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz294) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz294) Ns60p2821)) Ns60p2890) 

noncomputable def Ns60p2892 := @List.cons RS061to078.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns60p2788)) (@List.cons RS061to078.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz290 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz290) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz290) Ns60p2799)) Ns60p2891) 

noncomputable def Ns60p2893 := @List.cons RS061to078.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns60p2766)) (@List.cons RS061to078.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz286 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz286) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz286) Ns60p2777)) Ns60p2892) 

noncomputable def Ns60p2894 := @List.cons RS061to078.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz280 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz280) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz280) Ns60p2744)) (@List.cons RS061to078.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz282 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz282) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz282) Ns60p2755)) Ns60p2893) 

noncomputable def Ns60p2895 := @List.cons RS061to078.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz276 (@Or.inl (Zeta.Certificates.ZIntervalRS.Certificate qz276) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz276) Ns60p2722)) (@List.cons RS061to078.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz278 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz278) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz278) Ns60p2733)) Ns60p2894) 

noncomputable def Ns60p2896 := @List.cons RS061to078.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz272 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz272) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz272) Ns60p2700)) (@List.cons RS061to078.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz274 (@Or.inl (Zeta.Certificates.ZIntervalRS.Certificate qz274) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz274) Ns60p2711)) Ns60p2895) 

noncomputable abbrev qz620 := (@List.cons RS061to078.d1 (RS061to078.d2 qz861 qz871 (@Enclosure.dec_le_dec qz861 qz871 282868 1000 283692 1000 (@Eq.refl Real qz861) qz908 rfl rfl rfl)) (@List.cons RS061to078.d1 (RS061to078.d2 qz871 qz881 qz909) (@List.cons RS061to078.d1 (RS061to078.d2 qz881 qz891 qz910) (@List.nil RS061to078.d1))))

noncomputable abbrev qz308 := (@List.cons RS061to078.d1 (RS061to078.d2 qz540 qz552 qz907) (@List.cons RS061to078.d1 (RS061to078.d2 qz552 qz564 qz616) qz620))

noncomputable def Ns60p2897 := @List.cons RS061to078.d1 (RS061to078.d2 qz190 qz201 qz295) (@List.cons RS061to078.d1 (RS061to078.d2 qz201 qz211 qz297) qz308) 

noncomputable abbrev qz621 := (@List.cons RS061to078.d1 (RS061to078.d2 qz791 qz801 (@Enclosure.dec_le_dec qz791 qz801 270834 1000 272502 1000 (@Eq.refl Real qz791) qz904 rfl rfl rfl)) (@List.cons RS061to078.d1 (RS061to078.d2 qz801 qz811 qz905) (@List.cons RS061to078.d1 (RS061to078.d2 qz811 qz821 qz906) Ns60p2897)))

noncomputable abbrev qz309 := (@List.cons RS061to078.d1 (RS061to078.d2 qz456 qz468 qz903) (@List.cons RS061to078.d1 (RS061to078.d2 qz468 qz480 qz612) qz621))

noncomputable def Ns60p2898 := @List.cons RS061to078.d1 (RS061to078.d2 qz117 qz127 qz281) (@List.cons RS061to078.d1 (RS061to078.d2 qz127 qz137 qz283) qz309) 

noncomputable def Ns60p2899 := @List.IsChain.cons_cons RS061to078.d1 RS061to078.d67 (RS061to078.d2 qz89 qz117 qz279) (RS061to078.d2 qz117 qz127 qz281) (@List.cons RS061to078.d1 (RS061to078.d2 qz127 qz137 qz283) qz309) 

noncomputable def Ns60p2900 := @List.IsChain.cons_cons RS061to078.d1 RS061to078.d67 (RS061to078.d2 qz117 qz127 qz281) (RS061to078.d2 qz127 qz137 qz283) qz309 (@Enclosure.dec_le_dec qz127 qz127 265813 1000 265813 1000 (@Eq.refl Real qz127) (@Eq.refl Real qz127) rfl rfl rfl) 

noncomputable def Ns60p2901 := @List.IsChain.cons_cons RS061to078.d1 RS061to078.d67 (RS061to078.d2 qz179 qz190 qz293) (RS061to078.d2 qz190 qz201 qz295) (@List.cons RS061to078.d1 (RS061to078.d2 qz201 qz211 qz297) qz308) 

noncomputable def Ns60p2902 := @List.IsChain.cons_cons RS061to078.d1 RS061to078.d67 (RS061to078.d2 qz190 qz201 qz295) (RS061to078.d2 qz201 qz211 qz297) qz308 (@Enclosure.dec_le_dec qz201 qz201 277490 1000 277490 1000 (@Eq.refl Real qz201) (@Eq.refl Real qz201) rfl rfl rfl) 

noncomputable abbrev qz310 := qz620

noncomputable abbrev qz622 := (@List.cons RS061to078.d1 (RS061to078.d2 qz871 qz881 qz909) (@List.cons RS061to078.d1 (RS061to078.d2 qz881 qz891 qz910) (@List.nil RS061to078.d1)))

noncomputable abbrev qz311 := qz622

noncomputable def Ns60p2903 := @List.IsChain.cons_cons RS061to078.d1 RS061to078.d67 (RS061to078.d2 qz211 qz221 qz299) (RS061to078.d2 qz221 qz231 qz301) qz310 (@Enclosure.dec_le_dec qz221 qz221 281629 1000 281629 1000 (@Eq.refl Real qz221) (@Eq.refl Real qz221) rfl rfl rfl) (@List.IsChain.cons_cons RS061to078.d1 RS061to078.d67 (RS061to078.d2 qz221 qz231 qz301) (RS061to078.d2 qz231 qz242 qz303) qz311 (@Enclosure.dec_le_dec qz231 qz231 282868 1000 282868 1000 qz234 qz234 rfl rfl rfl) (@List.IsChain.cons_cons RS061to078.d1 RS061to078.d67 (RS061to078.d2 qz231 qz242 qz303) (RS061to078.d2 qz242 qz253 qz305) (@List.cons RS061to078.d1 (RS061to078.d2 qz253 qz264 qz307) (@List.nil RS061to078.d1)) (@Enclosure.dec_le_dec qz242 qz242 283692 1000 283692 1000 qz245 qz245 rfl rfl rfl) (@List.IsChain.cons_cons RS061to078.d1 RS061to078.d67 (RS061to078.d2 qz242 qz253 qz305) (RS061to078.d2 qz253 qz264 qz307) (@List.nil RS061to078.d1) (@Enclosure.dec_le_dec qz253 qz253 285752 1000 285752 1000 qz256 qz256 rfl rfl rfl) (@List.IsChain.singleton RS061to078.d1 RS061to078.d67 (RS061to078.d2 qz253 qz264 qz307))))) 

noncomputable abbrev qz312 := (@List.cons RS061to078.d1 (RS061to078.d2 qz552 qz564 qz616) qz620)

noncomputable def Ns60p2904 := @List.IsChain.cons_cons RS061to078.d1 RS061to078.d67 (RS061to078.d2 qz201 qz211 qz297) (RS061to078.d2 qz211 qz221 qz299) qz312 (@Enclosure.dec_le_dec qz211 qz211 279148 1000 279148 1000 (@Eq.refl Real qz211) (@Eq.refl Real qz211) rfl rfl rfl) Ns60p2903 

noncomputable abbrev qz313 := qz621

noncomputable abbrev qz623 := (@List.cons RS061to078.d1 (RS061to078.d2 qz801 qz811 qz905) (@List.cons RS061to078.d1 (RS061to078.d2 qz811 qz821 qz906) Ns60p2897))

noncomputable abbrev qz314 := qz623

noncomputable def Ns60p2905 := @List.IsChain.cons_cons RS061to078.d1 RS061to078.d67 (RS061to078.d2 qz137 qz147 qz285) (RS061to078.d2 qz147 qz157 qz287) qz313 (@Enclosure.dec_le_dec qz147 qz147 269163 1000 269163 1000 (@Eq.refl Real qz147) (@Eq.refl Real qz147) rfl rfl rfl) (@List.IsChain.cons_cons RS061to078.d1 RS061to078.d67 (RS061to078.d2 qz147 qz157 qz287) (RS061to078.d2 qz157 qz168 qz289) qz314 (@Enclosure.dec_le_dec qz157 qz157 270834 1000 270834 1000 qz160 qz160 rfl rfl rfl) (@List.IsChain.cons_cons RS061to078.d1 RS061to078.d67 (RS061to078.d2 qz157 qz168 qz289) (RS061to078.d2 qz168 qz179 qz291) (@List.cons RS061to078.d1 (RS061to078.d2 qz179 qz190 qz293) Ns60p2897) (@Enclosure.dec_le_dec qz168 qz168 272502 1000 272502 1000 qz171 qz171 rfl rfl rfl) (@List.IsChain.cons_cons RS061to078.d1 RS061to078.d67 (RS061to078.d2 qz168 qz179 qz291) (RS061to078.d2 qz179 qz190 qz293) Ns60p2897 (@Enclosure.dec_le_dec qz179 qz179 274167 1000 274167 1000 qz182 qz182 rfl rfl rfl) (Ns60p2901 (@Enclosure.dec_le_dec qz190 qz190 275830 1000 275830 1000 qz193 qz193 rfl rfl rfl) (Ns60p2902 Ns60p2904))))) 

noncomputable abbrev qz315 := (@List.cons RS061to078.d1 (RS061to078.d2 qz468 qz480 qz612) qz621)

noncomputable def Ns60p2906 := @List.IsChain.cons_cons RS061to078.d1 RS061to078.d67 (RS061to078.d2 qz127 qz137 qz283) (RS061to078.d2 qz137 qz147 qz285) qz315 (@Enclosure.dec_le_dec qz137 qz137 267489 1000 267489 1000 (@Eq.refl Real qz137) (@Eq.refl Real qz137) rfl rfl rfl) Ns60p2905 

noncomputable def Ns60p2907 := Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns60p2896 (@List.IsChain.cons_cons RS061to078.d1 RS061to078.d67 (RS061to078.d2 qz4 qz26 qz273) (RS061to078.d2 qz26 qz61 qz275) (@List.cons RS061to078.d1 (RS061to078.d2 qz61 qz89 qz277) (@List.cons RS061to078.d1 (RS061to078.d2 qz89 qz117 qz279) Ns60p2898)) (@Enclosure.dec_le_dec qz26 qz26 259079 1000 259079 1000 qz29 qz29 rfl rfl rfl) (@List.IsChain.cons_cons RS061to078.d1 RS061to078.d67 (RS061to078.d2 qz26 qz61 qz275) (RS061to078.d2 qz61 qz89 qz277) (@List.cons RS061to078.d1 (RS061to078.d2 qz89 qz117 qz279) Ns60p2898) (@Enclosure.dec_le_dec qz61 qz61 260767 1000 260767 1000 qz66 qz66 rfl rfl rfl) (@List.IsChain.cons_cons RS061to078.d1 RS061to078.d67 (RS061to078.d2 qz61 qz89 qz277) (RS061to078.d2 qz89 qz117 qz279) Ns60p2898 (@Enclosure.dec_le_dec qz89 qz89 262452 1000 262452 1000 qz94 qz94 rfl rfl rfl) (Ns60p2899 (@Enclosure.dec_le_dec qz117 qz117 264134 1000 264134 1000 (@Eq.refl Real qz117) (@Eq.refl Real qz117) rfl rfl rfl) (Ns60p2900 Ns60p2906))))) 

noncomputable abbrev qz911 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz912 := (Zeta.Certificates.CertifiedZeroIntervals.intervals Ns60p2907)

theorem RS061to078.d68 : Zeta.Certificates.BatchSpec 18 257388 1000 287396 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz911 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 18) (And (@Eq (Option Real) (@Option.map qz911 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz911 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz911 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz911 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz264)))) Ns60p2907 (@And.intro (@Eq Nat (@List.length qz911 qz912) 18) (And (@Eq (Option Real) (@Option.map qz911 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz911 qz912)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz911 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz911 qz912)) (@Option.some Real qz264))) (@Eq.refl Nat 18) (@And.intro (@Eq (Option Real) (@Option.map qz911 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz911 qz912)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz911 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz911 qz912)) (@Option.some Real qz264)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz264))))

theorem solution : Zeta.Certificates.BatchSpec 18 257388 1000 287396 1000 := RS061to078.d68
#print axioms solution
#check solution
