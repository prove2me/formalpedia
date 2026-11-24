-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_product_bound_to_286
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-21T16:32:42.659367+00:00
-- url     : https://prove2.me/submissions/3e3cf08a-a694-4316-8f52-d6aee028382f

import Theorems.Thm_TaoFivePrimes_theta_cert_totient_gamma_lower
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace TaoFivePrimes

open Finset

set_option linter.unnecessarySeqFocus false

/-! ### Certificate tables
`bPtab k` is the k-th checkpoint prime, `bLo k` the lower end of its x-interval
(here `bLo k = bPtab k`), `bClo k` = `10^6 · c_k` with `c_k/10^6 < log (bLo k)`,
`bSq k` a strict overestimator of `√(bLo k)`, and `bPnum k`/`bPden k`
numerator/denominator of `∏ p ∈ primesLE (bPtab k), p/(p-1)`. -/

def bPtab : ℕ → ℕ
  | 0 => 2
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | 4 => 11
  | 5 => 13
  | 6 => 17
  | 7 => 19
  | 8 => 23
  | 9 => 29
  | 10 => 31
  | 11 => 37
  | 12 => 41
  | 13 => 43
  | 14 => 47
  | 15 => 53
  | 16 => 59
  | 17 => 61
  | 18 => 67
  | 19 => 71
  | 20 => 73
  | 21 => 79
  | 22 => 83
  | 23 => 89
  | 24 => 97
  | 25 => 101
  | 26 => 103
  | 27 => 107
  | 28 => 109
  | 29 => 113
  | 30 => 127
  | 31 => 131
  | 32 => 137
  | 33 => 139
  | 34 => 149
  | 35 => 151
  | 36 => 157
  | 37 => 163
  | 38 => 167
  | 39 => 173
  | 40 => 179
  | 41 => 181
  | 42 => 191
  | 43 => 193
  | 44 => 197
  | 45 => 199
  | 46 => 211
  | 47 => 223
  | 48 => 227
  | 49 => 229
  | 50 => 233
  | 51 => 239
  | 52 => 241
  | 53 => 251
  | 54 => 257
  | 55 => 263
  | 56 => 269
  | 57 => 271
  | 58 => 277
  | 59 => 281
  | 60 => 283
  | _ => 0

def bLo : ℕ → ℕ
  | 0 => 2
  | 1 => 3
  | 2 => 5
  | 3 => 7
  | 4 => 11
  | 5 => 13
  | 6 => 17
  | 7 => 19
  | 8 => 23
  | 9 => 29
  | 10 => 31
  | 11 => 37
  | 12 => 41
  | 13 => 43
  | 14 => 47
  | 15 => 53
  | 16 => 59
  | 17 => 61
  | 18 => 67
  | 19 => 71
  | 20 => 73
  | 21 => 79
  | 22 => 83
  | 23 => 89
  | 24 => 97
  | 25 => 101
  | 26 => 103
  | 27 => 107
  | 28 => 109
  | 29 => 113
  | 30 => 127
  | 31 => 131
  | 32 => 137
  | 33 => 139
  | 34 => 149
  | 35 => 151
  | 36 => 157
  | 37 => 163
  | 38 => 167
  | 39 => 173
  | 40 => 179
  | 41 => 181
  | 42 => 191
  | 43 => 193
  | 44 => 197
  | 45 => 199
  | 46 => 211
  | 47 => 223
  | 48 => 227
  | 49 => 229
  | 50 => 233
  | 51 => 239
  | 52 => 241
  | 53 => 251
  | 54 => 257
  | 55 => 263
  | 56 => 269
  | 57 => 271
  | 58 => 277
  | 59 => 281
  | 60 => 283
  | _ => 0

def bClo : ℕ → ℕ
  | 0 => 693147
  | 1 => 1098612
  | 2 => 1609437
  | 3 => 1945910
  | 4 => 2397895
  | 5 => 2564949
  | 6 => 2833213
  | 7 => 2944438
  | 8 => 3135494
  | 9 => 3367295
  | 10 => 3433987
  | 11 => 3610917
  | 12 => 3713572
  | 13 => 3761200
  | 14 => 3850147
  | 15 => 3970291
  | 16 => 4077537
  | 17 => 4110873
  | 18 => 4204692
  | 19 => 4262679
  | 20 => 4290459
  | 21 => 4369447
  | 22 => 4418840
  | 23 => 4488636
  | 24 => 4574710
  | 25 => 4615120
  | 26 => 4634728
  | 27 => 4672828
  | 28 => 4691347
  | 29 => 4727387
  | 30 => 4844187
  | 31 => 4875197
  | 32 => 4919980
  | 33 => 4934473
  | 34 => 5003946
  | 35 => 5017279
  | 36 => 5056245
  | 37 => 5093750
  | 38 => 5117993
  | 39 => 5153291
  | 40 => 5187385
  | 41 => 5198497
  | 42 => 5252273
  | 43 => 5262690
  | 44 => 5283203
  | 45 => 5293304
  | 46 => 5351858
  | 47 => 5407171
  | 48 => 5424950
  | 49 => 5433722
  | 50 => 5451038
  | 51 => 5476463
  | 52 => 5484796
  | 53 => 5525452
  | 54 => 5549076
  | 55 => 5572154
  | 56 => 5594711
  | 57 => 5602118
  | 58 => 5624017
  | 59 => 5638354
  | 60 => 5645446
  | _ => 0

def bSq : ℕ → ℕ
  | 0 => 2
  | 1 => 2
  | 2 => 3
  | 3 => 3
  | 4 => 4
  | 5 => 4
  | 6 => 5
  | 7 => 5
  | 8 => 5
  | 9 => 6
  | 10 => 6
  | 11 => 7
  | 12 => 7
  | 13 => 7
  | 14 => 7
  | 15 => 8
  | 16 => 8
  | 17 => 8
  | 18 => 9
  | 19 => 9
  | 20 => 9
  | 21 => 9
  | 22 => 10
  | 23 => 10
  | 24 => 10
  | 25 => 11
  | 26 => 11
  | 27 => 11
  | 28 => 11
  | 29 => 11
  | 30 => 12
  | 31 => 12
  | 32 => 12
  | 33 => 12
  | 34 => 13
  | 35 => 13
  | 36 => 13
  | 37 => 13
  | 38 => 13
  | 39 => 14
  | 40 => 14
  | 41 => 14
  | 42 => 14
  | 43 => 14
  | 44 => 15
  | 45 => 15
  | 46 => 15
  | 47 => 15
  | 48 => 16
  | 49 => 16
  | 50 => 16
  | 51 => 16
  | 52 => 16
  | 53 => 16
  | 54 => 17
  | 55 => 17
  | 56 => 17
  | 57 => 17
  | 58 => 17
  | 59 => 17
  | 60 => 17
  | _ => 0

def bPnum : ℕ → ℕ
  | 0 => 2
  | 1 => 6
  | 2 => 30
  | 3 => 210
  | 4 => 2310
  | 5 => 30030
  | 6 => 510510
  | 7 => 9699690
  | 8 => 223092870
  | 9 => 6469693230
  | 10 => 200560490130
  | 11 => 7420738134810
  | 12 => 304250263527210
  | 13 => 13082761331670030
  | 14 => 614889782588491410
  | 15 => 32589158477190044730
  | 16 => 1922760350154212639070
  | 17 => 117288381359406970983270
  | 18 => 7858321551080267055879090
  | 19 => 557940830126698960967415390
  | 20 => 40729680599249024150621323470
  | 21 => 3217644767340672907899084554130
  | 22 => 267064515689275851355624017992790
  | 23 => 23768741896345550770650537601358310
  | 24 => 2305567963945518424753102147331756070
  | 25 => 232862364358497360900063316880507363070
  | 26 => 23984823528925228172706521638692258396210
  | 27 => 2566376117594999414479597815340071648394470
  | 28 => 279734996817854936178276161872067809674997230
  | 29 => 31610054640417607788145206291543662493274686990
  | 30 => 4014476939333036189094441199026045136645885247730
  | 31 => 525896479052627740771371797072411912900610967452630
  | 32 => 72047817630210000485677936198920432067383702541010310
  | 33 => 10014646650599190067509233131649940057366334653200433090
  | 34 => 1492182350939279320058875736615841068547583863326864530410
  | 35 => 225319534991831177328890236228992001350685163362356544091910
  | 36 => 35375166993717494840635767087951744212057570647889977422429870
  | 37 => 5766152219975951659023630035336134306565384015606066319856068810
  | 38 => 962947420735983927056946215901134429196419130606213075415963491270
  | 39 => 166589903787325219380851695350896256250980509594874862046961683989710
  | 40 => 29819592777931214269172453467810429868925511217482600306406141434158090
  | 41 => 5397346292805549782720214077673687806275517530364350655459511599582614290
  | 42 => 1030893141925860008499560888835674370998623848299590975192766715520279329390
  | 43 => 198962376391690981640415251545285153602734402721821058212203976095413910572270
  | 44 => 39195588149163123383161804554421175259738677336198748467804183290796540382737190
  | 45 => 7799922041683461553249199106329813876687996789903550945093032474868511536164700810
  | 46 => 1645783550795210387735581011435590727981167322669649249414629852197255934130751870910
  | 47 => 367009731827331916465034565550136732339800312955331782619462457039988073311157667212930
  | 48 => 83311209124804345037562846379881038241134671040860314654617977748077292641632790457335110
  | 49 => 19078266889580195013601891820992757757219839668357012055907516904309700014933909014729740190
  | 50 => 4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270
  | 51 => 1062411448280052319722448549835623701226301211611796930357321893850294264731624591303255041960530
  | 52 => 256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730
  | 53 => 64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230
  | 54 => 16516447045902521732188973253623425320896207954043566485360902980990824644545340710198976591011245999110
  | 55 => 4343825573072363215565699965702960859395702691913457985649917484000586881515424606782330843435957697765930
  | 56 => 1168489079156465704987173290774096471177444024124720198139827803196157871127649219224446996884272620699035170
  | 57 => 316660540451402206051523961799780143689087330537799173695893334666158783075592938409825136155637880209438531070
  | 58 => 87714969705038411076272137418539099801877190558970371113762453702525982911939243939521562715111692818014473106390
  | 59 => 24647906487115793512432470614609487044327490547070674282967249490409801198254927547005559122946385681862066942895590
  | 60 => 6975357535853769564018389183934484833544679824821000822079731605785973739106144495802573231793827147966964944839451970
  | _ => 1

def bPden : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 8
  | 3 => 48
  | 4 => 480
  | 5 => 5760
  | 6 => 92160
  | 7 => 1658880
  | 8 => 36495360
  | 9 => 1021870080
  | 10 => 30656102400
  | 11 => 1103619686400
  | 12 => 44144787456000
  | 13 => 1854081073152000
  | 14 => 85287729364992000
  | 15 => 4434961926979584000
  | 16 => 257227791764815872000
  | 17 => 15433667505888952320000
  | 18 => 1018622055388670853120000
  | 19 => 71303543877206959718400000
  | 20 => 5133855159158901099724800000
  | 21 => 400440702414394285778534400000
  | 22 => 32836137597980331433839820800000
  | 23 => 2889580108622269166177904230400000
  | 24 => 277399690427737839953078806118400000
  | 25 => 27739969042773783995307880611840000000
  | 26 => 2829476842362925967521403822407680000000
  | 27 => 299924545290470152557268805175214080000000
  | 28 => 32391850891370776476185030958923120640000000
  | 29 => 3627887299833526965332723467399389511680000000
  | 30 => 457113799779024397631923156892323078471680000000
  | 31 => 59424793971273171692150010396002000201318400000000
  | 32 => 8081771980093151350132401413856272027379302400000000
  | 33 => 1115284533252854886318271395112165539778343731200000000
  | 34 => 165062110921422523175104166476600499887194872217600000000
  | 35 => 24759316638213378476265624971490074983079230832640000000000
  | 36 => 3862453395561287042297437495552451697360360009891840000000000
  | 37 => 625717450080928500852184874279497174972378321602478080000000000
  | 38 => 103869096713434131141462689130396531045414801386011361280000000000
  | 39 => 17865484634710670556331582530428203339811345838393954140160000000000
  | 40 => 3180056264978499359027021690416220194486419559234123836948480000000000
  | 41 => 572410127696129884624863904274919635007555520662142290650726400000000000
  | 42 => 108757924262264678078724141812234730651435548925807035223638016000000000000
  | 43 => 20881521458354818191115035227949068285075625393754950762938499072000000000000
  | 44 => 4092778205837544365458546904678017383874822577175970349535945818112000000000000
  | 45 => 810370084755833784360792287126247442007214870280842129208117271986176000000000000
  | 46 => 170177717798725094715766380296511962821515122758976847133704627117096960000000000000
  | 47 => 37779453351316971026900136425825655746376357252492860063682427219995525120000000000000
  | 48 => 8538156457397635452079430832236598198681056739063386374392228551718988677120000000000000
  | 49 => 1946699672286660883074110229749944389299280936506452093361428109791929418383360000000000000
  | 50 => 451634323970505324873193573301987098317433177269496885659851321471727625064939520000000000000
  | 51 => 107488969104980267319820070445872929399549096190140258787044614510271174765455605760000000000000
  | 52 => 25797352585195264156756816907009503055891783085633662108890707482465081943709345382400000000000000
  | 53 => 6449338146298816039189204226752375763972945771408415527222676870616270485927336345600000000000000000
  | 54 => 1651030565452496906032436282048608195577074117480554374969005278877765244397398104473600000000000000000
  | 55 => 432570008148554189380498305896735347241193418779905246241879383065974494032118303372083200000000000000000
  | 56 => 115928762183812522753973545980325073060639836233014605992823674661681164400607705303718297600000000000000000
  | 57 => 31300765789629381143572857414687769726372755782913943618062392158653914388164080432003940352000000000000000000
  | 58 => 8639011357937709195626108646453824444478880596084248438585220235788480371133286199233087537152000000000000000000
  | 59 => 2418923180222558574775310421007070844454086566903589562803861666020774503917320135785264510402560000000000000000000
  | 60 => 682136336822761518086637538723993978136052411866812256710688989817858410104684278291444591933521920000000000000000000
  | _ => 1

lemma b_no_prime_284 (m : ℕ) (h1 : 284 ≤ m) (h2 : m ≤ 285) : ¬ m.Prime := by
  interval_cases m <;> decide

/-! ### Light table facts -/
lemma b_lo_pos (k : ℕ) (hk : k < 61) : 1 ≤ bLo k := by
  interval_cases k <;> decide

lemma b_sqlo_all (k : ℕ) (hk : k < 61) : bLo k < bSq k * bSq k := by
  interval_cases k <;> decide

lemma b_sq_pos (k : ℕ) (hk : k < 61) : 0 < bSq k := by
  interval_cases k <;> decide

lemma b_pden_pos (k : ℕ) (hk : k < 61) : 0 < bPden k := by
  interval_cases k <;> decide

/-! ### Telescoping the prime products -/
theorem primesLE_insert_next (q q' : ℕ) (h1 : q < q') (h2 : q'.Prime)
    (h3 : ∀ m, q < m → m < q' → ¬ m.Prime) :
    Nat.primesLE q' = insert q' (Nat.primesLE q) := by
  ext m
  rw [Finset.mem_insert, Nat.mem_primesLE, Nat.mem_primesLE]
  constructor
  · rintro ⟨hle, hmp⟩
    rcases lt_or_eq_of_le hle with h | h
    · rcases lt_trichotomy m q with h' | h' | h'
      · exact Or.inr ⟨le_of_lt h', hmp⟩
      · exact Or.inr ⟨le_of_eq h', hmp⟩
      · exact absurd hmp (h3 m h' h)
    · exact Or.inl h
  · rintro (rfl | ⟨hle, hmp⟩)
    · exact ⟨le_refl _, h2⟩
    · exact ⟨le_trans hle (le_of_lt h1), hmp⟩

theorem b_pnum_step_gen {b : ℕ} (s : Finset ℕ) (a : ℕ) (hmem : a ∉ s)
    (hbase : ∏ p ∈ s, (p : ℕ) = b) :
    ∏ p ∈ insert a s, (p : ℕ) = a * b := by
  rw [Finset.prod_insert hmem, hbase]

theorem b_pden_step_gen {b : ℕ} (s : Finset ℕ) (a : ℕ) (hmem : a ∉ s)
    (hbase : ∏ p ∈ s, ((p : ℕ) - 1) = b) :
    ∏ p ∈ insert a s, ((p : ℕ) - 1) = (a - 1) * b := by
  rw [Finset.prod_insert hmem, hbase]

theorem b_pnum_0 : ∏ p ∈ Nat.primesLE 2, (p : ℕ) = bPnum 0 := by decide
theorem b_pden_0 : ∏ p ∈ Nat.primesLE 2, ((p : ℕ) - 1) = bPden 0 := by decide

theorem b_step_1 : Nat.primesLE 3 = insert 3 (Nat.primesLE 2) :=
  primesLE_insert_next 2 3 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_1 : ∏ p ∈ Nat.primesLE 3, (p : ℕ) = bPnum 1 := by
  rw [b_step_1]
  exact b_pnum_step_gen (Nat.primesLE 2) 3
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_0
theorem b_pden_1 : ∏ p ∈ Nat.primesLE 3, ((p : ℕ) - 1) = bPden 1 := by
  rw [b_step_1]
  exact b_pden_step_gen (Nat.primesLE 2) 3
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_0

theorem b_step_2 : Nat.primesLE 5 = insert 5 (Nat.primesLE 3) :=
  primesLE_insert_next 3 5 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_2 : ∏ p ∈ Nat.primesLE 5, (p : ℕ) = bPnum 2 := by
  rw [b_step_2]
  exact b_pnum_step_gen (Nat.primesLE 3) 5
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_1
theorem b_pden_2 : ∏ p ∈ Nat.primesLE 5, ((p : ℕ) - 1) = bPden 2 := by
  rw [b_step_2]
  exact b_pden_step_gen (Nat.primesLE 3) 5
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_1

theorem b_step_3 : Nat.primesLE 7 = insert 7 (Nat.primesLE 5) :=
  primesLE_insert_next 5 7 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_3 : ∏ p ∈ Nat.primesLE 7, (p : ℕ) = bPnum 3 := by
  rw [b_step_3]
  exact b_pnum_step_gen (Nat.primesLE 5) 7
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_2
theorem b_pden_3 : ∏ p ∈ Nat.primesLE 7, ((p : ℕ) - 1) = bPden 3 := by
  rw [b_step_3]
  exact b_pden_step_gen (Nat.primesLE 5) 7
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_2

theorem b_step_4 : Nat.primesLE 11 = insert 11 (Nat.primesLE 7) :=
  primesLE_insert_next 7 11 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_4 : ∏ p ∈ Nat.primesLE 11, (p : ℕ) = bPnum 4 := by
  rw [b_step_4]
  exact b_pnum_step_gen (Nat.primesLE 7) 11
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_3
theorem b_pden_4 : ∏ p ∈ Nat.primesLE 11, ((p : ℕ) - 1) = bPden 4 := by
  rw [b_step_4]
  exact b_pden_step_gen (Nat.primesLE 7) 11
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_3

theorem b_step_5 : Nat.primesLE 13 = insert 13 (Nat.primesLE 11) :=
  primesLE_insert_next 11 13 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_5 : ∏ p ∈ Nat.primesLE 13, (p : ℕ) = bPnum 5 := by
  rw [b_step_5]
  exact b_pnum_step_gen (Nat.primesLE 11) 13
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_4
theorem b_pden_5 : ∏ p ∈ Nat.primesLE 13, ((p : ℕ) - 1) = bPden 5 := by
  rw [b_step_5]
  exact b_pden_step_gen (Nat.primesLE 11) 13
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_4

theorem b_step_6 : Nat.primesLE 17 = insert 17 (Nat.primesLE 13) :=
  primesLE_insert_next 13 17 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_6 : ∏ p ∈ Nat.primesLE 17, (p : ℕ) = bPnum 6 := by
  rw [b_step_6]
  exact b_pnum_step_gen (Nat.primesLE 13) 17
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_5
theorem b_pden_6 : ∏ p ∈ Nat.primesLE 17, ((p : ℕ) - 1) = bPden 6 := by
  rw [b_step_6]
  exact b_pden_step_gen (Nat.primesLE 13) 17
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_5

theorem b_step_7 : Nat.primesLE 19 = insert 19 (Nat.primesLE 17) :=
  primesLE_insert_next 17 19 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_7 : ∏ p ∈ Nat.primesLE 19, (p : ℕ) = bPnum 7 := by
  rw [b_step_7]
  exact b_pnum_step_gen (Nat.primesLE 17) 19
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_6
theorem b_pden_7 : ∏ p ∈ Nat.primesLE 19, ((p : ℕ) - 1) = bPden 7 := by
  rw [b_step_7]
  exact b_pden_step_gen (Nat.primesLE 17) 19
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_6

theorem b_step_8 : Nat.primesLE 23 = insert 23 (Nat.primesLE 19) :=
  primesLE_insert_next 19 23 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_8 : ∏ p ∈ Nat.primesLE 23, (p : ℕ) = bPnum 8 := by
  rw [b_step_8]
  exact b_pnum_step_gen (Nat.primesLE 19) 23
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_7
theorem b_pden_8 : ∏ p ∈ Nat.primesLE 23, ((p : ℕ) - 1) = bPden 8 := by
  rw [b_step_8]
  exact b_pden_step_gen (Nat.primesLE 19) 23
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_7

theorem b_step_9 : Nat.primesLE 29 = insert 29 (Nat.primesLE 23) :=
  primesLE_insert_next 23 29 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_9 : ∏ p ∈ Nat.primesLE 29, (p : ℕ) = bPnum 9 := by
  rw [b_step_9]
  exact b_pnum_step_gen (Nat.primesLE 23) 29
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_8
theorem b_pden_9 : ∏ p ∈ Nat.primesLE 29, ((p : ℕ) - 1) = bPden 9 := by
  rw [b_step_9]
  exact b_pden_step_gen (Nat.primesLE 23) 29
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_8

theorem b_step_10 : Nat.primesLE 31 = insert 31 (Nat.primesLE 29) :=
  primesLE_insert_next 29 31 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_10 : ∏ p ∈ Nat.primesLE 31, (p : ℕ) = bPnum 10 := by
  rw [b_step_10]
  exact b_pnum_step_gen (Nat.primesLE 29) 31
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_9
theorem b_pden_10 : ∏ p ∈ Nat.primesLE 31, ((p : ℕ) - 1) = bPden 10 := by
  rw [b_step_10]
  exact b_pden_step_gen (Nat.primesLE 29) 31
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_9

theorem b_step_11 : Nat.primesLE 37 = insert 37 (Nat.primesLE 31) :=
  primesLE_insert_next 31 37 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_11 : ∏ p ∈ Nat.primesLE 37, (p : ℕ) = bPnum 11 := by
  rw [b_step_11]
  exact b_pnum_step_gen (Nat.primesLE 31) 37
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_10
theorem b_pden_11 : ∏ p ∈ Nat.primesLE 37, ((p : ℕ) - 1) = bPden 11 := by
  rw [b_step_11]
  exact b_pden_step_gen (Nat.primesLE 31) 37
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_10

theorem b_step_12 : Nat.primesLE 41 = insert 41 (Nat.primesLE 37) :=
  primesLE_insert_next 37 41 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_12 : ∏ p ∈ Nat.primesLE 41, (p : ℕ) = bPnum 12 := by
  rw [b_step_12]
  exact b_pnum_step_gen (Nat.primesLE 37) 41
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_11
theorem b_pden_12 : ∏ p ∈ Nat.primesLE 41, ((p : ℕ) - 1) = bPden 12 := by
  rw [b_step_12]
  exact b_pden_step_gen (Nat.primesLE 37) 41
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_11

theorem b_step_13 : Nat.primesLE 43 = insert 43 (Nat.primesLE 41) :=
  primesLE_insert_next 41 43 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_13 : ∏ p ∈ Nat.primesLE 43, (p : ℕ) = bPnum 13 := by
  rw [b_step_13]
  exact b_pnum_step_gen (Nat.primesLE 41) 43
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_12
theorem b_pden_13 : ∏ p ∈ Nat.primesLE 43, ((p : ℕ) - 1) = bPden 13 := by
  rw [b_step_13]
  exact b_pden_step_gen (Nat.primesLE 41) 43
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_12

theorem b_step_14 : Nat.primesLE 47 = insert 47 (Nat.primesLE 43) :=
  primesLE_insert_next 43 47 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_14 : ∏ p ∈ Nat.primesLE 47, (p : ℕ) = bPnum 14 := by
  rw [b_step_14]
  exact b_pnum_step_gen (Nat.primesLE 43) 47
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_13
theorem b_pden_14 : ∏ p ∈ Nat.primesLE 47, ((p : ℕ) - 1) = bPden 14 := by
  rw [b_step_14]
  exact b_pden_step_gen (Nat.primesLE 43) 47
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_13

theorem b_step_15 : Nat.primesLE 53 = insert 53 (Nat.primesLE 47) :=
  primesLE_insert_next 47 53 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_15 : ∏ p ∈ Nat.primesLE 53, (p : ℕ) = bPnum 15 := by
  rw [b_step_15]
  exact b_pnum_step_gen (Nat.primesLE 47) 53
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_14
theorem b_pden_15 : ∏ p ∈ Nat.primesLE 53, ((p : ℕ) - 1) = bPden 15 := by
  rw [b_step_15]
  exact b_pden_step_gen (Nat.primesLE 47) 53
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_14

theorem b_step_16 : Nat.primesLE 59 = insert 59 (Nat.primesLE 53) :=
  primesLE_insert_next 53 59 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_16 : ∏ p ∈ Nat.primesLE 59, (p : ℕ) = bPnum 16 := by
  rw [b_step_16]
  exact b_pnum_step_gen (Nat.primesLE 53) 59
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_15
theorem b_pden_16 : ∏ p ∈ Nat.primesLE 59, ((p : ℕ) - 1) = bPden 16 := by
  rw [b_step_16]
  exact b_pden_step_gen (Nat.primesLE 53) 59
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_15

theorem b_step_17 : Nat.primesLE 61 = insert 61 (Nat.primesLE 59) :=
  primesLE_insert_next 59 61 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_17 : ∏ p ∈ Nat.primesLE 61, (p : ℕ) = bPnum 17 := by
  rw [b_step_17]
  exact b_pnum_step_gen (Nat.primesLE 59) 61
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_16
theorem b_pden_17 : ∏ p ∈ Nat.primesLE 61, ((p : ℕ) - 1) = bPden 17 := by
  rw [b_step_17]
  exact b_pden_step_gen (Nat.primesLE 59) 61
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_16

theorem b_step_18 : Nat.primesLE 67 = insert 67 (Nat.primesLE 61) :=
  primesLE_insert_next 61 67 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_18 : ∏ p ∈ Nat.primesLE 67, (p : ℕ) = bPnum 18 := by
  rw [b_step_18]
  exact b_pnum_step_gen (Nat.primesLE 61) 67
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_17
theorem b_pden_18 : ∏ p ∈ Nat.primesLE 67, ((p : ℕ) - 1) = bPden 18 := by
  rw [b_step_18]
  exact b_pden_step_gen (Nat.primesLE 61) 67
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_17

theorem b_step_19 : Nat.primesLE 71 = insert 71 (Nat.primesLE 67) :=
  primesLE_insert_next 67 71 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_19 : ∏ p ∈ Nat.primesLE 71, (p : ℕ) = bPnum 19 := by
  rw [b_step_19]
  exact b_pnum_step_gen (Nat.primesLE 67) 71
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_18
theorem b_pden_19 : ∏ p ∈ Nat.primesLE 71, ((p : ℕ) - 1) = bPden 19 := by
  rw [b_step_19]
  exact b_pden_step_gen (Nat.primesLE 67) 71
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_18

theorem b_step_20 : Nat.primesLE 73 = insert 73 (Nat.primesLE 71) :=
  primesLE_insert_next 71 73 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_20 : ∏ p ∈ Nat.primesLE 73, (p : ℕ) = bPnum 20 := by
  rw [b_step_20]
  exact b_pnum_step_gen (Nat.primesLE 71) 73
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_19
theorem b_pden_20 : ∏ p ∈ Nat.primesLE 73, ((p : ℕ) - 1) = bPden 20 := by
  rw [b_step_20]
  exact b_pden_step_gen (Nat.primesLE 71) 73
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_19

theorem b_step_21 : Nat.primesLE 79 = insert 79 (Nat.primesLE 73) :=
  primesLE_insert_next 73 79 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_21 : ∏ p ∈ Nat.primesLE 79, (p : ℕ) = bPnum 21 := by
  rw [b_step_21]
  exact b_pnum_step_gen (Nat.primesLE 73) 79
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_20
theorem b_pden_21 : ∏ p ∈ Nat.primesLE 79, ((p : ℕ) - 1) = bPden 21 := by
  rw [b_step_21]
  exact b_pden_step_gen (Nat.primesLE 73) 79
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_20

theorem b_step_22 : Nat.primesLE 83 = insert 83 (Nat.primesLE 79) :=
  primesLE_insert_next 79 83 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_22 : ∏ p ∈ Nat.primesLE 83, (p : ℕ) = bPnum 22 := by
  rw [b_step_22]
  exact b_pnum_step_gen (Nat.primesLE 79) 83
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_21
theorem b_pden_22 : ∏ p ∈ Nat.primesLE 83, ((p : ℕ) - 1) = bPden 22 := by
  rw [b_step_22]
  exact b_pden_step_gen (Nat.primesLE 79) 83
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_21

theorem b_step_23 : Nat.primesLE 89 = insert 89 (Nat.primesLE 83) :=
  primesLE_insert_next 83 89 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_23 : ∏ p ∈ Nat.primesLE 89, (p : ℕ) = bPnum 23 := by
  rw [b_step_23]
  exact b_pnum_step_gen (Nat.primesLE 83) 89
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_22
theorem b_pden_23 : ∏ p ∈ Nat.primesLE 89, ((p : ℕ) - 1) = bPden 23 := by
  rw [b_step_23]
  exact b_pden_step_gen (Nat.primesLE 83) 89
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_22

theorem b_step_24 : Nat.primesLE 97 = insert 97 (Nat.primesLE 89) :=
  primesLE_insert_next 89 97 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_24 : ∏ p ∈ Nat.primesLE 97, (p : ℕ) = bPnum 24 := by
  rw [b_step_24]
  exact b_pnum_step_gen (Nat.primesLE 89) 97
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_23
theorem b_pden_24 : ∏ p ∈ Nat.primesLE 97, ((p : ℕ) - 1) = bPden 24 := by
  rw [b_step_24]
  exact b_pden_step_gen (Nat.primesLE 89) 97
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_23

theorem b_step_25 : Nat.primesLE 101 = insert 101 (Nat.primesLE 97) :=
  primesLE_insert_next 97 101 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_25 : ∏ p ∈ Nat.primesLE 101, (p : ℕ) = bPnum 25 := by
  rw [b_step_25]
  exact b_pnum_step_gen (Nat.primesLE 97) 101
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_24
theorem b_pden_25 : ∏ p ∈ Nat.primesLE 101, ((p : ℕ) - 1) = bPden 25 := by
  rw [b_step_25]
  exact b_pden_step_gen (Nat.primesLE 97) 101
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_24

theorem b_step_26 : Nat.primesLE 103 = insert 103 (Nat.primesLE 101) :=
  primesLE_insert_next 101 103 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_26 : ∏ p ∈ Nat.primesLE 103, (p : ℕ) = bPnum 26 := by
  rw [b_step_26]
  exact b_pnum_step_gen (Nat.primesLE 101) 103
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_25
theorem b_pden_26 : ∏ p ∈ Nat.primesLE 103, ((p : ℕ) - 1) = bPden 26 := by
  rw [b_step_26]
  exact b_pden_step_gen (Nat.primesLE 101) 103
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_25

theorem b_step_27 : Nat.primesLE 107 = insert 107 (Nat.primesLE 103) :=
  primesLE_insert_next 103 107 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_27 : ∏ p ∈ Nat.primesLE 107, (p : ℕ) = bPnum 27 := by
  rw [b_step_27]
  exact b_pnum_step_gen (Nat.primesLE 103) 107
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_26
theorem b_pden_27 : ∏ p ∈ Nat.primesLE 107, ((p : ℕ) - 1) = bPden 27 := by
  rw [b_step_27]
  exact b_pden_step_gen (Nat.primesLE 103) 107
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_26

theorem b_step_28 : Nat.primesLE 109 = insert 109 (Nat.primesLE 107) :=
  primesLE_insert_next 107 109 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_28 : ∏ p ∈ Nat.primesLE 109, (p : ℕ) = bPnum 28 := by
  rw [b_step_28]
  exact b_pnum_step_gen (Nat.primesLE 107) 109
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_27
theorem b_pden_28 : ∏ p ∈ Nat.primesLE 109, ((p : ℕ) - 1) = bPden 28 := by
  rw [b_step_28]
  exact b_pden_step_gen (Nat.primesLE 107) 109
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_27

theorem b_step_29 : Nat.primesLE 113 = insert 113 (Nat.primesLE 109) :=
  primesLE_insert_next 109 113 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_29 : ∏ p ∈ Nat.primesLE 113, (p : ℕ) = bPnum 29 := by
  rw [b_step_29]
  exact b_pnum_step_gen (Nat.primesLE 109) 113
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_28
theorem b_pden_29 : ∏ p ∈ Nat.primesLE 113, ((p : ℕ) - 1) = bPden 29 := by
  rw [b_step_29]
  exact b_pden_step_gen (Nat.primesLE 109) 113
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_28

theorem b_step_30 : Nat.primesLE 127 = insert 127 (Nat.primesLE 113) :=
  primesLE_insert_next 113 127 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_30 : ∏ p ∈ Nat.primesLE 127, (p : ℕ) = bPnum 30 := by
  rw [b_step_30]
  exact b_pnum_step_gen (Nat.primesLE 113) 127
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_29
theorem b_pden_30 : ∏ p ∈ Nat.primesLE 127, ((p : ℕ) - 1) = bPden 30 := by
  rw [b_step_30]
  exact b_pden_step_gen (Nat.primesLE 113) 127
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_29

theorem b_step_31 : Nat.primesLE 131 = insert 131 (Nat.primesLE 127) :=
  primesLE_insert_next 127 131 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_31 : ∏ p ∈ Nat.primesLE 131, (p : ℕ) = bPnum 31 := by
  rw [b_step_31]
  exact b_pnum_step_gen (Nat.primesLE 127) 131
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_30
theorem b_pden_31 : ∏ p ∈ Nat.primesLE 131, ((p : ℕ) - 1) = bPden 31 := by
  rw [b_step_31]
  exact b_pden_step_gen (Nat.primesLE 127) 131
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_30

theorem b_step_32 : Nat.primesLE 137 = insert 137 (Nat.primesLE 131) :=
  primesLE_insert_next 131 137 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_32 : ∏ p ∈ Nat.primesLE 137, (p : ℕ) = bPnum 32 := by
  rw [b_step_32]
  exact b_pnum_step_gen (Nat.primesLE 131) 137
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_31
theorem b_pden_32 : ∏ p ∈ Nat.primesLE 137, ((p : ℕ) - 1) = bPden 32 := by
  rw [b_step_32]
  exact b_pden_step_gen (Nat.primesLE 131) 137
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_31

theorem b_step_33 : Nat.primesLE 139 = insert 139 (Nat.primesLE 137) :=
  primesLE_insert_next 137 139 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_33 : ∏ p ∈ Nat.primesLE 139, (p : ℕ) = bPnum 33 := by
  rw [b_step_33]
  exact b_pnum_step_gen (Nat.primesLE 137) 139
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_32
theorem b_pden_33 : ∏ p ∈ Nat.primesLE 139, ((p : ℕ) - 1) = bPden 33 := by
  rw [b_step_33]
  exact b_pden_step_gen (Nat.primesLE 137) 139
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_32

theorem b_step_34 : Nat.primesLE 149 = insert 149 (Nat.primesLE 139) :=
  primesLE_insert_next 139 149 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_34 : ∏ p ∈ Nat.primesLE 149, (p : ℕ) = bPnum 34 := by
  rw [b_step_34]
  exact b_pnum_step_gen (Nat.primesLE 139) 149
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_33
theorem b_pden_34 : ∏ p ∈ Nat.primesLE 149, ((p : ℕ) - 1) = bPden 34 := by
  rw [b_step_34]
  exact b_pden_step_gen (Nat.primesLE 139) 149
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_33

theorem b_step_35 : Nat.primesLE 151 = insert 151 (Nat.primesLE 149) :=
  primesLE_insert_next 149 151 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_35 : ∏ p ∈ Nat.primesLE 151, (p : ℕ) = bPnum 35 := by
  rw [b_step_35]
  exact b_pnum_step_gen (Nat.primesLE 149) 151
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_34
theorem b_pden_35 : ∏ p ∈ Nat.primesLE 151, ((p : ℕ) - 1) = bPden 35 := by
  rw [b_step_35]
  exact b_pden_step_gen (Nat.primesLE 149) 151
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_34

theorem b_step_36 : Nat.primesLE 157 = insert 157 (Nat.primesLE 151) :=
  primesLE_insert_next 151 157 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_36 : ∏ p ∈ Nat.primesLE 157, (p : ℕ) = bPnum 36 := by
  rw [b_step_36]
  exact b_pnum_step_gen (Nat.primesLE 151) 157
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_35
theorem b_pden_36 : ∏ p ∈ Nat.primesLE 157, ((p : ℕ) - 1) = bPden 36 := by
  rw [b_step_36]
  exact b_pden_step_gen (Nat.primesLE 151) 157
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_35

theorem b_step_37 : Nat.primesLE 163 = insert 163 (Nat.primesLE 157) :=
  primesLE_insert_next 157 163 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_37 : ∏ p ∈ Nat.primesLE 163, (p : ℕ) = bPnum 37 := by
  rw [b_step_37]
  exact b_pnum_step_gen (Nat.primesLE 157) 163
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_36
theorem b_pden_37 : ∏ p ∈ Nat.primesLE 163, ((p : ℕ) - 1) = bPden 37 := by
  rw [b_step_37]
  exact b_pden_step_gen (Nat.primesLE 157) 163
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_36

theorem b_step_38 : Nat.primesLE 167 = insert 167 (Nat.primesLE 163) :=
  primesLE_insert_next 163 167 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_38 : ∏ p ∈ Nat.primesLE 167, (p : ℕ) = bPnum 38 := by
  rw [b_step_38]
  exact b_pnum_step_gen (Nat.primesLE 163) 167
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_37
theorem b_pden_38 : ∏ p ∈ Nat.primesLE 167, ((p : ℕ) - 1) = bPden 38 := by
  rw [b_step_38]
  exact b_pden_step_gen (Nat.primesLE 163) 167
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_37

theorem b_step_39 : Nat.primesLE 173 = insert 173 (Nat.primesLE 167) :=
  primesLE_insert_next 167 173 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_39 : ∏ p ∈ Nat.primesLE 173, (p : ℕ) = bPnum 39 := by
  rw [b_step_39]
  exact b_pnum_step_gen (Nat.primesLE 167) 173
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_38
theorem b_pden_39 : ∏ p ∈ Nat.primesLE 173, ((p : ℕ) - 1) = bPden 39 := by
  rw [b_step_39]
  exact b_pden_step_gen (Nat.primesLE 167) 173
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_38

theorem b_step_40 : Nat.primesLE 179 = insert 179 (Nat.primesLE 173) :=
  primesLE_insert_next 173 179 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_40 : ∏ p ∈ Nat.primesLE 179, (p : ℕ) = bPnum 40 := by
  rw [b_step_40]
  exact b_pnum_step_gen (Nat.primesLE 173) 179
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_39
theorem b_pden_40 : ∏ p ∈ Nat.primesLE 179, ((p : ℕ) - 1) = bPden 40 := by
  rw [b_step_40]
  exact b_pden_step_gen (Nat.primesLE 173) 179
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_39

theorem b_step_41 : Nat.primesLE 181 = insert 181 (Nat.primesLE 179) :=
  primesLE_insert_next 179 181 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_41 : ∏ p ∈ Nat.primesLE 181, (p : ℕ) = bPnum 41 := by
  rw [b_step_41]
  exact b_pnum_step_gen (Nat.primesLE 179) 181
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_40
theorem b_pden_41 : ∏ p ∈ Nat.primesLE 181, ((p : ℕ) - 1) = bPden 41 := by
  rw [b_step_41]
  exact b_pden_step_gen (Nat.primesLE 179) 181
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_40

theorem b_step_42 : Nat.primesLE 191 = insert 191 (Nat.primesLE 181) :=
  primesLE_insert_next 181 191 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_42 : ∏ p ∈ Nat.primesLE 191, (p : ℕ) = bPnum 42 := by
  rw [b_step_42]
  exact b_pnum_step_gen (Nat.primesLE 181) 191
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_41
theorem b_pden_42 : ∏ p ∈ Nat.primesLE 191, ((p : ℕ) - 1) = bPden 42 := by
  rw [b_step_42]
  exact b_pden_step_gen (Nat.primesLE 181) 191
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_41

theorem b_step_43 : Nat.primesLE 193 = insert 193 (Nat.primesLE 191) :=
  primesLE_insert_next 191 193 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_43 : ∏ p ∈ Nat.primesLE 193, (p : ℕ) = bPnum 43 := by
  rw [b_step_43]
  exact b_pnum_step_gen (Nat.primesLE 191) 193
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_42
theorem b_pden_43 : ∏ p ∈ Nat.primesLE 193, ((p : ℕ) - 1) = bPden 43 := by
  rw [b_step_43]
  exact b_pden_step_gen (Nat.primesLE 191) 193
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_42

theorem b_step_44 : Nat.primesLE 197 = insert 197 (Nat.primesLE 193) :=
  primesLE_insert_next 193 197 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_44 : ∏ p ∈ Nat.primesLE 197, (p : ℕ) = bPnum 44 := by
  rw [b_step_44]
  exact b_pnum_step_gen (Nat.primesLE 193) 197
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_43
theorem b_pden_44 : ∏ p ∈ Nat.primesLE 197, ((p : ℕ) - 1) = bPden 44 := by
  rw [b_step_44]
  exact b_pden_step_gen (Nat.primesLE 193) 197
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_43

theorem b_step_45 : Nat.primesLE 199 = insert 199 (Nat.primesLE 197) :=
  primesLE_insert_next 197 199 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_45 : ∏ p ∈ Nat.primesLE 199, (p : ℕ) = bPnum 45 := by
  rw [b_step_45]
  exact b_pnum_step_gen (Nat.primesLE 197) 199
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_44
theorem b_pden_45 : ∏ p ∈ Nat.primesLE 199, ((p : ℕ) - 1) = bPden 45 := by
  rw [b_step_45]
  exact b_pden_step_gen (Nat.primesLE 197) 199
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_44

theorem b_step_46 : Nat.primesLE 211 = insert 211 (Nat.primesLE 199) :=
  primesLE_insert_next 199 211 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_46 : ∏ p ∈ Nat.primesLE 211, (p : ℕ) = bPnum 46 := by
  rw [b_step_46]
  exact b_pnum_step_gen (Nat.primesLE 199) 211
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_45
theorem b_pden_46 : ∏ p ∈ Nat.primesLE 211, ((p : ℕ) - 1) = bPden 46 := by
  rw [b_step_46]
  exact b_pden_step_gen (Nat.primesLE 199) 211
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_45

theorem b_step_47 : Nat.primesLE 223 = insert 223 (Nat.primesLE 211) :=
  primesLE_insert_next 211 223 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_47 : ∏ p ∈ Nat.primesLE 223, (p : ℕ) = bPnum 47 := by
  rw [b_step_47]
  exact b_pnum_step_gen (Nat.primesLE 211) 223
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_46
theorem b_pden_47 : ∏ p ∈ Nat.primesLE 223, ((p : ℕ) - 1) = bPden 47 := by
  rw [b_step_47]
  exact b_pden_step_gen (Nat.primesLE 211) 223
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_46

theorem b_step_48 : Nat.primesLE 227 = insert 227 (Nat.primesLE 223) :=
  primesLE_insert_next 223 227 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_48 : ∏ p ∈ Nat.primesLE 227, (p : ℕ) = bPnum 48 := by
  rw [b_step_48]
  exact b_pnum_step_gen (Nat.primesLE 223) 227
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_47
theorem b_pden_48 : ∏ p ∈ Nat.primesLE 227, ((p : ℕ) - 1) = bPden 48 := by
  rw [b_step_48]
  exact b_pden_step_gen (Nat.primesLE 223) 227
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_47

theorem b_step_49 : Nat.primesLE 229 = insert 229 (Nat.primesLE 227) :=
  primesLE_insert_next 227 229 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_49 : ∏ p ∈ Nat.primesLE 229, (p : ℕ) = bPnum 49 := by
  rw [b_step_49]
  exact b_pnum_step_gen (Nat.primesLE 227) 229
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_48
theorem b_pden_49 : ∏ p ∈ Nat.primesLE 229, ((p : ℕ) - 1) = bPden 49 := by
  rw [b_step_49]
  exact b_pden_step_gen (Nat.primesLE 227) 229
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_48

theorem b_step_50 : Nat.primesLE 233 = insert 233 (Nat.primesLE 229) :=
  primesLE_insert_next 229 233 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_50 : ∏ p ∈ Nat.primesLE 233, (p : ℕ) = bPnum 50 := by
  rw [b_step_50]
  exact b_pnum_step_gen (Nat.primesLE 229) 233
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_49
theorem b_pden_50 : ∏ p ∈ Nat.primesLE 233, ((p : ℕ) - 1) = bPden 50 := by
  rw [b_step_50]
  exact b_pden_step_gen (Nat.primesLE 229) 233
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_49

theorem b_step_51 : Nat.primesLE 239 = insert 239 (Nat.primesLE 233) :=
  primesLE_insert_next 233 239 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_51 : ∏ p ∈ Nat.primesLE 239, (p : ℕ) = bPnum 51 := by
  rw [b_step_51]
  exact b_pnum_step_gen (Nat.primesLE 233) 239
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_50
theorem b_pden_51 : ∏ p ∈ Nat.primesLE 239, ((p : ℕ) - 1) = bPden 51 := by
  rw [b_step_51]
  exact b_pden_step_gen (Nat.primesLE 233) 239
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_50

theorem b_step_52 : Nat.primesLE 241 = insert 241 (Nat.primesLE 239) :=
  primesLE_insert_next 239 241 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_52 : ∏ p ∈ Nat.primesLE 241, (p : ℕ) = bPnum 52 := by
  rw [b_step_52]
  exact b_pnum_step_gen (Nat.primesLE 239) 241
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_51
theorem b_pden_52 : ∏ p ∈ Nat.primesLE 241, ((p : ℕ) - 1) = bPden 52 := by
  rw [b_step_52]
  exact b_pden_step_gen (Nat.primesLE 239) 241
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_51

theorem b_step_53 : Nat.primesLE 251 = insert 251 (Nat.primesLE 241) :=
  primesLE_insert_next 241 251 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_53 : ∏ p ∈ Nat.primesLE 251, (p : ℕ) = bPnum 53 := by
  rw [b_step_53]
  exact b_pnum_step_gen (Nat.primesLE 241) 251
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_52
theorem b_pden_53 : ∏ p ∈ Nat.primesLE 251, ((p : ℕ) - 1) = bPden 53 := by
  rw [b_step_53]
  exact b_pden_step_gen (Nat.primesLE 241) 251
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_52

theorem b_step_54 : Nat.primesLE 257 = insert 257 (Nat.primesLE 251) :=
  primesLE_insert_next 251 257 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_54 : ∏ p ∈ Nat.primesLE 257, (p : ℕ) = bPnum 54 := by
  rw [b_step_54]
  exact b_pnum_step_gen (Nat.primesLE 251) 257
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_53
theorem b_pden_54 : ∏ p ∈ Nat.primesLE 257, ((p : ℕ) - 1) = bPden 54 := by
  rw [b_step_54]
  exact b_pden_step_gen (Nat.primesLE 251) 257
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_53

theorem b_step_55 : Nat.primesLE 263 = insert 263 (Nat.primesLE 257) :=
  primesLE_insert_next 257 263 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_55 : ∏ p ∈ Nat.primesLE 263, (p : ℕ) = bPnum 55 := by
  rw [b_step_55]
  exact b_pnum_step_gen (Nat.primesLE 257) 263
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_54
theorem b_pden_55 : ∏ p ∈ Nat.primesLE 263, ((p : ℕ) - 1) = bPden 55 := by
  rw [b_step_55]
  exact b_pden_step_gen (Nat.primesLE 257) 263
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_54

theorem b_step_56 : Nat.primesLE 269 = insert 269 (Nat.primesLE 263) :=
  primesLE_insert_next 263 269 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_56 : ∏ p ∈ Nat.primesLE 269, (p : ℕ) = bPnum 56 := by
  rw [b_step_56]
  exact b_pnum_step_gen (Nat.primesLE 263) 269
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_55
theorem b_pden_56 : ∏ p ∈ Nat.primesLE 269, ((p : ℕ) - 1) = bPden 56 := by
  rw [b_step_56]
  exact b_pden_step_gen (Nat.primesLE 263) 269
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_55

theorem b_step_57 : Nat.primesLE 271 = insert 271 (Nat.primesLE 269) :=
  primesLE_insert_next 269 271 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_57 : ∏ p ∈ Nat.primesLE 271, (p : ℕ) = bPnum 57 := by
  rw [b_step_57]
  exact b_pnum_step_gen (Nat.primesLE 269) 271
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_56
theorem b_pden_57 : ∏ p ∈ Nat.primesLE 271, ((p : ℕ) - 1) = bPden 57 := by
  rw [b_step_57]
  exact b_pden_step_gen (Nat.primesLE 269) 271
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_56

theorem b_step_58 : Nat.primesLE 277 = insert 277 (Nat.primesLE 271) :=
  primesLE_insert_next 271 277 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_58 : ∏ p ∈ Nat.primesLE 277, (p : ℕ) = bPnum 58 := by
  rw [b_step_58]
  exact b_pnum_step_gen (Nat.primesLE 271) 277
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_57
theorem b_pden_58 : ∏ p ∈ Nat.primesLE 277, ((p : ℕ) - 1) = bPden 58 := by
  rw [b_step_58]
  exact b_pden_step_gen (Nat.primesLE 271) 277
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_57

theorem b_step_59 : Nat.primesLE 281 = insert 281 (Nat.primesLE 277) :=
  primesLE_insert_next 277 281 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_59 : ∏ p ∈ Nat.primesLE 281, (p : ℕ) = bPnum 59 := by
  rw [b_step_59]
  exact b_pnum_step_gen (Nat.primesLE 277) 281
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_58
theorem b_pden_59 : ∏ p ∈ Nat.primesLE 281, ((p : ℕ) - 1) = bPden 59 := by
  rw [b_step_59]
  exact b_pden_step_gen (Nat.primesLE 277) 281
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_58

theorem b_step_60 : Nat.primesLE 283 = insert 283 (Nat.primesLE 281) :=
  primesLE_insert_next 281 283 (by norm_num) (by norm_num)
    (by intro m hm1 hm2; interval_cases m <;> norm_num)
theorem b_pnum_60 : ∏ p ∈ Nat.primesLE 283, (p : ℕ) = bPnum 60 := by
  rw [b_step_60]
  exact b_pnum_step_gen (Nat.primesLE 281) 283
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pnum_59
theorem b_pden_60 : ∏ p ∈ Nat.primesLE 283, ((p : ℕ) - 1) = bPden 60 := by
  rw [b_step_60]
  exact b_pden_step_gen (Nat.primesLE 281) 283
    (fun h => absurd ((Nat.mem_primesLE.mp h).1) (by omega))
    b_pden_59

theorem b_chain : Nat.primesLE 283
    = insert 283 (insert 281 (insert 277 (insert 271 (insert 269 (insert 263 (insert 257 (insert 251 (insert 241 (insert 239 (insert 233 (insert 229 (insert 227 (insert 223 (insert 211 (insert 199 (insert 197 (insert 193 (insert 191 (insert 181 (insert 179 (insert 173 (insert 167 (insert 163 (insert 157 (insert 151 (insert 149 (insert 139 (insert 137 (insert 131 (insert 127 (insert 113 (insert 109 (insert 107 (insert 103 (insert 101 (insert 97 (insert 89 (insert 83 (insert 79 (insert 73 (insert 71 (insert 67 (insert 61 (insert 59 (insert 53 (insert 47 (insert 43 (insert 41 (insert 37 (insert 31 (insert 29 (insert 23 (insert 19 (insert 17 (insert 13 (insert 11 (insert 7 (insert 5 (insert 3 (Nat.primesLE 2)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  rw [b_step_60, b_step_59, b_step_58, b_step_57, b_step_56, b_step_55, b_step_54, b_step_53, b_step_52, b_step_51, b_step_50, b_step_49, b_step_48, b_step_47, b_step_46, b_step_45, b_step_44, b_step_43, b_step_42, b_step_41, b_step_40, b_step_39, b_step_38, b_step_37, b_step_36, b_step_35, b_step_34, b_step_33, b_step_32, b_step_31, b_step_30, b_step_29, b_step_28, b_step_27, b_step_26, b_step_25, b_step_24, b_step_23, b_step_22, b_step_21, b_step_20, b_step_19, b_step_18, b_step_17, b_step_16, b_step_15, b_step_14, b_step_13, b_step_12, b_step_11, b_step_10, b_step_9, b_step_8, b_step_7, b_step_6, b_step_5, b_step_4, b_step_3, b_step_2, b_step_1]

theorem b_prime_in_table (q : ℕ) (h1 : 2 ≤ q) (h2 : q ≤ 283) (hp : q.Prime) :
    ∃ k, k < 61 ∧ bPtab k = q := by
  have hmem : q ∈ Nat.primesLE 283 := Nat.mem_primesLE.mpr ⟨h2, hp⟩
  rw [b_chain] at hmem
  simp only [Finset.mem_insert] at hmem
  rcases hmem with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|hrest)
  · exact ⟨60, by decide, by decide⟩
  · exact ⟨59, by decide, by decide⟩
  · exact ⟨58, by decide, by decide⟩
  · exact ⟨57, by decide, by decide⟩
  · exact ⟨56, by decide, by decide⟩
  · exact ⟨55, by decide, by decide⟩
  · exact ⟨54, by decide, by decide⟩
  · exact ⟨53, by decide, by decide⟩
  · exact ⟨52, by decide, by decide⟩
  · exact ⟨51, by decide, by decide⟩
  · exact ⟨50, by decide, by decide⟩
  · exact ⟨49, by decide, by decide⟩
  · exact ⟨48, by decide, by decide⟩
  · exact ⟨47, by decide, by decide⟩
  · exact ⟨46, by decide, by decide⟩
  · exact ⟨45, by decide, by decide⟩
  · exact ⟨44, by decide, by decide⟩
  · exact ⟨43, by decide, by decide⟩
  · exact ⟨42, by decide, by decide⟩
  · exact ⟨41, by decide, by decide⟩
  · exact ⟨40, by decide, by decide⟩
  · exact ⟨39, by decide, by decide⟩
  · exact ⟨38, by decide, by decide⟩
  · exact ⟨37, by decide, by decide⟩
  · exact ⟨36, by decide, by decide⟩
  · exact ⟨35, by decide, by decide⟩
  · exact ⟨34, by decide, by decide⟩
  · exact ⟨33, by decide, by decide⟩
  · exact ⟨32, by decide, by decide⟩
  · exact ⟨31, by decide, by decide⟩
  · exact ⟨30, by decide, by decide⟩
  · exact ⟨29, by decide, by decide⟩
  · exact ⟨28, by decide, by decide⟩
  · exact ⟨27, by decide, by decide⟩
  · exact ⟨26, by decide, by decide⟩
  · exact ⟨25, by decide, by decide⟩
  · exact ⟨24, by decide, by decide⟩
  · exact ⟨23, by decide, by decide⟩
  · exact ⟨22, by decide, by decide⟩
  · exact ⟨21, by decide, by decide⟩
  · exact ⟨20, by decide, by decide⟩
  · exact ⟨19, by decide, by decide⟩
  · exact ⟨18, by decide, by decide⟩
  · exact ⟨17, by decide, by decide⟩
  · exact ⟨16, by decide, by decide⟩
  · exact ⟨15, by decide, by decide⟩
  · exact ⟨14, by decide, by decide⟩
  · exact ⟨13, by decide, by decide⟩
  · exact ⟨12, by decide, by decide⟩
  · exact ⟨11, by decide, by decide⟩
  · exact ⟨10, by decide, by decide⟩
  · exact ⟨9, by decide, by decide⟩
  · exact ⟨8, by decide, by decide⟩
  · exact ⟨7, by decide, by decide⟩
  · exact ⟨6, by decide, by decide⟩
  · exact ⟨5, by decide, by decide⟩
  · exact ⟨4, by decide, by decide⟩
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · have hle : q ≤ 2 := (Nat.mem_primesLE.mp hrest).1
    have hq : q = 2 := by omega
    subst hq
    exact ⟨0, by decide, by decide⟩

lemma b_pnum_eq (k : ℕ) (hk : k < 61) :
    (∏ p ∈ Nat.primesLE (bPtab k), (p : ℕ)) = bPnum k := by
  interval_cases k
  · exact b_pnum_0
  · exact b_pnum_1
  · exact b_pnum_2
  · exact b_pnum_3
  · exact b_pnum_4
  · exact b_pnum_5
  · exact b_pnum_6
  · exact b_pnum_7
  · exact b_pnum_8
  · exact b_pnum_9
  · exact b_pnum_10
  · exact b_pnum_11
  · exact b_pnum_12
  · exact b_pnum_13
  · exact b_pnum_14
  · exact b_pnum_15
  · exact b_pnum_16
  · exact b_pnum_17
  · exact b_pnum_18
  · exact b_pnum_19
  · exact b_pnum_20
  · exact b_pnum_21
  · exact b_pnum_22
  · exact b_pnum_23
  · exact b_pnum_24
  · exact b_pnum_25
  · exact b_pnum_26
  · exact b_pnum_27
  · exact b_pnum_28
  · exact b_pnum_29
  · exact b_pnum_30
  · exact b_pnum_31
  · exact b_pnum_32
  · exact b_pnum_33
  · exact b_pnum_34
  · exact b_pnum_35
  · exact b_pnum_36
  · exact b_pnum_37
  · exact b_pnum_38
  · exact b_pnum_39
  · exact b_pnum_40
  · exact b_pnum_41
  · exact b_pnum_42
  · exact b_pnum_43
  · exact b_pnum_44
  · exact b_pnum_45
  · exact b_pnum_46
  · exact b_pnum_47
  · exact b_pnum_48
  · exact b_pnum_49
  · exact b_pnum_50
  · exact b_pnum_51
  · exact b_pnum_52
  · exact b_pnum_53
  · exact b_pnum_54
  · exact b_pnum_55
  · exact b_pnum_56
  · exact b_pnum_57
  · exact b_pnum_58
  · exact b_pnum_59
  · exact b_pnum_60

lemma b_pden_eq (k : ℕ) (hk : k < 61) :
    (∏ p ∈ Nat.primesLE (bPtab k), ((p : ℕ) - 1)) = bPden k := by
  interval_cases k
  · exact b_pden_0
  · exact b_pden_1
  · exact b_pden_2
  · exact b_pden_3
  · exact b_pden_4
  · exact b_pden_5
  · exact b_pden_6
  · exact b_pden_7
  · exact b_pden_8
  · exact b_pden_9
  · exact b_pden_10
  · exact b_pden_11
  · exact b_pden_12
  · exact b_pden_13
  · exact b_pden_14
  · exact b_pden_15
  · exact b_pden_16
  · exact b_pden_17
  · exact b_pden_18
  · exact b_pden_19
  · exact b_pden_20
  · exact b_pden_21
  · exact b_pden_22
  · exact b_pden_23
  · exact b_pden_24
  · exact b_pden_25
  · exact b_pden_26
  · exact b_pden_27
  · exact b_pden_28
  · exact b_pden_29
  · exact b_pden_30
  · exact b_pden_31
  · exact b_pden_32
  · exact b_pden_33
  · exact b_pden_34
  · exact b_pden_35
  · exact b_pden_36
  · exact b_pden_37
  · exact b_pden_38
  · exact b_pden_39
  · exact b_pden_40
  · exact b_pden_41
  · exact b_pden_42
  · exact b_pden_43
  · exact b_pden_44
  · exact b_pden_45
  · exact b_pden_46
  · exact b_pden_47
  · exact b_pden_48
  · exact b_pden_49
  · exact b_pden_50
  · exact b_pden_51
  · exact b_pden_52
  · exact b_pden_53
  · exact b_pden_54
  · exact b_pden_55
  · exact b_pden_56
  · exact b_pden_57
  · exact b_pden_58
  · exact b_pden_59
  · exact b_pden_60

lemma b_prod_id (k : ℕ) (hk : k < 61) :
    ∏ p ∈ Nat.primesLE (bPtab k), (p : ℝ) / ((p : ℝ) - 1) =
      ((bPnum k : ℕ) : ℝ) / ((bPden k : ℕ) : ℝ) := by
  have hsub : ∀ p ∈ Nat.primesLE (bPtab k), (p : ℝ) - 1 = ((p - 1 : ℕ) : ℝ) := by
    intro p hp
    have h1 : 1 ≤ p := (Nat.one_lt_of_mem_primesLE hp).le
    simpa using (Nat.cast_sub h1).symm
  rw [show (∏ p ∈ Nat.primesLE (bPtab k), (p : ℝ) / ((p : ℝ) - 1)) =
        ∏ p ∈ Nat.primesLE (bPtab k), (p : ℝ) / ((p - 1 : ℕ) : ℝ) by
      exact Finset.prod_congr rfl (fun p hp => by rw [hsub p hp]),
    Finset.prod_div_distrib, ← Nat.cast_prod, ← Nat.cast_prod,
    b_pnum_eq k hk, b_pden_eq k hk]

theorem b_exp_gamma_ge :
    (1781071 : ℝ) / 10 ^ 6 ≤ Real.exp Real.eulerMascheroniConstant := by
  calc (1781071 : ℝ) / 10 ^ 6
      ≤ ∑ i ∈ Finset.range 12, (57721565 / 10 ^ 8 : ℝ) ^ i / (i.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp (57721565 / 10 ^ 8) :=
        Real.sum_le_exp_of_nonneg (by norm_num) 12
    _ ≤ Real.exp Real.eulerMascheroniConstant :=
        Real.exp_le_exp.mpr theta_cert_totient_gamma_lower

lemma b_loglo_0 : ((bClo 0 : ℕ) : ℝ) < Real.log (bLo 0) * 10 ^ 6 := by
  rw [show bLo 0 = 2 by decide]
  have hM : ((bClo 0 : ℕ) : ℝ) = ((0 : ℝ) + 0.693147) * 10 ^ 6 := by
    rw [show bClo 0 = 693147 by decide]
    norm_num
  rw [hM]
  have hexp : (0 : ℝ) + 0.693147 < Real.log 2 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 2)]
    have hm : Real.exp (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 0 := by
      rw [show (0 : ℝ) = (0 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 0
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.693147)
      (by norm_num : (0.693147 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((0 : ℝ) + 0.693147) ≤
        (2.7182818286 : ℝ) ^ 0 * Real.exp 0.693147 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.693147)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 0)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((0 : ℝ) + 0.693147) * 10 ^ 6 < Real.log 2 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_1 : ((bClo 1 : ℕ) : ℝ) < Real.log (bLo 1) * 10 ^ 6 := by
  rw [show bLo 1 = 3 by decide]
  have hM : ((bClo 1 : ℕ) : ℝ) = ((1 : ℝ) + 0.098612) * 10 ^ 6 := by
    rw [show bClo 1 = 1098612 by decide]
    norm_num
  rw [hM]
  have hexp : (1 : ℝ) + 0.098612 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    have hm : Real.exp (1 : ℝ) ≤ (2.7182818286 : ℝ) ^ 1 := by
      rw [show (1 : ℝ) = (1 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 1
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.098612)
      (by norm_num : (0.098612 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((1 : ℝ) + 0.098612) ≤
        (2.7182818286 : ℝ) ^ 1 * Real.exp 0.098612 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.098612)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 1)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((1 : ℝ) + 0.098612) * 10 ^ 6 < Real.log 3 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_2 : ((bClo 2 : ℕ) : ℝ) < Real.log (bLo 2) * 10 ^ 6 := by
  rw [show bLo 2 = 5 by decide]
  have hM : ((bClo 2 : ℕ) : ℝ) = ((1 : ℝ) + 0.609437) * 10 ^ 6 := by
    rw [show bClo 2 = 1609437 by decide]
    norm_num
  rw [hM]
  have hexp : (1 : ℝ) + 0.609437 < Real.log 5 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 5)]
    have hm : Real.exp (1 : ℝ) ≤ (2.7182818286 : ℝ) ^ 1 := by
      rw [show (1 : ℝ) = (1 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 1
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.609437)
      (by norm_num : (0.609437 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((1 : ℝ) + 0.609437) ≤
        (2.7182818286 : ℝ) ^ 1 * Real.exp 0.609437 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.609437)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 1)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((1 : ℝ) + 0.609437) * 10 ^ 6 < Real.log 5 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_3 : ((bClo 3 : ℕ) : ℝ) < Real.log (bLo 3) * 10 ^ 6 := by
  rw [show bLo 3 = 7 by decide]
  have hM : ((bClo 3 : ℕ) : ℝ) = ((1 : ℝ) + 0.945910) * 10 ^ 6 := by
    rw [show bClo 3 = 1945910 by decide]
    norm_num
  rw [hM]
  have hexp : (1 : ℝ) + 0.945910 < Real.log 7 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 7)]
    have hm : Real.exp (1 : ℝ) ≤ (2.7182818286 : ℝ) ^ 1 := by
      rw [show (1 : ℝ) = (1 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 1
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.945910)
      (by norm_num : (0.945910 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((1 : ℝ) + 0.945910) ≤
        (2.7182818286 : ℝ) ^ 1 * Real.exp 0.945910 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.945910)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 1)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((1 : ℝ) + 0.945910) * 10 ^ 6 < Real.log 7 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_4 : ((bClo 4 : ℕ) : ℝ) < Real.log (bLo 4) * 10 ^ 6 := by
  rw [show bLo 4 = 11 by decide]
  have hM : ((bClo 4 : ℕ) : ℝ) = ((2 : ℝ) + 0.397895) * 10 ^ 6 := by
    rw [show bClo 4 = 2397895 by decide]
    norm_num
  rw [hM]
  have hexp : (2 : ℝ) + 0.397895 < Real.log 11 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 11)]
    have hm : Real.exp (2 : ℝ) ≤ (2.7182818286 : ℝ) ^ 2 := by
      rw [show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 2
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.397895)
      (by norm_num : (0.397895 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((2 : ℝ) + 0.397895) ≤
        (2.7182818286 : ℝ) ^ 2 * Real.exp 0.397895 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.397895)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 2)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((2 : ℝ) + 0.397895) * 10 ^ 6 < Real.log 11 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_5 : ((bClo 5 : ℕ) : ℝ) < Real.log (bLo 5) * 10 ^ 6 := by
  rw [show bLo 5 = 13 by decide]
  have hM : ((bClo 5 : ℕ) : ℝ) = ((2 : ℝ) + 0.564949) * 10 ^ 6 := by
    rw [show bClo 5 = 2564949 by decide]
    norm_num
  rw [hM]
  have hexp : (2 : ℝ) + 0.564949 < Real.log 13 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 13)]
    have hm : Real.exp (2 : ℝ) ≤ (2.7182818286 : ℝ) ^ 2 := by
      rw [show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 2
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.564949)
      (by norm_num : (0.564949 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((2 : ℝ) + 0.564949) ≤
        (2.7182818286 : ℝ) ^ 2 * Real.exp 0.564949 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.564949)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 2)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((2 : ℝ) + 0.564949) * 10 ^ 6 < Real.log 13 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_6 : ((bClo 6 : ℕ) : ℝ) < Real.log (bLo 6) * 10 ^ 6 := by
  rw [show bLo 6 = 17 by decide]
  have hM : ((bClo 6 : ℕ) : ℝ) = ((2 : ℝ) + 0.833213) * 10 ^ 6 := by
    rw [show bClo 6 = 2833213 by decide]
    norm_num
  rw [hM]
  have hexp : (2 : ℝ) + 0.833213 < Real.log 17 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 17)]
    have hm : Real.exp (2 : ℝ) ≤ (2.7182818286 : ℝ) ^ 2 := by
      rw [show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 2
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.833213)
      (by norm_num : (0.833213 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((2 : ℝ) + 0.833213) ≤
        (2.7182818286 : ℝ) ^ 2 * Real.exp 0.833213 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.833213)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 2)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((2 : ℝ) + 0.833213) * 10 ^ 6 < Real.log 17 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_7 : ((bClo 7 : ℕ) : ℝ) < Real.log (bLo 7) * 10 ^ 6 := by
  rw [show bLo 7 = 19 by decide]
  have hM : ((bClo 7 : ℕ) : ℝ) = ((2 : ℝ) + 0.944438) * 10 ^ 6 := by
    rw [show bClo 7 = 2944438 by decide]
    norm_num
  rw [hM]
  have hexp : (2 : ℝ) + 0.944438 < Real.log 19 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 19)]
    have hm : Real.exp (2 : ℝ) ≤ (2.7182818286 : ℝ) ^ 2 := by
      rw [show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 2
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.944438)
      (by norm_num : (0.944438 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((2 : ℝ) + 0.944438) ≤
        (2.7182818286 : ℝ) ^ 2 * Real.exp 0.944438 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.944438)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 2)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((2 : ℝ) + 0.944438) * 10 ^ 6 < Real.log 19 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_8 : ((bClo 8 : ℕ) : ℝ) < Real.log (bLo 8) * 10 ^ 6 := by
  rw [show bLo 8 = 23 by decide]
  have hM : ((bClo 8 : ℕ) : ℝ) = ((3 : ℝ) + 0.135494) * 10 ^ 6 := by
    rw [show bClo 8 = 3135494 by decide]
    norm_num
  rw [hM]
  have hexp : (3 : ℝ) + 0.135494 < Real.log 23 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 23)]
    have hm : Real.exp (3 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3 := by
      rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.135494)
      (by norm_num : (0.135494 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((3 : ℝ) + 0.135494) ≤
        (2.7182818286 : ℝ) ^ 3 * Real.exp 0.135494 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.135494)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((3 : ℝ) + 0.135494) * 10 ^ 6 < Real.log 23 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_9 : ((bClo 9 : ℕ) : ℝ) < Real.log (bLo 9) * 10 ^ 6 := by
  rw [show bLo 9 = 29 by decide]
  have hM : ((bClo 9 : ℕ) : ℝ) = ((3 : ℝ) + 0.367295) * 10 ^ 6 := by
    rw [show bClo 9 = 3367295 by decide]
    norm_num
  rw [hM]
  have hexp : (3 : ℝ) + 0.367295 < Real.log 29 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 29)]
    have hm : Real.exp (3 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3 := by
      rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.367295)
      (by norm_num : (0.367295 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((3 : ℝ) + 0.367295) ≤
        (2.7182818286 : ℝ) ^ 3 * Real.exp 0.367295 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.367295)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((3 : ℝ) + 0.367295) * 10 ^ 6 < Real.log 29 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_10 : ((bClo 10 : ℕ) : ℝ) < Real.log (bLo 10) * 10 ^ 6 := by
  rw [show bLo 10 = 31 by decide]
  have hM : ((bClo 10 : ℕ) : ℝ) = ((3 : ℝ) + 0.433987) * 10 ^ 6 := by
    rw [show bClo 10 = 3433987 by decide]
    norm_num
  rw [hM]
  have hexp : (3 : ℝ) + 0.433987 < Real.log 31 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 31)]
    have hm : Real.exp (3 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3 := by
      rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.433987)
      (by norm_num : (0.433987 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((3 : ℝ) + 0.433987) ≤
        (2.7182818286 : ℝ) ^ 3 * Real.exp 0.433987 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.433987)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((3 : ℝ) + 0.433987) * 10 ^ 6 < Real.log 31 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_11 : ((bClo 11 : ℕ) : ℝ) < Real.log (bLo 11) * 10 ^ 6 := by
  rw [show bLo 11 = 37 by decide]
  have hM : ((bClo 11 : ℕ) : ℝ) = ((3 : ℝ) + 0.610917) * 10 ^ 6 := by
    rw [show bClo 11 = 3610917 by decide]
    norm_num
  rw [hM]
  have hexp : (3 : ℝ) + 0.610917 < Real.log 37 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 37)]
    have hm : Real.exp (3 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3 := by
      rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.610917)
      (by norm_num : (0.610917 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((3 : ℝ) + 0.610917) ≤
        (2.7182818286 : ℝ) ^ 3 * Real.exp 0.610917 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.610917)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((3 : ℝ) + 0.610917) * 10 ^ 6 < Real.log 37 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_12 : ((bClo 12 : ℕ) : ℝ) < Real.log (bLo 12) * 10 ^ 6 := by
  rw [show bLo 12 = 41 by decide]
  have hM : ((bClo 12 : ℕ) : ℝ) = ((3 : ℝ) + 0.713572) * 10 ^ 6 := by
    rw [show bClo 12 = 3713572 by decide]
    norm_num
  rw [hM]
  have hexp : (3 : ℝ) + 0.713572 < Real.log 41 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 41)]
    have hm : Real.exp (3 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3 := by
      rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.713572)
      (by norm_num : (0.713572 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((3 : ℝ) + 0.713572) ≤
        (2.7182818286 : ℝ) ^ 3 * Real.exp 0.713572 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.713572)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((3 : ℝ) + 0.713572) * 10 ^ 6 < Real.log 41 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_13 : ((bClo 13 : ℕ) : ℝ) < Real.log (bLo 13) * 10 ^ 6 := by
  rw [show bLo 13 = 43 by decide]
  have hM : ((bClo 13 : ℕ) : ℝ) = ((3 : ℝ) + 0.761200) * 10 ^ 6 := by
    rw [show bClo 13 = 3761200 by decide]
    norm_num
  rw [hM]
  have hexp : (3 : ℝ) + 0.761200 < Real.log 43 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 43)]
    have hm : Real.exp (3 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3 := by
      rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.761200)
      (by norm_num : (0.761200 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((3 : ℝ) + 0.761200) ≤
        (2.7182818286 : ℝ) ^ 3 * Real.exp 0.761200 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.761200)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((3 : ℝ) + 0.761200) * 10 ^ 6 < Real.log 43 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_14 : ((bClo 14 : ℕ) : ℝ) < Real.log (bLo 14) * 10 ^ 6 := by
  rw [show bLo 14 = 47 by decide]
  have hM : ((bClo 14 : ℕ) : ℝ) = ((3 : ℝ) + 0.850147) * 10 ^ 6 := by
    rw [show bClo 14 = 3850147 by decide]
    norm_num
  rw [hM]
  have hexp : (3 : ℝ) + 0.850147 < Real.log 47 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 47)]
    have hm : Real.exp (3 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3 := by
      rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.850147)
      (by norm_num : (0.850147 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((3 : ℝ) + 0.850147) ≤
        (2.7182818286 : ℝ) ^ 3 * Real.exp 0.850147 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.850147)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((3 : ℝ) + 0.850147) * 10 ^ 6 < Real.log 47 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_15 : ((bClo 15 : ℕ) : ℝ) < Real.log (bLo 15) * 10 ^ 6 := by
  rw [show bLo 15 = 53 by decide]
  have hM : ((bClo 15 : ℕ) : ℝ) = ((3 : ℝ) + 0.970291) * 10 ^ 6 := by
    rw [show bClo 15 = 3970291 by decide]
    norm_num
  rw [hM]
  have hexp : (3 : ℝ) + 0.970291 < Real.log 53 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 53)]
    have hm : Real.exp (3 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3 := by
      rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.970291)
      (by norm_num : (0.970291 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((3 : ℝ) + 0.970291) ≤
        (2.7182818286 : ℝ) ^ 3 * Real.exp 0.970291 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.970291)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 3)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((3 : ℝ) + 0.970291) * 10 ^ 6 < Real.log 53 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_16 : ((bClo 16 : ℕ) : ℝ) < Real.log (bLo 16) * 10 ^ 6 := by
  rw [show bLo 16 = 59 by decide]
  have hM : ((bClo 16 : ℕ) : ℝ) = ((4 : ℝ) + 0.077537) * 10 ^ 6 := by
    rw [show bClo 16 = 4077537 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.077537 < Real.log 59 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 59)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.077537)
      (by norm_num : (0.077537 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.077537) ≤
        (2.7182818286 : ℝ) ^ 4 * Real.exp 0.077537 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.077537)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.077537) * 10 ^ 6 < Real.log 59 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_17 : ((bClo 17 : ℕ) : ℝ) < Real.log (bLo 17) * 10 ^ 6 := by
  rw [show bLo 17 = 61 by decide]
  have hM : ((bClo 17 : ℕ) : ℝ) = ((4 : ℝ) + 0.110873) * 10 ^ 6 := by
    rw [show bClo 17 = 4110873 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.110873 < Real.log 61 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 61)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.110873)
      (by norm_num : (0.110873 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.110873) ≤
        (2.7182818286 : ℝ) ^ 4 * Real.exp 0.110873 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.110873)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.110873) * 10 ^ 6 < Real.log 61 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_18 : ((bClo 18 : ℕ) : ℝ) < Real.log (bLo 18) * 10 ^ 6 := by
  rw [show bLo 18 = 67 by decide]
  have hM : ((bClo 18 : ℕ) : ℝ) = ((4 : ℝ) + 0.204692) * 10 ^ 6 := by
    rw [show bClo 18 = 4204692 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.204692 < Real.log 67 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 67)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.204692)
      (by norm_num : (0.204692 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.204692) ≤
        (2.7182818286 : ℝ) ^ 4 * Real.exp 0.204692 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.204692)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.204692) * 10 ^ 6 < Real.log 67 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_19 : ((bClo 19 : ℕ) : ℝ) < Real.log (bLo 19) * 10 ^ 6 := by
  rw [show bLo 19 = 71 by decide]
  have hM : ((bClo 19 : ℕ) : ℝ) = ((4 : ℝ) + 0.262679) * 10 ^ 6 := by
    rw [show bClo 19 = 4262679 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.262679 < Real.log 71 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 71)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.262679)
      (by norm_num : (0.262679 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.262679) ≤
        (2.7182818286 : ℝ) ^ 4 * Real.exp 0.262679 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.262679)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.262679) * 10 ^ 6 < Real.log 71 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_20 : ((bClo 20 : ℕ) : ℝ) < Real.log (bLo 20) * 10 ^ 6 := by
  rw [show bLo 20 = 73 by decide]
  have hM : ((bClo 20 : ℕ) : ℝ) = ((4 : ℝ) + 0.290459) * 10 ^ 6 := by
    rw [show bClo 20 = 4290459 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.290459 < Real.log 73 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 73)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.290459)
      (by norm_num : (0.290459 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.290459) ≤
        (2.7182818286 : ℝ) ^ 4 * Real.exp 0.290459 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.290459)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.290459) * 10 ^ 6 < Real.log 73 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_21 : ((bClo 21 : ℕ) : ℝ) < Real.log (bLo 21) * 10 ^ 6 := by
  rw [show bLo 21 = 79 by decide]
  have hM : ((bClo 21 : ℕ) : ℝ) = ((4 : ℝ) + 0.369447) * 10 ^ 6 := by
    rw [show bClo 21 = 4369447 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.369447 < Real.log 79 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 79)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.369447)
      (by norm_num : (0.369447 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.369447) ≤
        (2.7182818286 : ℝ) ^ 4 * Real.exp 0.369447 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.369447)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.369447) * 10 ^ 6 < Real.log 79 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_22 : ((bClo 22 : ℕ) : ℝ) < Real.log (bLo 22) * 10 ^ 6 := by
  rw [show bLo 22 = 83 by decide]
  have hM : ((bClo 22 : ℕ) : ℝ) = ((4 : ℝ) + 0.418840) * 10 ^ 6 := by
    rw [show bClo 22 = 4418840 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.418840 < Real.log 83 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 83)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.418840)
      (by norm_num : (0.418840 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.418840) ≤
        (2.7182818286 : ℝ) ^ 4 * Real.exp 0.418840 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.418840)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.418840) * 10 ^ 6 < Real.log 83 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_23 : ((bClo 23 : ℕ) : ℝ) < Real.log (bLo 23) * 10 ^ 6 := by
  rw [show bLo 23 = 89 by decide]
  have hM : ((bClo 23 : ℕ) : ℝ) = ((4 : ℝ) + 0.488636) * 10 ^ 6 := by
    rw [show bClo 23 = 4488636 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.488636 < Real.log 89 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 89)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.488636)
      (by norm_num : (0.488636 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.488636) ≤
        (2.7182818286 : ℝ) ^ 4 * Real.exp 0.488636 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.488636)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.488636) * 10 ^ 6 < Real.log 89 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_24 : ((bClo 24 : ℕ) : ℝ) < Real.log (bLo 24) * 10 ^ 6 := by
  rw [show bLo 24 = 97 by decide]
  have hM : ((bClo 24 : ℕ) : ℝ) = ((4 : ℝ) + 0.574710) * 10 ^ 6 := by
    rw [show bClo 24 = 4574710 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.574710 < Real.log 97 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 97)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.574710)
      (by norm_num : (0.574710 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.574710) ≤
        (2.7182818286 : ℝ) ^ 4 * Real.exp 0.574710 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.574710)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.574710) * 10 ^ 6 < Real.log 97 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_25 : ((bClo 25 : ℕ) : ℝ) < Real.log (bLo 25) * 10 ^ 6 := by
  rw [show bLo 25 = 101 by decide]
  have hM : ((bClo 25 : ℕ) : ℝ) = ((4 : ℝ) + 0.615120) * 10 ^ 6 := by
    rw [show bClo 25 = 4615120 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.615120 < Real.log 101 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 101)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.615120)
      (by norm_num : (0.615120 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.615120) ≤
        (2.7182818286 : ℝ) ^ 4 * Real.exp 0.615120 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.615120)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.615120) * 10 ^ 6 < Real.log 101 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_26 : ((bClo 26 : ℕ) : ℝ) < Real.log (bLo 26) * 10 ^ 6 := by
  rw [show bLo 26 = 103 by decide]
  have hM : ((bClo 26 : ℕ) : ℝ) = ((4 : ℝ) + 0.634728) * 10 ^ 6 := by
    rw [show bClo 26 = 4634728 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.634728 < Real.log 103 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 103)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.634728)
      (by norm_num : (0.634728 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.634728) ≤
        (2.7182818286 : ℝ) ^ 4 * Real.exp 0.634728 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.634728)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.634728) * 10 ^ 6 < Real.log 103 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_27 : ((bClo 27 : ℕ) : ℝ) < Real.log (bLo 27) * 10 ^ 6 := by
  rw [show bLo 27 = 107 by decide]
  have hM : ((bClo 27 : ℕ) : ℝ) = ((4 : ℝ) + 0.672828) * 10 ^ 6 := by
    rw [show bClo 27 = 4672828 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.672828 < Real.log 107 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 107)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.672828)
      (by norm_num : (0.672828 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.672828) ≤
        (2.7182818286 : ℝ) ^ 4 * Real.exp 0.672828 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.672828)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.672828) * 10 ^ 6 < Real.log 107 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_28 : ((bClo 28 : ℕ) : ℝ) < Real.log (bLo 28) * 10 ^ 6 := by
  rw [show bLo 28 = 109 by decide]
  have hM : ((bClo 28 : ℕ) : ℝ) = ((4 : ℝ) + 0.691347) * 10 ^ 6 := by
    rw [show bClo 28 = 4691347 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.691347 < Real.log 109 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 109)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.691347)
      (by norm_num : (0.691347 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.691347) ≤
        (2.7182818286 : ℝ) ^ 4 * Real.exp 0.691347 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.691347)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.691347) * 10 ^ 6 < Real.log 109 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_29 : ((bClo 29 : ℕ) : ℝ) < Real.log (bLo 29) * 10 ^ 6 := by
  rw [show bLo 29 = 113 by decide]
  have hM : ((bClo 29 : ℕ) : ℝ) = ((4 : ℝ) + 0.727387) * 10 ^ 6 := by
    rw [show bClo 29 = 4727387 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.727387 < Real.log 113 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 113)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.727387)
      (by norm_num : (0.727387 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.727387) ≤
        (2.7182818286 : ℝ) ^ 4 * Real.exp 0.727387 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.727387)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.727387) * 10 ^ 6 < Real.log 113 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_30 : ((bClo 30 : ℕ) : ℝ) < Real.log (bLo 30) * 10 ^ 6 := by
  rw [show bLo 30 = 127 by decide]
  have hM : ((bClo 30 : ℕ) : ℝ) = ((4 : ℝ) + 0.844187) * 10 ^ 6 := by
    rw [show bClo 30 = 4844187 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.844187 < Real.log 127 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 127)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.844187)
      (by norm_num : (0.844187 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.844187) ≤
        (2.7182818286 : ℝ) ^ 4 * Real.exp 0.844187 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.844187)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.844187) * 10 ^ 6 < Real.log 127 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_31 : ((bClo 31 : ℕ) : ℝ) < Real.log (bLo 31) * 10 ^ 6 := by
  rw [show bLo 31 = 131 by decide]
  have hM : ((bClo 31 : ℕ) : ℝ) = ((4 : ℝ) + 0.875197) * 10 ^ 6 := by
    rw [show bClo 31 = 4875197 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.875197 < Real.log 131 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 131)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.875197)
      (by norm_num : (0.875197 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.875197) ≤
        (2.7182818286 : ℝ) ^ 4 * Real.exp 0.875197 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.875197)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.875197) * 10 ^ 6 < Real.log 131 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_32 : ((bClo 32 : ℕ) : ℝ) < Real.log (bLo 32) * 10 ^ 6 := by
  rw [show bLo 32 = 137 by decide]
  have hM : ((bClo 32 : ℕ) : ℝ) = ((4 : ℝ) + 0.919980) * 10 ^ 6 := by
    rw [show bClo 32 = 4919980 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.919980 < Real.log 137 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 137)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.919980)
      (by norm_num : (0.919980 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.919980) ≤
        (2.7182818286 : ℝ) ^ 4 * Real.exp 0.919980 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.919980)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.919980) * 10 ^ 6 < Real.log 137 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_33 : ((bClo 33 : ℕ) : ℝ) < Real.log (bLo 33) * 10 ^ 6 := by
  rw [show bLo 33 = 139 by decide]
  have hM : ((bClo 33 : ℕ) : ℝ) = ((4 : ℝ) + 0.934473) * 10 ^ 6 := by
    rw [show bClo 33 = 4934473 by decide]
    norm_num
  rw [hM]
  have hexp : (4 : ℝ) + 0.934473 < Real.log 139 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 139)]
    have hm : Real.exp (4 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4 := by
      rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.934473)
      (by norm_num : (0.934473 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((4 : ℝ) + 0.934473) ≤
        (2.7182818286 : ℝ) ^ 4 * Real.exp 0.934473 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.934473)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 4)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((4 : ℝ) + 0.934473) * 10 ^ 6 < Real.log 139 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_34 : ((bClo 34 : ℕ) : ℝ) < Real.log (bLo 34) * 10 ^ 6 := by
  rw [show bLo 34 = 149 by decide]
  have hM : ((bClo 34 : ℕ) : ℝ) = ((5 : ℝ) + 0.003946) * 10 ^ 6 := by
    rw [show bClo 34 = 5003946 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.003946 < Real.log 149 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 149)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.003946)
      (by norm_num : (0.003946 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.003946) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.003946 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.003946)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.003946) * 10 ^ 6 < Real.log 149 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_35 : ((bClo 35 : ℕ) : ℝ) < Real.log (bLo 35) * 10 ^ 6 := by
  rw [show bLo 35 = 151 by decide]
  have hM : ((bClo 35 : ℕ) : ℝ) = ((5 : ℝ) + 0.017279) * 10 ^ 6 := by
    rw [show bClo 35 = 5017279 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.017279 < Real.log 151 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 151)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.017279)
      (by norm_num : (0.017279 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.017279) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.017279 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.017279)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.017279) * 10 ^ 6 < Real.log 151 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_36 : ((bClo 36 : ℕ) : ℝ) < Real.log (bLo 36) * 10 ^ 6 := by
  rw [show bLo 36 = 157 by decide]
  have hM : ((bClo 36 : ℕ) : ℝ) = ((5 : ℝ) + 0.056245) * 10 ^ 6 := by
    rw [show bClo 36 = 5056245 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.056245 < Real.log 157 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 157)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.056245)
      (by norm_num : (0.056245 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.056245) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.056245 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.056245)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.056245) * 10 ^ 6 < Real.log 157 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_37 : ((bClo 37 : ℕ) : ℝ) < Real.log (bLo 37) * 10 ^ 6 := by
  rw [show bLo 37 = 163 by decide]
  have hM : ((bClo 37 : ℕ) : ℝ) = ((5 : ℝ) + 0.093750) * 10 ^ 6 := by
    rw [show bClo 37 = 5093750 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.093750 < Real.log 163 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 163)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.093750)
      (by norm_num : (0.093750 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.093750) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.093750 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.093750)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.093750) * 10 ^ 6 < Real.log 163 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_38 : ((bClo 38 : ℕ) : ℝ) < Real.log (bLo 38) * 10 ^ 6 := by
  rw [show bLo 38 = 167 by decide]
  have hM : ((bClo 38 : ℕ) : ℝ) = ((5 : ℝ) + 0.117993) * 10 ^ 6 := by
    rw [show bClo 38 = 5117993 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.117993 < Real.log 167 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 167)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.117993)
      (by norm_num : (0.117993 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.117993) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.117993 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.117993)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.117993) * 10 ^ 6 < Real.log 167 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_39 : ((bClo 39 : ℕ) : ℝ) < Real.log (bLo 39) * 10 ^ 6 := by
  rw [show bLo 39 = 173 by decide]
  have hM : ((bClo 39 : ℕ) : ℝ) = ((5 : ℝ) + 0.153291) * 10 ^ 6 := by
    rw [show bClo 39 = 5153291 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.153291 < Real.log 173 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 173)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.153291)
      (by norm_num : (0.153291 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.153291) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.153291 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.153291)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.153291) * 10 ^ 6 < Real.log 173 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_40 : ((bClo 40 : ℕ) : ℝ) < Real.log (bLo 40) * 10 ^ 6 := by
  rw [show bLo 40 = 179 by decide]
  have hM : ((bClo 40 : ℕ) : ℝ) = ((5 : ℝ) + 0.187385) * 10 ^ 6 := by
    rw [show bClo 40 = 5187385 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.187385 < Real.log 179 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 179)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.187385)
      (by norm_num : (0.187385 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.187385) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.187385 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.187385)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.187385) * 10 ^ 6 < Real.log 179 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_41 : ((bClo 41 : ℕ) : ℝ) < Real.log (bLo 41) * 10 ^ 6 := by
  rw [show bLo 41 = 181 by decide]
  have hM : ((bClo 41 : ℕ) : ℝ) = ((5 : ℝ) + 0.198497) * 10 ^ 6 := by
    rw [show bClo 41 = 5198497 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.198497 < Real.log 181 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 181)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.198497)
      (by norm_num : (0.198497 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.198497) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.198497 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.198497)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.198497) * 10 ^ 6 < Real.log 181 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_42 : ((bClo 42 : ℕ) : ℝ) < Real.log (bLo 42) * 10 ^ 6 := by
  rw [show bLo 42 = 191 by decide]
  have hM : ((bClo 42 : ℕ) : ℝ) = ((5 : ℝ) + 0.252273) * 10 ^ 6 := by
    rw [show bClo 42 = 5252273 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.252273 < Real.log 191 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 191)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.252273)
      (by norm_num : (0.252273 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.252273) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.252273 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.252273)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.252273) * 10 ^ 6 < Real.log 191 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_43 : ((bClo 43 : ℕ) : ℝ) < Real.log (bLo 43) * 10 ^ 6 := by
  rw [show bLo 43 = 193 by decide]
  have hM : ((bClo 43 : ℕ) : ℝ) = ((5 : ℝ) + 0.262690) * 10 ^ 6 := by
    rw [show bClo 43 = 5262690 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.262690 < Real.log 193 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 193)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.262690)
      (by norm_num : (0.262690 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.262690) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.262690 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.262690)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.262690) * 10 ^ 6 < Real.log 193 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_44 : ((bClo 44 : ℕ) : ℝ) < Real.log (bLo 44) * 10 ^ 6 := by
  rw [show bLo 44 = 197 by decide]
  have hM : ((bClo 44 : ℕ) : ℝ) = ((5 : ℝ) + 0.283203) * 10 ^ 6 := by
    rw [show bClo 44 = 5283203 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.283203 < Real.log 197 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 197)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.283203)
      (by norm_num : (0.283203 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.283203) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.283203 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.283203)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.283203) * 10 ^ 6 < Real.log 197 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_45 : ((bClo 45 : ℕ) : ℝ) < Real.log (bLo 45) * 10 ^ 6 := by
  rw [show bLo 45 = 199 by decide]
  have hM : ((bClo 45 : ℕ) : ℝ) = ((5 : ℝ) + 0.293304) * 10 ^ 6 := by
    rw [show bClo 45 = 5293304 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.293304 < Real.log 199 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 199)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.293304)
      (by norm_num : (0.293304 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.293304) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.293304 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.293304)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.293304) * 10 ^ 6 < Real.log 199 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_46 : ((bClo 46 : ℕ) : ℝ) < Real.log (bLo 46) * 10 ^ 6 := by
  rw [show bLo 46 = 211 by decide]
  have hM : ((bClo 46 : ℕ) : ℝ) = ((5 : ℝ) + 0.351858) * 10 ^ 6 := by
    rw [show bClo 46 = 5351858 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.351858 < Real.log 211 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 211)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.351858)
      (by norm_num : (0.351858 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.351858) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.351858 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.351858)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.351858) * 10 ^ 6 < Real.log 211 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_47 : ((bClo 47 : ℕ) : ℝ) < Real.log (bLo 47) * 10 ^ 6 := by
  rw [show bLo 47 = 223 by decide]
  have hM : ((bClo 47 : ℕ) : ℝ) = ((5 : ℝ) + 0.407171) * 10 ^ 6 := by
    rw [show bClo 47 = 5407171 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.407171 < Real.log 223 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 223)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.407171)
      (by norm_num : (0.407171 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.407171) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.407171 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.407171)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.407171) * 10 ^ 6 < Real.log 223 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_48 : ((bClo 48 : ℕ) : ℝ) < Real.log (bLo 48) * 10 ^ 6 := by
  rw [show bLo 48 = 227 by decide]
  have hM : ((bClo 48 : ℕ) : ℝ) = ((5 : ℝ) + 0.424950) * 10 ^ 6 := by
    rw [show bClo 48 = 5424950 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.424950 < Real.log 227 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 227)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.424950)
      (by norm_num : (0.424950 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.424950) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.424950 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.424950)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.424950) * 10 ^ 6 < Real.log 227 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_49 : ((bClo 49 : ℕ) : ℝ) < Real.log (bLo 49) * 10 ^ 6 := by
  rw [show bLo 49 = 229 by decide]
  have hM : ((bClo 49 : ℕ) : ℝ) = ((5 : ℝ) + 0.433722) * 10 ^ 6 := by
    rw [show bClo 49 = 5433722 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.433722 < Real.log 229 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 229)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.433722)
      (by norm_num : (0.433722 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.433722) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.433722 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.433722)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.433722) * 10 ^ 6 < Real.log 229 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_50 : ((bClo 50 : ℕ) : ℝ) < Real.log (bLo 50) * 10 ^ 6 := by
  rw [show bLo 50 = 233 by decide]
  have hM : ((bClo 50 : ℕ) : ℝ) = ((5 : ℝ) + 0.451038) * 10 ^ 6 := by
    rw [show bClo 50 = 5451038 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.451038 < Real.log 233 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 233)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.451038)
      (by norm_num : (0.451038 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.451038) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.451038 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.451038)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.451038) * 10 ^ 6 < Real.log 233 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_51 : ((bClo 51 : ℕ) : ℝ) < Real.log (bLo 51) * 10 ^ 6 := by
  rw [show bLo 51 = 239 by decide]
  have hM : ((bClo 51 : ℕ) : ℝ) = ((5 : ℝ) + 0.476463) * 10 ^ 6 := by
    rw [show bClo 51 = 5476463 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.476463 < Real.log 239 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 239)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.476463)
      (by norm_num : (0.476463 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.476463) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.476463 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.476463)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.476463) * 10 ^ 6 < Real.log 239 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_52 : ((bClo 52 : ℕ) : ℝ) < Real.log (bLo 52) * 10 ^ 6 := by
  rw [show bLo 52 = 241 by decide]
  have hM : ((bClo 52 : ℕ) : ℝ) = ((5 : ℝ) + 0.484796) * 10 ^ 6 := by
    rw [show bClo 52 = 5484796 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.484796 < Real.log 241 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 241)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.484796)
      (by norm_num : (0.484796 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.484796) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.484796 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.484796)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.484796) * 10 ^ 6 < Real.log 241 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_53 : ((bClo 53 : ℕ) : ℝ) < Real.log (bLo 53) * 10 ^ 6 := by
  rw [show bLo 53 = 251 by decide]
  have hM : ((bClo 53 : ℕ) : ℝ) = ((5 : ℝ) + 0.525452) * 10 ^ 6 := by
    rw [show bClo 53 = 5525452 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.525452 < Real.log 251 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 251)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.525452)
      (by norm_num : (0.525452 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.525452) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.525452 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.525452)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.525452) * 10 ^ 6 < Real.log 251 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_54 : ((bClo 54 : ℕ) : ℝ) < Real.log (bLo 54) * 10 ^ 6 := by
  rw [show bLo 54 = 257 by decide]
  have hM : ((bClo 54 : ℕ) : ℝ) = ((5 : ℝ) + 0.549076) * 10 ^ 6 := by
    rw [show bClo 54 = 5549076 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.549076 < Real.log 257 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 257)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.549076)
      (by norm_num : (0.549076 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.549076) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.549076 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.549076)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.549076) * 10 ^ 6 < Real.log 257 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_55 : ((bClo 55 : ℕ) : ℝ) < Real.log (bLo 55) * 10 ^ 6 := by
  rw [show bLo 55 = 263 by decide]
  have hM : ((bClo 55 : ℕ) : ℝ) = ((5 : ℝ) + 0.572154) * 10 ^ 6 := by
    rw [show bClo 55 = 5572154 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.572154 < Real.log 263 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 263)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.572154)
      (by norm_num : (0.572154 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.572154) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.572154 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.572154)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.572154) * 10 ^ 6 < Real.log 263 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_56 : ((bClo 56 : ℕ) : ℝ) < Real.log (bLo 56) * 10 ^ 6 := by
  rw [show bLo 56 = 269 by decide]
  have hM : ((bClo 56 : ℕ) : ℝ) = ((5 : ℝ) + 0.594711) * 10 ^ 6 := by
    rw [show bClo 56 = 5594711 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.594711 < Real.log 269 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 269)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.594711)
      (by norm_num : (0.594711 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.594711) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.594711 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.594711)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.594711) * 10 ^ 6 < Real.log 269 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_57 : ((bClo 57 : ℕ) : ℝ) < Real.log (bLo 57) * 10 ^ 6 := by
  rw [show bLo 57 = 271 by decide]
  have hM : ((bClo 57 : ℕ) : ℝ) = ((5 : ℝ) + 0.602118) * 10 ^ 6 := by
    rw [show bClo 57 = 5602118 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.602118 < Real.log 271 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 271)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.602118)
      (by norm_num : (0.602118 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.602118) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.602118 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.602118)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.602118) * 10 ^ 6 < Real.log 271 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_58 : ((bClo 58 : ℕ) : ℝ) < Real.log (bLo 58) * 10 ^ 6 := by
  rw [show bLo 58 = 277 by decide]
  have hM : ((bClo 58 : ℕ) : ℝ) = ((5 : ℝ) + 0.624017) * 10 ^ 6 := by
    rw [show bClo 58 = 5624017 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.624017 < Real.log 277 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 277)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.624017)
      (by norm_num : (0.624017 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.624017) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.624017 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.624017)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.624017) * 10 ^ 6 < Real.log 277 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_59 : ((bClo 59 : ℕ) : ℝ) < Real.log (bLo 59) * 10 ^ 6 := by
  rw [show bLo 59 = 281 by decide]
  have hM : ((bClo 59 : ℕ) : ℝ) = ((5 : ℝ) + 0.638354) * 10 ^ 6 := by
    rw [show bClo 59 = 5638354 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.638354 < Real.log 281 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 281)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.638354)
      (by norm_num : (0.638354 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.638354) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.638354 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.638354)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.638354) * 10 ^ 6 < Real.log 281 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_60 : ((bClo 60 : ℕ) : ℝ) < Real.log (bLo 60) * 10 ^ 6 := by
  rw [show bLo 60 = 283 by decide]
  have hM : ((bClo 60 : ℕ) : ℝ) = ((5 : ℝ) + 0.645446) * 10 ^ 6 := by
    rw [show bClo 60 = 5645446 by decide]
    norm_num
  rw [hM]
  have hexp : (5 : ℝ) + 0.645446 < Real.log 283 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 283)]
    have hm : Real.exp (5 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5 := by
      rw [show (5 : ℝ) = (5 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 5
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 0.645446)
      (by norm_num : (0.645446 : ℝ) ≤ 1) (show (0 : ℕ) < 12 by norm_num)
    have s1 : Real.exp ((5 : ℝ) + 0.645446) ≤
        (2.7182818286 : ℝ) ^ 5 * Real.exp 0.645446 := by
      rw [Real.exp_add]
      exact mul_le_mul_of_nonneg_right hm (Real.exp_nonneg 0.645446)
    have s2 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ (2.7182818286 : ℝ) ^ 5)
    refine lt_of_le_of_lt (le_trans s1 s2) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  calc ((5 : ℝ) + 0.645446) * 10 ^ 6 < Real.log 283 * 10 ^ 6 :=
    mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 10 ^ 6)

lemma b_loglo_all (k : ℕ) (hk : k < 61) :
    ((bClo k : ℕ) : ℝ) < Real.log (bLo k) * 10 ^ 6 := by
  interval_cases k
  · exact b_loglo_0
  · exact b_loglo_1
  · exact b_loglo_2
  · exact b_loglo_3
  · exact b_loglo_4
  · exact b_loglo_5
  · exact b_loglo_6
  · exact b_loglo_7
  · exact b_loglo_8
  · exact b_loglo_9
  · exact b_loglo_10
  · exact b_loglo_11
  · exact b_loglo_12
  · exact b_loglo_13
  · exact b_loglo_14
  · exact b_loglo_15
  · exact b_loglo_16
  · exact b_loglo_17
  · exact b_loglo_18
  · exact b_loglo_19
  · exact b_loglo_20
  · exact b_loglo_21
  · exact b_loglo_22
  · exact b_loglo_23
  · exact b_loglo_24
  · exact b_loglo_25
  · exact b_loglo_26
  · exact b_loglo_27
  · exact b_loglo_28
  · exact b_loglo_29
  · exact b_loglo_30
  · exact b_loglo_31
  · exact b_loglo_32
  · exact b_loglo_33
  · exact b_loglo_34
  · exact b_loglo_35
  · exact b_loglo_36
  · exact b_loglo_37
  · exact b_loglo_38
  · exact b_loglo_39
  · exact b_loglo_40
  · exact b_loglo_41
  · exact b_loglo_42
  · exact b_loglo_43
  · exact b_loglo_44
  · exact b_loglo_45
  · exact b_loglo_46
  · exact b_loglo_47
  · exact b_loglo_48
  · exact b_loglo_49
  · exact b_loglo_50
  · exact b_loglo_51
  · exact b_loglo_52
  · exact b_loglo_53
  · exact b_loglo_54
  · exact b_loglo_55
  · exact b_loglo_56
  · exact b_loglo_57
  · exact b_loglo_58
  · exact b_loglo_59
  · exact b_loglo_60

lemma b_hmono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    Real.log a + 2 / Real.sqrt a ≤ Real.log b + 2 / Real.sqrt b := by
  have ha0 : (0:ℝ) < a := lt_of_lt_of_le (by norm_num) ha
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le ha0 hab
  have hsa : (0:ℝ) < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hsb : (0:ℝ) < Real.sqrt b := Real.sqrt_pos.mpr hb0
  set u : ℝ := Real.sqrt b / Real.sqrt a with hu
  have hu1 : (1:ℝ) ≤ u := by
    rw [hu, one_le_div hsa]
    exact Real.sqrt_le_sqrt hab
  have hune : u ≠ 0 := ne_of_gt (div_pos hsb hsa)
  have hlog1 : 1 - 1 / u ≤ Real.log u := by
    have h := Real.log_le_sub_one_of_pos
      (show (0:ℝ) < 1 / u by positivity)
    rw [one_div, Real.log_inv] at h
    rw [one_div]
    linarith
  have hb2 : b = a * u ^ 2 := by
    rw [hu, div_pow, Real.sq_sqrt hb0.le, Real.sq_sqrt ha0.le]
    field_simp
  have hlogb : Real.log b = Real.log a + 2 * Real.log u := by
    rw [hb2, Real.log_mul (ne_of_gt ha0) (by positivity), Real.log_pow]
    ring
  have hsrtb : Real.sqrt b = u * Real.sqrt a := by
    rw [hu]
    exact (div_mul_cancel₀ (Real.sqrt b) (ne_of_gt hsa)).symm
  have hkey : Real.log b + 2 / Real.sqrt b - (Real.log a + 2 / Real.sqrt a)
      = 2 * (Real.log u - (1 - 1 / u) / Real.sqrt a) := by
    rw [hlogb, hsrtb]
    field_simp
    ring
  rw [← sub_nonneg, hkey]
  have h2 : (0:ℝ) ≤ 1 - 1 / u := by
    have h3 : 1 / u ≤ 1 := by
      rw [div_le_one (div_pos hsb hsa)]
      linarith
    linarith
  have hsa1 : (1:ℝ) ≤ Real.sqrt a := by
    simpa using Real.sqrt_le_sqrt (by exact_mod_cast ha : (1:ℝ) ≤ a)
  have h3 : (1 - 1 / u) / Real.sqrt a ≤ 1 - 1 / u := by
    rw [div_le_iff₀ hsa]
    nlinarith
  have h4 : (1 - 1 / u) / Real.sqrt a ≤ Real.log u := le_trans h3 hlog1
  exact mul_nonneg (by norm_num) (sub_nonneg.mpr h4)

/-- Finisher: integer-certificate form → (4.10) bound. -/
lemma b_finish (x a c A : ℝ) (S : ℕ) (Q : ℝ)
    (hQ : Q < A * (c + 2 / (S:ℝ)))
    (hsqlo : Real.sqrt a < (S:ℝ)) (hloglo : c < Real.log a)
    (ha1 : 1 ≤ a) (hax : a ≤ x)
    (hA0 : 0 < A) (hA : A ≤ Real.exp Real.eulerMascheroniConstant) :
    Q < Real.exp Real.eulerMascheroniConstant * Real.log x +
      2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
  have hmono := b_hmono ha1 hax
  have ha0 : (0:ℝ) < a := lt_of_lt_of_le (by norm_num) ha1
  have hla : (0:ℝ) ≤ Real.log a := by
    have h : Real.log 1 ≤ Real.log a := Real.log_le_log (by norm_num) (by linarith)
    simpa using h
  -- A·(c + 2/S) < A·(log a + 2/√a)
  have h1 : A * (c + 2 / (S:ℝ)) < A * (Real.log a + 2 / Real.sqrt a) := by
    have hSpos : (0:ℝ) < (S:ℝ) := lt_of_le_of_lt (Real.sqrt_nonneg a) hsqlo
    have hrecip : (1:ℝ) / (S:ℝ) < 1 / Real.sqrt a :=
      (one_div_lt_one_div hSpos (Real.sqrt_pos.mpr ha0)).mpr hsqlo
    have h2 : (2:ℝ) / (S:ℝ) < 2 / Real.sqrt a := by
      rw [show (2:ℝ) / (S:ℝ) = 2 * (1 / (S:ℝ)) from by ring,
          show (2:ℝ) / Real.sqrt a = 2 * (1 / Real.sqrt a) from by ring]
      exact mul_lt_mul_of_pos_left hrecip (by norm_num)
    have hc2 : A * c < A * Real.log a := mul_lt_mul_of_pos_left hloglo hA0
    have hd2 : A * (2 / (S:ℝ)) < A * (2 / Real.sqrt a) := mul_lt_mul_of_pos_left h2 hA0
    have hsum := add_lt_add hc2 hd2
    rwa [mul_add, mul_add]
  -- A·(log a + 2/√a) ≤ e^γ·(log a + 2/√a)
  have h2 : A * (Real.log a + 2 / Real.sqrt a) ≤
      Real.exp Real.eulerMascheroniConstant * (Real.log a + 2 / Real.sqrt a) :=
    mul_le_mul hA le_rfl (by positivity) (Real.exp_nonneg _)
  -- ≤ e^γ·(log x + 2/√x)
  have h3 : Real.exp Real.eulerMascheroniConstant * (Real.log a + 2 / Real.sqrt a) ≤
      Real.exp Real.eulerMascheroniConstant * (Real.log x + 2 / Real.sqrt x) :=
    mul_le_mul_of_nonneg_left hmono (Real.exp_nonneg _)
  -- RHS rearrangement
  have hrew : Real.exp Real.eulerMascheroniConstant * (Real.log x + 2 / Real.sqrt x) =
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
    ring
  exact hQ.trans_le (h1.le.trans (h2.trans (h3.trans hrew.le)))


theorem b_sq_lt (lo S : ℕ) (h : lo < S * S) :
    Real.sqrt ((lo : ℕ) : ℝ) < ((S : ℕ) : ℝ) := by
  have hS0 : (0:ℝ) < ((S : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos S with h0 | h0
    · rw [h0] at h
      omega
    · exact_mod_cast h0
  rw [Real.sqrt_lt' hS0, pow_two]
  exact_mod_cast h

/-! ### The small range 0 < x < 2: the product is empty -/
lemma b_small2 (x : ℝ) (hx : 0 < x) :
    (2 : ℝ) ≤ Real.log x + 2 / Real.sqrt x := by
  have hlogsq : Real.log x = 2 * Real.log (Real.sqrt x) := by
    have h1 : Real.log (Real.sqrt x ^ 2) = 2 * Real.log (Real.sqrt x) :=
      Real.log_pow _ _
    rwa [Real.sq_sqrt hx.le] at h1
  have hlogu : 1 - 1 / Real.sqrt x ≤ Real.log (Real.sqrt x) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / Real.sqrt x by positivity)
    rw [one_div, Real.log_inv] at h
    rw [one_div]
    linarith
  rw [one_div] at hlogu
  rw [hlogsq, show (2 : ℝ) / Real.sqrt x = 2 * ((Real.sqrt x)⁻¹) from by ring]
  linarith

lemma b_small_fin (x : ℝ) (hx : 0 < x) :
    (1 : ℝ) < Real.exp Real.eulerMascheroniConstant * Real.log x +
      2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
  have hf : (2 : ℝ) ≤ Real.log x + 2 / Real.sqrt x := b_small2 x hx
  have hE2 : (2 : ℝ) * ((1781071 : ℝ) / 10 ^ 6) ≤
      2 * Real.exp Real.eulerMascheroniConstant :=
    mul_le_mul_of_nonneg_left b_exp_gamma_ge (by norm_num)
  have hA2 : (1 : ℝ) < (2 : ℝ) * ((1781071 : ℝ) / 10 ^ 6) := by norm_num
  have h3 : Real.exp Real.eulerMascheroniConstant * 2 ≤
      Real.exp Real.eulerMascheroniConstant * (Real.log x + 2 / Real.sqrt x) :=
    mul_le_mul_of_nonneg_left hf (Real.exp_nonneg _)
  have hrew : Real.exp Real.eulerMascheroniConstant * (Real.log x + 2 / Real.sqrt x) =
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
    ring
  rw [hrew] at h3
  linarith

/-! ### Assembly at a checkpoint -/
lemma b_assemble (k : ℕ) (hk : k < 61) (x : ℝ) (hlo : ((bLo k : ℕ) : ℝ) ≤ x) :
    ∏ p ∈ Nat.primesLE (bPtab k), (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
  rw [b_prod_id k hk]
  have hpd0 : (0 : ℝ) < ((bPden k : ℕ) : ℝ) := by
    have h1 : (0 : ℕ) < bPden k := b_pden_pos k hk
    exact_mod_cast h1
  have hSpos : (0 : ℝ) < ((bSq k : ℕ) : ℝ) := by
    have h1 : (0 : ℕ) < bSq k := b_sq_pos k hk
    exact_mod_cast h1
  have hck : ((bPnum k : ℕ) : ℝ) / ((bPden k : ℕ) : ℝ) <
      (1781071 : ℝ) / 10 ^ 6 * (((bClo k : ℕ) : ℝ) / 10 ^ 6 + 2 / ((bSq k : ℕ) : ℝ)) := by
    have h0 : bPnum k * (10 ^ 6 * (10 ^ 6 * bSq k)) <
        1781071 * (bSq k * bClo k + 2 * 10 ^ 6) * bPden k := by
      interval_cases k <;> decide
    rw [div_lt_iff₀ hpd0]
    have hident : (1781071 : ℝ) / 10 ^ 6 *
        (((bClo k : ℕ) : ℝ) / 10 ^ 6 + 2 / ((bSq k : ℕ) : ℝ)) * ((bPden k : ℕ) : ℝ) =
        1781071 * (((bSq k : ℕ) : ℝ) * ((bClo k : ℕ) : ℝ) + 2 * 10 ^ 6) *
          ((bPden k : ℕ) : ℝ) / (10 ^ 6 * (10 ^ 6 * ((bSq k : ℕ) : ℝ))) := by
      have hne : ((bSq k : ℕ) : ℝ) ≠ 0 := ne_of_gt hSpos
      field_simp
    have hT : (0 : ℝ) < 10 ^ 6 * (10 ^ 6 * ((bSq k : ℕ) : ℝ)) :=
      mul_pos (by norm_num : (0 : ℝ) < 10 ^ 6)
        (mul_pos (by norm_num : (0 : ℝ) < 10 ^ 6) hSpos)
    rw [hident, lt_div_iff₀ hT]
    exact_mod_cast h0
  have hloglo : ((bClo k : ℕ) : ℝ) / 10 ^ 6 < Real.log ((bLo k : ℕ) : ℝ) := by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 6)]
    exact b_loglo_all k hk
  have hsqlo := b_sq_lt (bLo k) (bSq k) (b_sqlo_all k hk)
  have ha1 : (1 : ℝ) ≤ ((bLo k : ℕ) : ℝ) := by exact_mod_cast (b_lo_pos k hk)
  exact b_finish x _ _ ((1781071 : ℝ) / 10 ^ 6) (bSq k) _ hck hsqlo hloglo ha1 hlo
    (by norm_num : (0 : ℝ) < 1781071 / 10 ^ 6) b_exp_gamma_ge

/-! ### Main theorem -/
theorem solution (x : ℝ) (hx : 0 < x) (hx' : x < 286) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
  rcases lt_or_ge x 2 with hx2 | hx2
  · -- 0 < x < 2: the product is empty
    have hx0 : (0 : ℝ) ≤ x := le_of_lt hx
    have h1 : ((⌊x⌋₊ : ℕ) : ℝ) < 2 := lt_of_le_of_lt (Nat.floor_le hx0) hx2
    have hfl : ⌊x⌋₊ < 2 := by exact_mod_cast h1
    interval_cases ⌊x⌋₊
    · rw [show Nat.primesLE 0 = (∅ : Finset ℕ) by decide, Finset.prod_empty]
      exact b_small_fin x hx
    · rw [show Nat.primesLE 1 = (∅ : Finset ℕ) by decide, Finset.prod_empty]
      exact b_small_fin x hx
  · -- 2 ≤ x < 286
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have hn2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx2
    have hnx : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
    have hnX : ⌊x⌋₊ ≤ 285 := by
      have h1 : ((⌊x⌋₊ : ℕ) : ℝ) < 286 := lt_of_le_of_lt hnx hx'
      have h2 : (⌊x⌋₊ : ℕ) < 286 := by exact_mod_cast h1
      omega
    have hne : (Nat.primesLE ⌊x⌋₊).Nonempty := by
      refine ⟨2, ?_⟩
      exact Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_two⟩
    set q := (Nat.primesLE ⌊x⌋₊).max' hne with hqdef
    have hqmem : q ∈ Nat.primesLE ⌊x⌋₊ := Finset.max'_mem _ hne
    have hqpr : q.Prime := (Nat.mem_primesLE.mp hqmem).2
    have hqle : q ≤ ⌊x⌋₊ := (Nat.mem_primesLE.mp hqmem).1
    have h2mem : 2 ∈ Nat.primesLE ⌊x⌋₊ :=
      Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_two⟩
    have hq2 : 2 ≤ q := Finset.le_max' _ _ h2mem
    have hqL : q ≤ 283 := by
      by_contra hcon
      have h1 : 284 ≤ q := by omega
      have h2 : q ≤ 285 := by omega
      exact b_no_prime_284 q h1 h2 hqpr
    obtain ⟨k, hklt, hktab⟩ := b_prime_in_table q hq2 hqL hqpr
    have hsub : Nat.primesLE ⌊x⌋₊ = Nat.primesLE q := by
      refine subset_antisymm ?_ ?_
      · intro p hp
        exact Nat.mem_primesLE.mpr
          ⟨Finset.le_max' _ _ hp, (Nat.mem_primesLE.mp hp).2⟩
      · intro p hp
        exact Nat.primesLE_mono hqle hp
    rw [hsub, ← hktab]
    refine b_assemble k hklt x ?_
    have hbLo : bLo k = bPtab k := by interval_cases k <;> decide
    rw [hbLo, hktab]
    exact le_trans (Nat.cast_le.mpr hqle) hnx

end TaoFivePrimes

open TaoFivePrimes

/-- Root re-export for the verification harness. -/
theorem solution (x : ℝ) (hx : 0 < x) (hx' : x < 286) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x :=
  TaoFivePrimes.solution x hx hx'

#print axioms solution
