-- Prove2me | solution 2 for TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid_lower
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T13:33:51.075771+00:00
-- url     : https://prove2.me/submissions/158ea9d0-167a-4e6d-b9b3-e6d8486afe05

import Mathlib
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic_finite
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert001
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert002
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert003
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert004
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert005
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert006
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert007
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert008
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert009
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert010
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert011
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert012
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert013
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert014
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert015
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert016
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert017
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert018
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert019
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert020
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert021
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert022
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert023
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert024
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert025
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert026
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert027
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert028
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert029
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert030
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert031
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert032
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert033
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert034
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert035
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert036
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert037
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert038
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert039
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert040
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert041
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert042
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert043
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert044
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert045
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert046
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert047
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert048
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert049
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert050
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert051
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert052
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert053
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert054
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert055
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert056
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert057
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert058
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert059
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert060
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert061
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert062
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert063
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert064
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert065
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert066
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert067
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert068
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert069
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert070
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert071
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert072
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert073
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert074
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert075
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert076
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert077
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert078
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert079
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert080
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert081
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert082
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert083
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert084
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert085
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert086
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert087
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert088
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert089
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert090
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert091
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert092
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert093
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert094
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert095
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert096
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert097
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert098
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert099
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert100
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert101
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert102
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert103
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert104
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert105
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert106
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert107
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert108
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert109
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert110
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert111
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert112
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert113
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert114
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert115
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert116
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert117
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert118
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert119
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert120
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert121
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert122
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert123
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert124
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert125
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert126
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert127
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert128
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert129
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert130
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert131
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert132
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert133
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert134
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert135
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert136
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert137
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert138
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert139
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert140
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert141
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert142
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert143
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert144
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert145
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert146
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert147
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert148
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert149
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert150
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_cert151

/-! Reduction of `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid_lower` (fa58620e) to
* `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_finite` (7c1e7cb4, Proved) on `[1420, 10 ^ 8]`,
* `TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large` (f48a0c89, Proved) at `t = 10 ^ 8`, which gives the first carry
  `C_0 / 2 ^ 40 = 99980000 = 10 ^ 8 - 2 √(10 ^ 8) < θ (10 ^ 8)`,
* the 151 certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_certNNN`: carry `C_k / 2 ^ 40 ≤ θ a_k` gives
  `(n + 1) - 10 √(n + 1) ≤ θ n` on `[a_k, b_k]` and the next carry.
For `10 ^ 8 < t ≤ 10 ^ 9` with `n = ⌊t⌋₊`: `θ t = θ n ≥ (n + 1) - 10 √(n + 1) ≥ t - 10 √t`
(monotone from 25 on) `> t - t / (2 log t)` since `20 log t < √t` (`glue_log`). -/

namespace TFPMidLower

/-- `y ↦ y - 10 √y` is monotone from `25` on -/
theorem sqrt_mono10 {t y : ℝ} (ht : 25 ≤ t) (hty : t ≤ y) :
    t - 10 * √t ≤ y - 10 * √y := by
  have hs : √t ≤ √y := Real.sqrt_le_sqrt hty
  have h5 : (5 : ℝ) ≤ √t := by
    rw [show (5 : ℝ) = √25 by
      rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt ht
  have et := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ t)
  have ey := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ y)
  nlinarith [mul_nonneg (sub_nonneg.2 hs) (by linarith : (0 : ℝ) ≤ √y + √t - 10)]

/-- the glue: `20 log t < √t` for `t ≥ 10 ^ 8` (via `log u ≤ u - 1` at `u = t ^ (1/4)`) -/
theorem glue_log (t : ℝ) (ht : 100000000 ≤ t) : 20 * Real.log t < √t := by
  have hs0 : 0 ≤ √t := Real.sqrt_nonneg _
  have hu0 : 0 ≤ √(√t) := Real.sqrt_nonneg _
  have hts : (√t) ^ 2 = t := Real.sq_sqrt (by linarith)
  have hsu : (√(√t)) ^ 2 = √t := Real.sq_sqrt hs0
  have hs1 : (10000 : ℝ) ≤ √t := by
    rw [show (10000 : ℝ) = √100000000 by
      rw [show (100000000 : ℝ) = 10000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt ht
  have hu1 : (100 : ℝ) ≤ √(√t) := by
    rw [show (100 : ℝ) = √10000 by
      rw [show (10000 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hs1
  have hlog : Real.log t = 4 * Real.log (√(√t)) := by
    conv_lhs => rw [← hts, ← hsu]
    rw [← pow_mul, Real.log_pow]
    norm_num
  have hlu : Real.log (√(√t)) ≤ √(√t) - 1 := Real.log_le_sub_one_of_pos (by linarith)
  rw [hlog]
  nlinarith [hlu, hsu, hu1, hu0]

/-- `θ t = θ ⌊t⌋₊` -/
theorem theta_floor (t : ℝ) : Chebyshev.theta t = Chebyshev.theta ((⌊t⌋₊ : ℕ) : ℝ) := by
  rw [Chebyshev.theta_eq_log_primorial, Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]

end TFPMidLower

namespace TFPMidLower

set_option maxHeartbeats 4000000 in
theorem chain_key : ∀ n : ℕ, 100000000 ≤ n → n ≤ 1000000000 →
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) := by
  have hb0 : (109929172545044480000 : Real) / 2 ^ 40 <= Chebyshev.theta (100000000 : Real) := by
    have hs : Real.sqrt (100000000 : ℝ) = 10000 := by
      rw [show (100000000 : ℝ) = 10000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have H := TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large 100000000 (by norm_num) (by norm_num)
    rw [hs] at H
    have hC : (109929172545044480000 : ℝ) / 2 ^ 40 = 99980000 := by norm_num
    rw [hC]
    linarith
  have hb1 : (115985490414503642521 : Real) / 2 ^ 40 <= Chebyshev.theta (105505290 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert001 hb0 100000000 le_rfl (by norm_num)).2
  have hb2 : (122058970791088291864 : Real) / 2 ^ 40 <= Chebyshev.theta (111026058 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert002 hb1 105505290 le_rfl (by norm_num)).2
  have hb3 : (128148815562481517540 : Real) / 2 ^ 40 <= Chebyshev.theta (116568182 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert003 hb2 111026058 le_rfl (by norm_num)).2
  have hb4 : (134254294163458731240 : Real) / 2 ^ 40 <= Chebyshev.theta (122125308 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert004 hb3 116568182 le_rfl (by norm_num)).2
  have hb5 : (140374725612029200054 : Real) / 2 ^ 40 <= Chebyshev.theta (127690208 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert005 hb4 122125308 le_rfl (by norm_num)).2
  have hb6 : (146509482822057092842 : Real) / 2 ^ 40 <= Chebyshev.theta (133269860 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert006 hb5 127690208 le_rfl (by norm_num)).2
  have hb7 : (152658009984549557155 : Real) / 2 ^ 40 <= Chebyshev.theta (138864182 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert007 hb6 133269860 le_rfl (by norm_num)).2
  have hb8 : (158819777702852284624 : Real) / 2 ^ 40 <= Chebyshev.theta (144462408 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert008 hb7 138864182 le_rfl (by norm_num)).2
  have hb9 : (164994290069456348378 : Real) / 2 ^ 40 <= Chebyshev.theta (150081180 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert009 hb8 144462408 le_rfl (by norm_num)).2
  have hb10 : (171181110267650324692 : Real) / 2 ^ 40 <= Chebyshev.theta (155710602 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert010 hb9 150081180 le_rfl (by norm_num)).2
  have hb11 : (177379807665904808287 : Real) / 2 ^ 40 <= Chebyshev.theta (161348330 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert011 hb10 155710602 le_rfl (by norm_num)).2
  have hb12 : (183589991146815588247 : Real) / 2 ^ 40 <= Chebyshev.theta (166998614 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert012 hb11 161348330 le_rfl (by norm_num)).2
  have hb13 : (189811285027837642575 : Real) / 2 ^ 40 <= Chebyshev.theta (172650912 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert013 hb12 166998614 le_rfl (by norm_num)).2
  have hb14 : (196043343088932618867 : Real) / 2 ^ 40 <= Chebyshev.theta (178316108 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert014 hb13 172650912 le_rfl (by norm_num)).2
  have hb15 : (202285846417560768081 : Real) / 2 ^ 40 <= Chebyshev.theta (183999360 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert015 hb14 178316108 le_rfl (by norm_num)).2
  have hb16 : (208538489905179355987 : Real) / 2 ^ 40 <= Chebyshev.theta (189683538 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert016 hb15 183999360 le_rfl (by norm_num)).2
  have hb17 : (214800989614683467040 : Real) / 2 ^ 40 <= Chebyshev.theta (195379782 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert017 hb16 189683538 le_rfl (by norm_num)).2
  have hb18 : (221073073202695746290 : Real) / 2 ^ 40 <= Chebyshev.theta (201089412 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert018 hb17 195379782 le_rfl (by norm_num)).2
  have hb19 : (227354479870817296173 : Real) / 2 ^ 40 <= Chebyshev.theta (206801942 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert019 hb18 201089412 le_rfl (by norm_num)).2
  have hb20 : (233644962155203533963 : Real) / 2 ^ 40 <= Chebyshev.theta (212522868 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert020 hb19 206801942 le_rfl (by norm_num)).2
  have hb21 : (239944291182350139519 : Real) / 2 ^ 40 <= Chebyshev.theta (218252720 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert021 hb20 212522868 le_rfl (by norm_num)).2
  have hb22 : (246252248086832042087 : Real) / 2 ^ 40 <= Chebyshev.theta (223991180 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert022 hb21 218252720 le_rfl (by norm_num)).2
  have hb23 : (252568618446463043437 : Real) / 2 ^ 40 <= Chebyshev.theta (229737948 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert023 hb22 223991180 le_rfl (by norm_num)).2
  have hb24 : (258893205654435319143 : Real) / 2 ^ 40 <= Chebyshev.theta (235488864 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert024 hb23 229737948 le_rfl (by norm_num)).2
  have hb25 : (265225813164412260592 : Real) / 2 ^ 40 <= Chebyshev.theta (241240752 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert025 hb24 235488864 le_rfl (by norm_num)).2
  have hb26 : (271566262903548526280 : Real) / 2 ^ 40 <= Chebyshev.theta (247010948 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert026 hb25 241240752 le_rfl (by norm_num)).2
  have hb27 : (277914381258425326537 : Real) / 2 ^ 40 <= Chebyshev.theta (252784854 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert027 hb26 247010948 le_rfl (by norm_num)).2
  have hb28 : (284270002542376905498 : Real) / 2 ^ 40 <= Chebyshev.theta (258564542 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert028 hb27 252784854 le_rfl (by norm_num)).2
  have hb29 : (290632967016128098646 : Real) / 2 ^ 40 <= Chebyshev.theta (264352070 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert029 hb28 258564542 le_rfl (by norm_num)).2
  have hb30 : (297003124359028185652 : Real) / 2 ^ 40 <= Chebyshev.theta (270147678 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert030 hb29 264352070 le_rfl (by norm_num)).2
  have hb31 : (303380331745508031739 : Real) / 2 ^ 40 <= Chebyshev.theta (275946488 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert031 hb30 270147678 le_rfl (by norm_num)).2
  have hb32 : (309764439977448747312 : Real) / 2 ^ 40 <= Chebyshev.theta (281750150 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert032 hb31 275946488 le_rfl (by norm_num)).2
  have hb33 : (316155320080910923937 : Real) / 2 ^ 40 <= Chebyshev.theta (287568014 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert033 hb32 281750150 le_rfl (by norm_num)).2
  have hb34 : (322552841604596834596 : Real) / 2 ^ 40 <= Chebyshev.theta (293386730 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert034 hb33 287568014 le_rfl (by norm_num)).2
  have hb35 : (328956876406464935138 : Real) / 2 ^ 40 <= Chebyshev.theta (299212862 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert035 hb34 293386730 le_rfl (by norm_num)).2
  have hb36 : (335367306052801765654 : Real) / 2 ^ 40 <= Chebyshev.theta (305039744 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert036 hb35 299212862 le_rfl (by norm_num)).2
  have hb37 : (341784010687424805078 : Real) / 2 ^ 40 <= Chebyshev.theta (310872278 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert037 hb36 305039744 le_rfl (by norm_num)).2
  have hb38 : (348206880615548571972 : Real) / 2 ^ 40 <= Chebyshev.theta (316715072 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert038 hb37 310872278 le_rfl (by norm_num)).2
  have hb39 : (354635812711236209502 : Real) / 2 ^ 40 <= Chebyshev.theta (322566954 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert039 hb38 316715072 le_rfl (by norm_num)).2
  have hb40 : (361070700599478951623 : Real) / 2 ^ 40 <= Chebyshev.theta (328418628 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert040 hb39 322566954 le_rfl (by norm_num)).2
  have hb41 : (367511443486110023181 : Real) / 2 ^ 40 <= Chebyshev.theta (334280034 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert041 hb40 328418628 le_rfl (by norm_num)).2
  have hb42 : (373957943387292629365 : Real) / 2 ^ 40 <= Chebyshev.theta (340142490 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert042 hb41 334280034 le_rfl (by norm_num)).2
  have hb43 : (380410102409431635883 : Real) / 2 ^ 40 <= Chebyshev.theta (346007568 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert043 hb42 340142490 le_rfl (by norm_num)).2
  have hb44 : (386867832720225827742 : Real) / 2 ^ 40 <= Chebyshev.theta (351884064 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert044 hb43 346007568 le_rfl (by norm_num)).2
  have hb45 : (393331045319442231038 : Real) / 2 ^ 40 <= Chebyshev.theta (357761984 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert045 hb44 351884064 le_rfl (by norm_num)).2
  have hb46 : (399799657437801949047 : Real) / 2 ^ 40 <= Chebyshev.theta (363647564 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert046 hb45 357761984 le_rfl (by norm_num)).2
  have hb47 : (406273582622677813668 : Real) / 2 ^ 40 <= Chebyshev.theta (369536114 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert047 hb46 363647564 le_rfl (by norm_num)).2
  have hb48 : (412752744404589158745 : Real) / 2 ^ 40 <= Chebyshev.theta (375427754 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert048 hb47 369536114 le_rfl (by norm_num)).2
  have hb49 : (419237053352189757959 : Real) / 2 ^ 40 <= Chebyshev.theta (381314304 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert049 hb48 375427754 le_rfl (by norm_num)).2
  have hb50 : (425726438872312599762 : Real) / 2 ^ 40 <= Chebyshev.theta (387220200 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert050 hb49 381314304 le_rfl (by norm_num)).2
  have hb51 : (432220832279890113048 : Real) / 2 ^ 40 <= Chebyshev.theta (393128004 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert051 hb50 387220200 le_rfl (by norm_num)).2
  have hb52 : (438720162594367374519 : Real) / 2 ^ 40 <= Chebyshev.theta (399042702 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert052 hb51 393128004 le_rfl (by norm_num)).2
  have hb53 : (445224358338395164829 : Real) / 2 ^ 40 <= Chebyshev.theta (404956580 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert053 hb52 399042702 le_rfl (by norm_num)).2
  have hb54 : (451733351471436040779 : Real) / 2 ^ 40 <= Chebyshev.theta (410875274 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert054 hb53 404956580 le_rfl (by norm_num)).2
  have hb55 : (458247076737233400394 : Real) / 2 ^ 40 <= Chebyshev.theta (416799212 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert055 hb54 410875274 le_rfl (by norm_num)).2
  have hb56 : (464765471319962846559 : Real) / 2 ^ 40 <= Chebyshev.theta (422732928 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert056 hb55 416799212 le_rfl (by norm_num)).2
  have hb57 : (471288470584453680001 : Real) / 2 ^ 40 <= Chebyshev.theta (428659842 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert057 hb56 422732928 le_rfl (by norm_num)).2
  have hb58 : (477816016178587556865 : Real) / 2 ^ 40 <= Chebyshev.theta (434599368 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert058 hb57 428659842 le_rfl (by norm_num)).2
  have hb59 : (484348049404722909416 : Real) / 2 ^ 40 <= Chebyshev.theta (440543372 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert059 hb58 434599368 le_rfl (by norm_num)).2
  have hb60 : (490884508741119358897 : Real) / 2 ^ 40 <= Chebyshev.theta (446484090 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert060 hb59 440543372 le_rfl (by norm_num)).2
  have hb61 : (497425340650655862257 : Real) / 2 ^ 40 <= Chebyshev.theta (452433602 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert061 hb60 446484090 le_rfl (by norm_num)).2
  have hb62 : (503970490490239355578 : Real) / 2 ^ 40 <= Chebyshev.theta (458385602 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert062 hb61 452433602 le_rfl (by norm_num)).2
  have hb63 : (510519906148567031997 : Real) / 2 ^ 40 <= Chebyshev.theta (464340914 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert063 hb62 458385602 le_rfl (by norm_num)).2
  have hb64 : (517073532751824881116 : Real) / 2 ^ 40 <= Chebyshev.theta (470299910 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert064 hb63 464340914 le_rfl (by norm_num)).2
  have hb65 : (523631323108648214468 : Real) / 2 ^ 40 <= Chebyshev.theta (476271710 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert065 hb64 470299910 le_rfl (by norm_num)).2
  have hb66 : (530193224740441363615 : Real) / 2 ^ 40 <= Chebyshev.theta (482231700 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert066 hb65 476271710 le_rfl (by norm_num)).2
  have hb67 : (536759189634361431455 : Real) / 2 ^ 40 <= Chebyshev.theta (488204660 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert067 hb66 482231700 le_rfl (by norm_num)).2
  have hb68 : (543329172451137520856 : Real) / 2 ^ 40 <= Chebyshev.theta (494180658 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert068 hb67 488204660 le_rfl (by norm_num)).2
  have hb69 : (549903124636662836886 : Real) / 2 ^ 40 <= Chebyshev.theta (500158950 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert069 hb68 494180658 le_rfl (by norm_num)).2
  have hb70 : (556481007097319716668 : Real) / 2 ^ 40 <= Chebyshev.theta (506149782 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert070 hb69 500158950 le_rfl (by norm_num)).2
  have hb71 : (563062775463423434123 : Real) / 2 ^ 40 <= Chebyshev.theta (512140712 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert071 hb70 506149782 le_rfl (by norm_num)).2
  have hb72 : (569648385879015499646 : Real) / 2 ^ 40 <= Chebyshev.theta (518131040 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert072 hb71 512140712 le_rfl (by norm_num)).2
  have hb73 : (576237791361682533557 : Real) / 2 ^ 40 <= Chebyshev.theta (524125040 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert073 hb72 518131040 le_rfl (by norm_num)).2
  have hb74 : (582830951760025759483 : Real) / 2 ^ 40 <= Chebyshev.theta (530117382 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert074 hb73 524125040 le_rfl (by norm_num)).2
  have hb75 : (589427826052419089208 : Real) / 2 ^ 40 <= Chebyshev.theta (536118548 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert075 hb74 530117382 le_rfl (by norm_num)).2
  have hb76 : (596028373735986433537 : Real) / 2 ^ 40 <= Chebyshev.theta (542123004 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert076 hb75 536118548 le_rfl (by norm_num)).2
  have hb77 : (602632561039693512653 : Real) / 2 ^ 40 <= Chebyshev.theta (548130750 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert077 hb76 542123004 le_rfl (by norm_num)).2
  have hb78 : (609240343544548301429 : Real) / 2 ^ 40 <= Chebyshev.theta (554131368 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert078 hb77 548130750 le_rfl (by norm_num)).2
  have hb79 : (615851686523513114393 : Real) / 2 ^ 40 <= Chebyshev.theta (560150714 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert079 hb78 554131368 le_rfl (by norm_num)).2
  have hb80 : (622466555512460505892 : Real) / 2 ^ 40 <= Chebyshev.theta (566166204 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert080 hb79 560150714 le_rfl (by norm_num)).2
  have hb81 : (629084914842862476593 : Real) / 2 ^ 40 <= Chebyshev.theta (572187692 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert081 hb80 566166204 le_rfl (by norm_num)).2
  have hb82 : (635706728842841852135 : Real) / 2 ^ 40 <= Chebyshev.theta (578210628 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert082 hb81 572187692 le_rfl (by norm_num)).2
  have hb83 : (642331962622553827553 : Real) / 2 ^ 40 <= Chebyshev.theta (584231732 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert083 hb82 578210628 le_rfl (by norm_num)).2
  have hb84 : (648960584159791684288 : Real) / 2 ^ 40 <= Chebyshev.theta (590261978 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert084 hb83 584231732 le_rfl (by norm_num)).2
  have hb85 : (655592556568974430329 : Real) / 2 ^ 40 <= Chebyshev.theta (596283782 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert085 hb84 590261978 le_rfl (by norm_num)).2
  have hb86 : (662227848773851227682 : Real) / 2 ^ 40 <= Chebyshev.theta (602321844 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert086 hb85 596283782 le_rfl (by norm_num)).2
  have hb87 : (668866429311341522443 : Real) / 2 ^ 40 <= Chebyshev.theta (608354970 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert087 hb86 602321844 le_rfl (by norm_num)).2
  have hb88 : (675508269938782616888 : Real) / 2 ^ 40 <= Chebyshev.theta (614398092 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert088 hb87 608354970 le_rfl (by norm_num)).2
  have hb89 : (682153340610911386285 : Real) / 2 ^ 40 <= Chebyshev.theta (620446704 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert089 hb88 614398092 le_rfl (by norm_num)).2
  have hb90 : (688801611561934755589 : Real) / 2 ^ 40 <= Chebyshev.theta (626495240 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert090 hb89 620446704 le_rfl (by norm_num)).2
  have hb91 : (695453050243453396043 : Real) / 2 ^ 40 <= Chebyshev.theta (632540862 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert091 hb90 626495240 le_rfl (by norm_num)).2
  have hb92 : (702107630830536850695 : Real) / 2 ^ 40 <= Chebyshev.theta (638593340 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert092 hb91 632540862 le_rfl (by norm_num)).2
  have hb93 : (708765323229731087442 : Real) / 2 ^ 40 <= Chebyshev.theta (644655242 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert093 hb92 638593340 le_rfl (by norm_num)).2
  have hb94 : (715426101088796647459 : Real) / 2 ^ 40 <= Chebyshev.theta (650706242 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert094 hb93 644655242 le_rfl (by norm_num)).2
  have hb95 : (722089935156783083852 : Real) / 2 ^ 40 <= Chebyshev.theta (656768864 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert095 hb94 650706242 le_rfl (by norm_num)).2
  have hb96 : (728756798384822531651 : Real) / 2 ^ 40 <= Chebyshev.theta (662826500 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert096 hb95 656768864 le_rfl (by norm_num)).2
  have hb97 : (735426664859975656738 : Real) / 2 ^ 40 <= Chebyshev.theta (668897498 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert097 hb96 662826500 le_rfl (by norm_num)).2
  have hb98 : (742099510508744477332 : Real) / 2 ^ 40 <= Chebyshev.theta (674966234 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert098 hb97 668897498 le_rfl (by norm_num)).2
  have hb99 : (748775310892756998710 : Real) / 2 ^ 40 <= Chebyshev.theta (681044628 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert099 hb98 674966234 le_rfl (by norm_num)).2
  have hb100 : (755454040236762193524 : Real) / 2 ^ 40 <= Chebyshev.theta (687113858 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert100 hb99 681044628 le_rfl (by norm_num)).2
  have hb101 : (762135668912283162940 : Real) / 2 ^ 40 <= Chebyshev.theta (693190904 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert101 hb100 687113858 le_rfl (by norm_num)).2
  have hb102 : (768820175898222834044 : Real) / 2 ^ 40 <= Chebyshev.theta (699268608 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert102 hb101 693190904 le_rfl (by norm_num)).2
  have hb103 : (775507537898463962466 : Real) / 2 ^ 40 <= Chebyshev.theta (705351204 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert103 hb102 699268608 le_rfl (by norm_num)).2
  have hb104 : (782197731126421227288 : Real) / 2 ^ 40 <= Chebyshev.theta (711434862 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert104 hb103 705351204 le_rfl (by norm_num)).2
  have hb105 : (788890733729285756594 : Real) / 2 ^ 40 <= Chebyshev.theta (717526298 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert105 hb104 711434862 le_rfl (by norm_num)).2
  have hb106 : (795586522840378970913 : Real) / 2 ^ 40 <= Chebyshev.theta (723611424 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert106 hb105 717526298 le_rfl (by norm_num)).2
  have hb107 : (802285074278471091679 : Real) / 2 ^ 40 <= Chebyshev.theta (729708912 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert107 hb106 723611424 le_rfl (by norm_num)).2
  have hb108 : (808986370222787851985 : Real) / 2 ^ 40 <= Chebyshev.theta (735806570 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert108 hb107 729708912 le_rfl (by norm_num)).2
  have hb109 : (815690386139319703486 : Real) / 2 ^ 40 <= Chebyshev.theta (741897012 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert109 hb108 735806570 le_rfl (by norm_num)).2
  have hb110 : (822397100049477645378 : Real) / 2 ^ 40 <= Chebyshev.theta (748005188 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert110 hb109 741897012 le_rfl (by norm_num)).2
  have hb111 : (829106495157148904514 : Real) / 2 ^ 40 <= Chebyshev.theta (754116218 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert111 hb110 748005188 le_rfl (by norm_num)).2
  have hb112 : (835818547468657503982 : Real) / 2 ^ 40 <= Chebyshev.theta (760217454 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert112 hb111 754116218 le_rfl (by norm_num)).2
  have hb113 : (842533237546694029282 : Real) / 2 ^ 40 <= Chebyshev.theta (766331430 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert113 hb112 760217454 le_rfl (by norm_num)).2
  have hb114 : (849250545549257083177 : Real) / 2 ^ 40 <= Chebyshev.theta (772433478 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert114 hb113 766331430 le_rfl (by norm_num)).2
  have hb115 : (855970449734618765565 : Real) / 2 ^ 40 <= Chebyshev.theta (778549394 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert115 hb114 772433478 le_rfl (by norm_num)).2
  have hb116 : (862692931825214548563 : Real) / 2 ^ 40 <= Chebyshev.theta (784659612 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert116 hb115 778549394 le_rfl (by norm_num)).2
  have hb117 : (869417970112622217083 : Real) / 2 ^ 40 <= Chebyshev.theta (790765920 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert117 hb116 784659612 le_rfl (by norm_num)).2
  have hb118 : (876145546815327278175 : Real) / 2 ^ 40 <= Chebyshev.theta (796888034 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert118 hb117 790765920 le_rfl (by norm_num)).2
  have hb119 : (882875643577989917160 : Real) / 2 ^ 40 <= Chebyshev.theta (803009258 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert119 hb118 796888034 le_rfl (by norm_num)).2
  have hb120 : (889608243169104607049 : Real) / 2 ^ 40 <= Chebyshev.theta (809125862 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert120 hb119 803009258 le_rfl (by norm_num)).2
  have hb121 : (896343326845943621413 : Real) / 2 ^ 40 <= Chebyshev.theta (815255994 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert121 hb120 809125862 le_rfl (by norm_num)).2
  have hb122 : (903080877159491121623 : Real) / 2 ^ 40 <= Chebyshev.theta (821378672 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert122 hb121 815255994 le_rfl (by norm_num)).2
  have hb123 : (909820878057709386928 : Real) / 2 ^ 40 <= Chebyshev.theta (827510988 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert123 hb122 821378672 le_rfl (by norm_num)).2
  have hb124 : (916563311903656646484 : Real) / 2 ^ 40 <= Chebyshev.theta (833642058 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert124 hb123 827510988 le_rfl (by norm_num)).2
  have hb125 : (923308160330829168848 : Real) / 2 ^ 40 <= Chebyshev.theta (839774562 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert125 hb124 833642058 le_rfl (by norm_num)).2
  have hb126 : (930055406383098040572 : Real) / 2 ^ 40 <= Chebyshev.theta (845911358 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert126 hb125 839774562 le_rfl (by norm_num)).2
  have hb127 : (936805035183985976272 : Real) / 2 ^ 40 <= Chebyshev.theta (852054188 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert127 hb126 845911358 le_rfl (by norm_num)).2
  have hb128 : (943557029663492111496 : Real) / 2 ^ 40 <= Chebyshev.theta (858192092 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert128 hb127 852054188 le_rfl (by norm_num)).2
  have hb129 : (950311375719728919082 : Real) / 2 ^ 40 <= Chebyshev.theta (864342252 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert129 hb128 858192092 le_rfl (by norm_num)).2
  have hb130 : (957068055072340891957 : Real) / 2 ^ 40 <= Chebyshev.theta (870482720 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert130 hb129 864342252 le_rfl (by norm_num)).2
  have hb131 : (963827052273630336921 : Real) / 2 ^ 40 <= Chebyshev.theta (876634988 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert131 hb130 870482720 le_rfl (by norm_num)).2
  have hb132 : (970588354123940266716 : Real) / 2 ^ 40 <= Chebyshev.theta (882785598 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert132 hb131 876634988 le_rfl (by norm_num)).2
  have hb133 : (977351944265527706504 : Real) / 2 ^ 40 <= Chebyshev.theta (888940590 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert133 hb132 882785598 le_rfl (by norm_num)).2
  have hb134 : (984117807606823907894 : Real) / 2 ^ 40 <= Chebyshev.theta (895099244 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert134 hb133 888940590 le_rfl (by norm_num)).2
  have hb135 : (990885929667298500107 : Real) / 2 ^ 40 <= Chebyshev.theta (901255308 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert135 hb134 895099244 le_rfl (by norm_num)).2
  have hb136 : (997656295101403628344 : Real) / 2 ^ 40 <= Chebyshev.theta (907413294 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert136 hb135 901255308 le_rfl (by norm_num)).2
  have hb137 : (1004428885821919545570 : Real) / 2 ^ 40 <= Chebyshev.theta (913563882 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert137 hb136 907413294 le_rfl (by norm_num)).2
  have hb138 : (1011203688383024899854 : Real) / 2 ^ 40 <= Chebyshev.theta (919722338 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert138 hb137 913563882 le_rfl (by norm_num)).2
  have hb139 : (1017980689931330188935 : Real) / 2 ^ 40 <= Chebyshev.theta (925885824 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert139 hb138 919722338 le_rfl (by norm_num)).2
  have hb140 : (1024759879293615383705 : Real) / 2 ^ 40 <= Chebyshev.theta (932059862 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert140 hb139 925885824 le_rfl (by norm_num)).2
  have hb141 : (1031541241048790125923 : Real) / 2 ^ 40 <= Chebyshev.theta (938225552 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert141 hb140 932059862 le_rfl (by norm_num)).2
  have hb142 : (1038324762665729977281 : Real) / 2 ^ 40 <= Chebyshev.theta (944397662 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert142 hb141 938225552 le_rfl (by norm_num)).2
  have hb143 : (1045110429120593951097 : Real) / 2 ^ 40 <= Chebyshev.theta (950571314 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert143 hb142 944397662 le_rfl (by norm_num)).2
  have hb144 : (1051898227664747297423 : Real) / 2 ^ 40 <= Chebyshev.theta (956743928 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert144 hb143 950571314 le_rfl (by norm_num)).2
  have hb145 : (1058688142822024335308 : Real) / 2 ^ 40 <= Chebyshev.theta (962909808 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert145 hb144 956743928 le_rfl (by norm_num)).2
  have hb146 : (1065480162958321338524 : Real) / 2 ^ 40 <= Chebyshev.theta (969088578 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert146 hb145 962909808 le_rfl (by norm_num)).2
  have hb147 : (1072274276176252210466 : Real) / 2 ^ 40 <= Chebyshev.theta (975269910 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert147 hb146 969088578 le_rfl (by norm_num)).2
  have hb148 : (1079070471680309439245 : Real) / 2 ^ 40 <= Chebyshev.theta (981454742 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert148 hb147 975269910 le_rfl (by norm_num)).2
  have hb149 : (1085868734456141367430 : Real) / 2 ^ 40 <= Chebyshev.theta (987633810 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert149 hb148 981454742 le_rfl (by norm_num)).2
  have hb150 : (1092669051988066974905 : Real) / 2 ^ 40 <= Chebyshev.theta (993817664 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert150 hb149 987633810 le_rfl (by norm_num)).2
  intro n hlo hhi
  rcases Nat.lt_or_ge n 536118548 with hc75 | hc75
  · rcases Nat.lt_or_ge n 310872278 with hc37 | hc37
    · rcases Nat.lt_or_ge n 201089412 with hc18 | hc18
      · rcases Nat.lt_or_ge n 150081180 with hc9 | hc9
        · rcases Nat.lt_or_ge n 122125308 with hc4 | hc4
          · rcases Nat.lt_or_ge n 111026058 with hc2 | hc2
            · rcases Nat.lt_or_ge n 105505290 with hc1 | hc1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert001 hb0 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert002 hb1 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 116568182 with hc3 | hc3
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert003 hb2 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert004 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 133269860 with hc6 | hc6
            · rcases Nat.lt_or_ge n 127690208 with hc5 | hc5
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert005 hb4 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert006 hb5 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 138864182 with hc7 | hc7
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert007 hb6 n (by omega) (by omega)).1
              · rcases Nat.lt_or_ge n 144462408 with hc8 | hc8
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert008 hb7 n (by omega) (by omega)).1
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert009 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 172650912 with hc13 | hc13
          · rcases Nat.lt_or_ge n 161348330 with hc11 | hc11
            · rcases Nat.lt_or_ge n 155710602 with hc10 | hc10
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert010 hb9 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert011 hb10 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 166998614 with hc12 | hc12
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert012 hb11 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert013 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 183999360 with hc15 | hc15
            · rcases Nat.lt_or_ge n 178316108 with hc14 | hc14
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert014 hb13 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert015 hb14 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 189683538 with hc16 | hc16
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert016 hb15 n (by omega) (by omega)).1
              · rcases Nat.lt_or_ge n 195379782 with hc17 | hc17
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert017 hb16 n (by omega) (by omega)).1
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert018 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 252784854 with hc27 | hc27
        · rcases Nat.lt_or_ge n 223991180 with hc22 | hc22
          · rcases Nat.lt_or_ge n 212522868 with hc20 | hc20
            · rcases Nat.lt_or_ge n 206801942 with hc19 | hc19
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert019 hb18 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert020 hb19 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 218252720 with hc21 | hc21
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert021 hb20 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert022 hb21 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 235488864 with hc24 | hc24
            · rcases Nat.lt_or_ge n 229737948 with hc23 | hc23
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert023 hb22 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert024 hb23 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 241240752 with hc25 | hc25
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert025 hb24 n (by omega) (by omega)).1
              · rcases Nat.lt_or_ge n 247010948 with hc26 | hc26
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert026 hb25 n (by omega) (by omega)).1
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert027 hb26 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 281750150 with hc32 | hc32
          · rcases Nat.lt_or_ge n 264352070 with hc29 | hc29
            · rcases Nat.lt_or_ge n 258564542 with hc28 | hc28
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert028 hb27 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert029 hb28 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 270147678 with hc30 | hc30
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert030 hb29 n (by omega) (by omega)).1
              · rcases Nat.lt_or_ge n 275946488 with hc31 | hc31
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert031 hb30 n (by omega) (by omega)).1
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert032 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 293386730 with hc34 | hc34
            · rcases Nat.lt_or_ge n 287568014 with hc33 | hc33
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert033 hb32 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert034 hb33 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 299212862 with hc35 | hc35
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert035 hb34 n (by omega) (by omega)).1
              · rcases Nat.lt_or_ge n 305039744 with hc36 | hc36
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert036 hb35 n (by omega) (by omega)).1
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert037 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 422732928 with hc56 | hc56
      · rcases Nat.lt_or_ge n 363647564 with hc46 | hc46
        · rcases Nat.lt_or_ge n 334280034 with hc41 | hc41
          · rcases Nat.lt_or_ge n 322566954 with hc39 | hc39
            · rcases Nat.lt_or_ge n 316715072 with hc38 | hc38
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert038 hb37 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert039 hb38 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 328418628 with hc40 | hc40
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert040 hb39 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert041 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 346007568 with hc43 | hc43
            · rcases Nat.lt_or_ge n 340142490 with hc42 | hc42
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert042 hb41 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert043 hb42 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 351884064 with hc44 | hc44
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert044 hb43 n (by omega) (by omega)).1
              · rcases Nat.lt_or_ge n 357761984 with hc45 | hc45
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert045 hb44 n (by omega) (by omega)).1
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert046 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 393128004 with hc51 | hc51
          · rcases Nat.lt_or_ge n 375427754 with hc48 | hc48
            · rcases Nat.lt_or_ge n 369536114 with hc47 | hc47
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert047 hb46 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert048 hb47 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 381314304 with hc49 | hc49
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert049 hb48 n (by omega) (by omega)).1
              · rcases Nat.lt_or_ge n 387220200 with hc50 | hc50
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert050 hb49 n (by omega) (by omega)).1
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert051 hb50 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 404956580 with hc53 | hc53
            · rcases Nat.lt_or_ge n 399042702 with hc52 | hc52
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert052 hb51 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert053 hb52 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 410875274 with hc54 | hc54
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert054 hb53 n (by omega) (by omega)).1
              · rcases Nat.lt_or_ge n 416799212 with hc55 | hc55
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert055 hb54 n (by omega) (by omega)).1
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert056 hb55 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 476271710 with hc65 | hc65
        · rcases Nat.lt_or_ge n 446484090 with hc60 | hc60
          · rcases Nat.lt_or_ge n 434599368 with hc58 | hc58
            · rcases Nat.lt_or_ge n 428659842 with hc57 | hc57
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert057 hb56 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert058 hb57 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 440543372 with hc59 | hc59
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert059 hb58 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert060 hb59 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 458385602 with hc62 | hc62
            · rcases Nat.lt_or_ge n 452433602 with hc61 | hc61
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert061 hb60 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert062 hb61 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 464340914 with hc63 | hc63
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert063 hb62 n (by omega) (by omega)).1
              · rcases Nat.lt_or_ge n 470299910 with hc64 | hc64
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert064 hb63 n (by omega) (by omega)).1
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert065 hb64 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 506149782 with hc70 | hc70
          · rcases Nat.lt_or_ge n 488204660 with hc67 | hc67
            · rcases Nat.lt_or_ge n 482231700 with hc66 | hc66
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert066 hb65 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert067 hb66 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 494180658 with hc68 | hc68
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert068 hb67 n (by omega) (by omega)).1
              · rcases Nat.lt_or_ge n 500158950 with hc69 | hc69
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert069 hb68 n (by omega) (by omega)).1
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert070 hb69 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 518131040 with hc72 | hc72
            · rcases Nat.lt_or_ge n 512140712 with hc71 | hc71
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert071 hb70 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert072 hb71 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 524125040 with hc73 | hc73
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert073 hb72 n (by omega) (by omega)).1
              · rcases Nat.lt_or_ge n 530117382 with hc74 | hc74
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert074 hb73 n (by omega) (by omega)).1
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert075 hb74 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 766331430 with hc113 | hc113
    · rcases Nat.lt_or_ge n 650706242 with hc94 | hc94
      · rcases Nat.lt_or_ge n 590261978 with hc84 | hc84
        · rcases Nat.lt_or_ge n 560150714 with hc79 | hc79
          · rcases Nat.lt_or_ge n 548130750 with hc77 | hc77
            · rcases Nat.lt_or_ge n 542123004 with hc76 | hc76
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert076 hb75 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert077 hb76 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 554131368 with hc78 | hc78
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert078 hb77 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert079 hb78 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 572187692 with hc81 | hc81
            · rcases Nat.lt_or_ge n 566166204 with hc80 | hc80
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert080 hb79 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert081 hb80 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 578210628 with hc82 | hc82
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert082 hb81 n (by omega) (by omega)).1
              · rcases Nat.lt_or_ge n 584231732 with hc83 | hc83
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert083 hb82 n (by omega) (by omega)).1
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert084 hb83 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 620446704 with hc89 | hc89
          · rcases Nat.lt_or_ge n 602321844 with hc86 | hc86
            · rcases Nat.lt_or_ge n 596283782 with hc85 | hc85
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert085 hb84 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert086 hb85 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 608354970 with hc87 | hc87
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert087 hb86 n (by omega) (by omega)).1
              · rcases Nat.lt_or_ge n 614398092 with hc88 | hc88
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert088 hb87 n (by omega) (by omega)).1
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert089 hb88 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 632540862 with hc91 | hc91
            · rcases Nat.lt_or_ge n 626495240 with hc90 | hc90
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert090 hb89 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert091 hb90 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 638593340 with hc92 | hc92
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert092 hb91 n (by omega) (by omega)).1
              · rcases Nat.lt_or_ge n 644655242 with hc93 | hc93
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert093 hb92 n (by omega) (by omega)).1
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert094 hb93 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 705351204 with hc103 | hc103
        · rcases Nat.lt_or_ge n 674966234 with hc98 | hc98
          · rcases Nat.lt_or_ge n 662826500 with hc96 | hc96
            · rcases Nat.lt_or_ge n 656768864 with hc95 | hc95
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert095 hb94 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert096 hb95 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 668897498 with hc97 | hc97
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert097 hb96 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert098 hb97 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 687113858 with hc100 | hc100
            · rcases Nat.lt_or_ge n 681044628 with hc99 | hc99
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert099 hb98 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert100 hb99 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 693190904 with hc101 | hc101
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert101 hb100 n (by omega) (by omega)).1
              · rcases Nat.lt_or_ge n 699268608 with hc102 | hc102
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert102 hb101 n (by omega) (by omega)).1
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert103 hb102 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 735806570 with hc108 | hc108
          · rcases Nat.lt_or_ge n 717526298 with hc105 | hc105
            · rcases Nat.lt_or_ge n 711434862 with hc104 | hc104
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert104 hb103 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert105 hb104 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 723611424 with hc106 | hc106
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert106 hb105 n (by omega) (by omega)).1
              · rcases Nat.lt_or_ge n 729708912 with hc107 | hc107
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert107 hb106 n (by omega) (by omega)).1
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert108 hb107 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 748005188 with hc110 | hc110
            · rcases Nat.lt_or_ge n 741897012 with hc109 | hc109
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert109 hb108 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert110 hb109 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 754116218 with hc111 | hc111
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert111 hb110 n (by omega) (by omega)).1
              · rcases Nat.lt_or_ge n 760217454 with hc112 | hc112
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert112 hb111 n (by omega) (by omega)).1
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert113 hb112 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 882785598 with hc132 | hc132
      · rcases Nat.lt_or_ge n 821378672 with hc122 | hc122
        · rcases Nat.lt_or_ge n 790765920 with hc117 | hc117
          · rcases Nat.lt_or_ge n 778549394 with hc115 | hc115
            · rcases Nat.lt_or_ge n 772433478 with hc114 | hc114
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert114 hb113 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert115 hb114 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 784659612 with hc116 | hc116
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert116 hb115 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert117 hb116 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 803009258 with hc119 | hc119
            · rcases Nat.lt_or_ge n 796888034 with hc118 | hc118
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert118 hb117 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert119 hb118 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 809125862 with hc120 | hc120
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert120 hb119 n (by omega) (by omega)).1
              · rcases Nat.lt_or_ge n 815255994 with hc121 | hc121
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert121 hb120 n (by omega) (by omega)).1
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert122 hb121 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 852054188 with hc127 | hc127
          · rcases Nat.lt_or_ge n 833642058 with hc124 | hc124
            · rcases Nat.lt_or_ge n 827510988 with hc123 | hc123
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert123 hb122 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert124 hb123 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 839774562 with hc125 | hc125
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert125 hb124 n (by omega) (by omega)).1
              · rcases Nat.lt_or_ge n 845911358 with hc126 | hc126
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert126 hb125 n (by omega) (by omega)).1
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert127 hb126 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 864342252 with hc129 | hc129
            · rcases Nat.lt_or_ge n 858192092 with hc128 | hc128
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert128 hb127 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert129 hb128 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 870482720 with hc130 | hc130
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert130 hb129 n (by omega) (by omega)).1
              · rcases Nat.lt_or_ge n 876634988 with hc131 | hc131
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert131 hb130 n (by omega) (by omega)).1
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert132 hb131 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 938225552 with hc141 | hc141
        · rcases Nat.lt_or_ge n 907413294 with hc136 | hc136
          · rcases Nat.lt_or_ge n 895099244 with hc134 | hc134
            · rcases Nat.lt_or_ge n 888940590 with hc133 | hc133
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert133 hb132 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert134 hb133 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 901255308 with hc135 | hc135
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert135 hb134 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert136 hb135 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 919722338 with hc138 | hc138
            · rcases Nat.lt_or_ge n 913563882 with hc137 | hc137
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert137 hb136 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert138 hb137 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 925885824 with hc139 | hc139
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert139 hb138 n (by omega) (by omega)).1
              · rcases Nat.lt_or_ge n 932059862 with hc140 | hc140
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert140 hb139 n (by omega) (by omega)).1
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert141 hb140 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 969088578 with hc146 | hc146
          · rcases Nat.lt_or_ge n 950571314 with hc143 | hc143
            · rcases Nat.lt_or_ge n 944397662 with hc142 | hc142
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert142 hb141 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert143 hb142 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 956743928 with hc144 | hc144
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert144 hb143 n (by omega) (by omega)).1
              · rcases Nat.lt_or_ge n 962909808 with hc145 | hc145
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert145 hb144 n (by omega) (by omega)).1
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert146 hb145 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 981454742 with hc148 | hc148
            · rcases Nat.lt_or_ge n 975269910 with hc147 | hc147
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert147 hb146 n (by omega) (by omega)).1
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert148 hb147 n (by omega) (by omega)).1
            · rcases Nat.lt_or_ge n 987633810 with hc149 | hc149
              · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert149 hb148 n (by omega) (by omega)).1
              · rcases Nat.lt_or_ge n 993817664 with hc150 | hc150
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert150 hb149 n (by omega) (by omega)).1
                · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert151 hb150 n (by omega) (by omega)).1

end TFPMidLower

theorem solution (t : ℝ) (h1 : 1420 ≤ t)
    (h2 : t ≤ 10 ^ 9) :
    t * (1 - 1 / (2 * Real.log t)) < Chebyshev.theta t := by
  rcases le_or_gt t (10 ^ 8) with hle | hlt
  · exact TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_finite t h1 hle
  have hlt' : (100000000 : ℝ) < t := by
    have := hlt
    norm_num at this
    exact this
  have h2' : t ≤ (1000000000 : ℝ) := by
    have := h2
    norm_num at this
    exact this
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌊t⌋₊ := ⟨_, rfl⟩
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hn1 : (n : ℝ) ≤ t := by rw [hn]; exact Nat.floor_le ht0
  have hn2 : t < (n : ℝ) + 1 := by rw [hn]; exact Nat.lt_floor_add_one t
  have hnlo : 100000000 ≤ n := by
    have : ((100000000 : ℕ) : ℝ) < (n : ℝ) + 1 := by push_cast; linarith
    have : 100000000 < n + 1 := by exact_mod_cast this
    omega
  have hnhi : n ≤ 1000000000 := by
    have : (n : ℝ) ≤ ((1000000000 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hk := TFPMidLower.chain_key n hnlo hnhi
  have hθ : Chebyshev.theta t = Chebyshev.theta (n : ℝ) := by rw [hn]; exact TFPMidLower.theta_floor t
  have hmono := TFPMidLower.sqrt_mono10 (t := t) (y := (n : ℝ) + 1) (by linarith) hn2.le
  have hg := TFPMidLower.glue_log t hlt'.le
  have hL : 0 < Real.log t := Real.log_pos (by linarith)
  have hst : √t * √t = t := Real.mul_self_sqrt ht0
  have hs0 : 0 < √t := Real.sqrt_pos.2 (by linarith)
  have hmain : 10 * √t < t / (2 * Real.log t) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left hg hs0]
  rw [mul_sub, mul_one, mul_one_div, hθ]
  linarith
