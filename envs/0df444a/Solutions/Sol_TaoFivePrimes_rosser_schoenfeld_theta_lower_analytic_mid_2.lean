-- Prove2me | solution 2 for TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T07:07:12.171839+00:00
-- url     : https://prove2.me/submissions/3aec7e0b-e65e-4472-b17a-e1b8cf92f43c

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic_mid_lower
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_grp01
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_grp02
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_lower_grp03
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp01
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp02
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp03
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp04
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp05
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp06
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp07
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp08
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp09
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp10
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp11
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp12
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp13
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp14
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp15
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp16
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp17
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp18
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp19
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp20
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp21
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp22
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp23
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp24
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp25
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp26
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp27

/-! Reduction of `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid` (56cff342) to
* `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid_lower` (fa58620e) on `[1420, 10 ^ 9]`,
* `TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large` (f48a0c89) at `t = 10 ^ 8`: the first carry `C_0 / 2 ^ 40 = 99980000 = 10 ^ 8 - 2 √(10 ^ 8) < θ (10 ^ 8)`,
* the 3 Phase 1 certificate blocks `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_grp01` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_grp03` on `[10 ^ 8, 10 ^ 9]` (carry chain to `θ (10 ^ 9 + 1)`, and the bound at `n = 10 ^ 9`),
* the 27 Phase 2 certificate blocks `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp01` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp27` on `[10 ^ 9 + 1, 10 ^ 10]`.
Each block has the shape of a certificate segment: carry in `C / 2 ^ 40 ≤ θ a` gives `(n + 1) - 10 √(n + 1) ≤ θ n` on `[a, b]` and the carry out at `b + 1`. For `10 ^ 9 < t ≤ 10 ^ 10` with `n = ⌊t⌋₊`: `θ t = θ n ≥ (n + 1) - 10 √(n + 1) ≥ t - 10 √t` (monotone from 25 on) `> t - t / (2 log t)` since `20 log t < √t` (`glue_log`). -/

namespace TFPMid

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

end TFPMid

namespace TFPMid

set_option maxHeartbeats 4000000 in
theorem key : ∀ n : ℕ, 1000000000 ≤ n → n ≤ 10000000000 →
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) := by
  have hb0 : (109929172545044480000 : Real) / 2 ^ 40 <= Chebyshev.theta (100000000 : Real) := by
    have hs : Real.sqrt (100000000 : ℝ) = 10000 := by
      rw [show (100000000 : ℝ) = 10000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have H := TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large 100000000 (by norm_num) (by norm_num)
    rw [hs] at H
    have hC : (109929172545044480000 : ℝ) / 2 ^ 40 = 99980000 := by norm_num
    rw [hC]
    linarith
  have hb1 : (432220832279890113048 : Real) / 2 ^ 40 <= Chebyshev.theta (393128004 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_grp01 hb0 100000000 le_rfl (by norm_num)).2
  have hb2 : (762135668912283162940 : Real) / 2 ^ 40 <= Chebyshev.theta (693190904 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_grp02 hb1 393128004 le_rfl (by norm_num)).2
  have hb3 : (1099469019730663974882 : Real) / 2 ^ 40 <= Chebyshev.theta (1000000001 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_grp03 hb2 693190904 le_rfl (by norm_num)).2
  have hb4 : (1443427307425134654554 : Real) / 2 ^ 40 <= Chebyshev.theta (1312834712 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp01 hb3 1000000001 le_rfl (by norm_num)).2
  have hb5 : (1791373280619079820717 : Real) / 2 ^ 40 <= Chebyshev.theta (1629291792 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp02 hb4 1312834712 le_rfl (by norm_num)).2
  have hb6 : (2142555716222639034474 : Real) / 2 ^ 40 <= Chebyshev.theta (1948709900 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp03 hb5 1629291792 le_rfl (by norm_num)).2
  have hb7 : (2496462384131083673405 : Real) / 2 ^ 40 <= Chebyshev.theta (2270572190 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp04 hb6 1948709900 le_rfl (by norm_num)).2
  have hb8 : (2852721260005778301656 : Real) / 2 ^ 40 <= Chebyshev.theta (2594569592 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp05 hb7 2270572190 le_rfl (by norm_num)).2
  have hb9 : (3211049915453427999706 : Real) / 2 ^ 40 <= Chebyshev.theta (2920492542 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp06 hb8 2594569592 le_rfl (by norm_num)).2
  have hb10 : (3571226616548090907563 : Real) / 2 ^ 40 <= Chebyshev.theta (3248089460 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp07 hb9 2920492542 le_rfl (by norm_num)).2
  have hb11 : (3933072480233213816578 : Real) / 2 ^ 40 <= Chebyshev.theta (3577176104 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp08 hb10 3248089460 le_rfl (by norm_num)).2
  have hb12 : (4296440043854818217785 : Real) / 2 ^ 40 <= Chebyshev.theta (3907634390 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp09 hb11 3577176104 le_rfl (by norm_num)).2
  have hb13 : (4661206139401073931926 : Real) / 2 ^ 40 <= Chebyshev.theta (4239430052 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp10 hb12 3907634390 le_rfl (by norm_num)).2
  have hb14 : (5027265814990202898813 : Real) / 2 ^ 40 <= Chebyshev.theta (4572345230 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp11 hb13 4239430052 le_rfl (by norm_num)).2
  have hb15 : (5394528782830522203927 : Real) / 2 ^ 40 <= Chebyshev.theta (4906374498 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp12 hb14 4572345230 le_rfl (by norm_num)).2
  have hb16 : (5762916616992118131115 : Real) / 2 ^ 40 <= Chebyshev.theta (5241435864 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp13 hb15 4906374498 le_rfl (by norm_num)).2
  have hb17 : (6132360425961107643378 : Real) / 2 ^ 40 <= Chebyshev.theta (5577453188 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp14 hb16 5241435864 le_rfl (by norm_num)).2
  have hb18 : (6502799203779927993439 : Real) / 2 ^ 40 <= Chebyshev.theta (5914357088 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp15 hb17 5577453188 le_rfl (by norm_num)).2
  have hb19 : (6874178730578669503809 : Real) / 2 ^ 40 <= Chebyshev.theta (6252112020 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp16 hb18 5914357088 le_rfl (by norm_num)).2
  have hb20 : (7246450329781067871514 : Real) / 2 ^ 40 <= Chebyshev.theta (6590693514 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp17 hb19 6252112020 le_rfl (by norm_num)).2
  have hb21 : (7619570092620144083607 : Real) / 2 ^ 40 <= Chebyshev.theta (6930050750 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp18 hb20 6590693514 le_rfl (by norm_num)).2
  have hb22 : (7993498298181659601707 : Real) / 2 ^ 40 <= Chebyshev.theta (7270138658 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp19 hb21 6930050750 le_rfl (by norm_num)).2
  have hb23 : (8368198731656839134845 : Real) / 2 ^ 40 <= Chebyshev.theta (7610969534 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp20 hb22 7270138658 le_rfl (by norm_num)).2
  have hb24 : (8743638325656144631277 : Real) / 2 ^ 40 <= Chebyshev.theta (7952421524 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp21 hb23 7610969534 le_rfl (by norm_num)).2
  have hb25 : (9119786553842252571751 : Real) / 2 ^ 40 <= Chebyshev.theta (8294482074 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp22 hb24 7952421524 le_rfl (by norm_num)).2
  have hb26 : (9496615449774559403785 : Real) / 2 ^ 40 <= Chebyshev.theta (8637206844 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp23 hb25 8294482074 le_rfl (by norm_num)).2
  have hb27 : (9874099226388381058938 : Real) / 2 ^ 40 <= Chebyshev.theta (8980547700 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp24 hb26 8637206844 le_rfl (by norm_num)).2
  have hb28 : (10252213892257269854204 : Real) / 2 ^ 40 <= Chebyshev.theta (9324426324 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp25 hb27 8980547700 le_rfl (by norm_num)).2
  have hb29 : (10623356848875818030645 : Real) / 2 ^ 40 <= Chebyshev.theta (9661975292 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp26 hb28 9324426324 le_rfl (by norm_num)).2
  intro n hlo hhi
  rcases Nat.lt_or_ge n 5241435864 with hc14 | hc14
  · rcases Nat.lt_or_ge n 2920492542 with hc7 | hc7
    · rcases Nat.lt_or_ge n 1629291792 with hc3 | hc3
      · rcases Nat.lt_or_ge n 1000000001 with hc1 | hc1
        · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_grp03 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1312834712 with hc2 | hc2
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp01 hb3 n (by omega) (by omega)).1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp02 hb4 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 2270572190 with hc5 | hc5
        · rcases Nat.lt_or_ge n 1948709900 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp03 hb5 n (by omega) (by omega)).1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp04 hb6 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2594569592 with hc6 | hc6
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp05 hb7 n (by omega) (by omega)).1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp06 hb8 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 3907634390 with hc10 | hc10
      · rcases Nat.lt_or_ge n 3248089460 with hc8 | hc8
        · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp07 hb9 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3577176104 with hc9 | hc9
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp08 hb10 n (by omega) (by omega)).1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp09 hb11 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 4572345230 with hc12 | hc12
        · rcases Nat.lt_or_ge n 4239430052 with hc11 | hc11
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp10 hb12 n (by omega) (by omega)).1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp11 hb13 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 4906374498 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp12 hb14 n (by omega) (by omega)).1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp13 hb15 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 7610969534 with hc21 | hc21
    · rcases Nat.lt_or_ge n 6252112020 with hc17 | hc17
      · rcases Nat.lt_or_ge n 5577453188 with hc15 | hc15
        · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp14 hb16 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 5914357088 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp15 hb17 n (by omega) (by omega)).1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp16 hb18 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 6930050750 with hc19 | hc19
        · rcases Nat.lt_or_ge n 6590693514 with hc18 | hc18
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp17 hb19 n (by omega) (by omega)).1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp18 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 7270138658 with hc20 | hc20
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp19 hb21 n (by omega) (by omega)).1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp20 hb22 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 8637206844 with hc24 | hc24
      · rcases Nat.lt_or_ge n 7952421524 with hc22 | hc22
        · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp21 hb23 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 8294482074 with hc23 | hc23
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp22 hb24 n (by omega) (by omega)).1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp23 hb25 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 9324426324 with hc26 | hc26
        · rcases Nat.lt_or_ge n 8980547700 with hc25 | hc25
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp24 hb26 n (by omega) (by omega)).1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp25 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 9661975292 with hc27 | hc27
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp26 hb28 n (by omega) (by omega)).1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp27 hb29 n (by omega) (by omega)).1

end TFPMid

theorem solution (t : ℝ) (h1 : 1420 ≤ t)
    (h2 : t ≤ 10 ^ 10) :
    t * (1 - 1 / (2 * Real.log t)) < Chebyshev.theta t := by
  rcases le_or_gt t (10 ^ 9) with hle | hlt
  · exact TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid_lower t h1 hle
  have hlt' : (1000000000 : ℝ) < t := by
    have := hlt
    norm_num at this
    exact this
  have h2' : t ≤ (10000000000 : ℝ) := by
    have := h2
    norm_num at this
    exact this
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌊t⌋₊ := ⟨_, rfl⟩
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hn1 : (n : ℝ) ≤ t := by rw [hn]; exact Nat.floor_le ht0
  have hn2 : t < (n : ℝ) + 1 := by rw [hn]; exact Nat.lt_floor_add_one t
  have hnlo : 1000000000 ≤ n := by
    have : ((1000000000 : ℕ) : ℝ) < (n : ℝ) + 1 := by push_cast; linarith
    have : 1000000000 < n + 1 := by exact_mod_cast this
    omega
  have hnhi : n ≤ 10000000000 := by
    have : (n : ℝ) ≤ ((10000000000 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hk := TFPMid.key n hnlo hnhi
  have hθ : Chebyshev.theta t = Chebyshev.theta (n : ℝ) := by rw [hn]; exact TFPMid.theta_floor t
  have hmono := TFPMid.sqrt_mono10 (t := t) (y := (n : ℝ) + 1) (by linarith) hn2.le
  have hg := TFPMid.glue_log t (by linarith)
  have hL : 0 < Real.log t := Real.log_pos (by linarith)
  have hst : √t * √t = t := Real.mul_self_sqrt ht0
  have hs0 : 0 < √t := Real.sqrt_pos.2 (by linarith)
  have hmain : 10 * √t < t / (2 * Real.log t) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [mul_lt_mul_of_pos_left hg hs0]
  rw [mul_sub, mul_one, mul_one_div, hθ]
  linarith
