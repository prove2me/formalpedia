-- Prove2me | solution 1 for ThreeSumSharpTail.entropy_log_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T16:32:27.723708+00:00
-- url     : https://prove2.me/submissions/e28401b6-b8da-409e-b102-3704987ed7de

import Theorems.Thm_ThreeSumSharpTail_encoding_log_certificate
import Definitions.Def_ThreeSumSharpTail_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 5000000
set_option exponentiation.threshold 1000
open scoped BigOperators

namespace ThreeSumSharpTail.CertEntropy

noncomputable def logSeries (n : ℕ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, z ^ (2 * i + 1) / (2 * i + 1)

lemma log_bounds_of_atanh {y z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hy : (1 + z) / (1 - z) = y) (n : ℕ) :
    2 * logSeries n z ≤ Real.log y ∧
      Real.log y ≤ 2 * (logSeries n z + z ^ (2 * n + 1) / (1 - z ^ 2)) := by
  have hlo := Real.sum_range_le_log_div hz0 hz1 n
  have hhi := Real.log_div_le_sum_range_add hz0 hz1 n
  constructor
  · calc
      2 * logSeries n z ≤ Real.log ((1 + z) / (1 - z)) := by
        simpa [logSeries, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using
          (mul_le_mul_of_nonneg_left hlo (by norm_num : 0 ≤ (2 : ℝ)))
      _ = Real.log y := by rw [hy]
  · calc
      Real.log y = Real.log ((1 + z) / (1 - z)) := by rw [hy]
      _ ≤ 2 * (logSeries n z + z ^ (2 * n + 1) / (1 - z ^ 2)) := by
        have hm := mul_le_mul_of_nonneg_left hhi (by norm_num : 0 ≤ (2 : ℝ))
        calc
          Real.log ((1 + z) / (1 - z)) =
              2 * (1 / 2 * Real.log ((1 + z) / (1 - z))) := by ring
          _ ≤ 2 * (logSeries n z + z ^ (2 * n + 1) / (1 - z ^ 2)) := by
            simpa [logSeries] using hm

lemma log_88798_65625_cert :
    (302407406 / 10^9 : ℝ) ≤ Real.log (88798 / 65625) ∧ Real.log (88798 / 65625) ≤ 302407407 / 10^9 := by
  have h := log_bounds_of_atanh (y := (88798 : ℝ) / 65625) (z := (23173 : ℝ) / 154423)
    (by norm_num) (by norm_num) (by norm_num) 12
  constructor
  · have hs : (302407406 / 10^9 : ℝ) ≤ 2 * logSeries 12 ((23173 : ℝ) / 154423) := by norm_num [logSeries]
    exact hs.trans h.1
  · have hs : 2 * (logSeries 12 ((23173 : ℝ) / 154423) + ((23173 : ℝ) / 154423) ^ (2 * 12 + 1) / (1 - ((23173 : ℝ) / 154423) ^ 2)) ≤ 302407407 / 10^9 := by norm_num [logSeries]
    exact h.2.trans hs

lemma log_1005601_525000_cert :
    (649942389 / 10^9 : ℝ) ≤ Real.log (1005601 / 525000) ∧ Real.log (1005601 / 525000) ≤ 649942390 / 10^9 := by
  have h := log_bounds_of_atanh (y := (1005601 : ℝ) / 525000) (z := (480601 : ℝ) / 1530601)
    (by norm_num) (by norm_num) (by norm_num) 12
  constructor
  · have hs : (649942389 / 10^9 : ℝ) ≤ 2 * logSeries 12 ((480601 : ℝ) / 1530601) := by norm_num [logSeries]
    exact hs.trans h.1
  · have hs : 2 * (logSeries 12 ((480601 : ℝ) / 1530601) + ((480601 : ℝ) / 1530601) ^ (2 * 12 + 1) / (1 - ((480601 : ℝ) / 1530601) ^ 2)) ≤ 649942390 / 10^9 := by norm_num [logSeries]
    exact h.2.trans hs

lemma log_5601_3125_cert :
    (583510870 / 10^9 : ℝ) ≤ Real.log (5601 / 3125) ∧ Real.log (5601 / 3125) ≤ 583510871 / 10^9 := by
  have h := log_bounds_of_atanh (y := (5601 : ℝ) / 3125) (z := (1238 : ℝ) / 4363)
    (by norm_num) (by norm_num) (by norm_num) 12
  constructor
  · have hs : (583510870 / 10^9 : ℝ) ≤ 2 * logSeries 12 ((1238 : ℝ) / 4363) := by norm_num [logSeries]
    exact hs.trans h.1
  · have hs : 2 * (logSeries 12 ((1238 : ℝ) / 4363) + ((1238 : ℝ) / 4363) ^ (2 * 12 + 1) / (1 - ((1238 : ℝ) / 4363) ^ 2)) ≤ 583510871 / 10^9 := by norm_num [logSeries]
    exact h.2.trans hs

lemma log_44399_25000_cert :
    (574341121 / 10^9 : ℝ) ≤ Real.log (44399 / 25000) ∧ Real.log (44399 / 25000) ≤ 574341122 / 10^9 := by
  have h := log_bounds_of_atanh (y := (44399 : ℝ) / 25000) (z := (19399 : ℝ) / 69399)
    (by norm_num) (by norm_num) (by norm_num) 12
  constructor
  · have hs : (574341121 / 10^9 : ℝ) ≤ 2 * logSeries 12 ((19399 : ℝ) / 69399) := by norm_num [logSeries]
    exact hs.trans h.1
  · have hs : 2 * (logSeries 12 ((19399 : ℝ) / 69399) + ((19399 : ℝ) / 69399) ^ (2 * 12 + 1) / (1 - ((19399 : ℝ) / 69399) ^ 2)) ≤ 574341122 / 10^9 := by norm_num [logSeries]
    exact h.2.trans hs

lemma log_scale_up (x y : ℝ) (k : ℕ) (hx : 0 < y)
    (hxy : x = y * (2 : ℝ) ^ k) : Real.log x = Real.log y + k * Real.log 2 := by
  rw [hxy, Real.log_mul (ne_of_gt hx) (by positivity), Real.log_pow]

lemma log_scale_down (x y : ℝ) (k : ℕ) (hx : 0 < x)
    (hxy : y = x * (2 : ℝ) ^ k) : Real.log x = Real.log y - k * Real.log 2 := by
  have h := log_scale_up y x k hx hxy
  linarith

end ThreeSumSharpTail.CertEntropy


theorem solution :
    ((-3163328497 / 10^9 : ℝ) ≤ Real.log (44399 / 1050000) ∧ Real.log (44399 / 1050000) ≤ -3163328495 / 10^9) ∧
    ((-43204792 / 10^9 : ℝ) ≤ Real.log (1005601 / 1050000) ∧ Real.log (1005601 / 1050000) ≤ -43204790 / 10^9) ∧
    ((-2189077853 / 10^9 : ℝ) ≤ Real.log (5601 / 50000) ∧ Real.log (5601 / 50000) ≤ -2189077851 / 10^9) ∧
    ((-118806060 / 10^9 : ℝ) ≤ Real.log (44399 / 50000) ∧ Real.log (44399 / 50000) ≤ -118806057 / 10^9) := by
  have enc := ThreeSumSharpTail.encoding_log_certificate
  have l2 := enc.1
  have luq := ThreeSumSharpTail.CertEntropy.log_88798_65625_cert
  have lucq := ThreeSumSharpTail.CertEntropy.log_1005601_525000_cert
  have l5601q := ThreeSumSharpTail.CertEntropy.log_5601_3125_cert
  have l44399q := ThreeSumSharpTail.CertEntropy.log_44399_25000_cert
  have lu : (-3163328497 / 10^9 : ℝ) ≤ Real.log (44399 / 1050000) ∧ Real.log (44399 / 1050000) ≤ -3163328495 / 10^9 := by
    rw [ThreeSumSharpTail.CertEntropy.log_scale_down (44399 / 1050000) (88798 / 65625) 5 (by norm_num) (by norm_num)]
    constructor <;> nlinarith [l2.1, l2.2, luq.1, luq.2]
  have luc : (-43204792 / 10^9 : ℝ) ≤ Real.log (1005601 / 1050000) ∧ Real.log (1005601 / 1050000) ≤ -43204790 / 10^9 := by
    rw [ThreeSumSharpTail.CertEntropy.log_scale_down (1005601 / 1050000) (1005601 / 525000) 1 (by norm_num) (by norm_num)]
    constructor <;> nlinarith [l2.1, l2.2, lucq.1, lucq.2]
  have lt : (-2189077853 / 10^9 : ℝ) ≤ Real.log (5601 / 50000) ∧ Real.log (5601 / 50000) ≤ -2189077851 / 10^9 := by
    rw [ThreeSumSharpTail.CertEntropy.log_scale_down (5601 / 50000) (5601 / 3125) 4 (by norm_num) (by norm_num)]
    constructor <;> nlinarith [l2.1, l2.2, l5601q.1, l5601q.2]
  have ltc : (-118806060 / 10^9 : ℝ) ≤ Real.log (44399 / 50000) ∧ Real.log (44399 / 50000) ≤ -118806057 / 10^9 := by
    rw [ThreeSumSharpTail.CertEntropy.log_scale_down (44399 / 50000) (44399 / 25000) 1 (by norm_num) (by norm_num)]
    constructor <;> nlinarith [l2.1, l2.2, l44399q.1, l44399q.2]
  exact ⟨lu, luc, lt, ltc⟩
