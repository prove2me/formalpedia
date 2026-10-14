-- Prove2me | solution 1 for ThreeSumSharpTail.encoding_log_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T16:32:26.469146+00:00
-- url     : https://prove2.me/submissions/eec9b5e6-206e-4c65-8b22-afd5fbea44ec

import Definitions.Def_ThreeSumSharpTail_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 5000000
set_option exponentiation.threshold 1000
open scoped BigOperators

namespace ThreeSumSharpTail.CertEncoding

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

lemma log_two_certificate :
    (693147180559945 / 10^15 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ 693147180559946 / 10^15 := by
  have h := log_bounds_of_atanh (y := 2) (z := (1 : ℝ) / 3)
    (by norm_num) (by norm_num) (by norm_num) 16
  constructor
  · have hs : (693147180559945 / 10^15 : ℝ) ≤
        2 * logSeries 16 ((1 : ℝ) / 3) := by norm_num [logSeries]
    exact hs.trans h.1
  · have hs : 2 * (logSeries 16 ((1 : ℝ) / 3) +
        ((1 : ℝ) / 3) ^ (2 * 16 + 1) / (1 - ((1 : ℝ) / 3) ^ 2)) ≤
          693147180559946 / 10^15 := by norm_num [logSeries]
    exact h.2.trans hs

lemma log_5_4_cert :
    (223143551 / 10^9 : ℝ) ≤ Real.log (5 / 4) ∧ Real.log (5 / 4) ≤ 223143552 / 10^9 := by
  have h := log_bounds_of_atanh (y := (5 : ℝ) / 4) (z := (1 : ℝ) / 9)
    (by norm_num) (by norm_num) (by norm_num) 12
  constructor
  · have hs : (223143551 / 10^9 : ℝ) ≤ 2 * logSeries 12 ((1 : ℝ) / 9) := by norm_num [logSeries]
    exact hs.trans h.1
  · have hs : 2 * (logSeries 12 ((1 : ℝ) / 9) + ((1 : ℝ) / 9) ^ (2 * 12 + 1) / (1 - ((1 : ℝ) / 9) ^ 2)) ≤ 223143552 / 10^9 := by norm_num [logSeries]
    exact h.2.trans hs

lemma log_3_2_cert :
    (405465108 / 10^9 : ℝ) ≤ Real.log (3 / 2) ∧ Real.log (3 / 2) ≤ 405465109 / 10^9 := by
  have h := log_bounds_of_atanh (y := (3 : ℝ) / 2) (z := (1 : ℝ) / 5)
    (by norm_num) (by norm_num) (by norm_num) 12
  constructor
  · have hs : (405465108 / 10^9 : ℝ) ≤ 2 * logSeries 12 ((1 : ℝ) / 5) := by norm_num [logSeries]
    exact hs.trans h.1
  · have hs : 2 * (logSeries 12 ((1 : ℝ) / 5) + ((1 : ℝ) / 5) ^ (2 * 12 + 1) / (1 - ((1 : ℝ) / 5) ^ 2)) ≤ 405465109 / 10^9 := by norm_num [logSeries]
    exact h.2.trans hs

lemma log_9_8_cert :
    (117783035 / 10^9 : ℝ) ≤ Real.log (9 / 8) ∧ Real.log (9 / 8) ≤ 117783036 / 10^9 := by
  have h := log_bounds_of_atanh (y := (9 : ℝ) / 8) (z := (1 : ℝ) / 17)
    (by norm_num) (by norm_num) (by norm_num) 12
  constructor
  · have hs : (117783035 / 10^9 : ℝ) ≤ 2 * logSeries 12 ((1 : ℝ) / 17) := by norm_num [logSeries]
    exact hs.trans h.1
  · have hs : 2 * (logSeries 12 ((1 : ℝ) / 17) + ((1 : ℝ) / 17) ^ (2 * 12 + 1) / (1 - ((1 : ℝ) / 17) ^ 2)) ≤ 117783036 / 10^9 := by norm_num [logSeries]
    exact h.2.trans hs

lemma log_32_21_cert :
    (421213465 / 10^9 : ℝ) ≤ Real.log (32 / 21) ∧ Real.log (32 / 21) ≤ 421213466 / 10^9 := by
  have h := log_bounds_of_atanh (y := (32 : ℝ) / 21) (z := (11 : ℝ) / 53)
    (by norm_num) (by norm_num) (by norm_num) 12
  constructor
  · have hs : (421213465 / 10^9 : ℝ) ≤ 2 * logSeries 12 ((11 : ℝ) / 53) := by norm_num [logSeries]
    exact hs.trans h.1
  · have hs : 2 * (logSeries 12 ((11 : ℝ) / 53) + ((11 : ℝ) / 53) ^ (2 * 12 + 1) / (1 - ((11 : ℝ) / 53) ^ 2)) ≤ 421213466 / 10^9 := by norm_num [logSeries]
    exact h.2.trans hs

lemma log_40_21_cert :
    (644357016 / 10^9 : ℝ) ≤ Real.log (40 / 21) ∧ Real.log (40 / 21) ≤ 644357017 / 10^9 := by
  have h := log_bounds_of_atanh (y := (40 : ℝ) / 21) (z := (19 : ℝ) / 61)
    (by norm_num) (by norm_num) (by norm_num) 12
  constructor
  · have hs : (644357016 / 10^9 : ℝ) ≤ 2 * logSeries 12 ((19 : ℝ) / 61) := by norm_num [logSeries]
    exact hs.trans h.1
  · have hs : 2 * (logSeries 12 ((19 : ℝ) / 61) + ((19 : ℝ) / 61) ^ (2 * 12 + 1) / (1 - ((19 : ℝ) / 61) ^ 2)) ≤ 644357017 / 10^9 := by norm_num [logSeries]
    exact h.2.trans hs

lemma log_scale_up (x y : ℝ) (k : ℕ) (hx : 0 < y)
    (hxy : x = y * (2 : ℝ) ^ k) : Real.log x = Real.log y + k * Real.log 2 := by
  rw [hxy, Real.log_mul (ne_of_gt hx) (by positivity), Real.log_pow]

lemma log_scale_down (x y : ℝ) (k : ℕ) (hx : 0 < x)
    (hxy : y = x * (2 : ℝ) ^ k) : Real.log x = Real.log y - k * Real.log 2 := by
  have h := log_scale_up y x k hx hxy
  linarith

end ThreeSumSharpTail.CertEncoding


theorem solution :
    ((693147180559945 / 10^15 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 693147180559946 / 10^15) ∧
    ((2302585092 / 10^9 : ℝ) ≤ Real.log 10 ∧ Real.log 10 ≤ 2302585094 / 10^9) ∧
    ((1098612288 / 10^9 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ 1098612290 / 10^9) ∧
    ((2197224575 / 10^9 : ℝ) ≤ Real.log 9 ∧ Real.log 9 ≤ 2197224580 / 10^9) ∧
    ((-3044522438 / 10^9 : ℝ) ≤ Real.log (1 / 21) ∧ Real.log (1 / 21) ≤ -3044522436 / 10^9) ∧
    ((-48790165 / 10^9 : ℝ) ≤ Real.log (20 / 21) ∧ Real.log (20 / 21) ≤ -48790163 / 10^9) := by
  have l2 := ThreeSumSharpTail.CertEncoding.log_two_certificate
  have l5q := ThreeSumSharpTail.CertEncoding.log_5_4_cert
  have l3q := ThreeSumSharpTail.CertEncoding.log_3_2_cert
  have l9q := ThreeSumSharpTail.CertEncoding.log_9_8_cert
  have l32q := ThreeSumSharpTail.CertEncoding.log_32_21_cert
  have l40q := ThreeSumSharpTail.CertEncoding.log_40_21_cert
  have l10 : (2302585092 / 10^9 : ℝ) ≤ Real.log 10 ∧ Real.log 10 ≤ 2302585094 / 10^9 := by
    rw [ThreeSumSharpTail.CertEncoding.log_scale_up 10 (5 / 4) 3 (by norm_num) (by norm_num)]
    constructor <;> nlinarith [l2.1, l2.2, l5q.1, l5q.2]
  have l3 : (1098612288 / 10^9 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ 1098612290 / 10^9 := by
    rw [ThreeSumSharpTail.CertEncoding.log_scale_up 3 (3 / 2) 1 (by norm_num) (by norm_num)]
    constructor <;> nlinarith [l2.1, l2.2, l3q.1, l3q.2]
  have l9 : (2197224575 / 10^9 : ℝ) ≤ Real.log 9 ∧ Real.log 9 ≤ 2197224580 / 10^9 := by
    rw [ThreeSumSharpTail.CertEncoding.log_scale_up 9 (9 / 8) 3 (by norm_num) (by norm_num)]
    constructor <;> nlinarith [l2.1, l2.2, l9q.1, l9q.2]
  have linv21 : (-3044522438 / 10^9 : ℝ) ≤ Real.log (1 / 21) ∧ Real.log (1 / 21) ≤ -3044522436 / 10^9 := by
    rw [ThreeSumSharpTail.CertEncoding.log_scale_down (1 / 21) (32 / 21) 5 (by norm_num) (by norm_num)]
    constructor <;> nlinarith [l2.1, l2.2, l32q.1, l32q.2]
  have l20_21 : (-48790165 / 10^9 : ℝ) ≤ Real.log (20 / 21) ∧ Real.log (20 / 21) ≤ -48790163 / 10^9 := by
    rw [ThreeSumSharpTail.CertEncoding.log_scale_down (20 / 21) (40 / 21) 1 (by norm_num) (by norm_num)]
    constructor <;> nlinarith [l2.1, l2.2, l40q.1, l40q.2]
  exact ⟨l2, l10, l3, l9, linv21, l20_21⟩
