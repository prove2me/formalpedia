-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P04.excessNoiseReach
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:18:41.840407+00:00
-- url     : https://prove2.me/submissions/1f64daa0-7e8b-4377-8652-d3de7b527c6c

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P04
namespace QAlgorithms.Papers.Independent.Bridge50.P04

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

noncomputable def s110rH (c y : ℝ) : ℝ :=
  c * (1 + y) * Real.log (c * (1 + y) + 1) - c * (1 + y) * Real.log (c * (1 + y)) -
    (y + 1) * Real.log (y + 1) + y * Real.log y

theorem s110r_rate_eq (tau e : ℝ) (h0 : 0 < tau) (h1 : tau < 1) (he : 0 ≤ e) :
    analyticRate tau e =
      (s110rH ((1 - tau) / tau) (tau * e / (2 * (1 - tau ^ 2))) - 1 - Real.log (1 - tau)) /
        Real.log 2 := by
  have h1t : 0 < 1 - tau := by linarith
  have h1t2 : 0 < 1 - tau ^ 2 := by nlinarith
  set c := (1 - tau) / tau with hc
  set y := tau * e / (2 * (1 - tau ^ 2)) with hy
  have hcpos : 0 < c := by positivity
  have hy0 : 0 ≤ y := by positivity
  have hA : ((equivalentNoise tau e / (1 + tau) - 1) - 1) / 2 = c * (1 + y) := by
    simp only [equivalentNoise, lossNoise, hc, hy]
    field_simp
    ring
  have hB : (((tau * equivalentNoise tau e - (1 + tau) ^ 2) / (1 - tau ^ 2)) - 1) / 2 = y := by
    simp only [equivalentNoise, lossNoise, hy]
    field_simp
    ring
  have hchi : equivalentNoise tau e = 2 * (1 + tau) * (c * (1 + y) + 1) := by
    rw [← hA]; field_simp; ring
  have hxpos : 0 < c * (1 + y) + 1 := by positivity
  have hlog : Real.log (2 * (1 + tau) / (Real.exp 1 * (1 - tau) * equivalentNoise tau e)) =
      -1 - Real.log (1 - tau) - Real.log (c * (1 + y) + 1) := by
    have le : Real.log (Real.exp 1 * (1 - tau)) = 1 + Real.log (1 - tau) := by
      rw [Real.log_mul (by positivity) h1t.ne', Real.log_exp]
    have l2 : Real.log (2 * (1 + tau) * (c * (1 + y) + 1)) =
        Real.log (2 * (1 + tau)) + Real.log (c * (1 + y) + 1) :=
      Real.log_mul (by positivity) (by positivity)
    have l3 : Real.log (Real.exp 1 * (1 - tau) * (2 * (1 + tau) * (c * (1 + y) + 1))) =
        Real.log (Real.exp 1 * (1 - tau)) + Real.log (2 * (1 + tau) * (c * (1 + y) + 1)) :=
      Real.log_mul (by positivity) (by positivity)
    rw [hchi, Real.log_div (by positivity) (by positivity), l3, le, l2]
    ring
  simp only [analyticRate, bosonicEntropy, logTwo]
  rw [hA, hB, hlog]
  simp only [s110rH]
  field_simp
  ring

end QAlgorithms.Papers.Independent.Bridge50.P04

theorem s110r_logbd {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 2) :
    |Real.log (1 + x) - (x - x ^ 2 / 2)| ≤ 2 * x ^ 3 ∧
    |Real.log (1 - x) - (-x - x ^ 2 / 2)| ≤ 2 * x ^ 3 := by
  have hax : |x| = x := abs_of_pos hx0
  have hlt : |x| < 1 := by rw [hax]; linarith
  have hlt' : |-x| < 1 := by rw [abs_neg, hax]; linarith
  have h1 := Real.abs_log_sub_add_sum_range_le hlt 2
  have h2 := Real.abs_log_sub_add_sum_range_le hlt' 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, hax] at h1 h2
  have hden : x ^ (2 + 1) / (1 - x) ≤ 2 * x ^ 3 := by
    rw [div_le_iff₀ (by linarith)]
    have : 0 < x ^ 3 := by positivity
    norm_num; nlinarith
  constructor
  · refine le_trans (le_of_eq ?_) (h2.trans hden)
    congr 1; push_cast; ring_nf
  · refine le_trans (le_of_eq ?_) (h1.trans hden)
    congr 1; push_cast; ring_nf

open QAlgorithms.Papers.Independent.Bridge50.P04 in
theorem solution :
    ∃ distance : ℝ, 100 < distance ∧
      0 < fiberTransmissivity distance ∧ fiberTransmissivity distance < 1 ∧
      0 < analyticRate (fiberTransmissivity distance) (1 / 50) := by
  have hT : fiberTransmissivity 150 = 1 / 1000 := by
    rw [fiberTransmissivity, show -((150 : ℝ) / 50) = -((3 : ℕ) : ℝ) by norm_num]
    change (10 : ℝ) ^ (-((3 : ℕ) : ℝ)) = 1 / 1000
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
    norm_num
  refine ⟨150, by norm_num, by rw [hT]; norm_num, by rw [hT]; norm_num, ?_⟩
  rw [hT, s110r_rate_eq _ _ (by norm_num) (by norm_num) (by norm_num)]
  apply div_pos _ (Real.log_pos (by norm_num))
  simp only [s110rH]
  set y : ℝ := 1 / 1000 * (1 / 50) / (2 * (1 - (1 / 1000) ^ 2)) with hy
  have hyv : y = 1 / 99999.9 := by rw [hy]; norm_num
  rw [hyv]
  norm_num
  have B1 : Real.log (1001010 / 1001) - Real.log (1000009 / 1001) ≥
      1001 / 1000009 - (1001 / 1000009) ^ 2 / 2 - 2 * (1001 / 1000009) ^ 3 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    have := (s110r_logbd (x := 1001 / 1000009) (by norm_num) (by norm_num)).1
    rw [abs_le] at this
    have e : (1001010 / 1001 : ℝ) / (1000009 / 1001) = 1 + 1001 / 1000009 := by norm_num
    rw [e]; linarith
  have B2 : Real.log (1000009 / 999999) ≤ 1000009 / 999999 - 1 :=
    Real.log_le_sub_one_of_pos (by norm_num)
  have hE : Real.exp 12 > 100000 := by
    have h : Real.exp 12 = Real.exp 1 ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h]
    have h1 := Real.exp_one_gt_d9
    have : (2.7 : ℝ) ^ 12 ≤ Real.exp 1 ^ 12 := pow_le_pow_left₀ (by norm_num) (by linarith) 12
    norm_num at this ⊢; linarith
  have B3 : Real.log (10 / 999999) ≥ -12 := by
    have h1 := Real.log_le_sub_one_of_pos (x := 999999 / 10 / Real.exp 12) (by positivity)
    rw [Real.log_div (by norm_num) (Real.exp_pos 12).ne', Real.log_exp] at h1
    have h2 : 999999 / 10 / Real.exp 12 ≤ 1 := by
      rw [div_le_one (Real.exp_pos 12)]; linarith
    have h3 : Real.log (10 / 999999) = - Real.log (999999 / 10) := by
      rw [← Real.log_inv]; norm_num
    linarith
  have B4 : Real.log (999 / 1000) ≤ 999 / 1000 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  nlinarith [B1, B2, B3, B4]
