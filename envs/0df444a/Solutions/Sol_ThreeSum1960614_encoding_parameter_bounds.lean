-- Prove2me | solution 1 for ThreeSum1960614.encoding_parameter_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-14T07:17:38.006825+00:00
-- url     : https://prove2.me/submissions/03e9ef10-def9-4e26-a45c-499b29ed4a7b

import Theorems.Thm_ThreeSum1960614_high_precision_logs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 5000000
open ThreeSum1960614

private theorem entropy_eq (t : ℝ) :
    entropy t = (-t * Real.log t - (1 - t) * Real.log (1 - t)) / Real.log 2 := by
  simp only [entropy, Real.binEntropy, Real.log_inv]
  ring

private theorem scaled_entropy (c : ℝ) (hc : 1 < c) :
    c * entropy (1 / c) = (Real.log c + (c - 1) * Real.log (c / (c - 1))) / Real.log 2 := by
  have hcn : c ≠ 0 := by linarith
  have hcm : c - 1 ≠ 0 := by linarith
  have hln : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  rw [entropy_eq]
  rw [show 1 - 1 / c = (c - 1) / c by field_simp <;> ring]
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hcn,
      Real.log_div hcm hcn, Real.log_div hcn hcm]
  simp only [Real.log_one]
  field_simp [hcn, hcm, hln]
  <;> ring

private theorem log_232 : Real.log (232 : ℝ) = 7 * Real.log 2 + Real.log (29 / 16) := by
  have h128 : Real.log (128 : ℝ) = 7 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 7
    norm_num at h
    exact h
  rw [show (232 : ℝ) = 128 * (29 / 16) by norm_num,
      Real.log_mul (by norm_num : (128 : ℝ) ≠ 0) (by norm_num : (29 / 16 : ℝ) ≠ 0), h128]

private theorem E_formula :
    E 232 = (7 * Real.log 2 + Real.log (29 / 16) + 231 * Real.log (232 / 231)) /
      (2 * Real.log 2) := by
  have h := scaled_entropy (232 : ℝ) (by norm_num)
  norm_num at h
  unfold E
  norm_num only [Nat.cast_ofNat]
  calc
    (116 : ℝ) * entropy (1 / 232) = (232 * entropy (1 / 232)) / 2 := by ring
    _ = (7 * Real.log 2 + Real.log (29 / 16) + 231 * Real.log (232 / 231)) /
        (2 * Real.log 2) := by rw [h, log_232]; ring

private theorem kappa_formula :
    kappa 232 = (463 * Real.log (464 / 463) - 231 * Real.log (232 / 231)) / Real.log 2 := by
  have h232 := scaled_entropy (232 : ℝ) (by norm_num)
  have h464 := scaled_entropy (464 : ℝ) (by norm_num)
  norm_num at h232 h464
  have hlog : Real.log (464 : ℝ) = Real.log 2 + Real.log 232 := by
    rw [show (464 : ℝ) = 2 * 232 by norm_num,
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (232 : ℝ) ≠ 0)]
  have hln : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hraw : kappa 232 = 464 * entropy (1 / 464) - 232 * entropy (1 / 232) - 1 := by
    norm_num [kappa]
  rw [hraw, h464, h232, hlog]
  field_simp [hln]
  <;> ring

theorem solution :
    4648781151243719 / 1000000000000000 < E 232 ∧
    E 232 < 4648781151243720 / 1000000000000000 ∧
    1557987216578 / 1000000000000000 < kappa 232 ∧
    kappa 232 < 1557987216579 / 1000000000000000 := by
  obtain ⟨hl, hm, hp, hq, _, _⟩ := ThreeSum1960614.high_precision_logs
  have hln : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [E_formula]
    apply (lt_div_iff₀ (by positivity : 0 < 2 * Real.log 2)).2
    have hn : (2 * (4648781151243719 / 1000000000000000 : ℝ) - 7) *
        (6931471805599453094173 / 10^22) <
        5947071077466927895143 / 10^22 + 231 * (43196611445164148724 / 10^22) := by norm_num
    nlinarith only [hl.2, hm.1, hp.1, hn]
  · rw [E_formula]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.log 2)).2
    have hn : (5947071077466927895144 / 10^22 : ℝ) + 231 * (43196611445164148725 / 10^22) <
        (2 * (4648781151243720 / 1000000000000000) - 7) * (6931471805599453094172 / 10^22) := by norm_num
    nlinarith only [hl.1, hm.2, hp.2, hn]
  · rw [kappa_formula]
    apply (lt_div_iff₀ hln).2
    have hn : (1557987216578 / 1000000000000000 : ℝ) * (6931471805599453094173 / 10^22) <
        463 * (21574981400211907723 / 10^22) - 231 * (43196611445164148725 / 10^22) := by norm_num
    nlinarith only [hl.2, hq.1, hp.2, hn]
  · rw [kappa_formula]
    apply (div_lt_iff₀ hln).2
    have hn : (463 * (21574981400211907724 / 10^22) - 231 * (43196611445164148724 / 10^22) : ℝ) <
        (1557987216579 / 1000000000000000) * (6931471805599453094172 / 10^22) := by norm_num
    nlinarith only [hl.1, hq.2, hp.1, hn]
