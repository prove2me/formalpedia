-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.potts_segment_metric
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:28:58.730781+00:00
-- url     : https://prove2.me/submissions/e815f3cc-ca8c-463d-b917-64a20b3f4078

import Mathlib
set_option autoImplicit false

theorem solution (β : ℂ) (s t : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ‖(1+(t:ℂ)*(β-1))-(1+(s:ℂ)*(β-1))‖ ≤ ‖β-1‖ ∧
      1-‖β-1‖ ≤ ‖1+(s:ℂ)*(β-1)‖ := by
  have habs : |t-s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1,hs.2,ht.1,ht.2]
  have hdiff : (1+(t:ℂ)*(β-1))-(1+(s:ℂ)*(β-1)) = ((t-s:ℝ):ℂ)*(β-1) := by push_cast; ring
  constructor
  · rw [hdiff,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    nlinarith [mul_nonneg (show 0 ≤ 1-|t-s| by linarith) (norm_nonneg (β-1))]
  · have hh := norm_sub_norm_le (1:ℂ) (1+(s:ℂ)*(β-1))
    have hid : (1:ℂ)-(1+(s:ℂ)*(β-1)) = -(s:ℂ)*(β-1) := by ring
    rw [norm_one,hid,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs.1] at hh
    nlinarith [mul_nonneg (show 0 ≤ 1-s by linarith [hs.2]) (norm_nonneg (β-1))]
