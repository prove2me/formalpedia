-- Prove2me | solution 1 for UCalibDirichlet.lemma_D_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:45:01.223826+00:00
-- url     : https://prove2.me/submissions/24174e4c-7dd7-44a1-a380-da5af49a5af5

import Mathlib

theorem solution (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Icc 0 1) f) :
    MonotoneOn (fun x => x * deriv f x - f x)
      {x | x ∈ Set.Ioo (0 : ℝ) 1 ∧ DifferentiableAt ℝ f x} := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with h | h
  · subst h
    exact le_rfl
  have hxS : x ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hx.1
  have hyS : y ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hy.1
  have d1 := hf.deriv_le_slope hxS hyS h hx.2
  have d2 := hf.slope_le_deriv hxS hyS h hy.2
  rw [slope_def_field] at d1 d2
  have hyx : 0 < y - x := by linarith
  rw [le_div_iff₀ hyx] at d1
  rw [div_le_iff₀ hyx] at d2
  have hm : deriv f x ≤ deriv f y := by
    by_contra hc
    push_neg at hc
    nlinarith
  have hx0 : 0 < x := hx.1.1
  simp only
  nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr hm)]
