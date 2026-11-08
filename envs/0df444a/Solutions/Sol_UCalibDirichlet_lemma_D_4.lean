-- Prove2me | solution 1 for UCalibDirichlet.lemma_D_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:48:35.297566+00:00
-- url     : https://prove2.me/submissions/1c43f186-bd55-4b77-ad56-9ac121a18c5a

import Mathlib

theorem solution (f : ℝ → ℝ) (hf : ConvexOn ℝ (Set.Icc 0 1) f) :
    MonotoneOn (fun x => f x + (1 - x) * deriv f x)
      {x | x ∈ Set.Ioo (0 : ℝ) 1 ∧ DifferentiableAt ℝ f x} := by
  rintro x ⟨hx, hdx⟩ y ⟨hy, hdy⟩ hxy
  rcases eq_or_lt_of_le hxy with h | h
  · exact le_of_eq (by rw [h])
  have hxS : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hx
  have hyS : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
  have h1 := hf.deriv_le_slope hxS hyS h hdx
  have h2 := hf.slope_le_deriv hxS hyS h hdy
  rw [slope_def_field] at h1 h2
  have hyx : 0 < y - x := by linarith
  have hs : f y - f x = (f y - f x) / (y - x) * (y - x) := by rw [div_mul_cancel₀ _ hyx.ne']
  have e1 : deriv f x * (y - x) ≤ (f y - f x) / (y - x) * (y - x) :=
    mul_le_mul_of_nonneg_right h1 hyx.le
  have e2 : (1 - y) * deriv f x ≤ (1 - y) * deriv f y :=
    mul_le_mul_of_nonneg_left (h1.trans h2) (by linarith [hy.2])
  show f x + (1 - x) * deriv f x ≤ f y + (1 - y) * deriv f y
  nlinarith
