-- Prove2me | solution 1 for ProcessingNetworks.EntropyIneq.lemma_B_15
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:54:46.492146+00:00
-- url     : https://prove2.me/submissions/dde4151d-b2de-4c33-9bf2-09e4367ac015

import Mathlib

theorem solution :
    ContinuousWithinAt (fun x : ℝ => x * Real.log x) (Set.Ici 0) 0 ∧
      (∀ x ∈ Set.Ioo (0 : ℝ) 1, x * Real.log x < 0) ∧
      IsGLB ((fun x : ℝ => x * Real.log x) '' Set.Ici 0) (-(1 / Real.exp 1)) := by
  have hlow : ∀ x : ℝ, 0 ≤ x → -(1 / Real.exp 1) ≤ x * Real.log x := by
    intro x hx
    rcases hx.eq_or_lt with h | h
    · rw [← h, zero_mul]
      exact neg_nonpos.mpr (by positivity)
    · have hy : 0 < Real.exp (-1) / x := div_pos (Real.exp_pos _) h
      have h1 := Real.log_le_sub_one_of_pos hy
      rw [Real.log_div (Real.exp_pos _).ne' h.ne', Real.log_exp] at h1
      have h2 : -Real.log x ≤ Real.exp (-1) / x := by linarith
      have h3 : x * (-Real.log x) ≤ x * (Real.exp (-1) / x) :=
        mul_le_mul_of_nonneg_left h2 h.le
      rw [mul_div_cancel₀ _ h.ne'] at h3
      rw [one_div, ← Real.exp_neg]
      linarith
  refine ⟨Real.continuous_mul_log.continuousWithinAt, ?_, ?_⟩
  · rintro x ⟨hx0, hx1⟩
    exact mul_neg_of_pos_of_neg hx0 (Real.log_neg hx0 hx1)
  · apply IsLeast.isGLB
    refine ⟨⟨Real.exp (-1), (Real.exp_pos _).le, ?_⟩, ?_⟩
    · show Real.exp (-1) * Real.log (Real.exp (-1)) = -(1 / Real.exp 1)
      rw [Real.log_exp, one_div, ← Real.exp_neg]
      ring
    · rintro _ ⟨x, hx, rfl⟩
      exact hlow x hx
