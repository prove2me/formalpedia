-- Prove2me | solution 1 for Rudin.ch05_vector_mean_value
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-13T13:19:31.176261+00:00
-- url     : https://prove2.me/submissions/4dc36dd0-abaf-402a-9cca-cc16c9dadfb1

import Mathlib
import Theorems.Thm_Rudin_ch05_vector_mean_value_nonzero

open Filter Topology

theorem solution (k : ℕ) (a b : ℝ) (hab : a < b)
    (f : ℝ → EuclideanSpace ℝ (Fin k))
    (hfc : ContinuousOn f (Set.Icc a b)) (hfd : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x) :
    ∃ x ∈ Set.Ioo a b, ‖f b - f a‖ ≤ (b - a) * ‖deriv f x‖ := by
  by_cases hzero : f b - f a = 0
  · refine ⟨(a + b) / 2, ?_, ?_⟩
    · constructor <;> linarith
    · rw [hzero, norm_zero]
      exact mul_nonneg (sub_nonneg.mpr (le_of_lt hab)) (norm_nonneg _)
  · exact Rudin.ch05_vector_mean_value_nonzero k a b hab f hfc hfd hzero
