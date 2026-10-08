-- Prove2me | solution 2 for Rudin.ch05_vector_mean_value
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-13T13:41:55.693107+00:00
-- url     : https://prove2.me/submissions/a1ec2ded-0dd6-4625-b714-8729040abf3c

import Mathlib

open Filter Topology

theorem solution (k : ℕ) (a b : ℝ) (hab : a < b)
    (f : ℝ → EuclideanSpace ℝ (Fin k))
    (hfc : ContinuousOn f (Set.Icc a b)) (hfd : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x) :
    ∃ x ∈ Set.Ioo a b, ‖f b - f a‖ ≤ (b - a) * ‖deriv f x‖ := by
  let d : EuclideanSpace ℝ (Fin k) := f b - f a
  by_cases hd : d = 0
  · refine ⟨(a + b) / 2, ?_, ?_⟩
    · constructor <;> linarith
    · rw [show f b - f a = d by rfl, hd, norm_zero]
      exact mul_nonneg (sub_nonneg.mpr (le_of_lt hab)) (norm_nonneg _)
  · let g : ℝ → ℝ := fun x => inner ℝ (f x) d
    have hgc : ContinuousOn g (Set.Icc a b) := by
      exact hfc.inner continuousOn_const
    have hgd : ∀ x ∈ Set.Ioo a b, HasDerivAt g (inner ℝ (deriv f x) d) x := by
      intro x hx
      simpa [g] using ((hfd x hx).hasDerivAt.inner ℝ (hasDerivAt_const x d))
    obtain ⟨x, hx, hxeq⟩ :=
      exists_hasDerivAt_eq_slope g (fun x => inner ℝ (deriv f x) d) hab hgc hgd
    have hgb : g b - g a = ‖d‖ ^ 2 := by
      dsimp [g]
      rw [← inner_sub_left]
      change inner ℝ d d = ‖d‖ ^ 2
      exact real_inner_self_eq_norm_sq d
    have hq : 0 < b - a := sub_pos.mpr hab
    have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
    have hinner : ‖d‖ ^ 2 / (b - a) ≤ ‖deriv f x‖ * ‖d‖ := by
      rw [← hgb, ← hxeq]
      exact (le_abs_self _).trans (abs_real_inner_le_norm _ _)
    have hmul : ‖d‖ ^ 2 ≤ (‖deriv f x‖ * ‖d‖) * (b - a) :=
      (div_le_iff₀ hq).mp hinner
    have hprod : ‖d‖ * ‖d‖ ≤ ‖d‖ * ((b - a) * ‖deriv f x‖) := by
      calc
        ‖d‖ * ‖d‖ = ‖d‖ ^ 2 := by ring
        _ ≤ (‖deriv f x‖ * ‖d‖) * (b - a) := hmul
        _ = ‖d‖ * ((b - a) * ‖deriv f x‖) := by ring
    refine ⟨x, hx, ?_⟩
    change ‖d‖ ≤ (b - a) * ‖deriv f x‖
    nlinarith
