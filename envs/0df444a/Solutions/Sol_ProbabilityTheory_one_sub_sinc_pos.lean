-- Prove2me | solution 1 for ProbabilityTheory.one_sub_sinc_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:47:13.181015+00:00
-- url     : https://prove2.me/submissions/32df563c-53c1-4899-b92a-d876adefe559

import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Probability.ConditionalProbability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ProbabilityTheory
open scoped Real

/-- Sinc is strictly less than one away from the origin. -/
theorem solution : ∀ {x : ℝ}, x ≠ 0 → 0 < 1 - Real.sinc x := by
  intro x hx
  rw [Real.sinc_of_ne_zero hx,
      show (1 : ℝ) - Real.sin x / x = (x - Real.sin x) / x from by field_simp, div_pos_iff]
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · right
    refine ⟨?_, hneg⟩
    have h := Real.sin_lt (neg_pos.mpr hneg)
    rw [Real.sin_neg] at h
    linarith
  · exact Or.inl ⟨by linarith [Real.sin_lt hpos], hpos⟩
