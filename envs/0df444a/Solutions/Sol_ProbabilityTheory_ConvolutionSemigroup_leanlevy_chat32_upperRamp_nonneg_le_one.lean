-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_upperRamp_nonneg_le_one
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T02:43:50.081716+00:00
-- url     : https://prove2.me/submissions/47657d18-a790-4315-84b8-bdba3c27324e

import Mathlib.Data.Real.Basic

theorem solution (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (x : ℝ) :
    0 ≤ min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) ∧
    min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) ≤ 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩
