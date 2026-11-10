-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_upperRamp_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T00:24:37.173053+00:00
-- url     : https://prove2.me/submissions/ce8fb772-c754-4457-b118-a7871dce6dda

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (x : ℝ)
    (hx : ρ ≤ |x|) : min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) = 1 := by
  have hnn : (0 : ℝ) ≤ (n + 1 : ℝ) / ρ := by positivity
  have h1 : 0 ≤ (|x| - ρ) * ((n + 1 : ℝ) / ρ) :=
    mul_nonneg (by linarith) hnn
  have h2 : 1 ≤ (|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1 := by linarith
  rw [show max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1) =
    (|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1 from max_eq_right (by linarith)]
  exact min_eq_left h2
