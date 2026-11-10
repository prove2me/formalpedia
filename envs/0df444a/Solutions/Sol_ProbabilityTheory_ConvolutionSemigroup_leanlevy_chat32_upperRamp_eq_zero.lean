-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_upperRamp_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T00:24:43.092317+00:00
-- url     : https://prove2.me/submissions/cc1f0b00-fa4d-4da0-97a8-a757ce500401

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (x : ℝ)
    (hx : |x| ≤ ρ - ρ / (n + 1 : ℝ)) : min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) = 0 := by
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hslope : (0 : ℝ) < (n + 1 : ℝ) / ρ := by positivity
  have hbnd : (|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1 ≤ 0 := by
    have h1 : |x| - ρ ≤ -(ρ / (n + 1 : ℝ)) := by linarith
    have h2 : (|x| - ρ) * ((n + 1 : ℝ) / ρ) ≤
        -(ρ / (n + 1 : ℝ)) * ((n + 1 : ℝ) / ρ) :=
      mul_le_mul_of_nonneg_right h1 hslope.le
    rw [show -(ρ / (n + 1 : ℝ)) * ((n + 1 : ℝ) / ρ) = -1 from by field_simp] at h2
    linarith
  rw [show max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1) = 0 from max_eq_left hbnd]
  exact min_eq_right zero_le_one
