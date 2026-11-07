-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat15_intInt_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:06:15.95749+00:00
-- url     : https://prove2.me/submissions/6c42478d-3157-424e-b627-30960e0866b1

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- Symmetric second moment of a translated interval, from the original source. -/
theorem solution (ξ : ℝ) :
    ∫ u in (-1 : ℝ)..1, (ξ + u) ^ 2 = 2 * ξ ^ 2 + 2 / 3 := by
  rw [intervalIntegral.integral_comp_add_left (fun v => v ^ 2) ξ, integral_pow]
  ring
