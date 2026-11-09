-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat23_intInt_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:41:02.169658+00:00
-- url     : https://prove2.me/submissions/c94844dc-a738-4285-95e1-43be241c4f50

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ENNReal Set ProbabilityTheory
open scoped NNReal ENNReal Real

theorem solution (ξ : ℝ) : ∫ u in (-1 : ℝ)..1, (ξ + u) ^ 2 = 2 * ξ ^ 2 + 2 / 3 := by
  rw [intervalIntegral.integral_comp_add_left (fun v => v ^ 2) ξ, integral_pow]
  ring
