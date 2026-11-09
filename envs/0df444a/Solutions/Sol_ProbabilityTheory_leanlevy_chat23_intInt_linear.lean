-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat23_intInt_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:40:55.82837+00:00
-- url     : https://prove2.me/submissions/bb4b4444-d77d-4b49-9c77-b9e166c44691

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ENNReal Set ProbabilityTheory
open scoped NNReal ENNReal Real

theorem solution (ξ : ℝ) : ∫ u in (-1 : ℝ)..1, (ξ + u) = 2 * ξ := by
  rw [intervalIntegral.integral_comp_add_left (fun v => v) ξ, integral_id]
  ring
