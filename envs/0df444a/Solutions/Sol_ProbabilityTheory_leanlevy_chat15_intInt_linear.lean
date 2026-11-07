-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat15_intInt_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:16:29.541781+00:00
-- url     : https://prove2.me/submissions/12d57b5f-5ef5-402f-ab78-154c3dda5549

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- Source-exact first moment of a translated symmetric interval. -/
theorem solution (ξ : ℝ) :
    ∫ u in (-1 : ℝ)..1, (ξ + u) = 2 * ξ := by
  rw [intervalIntegral.integral_comp_add_left (fun v => v) ξ, integral_id]
  ring
