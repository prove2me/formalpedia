-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat15_compensated_smear_algebra
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:21:21.807721+00:00
-- url     : https://prove2.me/submissions/5f9acb55-b129-4948-86bd-83600ead25a8

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- Cancellation of constant and linear compensators in a symmetric Fourier smear. -/
theorem solution (E L : ℂ) (s : ℝ) :
    (E - 1 - L) - (1 / 2 : ℂ) *
      (E * (2 * (s : ℂ)) - 2 - L * (2 : ℂ))
      = E * (1 - (s : ℂ)) := by
  ring
