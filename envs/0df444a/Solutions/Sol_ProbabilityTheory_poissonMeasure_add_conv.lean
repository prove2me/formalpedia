-- Prove2me | solution 1 for ProbabilityTheory.poissonMeasure_add_conv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:59:10.037751+00:00
-- url     : https://prove2.me/submissions/e31317b3-c9cd-4985-a8c3-084d8adedd79

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Group.Convolution

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal NNReal Nat
open MeasureTheory Real Complex Finset ProbabilityTheory

theorem solution (a b : ℝ≥0) :
    ((poissonMeasure a).prod (poissonMeasure b)).map
      (fun p : ℕ × ℕ => p.1 + p.2) = poissonMeasure (a + b) := by
  exact poissonMeasure_conv_poissonMeasure a b
