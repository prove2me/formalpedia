-- Prove2me | solution 1 for ProbabilityTheory.charFun_poissonMeasure_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:59:16.276781+00:00
-- url     : https://prove2.me/submissions/4fdd8e09-8ac0-4f19-a1a1-ba8a152e5803

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_LeanLevy_Probability_Characteristic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal NNReal Nat
open MeasureTheory Real Complex Finset ProbabilityTheory

theorem solution (r : ℝ≥0) (ξ : ℝ) :
    charFun ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) ξ =
    cexp (↑(r : ℝ) * (cexp (↑ξ * I) - 1)) := by
  rw [charFun_map_cast_poissonMeasure r ξ]
