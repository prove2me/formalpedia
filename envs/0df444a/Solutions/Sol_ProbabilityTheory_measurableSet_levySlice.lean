-- Prove2me | solution 1 for ProbabilityTheory.measurableSet_levySlice
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:11:56.903364+00:00
-- url     : https://prove2.me/submissions/1831787b-850a-4988-b808-960fe29e378c

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν]
  {μ : Measure Ω} {A : Set ℝ}

theorem solution (hν : IsLevyMeasure ν) (j : ℕ) :
    MeasurableSet (levySlice hν j) := by
  exact (measurableSet_levyAnnulus _).diff (measurableSet_levyAnnulus _)
