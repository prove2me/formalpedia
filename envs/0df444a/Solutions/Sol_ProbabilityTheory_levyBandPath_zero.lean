-- Prove2me | solution 1 for ProbabilityTheory.levyBandPath_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:03:11.443159+00:00
-- url     : https://prove2.me/submissions/b14f2c79-6917-4931-a840-2457aeb5e777

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Notation.Indicator
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω} {A : Set ℝ}

theorem solution : levyBandPath K X ν A 0 = 0 := by
  funext ω
  have hband : ((Set.Ioc (0 : ℝ) 0 ×ˢ A).indicator fun p : ℝ × ℝ => p.2) =
      fun _ => 0 := by
    rw [Set.Ioc_self, Set.empty_prod, Set.indicator_empty]
  simp only [levyBandPath, zero_mul, sub_zero, bandJumpSum, hband,
    pieceSum, Finset.sum_const_zero, tsum_zero, Pi.zero_apply]
