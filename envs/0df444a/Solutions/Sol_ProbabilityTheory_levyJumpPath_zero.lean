-- Prove2me | solution 1 for ProbabilityTheory.levyJumpPath_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:13:31.517887+00:00
-- url     : https://prove2.me/submissions/127ff174-ff46-4f70-ba68-9da8a0b749cd

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Theorems.Thm_ProbabilityTheory_levyLargeJumpSum_zero
import Theorems.Thm_ProbabilityTheory_levySmallJumpPath_zero
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν]
  {μ : Measure Ω} {A : Set ℝ}

theorem solution
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hν : IsLevyMeasure ν) (b : ℝ) :
    levyJumpPath hd hν b 0 = fun _ => 0 := by
  funext ω
  simp only [levyJumpPath, NNReal.coe_zero, mul_zero, levyLargeJumpSum_zero,
    levySmallJumpPath_zero, Pi.zero_apply, add_zero]
