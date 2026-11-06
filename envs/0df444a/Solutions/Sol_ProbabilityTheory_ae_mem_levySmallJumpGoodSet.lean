-- Prove2me | solution 1 for ProbabilityTheory.ae_mem_levySmallJumpGoodSet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:27:48.525015+00:00
-- url     : https://prove2.me/submissions/01024012-257c-4052-b6c1-f71917a5967c

import Init
import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Theorems.Thm_ProbabilityTheory_ae_levySmallJumpRaw
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν]
  {μ : Measure Ω} {A : Set ℝ}

theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν) :
    ∀ᵐ ω ∂μ, ω ∈ levySmallJumpGoodSet hd hν := by
  rw [ae_iff]
  have hset : {ω | ω ∉ levySmallJumpGoodSet hd hν}
      = MeasureTheory.toMeasurable μ {ω | ¬ levySmallJumpRaw hd hν ω} := by
    ext ω; simp only [levySmallJumpGoodSet, Set.mem_setOf_eq, Set.mem_compl_iff, not_not]
  rw [hset, measure_toMeasurable]
  exact ae_iff.mp (ae_levySmallJumpRaw hd hν)
