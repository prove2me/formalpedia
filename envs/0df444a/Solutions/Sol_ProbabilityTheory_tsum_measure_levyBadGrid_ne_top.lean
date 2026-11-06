-- Prove2me | solution 1 for ProbabilityTheory.tsum_measure_levyBadGrid_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:27:49.428042+00:00
-- url     : https://prove2.me/submissions/1137ad0f-780c-409c-94d7-b321efc8654f

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
import Theorems.Thm_ProbabilityTheory_measure_levyBadGrid_le
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν]
  {μ : Measure Ω} {A : Set ℝ}

theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν) (T : ℕ) :
    (∑' j, μ (levyBadGrid hd hν T j)) ≠ ⊤ := by
  have hsummable : Summable (fun j : ℕ => Real.sqrt (T : ℝ) * ((2 : ℝ)⁻¹) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hle : (∑' j, μ (levyBadGrid hd hν T j))
      ≤ ∑' j, ENNReal.ofReal (Real.sqrt (T : ℝ) * ((2 : ℝ)⁻¹) ^ j) :=
    ENNReal.tsum_le_tsum (measure_levyBadGrid_le hd hν T)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsummable] at hle
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
