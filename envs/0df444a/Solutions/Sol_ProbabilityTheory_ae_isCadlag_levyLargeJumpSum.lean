-- Prove2me | solution 1 for ProbabilityTheory.ae_isCadlag_levyLargeJumpSum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:07:33.377189+00:00
-- url     : https://prove2.me/submissions/39a2e562-e33e-460a-b790-0cced1a25ca3

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Theorems.Thm_ProbabilityTheory_ae_isCadlag_bandJumpSum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Complex ComplexConjugate Set Filter Topology Finset ProbabilityTheory
open scoped NNReal ENNReal
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν]
  {μ : Measure Ω} {A : Set ℝ}

theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν) :
    ∀ᵐ ω ∂μ, IsCadlag (fun t : ℝ => levyLargeJumpSum K X t ω) := by
  have h := ae_isCadlag_bandJumpSum hd
    (measurableSet_le measurable_const continuous_abs.measurable)
    (hν.measure_setOf_abs_ge_lt_top one_pos)
  filter_upwards [h] with ω hω
  change IsCadlag (fun t : ℝ => bandJumpSum K X {x : ℝ | 1 ≤ |x|} t ω)
  exact hω