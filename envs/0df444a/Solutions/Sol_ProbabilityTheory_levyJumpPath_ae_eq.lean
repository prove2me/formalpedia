-- Prove2me | solution 1 for ProbabilityTheory.levyJumpPath_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:47:54.97801+00:00
-- url     : https://prove2.me/submissions/9fba1528-9684-4d16-8e22-52edcde35394

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Theorems.Thm_ProbabilityTheory_levySmallJumpPath_ae_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}

theorem solution [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (b : ℝ) (t : ℝ≥0) :
    levyJumpPath hd hν b t =ᵐ[μ] levyJumpProcess hd hν b t := by
  filter_upwards [levySmallJumpPath_ae_eq hd hν (NNReal.coe_nonneg t)] with ω hω
  show b * (t : ℝ) + levyLargeJumpSum K X (t : ℝ) ω + levySmallJumpPath hd hν (t : ℝ) ω
    = b * (t : ℝ) + levyLargeJumpSum K X (t : ℝ) ω + levyCompensatedSmallJump hd hν (t : ℝ) ω
  rw [hω]
