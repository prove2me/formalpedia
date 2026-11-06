-- Prove2me | solution 1 for ProbabilityTheory.measurable_levyJumpPath
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:47:54.011413+00:00
-- url     : https://prove2.me/submissions/769d04fa-6f52-4600-bfb4-07a4b7dea979

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Theorems.Thm_ProbabilityTheory_measurable_levyLargeJumpSum
import Theorems.Thm_ProbabilityTheory_measurable_levySmallJumpPath
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators
variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × ℝ} {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}

theorem solution
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (b : ℝ) (t : ℝ≥0) : Measurable (levyJumpPath hd hν b t) :=
  (measurable_const.add
    (measurable_levyLargeJumpSum hd.measurable_count hd.measurable_point)).add
    (measurable_levySmallJumpPath hd hν _)
