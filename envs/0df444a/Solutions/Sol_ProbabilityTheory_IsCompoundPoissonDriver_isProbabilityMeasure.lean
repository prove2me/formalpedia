-- Prove2me | solution 1 for ProbabilityTheory.IsCompoundPoissonDriver.isProbabilityMeasure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:25:01.524051+00:00
-- url     : https://prove2.me/submissions/c620fd94-4b2d-472e-a8f6-77e79ddb8a13

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_LeanLevy_Processes_PiecewisePath
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.BorelCantelli

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω}
    (h : IsCompoundPoissonDriver τ Y r ν' μ) :
    IsProbabilityMeasure μ := by
  exact h.indep.isProbabilityMeasure