-- Prove2me | solution 1 for ProbabilityTheory.IsCompoundPoissonDriver.iIndepFun_interarrival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T19:24:49.338409+00:00
-- url     : https://prove2.me/submissions/1a89e2bc-3696-44a4-8f53-0cde93a69134

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
    iIndepFun τ μ := by
  have h' := h.indep.precomp (g := Sum.inl) Sum.inl_injective
  simpa [Function.comp] using h'