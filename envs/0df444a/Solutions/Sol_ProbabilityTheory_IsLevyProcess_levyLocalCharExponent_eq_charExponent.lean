-- Prove2me | solution 1 for ProbabilityTheory.IsLevyProcess.levyLocalCharExponent_eq_charExponent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T13:06:45.467193+00:00
-- url     : https://prove2.me/submissions/508de190-bbaa-4877-8f1c-c3a4d3954917

import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Normed.Module.Connected
import Theorems.Thm_levy_foundations_levyLocalCharExponent_eq_charExponent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableAdd₂ E]
  {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Source-compatible original local exponent lemma from accepted foundational adapter. -/
theorem solution (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) :
    ∃ ε > 0, ∀ ξ ∈ Metric.ball (0 : E) ε,
      h.levyLocalCharExponent hX ξ = h.charExponent ξ := by
  have h' : LevyFoundations.IsLevyProcess X μ := by
    exact ⟨h.start_zero, h.indep_increments, h.stationary_increments, h.cadlag_ae⟩
  obtain ⟨ε, hε, hball⟩ :=
    levy_foundations_levyLocalCharExponent_eq_charExponent h' hX
  refine ⟨ε, hε, fun ξ hξ => ?_⟩
  simpa [IsLevyProcess.levyLocalCharExponent, LevyFoundations.levyLocalCharExponent,
    LocalLog.localCharExponent, LevyFoundations.LocalLog.localCharExponent,
    IsLevyProcess.charExponent, LevyFoundations.charExponent] using hball ξ hξ
