-- Prove2me | solution 1 for ProbabilityTheory.IsLevyProcess.mem_levyGoodDomain_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:59:57.088412+00:00
-- url     : https://prove2.me/submissions/2779ae77-2df9-49d3-a6be-bbe507ef8b02

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Topology
open scoped NNReal
universe u v

/-! The time-one local logarithm's good domain contains zero. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : ProbabilityTheory.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) :
    (0 : E) ∈ h.levyGoodDomain hX := by
  haveI : IsProbabilityMeasure (μ.map (X 1)) :=
    Measure.isProbabilityMeasure_map (hX 1).aemeasurable
  have hz : charFun (μ.map (X 1)) (0 : E) = 1 := by
    simp [charFun_zero]
  change charFun (μ.map (X 1)) (0 : E) ∈ Complex.slitPlane
  simpa only [hz] using Complex.one_mem_slitPlane
