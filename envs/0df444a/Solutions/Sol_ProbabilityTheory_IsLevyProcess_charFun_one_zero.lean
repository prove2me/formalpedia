-- Prove2me | solution 1 for ProbabilityTheory.IsLevyProcess.charFun_one_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:52:27.649025+00:00
-- url     : https://prove2.me/submissions/b7c2e2f0-c464-4ed7-87ba-9cf072d118aa

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Topology
open scoped NNReal
universe u v

/-! Original LeanLevy time-one characteristic function at zero. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (_h : ProbabilityTheory.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) :
    charFun (μ.map (X 1)) (0 : E) = 1 := by
  haveI : IsProbabilityMeasure (μ.map (X 1)) :=
    Measure.isProbabilityMeasure_map (hX 1).aemeasurable
  simp [charFun_zero]
