-- Prove2me | solution 1 for ProbabilityTheory.IsLevyProcess.continuous_charFun_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T15:03:29.809133+00:00
-- url     : https://prove2.me/submissions/1a305aa1-89f8-4046-8535-ba10ba569623

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Topology
open scoped NNReal
universe u v

/-! Original source proof for continuity of the time-one characteristic function. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (_hX : ∀ t, Measurable (X t)) :
    Continuous (fun ξ => charFun (μ.map (X 1)) ξ) := by
  haveI : IsFiniteMeasure (μ.map (X 1)) := Measure.isFiniteMeasure_map μ (X 1)
  exact MeasureTheory.continuous_charFun
