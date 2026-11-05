-- Prove2me | solution 1 for ProbabilityTheory.IsLevyProcess.charFun_one_near_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T15:03:34.625672+00:00
-- url     : https://prove2.me/submissions/566d14fd-1f14-4220-8a43-d3bf3855530c

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Topology
open scoped NNReal
universe u v

/-! Characteristic-function convergence at the origin, source exact. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (_h : ProbabilityTheory.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) :
    Tendsto (fun ξ => charFun (μ.map (X 1)) ξ) (𝓝 0) (𝓝 1) := by
  haveI : IsFiniteMeasure (μ.map (X 1)) := Measure.isFiniteMeasure_map μ (X 1)
  have hc : Continuous (fun ξ : E => charFun (μ.map (X 1)) ξ) :=
    MeasureTheory.continuous_charFun
  haveI : IsProbabilityMeasure (μ.map (X 1)) :=
    Measure.isProbabilityMeasure_map (hX 1).aemeasurable
  have hz : charFun (μ.map (X 1)) (0 : E) = 1 := by
    simp [charFun_zero]
  have ht : Tendsto (fun ξ : E => charFun (μ.map (X 1)) ξ)
      (𝓝 (0 : E)) (𝓝 (charFun (μ.map (X 1)) (0 : E))) :=
    hc.continuousAt.tendsto
  simpa only [hz] using ht
