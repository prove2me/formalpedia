-- Prove2me | solution 1 for ProbabilityTheory.IsLevyProcess.continuousOn_levyLocalCharExponent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T15:06:07.750506+00:00
-- url     : https://prove2.me/submissions/3674108d-91ba-49c5-8117-5baeccb3df59

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Normed.Module.Connected
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Topology ProbabilityTheory
open scoped NNReal
universe u v

/-! Exact original LeanLevy local-exponent continuity proof. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : ProbabilityTheory.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) :
    ContinuousOn (h.levyLocalCharExponent hX) (h.levyGoodDomain hX) := by
  haveI : IsFiniteMeasure (μ.map (X 1)) := Measure.isFiniteMeasure_map μ (X 1)
  change ContinuousOn (fun ξ : E => Complex.log (charFun (μ.map (X 1)) ξ))
    ((fun ξ : E => charFun (μ.map (X 1)) ξ) ⁻¹' Complex.slitPlane)
  exact (MeasureTheory.continuous_charFun :
    Continuous (fun ξ : E => charFun (μ.map (X 1)) ξ)).continuousOn.clog
    (fun _ hx => hx)
