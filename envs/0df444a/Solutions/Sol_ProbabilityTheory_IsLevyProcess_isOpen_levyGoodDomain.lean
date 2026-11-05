-- Prove2me | solution 1 for ProbabilityTheory.IsLevyProcess.isOpen_levyGoodDomain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T15:06:03.242923+00:00
-- url     : https://prove2.me/submissions/46b322f2-def0-4bcb-8d7e-7505c9b9ef34

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

/-! The time-one local logarithm's good domain is open. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : ProbabilityTheory.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) :
    IsOpen (h.levyGoodDomain hX) := by
  haveI : IsFiniteMeasure (μ.map (X 1)) := Measure.isFiniteMeasure_map μ (X 1)
  change IsOpen ((fun ξ : E => charFun (μ.map (X 1)) ξ) ⁻¹' Complex.slitPlane)
  exact Complex.isOpen_slitPlane.preimage MeasureTheory.continuous_charFun
