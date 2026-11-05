-- Prove2me | solution 1 for ProbabilityTheory.IsLevyProcess.charExponent_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:40:43.462196+00:00
-- url     : https://prove2.me/submissions/5f6ee886-1273-42d7-978b-99f16aa748e3

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Topology ProbabilityTheory
open scoped NNReal
universe u v

/-! Exact upstream source theorem: characteristic exponent at the origin. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : ProbabilityTheory.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) :
    h.charExponent (0 : E) = 0 := by
  simp only [ProbabilityTheory.IsLevyProcess.charExponent]
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have hchar : charFun (μ.map (X t)) (0 : E) = 1 := by
    haveI : IsProbabilityMeasure (μ.map (X t)) :=
      Measure.isProbabilityMeasure_map (hX t).aemeasurable
    simp [charFun_zero]
  rw [hchar, Complex.log_one, zero_div]
