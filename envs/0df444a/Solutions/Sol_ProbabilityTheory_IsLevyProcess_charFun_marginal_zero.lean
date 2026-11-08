-- Prove2me | solution 1 for ProbabilityTheory.IsLevyProcess.charFun_marginal_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:21:41.6472+00:00
-- url     : https://prove2.me/submissions/36237195-bb36-4baa-a2b8-36c7bf3cb538

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_LeanLevy_Processes_LevyProcess

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsLevyProcess X μ) (ξ : E) :
    charFun (μ.map (X 0)) ξ = 1 := by
  have hmap : μ.map (X 0) = Measure.dirac (0 : E) := by
    rw [h.start_zero, Measure.map_const, measure_univ, one_smul]
  rw [hmap, charFun_dirac, inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
