-- Prove2me | solution 1 for ProbabilityTheory.IsLevyProcess.continuous_levyExpFormula_t
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:38:14.404865+00:00
-- url     : https://prove2.me/submissions/b746c9f0-26ee-4b2e-a440-8d3c7c27a290

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) (ξ : E) :
    Continuous (fun t : ℝ≥0 => h.levyExpFormula hX t ξ) := by
  simp only [IsLevyProcess.levyExpFormula]
  exact continuous_exp.comp
    ((continuous_ofReal.comp NNReal.continuous_coe).mul continuous_const)
