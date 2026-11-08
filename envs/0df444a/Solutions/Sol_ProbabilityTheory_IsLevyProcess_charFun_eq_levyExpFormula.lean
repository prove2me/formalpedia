-- Prove2me | solution 1 for ProbabilityTheory.IsLevyProcess.charFun_eq_levyExpFormula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:38:10.302029+00:00
-- url     : https://prove2.me/submissions/989ebf58-6e54-4756-9233-899b1f2be194

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_charFun_eq_exp_mul

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
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t))
    (t : ℝ≥0) (ξ : E) :
    charFun (μ.map (X t)) ξ = h.levyExpFormula hX t ξ := by
  exact h.charFun_eq_exp_mul hX t ξ
