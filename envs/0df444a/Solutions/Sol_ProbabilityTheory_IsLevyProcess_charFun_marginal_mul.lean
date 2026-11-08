-- Prove2me | solution 1 for ProbabilityTheory.IsLevyProcess.charFun_marginal_mul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:37:51.765044+00:00
-- url     : https://prove2.me/submissions/6b793190-7b24-4c52-9f36-bdc2a0a8d73c

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_charFun_eq_exp_mul

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ProbabilityTheory MeasureTheory Complex
open scoped NNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t))
    (s t : ℝ≥0) (ξ : E) :
    charFun (μ.map (X (s + t))) ξ =
      charFun (μ.map (X s)) ξ * charFun (μ.map (X t)) ξ := by
  rw [h.charFun_eq_exp_mul hX (s + t) ξ,
    h.charFun_eq_exp_mul hX s ξ,
    h.charFun_eq_exp_mul hX t ξ, ← exp_add]
  congr 1
  push_cast [NNReal.coe_add]
  ring
