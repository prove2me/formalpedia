-- Prove2me | solution 1 for ProbabilityTheory.IsLevyProcess.charFun_marginal_nat_mul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:37:54.599369+00:00
-- url     : https://prove2.me/submissions/88d9e0f8-faec-411d-acc5-40910201ec89

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
    (n : ℕ) (s : ℝ≥0) (ξ : E) :
    charFun (μ.map (X ((n : ℝ≥0) * s))) ξ =
      (charFun (μ.map (X s)) ξ) ^ n := by
  rw [h.charFun_eq_exp_mul hX ((n : ℝ≥0) * s) ξ,
    h.charFun_eq_exp_mul hX s ξ, ← exp_nat_mul]
  congr 1
  push_cast
  ring
