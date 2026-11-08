-- Prove2me | solution 1 for ProbabilityTheory.IsLevyProcess.charFun_marginal_rat_pow
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:37:47.783824+00:00
-- url     : https://prove2.me/submissions/b0fcdab1-65d9-4f28-b7a9-b4d9e51d98b9

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
    (k n : ℕ) (ξ : E) :
    charFun (μ.map (X ((k : ℝ≥0) / (n : ℝ≥0)))) ξ =
      (charFun (μ.map (X ((1 : ℝ≥0) / (n : ℝ≥0)))) ξ) ^ k := by
  rw [h.charFun_eq_exp_mul hX _ ξ,
    h.charFun_eq_exp_mul hX _ ξ, ← exp_nat_mul]
  congr 1
  push_cast
  ring
