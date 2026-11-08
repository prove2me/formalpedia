-- Prove2me | solution 1 for ProbabilityTheory.IsLevyProcess.continuous_charFun_marginal_t
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:38:06.07948+00:00
-- url     : https://prove2.me/submissions/65363d32-ebd8-4a68-9130-4967ce3b0ec2

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
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) (ξ : E) :
    Continuous (fun t : ℝ≥0 => charFun (μ.map (X t)) ξ) := by
  have hid : (fun t => charFun (μ.map (X t)) ξ) =
      (fun t => h.levyExpFormula hX t ξ) := by
    funext t
    exact h.charFun_eq_exp_mul hX t ξ
  rw [hid]
  simp only [IsLevyProcess.levyExpFormula]
  exact continuous_exp.comp
    ((continuous_ofReal.comp NNReal.continuous_coe).mul continuous_const)
