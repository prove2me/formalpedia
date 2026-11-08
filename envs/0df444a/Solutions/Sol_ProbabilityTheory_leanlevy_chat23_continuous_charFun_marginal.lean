-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat23_continuous_charFun_marginal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:01:07.651478+00:00
-- url     : https://prove2.me/submissions/2647bdb6-a00a-4358-85f3-5b0c21cc9921

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_charFun_eq_exp_mul

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

/-- The original Lévy characteristic-function continuity corollary, now obtained
directly from the accepted source's exponential factorisation. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) (ξ : E) :
    Continuous (fun t : ℝ≥0 => charFun (μ.map (X t)) ξ) := by
  have h_eq : (fun t : ℝ≥0 => charFun (μ.map (X t)) ξ) =
      (fun t : ℝ≥0 => exp ((t : ℝ) * h.charExponent ξ)) := by
    funext t
    exact h.charFun_eq_exp_mul hX t ξ
  rw [h_eq]
  fun_prop
