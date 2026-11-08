-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat22_charFun_rat_pow
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:40:55.409624+00:00
-- url     : https://prove2.me/submissions/9906af59-a583-476b-b309-a2238c5296a4

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_ProbabilityTheory_leanlevy_chat22_charFun_nat_mul

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

/-- A rational-time instance of the natural-time marginal power law. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t))
    (k n : ℕ) (ξ : E) :
    charFun (μ.map (X ((k : ℝ≥0) / (n : ℝ≥0)))) ξ =
      (charFun (μ.map (X (1 / (n : ℝ≥0)))) ξ) ^ k := by
  simpa [div_eq_mul_inv] using
    (leanlevy_chat22_charFun_nat_mul h hX k ((n : ℝ≥0)⁻¹) ξ)
