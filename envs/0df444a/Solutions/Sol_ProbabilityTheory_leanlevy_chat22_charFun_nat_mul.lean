-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat22_charFun_nat_mul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:30:43.139812+00:00
-- url     : https://prove2.me/submissions/3c206a42-e49e-4928-b077-ae625b68fb73

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_ProbabilityTheory_leanlevy_chat22_charFun_marginal_mul

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped NNReal

private theorem chat22_charFun_zero_nat
    {Ω : Type*} [MeasurableSpace Ω] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsLevyProcess X μ) (ξ : E) :
    charFun (μ.map (X 0)) ξ = 1 := by
  have hz : μ.map (X 0) = Measure.dirac (0 : E) := by
    rw [h.start_zero, Measure.map_const, measure_univ, one_smul]
  rw [hz, charFun_dirac, inner_zero_left, Complex.ofReal_zero, zero_mul, exp_zero]

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t))
    (n : ℕ) (s : ℝ≥0) (ξ : E) :
    charFun (μ.map (X ((n : ℝ≥0) * s))) ξ =
      (charFun (μ.map (X s)) ξ) ^ n := by
  induction n with
  | zero => simp [show (0 : ℝ≥0) * s = 0 from zero_mul s, chat22_charFun_zero_nat h ξ]
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : ℝ≥0) * s = s + (n : ℝ≥0) * s from by push_cast; ring,
        leanlevy_chat22_charFun_marginal_mul h hX, ih, pow_succ, mul_comm]
