-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.entropy_positive_mean_one
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:32:06.945144+00:00
-- url     : https://prove2.me/submissions/56210d2a-e1e9-4ac4-894a-1acc1f77ada7

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open MeasureTheory
open ZeroFreeRRG.Hardcore

/-- A nonconstant nonnegative mean-one factor has positive x log x expectation. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Ω → ℝ) (hE : ∀ᵐ ω ∂μ, 0 ≤ E ω) (hInt : Integrable E μ)
    (hEnt : Integrable (fun ω => xlogx (E ω)) μ) (hmean : (∫ ω, E ω ∂μ) = 1)
    (hpos : 0 < μ {ω | 0 ≤ E ω ∧ E ω ≠ 1}) :
    0 < ∫ ω, xlogx (E ω) ∂μ := by
  let gap : Ω → ℝ := fun ω => xlogx (E ω) - E ω + 1
  have hint : Integrable gap μ := (hEnt.sub hInt).add (integrable_const 1)
  have hgap : 0 ≤ᵐ[μ] gap := by
    filter_upwards [hE] with ω hω
    dsimp [gap,xlogx]
    linarith [Real.self_sub_one_le_mul_log hω]
  have hs : {ω | 0 ≤ E ω ∧ E ω ≠ 1} ⊆ Function.support gap := by
    intro ω hω
    change gap ω ≠ 0
    dsimp [gap,xlogx]
    have h := Real.self_sub_one_lt_mul_log hω.1 hω.2
    linarith
  have hpositive : 0 < μ (Function.support gap) := lt_of_lt_of_le hpos (measure_mono hs)
  have hh := (integral_pos_iff_support_of_nonneg_ae hgap hint).2 hpositive
  dsimp [gap] at hh
  have heq : (∫ ω, xlogx (E ω) - E ω + 1 ∂μ) =
      (∫ ω, xlogx (E ω) ∂μ) - (∫ ω, E ω ∂μ) + (1:ℝ) := by
    have hi := integral_add (hEnt.sub hInt) (integrable_const (1:ℝ))
    simp only [Pi.add_apply, Pi.sub_apply] at hi
    rw [hi, integral_sub hEnt hInt, integral_const]
    simp only [probReal_univ, one_smul]
  rw [heq, hmean] at hh
  linarith
