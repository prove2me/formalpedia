-- Prove2me | solution 1 for QubitFreqSensing.lemma_5_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:36:21.275923+00:00
-- url     : https://prove2.me/submissions/025bfcac-4aec-4a02-9c75-1d070cc5b794

import Mathlib

open Real

theorem solution (ω : ℝ) (hω : 0 < ω) :
    π - 1 ≤ ∫ x in (0 : ℝ)..2 * π, |Real.cos (ω * x)| := by
  have hsq : ∫ x in (0 : ℝ)..2 * π, Real.cos (ω * x) ^ 2
      = π + Real.cos (2 * π * ω) * Real.sin (2 * π * ω) / (2 * ω) := by
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x ^ 2) hω.ne',
      integral_cos_sq]
    simp only [mul_zero, Real.cos_zero, Real.sin_zero, smul_eq_mul]
    rw [mul_comm ω (2 * π)]
    field_simp <;> ring
  have hcs : -(2 * ω) ≤ Real.cos (2 * π * ω) * Real.sin (2 * π * ω) := by
    rcases le_or_gt (1 / 4) ω with h | h
    · have := Real.cos_sq_add_sin_sq (2 * π * ω)
      nlinarith [sq_nonneg (Real.cos (2 * π * ω) + Real.sin (2 * π * ω))]
    · have ht0 : 0 ≤ 2 * π * ω := by positivity
      have ht1 : 2 * π * ω ≤ π / 2 := by nlinarith [Real.pi_pos]
      have hc : 0 ≤ Real.cos (2 * π * ω) :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], ht1⟩
      have hs : 0 ≤ Real.sin (2 * π * ω) :=
        Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [Real.pi_pos])
      nlinarith [mul_nonneg hc hs]
  have hmono : ∫ x in (0 : ℝ)..2 * π, Real.cos (ω * x) ^ 2
      ≤ ∫ x in (0 : ℝ)..2 * π, |Real.cos (ω * x)| := by
    refine intervalIntegral.integral_mono_on (by positivity) ?_ ?_ ?_
    · exact (by fun_prop : Continuous fun x => Real.cos (ω * x) ^ 2).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun x => |Real.cos (ω * x)|).intervalIntegrable _ _
    · intro x _
      have h1 := Real.abs_cos_le_one (ω * x)
      have h2 := abs_nonneg (Real.cos (ω * x))
      rw [← sq_abs]
      nlinarith
  have hfrac : -1 ≤ Real.cos (2 * π * ω) * Real.sin (2 * π * ω) / (2 * ω) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  linarith
