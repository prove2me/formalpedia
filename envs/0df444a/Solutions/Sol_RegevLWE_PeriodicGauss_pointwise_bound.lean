-- Prove2me | solution 1 for RegevLWE.PeriodicGauss.pointwise_bound
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:30:00.019061+00:00
-- url     : https://prove2.me/submissions/a819896d-8ffa-46cf-a1a6-655142cf037f

import Mathlib
import Definitions.Def_RegevLWE_PeriodicGauss_Gaussian

open MeasureTheory
open RegevLWE.PeriodicGauss

/-- Proof of Claim 2.2, p. 34:16: since `1 - z ≤ e^{-z} ≤ 1` for all `z ≥ 0`,
`|e^{-π(1-1/(1+ϵ)²)x²} - 1| ≤ π(1 - 1/(1+ϵ)²)x² ≤ 2πϵx²` (here for every `ϵ ≥ 0` and real `x`). -/
theorem solution (ϵ : ℝ) (hϵ : 0 ≤ ϵ) (x : ℝ) :
    |Real.exp (-Real.pi * (1 - 1 / (1 + ϵ) ^ 2) * x ^ 2) - 1| ≤
        Real.pi * (1 - 1 / (1 + ϵ) ^ 2) * x ^ 2 ∧
      Real.pi * (1 - 1 / (1 + ϵ) ^ 2) * x ^ 2 ≤ 2 * Real.pi * ϵ * x ^ 2 := by
  have hd : 0 < (1 + ϵ)^2 := sq_pos_of_pos (by linarith)
  have hd1 : 1 ≤ (1 + ϵ)^2 := by nlinarith
  have hz : 0 ≤ 1 - 1 / (1 + ϵ)^2 := by
    have := (div_le_one hd).mpr hd1
    linarith
  have hb : 1 - 1 / (1 + ϵ)^2 ≤ 2 * ϵ := by
    apply (sub_le_iff_le_add).mpr
    have he : ϵ^3 ≥ 0 := pow_nonneg hϵ 3
    have h : (1 - 2 * ϵ) * (1 + ϵ)^2 ≤ 1 := by nlinarith [sq_nonneg ϵ]
    have hh := (le_div_iff₀ hd).mpr h
    linarith
  have hp : 0 ≤ Real.pi * (1 - 1 / (1 + ϵ)^2) * x^2 := by positivity
  have hn : -Real.pi * (1 - 1 / (1 + ϵ)^2) * x^2 ≤ 0 := by nlinarith
  have he : Real.exp (-Real.pi * (1 - 1 / (1 + ϵ)^2) * x^2) ≤ 1 :=
    Real.exp_le_one_iff.mpr hn
  constructor
  · rw [abs_of_nonpos (by linarith)]
    have := Real.add_one_le_exp (-Real.pi * (1 - 1 / (1 + ϵ)^2) * x^2)
    linarith
  · have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb Real.pi_pos.le) (sq_nonneg x)
    nlinarith


#print axioms solution
