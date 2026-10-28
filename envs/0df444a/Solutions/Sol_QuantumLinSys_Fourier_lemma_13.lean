-- Prove2me | solution 1 for QuantumLinSys.Fourier.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T22:09:55.947617+00:00
-- url     : https://prove2.me/submissions/52c072a0-246f-4b3b-8546-292f6f1af2df

import Mathlib
import Definitions.Def_QuantumLinSys_Fourier_Setting

open Complex

open QuantumLinSys.Fourier in
theorem solution (ω Δz : ℝ) (hΔ : 0 < Δz) :
    (∑' k : ℤ, (Real.exp (-(ω + 2 * Real.pi * (k : ℝ) / Δz) ^ 2 / 2) : ℂ)) =
      1 / (Real.sqrt (2 * Real.pi) : ℂ) *
        ∑' k : ℤ, (Δz : ℂ) *
          (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ) *
          Complex.exp (-Complex.I * ω * ((k : ℝ) * Δz)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set ar : ℝ := Δz ^ 2 / (2 * Real.pi) with har
  have harpos : 0 < ar := by positivity
  set cr : ℝ := ω * Δz / (2 * Real.pi) with hcr
  set b : ℂ := -I * (cr : ℂ) with hb
  have hIb : I * b = (cr : ℂ) := by
    rw [hb, ← mul_assoc, mul_neg, I_mul_I]; ring
  have hare : 0 < ((ar : ℂ)).re := by simpa using harpos
  have key := Complex.tsum_exp_neg_quadratic hare b
  -- rewrite RHS summand
  have hR : ∀ k : ℤ, (Δz : ℂ) * (Real.exp (-((k : ℝ) * Δz) ^ 2 / 2) : ℂ) *
      Complex.exp (-Complex.I * ω * ((k : ℝ) * Δz)) =
      (Δz : ℂ) * cexp (-(Real.pi : ℂ) * (ar : ℂ) * (k : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * b * (k : ℂ)) := by
    intro k
    rw [mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    rw [hb, har, hcr]
    push_cast
    field_simp
  -- rewrite LHS summand
  have hL : ∀ k : ℤ, (Real.exp (-(ω + 2 * Real.pi * (k : ℝ) / Δz) ^ 2 / 2) : ℂ) =
      cexp (-(Real.pi : ℂ) / (ar : ℂ) * ((k : ℂ) + I * b) ^ 2) := by
    intro k
    rw [hIb, Complex.ofReal_exp]
    congr 1
    have e : (-(ω + 2 * Real.pi * (k : ℝ) / Δz) ^ 2 / 2 : ℝ) =
        -Real.pi / ar * ((k : ℝ) + cr) ^ 2 := by
      rw [har, hcr]
      field_simp
      ring
    rw [e]
    push_cast
    ring
  have hsqrt : (ar : ℂ) ^ (1 / 2 : ℂ) = ((Δz / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) := by
    have h1 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h1, ← Complex.ofReal_cpow harpos.le, ← Real.sqrt_eq_rpow, har,
      Real.sqrt_div' _ (by positivity), Real.sqrt_sq hΔ.le]
  simp_rw [hR, hL]
  rw [tsum_mul_left, key, hsqrt]
  have hs : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hs' : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hΔ' : (Δz : ℂ) ≠ 0 := by exact_mod_cast hΔ.ne'
  push_cast
  field_simp
