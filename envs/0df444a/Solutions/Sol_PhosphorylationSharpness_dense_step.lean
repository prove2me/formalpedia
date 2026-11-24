-- Prove2me | solution 1 for PhosphorylationSharpness.dense_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:23:13.424807+00:00
-- url     : https://prove2.me/submissions/bd8d27d0-ea62-442c-b2dc-cb0378a797db

import Mathlib
import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
import Theorems.Thm_PhosphorylationSharpness_DensePositive_nonneg

set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial
namespace PhosphorylationSharpness
theorem _root_.solution {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m)
    (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    DensePositive (C a*p + C b*(X*p) + C c*q + C d*(X*q)) (m+1) := by
  constructor
  · intro i hi
    cases i with
    | zero =>
      simp only [coeff_add, coeff_C_mul, coeff_X_mul_zero, mul_zero, add_zero]
      exact add_pos_of_pos_of_nonneg (mul_pos ha (hp.1 0 (by omega)))
        (mul_nonneg hc (hq.nonneg 0))
    | succ i =>
      simp only [coeff_add, coeff_C_mul, coeff_X_mul]
      have h1 := mul_nonneg ha.le (hp.nonneg (i+1))
      have h2 := mul_pos hb (hp.1 i (by omega))
      have h3 := mul_nonneg hc (hq.nonneg (i+1))
      have h4 := mul_nonneg hd (hq.nonneg i)
      linarith
  · intro i hi
    cases i with
    | zero => omega
    | succ i =>
      simp only [coeff_add, coeff_C_mul, coeff_X_mul]
      rw [hp.2 (i+1) (by omega), hp.2 i (by omega),
        hq.2 (i+1) (by omega), hq.2 i (by omega)]
      ring
end PhosphorylationSharpness
