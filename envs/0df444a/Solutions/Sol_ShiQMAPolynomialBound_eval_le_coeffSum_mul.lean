-- Prove2me | solution 1 for ShiQMAPolynomialBound.eval_le_coeffSum_mul
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-01T01:28:59.44056+00:00
-- url     : https://prove2.me/submissions/f338034b-0538-4d8f-a7a2-5b55cb3de000

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Data.Nat.Log

set_option autoImplicit false

theorem solution (p : Polynomial ℕ) (n : ℕ) :
    p.eval n ≤ p.eval 1 * (n + 1) ^ p.natDegree := by
  classical
  have hpow (i : ℕ) (hi : i ∈ p.support) :
      n ^ i ≤ (n + 1) ^ p.natDegree := by
    calc
      n ^ i ≤ (n + 1) ^ i :=
        Nat.pow_le_pow_left (Nat.le_succ n) i
      _ ≤ (n + 1) ^ p.natDegree :=
        Nat.pow_le_pow_right (by omega)
          (Polynomial.le_natDegree_of_mem_supp i hi)
  have hs :
      (∑ i ∈ p.support, p.coeff i * n ^ i) ≤
        ∑ i ∈ p.support,
          p.coeff i * (n + 1) ^ p.natDegree := by
    apply Finset.sum_le_sum
    intro i hi
    exact Nat.mul_le_mul_left _ (hpow i hi)
  calc
    p.eval n = ∑ i ∈ p.support, p.coeff i * n ^ i := by
      rw [Polynomial.eval_eq_sum, Polynomial.sum]
    _ ≤ ∑ i ∈ p.support,
        p.coeff i * (n + 1) ^ p.natDegree := hs
    _ = p.eval 1 * (n + 1) ^ p.natDegree := by
      rw [← Finset.sum_mul]
      congr 1
      rw [Polynomial.eval_eq_sum, Polynomial.sum]
      simp
