-- Prove2me | solution 1 for OddPerfectNumber.Kernel.sq_parity_outside_two_primes
-- status  : ACCEPTED   (prove)
-- author  : @He Jiankui
-- created : 2026-10-01T20:53:19.552126+00:00
-- url     : https://prove2.me/submissions/3652eae2-6a45-4e27-a48c-07ac373292cc

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

theorem solution {X d1 q r l : Nat}
    (hX0 : X != 0) (hd10 : d1 != 0)
    (hm2 : X * d1 ^ 2 * (q * r) != 0)
    (hsq : ∃ y : Nat, y ^ 2 = X * d1 ^ 2 * (q * r))
    (hlq : Not (Dvd.dvd l q)) (hlr : Not (Dvd.dvd l r)) :
    Even (X.factorization l) := by
  have h_prod_ne : X * d1 ^ 2 * (q * r) ≠ 0 := by
    intro h; revert hm2; rw [h]; decide
  have hX_ne : X ≠ 0 := by
    intro h; revert hX0; rw [h]; decide
  have hd1_ne : d1 ≠ 0 := by
    intro h; revert hd10; rw [h]; decide
  have hd1sq_ne : d1 ^ 2 ≠ 0 := pow_ne_zero 2 hd1_ne
  have h_Xd1_ne : X * d1 ^ 2 ≠ 0 := mul_ne_zero hX_ne hd1sq_ne
  have h_qr_ne : q * r ≠ 0 := by
    intro h; apply h_prod_ne; rw [h, mul_zero]
  have h_q_ne : q ≠ 0 := by
    intro h; apply h_qr_ne; rw [h, zero_mul]
  have h_r_ne : r ≠ 0 := by
    intro h; apply h_qr_ne; rw [h, mul_zero]
  obtain ⟨y, hy⟩ := hsq
  have h_fact_eq : (y ^ 2).factorization l = (X * d1 ^ 2 * (q * r)).factorization l := by
    rw [hy]
  have h_lhs : (y ^ 2).factorization l = 2 * y.factorization l := by
    simp [Nat.factorization_pow, nsmul_eq_mul]
  have h_rhs : (X * d1 ^ 2 * (q * r)).factorization l =
      X.factorization l + 2 * d1.factorization l + (q.factorization l + r.factorization l) := by
    rw [Nat.factorization_mul h_Xd1_ne h_qr_ne]
    rw [Nat.factorization_mul hX_ne hd1sq_ne]
    rw [Nat.factorization_mul h_q_ne h_r_ne]
    simp [Nat.factorization_pow, nsmul_eq_mul, add_assoc]
  have h_q_fact : q.factorization l = 0 := Nat.factorization_eq_zero_of_not_dvd hlq
  have h_r_fact : r.factorization l = 0 := Nat.factorization_eq_zero_of_not_dvd hlr
  rw [h_lhs, h_rhs, h_q_fact, h_r_fact] at h_fact_eq
  have h_eq : 2 * y.factorization l = X.factorization l + 2 * d1.factorization l := by
    omega
  refine ⟨y.factorization l - d1.factorization l, by omega⟩
