-- Prove2me | solution 1 for OddPerfectNumber.four_support_factorization_expansion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T15:56:05.470041+00:00
-- url     : https://prove2.me/submissions/66234d56-e075-421a-beb3-b42ab59a60ab

import Mathlib

theorem solution (n q1 q2 q3 q4 : Nat)
    (hn : n ≠ 0)
    (hsupport : n.primeFactors = {q1, q2, q3, q4})
    (hne12 : q1 ≠ q2) (hne13 : q1 ≠ q3) (hne14 : q1 ≠ q4)
    (hne23 : q2 ≠ q3) (hne24 : q2 ≠ q4) (hne34 : q3 ≠ q4) :
    n = q1 ^ n.factorization q1 * q2 ^ n.factorization q2 *
      q3 ^ n.factorization q3 * q4 ^ n.factorization q4 := by
  have h := Nat.prod_factorization_pow_eq_self hn
  rw [Nat.prod_factorization_eq_prod_primeFactors] at h
  rw [hsupport] at h
  simpa [hne12, hne13, hne14, hne23, hne24, hne34,
    mul_assoc, mul_comm, mul_left_comm] using h.symm
