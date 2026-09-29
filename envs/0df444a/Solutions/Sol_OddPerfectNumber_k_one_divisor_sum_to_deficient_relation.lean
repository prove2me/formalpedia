-- Prove2me | solution 1 for OddPerfectNumber.k_one_divisor_sum_to_deficient_relation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T12:23:00.018968+00:00
-- url     : https://prove2.me/submissions/26ede9a4-7453-46b7-8a44-0dcf2cef499c

import Mathlib

theorem solution (m p d D sigma : Nat)
    (hp_eq : p = 2 * D - 1) (hDpos : 0 < D)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hglobal : sigma = (∑ x ∈ (m ^ 2).divisors, x)) :
    D * sigma = p * m ^ 2 := by
  have hhalf : (p + 1) / 2 = D := by omega
  rw [hhalf] at hprod
  calc D * sigma = D * (p * d) := by rw [hglobal, hsig]
    _ = p * (D * d) := by ring
    _ = p * m ^ 2 := by rw [← hprod]
