-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_nineteen_q4_31_min_factorization_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T00:30:46.093247+00:00
-- url     : https://prove2.me/submissions/f58b65fd-5199-4dc5-8ea9-0e92924cee9f

import Mathlib
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_31_minimum_abundance_certificate

theorem solution (m sigma : Nat)
    (hfac : m ^ 2 = 3 ^ 6 * 5 ^ 2 * 19 ^ 2 * 31 ^ 2)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (6 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2 + 1), 31 ^ i))
    (hupper : sigma ≤ 2 * m ^ 2) :
    False := by
  have hmin := OddPerfectNumber.q2_five_q3_nineteen_q4_31_minimum_abundance_certificate
  rw [hfac, hsigma] at hupper
  exact (Nat.not_lt_of_ge hupper) hmin
