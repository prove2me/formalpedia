-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_nineteen_q4_31_abundance_of_factorization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T00:31:12.734767+00:00
-- url     : https://prove2.me/submissions/87efcb90-cbc1-4ccd-9d83-2dbbeafe1ce6

import Mathlib
import Theorems.Thm_OddPerfectNumber_q2_five_q3_nineteen_q4_31_abundance_monotone

theorem solution (m a c e sigma : Nat)
    (hfac : m ^ 2 = 3 ^ a * 5 ^ 2 * 19 ^ c * 31 ^ e)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), 31 ^ i))
    (hupper : sigma ≤ 2 * m ^ 2)
    (ha : 6 ≤ a) (hc : 2 ≤ c) (he : 2 ≤ e) :
    False := by
  have hmono := OddPerfectNumber.q2_five_q3_nineteen_q4_31_abundance_monotone
    a c e ha hc he
  rw [hfac, hsigma] at hupper
  exact (Nat.not_lt_of_ge hupper) hmono
