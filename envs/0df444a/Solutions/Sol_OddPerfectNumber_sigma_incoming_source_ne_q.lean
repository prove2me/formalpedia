-- Prove2me | solution 1 for OddPerfectNumber.sigma_incoming_source_ne_q
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T10:55:26.763306+00:00
-- url     : https://prove2.me/submissions/e0b8551b-7b41-4436-8118-da20809a24d2

import Mathlib
import Theorems.Thm_OddPerfectNumber_prime_not_dvd_own_sigma_prime_pow

theorem solution (q r a : Nat)
    (hq : q.Prime)
    (hqr : q ∣ ∑ i ∈ Finset.range (a + 1), r ^ i) :
    r ≠ q := by
  intro hr
  subst r
  exact OddPerfectNumber.prime_not_dvd_own_sigma_prime_pow q a hq hqr
