-- Prove2me | solution 1 for OddPerfectNumber.k_one_non_source_sigma_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T19:48:07.53479+00:00
-- url     : https://prove2.me/submissions/1b6dab1b-d156-4ba3-8779-99a8d2177a1f

import Mathlib

theorem solution (p m q r : Nat)
    (huniq : ∀ y ∈ (m ^ 2).primeFactors,
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization y + 1), y ^ i → y = q)
    (hrmem : r ∈ (m ^ 2).primeFactors) (hrneq : r ≠ q) :
    ¬ p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization r + 1), r ^ i := by
  intro hlocal
  exact hrneq (huniq r hrmem hlocal)
