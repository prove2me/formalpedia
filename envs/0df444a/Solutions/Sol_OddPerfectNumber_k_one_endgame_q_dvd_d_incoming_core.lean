-- Prove2me | solution 1 for OddPerfectNumber.k_one_endgame_q_dvd_d_incoming_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T16:59:26.700661+00:00
-- url     : https://prove2.me/submissions/483f8f94-0bc4-4225-950d-c578f88a6623
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q_dvd_d_incoming_core_r_eq_p
import Theorems.Thm_OddPerfectNumber_k_one_q_dvd_d_incoming_core_r_ne_p

open OddPerfectNumber

-- This target is a structural split, so platform-theorem imports are used in
-- prove mode; neither branch is asserted to be solved here.
theorem solution (p m d q r : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hdvd : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hprime : q.Prime) (hqm : q ∣ m) (hqp : q ≠ p) (hqodd : Odd q)
    (hqmem : q ∈ (m ^ 2).primeFactors)
    (hqdvd : p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i)
    (huniq : ∀ y ∈ (m ^ 2).primeFactors,
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization y + 1), y ^ i → y = q)
    (hsq : IsSquare (q : ZMod p))
    (hsqP : IsSquare (p : ZMod q))
    (hqd : q ∣ d)
    (hrmem : r ∈ (m ^ 2).primeFactors)
    (hrneq : r ≠ q)
    (hqr : q ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization r + 1), r ^ i) :
    False := by
  by_cases hrp : r = p
  · exact k_one_q_dvd_d_incoming_core_r_eq_p p m d q r hp hp4 hdvd hsig
      hprime hqm hqp hqodd hqmem hqdvd huniq hsq hsqP hqd hrmem hrneq hqr hrp
  · exact k_one_q_dvd_d_incoming_core_r_ne_p p m d q r hp hp4 hdvd hsig
      hprime hqm hqp hqodd hqmem hqdvd huniq hsq hsqP hqd hrmem hrneq hqr hrp
