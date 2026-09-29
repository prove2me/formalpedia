-- Prove2me | solution 1 for OddPerfectNumber.k_one_q_dvd_d_incoming_core_r_eq_p
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T19:44:53.22181+00:00
-- url     : https://prove2.me/submissions/ecdaa57d-62f4-476a-9484-e833455ec2db
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_sigma_sq_dvd_of_incoming_source_eq_p
import Theorems.Thm_OddPerfectNumber_k_one_q_dvd_d_incoming_core_r_eq_p_after_p_sq_sigma

open OddPerfectNumber

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
    (hqr : q ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization r + 1), r ^ i)
    (hrp : r = p) :
    False := by
  have hp2sig : p ^ 2 ∣ ∑ x ∈ (m ^ 2).divisors, x :=
    k_one_sigma_sq_dvd_of_incoming_source_eq_p p m d q r hp hp4 hdvd hsig
      hprime hqm hqp hqodd hqmem hqdvd huniq hsq hsqP hqd hrmem hrneq hqr hrp
  exact k_one_q_dvd_d_incoming_core_r_eq_p_after_p_sq_sigma p m d q r hp hp4
    hdvd hsig hprime hqm hqp hqodd hqmem hqdvd huniq hsq hsqP hqd hrmem hrneq
    hqr hrp hp2sig
