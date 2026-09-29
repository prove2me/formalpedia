-- Prove2me | solution 1 for OddPerfectNumber.k_one_sigma_sq_dvd_of_incoming_source_eq_p
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T19:42:07.366921+00:00
-- url     : https://prove2.me/submissions/5a27a7af-e8d2-4cb5-bc46-61470476d767

import Mathlib
import Theorems.Thm_OddPerfectNumber_p_dvd_d_of_incoming_source_eq_p

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
    p ^ 2 ∣ ∑ x ∈ (m ^ 2).divisors, x := by
  have hpd : p ∣ d :=
    p_dvd_d_of_incoming_source_eq_p p m d r hp hp4 hdvd hrmem hrp
  obtain ⟨c, hc⟩ := hpd
  refine ⟨c, ?_⟩
  rw [hsig, hc]
  ring
