-- Prove2me | solution 1 for OddPerfectNumber.k_one_residue_endgame_reflected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T11:32:06.350985+00:00
-- url     : https://prove2.me/submissions/9af0a79c-ff66-4bca-9596-20ac493ab728
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_endgame_q_dvd_t
import Theorems.Thm_OddPerfectNumber_k_one_endgame_q_dvd_d

open OddPerfectNumber

-- Split reduction: q divides m^2 = t*d, so primality forces q | t or q | d.
theorem solution (p m d q : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1)
    (hdvd : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hprime : q.Prime) (hqm : q ∣ m) (hqp : q ≠ p) (hqodd : Odd q)
    (hqmem : q ∈ (m ^ 2).primeFactors)
    (hqdvd : p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i)
    (huniq : ∀ y ∈ (m ^ 2).primeFactors,
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization y + 1), y ^ i → y = q)
    (hsq : IsSquare (q : ZMod p))
    (hsqP : IsSquare (p : ZMod q)) :
    False := by
  have hm2dvd : q ∣ m ^ 2 := by
    rw [pow_two]
    exact hqm.mul_right m
  rw [hdvd] at hm2dvd
  -- NOTE (remote CE 95868d7a): Nat.Prime.dvd_mul takes Nat.Prime directly.
  rcases (Nat.Prime.dvd_mul hprime).mp hm2dvd with hqt | hqd
  · exact k_one_endgame_q_dvd_t p m d q hp hp4 hdvd hsig
      hprime hqm hqp hqodd hqmem hqdvd huniq hsq hsqP hqt
  · exact k_one_endgame_q_dvd_d p m d q hp hp4 hdvd hsig
      hprime hqm hqp hqodd hqmem hqdvd huniq hsq hsqP hqd
