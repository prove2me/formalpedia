-- Prove2me | solution 1 for OddPerfectNumber.k_one_endgame_q_dvd_t
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T22:41:52.637753+00:00
-- url     : https://prove2.me/submissions/43e99f17-7c9e-4073-8e61-2378708974f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_dris_packaged_core
import Theorems.Thm_OddPerfectNumber_k_one_endgame_q_dvd_t_normalization

open OddPerfectNumber

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
    (hsqP : IsSquare (p : ZMod q))
    (hqt : q ∣ (p + 1) / 2) :
    False := by
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hp4
  have hsigp : (∑ x ∈ (p ^ 1).divisors, x) = 2 * ((p + 1) / 2) := by
    rw [Nat.sum_divisors_prime_pow hp]
    norm_num [Finset.sum_range_succ]
    have hodd : Odd p := hp.odd_of_ne_two hp2
    omega
  have hnorm := k_one_endgame_q_dvd_t_normalization
    p m d q hp hp4 hdvd hsig hprime hqm hqp hqodd hqmem hqdvd huniq hsq hsqP hqt
  have hs1 : Odd 1 := by decide
  have hd_dvd : d ∣ m ^ 2 := by
    rw [hdvd]
    exact dvd_mul_left d ((p + 1) / 2)
  have hsig1 : (∑ x ∈ (m ^ 2).divisors, x) = p ^ 1 * d := by
    simpa only [Nat.pow_one] using hsig
  exact dris_packaged_core p 1 m 1 ((p + 1) / 2) d hp hnorm.1 hnorm.2 hs1
    hsigp hdvd hsig1 hd_dvd
