-- Prove2me | solution 1 for OddPerfectNumber.dris_packaged_congruent_absurd
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-11T19:25:22.701831+00:00
-- url     : https://prove2.me/submissions/3f54ca13-ebba-41a7-8320-44fc045589d4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OddPerfectNumber_dandapat_hunsucker_pomerance_two
import Theorems.Thm_OddPerfectNumber_no_dris_index_odd_prime_of_one_odd_prime
import Theorems.Thm_OddPerfectNumber_no_dris_one_odd_prime_core
import Theorems.Thm_OddPerfectNumber_no_dris_two_odd_primes_core

open Finset OddPerfectNumber

/-- **Reduction of the packaged Euler configuration to the two composite-index cores.**

With `s := d` the packaged identities are exactly the Dris relations
`2m² = σ(p^k)·d`, `σ(m²) = p^k·d`, and `d` is odd because it divides the odd number `m²`.
Splitting on the value of `d` and on the number of odd primes of `k + 1` leaves only the two
research cores. -/
theorem solution (p k m s t d : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m) (hs_odd : Odd s)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1)
    (hsig : (∑ d ∈ (p ^ k).divisors, d) = 2 * t)
    (hdvd : m ^ 2 = t * d)
    (hsigm : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * d)
    (hd_dvd : d ∣ m ^ 2) : False := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hk : k ≠ 0 := by omega
  -- the packaged identities are the Dris relations with index `d`
  have h1 : 2 * m ^ 2 = (∑ x ∈ (p ^ k).divisors, x) * d := by rw [hsig, hdvd]; ring
  -- the index is odd, being a divisor of the odd number `m²`
  have hm2odd : (m ^ 2) % 2 = 1 := by
    have := Nat.odd_iff.mp hm
    rw [pow_two, Nat.mul_mod, this]
  have hdodd : ¬ Even d := by
    intro he
    have h2d : (2 : ℕ) ∣ m ^ 2 := (he.two_dvd).trans hd_dvd
    omega
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hdvd
    exact hm0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hdvd)
  rcases Nat.lt_or_ge d 2 with hd1 | hd2
  · -- `d = 1`: the configuration is the Dandapat–Hunsucker–Pomerance system
    have hdeq : d = 1 := by omega
    subst hdeq
    refine dandapat_hunsucker_pomerance_two p k m hp hm hk ?_ ?_
    · rw [hsig]
      rw [mul_one] at hdvd
      rw [hdvd]
    · rw [hsigm, mul_one]
  · by_cases hk1 : ((k + 1).primeFactors.erase 2).card ≤ 1
    · by_cases hdp : Nat.Prime d
      · exact no_dris_index_odd_prime_of_one_odd_prime p k m d hp hdp
          (by rintro rfl; exact hdodd (by decide)) hk hm hpm hk1 ⟨h1, hsigm⟩
      · exact no_dris_one_odd_prime_core p k m d hp hk hm hpm hk1 hd2 hdodd hdp hd_dvd ⟨h1, hsigm⟩
    · exact no_dris_two_odd_primes_core p k m d hp hk hm hpm (by omega) hd2 hdodd hd_dvd
        ⟨h1, hsigm⟩
