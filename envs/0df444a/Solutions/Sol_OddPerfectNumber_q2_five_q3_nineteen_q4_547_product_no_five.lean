-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_nineteen_q4_547_product_no_five
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T03:19:56.440407+00:00
-- url     : https://prove2.me/submissions/23acff2f-5451-4071-bbc1-7220435f6cda

import Mathlib
import Theorems.Thm_OddPerfectNumber_prime_not_dvd_own_sigma_prime_pow

theorem solution (a b c e : Nat)
    (h3 : ¬ 5 ∣ ∑ i ∈ Finset.range (a + 1), 3 ^ i)
    (h19 : ¬ 5 ∣ ∑ i ∈ Finset.range (c + 1), 19 ^ i)
    (h547 : ¬ 5 ∣ ∑ i ∈ Finset.range (e + 1), 547 ^ i) :
    ¬ 5 ∣
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), 547 ^ i) := by
  have h5 : ¬ 5 ∣ ∑ i ∈ Finset.range (b + 1), 5 ^ i :=
    OddPerfectNumber.prime_not_dvd_own_sigma_prime_pow 5 b (by norm_num)
  intro h
  have hp : Nat.Prime 5 := by norm_num
  have hA : 5 ∣
      ((∑ i ∈ Finset.range (a + 1), 3 ^ i) *
        (∑ i ∈ Finset.range (b + 1), 5 ^ i)) *
        (∑ i ∈ Finset.range (c + 1), 19 ^ i) ∨
      5 ∣ ∑ i ∈ Finset.range (e + 1), 547 ^ i := hp.dvd_mul.mp h
  rcases hA with hA | h547'
  · have hB : 5 ∣
        (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
          (∑ i ∈ Finset.range (b + 1), 5 ^ i) ∨
        5 ∣ ∑ i ∈ Finset.range (c + 1), 19 ^ i := hp.dvd_mul.mp hA
    rcases hB with hB | h19'
    · rcases hp.dvd_mul.mp hB with h3' | h5'
      · exact h3 h3'
      · exact h5 h5'
    · exact h19 h19'
  · exact h547 h547'
