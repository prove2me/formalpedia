-- Prove2me | solution 2 for OddPerfectNumber.no_dris_one_odd_prime_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:08:20.990258+00:00
-- url     : https://prove2.me/submissions/b3c6e04a-90ae-42db-9ab0-32555e0c5e8d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_no_dris_one_odd_prime_shaped_core
import Theorems.Thm_OddPerfectNumber_exists_two_pow_mul_prime_pow_of_card_odd_primeFactors_le_one

theorem _root_.solution (p k m s : Nat)
    (hp : p.Prime) (hk : k ≠ 0) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hk1 : ((k + 1).primeFactors.erase 2).card ≤ 1)
    (hs2 : 2 ≤ s) (hs_not_even : ¬ Even s) (hs_not_prime : ¬ s.Prime)
    (hs_dvd : s ∣ m ^ 2) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  obtain ⟨a, q, b, hqp, hshape⟩ :=
    OddPerfectNumber.exists_two_pow_mul_prime_pow_of_card_odd_primeFactors_le_one
      (k + 1) (by omega) hk1
  exact OddPerfectNumber.no_dris_one_odd_prime_shaped_core p k m s a q b hp hk hm hpm hk1
    hs2 hs_not_even hs_not_prime hs_dvd hqp hshape

#print axioms solution
