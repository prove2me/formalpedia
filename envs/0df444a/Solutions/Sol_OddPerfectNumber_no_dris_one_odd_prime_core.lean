-- Prove2me | solution 1 for OddPerfectNumber.no_dris_one_odd_prime_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T09:47:10.793169+00:00
-- url     : https://prove2.me/submissions/ab24a88b-b3e5-4209-8124-ee89af44aa48
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_succ_shape_of_card_le_one
import Theorems.Thm_OddPerfectNumber_no_dris_one_odd_prime_shaped_core

open OddPerfectNumber

-- Reduction of the one-odd-prime core: extract the multiplicative shape of
-- k + 1 with the proved lemma, then isolate the order/LTE core. Staged;
-- submitted only after the shaped core is PUBLISHED.
theorem solution (p k m s : Nat)
    (hp : p.Prime) (hk : k ≠ 0) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hk1 : ((k + 1).primeFactors.erase 2).card ≤ 1)
    (hs2 : 2 ≤ s) (hs_not_even : ¬ Even s) (hs_not_prime : ¬ s.Prime)
    (hs_dvd : s ∣ m ^ 2) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  obtain ⟨a, q, b, hqp, hshape⟩ := k_succ_shape_of_card_le_one k hk1
  exact no_dris_one_odd_prime_shaped_core p k m s a q b hp hk hm hpm
    hk1 hs2 hs_not_even hs_not_prime hs_dvd hqp hshape
