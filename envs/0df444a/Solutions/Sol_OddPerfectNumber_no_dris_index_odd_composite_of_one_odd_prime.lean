-- Prove2me | solution 1 for OddPerfectNumber.no_dris_index_odd_composite_of_one_odd_prime
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T09:19:35.066505+00:00
-- url     : https://prove2.me/submissions/7a8c7fe1-7167-4235-866d-a04366121e6a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_dris_cofactor_dvd
import Theorems.Thm_OddPerfectNumber_no_dris_one_odd_prime_core

open OddPerfectNumber

-- Reduction of the one-odd-prime residual: peel off the elementary
-- odd-cofactor divisibility (shared, reusable packaging lemma), then
-- isolate the research core. Staged; submitted only after the core child
-- is PUBLISHED (dris_cofactor_dvd may still be Open -- that only affects
-- ACCEPTED vs SKETCH_ACCEPTED, not validity).
theorem solution (p k m s : Nat)
    (hp : p.Prime) (hk : k ≠ 0) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hk1 : ((k + 1).primeFactors.erase 2).card ≤ 1)
    (hs2 : 2 ≤ s) (hs_not_even : ¬ Even s) (hs_not_prime : ¬ s.Prime) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  intro hcon
  have hs_odd : Odd s := Nat.not_even_iff_odd.mp hs_not_even
  have hs_dvd : s ∣ m ^ 2 :=
    dris_cofactor_dvd m s (∑ d ∈ (p ^ k).divisors, d) hs_odd hcon.1
  exact no_dris_one_odd_prime_core p k m s hp hk hm hpm
    hk1 hs2 hs_not_even hs_not_prime hs_dvd hcon
