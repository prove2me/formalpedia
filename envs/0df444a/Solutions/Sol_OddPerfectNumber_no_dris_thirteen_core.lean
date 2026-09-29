-- Prove2me | solution 1 for OddPerfectNumber.no_dris_thirteen_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T09:43:17.22874+00:00
-- url     : https://prove2.me/submissions/e9c4c107-3311-4dcb-91a1-ad375e3c2b0a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_two_distinct_odd_prime_factors
import Theorems.Thm_OddPerfectNumber_no_dris_thirteen_witnessed_core

open OddPerfectNumber

-- Reduction of the thirteen core: extract the two odd-prime witnesses with
-- the proved lemma, then isolate the per-prime-analysis core. Staged;
-- submitted only after the witnessed core is PUBLISHED.
theorem solution (p k m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk13 : 13 ≤ k) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hs2 : 2 ≤ s) (hs_not_even : ¬ Even s)
    (hk1 : 2 ≤ ((k + 1).primeFactors.erase 2).card)
    (hs_dvd : s ∣ m ^ 2) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  obtain ⟨q1, q2, hq1ne, hq1p, hq2p, hq1o, hq2o, hq1d, hq2d⟩ :=
    two_distinct_odd_prime_factors k hk1
  exact no_dris_thirteen_witnessed_core p k m s q1 q2 hp hp2 hp4 hk4 hk13
    hm hpm hs2 hs_not_even hq1ne hq1p hq2p hq1o hq2o hq1d hq2d hs_dvd
