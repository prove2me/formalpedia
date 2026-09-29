-- Prove2me | solution 1 for OddPerfectNumber.no_dris_thirteen_s_ge_two_two_odd_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T09:17:34.294181+00:00
-- url     : https://prove2.me/submissions/66f3cb3c-a736-4eb4-94c0-1e2a04187200
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_dris_cofactor_dvd
import Theorems.Thm_OddPerfectNumber_no_dris_thirteen_core

open OddPerfectNumber

-- Reduction of the thirteen-residual: peel off the elementary odd-cofactor
-- divisibility once, then isolate the research core. Staged; submitted only
-- after both children PUBLISHED.
theorem solution (p k m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk13 : 13 ≤ k) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hs2 : 2 ≤ s) (hs_not_even : ¬ Even s)
    (hk1 : 2 ≤ ((k + 1).primeFactors.erase 2).card) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  intro hcon
  have hs_odd : Odd s := Nat.not_even_iff_odd.mp hs_not_even
  have hs_dvd : s ∣ m ^ 2 :=
    dris_cofactor_dvd m s (∑ d ∈ (p ^ k).divisors, d) hs_odd hcon.1
  exact no_dris_thirteen_core p k m s hp hp2 hp4 hk4 hk13 hm hpm
    hs2 hs_not_even hk1 hs_dvd hcon
