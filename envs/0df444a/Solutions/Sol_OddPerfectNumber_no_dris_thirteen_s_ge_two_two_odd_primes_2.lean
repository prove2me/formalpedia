-- Prove2me | solution 2 for OddPerfectNumber.no_dris_thirteen_s_ge_two_two_odd_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-22T04:35:06.609283+00:00
-- url     : https://prove2.me/submissions/7acb6d0e-4ac0-4131-b1d4-bd955b2233cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_dris_cofactor_dvd
import Theorems.Thm_OddPerfectNumber_no_dris_two_odd_primes_core

open Finset OddPerfectNumber

-- The thirteen, two-odd-prime residual is an exact specialization of the
-- general two-odd-prime residual.  The Dris cofactor divisibility is the only
-- packaged premise not present in the target and is supplied by the proved
-- shared lemma.
theorem solution (p k m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk13 : 13 ≤ k) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hs2 : 2 ≤ s) (hs_not_even : ¬ Even s)
    (hk1 : 2 ≤ ((k + 1).primeFactors.erase 2).card) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  intro hcon
  have hk : k ≠ 0 := by omega
  have hs_odd : Odd s := Nat.not_even_iff_odd.mp hs_not_even
  have hs_dvd : s ∣ m ^ 2 :=
    dris_cofactor_dvd m s (∑ d ∈ (p ^ k).divisors, d) hs_odd hcon.1
  exact (no_dris_two_odd_primes_core p k m s hp hk hm hpm hk1 hs2 hs_not_even hs_dvd) hcon
