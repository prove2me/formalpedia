-- Prove2me | solution 2 for OddPerfectNumber.no_dris_thirteen_s_ge_two_not_even
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-11T09:09:16.314372+00:00
-- url     : https://prove2.me/submissions/2659c89d-013d-4f1a-b47b-57947524a24a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_no_dris_index_odd_prime_of_one_odd_prime
import Theorems.Thm_OddPerfectNumber_no_dris_index_odd_composite_of_one_odd_prime
import Theorems.Thm_OddPerfectNumber_no_dris_thirteen_s_ge_two_two_odd_primes

/-!
Reduction of `OddPerfectNumber.no_dris_thirteen_s_ge_two_not_even`.

Split on the number of odd prime divisors of `k + 1`.  If there is at most one, a prime index
is excluded by `OddPerfectNumber.no_dris_index_odd_prime_of_one_odd_prime` and a composite one
is the child lemma `OddPerfectNumber.no_dris_index_odd_composite_of_one_odd_prime`.  If there
are at least two, the statement is the child lemma
`OddPerfectNumber.no_dris_thirteen_s_ge_two_two_odd_primes`.
-/

open Finset

theorem solution (p k m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk13 : 13 ≤ k) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hs2 : 2 ≤ s) (hs_not_even : ¬ Even s) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  by_cases hk1 : ((k + 1).primeFactors.erase 2).card ≤ 1
  · by_cases hsp : s.Prime
    · exact OddPerfectNumber.no_dris_index_odd_prime_of_one_odd_prime p k m s hp hsp
        (by rintro rfl; exact hs_not_even (by decide)) (by omega) hm hpm hk1
    · exact OddPerfectNumber.no_dris_index_odd_composite_of_one_odd_prime p k m s hp (by omega)
        hm hpm hk1 hs2 hs_not_even hsp
  · exact OddPerfectNumber.no_dris_thirteen_s_ge_two_two_odd_primes p k m s hp hp2 hp4 hk4 hk13
      hm hpm hs2 hs_not_even (by omega)
