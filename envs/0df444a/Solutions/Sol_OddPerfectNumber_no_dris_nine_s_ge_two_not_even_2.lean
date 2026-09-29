-- Prove2me | solution 2 for OddPerfectNumber.no_dris_nine_s_ge_two_not_even
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-11T08:51:11.378998+00:00
-- url     : https://prove2.me/submissions/98e647dd-a84e-4706-98e2-b893f76b2e3f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_no_dris_index_three_of_one_odd_prime
import Theorems.Thm_OddPerfectNumber_no_dris_nine_s_odd_ge_five

/-!
Reduction of `OddPerfectNumber.no_dris_nine_s_ge_two_not_even`.

An odd index `s ≥ 2` is either `3` or at least `5`.  The index-three case is closed by
`OddPerfectNumber.no_dris_index_three_of_one_odd_prime`, since `k + 1 = 10` has the single odd
prime divisor `5`; the remaining range is the child lemma
`OddPerfectNumber.no_dris_nine_s_odd_ge_five`.
-/

open Finset

theorem solution (p k m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk9 : k = 9) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hs2 : 2 ≤ s) (hs_not_even : ¬ Even s) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  rintro ⟨e1, e2⟩
  have hsodd : s % 2 = 1 := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hs_not_even)
  rcases (show s = 3 ∨ 5 ≤ s by omega) with rfl | hs5
  · subst hk9
    refine OddPerfectNumber.no_dris_index_three_of_one_odd_prime p 9 m hp (by norm_num) hm hpm
      ?_ ⟨e1, e2⟩
    have h10 : ((9 + 1 : ℕ)).primeFactors = {2, 5} := by simp [Nat.primeFactors]
    rw [h10]
    decide
  · exact OddPerfectNumber.no_dris_nine_s_odd_ge_five p k m s hp hp2 hp4 hk4 hk9 hm hpm hs5
      hs_not_even ⟨e1, e2⟩
