-- Prove2me | solution 2 for OddPerfectNumber.no_dris_five_s_ge_two_not_even
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:02:40.378391+00:00
-- url     : https://prove2.me/submissions/910e1248-2ec9-4391-b425-a3a03c560de5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_no_dris_five_s_odd_eq_three
import Theorems.Thm_OddPerfectNumber_no_dris_five_s_odd_ge_five

theorem _root_.solution (p m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hs : 2 ≤ s) (hs_not_even : ¬ Even s) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) := by
  have hodd : s % 2 = 1 := Nat.odd_iff.1 ((Nat.even_or_odd s).resolve_left hs_not_even)
  rcases (by omega : s = 3 ∨ 5 ≤ s) with h | h
  · exact OddPerfectNumber.no_dris_five_s_odd_eq_three p m s hp hp2 hp4 hm hpm h
  · exact OddPerfectNumber.no_dris_five_s_odd_ge_five p m s hp hp2 hp4 hm hpm hs_not_even h

#print axioms solution
