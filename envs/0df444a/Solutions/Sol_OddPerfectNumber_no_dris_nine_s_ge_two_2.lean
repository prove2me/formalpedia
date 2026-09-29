-- Prove2me | solution 2 for OddPerfectNumber.no_dris_nine_s_ge_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T07:09:39.182369+00:00
-- url     : https://prove2.me/submissions/cfe7b8c8-cb82-418b-99e8-6e88711a28c8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_no_dris_nine_s_ge_two_even
import Theorems.Thm_OddPerfectNumber_no_dris_nine_s_ge_two_not_even

theorem _root_.solution (p k m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk9 : k = 9) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hs2 : 2 ≤ s) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  by_cases hse : Even s
  · exact OddPerfectNumber.no_dris_nine_s_ge_two_even p k m s hp hp2 hp4 hk4 hk9 hm hpm hs2 hse
  · exact OddPerfectNumber.no_dris_nine_s_ge_two_not_even p k m s hp hp2 hp4 hk4 hk9 hm hpm hs2 hse

#print axioms solution
