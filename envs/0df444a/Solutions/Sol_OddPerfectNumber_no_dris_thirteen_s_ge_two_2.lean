-- Prove2me | solution 2 for OddPerfectNumber.no_dris_thirteen_s_ge_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T07:10:54.939691+00:00
-- url     : https://prove2.me/submissions/22ec3d21-0f72-4e2a-a69e-356df3ed5fc5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_no_dris_thirteen_s_ge_two_even
import Theorems.Thm_OddPerfectNumber_no_dris_thirteen_s_ge_two_not_even

theorem _root_.solution (p k m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk13 : 13 ≤ k) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hs2 : 2 ≤ s) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  by_cases hse : Even s
  · exact OddPerfectNumber.no_dris_thirteen_s_ge_two_even p k m s hp hp2 hp4 hk4 hk13 hm hpm hs2 hse
  · exact OddPerfectNumber.no_dris_thirteen_s_ge_two_not_even p k m s hp hp2 hp4 hk4 hk13 hm hpm hs2 hse

#print axioms solution
