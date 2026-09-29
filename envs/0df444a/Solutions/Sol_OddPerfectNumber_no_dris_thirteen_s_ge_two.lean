-- Prove2me | solution 1 for OddPerfectNumber.no_dris_thirteen_s_ge_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T06:13:10.306879+00:00
-- url     : https://prove2.me/submissions/346c4cb9-f004-42e6-a347-0784e6870e2e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_no_dris_thirteen_s_ge_two_even
import Theorems.Thm_OddPerfectNumber_no_dris_thirteen_s_ge_two_not_even

open OddPerfectNumber

theorem solution (p k m s : Nat) (hp : p.Prime) (hp2 : p != 2)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk13 : 13 ≤ k) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hs2 : 2 ≤ s) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ k).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ k * s) := by
  intro hcon
  by_cases hs_even : Even s
  · exact no_dris_thirteen_s_ge_two_even p k m s hp hp2 hp4 hk4 hk13 hm hpm hs2 hs_even hcon
  · exact no_dris_thirteen_s_ge_two_not_even p k m s hp hp2 hp4 hk4 hk13 hm hpm hs2 hs_even hcon
