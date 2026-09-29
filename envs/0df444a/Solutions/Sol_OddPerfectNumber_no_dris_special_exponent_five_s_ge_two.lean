-- Prove2me | solution 1 for OddPerfectNumber.no_dris_special_exponent_five_s_ge_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T22:47:31.434589+00:00
-- url     : https://prove2.me/submissions/1b9bed79-9a38-48a8-89d4-5db0dbaf0651
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_no_dris_five_s_ge_two_even
import Theorems.Thm_OddPerfectNumber_no_dris_five_s_ge_two_not_even

open OddPerfectNumber

theorem solution (p m s : Nat) (hp : p.Prime) (hp2 : p ≠ 2)
    (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m) (hs : 2 ≤ s) :
    ¬ (2 * m ^ 2 = (∑ d ∈ (p ^ 5).divisors, d) * s ∧
      (∑ d ∈ (m ^ 2).divisors, d) = p ^ 5 * s) := by
  intro h
  -- Children were published with boolean `!=`; bridge `Ne` to `(bne) = true`.
  have hp2b : (p != 2) = true := bne_iff_ne.mpr hp2
  by_cases he : Even s
  · exact no_dris_five_s_ge_two_even p m s hp hp2b hp4 hm hpm hs he h
  · exact no_dris_five_s_ge_two_not_even p m s hp hp2b hp4 hm hpm hs he h
