-- Prove2me | solution 1 for OddPerfectNumber.no_euler_equation_special_exponent_ge_nine
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T22:58:20.0465+00:00
-- url     : https://prove2.me/submissions/45a6a693-ce24-4870-b1ce-1ccc551ca9bd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_no_euler_ge_nine_eq_nine
import Theorems.Thm_OddPerfectNumber_no_euler_ge_nine_ge_thirteen

open OddPerfectNumber

theorem solution (p k m : Nat) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hk4 : k % 4 = 1) (hk9 : 9 ≤ k) (hm : Odd m) (hpm : ¬ p ∣ m) :
    (∑ d ∈ (p ^ k).divisors, d) * (∑ d ∈ (m ^ 2).divisors, d) ≠ 2 * (p ^ k * m ^ 2) := by
  by_cases heq : k = 9
  · subst heq
    -- Children were published with boolean `!=` conclusions; convert.
    exact bne_iff_ne.mp (no_euler_ge_nine_eq_nine p 9 m hp hp4 hk4 rfl hm hpm)
  · have h13 : 13 ≤ k := by omega
    exact bne_iff_ne.mp (no_euler_ge_nine_ge_thirteen p k m hp hp4 hk4 h13 hm hpm)
