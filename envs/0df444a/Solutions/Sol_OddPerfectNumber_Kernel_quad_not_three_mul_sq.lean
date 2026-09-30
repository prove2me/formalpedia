-- Prove2me | solution 1 for OddPerfectNumber.Kernel.quad_not_three_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:53:03.468916+00:00
-- url     : https://prove2.me/submissions/efc849a1-4b6e-44b6-9f79-4721aa1bea79

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

theorem solution (p : Nat) (hp4 : p % 4 = 1) :
    ¬ ∃ z : Nat, (p ^ 2 - p + 1) = (3 * z ^ 2) := by
  rintro ⟨z, hz⟩
  have hp : 1 ≤ p := by omega
  have hple : p ≤ p ^ 2 := by nlinarith
  have heq : p ^ 2 + 1 = p + 3 * z ^ 2 := by omega
  have hm := congrArg (fun n : ℕ => n % 4) heq
  have hzlt : z % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases hzr : z % 4 <;>
    norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hp4, hzr] at hm
