-- Prove2me | solution 1 for SCCThm8.trin_mul_factorial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:44:18.350781+00:00
-- url     : https://prove2.me/submissions/dbff5fe4-ee13-4817-8f40-f55c28538190

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
namespace SCCThm8
theorem _root_.solution (k : ℕ) : trin k * (k.factorial) ^ 3 = (3 * k).factorial := by
  have h1 := Nat.add_choose_mul_factorial_mul_factorial (2 * k) k
  have h2 := Nat.add_choose_mul_factorial_mul_factorial k k
  rw [show 2 * k + k = 3 * k by ring] at h1
  rw [show k + k = 2 * k by ring] at h2
  unfold trin
  rw [← h1, ← h2]; ring
end SCCThm8
