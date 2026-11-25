-- Prove2me | solution 1 for SCCThm8.trin_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:45:19.962272+00:00
-- url     : https://prove2.me/submissions/9c025bea-4872-49e2-8fd7-741ac6d4fefa

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric
public import Theorems.Thm_SCCThm8_trin_mul_factorial

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
namespace SCCThm8
theorem _root_.solution (k : ℕ) :
    (k + 1) ^ 2 * trin (k + 1) = 3 * (3 * k + 2) * (3 * k + 1) * trin k := by
  have h0 := trin_mul_factorial k
  have h1 := trin_mul_factorial (k + 1)
  have e1 : (3 * (k + 1)).factorial = (3 * k + 3) * ((3 * k + 2) * ((3 * k + 1) *
      (3 * k).factorial)) := by
    rw [show 3 * (k + 1) = 3 * k + 2 + 1 by ring, Nat.factorial_succ (3 * k + 2),
      Nat.factorial_succ (3 * k + 1), Nat.factorial_succ (3 * k)]
  have e2 : (k + 1).factorial = (k + 1) * k.factorial := Nat.factorial_succ k
  rw [e1, e2, ← h0] at h1
  have hf : 0 < (k + 1) * (k.factorial) ^ 3 := by positivity
  apply Nat.eq_of_mul_eq_mul_right hf
  calc (k + 1) ^ 2 * trin (k + 1) * ((k + 1) * k.factorial ^ 3)
      = trin (k + 1) * ((k + 1) * k.factorial) ^ 3 := by ring
    _ = (3 * k + 3) * ((3 * k + 2) * ((3 * k + 1) * (trin k * k.factorial ^ 3))) := h1
    _ = 3 * (3 * k + 2) * (3 * k + 1) * trin k * ((k + 1) * k.factorial ^ 3) := by ring
end SCCThm8
