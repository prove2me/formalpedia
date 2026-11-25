-- Prove2me | solution 1 for SCCThm8.choose_odd_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:44:11.041173+00:00
-- url     : https://prove2.me/submissions/c0566900-1ac6-4362-8ef6-28351f972c07

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
namespace SCCThm8
theorem _root_.solution (m : ℕ) :
    Nat.choose (2 * m + 1) m * (m + 1) = (2 * m + 1) * Nat.choose (2 * m) m := by
  have h := Nat.choose_mul_succ_eq (2 * m) m
  rw [show 2 * m + 1 - m = m + 1 by omega] at h
  rw [← h]; ring
end SCCThm8
