-- Prove2me | solution 1 for SCCThm8.centralBinom_succ_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:44:00.989457+00:00
-- url     : https://prove2.me/submissions/3eac20be-340e-48b7-a6b5-1cc71c8ced67

module
public import Mathlib
public import Definitions.Def_SCCThm8_Numeric

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
namespace SCCThm8
theorem _root_.solution (n : ℕ) : Nat.centralBinom (n + 1) < 4 * Nat.centralBinom n := by
  have h := Nat.succ_mul_centralBinom_succ n
  have hpos := Nat.centralBinom_pos n
  have : (n + 1) * Nat.centralBinom (n + 1) < (n + 1) * (4 * Nat.centralBinom n) := by
    rw [h]; nlinarith
  exact Nat.lt_of_mul_lt_mul_left this
end SCCThm8
