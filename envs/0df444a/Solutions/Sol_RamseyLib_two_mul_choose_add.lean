-- Prove2me | solution 1 for RamseyLib.two_mul_choose_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:15:55.847988+00:00
-- url     : https://prove2.me/submissions/d711bbe3-633a-419d-8ff2-93213223a854

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyLib
namespace RamseyLib
theorem _root_.solution (k : ℕ) : 2 * k.choose 2 + k = k ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.choose_succ_succ, Nat.choose_one_right]; nlinarith
end RamseyLib
