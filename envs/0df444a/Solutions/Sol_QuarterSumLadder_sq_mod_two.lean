-- Prove2me | solution 1 for QuarterSumLadder.sq_mod_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:54:08.43707+00:00
-- url     : https://prove2.me/submissions/84dda203-aa63-4c6f-aba8-41675fbf85ad

module
public import Mathlib
public import Definitions.Def_QuarterSumLadder_Arith

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
namespace QuarterSumLadder
theorem _root_.solution (a : ℤ) : a ^ 2 % 2 = a % 2 := by
  rcases Int.even_or_odd a with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · have : (r + r) ^ 2 = 2 * (2 * r ^ 2) := by ring
    rw [this]; omega
  · have : (2 * r + 1) ^ 2 = 2 * (2 * r ^ 2 + 2 * r) + 1 := by ring
    rw [this]; omega
end QuarterSumLadder
