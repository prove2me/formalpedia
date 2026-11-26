-- Prove2me | solution 1 for QuarterSumLadder.val_pos_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:57:22.833591+00:00
-- url     : https://prove2.me/submissions/6b8882a8-c23c-400a-99ed-f37b922f4c11

module
public import Definitions.Def_QuarterSumLadder_Defs
public import Definitions.Def_QuarterSumLadder_Prelim

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution {x : ZMod p} (hx : x ≠ 0) : 0 < x.val := by
  rw [Nat.pos_iff_ne_zero, ne_eq, ZMod.val_eq_zero]; exact hx
end QuarterSumLadder
