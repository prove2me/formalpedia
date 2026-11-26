-- Prove2me | solution 1 for QuarterSumLadder.val_two_mul_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:57:25.78782+00:00
-- url     : https://prove2.me/submissions/38297bac-79fb-44af-a513-3fe7e2c74e99

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
theorem _root_.solution {x : ZMod p} (hx : 2 * x.val < p) : (2 * x).val = 2 * x.val := by
  have : (2 * x : ZMod p) = ((2 * x.val : ℕ) : ZMod p) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [this, ZMod.val_natCast_of_lt hx]
end QuarterSumLadder
