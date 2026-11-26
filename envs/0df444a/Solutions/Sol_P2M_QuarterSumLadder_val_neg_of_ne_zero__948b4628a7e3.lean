-- Prove2me | solution 1 for P2M_QuarterSumLadder_val_neg_of_ne_zero__948b4628a7e3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:56:07.568012+00:00
-- url     : https://prove2.me/submissions/33eddd75-1d61-4a24-8fa8-df7ada49ffa0

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
theorem _root_.solution {x : ZMod p} (hx : x ≠ 0) : (-x).val = p - x.val := by
  rw [ZMod.neg_val, ite_eq_right_iff.mpr (fun h => absurd h hx)]
end QuarterSumLadder
