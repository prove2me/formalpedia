-- Prove2me | solution 1 for QuarterSumLadder.neg_half_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:58:30.981806+00:00
-- url     : https://prove2.me/submissions/a841ada6-ee5d-49b3-843b-46d59df742cf

module
public import Definitions.Def_QuarterSumLadder_Defs
public import Definitions.Def_QuarterSumLadder_Prelim
public import Theorems.Thm_QuarterSumLadder_odd_p
public import Theorems.Thm_P2M_QuarterSumLadder_val_neg_of_ne_zero__948b4628a7e3
public import Theorems.Thm_QuarterSumLadder_val_pos_of_ne_zero

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution (hp2 : p ≠ 2) {x : ZMod p} (hx : x ≠ 0) :
    2 * (-x).val < p ↔ ¬ 2 * x.val < p := by
  rw [val_neg_of_ne_zero' hx]
  have h1 := ZMod.val_lt x
  have h2 := val_pos_of_ne_zero hx
  obtain ⟨k, hk⟩ := odd_p hp2
  omega
end QuarterSumLadder
