-- Prove2me | solution 1 for QuarterSumLadder.gaussMap_mem_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:02:35.382991+00:00
-- url     : https://prove2.me/submissions/59e06eb9-8afc-4bc9-9f56-aa885c941db0

module
public import Definitions.Def_QuarterSumLadder_Defs
public import Definitions.Def_QuarterSumLadder_Prelim
public import Theorems.Thm_QuarterSumLadder_odd_p
public import Theorems.Thm_P2M_QuarterSumLadder_val_neg_of_ne_zero__948b4628a7e3
public import Theorems.Thm_QuarterSumLadder_two_ne_zero_zmod
public import Theorems.Thm_QuarterSumLadder_val_two_mul_of_lt

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution (hp2 : p ≠ 2) {x : ZMod p} (hx0 : x ≠ 0) (hx : 2 * x.val < p) :
    2 * (gaussMap x).val < p := by
  have hv := val_two_mul_of_lt hx
  have h2x : (2 * x : ZMod p) ≠ 0 := mul_ne_zero (two_ne_zero_zmod hp2) hx0
  unfold gaussMap
  split_ifs with h4
  · rw [hv]; omega
  · obtain ⟨k, hk⟩ := odd_p hp2
    rw [val_neg_of_ne_zero' h2x, hv]; omega
end QuarterSumLadder
