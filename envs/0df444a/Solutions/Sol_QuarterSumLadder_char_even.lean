-- Prove2me | solution 1 for QuarterSumLadder.char_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:01:09.697139+00:00
-- url     : https://prove2.me/submissions/c8ac3606-0ff8-44a3-8672-c2c4ea0e55b8

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
public import Theorems.Thm_QuarterSumLadder_quartic_apply_neg_one_of_one


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution : χ (-1) = 1 := quartic_apply_neg_one_of_one χ hχ hp8
end QuarterSumLadder
