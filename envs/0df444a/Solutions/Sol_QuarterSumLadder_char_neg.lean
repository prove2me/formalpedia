-- Prove2me | solution 1 for QuarterSumLadder.char_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:02:40.820574+00:00
-- url     : https://prove2.me/submissions/4eac6fff-af7f-4071-9238-26c862a91980

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
public import Theorems.Thm_QuarterSumLadder_char_even

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution (x : ZMod p) : χ (-x) = χ x := by
  calc χ (-x) = χ (-1 * x) := by rw [neg_one_mul]
    _ = χ (-1) * χ x := map_mul _ _ _
    _ = χ x := by rw [char_even hp8 hχ, one_mul]
end QuarterSumLadder
