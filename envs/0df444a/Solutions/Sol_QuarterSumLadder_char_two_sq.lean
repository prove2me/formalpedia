-- Prove2me | solution 1 for QuarterSumLadder.char_two_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:03:25.655609+00:00
-- url     : https://prove2.me/submissions/a70caa59-a47e-4a66-aabf-12529caeb55e

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
public import Theorems.Thm_QuarterSumLadder_char_two

set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution : χ 2 * χ 2 = 1 := by
  rcases char_two hp8 hχ with h | h <;> rw [h] <;> norm_num
end QuarterSumLadder
