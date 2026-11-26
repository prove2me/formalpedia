-- Prove2me | solution 1 for QuarterSumLadder.even_quartic_setting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:17:41.556445+00:00
-- url     : https://prove2.me/submissions/b099bd32-7ee4-41da-be44-ba3dca4a725a

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
public import Theorems.Thm_QuarterSumLadder_char_even
public import Theorems.Thm_QuarterSumLadder_char_two
public import Theorems.Thm_QuarterSumLadder_mod_eight_criterion


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) :
    χ (-1) = 1 ∧ (χ 2 = 1 ∨ χ 2 = -1) ∧ (χ 2 = 1 ↔ ∃ y : ZMod p, y ^ 4 = 2) :=
  ⟨char_even hp8 hχ, char_two hp8 hχ, (mod_eight_criterion hp8 hχ).2⟩
end QuarterSumLadder
