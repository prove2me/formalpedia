-- Prove2me | solution 1 for QuarterSumLadder.char_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:01:38.080338+00:00
-- url     : https://prove2.me/submissions/d2cece7a-71e2-4e8a-ae53-be6460251cae

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
public import Theorems.Thm_QuarterSumLadder_hp2_of
public import Theorems.Thm_QuarterSumLadder_isSquare_iff_char
public import Theorems.Thm_QuarterSumLadder_two_ne_zero_zmod


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution : χ 2 = 1 ∨ χ 2 = -1 := by
  have hsq : IsSquare (2 : ZMod p) := (ZMod.exists_sq_eq_two_iff (hp2_of hp8)).2 (Or.inl hp8)
  exact (isSquare_iff_char hχ (two_ne_zero_zmod (hp2_of hp8))).1 hsq
end QuarterSumLadder
