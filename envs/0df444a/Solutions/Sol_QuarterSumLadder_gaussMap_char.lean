-- Prove2me | solution 1 for QuarterSumLadder.gaussMap_char
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:06:12.552698+00:00
-- url     : https://prove2.me/submissions/c6f720cd-b41e-48fa-9bc5-6cafc26af918

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
public import Theorems.Thm_QuarterSumLadder_char_neg


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution (x : ZMod p) : χ (gaussMap x) = χ 2 * χ x := by
  unfold gaussMap
  split_ifs
  · rw [map_mul]
  · rw [char_neg hp8 hχ, map_mul]
end QuarterSumLadder
