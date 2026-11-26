-- Prove2me | solution 1 for QuarterSumLadder.neg_one_ne_one_zmod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:05:22.201809+00:00
-- url     : https://prove2.me/submissions/d7bd7a1c-e2aa-431d-b65d-21abca3254f5

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
public import Theorems.Thm_QuarterSumLadder_two_ne_zero_zmod


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
omit hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution (hp2 : p ≠ 2) : (-1 : ZMod p) ≠ 1 := by
  intro h
  have h2 : (2 : ZMod p) = 0 := by linear_combination -h
  exact two_ne_zero_zmod hp2 h2
end QuarterSumLadder
