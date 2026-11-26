-- Prove2me | solution 1 for QuarterSumLadder.class_sizes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:17:46.746543+00:00
-- url     : https://prove2.me/submissions/d67dfbad-2809-4b8f-9f76-98915d3fd2bd

module
public import Definitions.Def_QuarterSumLadder
public import Definitions.Def_QuarterSumLadder_Solution
public import Theorems.Thm_QuarterSumLadder_card_fiber
public import Theorems.Thm_QuarterSumLadder_sum_R


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace QuarterSumLadder
theorem _root_.solution {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4) {z : GaussianInt}
    (hz : (z = 1 ∨ z = gi ∨ z = -1 ∨ z = -gi)) :
    (fiber χ z).card = Q p ∧ R χ 0 + R χ 1 + R χ 2 + R χ 3 = Q p :=
  ⟨card_fiber hp8 hχ hz, sum_R hp8 hχ⟩
end QuarterSumLadder
