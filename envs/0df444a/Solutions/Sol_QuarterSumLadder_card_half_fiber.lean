-- Prove2me | solution 1 for QuarterSumLadder.card_half_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:05:57.676002+00:00
-- url     : https://prove2.me/submissions/4a8e29df-18fe-45e0-85f2-90644f9f3e17

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
public import Theorems.Thm_QuarterSumLadder_hp2_of
public import Theorems.Thm_QuarterSumLadder_two_mul_card_filter_of_neg
public import Theorems.Thm_QuarterSumLadder_neg_mem_fiber
public import Theorems.Thm_QuarterSumLadder_ne_zero_of_mem_fiber
public import Theorems.Thm_QuarterSumLadder_card_fiber
public import Theorems.Thm_QuarterSumLadder_neg_half_iff


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution {z : GaussianInt} (hz : FourVal z) :
    2 * ((fiber χ z).filter fun x => 2 * x.val < p).card = Q p := by
  have hz0 : z ≠ 0 := by rcases hz with rfl | rfl | rfl | rfl <;> decide
  rw [two_mul_card_filter_of_neg _ (fun x hx => neg_mem_fiber hp8 hχ hx)
    (fun x hx => neg_half_iff (hp2_of hp8) (ne_zero_of_mem_fiber hz0 hx)), card_fiber hp8 hχ hz]
end QuarterSumLadder
