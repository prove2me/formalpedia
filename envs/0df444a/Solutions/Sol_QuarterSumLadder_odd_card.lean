-- Prove2me | solution 1 for QuarterSumLadder.odd_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:10:12.638996+00:00
-- url     : https://prove2.me/submissions/5df18b33-2e98-4c61-9c98-cd728d624ee1

module
public import Definitions.Def_QuarterSumLadder_Counts
public import Definitions.Def_QuarterSumLadder_WeightTwo
public import Theorems.Thm_QuarterSumLadder_card_odd_fiber
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
attribute [local simp] QuarterSumLadder.gi_im
attribute [local simp] QuarterSumLadder.gi_re



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
    2 * ((fiber χ z).filter fun x => x.val % 2 = 1).card = Q p := by
  have h := card_odd_fiber hp8 hχ hz
  have : ((fiber χ z).filter fun x => x.val % 2 = 1) = (fiber χ z).filter fun x => Odd x.val := by
    ext x; simp [Nat.odd_iff]
  rw [this]; exact h
end QuarterSumLadder
