-- Prove2me | solution 1 for QuarterSumLadder.E_add_R
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:11:57.917297+00:00
-- url     : https://prove2.me/submissions/386b96b7-a6c0-46cc-84cc-81596428fe7f

module
public import Definitions.Def_QuarterSumLadder_Counts
public import Definitions.Def_QuarterSumLadder_WeightTwo
public import Theorems.Thm_QuarterSumLadder_fourVal_mul_two
public import Theorems.Thm_QuarterSumLadder_E_eq
public import Theorems.Thm_QuarterSumLadder_card_even_half
public import Theorems.Thm_QuarterSumLadder_card_half_fiber
public import Theorems.Thm_QuarterSumLadder_char_two_sq
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
    E χ z + ((fiber χ z).filter fun x => 4 * x.val < p).card = Q p / 2 := by
  have hsq := char_two_sq hp8 hχ
  set y := χ 2 * z with hy
  have hyv := fourVal_mul_two hp8 hχ hz
  have hhalf := card_half_fiber hp8 hχ hyv
  have hsplit := card_filter_add_card_filter_not (s := (fiber χ y).filter fun x => 2 * x.val < p)
    (p := fun x => Odd x.val)
  rw [filter_filter, filter_filter] at hsplit
  have heven : ((fiber χ y).filter fun x => 2 * x.val < p ∧ ¬ Odd x.val) =
      (fiber χ y).filter fun x => 2 * x.val < p ∧ Even x.val := by
    ext x; simp [Nat.not_odd_iff_even]
  rw [heven, card_even_half hp8 hχ, hy, ← mul_assoc, hsq, one_mul] at hsplit
  rw [E_eq hp8 hχ]
  omega
end QuarterSumLadder
