-- Prove2me | solution 1 for QuarterSumLadder.R_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:03:04.306157+00:00
-- url     : https://prove2.me/submissions/21c0f784-f4dd-40bd-a9e4-2d0892749730

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
public import Theorems.Thm_QuarterSumLadder_mem_fiber
public import Theorems.Thm_QuarterSumLadder_ne_zero_of_mem_fiber
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_val_pos_of_ne_zero
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
omit hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution (r : ℕ) : R χ r = ((fiber χ (gi ^ r)).filter fun x => 4 * x.val < p).card := by
  have hz0 : gi ^ r ≠ 0 := pow_ne_zero _ (by decide)
  unfold R
  refine card_nbij' (fun n => (n : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hn ⊢
    rw [mem_fiber, ZMod.val_natCast_of_lt hn.1]
    exact ⟨hn.2.2.2, hn.2.2.1⟩
  · intro x hx
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq, mem_fiber] at hx ⊢
    refine ⟨ZMod.val_lt x, val_pos_of_ne_zero (ne_zero_of_mem_fiber hz0 (mem_fiber.2 hx.1)),
      hx.2, by rw [ZMod.natCast_zmod_val]; exact hx.1⟩
  · intro n hn
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hn
    exact ZMod.val_natCast_of_lt hn.1
  · intro x _; exact ZMod.natCast_zmod_val x
end QuarterSumLadder
