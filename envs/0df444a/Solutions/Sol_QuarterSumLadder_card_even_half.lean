-- Prove2me | solution 1 for QuarterSumLadder.card_even_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:04:18.631623+00:00
-- url     : https://prove2.me/submissions/602d4141-565c-401a-88dd-c1d8e96e4f7e

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
public import Theorems.Thm_QuarterSumLadder_hp2_of
public import Theorems.Thm_QuarterSumLadder_mem_fiber
public import Theorems.Thm_QuarterSumLadder_char_two_sq
public import Theorems.Thm_QuarterSumLadder_val_half_of_even
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_val_two_mul_of_lt
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
theorem _root_.solution (z : GaussianInt) :
    ((fiber χ z).filter fun x => 2 * x.val < p ∧ Even x.val).card =
      ((fiber χ (χ 2 * z)).filter fun x => 4 * x.val < p).card := by
  have hsq := char_two_sq hp8 hχ
  have hp2 := hp2_of hp8
  refine card_nbij' (fun y => ((y.val / 2 : ℕ) : ZMod p)) (fun x => 2 * x) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [coe_filter, Set.mem_ofPred_eq, mem_fiber] at hy ⊢
    obtain ⟨hyz, hyl, hye⟩ := hy
    have hlt : y.val / 2 < p := by omega
    rw [ZMod.val_natCast_of_lt hlt]
    refine ⟨?_, by omega⟩
    have h2 : χ 2 * χ ((y.val / 2 : ℕ) : ZMod p) = z := by
      rw [← map_mul, val_half_of_even hye, hyz]
    linear_combination (χ 2) * h2 - χ ((y.val / 2 : ℕ) : ZMod p) * hsq
  · intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq, mem_fiber] at hx ⊢
    have hv := val_two_mul_of_lt (show 2 * x.val < p by omega)
    rw [hv, map_mul, hx.1]
    refine ⟨by linear_combination z * hsq, by omega, even_two_mul _⟩
  · intro y hy
    simp only [coe_filter, Set.mem_ofPred_eq] at hy
    exact val_half_of_even hy.2.2
  · intro x hx
    simp only [coe_filter, Set.mem_ofPred_eq] at hx
    have hv := val_two_mul_of_lt (show 2 * x.val < p by omega)
    show (((2 * x).val / 2 : ℕ) : ZMod p) = x
    rw [hv, show 2 * x.val / 2 = x.val by omega, ZMod.natCast_zmod_val]
end QuarterSumLadder
