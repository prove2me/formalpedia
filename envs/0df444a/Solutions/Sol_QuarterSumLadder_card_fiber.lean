-- Prove2me | solution 1 for QuarterSumLadder.card_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:04:01.446027+00:00
-- url     : https://prove2.me/submissions/8e4934d7-a6d3-4f4a-b90c-261ffa523417

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
public import Theorems.Thm_QuarterSumLadder_mod_eight_aux
public import Theorems.Thm_QuarterSumLadder_ne_zero_of_mem_fiber
public import Theorems.Thm_QuarterSumLadder_sum_univ_fibers
public import Theorems.Thm_QuarterSumLadder_card_fiber_eq_one
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
theorem _root_.solution {z : GaussianInt} (hz : FourVal z) : (fiber χ z).card = Q p := by
  have h := sum_univ_fibers hχ (fun x : ZMod p => if x = 0 then 0 else (1 : ℕ)) (by simp)
  have hf : ∀ w : GaussianInt, w ≠ 0 →
      ∑ x ∈ fiber χ w, (if x = 0 then 0 else (1 : ℕ)) = (fiber χ w).card := by
    intro w hw
    rw [card_eq_sum_ones]
    exact sum_congr rfl fun x hx => by simp [ne_zero_of_mem_fiber hw hx]
  rw [hf 1 one_ne_zero, hf gi (by decide), hf (-1) (by decide), hf (-gi) (by decide),
    card_fiber_eq_one hχ (Or.inr (Or.inl rfl)), card_fiber_eq_one hχ (Or.inr (Or.inr (Or.inl rfl))),
    card_fiber_eq_one hχ (Or.inr (Or.inr (Or.inr rfl)))] at h
  have hl : ∑ x : ZMod p, (if x = 0 then 0 else (1 : ℕ)) = p - 1 := by
    rw [sum_ite, sum_const_zero, zero_add, sum_const, smul_eq_mul, mul_one,
      filter_ne', card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
  rw [hl] at h
  rw [card_fiber_eq_one hχ hz]
  have := mod_eight_aux hp8
  omega
end QuarterSumLadder
