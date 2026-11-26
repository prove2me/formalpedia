-- Prove2me | solution 1 for QuarterSumLadder.E_sums
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:10.564684+00:00
-- url     : https://prove2.me/submissions/dbc7eba8-868f-440a-9a39-b3168d88b2d0

module
public import Definitions.Def_QuarterSumLadder_Counts
public import Definitions.Def_QuarterSumLadder_WeightTwo
public import Theorems.Thm_QuarterSumLadder_E_add_R
public import Theorems.Thm_QuarterSumLadder_R_one
public import Theorems.Thm_QuarterSumLadder_R_three
public import Theorems.Thm_QuarterSumLadder_R_two
public import Theorems.Thm_QuarterSumLadder_R_zero
public import Theorems.Thm_QuarterSumLadder_mod_eight_aux
public import Theorems.Thm_QuarterSumLadder_sum_R


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution : E χ 1 + E χ (-1) = R χ 1 + R χ 3 ∧ E χ gi + E χ (-gi) = R χ 0 + R χ 2 := by
  have a := E_add_R hp8 hχ (z := 1) (Or.inl rfl)
  have b := E_add_R hp8 hχ (z := gi) (Or.inr (Or.inl rfl))
  have c := E_add_R hp8 hχ (z := -1) (Or.inr (Or.inr (Or.inl rfl)))
  have d := E_add_R hp8 hχ (z := -gi) (Or.inr (Or.inr (Or.inr rfl)))
  rw [← R_zero] at a; rw [← R_one] at b; rw [← R_two] at c; rw [← R_three] at d
  have hs := sum_R hp8 hχ
  have hQ : 2 ∣ Q p := by have := mod_eight_aux hp8; unfold Q; omega
  omega
end QuarterSumLadder
