-- Prove2me | solution 1 for QuarterSumLadder.orbit_parity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:08:42.022328+00:00
-- url     : https://prove2.me/submissions/71fd632f-4a0d-45d6-9424-6e07d1890f44

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
public import Theorems.Thm_QuarterSumLadder_R_zero
public import Theorems.Thm_QuarterSumLadder_R_one
public import Theorems.Thm_QuarterSumLadder_R_two
public import Theorems.Thm_QuarterSumLadder_R_three
public import Theorems.Thm_QuarterSumLadder_gauss_class
public import Theorems.Thm_QuarterSumLadder_neg_one_pow_eq_iff
public import Theorems.Thm_QuarterSumLadder_hp2_of
public import Theorems.Thm_QuarterSumLadder_two_ne_zero_zmod


set_option autoImplicit true
@[expose] public section
public section
open QuarterSumLadder
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution (hw : χ 2 = 1) :
    R χ 1 % 2 = R χ 0 % 2 ∧ R χ 2 % 2 = R χ 0 % 2 ∧ R χ 3 % 2 = R χ 0 % 2 := by
  have hp2 := hp2_of hp8
  have g0 := gauss_class hp8 hχ hw (z := 1) (Or.inl rfl)
  have g1 := gauss_class hp8 hχ hw (z := gi) (Or.inr (Or.inl rfl))
  have g2 := gauss_class hp8 hχ hw (z := -1) (Or.inr (Or.inr (Or.inl rfl)))
  have g3 := gauss_class hp8 hχ hw (z := -gi) (Or.inr (Or.inr (Or.inr rfl)))
  rw [← R_zero] at g0
  rw [← R_one] at g1
  rw [← R_two] at g2
  rw [← R_three] at g3
  have hc : ∀ a b : ℕ, (2 : ZMod p) ^ (Q p / 2) * (-1) ^ a = 1 →
      (2 : ZMod p) ^ (Q p / 2) * (-1) ^ b = 1 → a % 2 = b % 2 := by
    intro a b ha hb
    rw [← neg_one_pow_eq_iff hp2]
    have h2 : (2 : ZMod p) ^ (Q p / 2) ≠ 0 := pow_ne_zero _ (two_ne_zero_zmod hp2)
    exact mul_left_cancel₀ h2 (ha.trans hb.symm)
  have e1 := hc _ _ g1.1 g0.1
  have e2 := hc _ _ g2.1 g0.1
  have e3 := hc _ _ g3.1 g0.1
  have := g0.2; have := g1.2; have := g2.2; have := g3.2
  omega
end QuarterSumLadder
