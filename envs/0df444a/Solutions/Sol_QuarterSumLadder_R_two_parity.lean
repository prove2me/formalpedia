-- Prove2me | solution 1 for QuarterSumLadder.R_two_parity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:09:18.975356+00:00
-- url     : https://prove2.me/submissions/da1fdf75-dde1-49aa-ab97-05ec84b0793a

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
public import Theorems.Thm_QuarterSumLadder_R_two
public import Theorems.Thm_QuarterSumLadder_neg_one_ne_one_zmod
public import Theorems.Thm_QuarterSumLadder_gauss_class
public import Theorems.Thm_QuarterSumLadder_hp2_of


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
    R χ 2 % 2 = ((p - 1) / 8 + if (2 : ZMod p) ^ ((p - 1) / 8) = -1 then 1 else 0) % 2 := by
  have hp2 := hp2_of hp8
  have g2 := gauss_class hp8 hχ hw (z := -1) (Or.inr (Or.inr (Or.inl rfl)))
  rw [← R_two] at g2
  have hQ8 : Q p / 2 = (p - 1) / 8 := by unfold Q; omega
  rw [hQ8] at g2
  obtain ⟨hk, hle⟩ := g2
  have h1 := neg_one_ne_one_zmod hp2
  rcases Nat.even_or_odd ((p - 1) / 8 - R χ 2) with he | ho
  · rw [he.neg_one_pow, mul_one] at hk
    rw [hk, if_neg h1.symm]
    obtain ⟨j, hj⟩ := he; omega
  · rw [ho.neg_one_pow] at hk
    have : (2 : ZMod p) ^ ((p - 1) / 8) = -1 := by linear_combination -hk
    rw [if_pos this]
    obtain ⟨j, hj⟩ := ho; omega
end QuarterSumLadder
