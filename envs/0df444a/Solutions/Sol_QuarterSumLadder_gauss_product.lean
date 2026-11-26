-- Prove2me | solution 1 for QuarterSumLadder.gauss_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:02:41.832284+00:00
-- url     : https://prove2.me/submissions/b8b90778-588a-4b25-8b86-76ebea489a1b

module
public import Definitions.Def_QuarterSumLadder_Defs
public import Definitions.Def_QuarterSumLadder_Prelim
public import Theorems.Thm_QuarterSumLadder_two_ne_zero_zmod
public import Theorems.Thm_QuarterSumLadder_neg_half_iff
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
namespace QuarterSumLadder
theorem _root_.solution (hp2 : p ≠ 2) (A : Finset (ZMod p))
    (hA : ∀ x ∈ A, x ≠ 0 ∧ 2 * x.val < p) (hφ : ∀ x ∈ A, gaussMap x ∈ A) :
    (2 : ZMod p) ^ A.card * (-1) ^ (A.filter fun x => ¬ 4 * x.val < p).card = 1 := by
  have h20 := two_ne_zero_zmod hp2
  have hinj : Set.InjOn gaussMap (A : Set (ZMod p)) := by
    intro x hx y hy hxy
    rw [mem_coe] at hx hy
    obtain ⟨hx0, hxl⟩ := hA x hx
    obtain ⟨hy0, hyl⟩ := hA y hy
    have key : x = y ∨ x = -y := by
      simp only [gaussMap] at hxy
      split_ifs at hxy
      · exact Or.inl (mul_left_cancel₀ h20 hxy)
      · right; apply mul_left_cancel₀ h20; rw [hxy]; ring
      · right; apply mul_left_cancel₀ h20; rw [mul_neg, ← hxy]; ring
      · left; exact mul_left_cancel₀ h20 (neg_injective hxy)
    rcases key with h | h
    · exact h
    · exfalso
      have := (neg_half_iff hp2 hy0).1
      rw [← h] at this
      exact this hxl hyl
  have himage : A.image gaussMap = A :=
    eq_of_subset_of_card_le (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hy; exact hφ x hx)
      (by rw [card_image_of_injOn hinj])
  have hprod : ∏ x ∈ A, gaussMap x = ∏ x ∈ A, x := by
    calc ∏ x ∈ A, gaussMap x = ∏ y ∈ A.image gaussMap, y :=
          (prod_image (f := fun y => y) (fun x hx y hy h => hinj hx hy h)).symm
      _ = ∏ x ∈ A, x := by rw [himage]
  have hsplit : ∀ x ∈ A, gaussMap x = (if 4 * x.val < p then 1 else -1) * 2 * x := by
    intro x _; simp only [gaussMap]; split_ifs <;> ring
  rw [prod_congr rfl hsplit, prod_mul_distrib, prod_mul_distrib, prod_const, prod_ite,
    prod_const_one, one_mul, prod_const] at hprod
  have hP0 : ∏ x ∈ A, x ≠ 0 := prod_ne_zero_iff.2 fun x hx => (hA x hx).1
  have := (mul_eq_right₀ hP0).1 hprod
  linear_combination this
end QuarterSumLadder
