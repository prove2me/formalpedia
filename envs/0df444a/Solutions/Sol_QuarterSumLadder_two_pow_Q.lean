-- Prove2me | solution 1 for QuarterSumLadder.two_pow_Q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:10:08.770427+00:00
-- url     : https://prove2.me/submissions/de8cc34a-d519-4496-94c5-d78d6c747666

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
public import Theorems.Thm_QuarterSumLadder_R_zero
public import Theorems.Thm_QuarterSumLadder_R_two
public import Theorems.Thm_QuarterSumLadder_sum_R
public import Theorems.Thm_QuarterSumLadder_half_mem
public import Theorems.Thm_QuarterSumLadder_gaussMap_char
public import Theorems.Thm_QuarterSumLadder_neg_one_pow_mul_self
public import Theorems.Thm_QuarterSumLadder_card_half_fiber
public import Theorems.Thm_QuarterSumLadder_char_two
public import Theorems.Thm_QuarterSumLadder_gaussMap_mem_half
public import Theorems.Thm_QuarterSumLadder_gauss_product
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_hp2_of
public import Theorems.Thm_QuarterSumLadder_mem_fiber
public import Theorems.Thm_QuarterSumLadder_ne_zero_of_mem_fiber
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
theorem _root_.solution : (2 : ZMod p) ^ Q p = (-1) ^ (R χ 1 + R χ 3) := by
  have hp2 := hp2_of hp8
  set A := (fiber χ 1 ∪ fiber χ (-1)).filter fun x => 2 * x.val < p with hA
  have hdisj : Disjoint (fiber χ 1) (fiber χ (-1)) := by
    rw [disjoint_left]; intro x h1 h2
    rw [mem_fiber] at h1 h2; rw [h1] at h2; exact absurd h2 (by decide)
  have hcardA : A.card = Q p := by
    rw [hA, filter_union, card_union_of_disjoint (disjoint_filter_filter hdisj)]
    have h1 := card_half_fiber hp8 hχ (z := 1) (Or.inl rfl)
    have h2 := card_half_fiber hp8 hχ (z := -1) (Or.inr (Or.inr (Or.inl rfl)))
    omega
  have hmem : ∀ x ∈ A, x ≠ 0 ∧ 2 * x.val < p := by
    intro x hx
    rw [hA, mem_filter, mem_union] at hx
    refine ⟨?_, hx.2⟩
    rcases hx.1 with h | h
    · exact ne_zero_of_mem_fiber one_ne_zero h
    · exact ne_zero_of_mem_fiber (by decide) h
  have hφ : ∀ x ∈ A, gaussMap x ∈ A := by
    intro x hx
    have hx0 := (hmem x hx).1
    rw [hA, mem_filter, mem_union] at hx ⊢
    refine ⟨?_, gaussMap_mem_half hp2 hx0 hx.2⟩
    rw [mem_fiber, mem_fiber, gaussMap_char hp8 hχ]
    rcases char_two hp8 hχ with h2 | h2 <;> rcases hx.1 with h | h <;>
      rw [mem_fiber] at h <;> rw [h2, h] <;> norm_num
  have hkey := gauss_product hp2 A hmem hφ
  have hq : (A.filter fun x => 4 * x.val < p).card = R χ 0 + R χ 2 := by
    rw [hA, filter_filter, filter_union, card_union_of_disjoint
      (disjoint_filter_filter hdisj), R_zero, R_two]
    congr 2 <;> ext x <;> simp only [mem_filter] <;>
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, half_mem h.2, h.2⟩⟩
  have hsplit := card_filter_add_card_filter_not (s := A) (p := fun x => 4 * x.val < p)
  have hsum := sum_R hp8 hχ
  rw [hq, hcardA] at hsplit
  have hμ : (A.filter fun x => ¬ 4 * x.val < p).card = R χ 1 + R χ 3 := by omega
  rw [hμ, hcardA] at hkey
  calc (2 : ZMod p) ^ Q p = (2 : ZMod p) ^ Q p * ((-1) ^ (R χ 1 + R χ 3) * (-1) ^ (R χ 1 + R χ 3)) :=
        by rw [neg_one_pow_mul_self, mul_one]
    _ = (-1) ^ (R χ 1 + R χ 3) := by rw [← mul_assoc, hkey, one_mul]
end QuarterSumLadder
