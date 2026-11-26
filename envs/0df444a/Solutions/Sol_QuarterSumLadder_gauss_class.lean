-- Prove2me | solution 1 for QuarterSumLadder.gauss_class
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:07:21.975718+00:00
-- url     : https://prove2.me/submissions/d964b391-6957-4378-a78e-4e39cc6a73df

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
public import Theorems.Thm_QuarterSumLadder_half_mem
public import Theorems.Thm_QuarterSumLadder_gaussMap_char
public import Theorems.Thm_QuarterSumLadder_card_half_fiber
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
theorem _root_.solution (hw : χ 2 = 1) {z : GaussianInt} (hz : FourVal z) :
    (2 : ZMod p) ^ (Q p / 2) *
        (-1) ^ (Q p / 2 - ((fiber χ z).filter fun x => 4 * x.val < p).card) = 1 ∧
      ((fiber χ z).filter fun x => 4 * x.val < p).card ≤ Q p / 2 := by
  have hp2 := hp2_of hp8
  have hz0 : z ≠ 0 := by rcases hz with rfl | rfl | rfl | rfl <;> decide
  set A := (fiber χ z).filter fun x => 2 * x.val < p with hA
  have hcardA : A.card = Q p / 2 := by
    have := card_half_fiber hp8 hχ hz; rw [← hA] at this; omega
  have hmem : ∀ x ∈ A, x ≠ 0 ∧ 2 * x.val < p := fun x hx =>
    ⟨ne_zero_of_mem_fiber hz0 (mem_filter.1 hx).1, (mem_filter.1 hx).2⟩
  have hφ : ∀ x ∈ A, gaussMap x ∈ A := by
    intro x hx
    have hx0 := (hmem x hx).1
    rw [hA, mem_filter] at hx ⊢
    refine ⟨?_, gaussMap_mem_half hp2 hx0 hx.2⟩
    rw [mem_fiber, gaussMap_char hp8 hχ, hw, one_mul]; exact mem_fiber.1 hx.1
  have hkey := gauss_product hp2 A hmem hφ
  have hsplit := card_filter_add_card_filter_not (s := A) (p := fun x => 4 * x.val < p)
  rw [hA, filter_filter] at hsplit
  have hf : ((fiber χ z).filter fun x => 2 * x.val < p ∧ 4 * x.val < p) =
      (fiber χ z).filter fun x => 4 * x.val < p := by
    ext x; simp only [mem_filter]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, half_mem h.2, h.2⟩⟩
  rw [hf, ← hA, hcardA] at hsplit
  rw [hcardA] at hkey
  refine ⟨?_, by omega⟩
  rwa [show (A.filter fun x => ¬ 4 * x.val < p).card =
    Q p / 2 - ((fiber χ z).filter fun x => 4 * x.val < p).card by omega] at hkey
end QuarterSumLadder
