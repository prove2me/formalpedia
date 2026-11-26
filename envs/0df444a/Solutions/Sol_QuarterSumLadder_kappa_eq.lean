-- Prove2me | solution 1 for QuarterSumLadder.kappa_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:09:59.704542+00:00
-- url     : https://prove2.me/submissions/e679de43-5b1b-46c2-a461-1c44480ce0ae

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
public import Theorems.Thm_QuarterSumLadder_R_zero
public import Theorems.Thm_QuarterSumLadder_R_one
public import Theorems.Thm_QuarterSumLadder_R_two
public import Theorems.Thm_QuarterSumLadder_R_three
public import Theorems.Thm_QuarterSumLadder_sum_R
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_mem_fiber
public import Theorems.Thm_QuarterSumLadder_mod_eight_aux
public import Theorems.Thm_QuarterSumLadder_ne_zero_of_mem_fiber
public import Theorems.Thm_QuarterSumLadder_quadraticChar_of_char_gi
public import Theorems.Thm_QuarterSumLadder_quadraticChar_of_char_one
public import Theorems.Thm_QuarterSumLadder_sum_univ_fibers
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
namespace QuarterSumLadder
theorem _root_.solution : kappa p = (Q p : ℤ) - 2 * (R χ 1 + R χ 3) := by
  have hpq := mod_eight_aux hp8
  set q : ZMod p → ℤ := fun x => quadraticChar (ZMod p) x with hq
  have h1 : kappa p = ∑ x ∈ univ.filter (fun x : ZMod p => x ≠ 0 ∧ 4 * x.val < p), q x := by
    unfold kappa
    refine sum_nbij' (fun n => (n : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      simp only [mem_filter, mem_range, mem_univ, true_and] at hn ⊢
      rw [ZMod.val_natCast_of_lt hn.1]
      refine ⟨?_, hn.2.2⟩
      rw [Ne, ← ZMod.val_eq_zero, ZMod.val_natCast_of_lt hn.1]; omega
    · intro x hx
      simp only [mem_filter, mem_range, mem_univ, true_and] at hx ⊢
      exact ⟨ZMod.val_lt x, val_pos_of_ne_zero hx.1, hx.2⟩
    · intro n hn
      simp only [mem_filter, mem_range] at hn
      exact ZMod.val_natCast_of_lt hn.1
    · intro x _; exact ZMod.natCast_zmod_val x
    · intro n _; simp [hq, legendreSym]
  have h2 := sum_univ_fibers hχ (fun x : ZMod p => if x ≠ 0 ∧ 4 * x.val < p then q x else 0)
    (by simp)
  rw [← sum_filter] at h2
  have hf : ∀ w : GaussianInt, w ≠ 0 → ∀ ε : ℤ, (∀ x ∈ fiber χ w, q x = ε) →
      ∑ x ∈ fiber χ w, (if x ≠ 0 ∧ 4 * x.val < p then q x else 0) =
        ε * ((fiber χ w).filter fun x => 4 * x.val < p).card := by
    intro w hw ε hε
    rw [card_eq_sum_ones, Nat.cast_sum, mul_sum, sum_filter]
    refine sum_congr rfl fun x hx => ?_
    by_cases h4 : 4 * x.val < p <;> simp [h4, ne_zero_of_mem_fiber hw hx, hε x hx]
  have hq1 : ∀ w : GaussianInt, (w = 1 ∨ w = -1) → ∀ x ∈ fiber χ w, q x = 1 := by
    intro w hw x hx
    have hx0 := ne_zero_of_mem_fiber (by rcases hw with rfl | rfl <;> decide) hx
    show (quadraticChar (ZMod p) x : ℤ) = 1; rw [quadraticChar_of_char_one hχ hx0 (by rw [mem_fiber.1 hx]; exact hw)]
  have hqi : ∀ w : GaussianInt, (w = gi ∨ w = -gi) → ∀ x ∈ fiber χ w, q x = -1 := by
    intro w hw x hx
    have hx0 := ne_zero_of_mem_fiber (by rcases hw with rfl | rfl <;> decide) hx
    show (quadraticChar (ZMod p) x : ℤ) = -1; rw [quadraticChar_of_char_gi hχ hx0 (by rw [mem_fiber.1 hx]; exact hw)]
  rw [hf 1 one_ne_zero 1 (hq1 1 (Or.inl rfl)), hf gi (by decide) (-1) (hqi gi (Or.inl rfl)),
    hf (-1) (by decide) 1 (hq1 (-1) (Or.inr rfl)), hf (-gi) (by decide) (-1) (hqi (-gi) (Or.inr rfl)),
    ← R_zero, ← R_one, ← R_two, ← R_three] at h2
  rw [h1, h2]
  have hs := sum_R hp8 hχ
  have : (Q p : ℤ) = R χ 0 + R χ 1 + R χ 2 + R χ 3 := by exact_mod_cast hs.symm
  rw [this]; ring
end QuarterSumLadder
