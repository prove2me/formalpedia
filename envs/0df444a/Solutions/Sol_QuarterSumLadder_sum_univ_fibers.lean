-- Prove2me | solution 1 for QuarterSumLadder.sum_univ_fibers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:02:52.339932+00:00
-- url     : https://prove2.me/submissions/11f4b7b0-e457-4cc6-9c01-75f5b7a65055

module
public import Definitions.Def_QuarterSumLadder_Prelim
public import Definitions.Def_QuarterSumLadder_Classes
public import Theorems.Thm_QuarterSumLadder_char_ne_zero
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_quartic_values
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
omit hp8
namespace QuarterSumLadder
theorem _root_.solution {M : Type*} [AddCommMonoid M] (f : ZMod p → M) (h0 : f 0 = 0) :
    ∑ x, f x = ∑ x ∈ fiber χ 1, f x + ∑ x ∈ fiber χ gi, f x + ∑ x ∈ fiber χ (-1), f x +
      ∑ x ∈ fiber χ (-gi), f x := by
  have hmaps : ∀ x ∈ (univ : Finset (ZMod p)),
      χ x ∈ ({0, 1, gi, -1, -gi} : Finset GaussianInt) := by
    intro x _
    by_cases hx : x = 0
    · simp [hx, MulChar.map_zero]
    · rcases quartic_values χ hχ hx with h | h | h | h <;> simp [h]
  rw [← sum_fiberwise_of_maps_to hmaps, sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_singleton]
  have hz : ∑ x ∈ univ.filter (fun x => χ x = 0), f x = 0 := by
    refine sum_eq_zero fun x hx => ?_
    have hx0 : x = 0 := by
      by_contra h; exact char_ne_zero hχ h (mem_filter.1 hx).2
    rw [hx0, h0]
  rw [hz, zero_add]
  simp only [fiber, add_assoc]
end QuarterSumLadder
