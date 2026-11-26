-- Prove2me | solution 1 for QuarterSumLadder.T2_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:11:51.408916+00:00
-- url     : https://prove2.me/submissions/51b9b342-4da6-4679-849f-d8f282937f7c

module
public import Definitions.Def_QuarterSumLadder_Counts
public import Definitions.Def_QuarterSumLadder_WeightTwo
public import Theorems.Thm_QuarterSumLadder_p_mul_c0
public import Theorems.Thm_QuarterSumLadder_p_mul_c1
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_mem_fiber
public import Theorems.Thm_QuarterSumLadder_sum_univ_fibers
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
theorem _root_.solution : T2 χ = (p : GaussianInt) * B2 χ := by
  have hfib : ∀ w : GaussianInt, ∑ x ∈ fiber χ w, χ x * (((x.val : ℤ) ^ 2 : ℤ) : GaussianInt) =
      w * ((U χ w : ℤ) : GaussianInt) := by
    intro w; unfold U; push_cast; rw [mul_sum]
    exact sum_congr rfl fun x hx => by rw [mem_fiber.1 hx]
  unfold T2
  rw [sum_univ_fibers hχ _ (by simp [MulChar.map_zero]), hfib, hfib, hfib, hfib]
  have h0 := p_mul_c0 hp8 hχ
  have h1 := p_mul_c1 hp8 hχ
  unfold B2
  set a := U χ 1
  set b := U χ gi
  set c := U χ (-1)
  set d := U χ (-gi)
  ext <;> simp [gi] <;> linarith
end QuarterSumLadder
