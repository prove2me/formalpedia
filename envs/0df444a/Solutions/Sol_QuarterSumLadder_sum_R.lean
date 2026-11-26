-- Prove2me | solution 1 for QuarterSumLadder.sum_R
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:08:40.012806+00:00
-- url     : https://prove2.me/submissions/0e71fa04-0051-42f5-93fe-fc583eb2e0a1

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
public import Theorems.Thm_QuarterSumLadder_card_quarter
public import Theorems.Thm_QuarterSumLadder_R_zero
public import Theorems.Thm_QuarterSumLadder_R_one
public import Theorems.Thm_QuarterSumLadder_R_two
public import Theorems.Thm_QuarterSumLadder_R_three
public import Theorems.Thm_QuarterSumLadder_gi_im
public import Theorems.Thm_QuarterSumLadder_gi_re
public import Theorems.Thm_QuarterSumLadder_ne_zero_of_mem_fiber
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
theorem _root_.solution : R χ 0 + R χ 1 + R χ 2 + R χ 3 = Q p := by
  have h := sum_univ_fibers hχ
    (fun x : ZMod p => if x ≠ 0 ∧ 4 * x.val < p then (1 : ℕ) else 0) (by simp)
  have hf : ∀ w : GaussianInt, w ≠ 0 →
      ∑ x ∈ fiber χ w, (if x ≠ 0 ∧ 4 * x.val < p then (1 : ℕ) else 0) =
        ((fiber χ w).filter fun x => 4 * x.val < p).card := by
    intro w hw
    rw [card_filter]
    exact sum_congr rfl fun x hx => by simp [ne_zero_of_mem_fiber hw hx]
  rw [hf 1 one_ne_zero, hf gi (by decide), hf (-1) (by decide), hf (-gi) (by decide),
    sum_boole, Nat.cast_id, card_quarter hp8] at h
  rw [R_zero, R_one, R_two, R_three]
  omega
end QuarterSumLadder
