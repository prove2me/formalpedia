-- Prove2me | solution 1 for QuarterSumLadder.card_half_filter_quarter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:07:39.6788+00:00
-- url     : https://prove2.me/submissions/7de506d6-e84e-4813-8f51-964d9e0120a9

module
public import Definitions.Def_QuarterSumLadder_Classes
public import Definitions.Def_QuarterSumLadder_Counts
public import Theorems.Thm_QuarterSumLadder_half_mem
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
variable {χ : MulChar (ZMod p) GaussianInt} (hp8 : p % 8 = 1) (hχ : orderOf χ = 4)
include hp8 hχ
omit hp8 hχ
namespace QuarterSumLadder
theorem _root_.solution (z : GaussianInt) :
    (((fiber χ z).filter fun x => 2 * x.val < p).filter fun x => 4 * x.val < p) =
      (fiber χ z).filter fun x => 4 * x.val < p := by
  ext x; simp only [mem_filter]; constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨⟨h1, half_mem h3⟩, h3⟩
end QuarterSumLadder
