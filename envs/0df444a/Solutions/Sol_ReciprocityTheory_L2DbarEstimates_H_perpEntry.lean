-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.perpEntry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:39:21.478628+00:00
-- url     : https://prove2.me/submissions/27cf08ca-4d1d-4f6d-8dda-b8730f2bb984

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_HlinVsqPos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_hlin_vsq_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_hlin_orth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates ComplexConjugate
open scoped ENNReal InnerProductSpace
private lemma norm_sum_mul_sq_le_sum_sq_mul_sum_sq {ι : Type*} (s : Finset ι) (a b : ι → ℂ) :
    ‖∑ q ∈ s, a q * b q‖ ^ 2 ≤ (∑ q ∈ s, ‖a q‖ ^ 2) * ∑ q ∈ s, ‖b q‖ ^ 2 := by
  calc ‖∑ q ∈ s, a q * b q‖ ^ 2 ≤ (∑ q ∈ s, ‖a q‖ * ‖b q‖) ^ 2 := by
        gcongr
        exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun q _ => norm_mul _ _))
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq s _ _
end ReciprocityTheory.L2DbarEstimates.H
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates ComplexConjugate
open scoped ENNReal InnerProductSpace
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution : PerpEntryStatement := by
  intro p g w i hg
  have hs := hlin_vsq_pos hg
  have horth := hlin_orth g w hg
  have hsplit : conj (g i) * perp g w i = -∑ j ∈ Finset.univ.erase i, conj (g j) * perp g w j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at horth
    linear_combination horth
  have hcs := norm_sum_mul_sq_le_sum_sq_mul_sum_sq (Finset.univ.erase i) (fun j => conj (g j)) (perp g w)
  have h0 : ‖conj (g i) * perp g w i‖ ^ 2 ≤
      (∑ j ∈ Finset.univ.erase i, ‖conj (g j)‖ ^ 2) *
        ∑ j ∈ Finset.univ.erase i, ‖perp g w j‖ ^ 2 := by
    rw [hsplit, norm_neg]
    exact hcs
  simp only [norm_mul, Complex.norm_conj, mul_pow] at h0
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), Finset.sum_erase_eq_sub (Finset.mem_univ i)] at h0
  change ‖g i‖ ^ 2 * ‖perp g w i‖ ^ 2 ≤ (vsq g - ‖g i‖ ^ 2) * (vsq (perp g w) - ‖perp g w i‖ ^ 2) at h0
  rw [one_sub_div hs.ne', div_mul_eq_mul_div, le_div_iff₀ hs]
  nlinarith [h0]
end ReciprocityTheory.L2DbarEstimates.H
