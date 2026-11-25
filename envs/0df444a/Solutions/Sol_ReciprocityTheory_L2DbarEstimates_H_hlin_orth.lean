-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.hlin_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:21:12.236269+00:00
-- url     : https://prove2.me/submissions/88e040b1-755c-44cb-bf1d-137fff1b3aea

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_HlinVsqPos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_hlin_vsqC
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_hlin_vsq_pos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.H
open MeasureTheory ReciprocityTheory.L2DbarEstimates ComplexConjugate
open scoped ENNReal InnerProductSpace
namespace ReciprocityTheory.L2DbarEstimates.H
theorem _root_.solution {p : ℕ} (g w : Fin p → ℂ) (hg : g ≠ 0) :
    ∑ j, conj (g j) * perp g w j = 0 := by
  have hs : ((vsq g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hlin_vsq_pos hg).ne'
  simp only [perp, mul_sub, Finset.sum_sub_distrib]
  have h2 : ∑ j, conj (g j) * (g j * ((∑ j, conj (g j) * w j) / ((vsq g : ℝ) : ℂ))) =
      ((vsq g : ℝ) : ℂ) * ((∑ j, conj (g j) * w j) / ((vsq g : ℝ) : ℂ)) := by
    generalize (∑ j, conj (g j) * w j) / ((vsq g : ℝ) : ℂ) = X
    rw [hlin_vsqC g, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h2, mul_div_assoc', mul_div_cancel_left₀ _ hs, sub_self]
end ReciprocityTheory.L2DbarEstimates.H
