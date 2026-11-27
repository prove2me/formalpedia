-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.H.perpNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:30:20.04291+00:00
-- url     : https://prove2.me/submissions/4084afa4-1224-4419-a2fe-9be0afcc71fc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_HlinVsqPos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_H_hlin_sqC
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
theorem _root_.solution : PerpNormStatement := by
  intro p g w hg
  have hs : ((vsq g : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hlin_vsq_pos hg).ne'
  obtain ⟨c, hc⟩ : ∃ c, c = ∑ j, (starRingEnd ℂ) (g j) * w j := ⟨_, rfl⟩
  have hc' : ∑ i, g i * conj (w i) = conj c := by
    rw [hc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, Complex.conj_conj, mul_comm]
  have key : ((vsq (perp g w) : ℝ) : ℂ) =
      ((vsq w : ℝ) : ℂ) - ((‖c‖ ^ 2 : ℝ) : ℂ) / ((vsq g : ℝ) : ℂ) := by
    rw [hlin_vsqC (perp g w), hlin_vsqC w, hlin_sqC]
    simp only [perp, ← hc]
    have e : ∀ i, (w i - g i * (c / ((vsq g : ℝ) : ℂ))) *
        conj (w i - g i * (c / ((vsq g : ℝ) : ℂ))) =
        w i * conj (w i) - conj c / ((vsq g : ℝ) : ℂ) * (conj (g i) * w i)
          - c / ((vsq g : ℝ) : ℂ) * (g i * conj (w i))
          + c * conj c / ((vsq g : ℝ) : ℂ) ^ 2 * (g i * conj (g i)) := by
      intro i
      simp only [map_sub, map_mul, map_div₀, Complex.conj_ofReal]
      ring
    rw [Finset.sum_congr rfl (fun i _ => e i)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [← hc, hc', ← hlin_vsqC g]
    field_simp <;> ring
  rw [hc] at key
  exact_mod_cast key
end ReciprocityTheory.L2DbarEstimates.H
