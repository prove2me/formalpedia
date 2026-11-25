-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.exists_chart_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:11:15.893651+00:00
-- url     : https://prove2.me/submissions/95f22888-0ed6-453a-bd33-5325a00e1ac5

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_ck
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_exists_chart_partition


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : M → ℂ) (hg : Ck n z 1 g) (hc : HasCompactSupport g) :
    ∃ (N : ℕ) (e : Fin N → OpenPartialHomeomorph M (V n)) (h : Fin N → M → ℂ),
      (∀ i, IsChart n z (e i)) ∧ (∀ i, Ck n z 1 (h i)) ∧ (∀ i, HasCompactSupport (h i)) ∧
      (∀ i, tsupport (h i) ⊆ (e i).source) ∧ g = fun x => ∑ i, h i x := by
  obtain ⟨N, e, χ, he, hχs, -, hχsub, -, -, hχ1⟩ :=
    exists_chart_partition n z hz (tsupport g) univ hc isOpen_univ (subset_univ _)
  refine ⟨N, e, fun i x => (χ i x : ℂ) * g x, he, fun i => Ck.mul n z 1 _ _ (Smooth.ck n z 1 _ (hχs i)) hg,
    fun i => hc.mul_left, fun i => ?_, ?_⟩
  · refine (tsupport_mul_subset_left (f := fun x => (χ i x : ℂ)) (g := g)).trans ?_
    refine (tsupport_comp_subset Complex.ofReal_zero (χ i)).trans ?_
    exact (hχsub i).trans inter_subset_left
  · funext x
    by_cases hx : x ∈ tsupport g
    · rw [← Finset.sum_mul, ← Complex.ofReal_sum, hχ1 x hx]; simp
    · have : g x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this]
end ReciprocityTheory.L2DbarEstimates
