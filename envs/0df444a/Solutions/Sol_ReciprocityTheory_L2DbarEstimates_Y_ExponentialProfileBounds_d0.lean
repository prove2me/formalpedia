-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds.d0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:30:40.647028+00:00
-- url     : https://prove2.me/submissions/2b8a8f19-cdbf-4c45-aca3-680d3dadc606

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_EuclideanAtlasPointwiseNormSqUnitSection
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ExponentialProfileBounds_differentiable_coord
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ExponentialProfileBounds_differentiable_wv
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ExponentialProfileBounds_isSecOn_of
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ExponentialProfileBounds_sqn_w
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ExponentialProfileBounds_euclideanAtlas_sumNormSq_coordSections
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ExponentialProfileBounds_euclideanAtlas_pointwiseNormSq_unitSection
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ExponentialProfileBounds_det_ne
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ExponentialProfileBounds_zeroSet_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Matrix
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds
theorem _root_.solution : (atlas n).D0 1 (wI n) (w0I n) (sI n) where
  sec_w k := isSecOn_of _ _ _ (differentiable_wv k)
  isSection_denom := isSecOn_of _ _ _ (differentiable_const 1)
  sec_s k := isSecOn_of _ _ _ (differentiable_coord k)
  no_common_zero _ := ⟨0, by simp [wI, wv]⟩
  finite_S := by rw [zeroSet_eq]; exact Set.finite_singleton 0
  w0_ne _ _ := one_ne_zero
  coord P _ := det_ne P
  meets y := ⟨0, by rw [zeroSet_eq]; rfl,
    isPreconnected_univ.subset_connectedComponent (Set.mem_univ y) (Set.mem_univ 0)⟩
  family_le_coords U hU hS := by
    have h0 : (0 : V n) ∈ U := hS (by rw [zeroSet_eq]; rfl)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 h0
    refine ⟨1 + (ε ^ 2)⁻¹, fun y hy => ?_⟩
    have hεy : ε ≤ ‖y‖ := by
      by_contra h
      exact hy (hball (by rw [Metric.mem_ball, dist_zero_right]; exact lt_of_not_ge h))
    rw [sqn_w, euclideanAtlas_sumNormSq_coordSections]
    set t := ‖y‖ ^ 2
    have ht : ε ^ 2 ≤ t := pow_le_pow_left₀ hε.le hεy 2
    have hε2 : 0 < ε ^ 2 := by positivity
    have ht0 : 0 < 1 + t := by positivity
    have key : 1 + t ≤ (1 + (ε ^ 2)⁻¹) * t := by
      have : 1 ≤ (ε ^ 2)⁻¹ * t := (le_inv_mul_iff₀ hε2).2 (by rw [mul_one]; exact ht)
      nlinarith
    calc (1 : ℝ) = (1 + t) * (1 + t)⁻¹ := (mul_inv_cancel₀ ht0.ne').symm
      _ ≤ ((1 + (ε ^ 2)⁻¹) * t) * (1 + t)⁻¹ :=
        mul_le_mul_of_nonneg_right key (inv_nonneg.2 ht0.le)
      _ = _ := by ring
  s_le_w := ⟨1, fun y => by
    rw [sqn_w, euclideanAtlas_sumNormSq_coordSections, mul_one, ← div_eq_mul_inv]
    exact (div_le_one (pos_one_add y)).2 (by linarith)⟩
  denom_le_family := ⟨1, fun y => by
    rw [euclideanAtlas_pointwiseNormSq_unitSection, sqn_w, mul_one]
    exact inv_le_one_of_one_le₀ (by linarith [sq_nonneg ‖y‖])⟩
end ReciprocityTheory.L2DbarEstimates.Y.ExponentialProfileBounds
