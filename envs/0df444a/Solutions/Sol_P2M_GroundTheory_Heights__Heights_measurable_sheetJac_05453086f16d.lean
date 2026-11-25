-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_measurable_sheetJac_05453086f16d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:38:44.336502+00:00
-- url     : https://prove2.me/submissions/f53583ef-a612-42c5-a9d9-4d14fb75122c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetImageArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetImageAreaSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjectionFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetImageArea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_continuous_areaJacobian_b8921d31322f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Matrix
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n d : ℕ} (s : (Fin d → ℂ) → Fin n → ℂ) : Measurable (sheetJac s) := by
  let C₁ : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (WithLp.linearEquiv 2 ℝ (Fin n → ℂ)).symm.toLinearMap
  let C₂ : EuclideanSpace ℂ (Fin d) →L[ℝ] (Fin d → ℂ) :=
    LinearMap.toContinuousLinearMap (WithLp.linearEquiv 2 ℝ (Fin d → ℂ)).toLinearMap
  have hΦ : Continuous fun M : (Fin d → ℂ) →L[ℝ] (Fin n → ℂ) => C₁.comp (M.comp C₂) :=
    continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
  have h : sheetJac s = (fun M : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin n) =>
      areaJacobian (M : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))) ∘
      (fun M : (Fin d → ℂ) →L[ℝ] (Fin n → ℂ) => C₁.comp (M.comp C₂)) ∘ fderiv ℝ s := by
    funext y
    rfl
  rw [h]
  exact (continuous_areaJacobian.comp hΦ).measurable.comp (measurable_fderiv ℝ s)
end GroundTheory.Heights₂.Heights
