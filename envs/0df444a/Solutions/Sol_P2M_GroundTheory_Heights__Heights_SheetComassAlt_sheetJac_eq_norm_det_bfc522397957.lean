-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SheetComassAlt_sheetJac_eq_norm_det_bfc522397957
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:29:36.606802+00:00
-- url     : https://prove2.me/submissions/7063e63e-5656-4091-9b2d-68bbe871034b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSheetComass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFrameJacobianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetComass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_areaJacobian_restrictScalars_31766ed81e91
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_det_adjoint_comp_cac87e9cc559


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
open MvPolynomial Matrix ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.SheetComassAlt
namespace GroundTheory.Heights₂.Heights.SheetComassAlt
theorem _root_.solution {n d : ℕ} (s : (Fin d → ℂ) → Fin n → ℂ) (y : Fin d → ℂ)
    (hs : DifferentiableAt ℂ s y) :
    sheetJac s y = ‖((ReciprocityTheory.AnForm.A.jacC s y)ᴴ * ReciprocityTheory.AnForm.A.jacC s y).det‖ := by
  set S : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm.toLinearMap ∘ₗ
      ((fderiv ℂ s y : (Fin d → ℂ) →L[ℂ] (Fin n → ℂ)) : (Fin d → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ
        (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).toLinearMap with hS
  have hR : fderiv ℝ s y = (fderiv ℂ s y).restrictScalars ℝ := hs.fderiv_restrictScalars ℝ
  have e : (WithLp.linearEquiv 2 ℝ (Fin n → ℂ)).symm.toLinearMap ∘ₗ
      ((fderiv ℝ s y : (Fin d → ℂ) →L[ℝ] (Fin n → ℂ)) : (Fin d → ℂ) →ₗ[ℝ] (Fin n → ℂ)) ∘ₗ
        (WithLp.linearEquiv 2 ℝ (Fin d → ℂ)).toLinearMap = S.restrictScalars ℝ := by
    ext v : 1
    simp [hS, hR]
  rw [sheetJac, e, FrameJacobianSumAlt.areaJacobian_restrictScalars,
    FrameJacobianSumAlt.det_adjoint_comp]
  congr 2
  ext i j
  simp [hS, Matrix.mul_apply, ReciprocityTheory.AnForm.A.jacC, PiLp.inner_apply, mul_comm]
end GroundTheory.Heights₂.Heights.SheetComassAlt
