-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsHeight_exists_eq_ofPointMatrix_f9a576162836
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:52.288776+00:00
-- url     : https://prove2.me/submissions/18044cef-d6fb-459c-85e2-4e8e34dc5128

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm

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
open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ObjectsHeight
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsHeight
theorem _root_.solution (h : HermNorm n) :
    ∃ (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S), h = ofPointMatrix S hS := by
  have hA : IsUnit h.mat := (Matrix.isUnit_iff_isUnit_det _).mpr h.isUnit_det
  refine ⟨(h.matᵀ)⁻¹, (Matrix.isUnit_nonsing_inv_iff).mpr ((isUnit_transpose _).mpr hA), ?_⟩
  cases h with
  | mk A hAdet =>
    simp only [ofPointMatrix, HermNorm.mk.injEq]
    rw [nonsing_inv_nonsing_inv _ (by rw [det_transpose]; exact hAdet), transpose_transpose]
end GroundTheory.Heights₂.Heights.ObjectsHeight
