-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsHeight_ofPointMatrix_dualNorm_fa5369e88d9b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:44.680884+00:00
-- url     : https://prove2.me/submissions/10c5c03e-c38d-4747-82f3-3c2ee1e9bb91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ObjectsHeight_euclid_norm_eq_471a80e339c7

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
theorem _root_.solution (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (y : Fin n → ℂ) :
    (ofPointMatrix S hS).dualNorm y = (IndefiniteRowSideFullHecke.ArithBezout.pointMetric S hS).ρ y := by
  have h : ((ofPointMatrix S hS).matᵀ)⁻¹ = S := by
    simp only [ofPointMatrix, transpose_transpose]
    exact nonsing_inv_nonsing_inv S (isUnit_det_of_isUnit hS)
  simp only [HermNorm.dualNorm, h, IndefiniteRowSideFullHecke.ArithBezout.pointMetric, euclid_norm_eq]
end GroundTheory.Heights₂.Heights.ObjectsHeight
