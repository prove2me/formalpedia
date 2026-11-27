-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TangentJacComp_proof_e66001b4f48a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:08:14.563218+00:00
-- url     : https://prove2.me/submissions/00be4c76-a6e5-4a51-b53e-1f0300891add

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacComp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentJacComp
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TangentJacComp_areaJacobian_eq_d7276c711add

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
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace TangentJacComp
theorem _root_.solution : TangentJacComp.Statement := by
  intro d n L π
  have hc := LinearMap.normDet_comp L (linProjₗ π)
  have hr : |LinearMap.det (((linProjₗ π).comp L).restrictScalars ℝ)| =
      ((linProjₗ π).comp L).normDet ^ 2 := by
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, LinearMap.normDet_eq_norm_det,
      Complex.sq_norm, abs_of_nonneg (Complex.normSq_nonneg _)]
  rw [hr, hc, tangentJac, TangentJacComp.areaJacobian_eq]
  rw [mul_pow]
  rfl
end TangentJacComp
end GroundTheory.Heights₂.Heights
