-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TangentJacComp_areaJacobian_eq_d7276c711add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:32:14.211176+00:00
-- url     : https://prove2.me/submissions/1f8a9e09-7b7b-4669-806c-5169217df8c7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacComp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentJacComp
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TangentJacComp_adjoint_restrictScalars_6c2dd86bcf0a

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
theorem _root_.solution {d n : ℕ}
    (L : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :
    areaJacobian (L.restrictScalars ℝ) = L.normDet ^ 2 := by
  have hsq : ((L.normDet ^ 2 : ℝ) : ℂ) = LinearMap.det (LinearMap.adjoint L ∘ₗ L) := L.normDet_sq
  rw [areaJacobian, TangentJacComp.adjoint_restrictScalars]
  have hc : (LinearMap.adjoint L).restrictScalars ℝ ∘ₗ L.restrictScalars ℝ =
      (LinearMap.adjoint L ∘ₗ L).restrictScalars ℝ := rfl
  rw [hc, LinearMap.det_restrictScalars, ← hsq, Algebra.norm_complex_apply, Complex.normSq_ofReal,
    Real.sqrt_mul_self (by positivity)]
end TangentJacComp
end GroundTheory.Heights₂.Heights
