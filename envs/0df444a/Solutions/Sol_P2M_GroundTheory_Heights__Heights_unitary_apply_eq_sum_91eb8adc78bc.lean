-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_unitary_apply_eq_sum_91eb8adc78bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:40:55.106413+00:00
-- url     : https://prove2.me/submissions/708136b9-2df6-4584-ab58-1e38da16138f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentGaussInvariant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentGaussInvariant

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
open MeasureTheory Module
open scoped Matrix
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (v : EuclideanSpace ℂ (Fin n)) (k : Fin n) : U v k = ∑ j, unitMat U k j * v j := by
  have h := LinearMap.toMatrix_mulVec_repr (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis U.toLinearMap v
  have h2 := congrFun h k
  simpa [unitMat, Matrix.mulVec, dotProduct] using h2.symm
end GroundTheory.Heights₂.Heights
