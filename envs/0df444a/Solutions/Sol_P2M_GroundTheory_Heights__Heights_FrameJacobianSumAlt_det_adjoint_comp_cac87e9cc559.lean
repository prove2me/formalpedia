-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_det_adjoint_comp_cac87e9cc559
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:26.638882+00:00
-- url     : https://prove2.me/submissions/72231aaa-6f69-4fc2-a8c0-f204d2ddc39f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFrameJacobianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFrameJacobianSum

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
open Matrix Finset Module
noncomputable section
open GroundTheory.Heights₂.Heights.FrameJacobianSumAlt
variable {d : ℕ} {ι : Type*} [Fintype ι]
namespace GroundTheory.Heights₂.Heights.FrameJacobianSumAlt
theorem _root_.solution (S : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ ι) :
    LinearMap.det (LinearMap.adjoint S ∘ₗ S) =
      (Matrix.of fun i j : Fin d => inner ℂ (S (EuclideanSpace.basisFun (Fin d) ℂ i))
        (S (EuclideanSpace.basisFun (Fin d) ℂ j))).det := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin d) ℂ).toBasis]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, LinearMap.comp_apply,
    LinearMap.adjoint_inner_right, Matrix.of_apply]
end GroundTheory.Heights₂.Heights.FrameJacobianSumAlt
