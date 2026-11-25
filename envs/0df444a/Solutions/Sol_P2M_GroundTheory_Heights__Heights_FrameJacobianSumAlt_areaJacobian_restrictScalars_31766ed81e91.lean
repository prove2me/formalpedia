-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_areaJacobian_restrictScalars_31766ed81e91
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:12:31.732185+00:00
-- url     : https://prove2.me/submissions/113da04b-27a0-4e53-85dd-367f54bcfecd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFrameJacobianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFrameJacobianSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_adjoint_restrictScalars_dee6cd1ed16a

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
    areaJacobian (S.restrictScalars ℝ) = ‖LinearMap.det (LinearMap.adjoint S ∘ₗ S)‖ := by
  rw [areaJacobian, adjoint_restrictScalars, ← LinearMap.restrictScalars_comp,
    LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.norm_def]
end GroundTheory.Heights₂.Heights.FrameJacobianSumAlt
