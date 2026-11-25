-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_adjoint_restrictScalars_dee6cd1ed16a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:28:30.478041+00:00
-- url     : https://prove2.me/submissions/1bf5832c-2cc2-49aa-b1a8-41b1727dd1d4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFrameJacobianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFrameJacobianSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FrameJacobianSumAlt_real_inner_eq_re_69fd56d86293

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
    LinearMap.adjoint (S.restrictScalars ℝ) = (LinearMap.adjoint S).restrictScalars ℝ := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, real_inner_eq_re,
    real_inner_eq_re, LinearMap.adjoint_inner_left]
end GroundTheory.Heights₂.Heights.FrameJacobianSumAlt
