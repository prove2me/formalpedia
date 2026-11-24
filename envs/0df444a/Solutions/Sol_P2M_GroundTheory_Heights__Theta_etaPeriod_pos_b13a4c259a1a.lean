-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_etaPeriod_pos_b13a4c259a1a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:58.495901+00:00
-- url     : https://prove2.me/submissions/b15ef3bf-0ec1-4f5e-8f15-fc8d372e6b17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open UpperHalfPlane ModularGroup ModularForm Complex NumberField
open scoped Real Modular MatrixGroups nonZeroDivisors
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (τ : ℍ) : 0 < etaPeriod τ := by
  have h : η (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero τ.im_pos
  unfold etaPeriod
  have : 0 < ‖η (τ : ℂ)‖ := norm_pos_iff.mpr h
  have := τ.im_pos
  positivity
end GroundTheory.Heights₂.Theta
