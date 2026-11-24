-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_image_mul_span_pair_bc3f8dbd8800
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:04:43.209052+00:00
-- url     : https://prove2.me/submissions/95b61bd3-488b-4ba4-a4a3-6e1be90be74f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassReducedParamsNonemptyPf

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
open UpperHalfPlane ModularGroup Complex NumberField
open scoped Real MatrixGroups nonZeroDivisors
namespace GroundTheory.Heights₂.Theta
theorem _root_.solution (u a b : ℂ) :
    (fun z => u * z) '' (Submodule.span ℤ ({a, b} : Set ℂ) : Set ℂ) =
      (Submodule.span ℤ ({u * a, u * b} : Set ℂ) : Set ℂ) := by
  have h := Submodule.map_span (LinearMap.mulLeft ℤ u) ({a, b} : Set ℂ)
  rw [Set.image_pair] at h
  simp only [LinearMap.mulLeft_apply] at h
  rw [← h, Submodule.map_coe]
  rfl
end GroundTheory.Heights₂.Theta
