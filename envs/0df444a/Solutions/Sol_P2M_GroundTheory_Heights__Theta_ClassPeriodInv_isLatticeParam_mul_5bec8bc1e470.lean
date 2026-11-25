-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ClassPeriodInv_isLatticeParam_mul_5bec8bc1e470
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:42:54.249113+00:00
-- url     : https://prove2.me/submissions/0b3d043d-257f-40c4-a688-cd8202239895

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaLogPeriodNegConjPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassPeriodInvConj

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
open UpperHalfPlane ModularGroup ModularForm Complex NumberField Module
open scoped Real Modular MatrixGroups nonZeroDivisors
open GroundTheory.Heights₂.Theta.ClassPeriodInv
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Theta.ClassPeriodInv
theorem _root_.solution {Λ : Set ℂ} {τ : ℍ} (h : IsLatticeParam Λ τ) {w : ℂ} (hw : w ≠ 0) :
    IsLatticeParam ((fun z => w * z) '' Λ) τ := by
  obtain ⟨c, hc, hΛ⟩ := h
  refine ⟨c / w, div_ne_zero hc hw, ?_⟩
  rw [← hΛ, Set.image_image]
  refine Set.image_congr fun x _ => ?_
  field_simp
end GroundTheory.Heights₂.Theta.ClassPeriodInv
