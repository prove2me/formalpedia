-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ClassPeriodInv_isLatticeParam_conj_d29d060aaf70
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:51:30.63704+00:00
-- url     : https://prove2.me/submissions/f00b6e74-f5c2-4799-8073-57733624e645

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaLogPeriodNegConjPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassPeriodInvConj
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_conj_latticeOf_d783b3b81477

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
    IsLatticeParam ((fun z => w * z) '' (starRingEnd ℂ '' Λ)) (negConj τ) := by
  obtain ⟨c, hc, hΛ⟩ := h
  refine ⟨starRingEnd ℂ c / w, div_ne_zero ((map_ne_zero _).mpr hc) hw, ?_⟩
  have hneg : ((negConj τ : ℍ) : ℂ) = -(starRingEnd ℂ (τ : ℂ)) := rfl
  rw [hneg, ← conj_latticeOf, ← hΛ]
  simp only [Set.image_image]
  refine Set.image_congr fun x _ => ?_
  rw [map_mul]
  field_simp
end GroundTheory.Heights₂.Theta.ClassPeriodInv
