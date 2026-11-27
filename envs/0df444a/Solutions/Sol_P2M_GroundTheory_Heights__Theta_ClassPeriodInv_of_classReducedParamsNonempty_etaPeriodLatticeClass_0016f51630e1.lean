-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ClassPeriodInv_of_classReducedParamsNonempty_etaPeriodLatticeClass_0016f51630e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:11:05.374094+00:00
-- url     : https://prove2.me/submissions/c184d0fa-e86e-4d57-8271-7bc065837f60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaLogPeriodNegConjPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassPeriodInvConj
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_negConj_mem_classReducedParams_01e2a9b546ba
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_isLatticeParam_of_mem_classReducedParams_e8b7265c478f
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_ClassPeriodInv_etaPeriod_negConj_be9b75867e11

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
theorem _root_.solution
    (hne : ClassReducedParamsNonempty.Statement) (hlc : EtaPeriodLatticeClass.Statement) :
    ClassPeriodInv.Statement := by
  intro K _ _ hK σ hσ A
  have hA : classTau σ A ∈ classReducedParams σ A := Classical.epsilon_spec (hne K hK σ hσ A)
  have hB : classTau σ A⁻¹ ∈ classReducedParams σ A⁻¹ :=
    Classical.epsilon_spec (hne K hK σ hσ A⁻¹)
  obtain ⟨I, hIA, -⟩ := hA
  have hI' : ClassGroup.mk K I⁻¹ = A⁻¹ := by rw [map_inv, hIA]
  have h1 := isLatticeParam_of_mem_classReducedParams σ hB hI'
  have h2 := isLatticeParam_of_mem_classReducedParams σ
    (negConj_mem_classReducedParams hK σ hσ A (Classical.epsilon_spec (hne K hK σ hσ A))) hI'
  unfold classPeriod
  rw [hlc _ _ _ h1 h2, etaPeriod_negConj]
  rfl
end GroundTheory.Heights₂.Theta.ClassPeriodInv
