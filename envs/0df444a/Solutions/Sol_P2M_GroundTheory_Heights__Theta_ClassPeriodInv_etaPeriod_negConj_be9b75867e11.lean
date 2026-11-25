-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ClassPeriodInv_etaPeriod_negConj_be9b75867e11
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:32:25.414936+00:00
-- url     : https://prove2.me/submissions/92124266-2039-43c0-9ff4-b793766fd5bc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaLogPeriodNegConjPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassPeriodInvConj
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_EtaLogPeriodNegConj_proof_d791d33798ab
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_etaPeriod_pos_b13a4c259a1a


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
theorem _root_.solution (τ : ℍ) : etaPeriod (negConj τ) = etaPeriod τ :=
  Real.log_injOn_pos (etaPeriod_pos _) (etaPeriod_pos _) (EtaLogPeriodNegConj.proof τ)
end GroundTheory.Heights₂.Theta.ClassPeriodInv
