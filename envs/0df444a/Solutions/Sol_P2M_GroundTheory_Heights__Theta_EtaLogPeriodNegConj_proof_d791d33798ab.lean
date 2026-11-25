-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_EtaLogPeriodNegConj_proof_d791d33798ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:00:17.961074+00:00
-- url     : https://prove2.me/submissions/0a0cae7b-42d0-49ac-aee6-93e23e329acb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaLogPeriodNegConjPf
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_eta_negConj_2fb1bbadea8b

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
open UpperHalfPlane ModularForm Complex
open scoped Real
namespace GroundTheory.Heights₂.Theta
namespace EtaLogPeriodNegConj
theorem _root_.solution : EtaLogPeriodNegConj.Statement := by
  intro τ
  have him : (negConj τ).im = τ.im := by
    show (-(starRingEnd ℂ) (τ : ℂ)).im = (τ : ℂ).im
    simp
  unfold etaLogPeriod etaPeriod
  rw [him, eta_negConj, Complex.norm_conj]
end EtaLogPeriodNegConj
end GroundTheory.Heights₂.Theta
