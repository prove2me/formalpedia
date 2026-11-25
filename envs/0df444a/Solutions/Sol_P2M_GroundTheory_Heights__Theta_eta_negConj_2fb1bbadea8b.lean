-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_eta_negConj_2fb1bbadea8b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:54:19.980668+00:00
-- url     : https://prove2.me/submissions/abd04033-ac38-4058-b523-0d09104b69d8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaLogPeriodNegConjPf
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_qParam_neg_conj_e3e5999e3544

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
theorem _root_.solution (τ : ℍ) : η (negConj τ : ℂ) = starRingEnd ℂ (η (τ : ℂ)) := by
  have hc : ((negConj τ : ℍ) : ℂ) = -(starRingEnd ℂ) (τ : ℂ) := rfl
  have hq1 : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have hm := (multipliable_one_sub_pow hq1).hasProd.map (starRingEnd ℂ) Complex.continuous_conj
  have hprod : ∏' n : ℕ, (1 - eta_q n ((negConj τ : ℍ) : ℂ)) =
      starRingEnd ℂ (∏' n : ℕ, (1 - eta_q n (τ : ℂ))) := by
    rw [← hm.tprod_eq]
    congr 1
    funext n
    simp [hc, eta_q, qParam_neg_conj]
  unfold ModularForm.eta
  rw [hprod, hc, qParam_neg_conj, map_mul]
end GroundTheory.Heights₂.Theta
