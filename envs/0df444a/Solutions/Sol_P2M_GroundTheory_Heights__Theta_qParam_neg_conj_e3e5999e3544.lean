-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_qParam_neg_conj_e3e5999e3544
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:44:39.744909+00:00
-- url     : https://prove2.me/submissions/3ef0533f-bf71-4013-9e54-898a58cbe569

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaLogPeriodNegConjPf

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
theorem _root_.solution (h : ℝ) (z : ℂ) :
    Function.Periodic.qParam h (-(starRingEnd ℂ) z) =
      starRingEnd ℂ (Function.Periodic.qParam h z) := by
  unfold Function.Periodic.qParam
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring
end GroundTheory.Heights₂.Theta
