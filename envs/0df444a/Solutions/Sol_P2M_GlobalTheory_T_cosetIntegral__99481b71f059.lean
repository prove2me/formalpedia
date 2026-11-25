-- Prove2me | solution 1 for P2M_GlobalTheory_T_cosetIntegral__99481b71f059
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:38:11.376666+00:00
-- url     : https://prove2.me/submissions/373c482d-2be4-47ab-aa90-770f7aa57fbd

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetIntegralStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_cosetIntegral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : CosetIntegral := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.cosetIntegral | exact GlobalTheory.CompanionTheory.InertZeta.cosetIntegral | (intros; apply GlobalTheory.CompanionTheory.InertZeta.cosetIntegral <;> assumption)
end _root_.GlobalTheory.T
