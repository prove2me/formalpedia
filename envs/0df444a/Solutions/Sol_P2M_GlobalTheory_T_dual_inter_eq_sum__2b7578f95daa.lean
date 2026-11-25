-- Prove2me | solution 1 for P2M_GlobalTheory_T_dual_inter_eq_sum__2b7578f95daa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:33:53.710181+00:00
-- url     : https://prove2.me/submissions/f525eb3c-6a15-4bdc-8117-0b37e8aaf65d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DualInterEqSum
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DualInterEqSumStatement
import Theorems.Thm_GlobalTheory_InertZeta_dual_inter_eq_sum


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
theorem _root_.solution : Dual := by
  first | exact @GlobalTheory.InertZeta.dual_inter_eq_sum | exact GlobalTheory.InertZeta.dual_inter_eq_sum | (intros; apply GlobalTheory.InertZeta.dual_inter_eq_sum <;> assumption)
end _root_.GlobalTheory.T
