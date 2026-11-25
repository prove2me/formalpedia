-- Prove2me | solution 1 for P2M_GlobalTheory_T_isRegularLocalRing_adicCompletion__0bd02646f3a5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:34:04.512679+00:00
-- url     : https://prove2.me/submissions/84ec56f3-a4f7-4b7a-add6-4095191a3414

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsRegularLocalRingAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsRegularLocalRingAdicCompletionStatement
import Theorems.Thm_GlobalTheory_RegularCompletion_isRegularLocalRing_adicCompletion


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (T : Type) [CommRing T] [IsRegularLocalRing T], IsRegularLocalRing (AdicCompletion (maximalIdeal T) T) := by
  first | exact @GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion | exact GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion | (intros; apply GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion <;> assumption)
end _root_.GlobalTheory.T
