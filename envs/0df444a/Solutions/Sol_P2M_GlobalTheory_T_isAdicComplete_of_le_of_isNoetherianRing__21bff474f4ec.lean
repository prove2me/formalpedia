-- Prove2me | solution 1 for P2M_GlobalTheory_T_isAdicComplete_of_le_of_isNoetherianRing__21bff474f4ec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:52:35.056321+00:00
-- url     : https://prove2.me/submissions/575f57d0-d672-4f86-b67a-07861fc1bc17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAdicCompleteOfLeOfIsNoetherianRing
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAdicCompleteOfLeOfIsNoetherianRingStatement
import Theorems.Thm_GlobalTheory_isAdicComplete_of_le_of_isNoetherianRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I J : Ideal R), I ≤ J → IsAdicComplete J R → IsAdicComplete I R := by
  first | exact @GlobalTheory.isAdicComplete_of_le_of_isNoetherianRing | exact GlobalTheory.isAdicComplete_of_le_of_isNoetherianRing | (intros; apply GlobalTheory.isAdicComplete_of_le_of_isNoetherianRing <;> assumption)
end _root_.GlobalTheory.T
