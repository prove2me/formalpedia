-- Prove2me | solution 1 for P2M_GlobalTheory_T_isReduced_of_smooth_over_field__f558e13e1603
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:52:46.718945+00:00
-- url     : https://prove2.me/submissions/e26a3195-ffb4-4c28-85eb-ee76e9698aac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsReducedOfSmoothOverField
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsReducedOfSmoothOverFieldStatement
import Theorems.Thm_GlobalTheory_isReduced_of_smooth_over_field


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
theorem _root_.solution : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Algebra.Smooth K A], IsReduced A := by
  first | exact @GlobalTheory.isReduced_of_smooth_over_field | exact GlobalTheory.isReduced_of_smooth_over_field | (intros; apply GlobalTheory.isReduced_of_smooth_over_field <;> assumption)
end _root_.GlobalTheory.T
