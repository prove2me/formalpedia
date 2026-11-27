-- Prove2me | solution 1 for P2M_GlobalTheory_Flasque_isFlasque_injectiveShortComplex_X__4b84a5ce729c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:52:06.941136+00:00
-- url     : https://prove2.me/submissions/08190416-264f-44d2-a5fc-bb4807b267d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Theorems.Thm_GlobalTheory_Flasque_injectiveShortComplex_shortExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w v u
open GlobalTheory
open GlobalTheory.Flasque
variable {X : TopCat.{u}}
namespace GlobalTheory.Flasque
theorem _root_.solution (F : TopCat.Sheaf AddCommGrpCat.{u} X) [F.IsFlasque] :
    (injectiveShortComplex F).X₃.IsFlasque :=
  TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ (injectiveShortComplex_shortExact F)
end GlobalTheory.Flasque
