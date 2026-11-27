-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertModule_proof_c4bb6dc798ea
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:56:57.95697+00:00
-- url     : https://prove2.me/submissions/03143215-bb88-4cc2-81a1-b56fd98f154e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
universe u v
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace HilbertModule
theorem _root_.solution (hMP : ModulesFromPrimes.Statement.{u, v})
    (hHP : HilbertPrime.Statement.{u}) : HilbertModule.Statement.{u, v} :=
  fun d => hMP d fun e _ => hHP e
end HilbertModule
end GroundTheory.Heights₂.Heights.HilbertSamuel
