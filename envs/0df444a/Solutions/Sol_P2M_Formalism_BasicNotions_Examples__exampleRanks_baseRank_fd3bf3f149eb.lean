-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__exampleRanks_baseRank_fd3bf3f149eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:50:24.444564+00:00
-- url     : https://prove2.me/submissions/0f6aeac4-0969-4d61-8ad7-8e147c793184

import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExampleRanksRankComplement
import Theorems.Thm_Formalism_HC_frameCyclic_order


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution : R0.n0 = 4 := by
  show (Formalism.HC.frameCyc 2 1).n0 = 4
  rw [Formalism.HC.frameCyclic_order]
  exact ZMod.addOrderOf_one _
end Formalism.BasicNotions.Examples₂
