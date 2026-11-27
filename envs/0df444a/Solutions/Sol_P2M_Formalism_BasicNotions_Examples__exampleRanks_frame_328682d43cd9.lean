-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__exampleRanks_frame_328682d43cd9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:51:56.891335+00:00
-- url     : https://prove2.me/submissions/7161bf32-c2af-4d25-8cd9-1534bd1f18d5

import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExampleRanksRankComplement

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
theorem _root_.solution : R0.toFrame = Formalism.HC.cyclicFrame 2 := rfl
end Formalism.BasicNotions.Examples₂
