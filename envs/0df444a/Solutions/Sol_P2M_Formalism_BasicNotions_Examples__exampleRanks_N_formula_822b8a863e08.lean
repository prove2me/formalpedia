-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__exampleRanks_N_formula_822b8a863e08
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:11:22.244565+00:00
-- url     : https://prove2.me/submissions/010893c2-0899-4078-a2e0-2db8ba4754c8

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
theorem _root_.solution (j : ℕ) : R0.N j = 8 + j * 16 := rfl
end Formalism.BasicNotions.Examples₂
