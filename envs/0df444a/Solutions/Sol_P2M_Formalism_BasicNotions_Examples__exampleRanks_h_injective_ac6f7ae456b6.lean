-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__exampleRanks_h_injective_ac6f7ae456b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:16:58.87309+00:00
-- url     : https://prove2.me/submissions/6653aa35-b442-4838-93a7-d72387258683

import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExampleRanksRankComplement
import Theorems.Thm_Formalism_HC_frameCyc_h_injective


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
theorem _root_.solution : Function.Injective R0.h :=
  Formalism.HC.frameCyc_h_injective 2 1
end Formalism.BasicNotions.Examples₂
