-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__exampleRanks_o_141199d5c6d3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:08:59.469799+00:00
-- url     : https://prove2.me/submissions/2999c774-d3b1-4d90-a207-42427bc2e982

import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameCyclicGenerator
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExampleRanksRankComplement
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_order_e93fa31b6760
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__exampleRanks_baseRank_fd3bf3f149eb
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


attribute [local simp] Formalism.BasicNotions.Examples₂.exampleRanks_order

set_option autoImplicit false
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂
namespace Formalism.BasicNotions.Examples₂
theorem _root_.solution : R0.o = 1 := by
  show R0.toFrame.ord / R0.toFrame.n0 = 1
  have h1 : R0.toFrame.n0 = 4 := exampleRanks_baseRank
  have h2 : R0.toFrame.ord = 4 := exampleRanks_order
  rw [h1, h2]
end Formalism.BasicNotions.Examples₂
