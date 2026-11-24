-- Prove2me | solution 1 for PositivityTheory.ThK.SiegelT.star_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:36:30.369991+00:00
-- url     : https://prove2.me/submissions/617e135a-a830-4310-9e6c-4664e07df169

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SiegelT
open Matrix GlobalTheory.WeilM Topology Filter
variable {R : Type} [TopologicalSpace R] [T2Space R] {κ κ' : Type}
namespace PositivityTheory.ThK.SiegelT
theorem _root_.solution {X : Type} [TopologicalSpace X] {φ : X → ℂ} (h : φ ∈ SB X) : star φ ∈ SB X :=
  ⟨h.1.comp star, h.2.comp_left (g := star) (star_zero ℂ)⟩
end PositivityTheory.ThK.SiegelT
