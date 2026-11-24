-- Prove2me | solution 1 for PositivityTheory.ThK.SiegelT.cont_inr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:55.396394+00:00
-- url     : https://prove2.me/submissions/98c3169d-c40f-473b-9e2d-afe3d794089f

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
omit [T2Space R]
namespace PositivityTheory.ThK.SiegelT
theorem _root_.solution : Continuous fun z : κ ⊕ κ' → R => z ∘ Sum.inr := continuous_pi fun _ => continuous_apply _
end PositivityTheory.ThK.SiegelT
