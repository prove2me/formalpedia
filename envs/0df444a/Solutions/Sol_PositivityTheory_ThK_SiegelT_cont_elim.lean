-- Prove2me | solution 1 for PositivityTheory.ThK.SiegelT.cont_elim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:12.37943+00:00
-- url     : https://prove2.me/submissions/54ebde97-66ff-434b-87c8-3c74ba7d57cc

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
theorem _root_.solution : Continuous fun z : (κ → R) × (κ' → R) => (Sum.elim z.1 z.2 : κ ⊕ κ' → R) :=
  continuous_pi fun i => by
    rcases i with i | i
    · exact (continuous_apply i).comp continuous_fst
    · exact (continuous_apply i).comp continuous_snd
end PositivityTheory.ThK.SiegelT
