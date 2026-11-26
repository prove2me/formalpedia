-- Prove2me | solution 1 for TunnellMap.residualDeferredAcceptance_rerun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:26:29.720893+00:00
-- url     : https://prove2.me/submissions/aa8b78dc-8a47-4f7f-83b4-4d8019bee946

import Definitions.Def_TunnellMap_OrderedGenerator
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_deferredAcceptanceMatching_order_independent


set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {n : ℤ} (hnpos : 0 < n)
  [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap
theorem _root_.solution
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (sourceOrder : List (bResidualInvolution n).Orbit)
    (hnodup : sourceOrder.Nodup)
    (hcomplete : ∀ s, s ∈ sourceOrder) :
    GloballyRanked.DAState.deferredAcceptanceMatching
        (residualOrbitRanking hnpos) hcard sourceOrder hnodup hcomplete =
      algorithmicResidualOrbitMatching hnpos hcard := by
  classical
  exact GloballyRanked.DAState.deferredAcceptanceMatching_order_independent
    (residualOrbitRanking hnpos) hcard sourceOrder residualSourceOrder
      hnodup residualSourceOrder_nodup hcomplete mem_residualSourceOrder
end TunnellMap
