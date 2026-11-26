-- Prove2me | solution 1 for TunnellMap.algorithmicResidualOrbitMatching_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:58:07.319388+00:00
-- url     : https://prove2.me/submissions/4ae74d50-2cf7-4688-8b34-c8dd03c0b339

import Definitions.Def_TunnellMap_OrderedGenerator
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_deferredAcceptanceMatching_stable


set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {n : ℤ} (hnpos : 0 < n)
  [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap
theorem _root_.solution
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    (residualOrbitRanking hnpos).Stable
      (algorithmicResidualOrbitMatching hnpos hcard) := by
  classical
  exact GloballyRanked.DAState.deferredAcceptanceMatching_stable
    (residualOrbitRanking hnpos) hcard residualSourceOrder
      residualSourceOrder_nodup mem_residualSourceOrder
end TunnellMap
