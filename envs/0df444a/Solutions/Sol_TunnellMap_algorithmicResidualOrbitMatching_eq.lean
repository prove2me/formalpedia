-- Prove2me | solution 1 for TunnellMap.algorithmicResidualOrbitMatching_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:01:25.327799+00:00
-- url     : https://prove2.me/submissions/e4b66c9a-cc1b-4cf2-ab3f-e4405e7c3a14

import Definitions.Def_TunnellMap_OrderedGenerator
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Theorems.Thm_TunnellMap_algorithmicResidualOrbitMatching_stable
import Theorems.Thm_TunnellMap_residualOrbitMatching_unique


set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {n : ℤ} (hnpos : 0 < n)
  [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap
theorem _root_.solution
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    algorithmicResidualOrbitMatching hnpos hcard =
      residualOrbitMatching hnpos hcard := by
  classical
  exact residualOrbitMatching_unique hnpos hcard _
    (algorithmicResidualOrbitMatching_stable hnpos hcard)
end TunnellMap
