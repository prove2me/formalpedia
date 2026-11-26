-- Prove2me | solution 1 for TunnellMap.algorithmicResidualEquiv_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:26:34.90308+00:00
-- url     : https://prove2.me/submissions/716023e4-45c3-4d51-8617-080cef95bc6a

import Definitions.Def_TunnellMap_OrderedGenerator
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Theorems.Thm_TunnellMap_algorithmicResidualOrbitMatching_eq

set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {n : ℤ} (hnpos : 0 < n)
  [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap
theorem _root_.solution
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    algorithmicResidualEquiv hnpos hcard =
      residualEquivOfOrbitCard hnpos hcard := by
  classical
  unfold algorithmicResidualEquiv residualEquivOfOrbitCard
  rw [algorithmicResidualOrbitMatching_eq hnpos hcard]
end TunnellMap
