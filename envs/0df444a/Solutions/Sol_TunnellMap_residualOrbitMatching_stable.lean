-- Prove2me | solution 1 for TunnellMap.residualOrbitMatching_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:46:12.194405+00:00
-- url     : https://prove2.me/submissions/47d01708-b66a-4b0f-aecd-3f8534786799

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_ResidualBalance
import Definitions.Def_TunnellMap_OrbitRanking
import Theorems.Thm_TunnellMap_GloballyRanked_exists_unique_stable


set_option autoImplicit true
open TunnellMap
variable {n : ℤ} (hnpos : 0 < n)
  [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap
theorem _root_.solution
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    (residualOrbitRanking hnpos).Stable
      (residualOrbitMatching hnpos hcard) := by
  classical
  exact (Classical.choose_spec
    (GloballyRanked.exists_unique_stable (residualOrbitRanking hnpos) hcard)).1
end TunnellMap
