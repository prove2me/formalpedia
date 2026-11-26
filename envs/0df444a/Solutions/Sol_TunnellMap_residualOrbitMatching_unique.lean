-- Prove2me | solution 1 for TunnellMap.residualOrbitMatching_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:43:57.483913+00:00
-- url     : https://prove2.me/submissions/feb199df-609e-44d1-a66c-c5e8ed6090f3

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
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (M : (bResidualInvolution n).Orbit ≃
      (aResidualInvolution n hnpos).Orbit)
    (hM : (residualOrbitRanking hnpos).Stable M) :
    M = residualOrbitMatching hnpos hcard := by
  classical
  exact (Classical.choose_spec
    (GloballyRanked.exists_unique_stable (residualOrbitRanking hnpos) hcard)).2 M hM
end TunnellMap
