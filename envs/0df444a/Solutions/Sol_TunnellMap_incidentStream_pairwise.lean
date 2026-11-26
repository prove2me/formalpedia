-- Prove2me | solution 1 for TunnellMap.incidentStream_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:57:40.570345+00:00
-- url     : https://prove2.me/submissions/e1887eca-245f-495e-948b-ed5afd097a3f

import Definitions.Def_TunnellMap_OrderedGenerator
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Theorems.Thm_TunnellMap_OrderedGenerator_incidentStream_key_strict


set_option autoImplicit true
open TunnellMap
open OrderedGenerator
variable {n : ℤ} [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap
theorem _root_.solution (hnpos : 0 < n) (s : BResidual n)
    (F : OrthogonalFrame (tau (residualSourceLift s))) :
    (incidentStream hnpos s F).Pairwise fun t₁ t₂ =>
      (residualOrbitRanking hnpos).rank
          ((bResidualInvolution n).orbit s) t₁ ≤
        (residualOrbitRanking hnpos).rank
          ((bResidualInvolution n).orbit s) t₂ := by
  rw [List.pairwise_iff_get]
  intro i j hij
  exact (incidentStream_key_strict hnpos s F hij).le
end TunnellMap
