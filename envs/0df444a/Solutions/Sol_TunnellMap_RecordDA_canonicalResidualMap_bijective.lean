-- Prove2me | solution 1 for TunnellMap.RecordDA.canonicalResidualMap_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:30:11.05842+00:00
-- url     : https://prove2.me/submissions/ac5bc1d5-8ef6-4a01-8ed0-acb4bb104c5f

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_RecordSign
import Definitions.Def_TunnellMap_InverseByRerun
import Theorems.Thm_TunnellMap_RecordDA_inverseByRerun_canonicalResidualMap
import Theorems.Thm_TunnellMap_RecordDA_canonicalResidualMap_inverseByRerun

set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)]
variable [Fintype (ARep n)]
namespace TunnellMap.RecordDA
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallback : BResidual n) :
    Function.Bijective
      (canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard)) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨inverseByRerun frames fallback,
      inverseByRerun_canonicalResidualMap hn hnpos frames hcard fallback,
      canonicalResidualMap_inverseByRerun hn hnpos frames hcard fallback⟩
end TunnellMap.RecordDA
