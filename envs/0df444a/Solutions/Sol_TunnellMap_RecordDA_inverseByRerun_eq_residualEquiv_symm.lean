-- Prove2me | solution 1 for TunnellMap.RecordDA.inverseByRerun_eq_residualEquiv_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:47:34.266658+00:00
-- url     : https://prove2.me/submissions/021c9968-3c97-436d-9834-27a44699bb91

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_RecordSign
import Definitions.Def_TunnellMap_InverseByRerun
import Theorems.Thm_TunnellMap_RecordDA_canonicalResidualMap_inverseByRerun
import Theorems.Thm_TunnellMap_canonicalResidualMapOf_eq_residualEquivOfOrbitCard


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
    (fallback : BResidual n) (y : AResidual n) :
    inverseByRerun frames fallback y =
      (residualEquivOfOrbitCard hnpos hcard).symm y := by
  apply (residualEquivOfOrbitCard hnpos hcard).injective
  rw [Equiv.apply_symm_apply,
    ← canonicalResidualMapOf_eq_residualEquivOfOrbitCard hnpos hcard]
  exact canonicalResidualMap_inverseByRerun hn hnpos frames hcard fallback y
end TunnellMap.RecordDA
