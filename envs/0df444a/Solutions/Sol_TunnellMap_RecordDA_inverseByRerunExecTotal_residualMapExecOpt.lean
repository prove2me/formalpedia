-- Prove2me | solution 1 for TunnellMap.RecordDA.inverseByRerunExecTotal_residualMapExecOpt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:11:30.772117+00:00
-- url     : https://prove2.me/submissions/8d294e8e-cf71-4505-9882-9390d30d6c68

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap
import Theorems.Thm_TunnellMap_RecordDA_inverseByRerunExecTotal_eq_residualEquiv_symm
import Theorems.Thm_TunnellMap_canonicalResidualMapOf_eq_residualEquivOfOrbitCard


set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
open TunnellMap.RecordDA
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap.RecordDA
theorem _root_.solution
    (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (x : BResidual n) :
    inverseByRerunExecTotal hn hnpos hsq hcard
      (canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard) x) = x := by
  rw [inverseByRerunExecTotal_eq_residualEquiv_symm,
    canonicalResidualMapOf_eq_residualEquivOfOrbitCard hnpos hcard,
    Equiv.symm_apply_apply]
end TunnellMap.RecordDA
