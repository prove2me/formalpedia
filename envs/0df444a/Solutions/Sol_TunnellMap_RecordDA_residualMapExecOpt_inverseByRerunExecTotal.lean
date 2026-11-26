-- Prove2me | solution 1 for TunnellMap.RecordDA.residualMapExecOpt_inverseByRerunExecTotal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:11:33.945906+00:00
-- url     : https://prove2.me/submissions/c9a1222e-e9a0-4cf4-960d-3c3efc4209f9

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
    (y : AResidual n) :
    canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard)
      (inverseByRerunExecTotal hn hnpos hsq hcard y) = y := by
  rw [inverseByRerunExecTotal_eq_residualEquiv_symm,
    canonicalResidualMapOf_eq_residualEquivOfOrbitCard hnpos hcard,
    Equiv.apply_symm_apply]
end TunnellMap.RecordDA
