-- Prove2me | solution 1 for TunnellMap.RecordDA.inverseByRerunExecTotal_eq_residualEquiv_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:04:35.483007+00:00
-- url     : https://prove2.me/submissions/37f44f5a-f74f-48cf-bd84-2b3ec987c5ae

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap
import Theorems.Thm_TunnellMap_RecordDA_inverseByRerunExec_eq
import Theorems.Thm_TunnellMap_RecordDA_inverseByRerunExec_eq_residualEquiv_symm
import Theorems.Thm_TunnellMap_RecordDA_inverseByRerun_apply


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
    inverseByRerunExecTotal hn hnpos hsq hcard y =
      (residualEquivOfOrbitCard hnpos hcard).symm y := by
  let z := inverseByRerunExecTotal hn hnpos hsq hcard y
  have hsame : z = inverseByRerunExec hsq z y := by
    rw [inverseByRerunExec_eq, inverseByRerun_apply hn hnpos (framesExec hsq) hcard]
    apply Option.some.inj
    exact (Option.some_get
      (inverseByRerunExecOpt_isSome hn hnpos hsq hcard y)).trans
      (inverseByRerunExecOpt_eq_some_value hn hnpos hsq hcard y)
  change z = (residualEquivOfOrbitCard hnpos hcard).symm y
  exact hsame.trans
    (inverseByRerunExec_eq_residualEquiv_symm hn hnpos hsq hcard z y)
end TunnellMap.RecordDA
