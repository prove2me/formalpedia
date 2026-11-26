-- Prove2me | solution 1 for TunnellMap.RecordDA.inverseByRerunExec_eq_residualEquiv_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:02:33.745699+00:00
-- url     : https://prove2.me/submissions/370c467d-94aa-4dd9-bd7e-5008d49f215b

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_InverseByRerun
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ComputablePipeline
import Theorems.Thm_TunnellMap_RecordDA_inverseByRerunExec_eq
import Theorems.Thm_TunnellMap_RecordDA_inverseByRerun_eq_residualEquiv_symm


set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
variable [Fintype (BOddRep n)]
variable [Fintype (ARep n)]
namespace TunnellMap.RecordDA
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallback : BResidual n) (y : AResidual n) :
    inverseByRerunExec hsq fallback y =
      (residualEquivOfOrbitCard hnpos hcard).symm y := by
  rw [inverseByRerunExec_eq]
  exact inverseByRerun_eq_residualEquiv_symm hn hnpos (framesExec hsq) hcard
    fallback y
end TunnellMap.RecordDA
