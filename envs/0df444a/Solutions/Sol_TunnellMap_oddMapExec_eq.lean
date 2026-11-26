-- Prove2me | solution 1 for TunnellMap.oddMapExec_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:07:01.418947+00:00
-- url     : https://prove2.me/submissions/ec140b33-edff-4556-8682-cc6995d5a0cb

import Definitions.Def_TunnellMap_ComputableDirect
import Definitions.Def_TunnellMap_ComputablePipeline
import Definitions.Def_TunnellMap_FullAssembly
import Definitions.Def_TunnellMap_ComputableFullMap
import Theorems.Thm_TunnellMap_oddEquivOfBalance_apply_direct
import Theorems.Thm_TunnellMap_oddEquivOfBalance_apply_residual
import Theorems.Thm_TunnellMap_RecordDA_residualMapExec_eq_residualEquiv
import Theorems.Thm_TunnellMap_directMapExec_eq
import Theorems.Thm_TunnellMap_residual_orbit_card_eq


set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hbal : Fintype.card (BOddRep n) = Fintype.card (ARep n))
    (fallback : AResidual n) (q : BOddRep n) :
    oddMapExec hnpos hsq fallback q = oddEquivOfBalance hn hnpos hbal q := by
  by_cases hd : DirectSourceUsed q
  · have hd' : SourceUsedTriple q.1 := (directSourceUsed_iff q).mp hd
    rw [oddEquivOfBalance_apply_direct hn hnpos hbal q hd, oddMapExec,
      dif_pos hd', directMapExec_eq hn q hd]
    rfl
  · have hd' : ¬ SourceUsedTriple q.1 := fun hc =>
      hd ((directSourceUsed_iff q).mpr hc)
    rw [oddEquivOfBalance_apply_residual hn hnpos hbal q hd, oddMapExec,
      dif_neg hd']
    congr 1
    exact RecordDA.residualMapExec_eq_residualEquiv hn hnpos hsq
      (residual_orbit_card_eq hn hnpos hbal) fallback _
end TunnellMap
