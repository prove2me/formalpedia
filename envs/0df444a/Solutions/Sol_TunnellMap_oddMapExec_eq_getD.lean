-- Prove2me | solution 1 for TunnellMap.oddMapExec_eq_getD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:14:28.264805+00:00
-- url     : https://prove2.me/submissions/6effb2cb-3fbc-4561-a803-897a8ed1287e

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap
import Theorems.Thm_TunnellMap_RecordDA_residualMapExec_eq_getD

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution (hnpos : 0 < n) (hsq : Squarefree n)
    (fallback : AResidual n) (q : BOddRep n) :
    oddMapExec hnpos hsq fallback q =
      (oddMapExecOpt hnpos hsq q).getD fallback.1 := by
  unfold oddMapExec oddMapExecOpt
  by_cases hd : SourceUsedTriple q.1
  · rw [dif_pos hd, dif_pos hd]
  · rw [dif_neg hd, dif_neg hd, RecordDA.residualMapExec_eq_getD]
    cases RecordDA.residualMapExecOpt hnpos hsq
      (⟨q, fun hc => hd ((directSourceUsed_iff q).mp hc)⟩ : BResidual n) <;> rfl
end TunnellMap
