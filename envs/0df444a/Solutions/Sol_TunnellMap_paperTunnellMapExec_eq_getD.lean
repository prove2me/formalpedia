-- Prove2me | solution 1 for TunnellMap.paperTunnellMapExec_eq_getD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:41:16.713464+00:00
-- url     : https://prove2.me/submissions/b91d15e6-e6d4-43d2-9dc5-6e9d700a5b05

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap
import Theorems.Thm_TunnellMap_oddMapExec_eq_getD

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution (hnpos : 0 < n) (hsq : Squarefree n)
    (fallback : AResidual n) (p : BRep n) :
    paperTunnellMapExec hnpos hsq fallback p =
      (paperTunnellMapExecOpt hnpos hsq p).getD fallback.1 := by
  unfold paperTunnellMapExec paperTunnellMapExecOpt
  by_cases h : p.1.z % 2 = 0
  · rw [dif_pos h, dif_pos h, Option.getD_some]
  · rw [dif_neg h, dif_neg h]
    exact oddMapExec_eq_getD hnpos hsq fallback
      ⟨p.1, p.2, Int.odd_iff.mpr (by omega)⟩
end TunnellMap
