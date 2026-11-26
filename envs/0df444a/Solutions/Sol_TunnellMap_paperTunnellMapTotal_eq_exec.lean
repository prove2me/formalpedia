-- Prove2me | solution 1 for TunnellMap.paperTunnellMapTotal_eq_exec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:15:10.50556+00:00
-- url     : https://prove2.me/submissions/dede79f9-36f3-40fb-be27-36efac9f1b3d

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap
import Theorems.Thm_TunnellMap_paperTunnellMapTotal_eq
import Theorems.Thm_TunnellMap_paperTunnellMapExec_eq


set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (fallback : AResidual n) (p : BRep n) :
    paperTunnellMapTotal hn hnpos hsq hbal p =
      paperTunnellMapExec hnpos hsq fallback p := by
  rw [paperTunnellMapTotal_eq hn hnpos hsq hbal,
    paperTunnellMapExec_eq hn hnpos hsq (fintype_balance_of_nat_card hbal)]
end TunnellMap
