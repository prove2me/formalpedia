-- Prove2me | solution 1 for TunnellMap.paperTunnellMapTotal_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:12:00.747406+00:00
-- url     : https://prove2.me/submissions/dfa62300-315f-4796-b969-7a34eb3e8f46

import Definitions.Def_TunnellMap_FallbackFreeMap
import Definitions.Def_TunnellMap_BranchSpec
import Theorems.Thm_TunnellMap_paperTunnellMapTotal_val_eq

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) (hz : p.1.z % 2 = 0) :
    (paperTunnellMapTotal hn hnpos hsq hbal p).1 =
      ⟨p.1.x, p.1.y, p.1.z / 2⟩ := by
  refine paperTunnellMapTotal_val_eq hn hnpos hsq hbal ?_
  rw [paperTunnellMapExecOpt, dif_pos hz]
  rfl
end TunnellMap
