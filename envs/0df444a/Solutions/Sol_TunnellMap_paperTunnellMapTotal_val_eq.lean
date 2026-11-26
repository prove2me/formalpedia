-- Prove2me | solution 1 for TunnellMap.paperTunnellMapTotal_val_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:58:22.624614+00:00
-- url     : https://prove2.me/submissions/7069643c-689c-40f1-8108-2e38953c32d4

import Definitions.Def_TunnellMap_FallbackFreeMap
import Definitions.Def_TunnellMap_BranchSpec
import Theorems.Thm_TunnellMap_some_paperTunnellMapTotal


set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    {p : BRep n} {v : Triple}
    (h : Option.map (fun a : ARep n => a.1) (paperTunnellMapExecOpt hnpos hsq p) =
      some v) :
    (paperTunnellMapTotal hn hnpos hsq hbal p).1 = v := by
  rw [← some_paperTunnellMapTotal hn hnpos hsq hbal p, Option.map_some] at h
  exact Option.some.inj h
end TunnellMap
