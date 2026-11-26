-- Prove2me | solution 1 for TunnellMap.paperTunnellMapTotal_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:57:26.539587+00:00
-- url     : https://prove2.me/submissions/322947c8-b283-41a8-867c-60dc76353fd1

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap
import Theorems.Thm_TunnellMap_some_paperTunnellMapTotal

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n)) (p : BRep n) :
    paperTunnellMapTotal hn hnpos hsq hbal p =
      paperTunnellMap hn hnpos (fintype_balance_of_nat_card hbal) p :=
  Option.some.inj
    ((some_paperTunnellMapTotal hn hnpos hsq hbal p).trans
      (paperTunnellMapExecOpt_eq_some hn hnpos hsq
        (fintype_balance_of_nat_card hbal) p))
end TunnellMap
