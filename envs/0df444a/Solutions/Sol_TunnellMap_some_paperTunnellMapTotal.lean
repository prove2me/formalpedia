-- Prove2me | solution 1 for TunnellMap.some_paperTunnellMapTotal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:54:59.832367+00:00
-- url     : https://prove2.me/submissions/8076a68e-cbd6-4ed6-a6ed-ce53e8ec699f

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
namespace TunnellMap
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n) (hbal : Nat.card (BRep n) = 2 * Nat.card (ARep n))
    (p : BRep n) :
    some (paperTunnellMapTotal hn hnpos hsq hbal p) =
      paperTunnellMapExecOpt hnpos hsq p :=
  Option.some_get _
end TunnellMap
