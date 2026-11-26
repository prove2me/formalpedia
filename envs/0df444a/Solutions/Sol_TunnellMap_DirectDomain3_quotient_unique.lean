-- Prove2me | solution 1 for TunnellMap.DirectDomain3.quotient_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:45.712686+00:00
-- url     : https://prove2.me/submissions/f4de7ce3-c755-4cdc-bd83-ae866da4637c

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
namespace DirectDomain3
theorem _root_.solution {n : ℤ} (p : DirectDomain3 n)
    {q : ℤ} (hq : p.rep.1.x = 4 * q) : q = p.quotient := by
  nlinarith [p.equation]
end DirectDomain3
end TunnellMap
