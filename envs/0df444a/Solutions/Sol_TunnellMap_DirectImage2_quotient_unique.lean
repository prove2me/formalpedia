-- Prove2me | solution 1 for TunnellMap.DirectImage2.quotient_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:53.323679+00:00
-- url     : https://prove2.me/submissions/32caafff-8987-4079-8d59-f1c903b10cc5

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
namespace DirectImage2
theorem _root_.solution {n : ℤ} (p : DirectImage2 n)
    {q : ℤ} (hq : p.rep.1.x - 4 * p.rep.1.z + p.rep.1.y = 4 * q) :
    q = p.quotient := by
  nlinarith [p.equation]
end DirectImage2
end TunnellMap
