-- Prove2me | solution 1 for TunnellMap.DirectDomain2.quotient_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:34.182164+00:00
-- url     : https://prove2.me/submissions/0bebdec0-4be2-4590-a631-eabc1e57530a

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
namespace DirectDomain2
theorem _root_.solution {n : ℤ} (p : DirectDomain2 n)
    {q : ℤ} (hq : p.rep.1.y - p.rep.1.x + 2 * p.rep.1.z = 8 * q) :
    q = p.quotient := by
  nlinarith [p.equation]
end DirectDomain2
end TunnellMap
