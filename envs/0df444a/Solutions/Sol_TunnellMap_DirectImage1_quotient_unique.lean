-- Prove2me | solution 1 for TunnellMap.DirectImage1.quotient_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:49.94833+00:00
-- url     : https://prove2.me/submissions/477e5c47-0780-436f-bffc-296b068b07d6

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
namespace DirectImage1
theorem _root_.solution {n : ℤ} (p : DirectImage1 n)
    {q : ℤ} (hq : p.rep.1.x + 4 * p.rep.1.z - p.rep.1.y = 4 * q) :
    q = p.quotient := by
  nlinarith [p.equation]
end DirectImage1
end TunnellMap
