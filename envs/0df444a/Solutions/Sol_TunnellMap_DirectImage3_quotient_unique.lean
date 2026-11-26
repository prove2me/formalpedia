-- Prove2me | solution 1 for TunnellMap.DirectImage3.quotient_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:59.862951+00:00
-- url     : https://prove2.me/submissions/b6800f61-c039-4c92-a382-b41dd61f48de

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
namespace DirectImage3
theorem _root_.solution {n : ℤ} (p : DirectImage3 n)
    {q : ℤ} (hq : p.rep.1.x = 2 * q) : q = p.quotient := by
  nlinarith [p.equation]
end DirectImage3
end TunnellMap
