-- Prove2me | solution 1 for TunnellMap.DirectDomain1.quotient_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:33.628665+00:00
-- url     : https://prove2.me/submissions/f6ec6ee8-9828-4033-9e1e-53a46cc46381

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_QuarterTurns

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
namespace DirectDomain1
theorem _root_.solution {n : ℤ} (p : DirectDomain1 n)
    {q : ℤ} (hq : p.rep.1.x + 2 * p.rep.1.z + p.rep.1.y = 8 * q) :
    q = p.quotient := by
  nlinarith [p.equation]
end DirectDomain1
end TunnellMap
