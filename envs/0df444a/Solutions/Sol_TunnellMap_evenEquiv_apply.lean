-- Prove2me | solution 1 for TunnellMap.evenEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:18.099862+00:00
-- url     : https://prove2.me/submissions/915616c4-e6e9-4cd9-baea-6892d8833950

import Mathlib
import Definitions.Def_TunnellMap_Basic

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (n : ℤ) (p : BEvenParam n) :
    (evenEquiv n p).1 = ⟨p.x, p.y, p.w⟩ :=
  rfl
end TunnellMap
