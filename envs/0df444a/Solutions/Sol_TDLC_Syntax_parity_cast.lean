-- Prove2me | solution 1 for TDLC.Syntax.parity_cast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:27:01.897814+00:00
-- url     : https://prove2.me/submissions/3031f995-674b-48d0-b3eb-f74d5708db1b

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Syntax

set_option autoImplicit true
open TDLC TDLC.Syntax
namespace TDLC.Syntax
theorem _root_.solution {A : Type} {x y x' y' : A}
    (hx : x = x') (hy : y = y') (s : TDLC.Step x y) :
    TDLC.Step.parity (castStep hx hy s) = TDLC.Step.parity s := by
  cases hx
  cases hy
  rfl
end TDLC.Syntax
