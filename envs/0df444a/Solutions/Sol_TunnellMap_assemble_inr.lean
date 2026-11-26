-- Prove2me | solution 1 for TunnellMap.assemble_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:43.638786+00:00
-- url     : https://prove2.me/submissions/18b5fdbc-b380-45ab-8e53-736dbfb493d6

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_Assembly

set_option autoImplicit true
open TunnellMap
variable {E O A : Type*}
namespace TunnellMap
theorem _root_.solution (even : E ≃ A) (odd : O ≃ A) (o : O) :
    assemble even odd (Sum.inr o) = odd o :=
  rfl
end TunnellMap
