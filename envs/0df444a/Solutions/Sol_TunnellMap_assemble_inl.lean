-- Prove2me | solution 1 for TunnellMap.assemble_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:40.219184+00:00
-- url     : https://prove2.me/submissions/2f9d7bc9-7405-4d2a-8f5d-082e95067f04

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_Assembly

set_option autoImplicit true
open TunnellMap
variable {E O A : Type*}
namespace TunnellMap
theorem _root_.solution (even : E ≃ A) (odd : O ≃ A) (e : E) :
    assemble even odd (Sum.inl e) = even e :=
  rfl
end TunnellMap
