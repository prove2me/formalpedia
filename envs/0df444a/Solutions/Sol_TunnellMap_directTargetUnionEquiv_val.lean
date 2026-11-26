-- Prove2me | solution 1 for TunnellMap.directTargetUnionEquiv_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:38:43.428215+00:00
-- url     : https://prove2.me/submissions/3fffba8d-30b1-42b4-a2ba-1529286e7406

import Definitions.Def_TunnellMap_ResidualBalance
import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableDirect

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution {n : ℤ} (hn : Odd n) (i : DirectImage n) :
    (directTargetUnionEquiv hn i).1 = directImageRep i := by
  rcases i with i | i | i <;> rfl
end TunnellMap
