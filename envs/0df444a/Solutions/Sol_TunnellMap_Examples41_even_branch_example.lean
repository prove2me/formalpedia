-- Prove2me | solution 1 for TunnellMap.Examples41.even_branch_example
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:38:13.39907+00:00
-- url     : https://prove2.me/submissions/19a333b8-a30c-4388-8788-d8479d61da36

import Definitions.Def_TunnellMap_ControlCost
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_PureCoordinates
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Definitions.Def_TunnellMap_Examples41

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution :
    (evenEquiv 41 evenSource41).1 = ⟨2, -1, 1⟩ := by
  rfl
end TunnellMap.Examples41
