-- Prove2me | solution 1 for TunnellMap.Examples41.midpoint_bound_attained
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:38:11.324802+00:00
-- url     : https://prove2.me/submissions/eab98463-a21e-4f3d-8073-dca4f41cd02a

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
theorem _root_.solution : qForm ⟨1, -4, 1⟩ = (41 - 1) / 2 := by
  norm_num [qForm]
end TunnellMap.Examples41
