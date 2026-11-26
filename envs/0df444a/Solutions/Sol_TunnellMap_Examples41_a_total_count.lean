-- Prove2me | solution 1 for TunnellMap.Examples41.a_total_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:49:17.277849+00:00
-- url     : https://prove2.me/submissions/5089f2dc-4da0-4e3f-bcac-2d773d71143f

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
theorem _root_.solution : aRepresentations41.card = 16 := by
  decide +kernel
end TunnellMap.Examples41
