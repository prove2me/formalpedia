-- Prove2me | solution 1 for TunnellMap.Examples41.b_total_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:49:12.414906+00:00
-- url     : https://prove2.me/submissions/81858538-b687-4370-9886-535ea3a37b46

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
theorem _root_.solution : bRepresentations41.card = 32 := by
  decide +kernel
end TunnellMap.Examples41
