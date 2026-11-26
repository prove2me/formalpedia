-- Prove2me | solution 1 for TunnellMap.Examples41.a_slice_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:36:12.957726+00:00
-- url     : https://prove2.me/submissions/026670dc-5222-4d6e-835c-0c3c756340b7

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
    (aSlice41 0).card = 4 ∧
      (aSlice41 1).card = 6 ∧
      (aSlice41 (-1)).card = 6 := by
  decide +kernel
end TunnellMap.Examples41
