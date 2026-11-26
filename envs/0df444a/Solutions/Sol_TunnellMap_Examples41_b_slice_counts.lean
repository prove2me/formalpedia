-- Prove2me | solution 1 for TunnellMap.Examples41.b_slice_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:36:00.619577+00:00
-- url     : https://prove2.me/submissions/c43a96b8-1598-4fe2-9f1a-c02f33eed896

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
    (bSlice41 0).card = 4 ∧
      (bSlice41 1).card = 8 ∧
      (bSlice41 (-1)).card = 8 ∧
      (bSlice41 2).card = 6 ∧
      (bSlice41 (-2)).card = 6 := by
  decide +kernel
end TunnellMap.Examples41
