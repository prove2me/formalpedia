-- Prove2me | solution 1 for TunnellMap.Examples41.coordinate_change_example
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:36:51.107388+00:00
-- url     : https://prove2.me/submissions/e067ade8-b46a-4a96-a714-33354c22b0f1

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
    bLift Xcoord = ⟨-4, -1, 2⟩ ∧
      aLift Ycoord = ⟨2, -1, 4⟩ ∧
      qForm (bLift Xcoord) = 41 ∧
      qForm (aLift Ycoord) = 41 := by
  norm_num [Xcoord, Ycoord, bLift, aLift, qForm]
end TunnellMap.Examples41
