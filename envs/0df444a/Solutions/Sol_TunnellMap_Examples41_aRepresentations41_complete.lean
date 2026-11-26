-- Prove2me | solution 1 for TunnellMap.Examples41.aRepresentations41_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:36:17.102869+00:00
-- url     : https://prove2.me/submissions/e69ec05f-3ea6-48f7-b713-714b53c95d25

import Definitions.Def_TunnellMap_ControlCost
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_PureCoordinates
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Definitions.Def_TunnellMap_Examples41
import Theorems.Thm_TunnellMap_Examples41_box41_complete_for_a

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution (p : Triple) :
    p ∈ aRepresentations41 ↔ aForm p = 41 := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · exact fun h => Finset.mem_filter.mpr ⟨box41_complete_for_a p h, h⟩
end TunnellMap.Examples41
