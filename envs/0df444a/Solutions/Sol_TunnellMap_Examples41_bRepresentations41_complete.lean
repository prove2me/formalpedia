-- Prove2me | solution 1 for TunnellMap.Examples41.bRepresentations41_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:36:13.85392+00:00
-- url     : https://prove2.me/submissions/dfe66bc8-c690-491d-98b7-50b2a846d9e1

import Definitions.Def_TunnellMap_ControlCost
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_PureCoordinates
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Definitions.Def_TunnellMap_Examples41
import Theorems.Thm_TunnellMap_Examples41_box41_complete_for_b

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution (p : Triple) :
    p ∈ bRepresentations41 ↔ bForm p = 41 := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · exact fun h => Finset.mem_filter.mpr ⟨box41_complete_for_b p h, h⟩
end TunnellMap.Examples41
