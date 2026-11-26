-- Prove2me | solution 1 for TunnellMap.Examples41.balance_at_41
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:36:50.290059+00:00
-- url     : https://prove2.me/submissions/8e2627e0-aabe-4a9e-9d53-62e3e5239af3

import Definitions.Def_TunnellMap_ControlCost
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_PureCoordinates
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Definitions.Def_TunnellMap_Examples41
import Theorems.Thm_TunnellMap_Examples41_b_total_count
import Theorems.Thm_TunnellMap_Examples41_a_total_count

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution :
    bRepresentations41.card = 2 * aRepresentations41.card := by
  norm_num [b_total_count, a_total_count]
end TunnellMap.Examples41
