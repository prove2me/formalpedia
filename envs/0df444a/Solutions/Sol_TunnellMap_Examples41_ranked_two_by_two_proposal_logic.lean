-- Prove2me | solution 1 for TunnellMap.Examples41.ranked_two_by_two_proposal_logic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:45:38.085285+00:00
-- url     : https://prove2.me/submissions/2d96a6dc-61b4-41e9-963e-284b2beec601

import Definitions.Def_TunnellMap_Examples41Generator
import Definitions.Def_TunnellMap_Sharpness
import Definitions.Def_TunnellMap_Examples41Matching

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open GloballyRanked
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution :
    ranking2.rank 0 0 < ranking2.rank 0 1 ∧
      ranking2.rank 1 0 < ranking2.rank 1 1 ∧
      ranking2.rank 0 0 < ranking2.rank 1 0 := by
  decide
end TunnellMap.Examples41
