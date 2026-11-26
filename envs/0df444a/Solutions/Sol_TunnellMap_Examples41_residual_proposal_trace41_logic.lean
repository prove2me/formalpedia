-- Prove2me | solution 1 for TunnellMap.Examples41.residual_proposal_trace41_logic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:46:32.562494+00:00
-- url     : https://prove2.me/submissions/9aceaffd-9ec4-4d21-b471-9142e4cdcda9

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
    residualRank41 0 0 < residualRank41 0 2 ∧
      residualRank41 1 0 < residualRank41 1 3 ∧
      residualRank41 1 3 < residualRank41 1 1 ∧
      residualRank41 2 3 < residualRank41 2 1 ∧
      residualRank41 3 2 < residualRank41 3 1 ∧
      residualRank41 0 0 < residualRank41 1 0 ∧
      residualRank41 2 3 < residualRank41 1 3 := by
  decide
end TunnellMap.Examples41
