-- Prove2me | solution 1 for TunnellMap.Examples41.residual_proposal_counts41
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:47:05.845327+00:00
-- url     : https://prove2.me/submissions/ba0071af-4dbf-4393-86ed-4e3271515d0e

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
    residualRanking41.proposalCount residualMatching41 0 = 1 ∧
      residualRanking41.proposalCount residualMatching41 1 = 3 ∧
      residualRanking41.proposalCount residualMatching41 2 = 1 ∧
      residualRanking41.proposalCount residualMatching41 3 = 1 := by
  decide
end TunnellMap.Examples41
