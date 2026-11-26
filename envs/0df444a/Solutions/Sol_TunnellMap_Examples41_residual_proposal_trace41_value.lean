-- Prove2me | solution 1 for TunnellMap.Examples41.residual_proposal_trace41_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:46:28.298968+00:00
-- url     : https://prove2.me/submissions/1e737b07-ab08-4244-a8b0-5da5872d8f0e

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
    residualProposalTrace41 =
      [(0, 0), (1, 0), (2, 3), (3, 2), (1, 3), (1, 1)] := rfl
end TunnellMap.Examples41
