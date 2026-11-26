-- Prove2me | solution 1 for TunnellMap.Examples41.ranked_two_by_two_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:45:35.154807+00:00
-- url     : https://prove2.me/submissions/558a4a9e-25a6-4577-80fd-0619451b5553

import Definitions.Def_TunnellMap_Examples41Generator
import Definitions.Def_TunnellMap_Sharpness
import Definitions.Def_TunnellMap_Examples41Matching

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open GloballyRanked
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution : ranking2.Stable matching2 := by
  intro s t
  fin_cases s <;> fin_cases t <;>
    norm_num [GloballyRanked.Blocks, ranking2, rank2, matching2]
end TunnellMap.Examples41
