-- Prove2me | solution 1 for TunnellMap.Examples41.residual_matching41_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:46:13.758164+00:00
-- url     : https://prove2.me/submissions/4876196c-5101-4631-b1b9-816fd0f59b03

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
    residualRanking41.Stable residualMatching41 := by
  intro s t
  fin_cases s <;> fin_cases t <;>
    unfold GloballyRanked.Blocks <;>
    decide
end TunnellMap.Examples41
