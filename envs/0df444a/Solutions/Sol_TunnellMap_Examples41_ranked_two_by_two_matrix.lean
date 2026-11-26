-- Prove2me | solution 1 for TunnellMap.Examples41.ranked_two_by_two_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:45:31.964867+00:00
-- url     : https://prove2.me/submissions/df36a15e-6d0e-4436-a422-ae9795415e7a

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
    ranking2.rank 0 0 = 1 ∧ ranking2.rank 0 1 = 3 ∧
      ranking2.rank 1 0 = 2 ∧ ranking2.rank 1 1 = 4 := by
  decide
end TunnellMap.Examples41
