-- Prove2me | solution 1 for TunnellMap.Examples41.residual_matching41_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:46:57.926355+00:00
-- url     : https://prove2.me/submissions/0d9815c5-68c2-49e2-9281-0959af7a1db3

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
    residualMatching41 0 = 0 ∧ residualMatching41 1 = 1 ∧
      residualMatching41 2 = 3 ∧ residualMatching41 3 = 2 := by
  decide
end TunnellMap.Examples41
