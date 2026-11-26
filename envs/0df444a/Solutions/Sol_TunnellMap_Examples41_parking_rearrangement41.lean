-- Prove2me | solution 1 for TunnellMap.Examples41.parking_rearrangement41
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:47:26.3578+00:00
-- url     : https://prove2.me/submissions/3f98a1ff-5847-4eda-939d-f592c53438f4

import Definitions.Def_TunnellMap_Examples41Generator
import Definitions.Def_TunnellMap_Sharpness
import Definitions.Def_TunnellMap_Examples41Matching
import Theorems.Thm_TunnellMap_Examples41_isParkingFunction_of_sortedCounts_eq
import Theorems.Thm_TunnellMap_Examples41_sortedCounts_counts41

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open GloballyRanked
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution :
    sortedCounts [1, 3, 1, 1] = [1, 1, 1, 3] ∧
      IsParkingFunction [1, 3, 1, 1] ∧
      1 + 3 + 1 + 1 = 6 ∧
      6 ≤ 4 * (4 + 1) / 2 := by
  exact ⟨sortedCounts_counts41,
    isParkingFunction_of_sortedCounts_eq (by decide) sortedCounts_counts41 (by decide),
    by norm_num, by norm_num⟩
end TunnellMap.Examples41
