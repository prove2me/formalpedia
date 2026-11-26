-- Prove2me | solution 1 for TunnellMap.Examples41.sortedCounts_counts41
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:21:21.764302+00:00
-- url     : https://prove2.me/submissions/73904049-40e0-40e6-86ac-a4d9eacecafc

import Definitions.Def_TunnellMap_Examples41Generator
import Definitions.Def_TunnellMap_Sharpness
import Definitions.Def_TunnellMap_Examples41Matching

set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open GloballyRanked
set_option maxRecDepth 10000
namespace TunnellMap.Examples41
theorem _root_.solution : sortedCounts [1, 3, 1, 1] = [1, 1, 1, 3] := by
  unfold sortedCounts
  refine List.Perm.eq_of_pairwise' (r := (· ≤ ·))
    (List.pairwise_mergeSort' (· ≤ ·) [1, 3, 1, 1]) (by decide) ?_
  exact (List.mergeSort_perm [1, 3, 1, 1] _).trans (by decide)
end TunnellMap.Examples41
