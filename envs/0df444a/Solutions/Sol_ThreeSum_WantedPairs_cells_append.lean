-- Prove2me | solution 1 for ThreeSum.WantedPairs.cells_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:04:26.352291+00:00
-- url     : https://prove2.me/submissions/6a0fb6de-2f34-4800-b258-f5ee26892aab

import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
set_option autoImplicit false
open ThreeSum ThreeSum.WantedPairs
open Light SourceBuckets
open scoped BigOperators
set_option maxHeartbeats 1200000
namespace ThreeSum.WantedPairs
theorem _root_.solution (as bs : List (ℕ × ℕ)) : cells (as ++ bs) = cells as ++ cells bs :=
  List.flatMap_append ..
end ThreeSum.WantedPairs
