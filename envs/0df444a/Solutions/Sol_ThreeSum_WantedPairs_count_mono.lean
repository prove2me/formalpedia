-- Prove2me | solution 1 for ThreeSum.WantedPairs.count_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:04:01.822085+00:00
-- url     : https://prove2.me/submissions/83734c78-5dc0-48ea-9a1b-1a0a7e725ad8

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
theorem _root_.solution (left right : ℕ → ℕ) (NR : ℕ) : Monotone (count left right NR) := by
  intro i j hij
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hij)
end ThreeSum.WantedPairs
