-- Prove2me | solution 1 for ThreeSum.WantedPairs.count_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:04:25.186395+00:00
-- url     : https://prove2.me/submissions/8070076b-663d-445c-ba6b-3a1c29a1d0a7

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
theorem _root_.solution (left right : ℕ → ℕ) (NR n : ℕ) :
    count left right NR (n+1)=count left right NR n+LightHistogram.count right (left n) NR :=
  Finset.sum_range_succ _ _
end ThreeSum.WantedPairs
