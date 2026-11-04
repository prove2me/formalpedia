-- Prove2me | solution 1 for ThreeSum.WantedPairs.row_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:10:41.995888+00:00
-- url     : https://prove2.me/submissions/d45428af-cba4-4892-86f7-8af190bfcf8b

import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
import Theorems.Thm_ThreeSum_SourceBucketView_indices_length


set_option autoImplicit false
open ThreeSum ThreeSum.WantedPairs
open Light SourceBuckets
open scoped BigOperators
set_option maxHeartbeats 1200000
namespace ThreeSum.WantedPairs
theorem _root_.solution {μ : ℕ → ℤ} {offsets flat NR M i : ℕ} {left right : ℕ → ℕ}
    (H : Stored μ right NR M offsets flat) (hi : left i < M) :
    (row μ offsets flat left i).length=LightHistogram.count right (left i) NR := by
  rw [row,List.length_map,SourceBucketView.indices_length H hi]
end ThreeSum.WantedPairs
