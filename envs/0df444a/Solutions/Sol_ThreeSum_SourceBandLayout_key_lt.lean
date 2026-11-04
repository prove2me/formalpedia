-- Prove2me | solution 1 for ThreeSum.SourceBandLayout.key_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:57:33.909853+00:00
-- url     : https://prove2.me/submissions/79c08494-52a1-45d9-8a7b-57e9c30ed695

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Theorems.Thm_ThreeSum_LightSourceResidues_key_lt


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandLayout
open BandPartition LightHistogram SourceBuckets
namespace ThreeSum.SourceBandLayout
theorem _root_.solution {f : ℕ → ℤ} {g p m : ℕ} {shift : ℤ} (hm : 0 < m) (i j : ℕ) :
    key f g p m shift i j < m := LightSourceResidues.key_lt hm shift _
end ThreeSum.SourceBandLayout
