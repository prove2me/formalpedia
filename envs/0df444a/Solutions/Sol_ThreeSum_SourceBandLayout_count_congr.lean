-- Prove2me | solution 1 for ThreeSum.SourceBandLayout.count_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:57:24.623747+00:00
-- url     : https://prove2.me/submissions/d3fb6f2e-b064-4195-8b19-74feb5496856

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandLayout
open BandPartition LightHistogram SourceBuckets
namespace ThreeSum.SourceBandLayout
theorem _root_.solution {key key' : ℕ → ℕ} {N t : ℕ}
    (he : ∀ i < N, key i=key' i) (ht : t ≤ N) (r : ℕ) :
    count key r t=count key' r t := by
  unfold count
  congr 1
  apply Finset.filter_congr
  intro i hi
  rw [he i ((Finset.mem_range.mp hi).trans_le ht)]
end ThreeSum.SourceBandLayout
