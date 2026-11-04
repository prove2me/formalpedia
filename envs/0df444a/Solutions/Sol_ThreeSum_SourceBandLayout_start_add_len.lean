-- Prove2me | solution 1 for ThreeSum.SourceBandLayout.start_add_len
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:08:53.036206+00:00
-- url     : https://prove2.me/submissions/3783a605-c1aa-41fc-b64a-82bd424cad7c

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSourceBucketOriginal
import Definitions.Def_Submission_ThreeSum_SourceBucketView
import Definitions.Def_Submission_ThreeSum_SourceBandLayout

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandLayout
open BandPartition LightHistogram SourceBuckets
namespace ThreeSum.SourceBandLayout
theorem _root_.solution {n g i : ℕ} (hg : 0 < g) (hi : i < size n g) :
    start g i+len n g i = stop n g i := by
  have hs := start_lt_stop hg hi
  unfold len
  omega
end ThreeSum.SourceBandLayout
