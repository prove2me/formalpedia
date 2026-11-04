-- Prove2me | solution 1 for ThreeSum.SourceBandData.At.nodup_positions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:53:56.676991+00:00
-- url     : https://prove2.me/submissions/c71d0101-7da2-4c4d-b594-125f05053102

import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedStages
import Definitions.Def_Submission_ThreeSum_SourceBandData
import Theorems.Thm_ThreeSum_LightSourceResidues_key_lt
import Theorems.Thm_ThreeSum_SourceBandLayout_key_lt
import Theorems.Thm_ThreeSum_SourceBucketView_nodup_indices


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandData
open Light BandPartition SourceBandLayout
namespace ThreeSum.SourceBandData
namespace At
theorem _root_.solution {μ : ℕ → ℤ} {f : ℕ → ℤ} {base n g p m i r : ℕ} {shift : ℤ}
    (H : At μ f base n g p m shift i) (hm : 0 < m) (hr : r < m) :
    (positions μ base n g m i r).Nodup := by
  apply (SourceBucketView.nodup_indices H.buckets
    (fun q _ => key_lt (f := f) (g := g) (p := p) (shift := shift) hm i q) hr).map
  intro x y hxy
  exact Nat.add_left_cancel hxy
end At
end ThreeSum.SourceBandData
