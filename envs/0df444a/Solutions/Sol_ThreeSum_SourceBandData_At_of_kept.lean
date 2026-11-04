-- Prove2me | solution 1 for ThreeSum.SourceBandData.At.of_kept
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:10:25.85179+00:00
-- url     : https://prove2.me/submissions/7319cd43-c2f9-4704-a1d2-781baff81f9c

import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedStages
import Definitions.Def_Submission_ThreeSum_SourceBandData
import Definitions.Def_WeightedCache3SUM_Alias_f1b01b4676766ea6
import Theorems.Thm_ThreeSum_SourceBandLayout_flat_end_le_work
import Theorems.Thm_ThreeSum_SourceBandLayout_header_end


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandData
open Light BandPartition SourceBandLayout
namespace ThreeSum.SourceBandData
namespace At
theorem _root_.solution {μ ν : ℕ → ℤ} {f : ℕ → ℤ} {base n g p m i bound : ℕ} {shift : ℤ}
    (H : At μ f base n g p m shift i) (hm : 0 < m) (hi : i < size n g)
    (K : Kept μ ν bound) (hbound : work base n g m ≤ bound) :
    At ν f base n g p m shift i := by
  have he := header_end (base := base) (m := m) hi
  have hf := flat_end_le_work (base := base) (m := m) hi
  have hh : hist base n g m i ≤ flat base n g m i+cap n g := by
    unfold flat cursor offsets codes
    omega
  apply H.transfer hm
  · intro q hq
    exact K _ (by omega)
  · intro x _ hxe
    exact K _ (by omega)
end At
end ThreeSum.SourceBandData
