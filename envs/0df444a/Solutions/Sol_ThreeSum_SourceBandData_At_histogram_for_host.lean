-- Prove2me | solution 1 for ThreeSum.SourceBandData.At.histogram_for_host
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:08:59.203218+00:00
-- url     : https://prove2.me/submissions/fd622a8e-3bd7-4dce-b5ae-56cb6f617c8b

import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Definitions.Def_Submission_ThreeSum_LightBlockSourceRetainedStages
import Definitions.Def_Submission_ThreeSum_SourceBandData

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandData
open Light BandPartition SourceBandLayout
namespace ThreeSum.SourceBandData
namespace At
theorem _root_.solution {μ : ℕ → ℤ} {f : ℕ → ℤ} {base n g p m i : ℕ} {shift : ℤ}
    (H : At μ f base n g p m shift i) (r : ℕ) (hr : r < m) :
    μ (hist base n g m i+r) =
      (LightBlockSourceRetainedStages.histogram p m shift (fun j => f (start g i+j)) (len n g i) r : ℤ) :=
  H.histRead r hr
end At
end ThreeSum.SourceBandData
