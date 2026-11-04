-- Prove2me | solution 1 for ThreeSum.Switch.actual_totalSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:04:09.613579+00:00
-- url     : https://prove2.me/submissions/845ec0c7-d3cf-444a-90e6-0e3a586980a4

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch

set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section
namespace ThreeSum.Switch
theorem _root_.solution (n : ℕ) : mu n = blockCount (inputBits n) * muZero n := rfl
end ThreeSum.Switch
