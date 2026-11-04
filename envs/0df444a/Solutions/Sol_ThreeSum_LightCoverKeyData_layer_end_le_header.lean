-- Prove2me | solution 1 for ThreeSum.LightCoverKeyData.layer_end_le_header
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:42:01.013422+00:00
-- url     : https://prove2.me/submissions/94eae7ca-a7ef-4c7d-8d75-69dd2ddec49b

import Definitions.Def_Submission_ThreeSum_LightCoverKeys
import Definitions.Def_Submission_ThreeSum_LightCoverKeyData

set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverKeyData
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
namespace ThreeSum.LightCoverKeyData
theorem _root_.solution (free h J : ℕ) :
    LightCoverKeys.afterCover free h+outputCount (512*h) h ≤ LightCoverKeys.keyHeader free h J := by
  unfold LightCoverKeys.keyHeader LightGlobalKeys.scratch
  omega
end ThreeSum.LightCoverKeyData
