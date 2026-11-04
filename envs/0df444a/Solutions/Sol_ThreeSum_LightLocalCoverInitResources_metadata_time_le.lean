-- Prove2me | solution 1 for ThreeSum.LightLocalCoverInitResources.metadata_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:05:36.927613+00:00
-- url     : https://prove2.me/submissions/2322de53-7d35-4b41-9aac-ec59e6f008bf

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverResources
import Definitions.Def_Submission_ThreeSum_LightLocalCoverInitResources

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverInitResources
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout
set_option maxHeartbeats 1500000
namespace ThreeSum.LightLocalCoverInitResources
theorem _root_.solution (h : ℕ) :
    LightLocalCoverMetadata.time h ≤ LightLocalCoverSetup.time h+500 := by
  unfold LightLocalCoverMetadata.time LightLocalCoverSetup.time
  omega
end ThreeSum.LightLocalCoverInitResources
