-- Prove2me | solution 1 for ThreeSum.LightLocalCoverRetention.base_le_nextFree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:28:38.467227+00:00
-- url     : https://prove2.me/submissions/ace67f2a-844d-44bc-b413-d7b3d29fba01

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverRetention

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverRetention
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMetadata
set_option maxHeartbeats 1000000
namespace ThreeSum.LightLocalCoverRetention
theorem _root_.solution (base h : ℕ) : base ≤ nextFree base h := by
  unfold nextFree scheduleMaps work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr
    LightCoverGreedy.total
  omega
end ThreeSum.LightLocalCoverRetention
