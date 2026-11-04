-- Prove2me | solution 1 for ThreeSum.LightLocalCoverRetention.nextFree_le_space
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:51:38.155198+00:00
-- url     : https://prove2.me/submissions/d3536252-a771-46fc-88e7-0d59179d73d1

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverRetention
import Theorems.Thm_ThreeSum_LightLocalCoverLayout_schedule_end_le_space


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverRetention
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMetadata
set_option maxHeartbeats 1000000
namespace ThreeSum.LightLocalCoverRetention
theorem _root_.solution (base h : ℕ) : nextFree base h ≤ space base h :=
  schedule_end_le_space base h
end ThreeSum.LightLocalCoverRetention
