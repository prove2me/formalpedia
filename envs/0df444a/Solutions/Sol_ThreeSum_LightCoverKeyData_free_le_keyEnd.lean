-- Prove2me | solution 1 for ThreeSum.LightCoverKeyData.free_le_keyEnd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:49:56.297445+00:00
-- url     : https://prove2.me/submissions/53c070a4-5547-498b-8722-c98269a3c8cc

import Definitions.Def_Submission_ThreeSum_LightCoverKeys
import Definitions.Def_Submission_ThreeSum_LightCoverKeyData
import Theorems.Thm_ThreeSum_LightCoverKeyData_afterCover_le_keyEnd
import Theorems.Thm_ThreeSum_LightLocalCoverRetention_base_le_nextFree


set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverKeyData
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
namespace ThreeSum.LightCoverKeyData
theorem _root_.solution (free h J : ℕ) : free ≤ keyEnd free h J := by
  have hh := LightLocalCoverRetention.base_le_nextFree (LightLocalCoverInit.base free) h
  have hk := afterCover_le_keyEnd free h J
  change free+20 ≤ LightCoverKeys.afterCover free h at hh
  omega
end ThreeSum.LightCoverKeyData
