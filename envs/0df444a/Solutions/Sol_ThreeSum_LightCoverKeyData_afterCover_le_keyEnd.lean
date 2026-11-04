-- Prove2me | solution 1 for ThreeSum.LightCoverKeyData.afterCover_le_keyEnd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:47:14.464407+00:00
-- url     : https://prove2.me/submissions/10a022b3-1b54-417d-84a9-6144311bd86e

import Definitions.Def_Submission_ThreeSum_LightCoverKeys
import Definitions.Def_Submission_ThreeSum_LightCoverKeyData
import Theorems.Thm_ThreeSum_LightCoverKeyData_layer_end_le_header

set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverKeyData
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
namespace ThreeSum.LightCoverKeyData
theorem _root_.solution (free h J : ℕ) : LightCoverKeys.afterCover free h ≤ keyEnd free h J := by
  have hh := layer_end_le_header free h J
  unfold keyEnd
  omega
end ThreeSum.LightCoverKeyData
