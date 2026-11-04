-- Prove2me | solution 1 for ThreeSum.LightCoverKeyData.keyEnd_le_space
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:51:39.408621+00:00
-- url     : https://prove2.me/submissions/45e9e796-6c59-4b19-b3c8-0e96240b6f1a

import Definitions.Def_Submission_ThreeSum_LightCoverKeys
import Definitions.Def_Submission_ThreeSum_LightCoverKeyData

set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverKeyData
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
namespace ThreeSum.LightCoverKeyData
theorem _root_.solution (free h J : ℕ) : keyEnd free h J ≤ LightCoverKeys.space free h J := by
  have hg : LightRadixKeys.space (LightGlobalKeys.scratch (LightCoverKeys.afterCover free h) h)
      (LightGlobalKeys.localCount h) J ≤ LightGlobalKeys.space (LightCoverKeys.afterCover free h) h J :=
    le_max_right _ _
  exact hg.trans (le_max_right _ _)
end ThreeSum.LightCoverKeyData
