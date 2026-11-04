-- Prove2me | solution 1 for ThreeSum.GlobalKeyOffset.keys_length_records
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:51:59.475819+00:00
-- url     : https://prove2.me/submissions/ed2de3ee-c155-4827-ad3d-78d2d2626e72

import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Definitions.Def_Submission_ThreeSum_LightOriginalOffset
import Definitions.Def_Submission_ThreeSum_RawReporting
import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
import Theorems.Thm_ThreeSum_GlobalKeyEnumeration_globalKeys_eq_map


set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyOffset
open GlobalEncoding GlobalKeyEnumeration
open scoped BigOperators
set_option maxHeartbeats 1800000
namespace ThreeSum.GlobalKeyOffset
theorem _root_.solution (h J : ℕ) : (globalKeys h J).length=(globalRecords h J).length := by
  rw [globalKeys_eq_map,List.length_map]
end ThreeSum.GlobalKeyOffset
