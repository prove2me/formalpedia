-- Prove2me | solution 1 for ThreeSum.EncodedColorCoverData.header_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:24:39.799203+00:00
-- url     : https://prove2.me/submissions/3e2fecbb-ceb1-4dec-bf65-439686de2e59

import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
import Definitions.Def_Submission_ThreeSum_EncodedColorCoverData
import Theorems.Thm_ThreeSum_LightCoverKeyData_afterCover_le_keyEnd
import Theorems.Thm_ThreeSum_LightLocalCoverRetention_base_le_nextFree


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorCoverData
open Light GlobalEncoding LocalCoverBounds SourceFiniteInputs
namespace ThreeSum.EncodedColorCoverData
theorem _root_.solution (free h J : ℕ) : free+20 ≤ LightCoverKeyData.keyEnd free h J :=
  (LightLocalCoverRetention.base_le_nextFree (LightLocalCoverInit.base free) h).trans
    (LightCoverKeyData.afterCover_le_keyEnd free h J)
end ThreeSum.EncodedColorCoverData
