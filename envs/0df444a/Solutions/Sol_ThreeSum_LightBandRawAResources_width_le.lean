-- Prove2me | solution 1 for ThreeSum.LightBandRawAResources.width_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:07:39.621778+00:00
-- url     : https://prove2.me/submissions/1f02181f-dd38-485d-83eb-441bd54df5ea

import Definitions.Def_Submission_ThreeSum_EncodedColorLayout
import Definitions.Def_Submission_ThreeSum_LightBandRawAResources
import Theorems.Thm_ThreeSum_LightBandRawAResources_clog_le_self
import Theorems.Thm_ThreeSum_BandPartition_size_le
import Theorems.Thm_ThreeSum_LightPrimePool_size_le


set_option autoImplicit false
open ThreeSum ThreeSum.LightBandRawAResources
open Light EncodedColorLayout
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
namespace ThreeSum.LightBandRawAResources
theorem _root_.solution (n g : ℕ) : ColorBandBounds.width n g ≤ 3*n+1 := by
  have hm := BandPartition.size_le n g
  have hc := clog_le_self (BandPartition.size n g+BandPartition.size n g+BandPartition.size n g+1)
  unfold ColorBandBounds.width LightBandEnumeration.width
  omega
end ThreeSum.LightBandRawAResources
