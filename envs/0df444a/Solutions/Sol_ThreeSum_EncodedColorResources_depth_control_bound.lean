-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.depth_control_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:40:59.947049+00:00
-- url     : https://prove2.me/submissions/5059548d-3a13-494a-84f7-5f665718a1f1

import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeHost
import Definitions.Def_Submission_ThreeSum_EncodedColorPipelineData
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Definitions.Def_WeightedCache3SUM_Alias_aa1db49eeb0333a7


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open EncodedColorLayout KaratsubaInterface
set_option maxHeartbeats 2400000
set_option maxRecDepth 13000
namespace ThreeSum.EncodedColorResources
theorem _root_.solution (n : ℕ) : LightBandPrimeDepth.depth (radix n) (primeWindow n) ≤ scale n := by
  exact ((Nat.log_le_self _ _).trans (Nat.div_le_self _ _)).trans (dimensions n).2.2.2.2
end ThreeSum.EncodedColorResources
