-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.prime_address_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:16:07.715726+00:00
-- url     : https://prove2.me/submissions/4fd6725c-edcd-4d3a-9e38-54a300c5abd9

import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeHost
import Definitions.Def_Submission_ThreeSum_EncodedColorPipelineData
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Theorems.Thm_ThreeSum_EncodedColorResources_normalized_end_bound

set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open EncodedColorLayout KaratsubaInterface
set_option maxHeartbeats 2400000
set_option maxRecDepth 13000
namespace ThreeSum.EncodedColorResources
theorem _root_.solution (free n : ℕ) : prime free n (bandSize n) ≤ free+1000*(scale n)^3+1 :=
  Nat.add_le_add_right (normalized_end_bound free n) 1
end ThreeSum.EncodedColorResources
