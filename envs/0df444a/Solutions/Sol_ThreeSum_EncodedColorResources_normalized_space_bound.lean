-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.normalized_space_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:52:57.03195+00:00
-- url     : https://prove2.me/submissions/2b6f2b50-8a96-4927-a36d-53776e5e814a

import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeHost
import Definitions.Def_Submission_ThreeSum_EncodedColorPipelineData
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Theorems.Thm_ThreeSum_EncodedColorResources_normalized_cells_bound
import Theorems.Thm_ThreeSum_EncodedColorPrimeCosts_space_eq
import Theorems.Thm_ThreeSum_LightBandRawAResources_space_eq


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open EncodedColorLayout KaratsubaInterface
set_option maxHeartbeats 2400000
set_option maxRecDepth 13000
namespace ThreeSum.EncodedColorResources
theorem _root_.solution (free n : ℕ) :
    LightEncodedColorNormalize.space free n ≤ free+1000*(scale n)^3+1 := by
  unfold LightEncodedColorNormalize.space
  rw [LightBandRawAResources.space_eq]
  exact Nat.add_le_add_right (Nat.add_le_add_left (normalized_cells_bound n) free) 1
end ThreeSum.EncodedColorResources
