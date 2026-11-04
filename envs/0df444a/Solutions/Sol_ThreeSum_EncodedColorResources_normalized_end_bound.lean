-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.normalized_end_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:52:58.382362+00:00
-- url     : https://prove2.me/submissions/5668150a-4b56-4f99-9fab-2d5c551ef801

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
theorem _root_.solution (free n : ℕ) : normalizedEnd free n (bandSize n) ≤ free+1000*(scale n)^3 := by
  have hh : normalizedEnd free n (bandSize n) ≤
      LightBandRawAColor.space (tables free n) (vals free n (bandSize n)) (inputBits n+1) n (bandSize n) :=
    le_max_right _ _
  rw [LightBandRawAResources.space_eq] at hh
  exact hh.trans (Nat.add_le_add_left (normalized_cells_bound n) free)
end ThreeSum.EncodedColorResources
