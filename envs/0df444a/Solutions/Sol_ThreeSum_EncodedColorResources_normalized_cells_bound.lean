-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.normalized_cells_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:43:28.906212+00:00
-- url     : https://prove2.me/submissions/f76fe856-8289-4fb6-af63-cdeae800b89f

import Definitions.Def_Submission_ThreeSum_EncodedColorResourceScale
import Definitions.Def_Submission_ThreeSum_LightEncodedColorPrimeHost
import Definitions.Def_Submission_ThreeSum_EncodedColorPipelineData
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Theorems.Thm_ThreeSum_EncodedColorResources_scale_bounds
import Definitions.Def_WeightedCache3SUM_Alias_578316aa2eec7e02


set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorResources
open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open EncodedColorLayout KaratsubaInterface
set_option maxHeartbeats 2400000
set_option maxRecDepth 13000
namespace ThreeSum.EncodedColorResources
theorem _root_.solution (n : ℕ) :
    LightBandRawAResources.cells (inputBits n+1) n (bandSize n) ≤ 1000*(scale n)^3 := by
  have hm : SharedReportingBankResourceBounds.magnitude n+1 ≤ scale n := by unfold scale; omega
  have hn := (scale_bounds n).2.1
  apply (LightBandRawAResources.cells_bound n).trans
  unfold LightBandRawAResources.envelope LightBandRawAResources.base
  have hh := Nat.mul_le_mul hm (Nat.pow_le_pow_left hn 2)
  nlinarith only [hh]
end ThreeSum.EncodedColorResources
