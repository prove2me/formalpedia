-- Prove2me | solution 1 for ThreeSum.ThreeSumParameterResources.global_word_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:28:46.327945+00:00
-- url     : https://prove2.me/submissions/d181fe5a-c691-494d-ba3c-713324994f66

import Definitions.Def_Submission_ThreeSum_LightParameterInit
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Definitions.Def_Submission_ThreeSum_ThreeSumParameterResources
import Theorems.Thm_ThreeSum_ThreeSumParameterResources_local_output_power_le
import Theorems.Thm_ThreeSum_ThreeSumParameterResources_divisor_le
import Definitions.Def_WeightedCache3SUM_Alias_aa1db49eeb0333a7
import Theorems.Thm_ThreeSum_EncodedColorResources_layer_le
import Theorems.Thm_ThreeSum_EncodedColorResources_local_bounds
import Theorems.Thm_ThreeSum_EncodedColorResources_scale_bounds


set_option autoImplicit false
open ThreeSum ThreeSum.ThreeSumParameterResources
open Light Scales BandScales LocalCoverBounds EncodedColorResources StageBounds
set_option maxHeartbeats 2200000
set_option maxRecDepth 14000
namespace ThreeSum.ThreeSumParameterResources
theorem _root_.solution (n : ℕ) :
    LightGlobalSizes.word (LightGlobalSizes.localCount n) (localRadix n)
      (blockCount (inputBits n)) (mu n) ≤ 8000*scale n := by
  have hS : 1 ≤ scale n := by have hh := (scale_bounds n).1; omega
  have hC : LightGlobalSizes.localCount n ≤ scale n := layer_le n
  have hp : localRadix n ≤ scale n := by
    have hh := (local_bounds n).prime
    change localRadix n+1 ≤ scale n at hh
    omega
  have hJ : blockCount (inputBits n)+1 ≤ scale n := (dimensions n).2.1
  have hmu : mu n+1 ≤ scale n := (dimensions n).2.2.1
  have hCP := local_output_power_le n
  have hPP : localRadix n^(blockCount (inputBits n)) ≤ scale n := (dimensions n).2.2.2.2
  have hd := divisor_le n
  unfold LightGlobalSizes.word
  omega
end ThreeSum.ThreeSumParameterResources
