-- Prove2me | solution 1 for ThreeSum.ThreeSumParameterResources.divisor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:10:09.2574+00:00
-- url     : https://prove2.me/submissions/d80fa83b-bd43-4da7-87bd-4935e6044527

import Definitions.Def_Submission_ThreeSum_LightParameterInit
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeResources
import Definitions.Def_Submission_ThreeSum_ThreeSumParameterResources
import Theorems.Thm_ThreeSum_EncodedColorResources_scale_bounds
import Theorems.Thm_ThreeSum_LightScales_totalSize_le_self


set_option autoImplicit false
open ThreeSum ThreeSum.ThreeSumParameterResources
open Light Scales BandScales LocalCoverBounds EncodedColorResources StageBounds
set_option maxHeartbeats 2200000
set_option maxRecDepth 14000
namespace ThreeSum.ThreeSumParameterResources
theorem _root_.solution (n : ℕ) : LightGlobalSizes.divisor (mu n) ≤ scale n := by
  have ht : mu n ≤ inputBits n := LightScales.totalSize_le_self _
  have hd := Nat.div_le_self (mu n) 20
  have hp : LightGlobalSizes.divisor (mu n) ≤ SharedReportingBankResourceBounds.magnitude n :=
    Nat.pow_le_pow_right (by decide) (by omega)
  exact hp.trans (scale_bounds n).2.2.1
end ThreeSum.ThreeSumParameterResources
