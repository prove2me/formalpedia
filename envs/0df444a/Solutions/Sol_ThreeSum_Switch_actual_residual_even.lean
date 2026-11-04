-- Prove2me | solution 1 for ThreeSum.Switch.actual_residual_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:48:02.128674+00:00
-- url     : https://prove2.me/submissions/ef258d4b-b502-4467-9df6-1fe22c836166

import Definitions.Def_Submission_ThreeSum_BandScales
import Mathlib.Data.Finset.Max
import Definitions.Def_Submission_ThreeSum_Switch
import Theorems.Thm_ThreeSum_Scales_microSize_even


set_option autoImplicit false
open ThreeSum ThreeSum.Switch
open Set ThreeSum.Parameters ThreeSum.Scales
set_option maxHeartbeats 0
noncomputable section
namespace ThreeSum.Switch
theorem _root_.solution (n j : ℕ) : 2 ∣ residualSize n j := by
  exact dvd_mul_of_dvd_right (microSize_even (inputBits n)) _
end ThreeSum.Switch
