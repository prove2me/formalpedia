-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.primitive_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:26:06.671548+00:00
-- url     : https://prove2.me/submissions/7fa5d5b6-2d04-4cd2-8731-b1158e357c32

import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsScales
import Theorems.Thm_ThreeSum_LightScales_blockCount_le
import Theorems.Thm_ThreeSum_LightScales_microHalf_le_self
import Theorems.Thm_ThreeSum_LightScales_totalSize_le_self


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Scales Light SubsetAddress SharedReportingBankLayout SharedReportingBankHeader
set_option maxHeartbeats 3000000
set_option maxRecDepth 14000
namespace ThreeSum.SharedReportingBankResourceBounds
theorem _root_.solution (n : ℕ) :
    half n ≤ inputBits n ∧ blocks n ≤ 20*inputBits n ∧
    2*half n*blocks n ≤ inputBits n ∧
    width (half n) (blocks n) ≤ 256*inputBits n := by
  have hh := LightScales.microHalf_le_self (inputBits n)
  have hj := LightScales.blockCount_le (inputBits n)
  have ht := LightScales.totalSize_le_self (inputBits n)
  change blocks n*(2*half n) ≤ inputBits n at ht
  refine ⟨hh,hj,by nlinarith,?_⟩
  unfold width localWidth
  nlinarith
end ThreeSum.SharedReportingBankResourceBounds
