-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.linear_le_magnitude
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:25:59.775677+00:00
-- url     : https://prove2.me/submissions/e337e640-06d4-4059-a984-0a72e8f5e48d

import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBoundsScales

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Scales Light SubsetAddress SharedReportingBankLayout SharedReportingBankHeader
set_option maxHeartbeats 3000000
set_option maxRecDepth 14000
namespace ThreeSum.SharedReportingBankResourceBounds
theorem _root_.solution (n : ℕ) : 2048*(inputBits n+1) ≤ magnitude n := by
  have hh : inputBits n+1 ≤ 2^(inputBits n) := Nat.lt_two_pow_self
  calc
    _ ≤ 2048*2^(inputBits n) := Nat.mul_le_mul_left _ hh
    _ = 2^(inputBits n+11) := by rw [pow_add]; norm_num; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
end ThreeSum.SharedReportingBankResourceBounds
