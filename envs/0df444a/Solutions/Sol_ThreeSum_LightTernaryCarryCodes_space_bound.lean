-- Prove2me | solution 1 for ThreeSum.LightTernaryCarryCodes.space_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:46:52.856412+00:00
-- url     : https://prove2.me/submissions/775a2104-6d20-431b-a9ac-58f3042370b4

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Theorems.Thm_ThreeSum_LightTernaryCarryCodes_log_code_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCarryCodes
open Light TernarySignedDigits
set_option maxHeartbeats 2400000
set_option maxRecDepth 9000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
namespace ThreeSum.LightTernaryCarryCodes
theorem _root_.solution (work J : ℕ) : space work (2^J)≤work+J+3 := by
  have hh := log_code_bound J
  unfold space LightOutputDecodeDigits.space
  omega
end ThreeSum.LightTernaryCarryCodes
