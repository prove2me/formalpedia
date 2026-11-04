-- Prove2me | solution 1 for ThreeSum.LightTernaryCarryCodes.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:28:11.599622+00:00
-- url     : https://prove2.me/submissions/f0b83bfb-961b-4b2a-b01d-189af42bc2e8

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
theorem _root_.solution (J : ℕ) : time J≤2000*2^J*(J+2)^2 := by
  have hlog := log_code_bound J
  have hmul := Nat.mul_le_mul_left J hlog
  have hrow : rowTime J (2^J)+100≤1000*(J+2)^2 := by
    unfold rowTime LightOutputDecodeDigits.time LightOutputDecodeDivide.budget
    nlinarith
  have hQ : 1≤2^J := Nat.one_le_pow J 2 (by decide)
  have ht := Nat.mul_le_mul_left (2^J) hrow
  have hlow : 20*J+150≤1000*(J+2)^2 := by nlinarith
  have hscale := Nat.mul_le_mul_right (1000*(J+2)^2) hQ
  unfold time tableTime LightNatPower.time
  nlinarith
end ThreeSum.LightTernaryCarryCodes
