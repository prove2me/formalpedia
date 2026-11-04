-- Prove2me | solution 1 for ThreeSum.LightTernarySignedMatrix.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:25:30.936402+00:00
-- url     : https://prove2.me/submissions/581a0241-3622-43e3-841f-b04d84285cfe

import Definitions.Def_Submission_ThreeSum_LightTernarySignedRow
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernarySignedMatrix
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernarySignedMatrix
theorem _root_.solution (n J U : ℕ) :
    time n J U ≤ 600*n*(J+1)*(Nat.log 2 (3*U+1)+2)+20 := by
  have hlog : 2 ≤ Nat.log 2 (3*U+1)+2 := by omega
  have hlogJ := Nat.mul_le_mul_left J hlog
  have hrow : LightTernarySignedRow.time J (3*U)+200 ≤
      600*(J+1)*(Nat.log 2 (3*U+1)+2) := by
    unfold LightTernarySignedRow.time LightOutputDecodeDigits.time LightOutputDecodeDivide.budget
    nlinarith
  have hh := Nat.mul_le_mul_left n hrow
  unfold time
  nlinarith
end ThreeSum.LightTernarySignedMatrix
