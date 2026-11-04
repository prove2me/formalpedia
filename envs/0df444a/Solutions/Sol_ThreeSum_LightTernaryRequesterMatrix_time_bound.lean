-- Prove2me | solution 1 for ThreeSum.LightTernaryRequesterMatrix.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:36:26.104146+00:00
-- url     : https://prove2.me/submissions/86c112c0-bf43-4480-af81-84e402b6c8ef

import Definitions.Def_Submission_ThreeSum_LightTernaryOriginalRequester
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_LightTernaryRequesterMatrix

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryRequesterMatrix
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightTernaryRequesterMatrix
theorem _root_.solution (n Q J U : ℕ) :
    time n Q J U≤1000*n*Q*(J+1)*(Nat.log 2 (3*U+1)+2)+230*n+30 := by
  have hlog : 2≤Nat.log 2 (3*U+1)+2 := by omega
  have hrow : LightTernaryOriginalRequester.time J U+300≤
      1000*(J+1)*(Nat.log 2 (3*U+1)+2) := by
    unfold LightTernaryOriginalRequester.time LightTernarySignedRow.time
      LightOutputDecodeDigits.time LightOutputDecodeDivide.budget LightTernaryCarryApply.time LightArray.linearTime
    nlinarith
  have h := Nat.mul_le_mul_left n (Nat.mul_le_mul_left Q hrow)
  unfold time innerTime
  nlinarith
end ThreeSum.LightTernaryRequesterMatrix
