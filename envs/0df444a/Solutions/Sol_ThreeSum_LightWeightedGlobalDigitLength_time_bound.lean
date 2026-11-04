-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalDigitLength.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:27:39.236174+00:00
-- url     : https://prove2.me/submissions/e787d1a2-73c0-4940-81ba-7b2b365ebd47

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernarySignedPadding
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_Weighted_Global_LightTernaryDigitLength

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalDigitLength
open Light WeightedGlobalSignedPadding
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightWeightedGlobalDigitLength
theorem _root_.solution {b : ℕ} (hb : 1<b) (U : ℕ) :
    time b U≤20*Nat.log 2 (3*U+1)+120 := by
  have hl := Nat.lt_pow_succ_log_self (by decide : 1<(2 : ℕ)) (3*U+1)
  have hh : 4*U+1≤2^(Nat.log 2 (3*U+1)+2) := by
    rw [show Nat.log 2 (3*U+1)+2=(Nat.log 2 (3*U+1)+1)+1 by omega,pow_succ]
    omega
  have hp := Nat.pow_le_pow_left (show 2≤b by omega) (Nat.log 2 (3*U+1)+2)
  have hc : Nat.clog b (4*U+1)≤Nat.log 2 (3*U+1)+2 := Nat.clog_le_of_le_pow (hh.trans hp)
  unfold time clogTime
  omega
end ThreeSum.LightWeightedGlobalDigitLength
