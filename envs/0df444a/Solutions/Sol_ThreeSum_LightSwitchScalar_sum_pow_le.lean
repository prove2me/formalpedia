-- Prove2me | solution 1 for ThreeSum.LightSwitchScalar.sum_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:04:04.985998+00:00
-- url     : https://prove2.me/submissions/f29eb8df-72cc-41c4-b7fb-7cc060025143

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightSwitchScalar

set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitchScalar
open Light
set_option maxHeartbeats 1600000
namespace ThreeSum.LightSwitchScalar
theorem _root_.solution {B : ℕ} (hB : 2 ≤ B) (a b : ℕ) :
    B^a+B^b ≤ B^(a+b+1) := by
  have ha : B^a ≤ B^(a+b) := Nat.pow_le_pow_right (by omega) (by omega)
  have hb : B^b ≤ B^(a+b) := Nat.pow_le_pow_right (by omega) (by omega)
  calc
    _ ≤ B^(a+b)+B^(a+b) := Nat.add_le_add ha hb
    _ = B^(a+b)*2 := by ring
    _ ≤ B^(a+b)*B := Nat.mul_le_mul_left _ hB
    _ = _ := by rw [pow_succ]
end ThreeSum.LightSwitchScalar
