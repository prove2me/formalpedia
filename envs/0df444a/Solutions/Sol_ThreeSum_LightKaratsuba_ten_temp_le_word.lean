-- Prove2me | solution 1 for ThreeSum.LightKaratsuba.ten_temp_le_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:29:49.177878+00:00
-- url     : https://prove2.me/submissions/aee02e74-89b5-4439-b84b-4dd41b4b8cba

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba

set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial
namespace ThreeSum.LightKaratsuba
theorem _root_.solution (n U : ℕ) (hn : 0 < n) :
    10 * (4 * n * U ^ 2) ≤ wordBound n U := by
  have hn3 : n ≤ n ^ 3 := by nlinarith [Nat.one_le_pow 2 n hn]
  have hu : U ^ 2 ≤ (U + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hm := Nat.mul_le_mul hn3 hu
  unfold wordBound
  nlinarith
end ThreeSum.LightKaratsuba
