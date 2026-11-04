-- Prove2me | solution 1 for ThreeSum.LightKaratsuba.wordBound_ge_twice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:16:18.519722+00:00
-- url     : https://prove2.me/submissions/a99c0fe8-3346-42c1-ba01-1cc35ecc304a

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
theorem _root_.solution (n U : ℕ) (hn : 0 < n) : 2 * U ≤ wordBound n U := by
  have hn3 : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ hn
  have hu : U ≤ (U + 1) ^ 2 := by nlinarith
  have hm := Nat.mul_le_mul_left ((U + 1) ^ 2) hn3
  unfold wordBound
  nlinarith
end ThreeSum.LightKaratsuba
