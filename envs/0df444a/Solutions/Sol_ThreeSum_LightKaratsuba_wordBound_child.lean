-- Prove2me | solution 1 for ThreeSum.LightKaratsuba.wordBound_child
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:16:17.373107+00:00
-- url     : https://prove2.me/submissions/19ea5b86-b94c-4ead-bc92-53d38a78b8f5

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
theorem _root_.solution (m U : ℕ) : wordBound m (2 * U) ≤ wordBound (2 * m) U := by
  unfold wordBound
  have hu : (2 * U + 1) ^ 2 ≤ (2 * (U + 1)) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  calc
    _ ≤ 128 * m ^ 3 * (2 * (U + 1)) ^ 2 := Nat.mul_le_mul_left _ hu
    _ ≤ _ := by ring_nf; omega
end ThreeSum.LightKaratsuba
