-- Prove2me | solution 1 for ThreeSum.LightKaratsuba.wordBound_monoU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:16:16.249579+00:00
-- url     : https://prove2.me/submissions/273189fd-c73c-41bb-973c-55065a82b99c

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
theorem _root_.solution {n U V : ℕ} (hUV : U ≤ V) : wordBound n U ≤ wordBound n V := by
  unfold wordBound
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : U + 1 ≤ V + 1) 2)
end ThreeSum.LightKaratsuba
