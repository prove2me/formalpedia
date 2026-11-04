-- Prove2me | solution 1 for ThreeSum.LightKaratsuba.time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:30:32.138482+00:00
-- url     : https://prove2.me/submissions/aeed1760-640a-4cea-bcce-ae96304b3011

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Theorems.Thm_ThreeSum_LightKaratsuba_time_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial
namespace ThreeSum.LightKaratsuba
theorem _root_.solution (k : ℕ) : time k ≤ 2530 * 3 ^ k :=
  (Nat.le_add_right _ _).trans (time_bound k)
end ThreeSum.LightKaratsuba
