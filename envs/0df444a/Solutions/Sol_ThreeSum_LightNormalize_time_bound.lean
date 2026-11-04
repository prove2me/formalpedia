-- Prove2me | solution 1 for ThreeSum.LightNormalize.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:27:30.664254+00:00
-- url     : https://prove2.me/submissions/858db9f1-8201-4baf-8f3f-29b97d32730c

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Mathlib.Data.List.Dedup
import Definitions.Def_Submission_ThreeSum_LightNormalize

set_option autoImplicit false
open ThreeSum ThreeSum.LightNormalize
open Light
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightNormalize
theorem _root_.solution (n : ℕ) : time n ≤ 400*(n+1)*(Nat.clog 2 n+1) := by
  have hsub : n-1 ≤ n := Nat.sub_le _ _
  unfold time sortTime dedupTime
  nlinarith
end ThreeSum.LightNormalize
