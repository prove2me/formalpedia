-- Prove2me | solution 1 for ThreeSum.LightTernaryEulerRow.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:33:23.542331+00:00
-- url     : https://prove2.me/submissions/0a5eb49a-5780-4f88-84df-cec134b35d4a

import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedSum
import Definitions.Def_Submission_ThreeSum_LightTernaryDivide
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerRow
import Theorems.Thm_ThreeSum_LightTernaryDivide_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEulerRow
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryEulerRow
theorem _root_.solution (N V : ℕ) :
    time N V ≤ 400*(N+Nat.log 2 (V+1)+3) := by
  have hd := LightTernaryDivide.time_bound V
  unfold time LightTernaryWeightedSum.time
  omega
end ThreeSum.LightTernaryEulerRow
