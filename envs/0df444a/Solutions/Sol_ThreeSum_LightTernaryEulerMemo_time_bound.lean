-- Prove2me | solution 1 for ThreeSum.LightTernaryEulerMemo.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:41:37.266282+00:00
-- url     : https://prove2.me/submissions/15893931-7d76-4610-8027-6a125d2eeeee

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerScan
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Theorems.Thm_ThreeSum_LightTernaryDivide_time_bound
import Theorems.Thm_ThreeSum_LightTernaryEulerRow_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEulerMemo
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryEulerMemo
theorem _root_.solution (N rows stages V : ℕ) :
    time N rows stages V ≤
      (stages+1)*(rows+1)*(400*(N+Nat.log 2 (V+1)+3)+500) := by
  have hrow := LightTernaryEulerRow.time_bound N V
  let K := N+Nat.log 2 (V+1)+3
  have hbound : LightTernaryEulerRow.time N V ≤ 400*K := hrow
  unfold time LightTernaryEulerScan.time LightTernaryEulerRow.fillTime
  calc
    _ ≤ stages*(rows*(400*K+250)+250)+100 := by
      have hb : LightTernaryEulerRow.time N V+100+150 ≤ 400*K+250 := by omega
      have hm := Nat.mul_le_mul_left rows hb
      have hs : rows*(LightTernaryEulerRow.time N V+100+150)+100+150 ≤
          rows*(400*K+250)+250 := by omega
      exact Nat.add_le_add_right (Nat.mul_le_mul_left stages hs) 100
    _ ≤ (stages+1)*(rows+1)*(400*K+500) := by
      nlinarith
    _ = _ := rfl
end ThreeSum.LightTernaryEulerMemo
