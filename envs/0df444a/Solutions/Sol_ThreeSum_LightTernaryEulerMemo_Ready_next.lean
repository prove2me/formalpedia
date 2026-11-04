-- Prove2me | solution 1 for ThreeSum.LightTernaryEulerMemo.Ready.next
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:03:41.581169+00:00
-- url     : https://prove2.me/submissions/d19b3d3e-d6a3-4f35-9057-95606e5efbee

import Definitions.Def_Submission_ThreeSum_LightTernaryEulerScan
import Definitions.Def_Submission_ThreeSum_LightTernaryEulerMemo
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightTernaryEulerScan_stageValue_below
import Theorems.Thm_ThreeSum_LightTernaryWeightedSum_sum_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightTernaryWeightedSum.sum_zero



set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryEulerMemo
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
namespace ThreeSum.LightTernaryEulerMemo
namespace Ready
theorem _root_.solution {μ ν ξ : ℕ → ℤ} {f : ℕ → ℤ} {rank : ℕ → ℕ}
    {vals rows T fr stage : ℕ} (H : Ready μ ν f rank vals rows T stage)
    (hvals : vals+rows ≤ fr)
    (hs : LightTernaryEulerScan.Stored ν ξ f rank vals (T+stage+1) fr rows) :
    Ready μ ξ f rank vals rows T (stage+1) := by
  constructor
  · intro a ha
    rw [hs a (by omega),LightTernaryEulerScan.stageValue_below ν f rank ha]
    exact H.1 a ha
  · intro j hj hr
    rw [hs (vals+j) (by omega)]
    by_cases hc : rank j=T+stage+1
    · simp [LightTernaryEulerScan.stageValue,hc,hj]
    · have hp : rank j≤T+stage := by omega
      simpa [LightTernaryEulerScan.stageValue,hc] using H.2 j hj hp
end Ready
end ThreeSum.LightTernaryEulerMemo
