-- Prove2me | solution 1 for ThreeSum.LightSwitch.test_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:19:56.644258+00:00
-- url     : https://prove2.me/submissions/ba4af068-e804-4de3-a797-187a44dead5f

import Definitions.Def_Submission_ThreeSum_LightSwitchBounds
import Definitions.Def_Submission_ThreeSum_LightSwitchScalar
import Definitions.Def_Submission_ThreeSum_LightSwitch
import Theorems.Thm_ThreeSum_LightSwitch_frame_vars_bound
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Definitions.Def_WeightedCache3SUM_Alias_73a640d455410285
import Theorems.Thm_ThreeSum_Switch_mem_candidates
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.Switch.mem_candidates



set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitch
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {μ : ℕ→ℤ} {J j r q d : ℕ}
namespace ThreeSum.LightSwitch
theorem _root_.solution (hj : j ≤ J) (hq : q ≤ r)
    (hword : (word J r : ℤ) ≤ lim.word) :
    test.Safe lim ⟨frame [(J : ℤ),j,r,q],μ⟩ := by
  have hv := frame_vars_bound hj hq
  have hB : 2 ≤ J+r+1001 := by omega
  unfold test Cond.Safe
  constructor
  · apply LightSwitchScalar.scalar_safe hB _ hv
      _ (by simp [LightSwitchScalar.Small])
    exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by omega)
      (by decide : (k 10 *' (v 0 -' v 1) *'
        (v 3 *' (k 799 *' v 2 *' v 2 +' v 3 *' (k 72 *' v 2 +' k 24 *' v 3)))).cost ≤ 64))).trans hword
  · apply LightSwitchScalar.scalar_safe hB _ hv
      _ (by simp [LightSwitchScalar.Small])
    exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by omega)
      (by decide : ((k 291 *' v 0 +' k 1000 *' v 1) *' v 2 *' v 2 *' v 2).cost ≤ 64))).trans hword
end ThreeSum.LightSwitch
