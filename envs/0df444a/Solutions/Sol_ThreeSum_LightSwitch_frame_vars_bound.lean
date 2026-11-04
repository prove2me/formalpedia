-- Prove2me | solution 1 for ThreeSum.LightSwitch.frame_vars_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:04:06.21984+00:00
-- url     : https://prove2.me/submissions/357ce54d-df5a-421c-84ce-5915f4759397

import Definitions.Def_Submission_ThreeSum_LightSwitchBounds
import Definitions.Def_Submission_ThreeSum_LightSwitchScalar
import Definitions.Def_Submission_ThreeSum_LightSwitch
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
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
theorem _root_.solution (hj : j ≤ J) (hq : q ≤ r) :
    ∀ i, |(frame [(J : ℤ),j,r,q]) i| ≤ ((J+r+1001 : ℕ) : ℤ) := by
  intro i
  rcases i with _ | _ | _ | _ | i <;> simp [frame] <;> omega
end ThreeSum.LightSwitch
