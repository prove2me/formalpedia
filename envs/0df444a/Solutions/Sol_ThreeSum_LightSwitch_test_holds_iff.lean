-- Prove2me | solution 1 for ThreeSum.LightSwitch.test_holds_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:04:07.500798+00:00
-- url     : https://prove2.me/submissions/9d6d5c23-c2e0-48cf-9b2c-ca6f8dbdabc4

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
theorem _root_.solution (hj : j ≤ J) :
    test.Holds ⟨frame [(J : ℤ),j,r,q],μ⟩ ↔ factor J j*cubic r q < left J j r := by
  simp only [test,Cond.Holds,Expr.val,Op.eval,frame,List.getD_cons_zero,
    List.getD_cons_succ,Nat.cast_add,Nat.cast_ofNat]
  unfold factor cubic left
  exact_mod_cast (Iff.rfl :
    10*(J-j)*(q*(799*r*r+q*(72*r+24*q))) < (291*J+1000*j)*r*r*r ↔
    10*(J-j)*(q*(799*r*r+q*(72*r+24*q))) < (291*J+1000*j)*r*r*r)
end ThreeSum.LightSwitch
