-- Prove2me | solution 1 for ThreeSum.LightRadixKeys.time_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:30:14.689839+00:00
-- url     : https://prove2.me/submissions/8c5ced0c-7798-4030-96a1-57c2044bb445

import Definitions.Def_Submission_ThreeSum_LightRadixRows
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightRadixRows_time_bound_product
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.LightRadixKeys
open Light RadixKeyLists
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
namespace ThreeSum.LightRadixKeys
theorem _root_.solution (m J : ℕ) (hm : 1 ≤ m) :
    time m J ≤ 300*(J+1)*(m^J+1) := by
  have haux : ∀ j, j ≤ J → time m j ≤ 50+j*(130*m^J+220) := by
    intro j
    induction j with
    | zero => simp [time]
    | succ j ih =>
      intro hj
      have ht := ih (by omega)
      have hr := LightRadixRows.time_bound_product m (m^j) (Nat.pow_pos (by omega))
      have hp := Nat.pow_le_pow_right hm hj
      rw [pow_succ'] at hp
      have hp' := Nat.mul_le_mul_left 130 hp
      rw [time]
      nlinarith
  have hh := haux J le_rfl
  have he : 300*(J+1)*(m^J+1) =
      50+J*(130*m^J+220)+(170*J*m^J+80*J+300*m^J+250) := by ring
  rw [he]
  omega
end ThreeSum.LightRadixKeys
