-- Prove2me | solution 1 for ThreeSum.LightRadixKeys.space_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:21:25.462191+00:00
-- url     : https://prove2.me/submissions/a5924f22-77e1-4ae9-a739-5a4f5b9cd425

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
theorem _root_.solution (dst m J : ℕ) (hm : 1 ≤ m) :
    space dst m J ≤ dst+(J+1)*(m^J+1) := by
  have haux : ∀ j, j ≤ J → offset m j ≤ j*(m^J+1) := by
    intro j
    induction j with
    | zero => simp [offset]
    | succ j ih =>
      intro hj
      have hh := ih (by omega)
      have hp := Nat.pow_le_pow_right hm (show j ≤ J by omega)
      rw [offset]
      nlinarith
  have hh := haux J le_rfl
  unfold space
  nlinarith
end ThreeSum.LightRadixKeys
