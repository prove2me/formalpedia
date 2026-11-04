-- Prove2me | solution 1 for ThreeSum.LightClassFilter.items_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:26:05.941746+00:00
-- url     : https://prove2.me/submissions/d30a64ed-5ab7-444d-9b94-b9806cfbc96a

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightClassFilter
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast



set_option autoImplicit false
open ThreeSum ThreeSum.LightClassFilter
open Light
set_option maxHeartbeats 1200000
namespace ThreeSum.LightClassFilter
theorem _root_.solution (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) :
    items x color want scale 0 = [] := by simp [items]
end ThreeSum.LightClassFilter
