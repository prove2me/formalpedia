-- Prove2me | solution 1 for ThreeSum.LightClassFilter.items_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:04:50.702486+00:00
-- url     : https://prove2.me/submissions/d4c1fe06-c1ec-4999-9638-adf940a4686a

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightClassFilter
import Theorems.Thm_ThreeSum_LightClassFilter_items_zero
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


attribute [local simp] ThreeSum.LightClassFilter.items_zero

set_option autoImplicit false
open ThreeSum ThreeSum.LightClassFilter
open Light
set_option maxHeartbeats 1200000
namespace ThreeSum.LightClassFilter
theorem _root_.solution (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) :
    items x color want scale (n+1) =
      items x color want scale n ++ (if color n = want then [scale*x n] else []) := by
  by_cases h : color n = want <;> simp [items,List.range_succ,h]
end ThreeSum.LightClassFilter
