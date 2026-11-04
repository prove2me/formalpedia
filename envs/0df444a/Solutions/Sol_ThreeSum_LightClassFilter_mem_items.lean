-- Prove2me | solution 1 for ThreeSum.LightClassFilter.mem_items
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:29:50.23387+00:00
-- url     : https://prove2.me/submissions/b2f6e085-5e57-469e-9ee5-b1d64ce22de9

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
theorem _root_.solution (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) (z : ℤ) :
    z ∈ items x color want scale n ↔ ∃ i, i < n ∧ color i = want ∧ scale*x i = z := by
  simp [items,and_assoc]
end ThreeSum.LightClassFilter
