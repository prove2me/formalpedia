-- Prove2me | solution 1 for ThreeSum.LightSourceFlagTest.flag_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:07:22.332097+00:00
-- url     : https://prove2.me/submissions/3c11c6a2-3074-455d-8ab6-6a5e8e74df9a

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightSourceFlagTest
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
open ThreeSum ThreeSum.LightSourceFlagTest
open Light
namespace ThreeSum.LightSourceFlagTest
theorem _root_.solution (card required count cap : ℕ) :
    flag card required count cap=1 ↔ card=required ∧ count≤cap := by
  unfold flag
  split <;> simp_all
end ThreeSum.LightSourceFlagTest
