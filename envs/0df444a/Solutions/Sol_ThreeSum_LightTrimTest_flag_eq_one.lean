-- Prove2me | solution 1 for ThreeSum.LightTrimTest.flag_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:34:54.553932+00:00
-- url     : https://prove2.me/submissions/4528020e-cf30-4c61-9ec7-f4f81e2a1544

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTrimTest
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
open ThreeSum ThreeSum.LightTrimTest
open Light
namespace ThreeSum.LightTrimTest
theorem _root_.solution (overlap leftCount rightCount cap : ℕ) :
    flag overlap leftCount rightCount cap=1 ↔ overlap=0 ∧ leftCount≤cap ∧ rightCount≤cap := by
  unfold flag
  split <;> simp_all
end ThreeSum.LightTrimTest
