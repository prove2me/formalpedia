-- Prove2me | solution 1 for ThreeSum.LightTernaryWeightedSum.sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:30:46.873243+00:00
-- url     : https://prove2.me/submissions/3efb31d5-1746-445f-b5a3-3d0d1f0c8283

import Definitions.Def_Submission_ThreeSum_LightLookupSum
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedSum
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
open ThreeSum ThreeSum.LightTernaryWeightedSum
open Light Finset
namespace ThreeSum.LightTernaryWeightedSum
theorem _root_.solution (weights keys : ℕ → ℕ) (f : ℕ → ℤ) : sum weights keys f 0 = 0 := by
  simp [sum]
end ThreeSum.LightTernaryWeightedSum
