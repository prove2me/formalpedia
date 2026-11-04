-- Prove2me | solution 1 for ThreeSum.LightMinimum.least_lt_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:32:50.869566+00:00
-- url     : https://prove2.me/submissions/f0cdd135-8e20-4103-802a-426f067c974c

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_Balancing
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Theorems.Thm_ThreeSum_LightMinimum_least_lt
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
open ThreeSum ThreeSum.LightMinimum
open Light
namespace ThreeSum.LightMinimum
theorem _root_.solution (f : ℕ → ℤ) {j n : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    least f j < n := by
  by_cases h : j = 0
  · simp [h, least, hn]
  · exact (least_lt f (by omega)).trans_le hj
end ThreeSum.LightMinimum
