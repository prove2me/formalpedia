-- Prove2me | solution 1 for ThreeSum.LightMinimum.least_value_le_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:17:05.791952+00:00
-- url     : https://prove2.me/submissions/c82d5e09-c899-426d-8392-306f8eb71ee2

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_Balancing
import Definitions.Def_Submission_ThreeSum_LightMinimum
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
theorem _root_.solution (f : ℕ → ℤ) (n i : ℕ) (hi : i < n) :
    f (least f n) ≤ f i := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h : f n < f (least f n)
      · rw [least, if_pos h]
        by_cases hin : i < n
        · exact h.le.trans (ih hin)
        · have he : i = n := by omega
          simp [he]
      · rw [least, if_neg h]
        by_cases hin : i < n
        · exact ih hin
        · have he : i = n := by omega
          simpa only [he] using le_of_not_gt h
end ThreeSum.LightMinimum
