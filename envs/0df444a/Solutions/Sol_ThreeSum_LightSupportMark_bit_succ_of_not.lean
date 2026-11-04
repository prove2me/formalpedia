-- Prove2me | solution 1 for ThreeSum.LightSupportMark.bit_succ_of_not
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:45:25.206732+00:00
-- url     : https://prove2.me/submissions/05a7863a-1cfa-44ac-bd86-01b3330ef9c5

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Finset.Range
import Definitions.Def_Submission_ThreeSum_LightSupportMark
import Theorems.Thm_ThreeSum_LightSupportMark_hit_succ
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
open ThreeSum ThreeSum.LightSupportMark
open Light Finset
namespace ThreeSum.LightSupportMark
theorem _root_.solution (key valid : ℕ → ℕ) (r i : ℕ)
    (h : ¬(valid i=1 ∧ key i=r)) : bit key valid r (i+1) = bit key valid r i := by
  unfold bit
  by_cases hh : Hit key valid r i
  · have hn : Hit key valid r (i+1) := (hit_succ key valid r i).mpr (Or.inl hh)
    simp only [if_pos hh,if_pos hn]
  · have hn : ¬Hit key valid r (i+1) := by
      intro hi
      rcases (hit_succ key valid r i).mp hi with hi | hi
      · exact hh hi
      · exact h hi
    simp only [if_neg hh,if_neg hn]
end ThreeSum.LightSupportMark
