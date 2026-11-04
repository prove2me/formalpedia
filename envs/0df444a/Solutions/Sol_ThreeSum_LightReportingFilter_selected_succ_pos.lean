-- Prove2me | solution 1 for ThreeSum.LightReportingFilter.selected_succ_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:42:10.371967+00:00
-- url     : https://prove2.me/submissions/5b60e37f-28f9-408a-99a1-b6cfb0acd49d

import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightReportingFilter
import Theorems.Thm_ThreeSum_LightReportingFilter_selected_zero
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


attribute [local simp] ThreeSum.LightReportingFilter.selected_zero

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingFilter
open Light
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightReportingFilter
theorem _root_.solution (count : ℕ → ℕ) (j : ℕ) (hj : 0 < count j) :
    selected count (j+1) = selected count j ++ [j] := by
  simp [selected,List.range_succ,List.filter_append,hj]
end ThreeSum.LightReportingFilter
