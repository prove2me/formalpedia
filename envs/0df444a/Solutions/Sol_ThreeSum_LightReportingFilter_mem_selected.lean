-- Prove2me | solution 1 for ThreeSum.LightReportingFilter.mem_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:33:21.366201+00:00
-- url     : https://prove2.me/submissions/09fd7b8d-89b5-4f55-83ed-c94190678817

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
theorem _root_.solution (count : ℕ → ℕ) (j i : ℕ) :
    i ∈ selected count j ↔ i < j ∧ 0 < count i := by
  simp [selected]
end ThreeSum.LightReportingFilter
