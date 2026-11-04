-- Prove2me | solution 1 for ThreeSum.LightReportingFilter.selected_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:34:53.536882+00:00
-- url     : https://prove2.me/submissions/08099b18-6e4a-4f2e-b496-5adeb435276c

import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightReportingFilter

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingFilter
open Light
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightReportingFilter
theorem _root_.solution (count : ℕ → ℕ) (j : ℕ) : (selected count j).length ≤ j := by
  exact (List.length_filter_le _ _).trans_eq List.length_range
end ThreeSum.LightReportingFilter
