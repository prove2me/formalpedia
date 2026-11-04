-- Prove2me | solution 1 for ThreeSum.LightReportingFilter.selected_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:51:29.077789+00:00
-- url     : https://prove2.me/submissions/cb8ce9e3-47e4-48ea-ab27-fb53de4840a0

import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightReportingFilter

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingFilter
open Light
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightReportingFilter
theorem _root_.solution (count : ℕ → ℕ) (j : ℕ) : (selected count j).Nodup :=
  List.nodup_range.filter _
end ThreeSum.LightReportingFilter
