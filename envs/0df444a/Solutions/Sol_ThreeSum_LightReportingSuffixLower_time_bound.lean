-- Prove2me | solution 1 for ThreeSum.LightReportingSuffixLower.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:57:09.353878+00:00
-- url     : https://prove2.me/submissions/b831ddbf-e8ad-4927-9db3-ef987ca449be

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCell
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixLower

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixLower
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open ReportingHostSuffix MaskErase
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightReportingSuffixLower
theorem _root_.solution {W V : ℕ} (hV : V ≤ W) : time W V ≤ 400*(W+1)^2 := by
  have hm := Nat.mul_le_mul_right (LightMaskErase.time W+100) hV
  unfold time powTableTime LightMaskErase.time at *
  nlinarith
end ThreeSum.LightReportingSuffixLower
