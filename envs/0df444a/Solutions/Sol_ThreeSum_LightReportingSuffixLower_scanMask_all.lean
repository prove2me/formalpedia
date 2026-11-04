-- Prove2me | solution 1 for ThreeSum.LightReportingSuffixLower.scanMask_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:34:20.402927+00:00
-- url     : https://prove2.me/submissions/702a3f5f-0ae7-4aad-8ce2-f045550012c1

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixCell
import Definitions.Def_Submission_ThreeSum_LightReportingSuffixLower

set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingSuffixLower
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open ReportingHostSuffix MaskErase
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightReportingSuffixLower
theorem _root_.solution {V : ℕ} (S : Finset (Fin V)) : scanMask S V = subsetMask S := by
  have he : S.filter (fun i => i.val < V) = S := Finset.filter_true_of_mem (fun i _ => i.isLt)
  rw [scanMask,he]
end ThreeSum.LightReportingSuffixLower
