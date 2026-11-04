-- Prove2me | solution 1 for ThreeSum.LightBlockChildren.time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:04:56.347804+00:00
-- url     : https://prove2.me/submissions/db09969f-d48c-4566-a247-59ba6f3c564a

import Definitions.Def_Submission_ThreeSum_ReportingHostMasks
import Definitions.Def_Submission_ThreeSum_LightQueryEnumeration
import Definitions.Def_Submission_ThreeSum_LightReportingAffine
import Definitions.Def_Submission_ThreeSum_LightBlockChildren
import Theorems.Thm_ThreeSum_LightQueryEnumeration_time_bound
import Theorems.Thm_ThreeSum_LightQueryWeights_time_bound
import Theorems.Thm_ThreeSum_LightSubsetEnumeration_time_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockChildren
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open QueryCoordinates ReportingHostMasks
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBlockChildren
theorem _root_.solution {W c h : ℕ} (hc : c ≤ W) :
    time W c h ≤ 1600*(W+1)^2*(c.choose h+1) := by
  have he := LightQueryEnumeration.time_bound (t := h) hc
  have hpow : 1 ≤ (W+1)^2 := by nlinarith
  unfold time LightReportingAffine.time
  nlinarith
end ThreeSum.LightBlockChildren
