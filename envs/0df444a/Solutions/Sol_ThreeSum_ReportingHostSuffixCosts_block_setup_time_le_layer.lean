-- Prove2me | solution 1 for ThreeSum.ReportingHostSuffixCosts.block_setup_time_le_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:41:52.543709+00:00
-- url     : https://prove2.me/submissions/21636d6c-6704-4063-be74-ac711ce6e2de

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
import Theorems.Thm_ThreeSum_ReportingHostSuffixCosts_setup_time_le_layer
import Theorems.Thm_ThreeSum_ReportingHostSuffixCosts_suffix_width_eq

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffixCosts
open ThreeSum.SubsetAddress ThreeSum.LightBlockQuery ThreeSum.BlockIndexedQuery
open scoped BigOperators
namespace ThreeSum.ReportingHostSuffixCosts
theorem _root_.solution {h J k cut : ℕ} (hk : k ≤ J)
    (hcut : cut ≤ residualSize h J k) :
    LightReportingSuffixSetup.time (width h J) (suffixStage J (512*h) k) cut (k*(512*h)) ≤
      40000*(width h J+1)^5*(256*residualSize h J k).choose cut := by
  have hhalf : cut ≤ suffixStage J (512*h) k/2 := by
    rw [suffix_width_eq]
    omega
  calc
    _ ≤ 40000*(width h J+1)^5*(suffixStage J (512*h) k).choose cut :=
      setup_time_le_layer (W := width h J) (V := suffixStage J (512*h) k)
        (offset := k*(512*h)) (ReportingHostSuffix.block_fit hk) hhalf
    _ = _ := by rw [suffix_width_eq]
end ThreeSum.ReportingHostSuffixCosts
