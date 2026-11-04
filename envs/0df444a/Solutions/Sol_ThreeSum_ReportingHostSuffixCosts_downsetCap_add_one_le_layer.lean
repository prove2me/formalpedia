-- Prove2me | solution 1 for ThreeSum.ReportingHostSuffixCosts.downsetCap_add_one_le_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:48:13.213466+00:00
-- url     : https://prove2.me/submissions/0f7d5a21-dea4-432b-9f4a-20a6ad9a8f2d

import Definitions.Def_Submission_ThreeSum_LightReportingSuffixSetup
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffixCosts
import Theorems.Thm_ThreeSum_ReportingHostSuffixCosts_downsetCap_le_layer

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffixCosts
open ThreeSum.SubsetAddress ThreeSum.LightBlockQuery ThreeSum.BlockIndexedQuery
open scoped BigOperators
namespace ThreeSum.ReportingHostSuffixCosts
theorem _root_.solution {V cut : ℕ} (hhalf : cut ≤ V/2) :
    downsetCap V cut+1 ≤ (V+2)*V.choose cut := by
  have hcut : cut ≤ V := hhalf.trans (Nat.div_le_self _ _)
  have hp := Nat.choose_pos hcut
  have hd := downsetCap_le_layer hhalf
  have hm := Nat.mul_le_mul_right (V.choose cut) (Nat.succ_le_succ hcut)
  nlinarith
end ThreeSum.ReportingHostSuffixCosts
