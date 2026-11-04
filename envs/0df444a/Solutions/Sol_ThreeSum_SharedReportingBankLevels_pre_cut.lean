-- Prove2me | solution 1 for ThreeSum.SharedReportingBankLevels.pre_cut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:38:11.291946+00:00
-- url     : https://prove2.me/submissions/2167e2ae-abcd-490d-9e34-eb3b68a3a3e8

import Definitions.Def_Submission_ThreeSum_SharedReportingBankMemory
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLevels
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_boxCut_le

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLevels
open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1400000
namespace ThreeSum.SharedReportingBankLevels
theorem _root_.solution {h J k : ℕ} (hk : k ≤ J) : k*h+boxCut h J k ≤ 2*h*J := by
  have hc := boxCut_le h J k
  have hd := Nat.sub_add_cancel hk
  unfold residual at hc
  nlinarith
end ThreeSum.SharedReportingBankLevels
