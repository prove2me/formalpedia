-- Prove2me | solution 1 for ThreeSum.SharedReportingBankHeader.done_of_after
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:25:28.058725+00:00
-- url     : https://prove2.me/submissions/6a61fa8f-88ea-43d6-bb1c-f212e1b86d07

import Definitions.Def_Submission_ThreeSum_SharedReportingBankRows
import Definitions.Def_Submission_ThreeSum_LightSwitchDepth
import Definitions.Def_Submission_ThreeSum_SharedReportingBankHeader
import Theorems.Thm_ThreeSum_SharedReportingBankHeader_levels_of_after
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankHeader
open Light GlobalEncoding SharedReportingBankRows SharedReportingBankLevels
open SharedReportingBankLayout SharedReportingBankData
set_option maxHeartbeats 1900000
namespace ThreeSum.SharedReportingBankHeader
theorem _root_.solution {μ ν : ℕ → ℤ} {record base h J K NB NC g processed low : ℕ}
    {fB fC : ℕ → ℤ} {p shift : ℤ}
    (H : Done μ record base h J K NB NC g processed fB fC p shift)
    (heq : ∀ a, low ≤ a → ν a=μ a) (hrecord : low ≤ record) (hbase : low ≤ base) :
    Done ν record base h J K NB NC g processed fB fC p shift := by
  intro s hs i hi j hj hr
  exact levels_of_after (H s hs i hi j hj hr) heq
    (hrecord.trans (Nat.le_add_right _ _)) (hbase.trans (Nat.le_add_right _ _))
end ThreeSum.SharedReportingBankHeader
