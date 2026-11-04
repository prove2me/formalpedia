-- Prove2me | solution 1 for ThreeSum.SharedReportingBankLayout.downset_scratch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:20:17.254191+00:00
-- url     : https://prove2.me/submissions/644a1295-abc1-48ff-9297-c3aca02d56cb

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout
import Theorems.Thm_ThreeSum_SharedReportingBankLayout_ordered
import Theorems.Thm_ThreeSum_SharedReportingBankLayout_table_scratch

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLayout
open Light SubsetAddress LightPascal LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 1400000
set_option maxRecDepth 9000
namespace ThreeSum.SharedReportingBankLayout
theorem _root_.solution {h J k : ℕ} (hk : k ≤ J) (base boxCut : ℕ) :
    base+tableSize ((J-k)*(512*h))+((J-k)*(512*h)+1) ≤ finish base h J k boxCut := by
  have hV : (J-k)*(512*h) ≤ J*(512*h) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have htable : tableSize ((J-k)*(512*h)) ≤ tableSize (J*(512*h)) := by
    exact Nat.pow_le_pow_left (Nat.add_le_add_right hV 1) 2
  have ho := ordered base h J k boxCut
  have hs := table_scratch base h J k boxCut
  omega
end ThreeSum.SharedReportingBankLayout
