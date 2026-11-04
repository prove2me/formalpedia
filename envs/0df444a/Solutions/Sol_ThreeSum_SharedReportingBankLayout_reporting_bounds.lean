-- Prove2me | solution 1 for ThreeSum.SharedReportingBankLayout.reporting_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:20:41.699831+00:00
-- url     : https://prove2.me/submissions/40100be8-efd7-436c-b7f9-388363e95a85

import Definitions.Def_Submission_ThreeSum_SharedReportingBankData
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_SharedReportingBankLayout
import Theorems.Thm_ThreeSum_SharedReportingBankLayout_ordered
import Theorems.Thm_ThreeSum_SharedReportingBankLayout_index_end

set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankLayout
open Light SubsetAddress LightPascal LightReportingPrefixCatalog LightReportingSuffixCatalog
set_option maxHeartbeats 1400000
set_option maxRecDepth 9000
namespace ThreeSum.SharedReportingBankLayout
theorem _root_.solution {h J k base baseL baseR cut stop : ℕ}
    (t boxCut : ℕ)
    (hleft : baseL+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ base)
    (hright : baseR+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ base)
    (hcut : cut=LightBlockQuery.sourceCut h J)
    (hstop : finish base h J k boxCut ≤ stop) :
    ReportingHostLevelData.Bounds h J k (catalog base h J k boxCut t) baseL baseR stop := by
  subst cut
  have ho := ordered base h J k boxCut
  have hi := index_end base h J k boxCut
  constructor
  · exact hleft.trans (by omega)
  · exact hright.trans (by omega)
  · change index base h J k boxCut+count h k ≤ stop
    omega
  · change pointers base h k+count h k ≤ stop
    have hh : boxes base h k ≤ stop := by omega
    exact hh
  · change boxes base h k+count h k*stride ((J-k)*(512*h)) boxCut ≤ stop
    have hm : masks base h J k boxCut ≤ stop := by omega
    exact hm
end ThreeSum.SharedReportingBankLayout
