-- Prove2me | solution 1 for ThreeSum.ReportingHostPackedCatalog.sorted_getD_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:06:30.538486+00:00
-- url     : https://prove2.me/submissions/86209539-87b0-4572-806c-955c7fadceb3

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog
import Definitions.Def_Submission_ThreeSum_ReportingHostPackedCatalog

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPackedCatalog
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPrefixOrder
set_option maxHeartbeats 600000
namespace ThreeSum.ReportingHostPackedCatalog
theorem _root_.solution {S : List ℤ} (hs : S.Pairwise (· ≤ ·)) :
    ∀ i j, i ≤ j → j < S.length → S.getD i 0 ≤ S.getD j 0 := by
  intro i j hij hj
  by_cases he : i=j
  · subst j; exact le_rfl
  · rw [List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ hj]
    exact List.pairwise_iff_getElem.mp hs i j (by omega) hj (by omega)
end ThreeSum.ReportingHostPackedCatalog
