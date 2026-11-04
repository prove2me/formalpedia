-- Prove2me | solution 1 for ThreeSum.ReportingHostPrefixOrder.exists_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:16:23.792428+00:00
-- url     : https://prove2.me/submissions/c60500d4-f5d5-4ae9-83d9-bb4580cfc68a

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixMasks
import Definitions.Def_Submission_ThreeSum_ReportingHostPairSegments
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Theorems.Thm_ThreeSum_ReportingHostPrefixOrder_mem_prefixes
import Theorems.Thm_ThreeSum_ReportingHostPrefixOrder_preL_get
import Theorems.Thm_ThreeSum_ReportingHostPrefixOrder_preR_get

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixOrder
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPairEnumeration
open ReportingHostPrefixMasks ReportingHostPairSegments
set_option maxHeartbeats 600000
namespace ThreeSum.ReportingHostPrefixOrder
theorem _root_.solution {h J k : ℕ} (p : Prefix h k) :
    ∃ i < (prefixes h k).length, preL h J k i = leftSet (J := J) p ∧
      preR h J k i = rightSet (J := J) p := by
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (mem_prefixes p)
  exact ⟨i,hi,by rw [preL_get hi,he],by rw [preR_get hi,he]⟩
end ThreeSum.ReportingHostPrefixOrder
