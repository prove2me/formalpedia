-- Prove2me | solution 1 for ThreeSum.ReportingHostPrefixOrder.mem_prefixes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:10:06.120347+00:00
-- url     : https://prove2.me/submissions/59dc3dbc-38ca-4c66-90a1-1c03f2ab0389

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixMasks
import Definitions.Def_Submission_ThreeSum_ReportingHostPairSegments
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Theorems.Thm_ThreeSum_ReportingHostPrefixOrder_prefixes_tuple
import Theorems.Thm_ThreeSum_ReportingHostPrefixMasks_tuple_injective
import Theorems.Thm_ThreeSum_ReportingHostPrefixMasks_tuple_mem


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixOrder
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPairEnumeration
open ReportingHostPrefixMasks ReportingHostPairSegments
set_option maxHeartbeats 600000
namespace ThreeSum.ReportingHostPrefixOrder
theorem _root_.solution {h k : ℕ} (p : Prefix h k) : p ∈ prefixes h k := by
  have hm : tuple p ∈ (prefixes h k).map tuple := by
    rw [prefixes_tuple]
    exact tuple_mem p
  obtain ⟨q,hq,he⟩ := List.mem_map.mp hm
  exact (tuple_injective he) ▸ hq
end ThreeSum.ReportingHostPrefixOrder
