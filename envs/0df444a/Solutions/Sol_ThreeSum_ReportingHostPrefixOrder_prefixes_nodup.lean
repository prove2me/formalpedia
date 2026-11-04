-- Prove2me | solution 1 for ThreeSum.ReportingHostPrefixOrder.prefixes_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:09:36.34275+00:00
-- url     : https://prove2.me/submissions/fa8c8e6e-00cf-423c-a46f-ba63d2cff425

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixMasks
import Definitions.Def_Submission_ThreeSum_ReportingHostPairSegments
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Theorems.Thm_ThreeSum_ReportingHostPrefixOrder_prefixes_tuple
import Definitions.Def_WeightedCache3SUM_Alias_03e0bdb6c4745899
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_pairs_nodup


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixOrder
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPairEnumeration
open ReportingHostPrefixMasks ReportingHostPairSegments
set_option maxHeartbeats 600000
namespace ThreeSum.ReportingHostPrefixOrder
theorem _root_.solution (h k : ℕ) : (prefixes h k).Nodup := by
  apply List.Nodup.of_map
  rw [prefixes_tuple]
  exact RadixKeyLists.tuples_nodup _ (pairs_nodup _ _) _
end ThreeSum.ReportingHostPrefixOrder
