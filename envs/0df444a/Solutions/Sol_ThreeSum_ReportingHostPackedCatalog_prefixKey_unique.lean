-- Prove2me | solution 1 for ThreeSum.ReportingHostPackedCatalog.prefixKey_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:20:31.229491+00:00
-- url     : https://prove2.me/submissions/38520289-4a8d-4cb5-ad03-6a322c48b1c5

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog
import Definitions.Def_Submission_ThreeSum_ReportingHostPackedCatalog
import Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_pairKey_injective
import Theorems.Thm_ThreeSum_LightReportingPrefixCatalog_count_eq_length
import Theorems.Thm_ThreeSum_ReportingHostPrefixOrder_maskPair_unique
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPackedCatalog
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPrefixOrder
set_option maxHeartbeats 600000
namespace ThreeSum.ReportingHostPackedCatalog
theorem _root_.solution {h J k : ℕ} (hk : k ≤ J) :
    ∀ i < LightReportingPrefixCatalog.count h k,
    ∀ j < LightReportingPrefixCatalog.count h k,
      prefixKey h J k i=prefixKey h J k j → i=j := by
  intro i hi j hj he
  have hp := pairKey_injective (subsetMask_isMask (preL h J k i)).1
    (subsetMask_isMask (preL h J k j)).1 he
  exact maskPair_unique hk (by rwa [← LightReportingPrefixCatalog.count_eq_length])
    (by rwa [← LightReportingPrefixCatalog.count_eq_length]) hp.1 hp.2
end ThreeSum.ReportingHostPackedCatalog
