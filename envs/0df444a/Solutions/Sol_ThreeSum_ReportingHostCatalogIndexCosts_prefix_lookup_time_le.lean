-- Prove2me | solution 1 for ThreeSum.ReportingHostCatalogIndexCosts.prefix_lookup_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:38:35.934771+00:00
-- url     : https://prove2.me/submissions/c1a22361-95c7-48db-aeb0-6abbb17c0cb6

import Definitions.Def_Submission_ThreeSum_LightReportingSortedCatalog
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogLookup
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
import Theorems.Thm_ThreeSum_ReportingHostCatalogIndexCosts_lookup_time_le
import Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_prefix_count_le_pow


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostCatalogIndexCosts
open Light ThreeSum.LightPascal
set_option maxHeartbeats 300000
namespace ThreeSum.ReportingHostCatalogIndexCosts
theorem _root_.solution {h J k : ℕ} (hk : k ≤ J) :
    LightReportingCatalogLookup.time (J*(512*h)) (LightReportingPrefixCatalog.count h k) ≤
      1000*(J*(512*h)+1) :=
  lookup_time_le (ReportingHostPackedCatalog.prefix_count_le_pow hk)
end ThreeSum.ReportingHostCatalogIndexCosts
