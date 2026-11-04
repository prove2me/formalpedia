-- Prove2me | solution 1 for ThreeSum.ReportingHostCatalogIndexCosts.prefix_index_setup_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:25:02.526128+00:00
-- url     : https://prove2.me/submissions/ac47e811-dca1-49dd-9609-1b239298530b

import Definitions.Def_Submission_ThreeSum_LightReportingSortedCatalog
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogLookup
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
import Theorems.Thm_ThreeSum_ReportingHostCatalogIndexCosts_index_setup_time_le
import Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_prefix_count_le_pow


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostCatalogIndexCosts
open Light ThreeSum.LightPascal
set_option maxHeartbeats 300000
namespace ThreeSum.ReportingHostCatalogIndexCosts
theorem _root_.solution {h J k : ℕ} (hk : k ≤ J) :
    LightReportingSortedCatalog.time (J*(512*h)) (LightReportingPrefixCatalog.count h k) ≤
      1000*(J*(512*h)+1)*(LightReportingPrefixCatalog.count h k+1) :=
  index_setup_time_le (ReportingHostPackedCatalog.prefix_count_le_pow hk)
end ThreeSum.ReportingHostCatalogIndexCosts
