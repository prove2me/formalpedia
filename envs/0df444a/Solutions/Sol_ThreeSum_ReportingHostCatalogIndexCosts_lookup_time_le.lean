-- Prove2me | solution 1 for ThreeSum.ReportingHostCatalogIndexCosts.lookup_time_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:34:19.21673+00:00
-- url     : https://prove2.me/submissions/f4f349da-45dd-4a20-ac1a-c619d8872587

import Definitions.Def_Submission_ThreeSum_LightReportingSortedCatalog
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogLookup
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
import Theorems.Thm_ThreeSum_ReportingHostCatalogIndexCosts_remainder_log_le

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostCatalogIndexCosts
open Light ThreeSum.LightPascal
set_option maxHeartbeats 300000
namespace ThreeSum.ReportingHostCatalogIndexCosts
theorem _root_.solution {W n : ℕ} (hn : n ≤ 2^(2*W)) :
    LightReportingCatalogLookup.time W n ≤ 1000*(W+1) := by
  have hh := remainder_log_le hn
  unfold LightReportingCatalogLookup.time powTableTime LightBandLookup.searchTime
  omega
end ThreeSum.ReportingHostCatalogIndexCosts
