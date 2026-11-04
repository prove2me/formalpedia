-- Prove2me | solution 1 for ThreeSum.ReportingHostCatalogIndexCosts.remainder_log_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:29:01.088207+00:00
-- url     : https://prove2.me/submissions/db9aae49-0e7b-4b0b-a555-da8f66fe9c82

import Definitions.Def_Submission_ThreeSum_LightReportingSortedCatalog
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogLookup
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
import Theorems.Thm_ThreeSum_ReportingHostCatalogIndexCosts_valueBound_add_one_le

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostCatalogIndexCosts
open Light ThreeSum.LightPascal
set_option maxHeartbeats 300000
namespace ThreeSum.ReportingHostCatalogIndexCosts
theorem _root_.solution {W n : ℕ} (hn : n ≤ 2^(2*W)) :
    Nat.log 2 (LightReportingCatalogLookup.valueBound W n+1) ≤ 4*W+2 :=
  (Nat.log_le_clog _ _).trans (Nat.clog_le_of_le_pow (valueBound_add_one_le hn))
end ThreeSum.ReportingHostCatalogIndexCosts
