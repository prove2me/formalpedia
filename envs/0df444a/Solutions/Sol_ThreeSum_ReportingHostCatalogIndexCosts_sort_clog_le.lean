-- Prove2me | solution 1 for ThreeSum.ReportingHostCatalogIndexCosts.sort_clog_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:16:42.556802+00:00
-- url     : https://prove2.me/submissions/a80ca296-35d8-4d2c-ba61-d59529b56a1c

import Definitions.Def_Submission_ThreeSum_LightReportingSortedCatalog
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogLookup
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostCatalogIndexCosts
open Light ThreeSum.LightPascal
set_option maxHeartbeats 300000
namespace ThreeSum.ReportingHostCatalogIndexCosts
theorem _root_.solution {W n : ℕ} (hn : n ≤ 2^(2*W)) : Nat.clog 2 n ≤ 2*W :=
  Nat.clog_le_of_le_pow hn
end ThreeSum.ReportingHostCatalogIndexCosts
