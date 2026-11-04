-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.count_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:32:02.763812+00:00
-- url     : https://prove2.me/submissions/93b7e7f0-9e6b-40a0-8223-401291310014

import Definitions.Def_Submission_ThreeSum_SharedReportingBankCosts
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBounds
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_levels_le
import Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_prefix_count_le_pow


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Light SubsetAddress SharedReportingBankLayout SharedReportingBankLevels
open SharedReportingBankHeader SharedReportingBankRows
set_option maxHeartbeats 2800000
set_option maxRecDepth 14000
namespace ThreeSum.SharedReportingBankResourceBounds
theorem _root_.solution {h J k : ℕ} (hk : k ≤ levels J) :
    LightReportingPrefixCatalog.count h k ≤ prefixCount h J :=
  ReportingHostPackedCatalog.prefix_count_le_pow (hk.trans (levels_le J))
end ThreeSum.SharedReportingBankResourceBounds
