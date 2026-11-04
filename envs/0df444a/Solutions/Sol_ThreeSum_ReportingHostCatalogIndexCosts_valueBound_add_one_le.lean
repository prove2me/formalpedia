-- Prove2me | solution 1 for ThreeSum.ReportingHostCatalogIndexCosts.valueBound_add_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:22:22.967998+00:00
-- url     : https://prove2.me/submissions/48530fe5-ce0e-48b3-b7a3-0caddc3dd63f

import Definitions.Def_Submission_ThreeSum_LightReportingSortedCatalog
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogLookup
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
import Theorems.Thm_ThreeSum_ReportingHostCatalogIndexCosts_valueBound_le

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostCatalogIndexCosts
open Light ThreeSum.LightPascal
set_option maxHeartbeats 300000
namespace ThreeSum.ReportingHostCatalogIndexCosts
theorem _root_.solution {W n : ℕ} (hn : n ≤ 2^(2*W)) :
    LightReportingCatalogLookup.valueBound W n+1 ≤ 2^(4*W+2) := by
  have hb := valueBound_le hn
  have hp : 0 < 2^(4*W+1) := Nat.two_pow_pos _
  calc
    _ ≤ 2^(4*W+1)+2^(4*W+1) := by omega
    _ = 2^(4*W+2) := by ring
end ThreeSum.ReportingHostCatalogIndexCosts
