-- Prove2me | solution 1 for ThreeSum.ReportingHostCatalogIndexCosts.valueBound_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:16:57.966811+00:00
-- url     : https://prove2.me/submissions/4bc4a436-b8ca-4ffe-904d-64d99657f1e2

import Definitions.Def_Submission_ThreeSum_LightReportingSortedCatalog
import Definitions.Def_Submission_ThreeSum_LightReportingCatalogLookup
import Definitions.Def_Submission_ThreeSum_ReportingHostCatalogIndexCosts
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostCatalogIndexCosts
open Light ThreeSum.LightPascal
set_option maxHeartbeats 300000
namespace ThreeSum.ReportingHostCatalogIndexCosts
theorem _root_.solution {W n : ℕ} (hn : n ≤ 2^(2*W)) :
    LightReportingCatalogLookup.valueBound W n ≤ 2^(4*W+1) := by
  have hp : 0 < 2^(2*W) := Nat.two_pow_pos _
  have hn' : n+1 ≤ 2^(2*W+1) := by
    calc
      n+1 ≤ 2^(2*W)+2^(2*W) := by omega
      _ = 2^(2*W+1) := by ring
  calc
    _ ≤ 2^(2*W)*2^(2*W+1) := Nat.mul_le_mul_left _ hn'
    _ = 2^(4*W+1) := by rw [← pow_add]; congr 1; omega
end ThreeSum.ReportingHostCatalogIndexCosts
