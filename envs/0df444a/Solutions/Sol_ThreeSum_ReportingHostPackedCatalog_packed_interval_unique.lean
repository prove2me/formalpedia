-- Prove2me | solution 1 for ThreeSum.ReportingHostPackedCatalog.packed_interval_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:09:37.88619+00:00
-- url     : https://prove2.me/submissions/1975eebe-819b-49ef-a672-ab2a63efc5ec

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog
import Definitions.Def_Submission_ThreeSum_ReportingHostPackedCatalog

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPackedCatalog
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPrefixOrder
set_option maxHeartbeats 600000
namespace ThreeSum.ReportingHostPackedCatalog
theorem _root_.solution {key : ℕ → ℕ} {n i j : ℕ}
    (hi : i < n) (hj : j < n)
    (hunique : ∀ a < n, ∀ b < n, key a=key b → a=b)
    (hlo : packed key n i ≤ packed key n j)
    (hhi : packed key n j ≤ key i*(n+1)+n) : i=j := by
  have hle : key i ≤ key j := by
    by_contra hh
    have hh' : key j+1 ≤ key i := by omega
    unfold packed at hlo
    nlinarith
  have hge : key j ≤ key i := by
    by_contra hh
    have hh' : key i+1 ≤ key j := by omega
    unfold packed at hhi
    nlinarith
  exact hunique i hi j hj (Nat.le_antisymm hle hge)
end ThreeSum.ReportingHostPackedCatalog
