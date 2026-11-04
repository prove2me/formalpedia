-- Prove2me | solution 1 for ThreeSum.ReportingHostPackedCatalog.packed_emod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:11:17.623555+00:00
-- url     : https://prove2.me/submissions/bbe54de9-54c0-48f7-ade6-026814dc797f

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixOrder
import Definitions.Def_Submission_ThreeSum_BinarySearch
import Definitions.Def_Submission_ThreeSum_LightReportingPrefixCatalog
import Definitions.Def_Submission_ThreeSum_ReportingHostPackedCatalog
import Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_packed_mod

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPackedCatalog
open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPrefixOrder
set_option maxHeartbeats 600000
namespace ThreeSum.ReportingHostPackedCatalog
theorem _root_.solution {key : ℕ → ℕ} {n i : ℕ} (hi : i < n) :
    ((packed key n i : ℕ) : ℤ)%((n+1 : ℕ) : ℤ) = (i : ℤ) := by
  exact_mod_cast packed_mod (key := key) hi
end ThreeSum.ReportingHostPackedCatalog
