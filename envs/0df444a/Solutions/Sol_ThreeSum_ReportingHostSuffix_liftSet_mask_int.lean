-- Prove2me | solution 1 for ThreeSum.ReportingHostSuffix.liftSet_mask_int
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:34:55.298243+00:00
-- url     : https://prove2.me/submissions/44e74361-9465-4347-a2cc-fb100e5df18b

import Definitions.Def_Submission_ThreeSum_LightBlockBoxes
import Definitions.Def_Submission_ThreeSum_ReportingHostSuffix
import Theorems.Thm_ThreeSum_ReportingHostSuffix_liftSet_mask

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostSuffix
open Finset ThreeSum.SubsetAddress BlockIndexedQuery BlockRows BlockIndex BlockForced
open GlobalEncoding LocalCoverBounds StoredReporting LightBlockQuery
open scoped BigOperators
namespace ThreeSum.ReportingHostSuffix
theorem _root_.solution {W V offset : ℕ} (hfit : offset+V ≤ W) (S : Finset (Fin V)) :
    (subsetMask (liftSet hfit S) : ℤ) = (2^offset : ℕ)*(subsetMask S : ℤ) := by
  rw [liftSet_mask]
  push_cast
  rfl
end ThreeSum.ReportingHostSuffix
