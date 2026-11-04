-- Prove2me | solution 1 for ThreeSum.SourceBandBankLayout.baseAt_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:05:04.565235+00:00
-- url     : https://prove2.me/submissions/fbe50778-0703-40a2-92ee-dba25c70b704

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalog
import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBankLayout

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBankLayout
open Light LightBlockSourceBatchLayout GlobalEncoding BlockSourceOccurrenceOrder
namespace ThreeSum.SourceBandBankLayout
theorem _root_.solution (base h J cut : ℕ) : Monotone (baseAt base h J cut) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _
end ThreeSum.SourceBandBankLayout
