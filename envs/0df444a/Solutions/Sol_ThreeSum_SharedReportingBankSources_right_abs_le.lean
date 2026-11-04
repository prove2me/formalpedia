-- Prove2me | solution 1 for ThreeSum.SharedReportingBankSources.right_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:28:22.15569+00:00
-- url     : https://prove2.me/submissions/476c24ae-58ed-436c-9961-960f7e776391

import Definitions.Def_Submission_ThreeSum_SharedReportingBankSources
import Definitions.Def_Submission_ThreeSum_SourceBandFinite
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSourceBounds
import Theorems.Thm_ThreeSum_SharedReportingBankSources_source_card_le
import Theorems.Thm_ThreeSum_BlockIndexedQuery_rightSource_abs_le


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankSources
open Light SubsetAddress BlockIndexedQuery GlobalEncoding
namespace ThreeSum.SharedReportingBankSources
theorem _root_.solution (p shift : ℤ) (NC g i h J s : ℕ) (fC : ℕ → ℤ)
    (S : Finset (Fin (J*(512*h)))) :
    |rightSource p shift (SourceBandPartition.source NC g i) (fun t : Fin NC => fC t.val)
      (BlockSourceOccurrenceOrder.representative h J s) S| ≤ (g : ℤ) :=
  (rightSource_abs_le _ _ _ _ _ _).trans (Int.ofNat_le.mpr (source_card_le NC g i))
end ThreeSum.SharedReportingBankSources
