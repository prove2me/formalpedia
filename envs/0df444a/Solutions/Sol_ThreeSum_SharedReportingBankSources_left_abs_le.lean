-- Prove2me | solution 1 for ThreeSum.SharedReportingBankSources.left_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:28:10.326241+00:00
-- url     : https://prove2.me/submissions/dbccff85-5cac-46b1-9987-0ed332e6f9b9

import Definitions.Def_Submission_ThreeSum_SharedReportingBankSources
import Definitions.Def_Submission_ThreeSum_SourceBandFinite
import Definitions.Def_Submission_ThreeSum_SharedReportingBankSourceBounds
import Theorems.Thm_ThreeSum_SharedReportingBankSources_source_card_le
import Theorems.Thm_ThreeSum_BlockIndexedQuery_leftSource_abs_le


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankSources
open Light SubsetAddress BlockIndexedQuery GlobalEncoding
namespace ThreeSum.SharedReportingBankSources
theorem _root_.solution (p : ℤ) (NB g i h J s : ℕ) (fB : ℕ → ℤ)
    (S : Finset (Fin (J*(512*h)))) :
    |leftSource p (SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val)
      (BlockSourceOccurrenceOrder.representative h J s) S| ≤ (g : ℤ) :=
  (leftSource_abs_le _ _ _ _ _).trans (Int.ofNat_le.mpr (source_card_le NB g i))
end ThreeSum.SharedReportingBankSources
