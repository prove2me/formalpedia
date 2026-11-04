-- Prove2me | solution 1 for ThreeSum.BlockSourceOccurrenceOrder.rightSource_decoded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:55:11.519365+00:00
-- url     : https://prove2.me/submissions/c1425e78-625d-4d97-9f86-88ff1d6a5838

import Definitions.Def_Submission_ThreeSum_OutputDecodeOccurrenceCode
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
import Definitions.Def_Submission_ThreeSum_BlockSourceOccurrenceOrder
import Theorems.Thm_ThreeSum_BlockSourceOccurrenceOrder_decoded_occurrences
import Theorems.Thm_ThreeSum_BlockSourceSharing_rightSource_eq_of_occurrences


set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceOccurrenceOrder
open GlobalEncoding BlockEncoding BlockCoefficientRows OutputDecodeOrder
open OutputDecodeRecords OutputDecodeOccurrenceCode GlobalKeyEnumeration
namespace ThreeSum.BlockSourceOccurrenceOrder
theorem _root_.solution {β : Type*} [Fintype β] [DecidableEq β]
    {h J k : ℕ} (P d : ℤ) (B : Finset β) (b : β → ℤ) (hk : k < localCount h^J) :
    BlockIndexedQuery.rightSource P d B b
      (representative h J (code (scheduleSize h) (layerCount h) J k)) =
    BlockIndexedQuery.rightSource P d B b ((globalRecords h J).getD k (outputDefault h J)) :=
  BlockSourceSharing.rightSource_eq_of_occurrences P d B b (decoded_occurrences hk)
end ThreeSum.BlockSourceOccurrenceOrder
