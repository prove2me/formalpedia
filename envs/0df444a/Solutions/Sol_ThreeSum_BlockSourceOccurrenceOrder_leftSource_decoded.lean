-- Prove2me | solution 1 for ThreeSum.BlockSourceOccurrenceOrder.leftSource_decoded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:55:10.256615+00:00
-- url     : https://prove2.me/submissions/41915350-0c8b-4217-ab38-1d1b40be1cc4

import Definitions.Def_Submission_ThreeSum_OutputDecodeOccurrenceCode
import Definitions.Def_Submission_ThreeSum_BlockSourceSharing
import Definitions.Def_Submission_ThreeSum_BlockSourceOccurrenceOrder
import Theorems.Thm_ThreeSum_BlockSourceOccurrenceOrder_decoded_occurrences
import Theorems.Thm_ThreeSum_BlockSourceSharing_leftSource_eq_of_occurrences


set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceOccurrenceOrder
open GlobalEncoding BlockEncoding BlockCoefficientRows OutputDecodeOrder
open OutputDecodeRecords OutputDecodeOccurrenceCode GlobalKeyEnumeration
namespace ThreeSum.BlockSourceOccurrenceOrder
theorem _root_.solution {β : Type*} [Fintype β] [DecidableEq β]
    {h J k : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ) (hk : k < localCount h^J) :
    BlockIndexedQuery.leftSource P B b
      (representative h J (code (scheduleSize h) (layerCount h) J k)) =
    BlockIndexedQuery.leftSource P B b ((globalRecords h J).getD k (outputDefault h J)) :=
  BlockSourceSharing.leftSource_eq_of_occurrences P B b (decoded_occurrences hk)
end ThreeSum.BlockSourceOccurrenceOrder
