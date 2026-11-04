-- Prove2me | solution 1 for ThreeSum.SourceBandPartition.source_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:54:10.013834+00:00
-- url     : https://prove2.me/submissions/693f9519-ffd8-40cf-8e4c-698052d60409

import Definitions.Def_Submission_ThreeSum_SourceBandLayout
import Definitions.Def_Submission_ThreeSum_SourceBandPartition
import Theorems.Thm_ThreeSum_SourceBandPartition_source_card
import Theorems.Thm_ThreeSum_SourceBandPartition_len_eq_zero

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPartition
open BandPartition SourceBandLayout
namespace ThreeSum.SourceBandPartition
theorem _root_.solution {n g i : ℕ} (hg : 0 < g) (hi : size n g ≤ i) : source n g i=∅ := by
  apply Finset.card_eq_zero.mp
  rw [source_card,len_eq_zero hg hi]
end ThreeSum.SourceBandPartition
