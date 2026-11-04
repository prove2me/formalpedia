-- Prove2me | solution 1 for ThreeSum.OutputDecodeRecords.source_occurrence_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:53:50.770199+00:00
-- url     : https://prove2.me/submissions/dfe72036-bb7c-4d27-8673-82ab5861d4a2

import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
import Theorems.Thm_ThreeSum_OutputDecodeRecords_original_occurrence_index
import Theorems.Thm_ThreeSum_BlockCoefficientRows_occurrenceIndices_fin
attribute [local simp] ThreeSum.BlockCoefficientRows.occurrenceIndices_fin



set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeRecords
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
namespace ThreeSum.OutputDecodeRecords
theorem _root_.solution {h J k j : ℕ} (hk : k < localCount h^J) (hj : j < J) :
    BlockCoefficientRows.occurrenceIndices
      (BlockEncoding.outputOccurrences ((globalRecords h J).getD k (outputDefault h J))) j =
        occurrenceIndex h J k j := by
  rw [BlockCoefficientRows.occurrenceIndices_fin _ ⟨j,hj⟩]
  exact original_occurrence_index hk ⟨j,hj⟩
end ThreeSum.OutputDecodeRecords
