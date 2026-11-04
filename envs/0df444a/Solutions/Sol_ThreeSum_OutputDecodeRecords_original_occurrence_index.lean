-- Prove2me | solution 1 for ThreeSum.OutputDecodeRecords.original_occurrence_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:25:46.175748+00:00
-- url     : https://prove2.me/submissions/2b987e74-f698-4a5d-9d57-b5b596614acb

import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
import Definitions.Def_WeightedCache3SUM_Alias_70ec7e5e07019f61
import Theorems.Thm_ThreeSum_OutputDecodeRecords_localIndex_lt
import Definitions.Def_WeightedCache3SUM_Alias_8048a511a78b5b94

set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeRecords
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
namespace ThreeSum.OutputDecodeRecords
theorem _root_.solution {h J k : ℕ} (hk : k < localCount h^J) (j : Fin J) :
    (((globalRecords h J).getD k (outputDefault h J)) j).1.val = occurrenceIndex h J k j.val := by
  rw [global_record_block hk j,localRecords_getD (localIndex_lt j.isLt)]
  rfl
end ThreeSum.OutputDecodeRecords
