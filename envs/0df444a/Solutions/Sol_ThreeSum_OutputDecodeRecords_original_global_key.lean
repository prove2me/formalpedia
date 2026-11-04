-- Prove2me | solution 1 for ThreeSum.OutputDecodeRecords.original_global_key
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:53:52.20708+00:00
-- url     : https://prove2.me/submissions/0e046b41-e2df-4b79-af30-7810603b0719

import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
import Theorems.Thm_P2M_ThreeSum_OutputDecodeRecords_globalRecords_length__49b1eac26ca2
import Theorems.Thm_List_getD_map_of_lt
import Theorems.Thm_ThreeSum_GlobalKeyEnumeration_globalKeys_eq_map


set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeRecords
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
namespace ThreeSum.OutputDecodeRecords
theorem _root_.solution {h J k : ℕ} (hk : k < localCount h^J) :
    (globalKeys h J).getD k 0 =
      globalKey ((globalRecords h J).getD k (outputDefault h J)) := by
  rw [globalKeys_eq_map]
  exact List.getD_map_of_lt _ (by rwa [globalRecords_length']) (outputDefault h J) 0
end ThreeSum.OutputDecodeRecords
