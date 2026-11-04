-- Prove2me | solution 1 for ThreeSum.OutputDecodeRecords.globalRecords_getD_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:03:59.787701+00:00
-- url     : https://prove2.me/submissions/2629df20-34fa-451e-bc21-ac824d0772e6

import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
import Theorems.Thm_ThreeSum_OutputDecodeRecords_globalRecords_map_ofFn
import Theorems.Thm_P2M_ThreeSum_OutputDecodeRecords_globalRecords_length__49b1eac26ca2
import Theorems.Thm_List_getD_map_of_lt


set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeRecords
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
namespace ThreeSum.OutputDecodeRecords
theorem _root_.solution {h J k : ℕ} (hk : k < localCount h^J) :
    List.ofFn ((globalRecords h J).getD k (outputDefault h J)) =
      (tuples (localRecords h) J).getD k [] := by
  have hi : k < (globalRecords h J).length := by rwa [globalRecords_length']
  have he := List.getD_map_of_lt (fun q : GlobalOutput h J => List.ofFn q) hi (outputDefault h J) []
  rw [globalRecords_map_ofFn] at he
  exact he.symm
end ThreeSum.OutputDecodeRecords
