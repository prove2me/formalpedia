-- Prove2me | solution 1 for ThreeSum.OutputDecodeRecords.original_output_mask
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:53:49.595595+00:00
-- url     : https://prove2.me/submissions/f5d4b5fc-4108-4b88-a626-dc574301f2b0

import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
import Definitions.Def_WeightedCache3SUM_Alias_70ec7e5e07019f61
import Theorems.Thm_ThreeSum_OutputDecodeRecords_localIndex_lt
import Theorems.Thm_ThreeSum_OutputDecodeRecords_maskIndex_lt
import Definitions.Def_WeightedCache3SUM_Alias_8048a511a78b5b94
import Theorems.Thm_ThreeSum_LocalMaskGraph_subsetMask_setAt


set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeRecords
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
namespace ThreeSum.OutputDecodeRecords
theorem _root_.solution {h J k : ℕ} (hk : k < localCount h^J) (j : Fin J) :
    SubsetAddress.subsetMask ((((globalRecords h J).getD k (outputDefault h J)) j).2.val) =
      LocalMaskGraph.maskAt (512*h) (2*h) (maskIndex h J k j.val) := by
  rw [global_record_block hk j,localRecords_getD (localIndex_lt j.isLt)]
  exact LocalMaskGraph.subsetMask_setAt (maskIndex_lt h J k j.val)
end ThreeSum.OutputDecodeRecords
