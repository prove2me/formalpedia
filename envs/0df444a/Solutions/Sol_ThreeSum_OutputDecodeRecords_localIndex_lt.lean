-- Prove2me | solution 1 for ThreeSum.OutputDecodeRecords.localIndex_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:28:46.949749+00:00
-- url     : https://prove2.me/submissions/bc7cb373-c874-4770-bde5-85af20bebce3

import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
import Theorems.Thm_ThreeSum_OutputDecodeRecords_localCount_pos
import Theorems.Thm_ThreeSum_OutputDecodeOrder_indices_getD_lt


set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeRecords
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
namespace ThreeSum.OutputDecodeRecords
theorem _root_.solution {h J k j : ℕ} (hj : j < J) : localIndex h J k j < localCount h :=
  indices_getD_lt (localCount_pos h) hj
end ThreeSum.OutputDecodeRecords
