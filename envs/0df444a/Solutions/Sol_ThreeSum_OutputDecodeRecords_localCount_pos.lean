-- Prove2me | solution 1 for ThreeSum.OutputDecodeRecords.localCount_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:19:46.596203+00:00
-- url     : https://prove2.me/submissions/bf5813e7-ba1d-4be0-b677-139c32067423

import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords

set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeRecords
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
namespace ThreeSum.OutputDecodeRecords
theorem _root_.solution (h : ℕ) : 0 < localCount h := Nat.mul_pos (schedule_pos h) (layerCount_pos h)
end ThreeSum.OutputDecodeRecords
