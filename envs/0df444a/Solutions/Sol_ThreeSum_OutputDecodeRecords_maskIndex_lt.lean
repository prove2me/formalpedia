-- Prove2me | solution 1 for ThreeSum.OutputDecodeRecords.maskIndex_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:57:51.255437+00:00
-- url     : https://prove2.me/submissions/eb6d0f4e-b9fb-40be-ab14-3f19a7e8312d

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
theorem _root_.solution (h J k j : ℕ) : maskIndex h J k j < layerCount h :=
  Nat.mod_lt _ (layerCount_pos h)
end ThreeSum.OutputDecodeRecords
