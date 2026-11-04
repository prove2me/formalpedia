-- Prove2me | solution 1 for ThreeSum.OutputDecodeRecords.occurrenceIndex_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:53:48.397384+00:00
-- url     : https://prove2.me/submissions/79340d6b-8e0b-42f1-b06c-3a482ff3070d

import Definitions.Def_Submission_ThreeSum_OutputDecodeOrder
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
import Theorems.Thm_ThreeSum_OutputDecodeRecords_localIndex_lt

set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeRecords
open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
namespace ThreeSum.OutputDecodeRecords
theorem _root_.solution {h J k j : ℕ} (hj : j < J) :
    occurrenceIndex h J k j < scheduleSize h :=
  (Nat.div_lt_iff_lt_mul (layerCount_pos h)).mpr (localIndex_lt hj)
end ThreeSum.OutputDecodeRecords
