-- Prove2me | solution 1 for ThreeSum.OutputDecodeOccurrenceCode.source_code_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:04:30.034392+00:00
-- url     : https://prove2.me/submissions/23221d6e-7c6b-4282-bf96-649081492ebd

import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
import Definitions.Def_Submission_ThreeSum_OutputDecodeOccurrenceCode
import Theorems.Thm_ThreeSum_OutputDecodeOccurrenceCode_code_lt

set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeOccurrenceCode
open OutputDecodeOrder OutputDecodeRecords GlobalEncoding
set_option maxHeartbeats 1500000
namespace ThreeSum.OutputDecodeOccurrenceCode
theorem _root_.solution (h J k : ℕ) :
    code (scheduleSize h) (layerCount h) J k < scheduleSize h^J :=
  code_lt (schedule_pos h) (layerCount_pos h) J k
end ThreeSum.OutputDecodeOccurrenceCode
