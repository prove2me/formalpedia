-- Prove2me | solution 1 for ThreeSum.OutputDecodeOccurrenceCode.last_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:23:33.615537+00:00
-- url     : https://prove2.me/submissions/acbd6546-c4f4-461f-bf11-ae97c073a2db

import Definitions.Def_Submission_ThreeSum_OutputDecodeRecords
import Definitions.Def_Submission_ThreeSum_OutputDecodeOccurrenceCode

set_option autoImplicit false
open ThreeSum ThreeSum.OutputDecodeOccurrenceCode
open OutputDecodeOrder OutputDecodeRecords GlobalEncoding
set_option maxHeartbeats 1500000
namespace ThreeSum.OutputDecodeOccurrenceCode
theorem _root_.solution {T M : ℕ} (hT : 0 < T) (hM : 0 < M) (k : ℕ) :
    (k%(T*M))/M < T :=
  (Nat.div_lt_iff_lt_mul hM).mpr (Nat.mod_lt _ (Nat.mul_pos hT hM))
end ThreeSum.OutputDecodeOccurrenceCode
