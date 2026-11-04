-- Prove2me | solution 1 for ThreeSum.BandRawA.row_position_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:50:45.677274+00:00
-- url     : https://prove2.me/submissions/5ca75757-563c-4c55-a615-f7a4733ac33c

import Definitions.Def_Submission_ThreeSum_LightBandRawARow
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Theorems.Thm_ThreeSum_BandRawA_row_length


set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open Light BandCandidateRows
set_option maxHeartbeats 1400000
namespace ThreeSum.BandRawA
theorem _root_.solution {n g owner j : ℕ} {r : Record}
    (hj : j < (row n g owner r).length) : BandPartition.start g r.a+j < n := by
  rw [row_length] at hj
  split_ifs at hj with hf
  · have hh := BandPartition.stop_le n g r.a
    unfold bandLength at hj
    omega
  · omega
end ThreeSum.BandRawA
