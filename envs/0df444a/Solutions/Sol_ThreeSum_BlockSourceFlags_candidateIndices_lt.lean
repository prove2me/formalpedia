-- Prove2me | solution 1 for ThreeSum.BlockSourceFlags.candidateIndices_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:22:03.756838+00:00
-- url     : https://prove2.me/submissions/252d0c51-7eb5-477b-b573-7547d7987d31

import Definitions.Def_Submission_ThreeSum_BlockSourceRows
import Definitions.Def_Submission_ThreeSum_LightSourceTrim
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Definitions.Def_Submission_ThreeSum_BlockSourceFlags
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_candidateAt_lt


set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceFlags
open BlockRows BlockIndex BlockEncoding BlockCoefficientRows
open LocalHashMoments LocalCoverBounds GlobalEncoding
set_option maxHeartbeats 1200000
namespace ThreeSum.BlockSourceFlags
theorem _root_.solution {h s : ℕ} (hs : s < scheduleSize h) :
    candidateIndices h s < LightLocalCoverSchedule.rows h :=
  LightLocalCoverSchedule.candidateAt_lt h ⟨s,hs⟩
end ThreeSum.BlockSourceFlags
