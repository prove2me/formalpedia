-- Prove2me | solution 1 for ThreeSum.BandRawA.bandPositions_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:45:47.635111+00:00
-- url     : https://prove2.me/submissions/1689b28e-c088-4078-82ac-afbca023c04f

import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandRawAProduct
import Theorems.Thm_ThreeSum_BandRawA_mem_bandPositions

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000
namespace ThreeSum.BandRawA
theorem _root_.solution {n g a p : ℕ} (hp : p ∈ bandPositions n g a) : p < n :=
  (mem_bandPositions.mp hp).2.trans_le (BandPartition.stop_le n g a)
end ThreeSum.BandRawA
