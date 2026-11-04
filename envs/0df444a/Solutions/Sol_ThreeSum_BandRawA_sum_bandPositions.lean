-- Prove2me | solution 1 for ThreeSum.BandRawA.sum_bandPositions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:54:50.675789+00:00
-- url     : https://prove2.me/submissions/415c5a53-7fdc-49be-a339-741739b80d4a

import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandRawAProduct

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000
namespace ThreeSum.BandRawA
theorem _root_.solution (F : ℕ → ℕ) (n g a : ℕ) :
    (∑ p ∈ bandPositions n g a, F p)=
      ∑ j ∈ range (bandLength n g a), F (BandPartition.start g a+j) := by
  unfold bandPositions
  exact sum_image (fun i _ j _ he => by omega)
end ThreeSum.BandRawA
