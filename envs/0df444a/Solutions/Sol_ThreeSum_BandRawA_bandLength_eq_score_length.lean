-- Prove2me | solution 1 for ThreeSum.BandRawA.bandLength_eq_score_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:05:38.208768+00:00
-- url     : https://prove2.me/submissions/45e97280-111c-46eb-a487-db149d24fcdd

import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Definitions.Def_Submission_ThreeSum_BandWeightedScore
import Definitions.Def_Submission_ThreeSum_BandRawAProduct
import Theorems.Thm_ThreeSum_BandWeightedScore_length_eq_partition


set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000
namespace ThreeSum.BandRawA
theorem _root_.solution (n g a : ℕ) :
    bandLength n g a=BandWeightedScore.length n g a :=
  (BandWeightedScore.length_eq_partition n g a).symm
end ThreeSum.BandRawA
