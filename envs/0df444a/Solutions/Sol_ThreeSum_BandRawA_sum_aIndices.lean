-- Prove2me | solution 1 for ThreeSum.BandRawA.sum_aIndices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:54:49.271728+00:00
-- url     : https://prove2.me/submissions/8e97f4af-0d93-4ed8-a564-2e8d600b9996

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
theorem _root_.solution (F : ℕ → ℕ) (n g : ℕ) (rs : List Record) (s : ℕ) :
    (∑ k ∈ aIndices n g rs s, F k)=
      ∑ j ∈ range (row n g s (rs.getD s default)).length, F (count n g rs s+j) := by
  unfold aIndices
  exact sum_image (fun i _ j _ he => by omega)
end ThreeSum.BandRawA
