-- Prove2me | solution 1 for ThreeSum.BandRawA.mem_aIndices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:41:05.665466+00:00
-- url     : https://prove2.me/submissions/7f01d10f-ec2f-4c71-a80a-06e584833f8c

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
theorem _root_.solution {n g s k : ℕ} {rs : List Record} :
    k ∈ aIndices n g rs s ↔
      ∃ j < (row n g s (rs.getD s default)).length, k=count n g rs s+j := by
  constructor
  · intro hk
    obtain ⟨j,hj,he⟩ := mem_image.mp hk
    exact ⟨j,mem_range.mp hj,he.symm⟩
  · rintro ⟨j,hj,he⟩
    exact mem_image.mpr ⟨j,mem_range.mpr hj,he.symm⟩
end ThreeSum.BandRawA
