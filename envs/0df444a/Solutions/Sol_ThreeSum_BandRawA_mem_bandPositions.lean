-- Prove2me | solution 1 for ThreeSum.BandRawA.mem_bandPositions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:40:24.823481+00:00
-- url     : https://prove2.me/submissions/b53bddbd-9afe-4f84-9a95-b0fa4c3d812b

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
theorem _root_.solution {n g a p : ℕ} :
    p ∈ bandPositions n g a ↔
      BandPartition.start g a ≤ p ∧ p < BandPartition.stop n g a := by
  constructor
  · intro hp
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hp
    have hj' : j < bandLength n g a := mem_range.mp hj
    unfold bandLength at hj'
    omega
  · rintro ⟨hs,he⟩
    exact mem_image.mpr ⟨p-BandPartition.start g a,
      mem_range.mpr (by unfold bandLength; omega),by omega⟩
end ThreeSum.BandRawA
