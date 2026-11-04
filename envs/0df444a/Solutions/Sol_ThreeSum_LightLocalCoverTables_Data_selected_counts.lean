-- Prove2me | solution 1 for ThreeSum.LightLocalCoverTables.Data.selected_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:56:27.743057+00:00
-- url     : https://prove2.me/submissions/a2ad43d3-82bf-4f01-8a54-2b50f72d3ca0

import Definitions.Def_Submission_ThreeSum_LightLocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_LightLocalCoverTables
import Theorems.Thm_ThreeSum_LightLocalCoverTables_Data_counts_read
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_candidateAt_lt
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_leftCount_candidateAt
import Theorems.Thm_ThreeSum_LightLocalCoverSchedule_rightCount_candidateAt


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverTables
open Light LocalHashMoments LocalCoverBounds GlobalEncoding LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
namespace Data
theorem _root_.solution {μ : ℕ → ℤ} {h maps hist0 hist1 matrixPtr : ℕ}
    (H : Data μ h maps hist0 hist1 matrixPtr) (s : Occurrence h) {r : ℕ} (hr : r < localPrime h) :
    μ (hist0+candidateAt h s*localPrime h+r) =
      (HashFamily.bucketSize (LocalGraph.leftVertices (512*h) h) (mapAt h s) (r : LocalField h) : ℤ) ∧
    μ (hist1+candidateAt h s*localPrime h+r) =
      (HashFamily.bucketSize (LocalGraph.rightVertices (512*h) h) (mapAt h s) (r : LocalField h) : ℤ) := by
  have hc := H.counts_read (candidateAt_lt h s) hr
  rw [leftCount_candidateAt h s hr,rightCount_candidateAt h s hr] at hc
  exact hc
end Data
end ThreeSum.LightLocalCoverTables
