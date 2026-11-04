-- Prove2me | solution 1 for ThreeSum.LightLocalCoverTables.Data.counts_read
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:08:03.252233+00:00
-- url     : https://prove2.me/submissions/c3a5d2fe-720a-4499-94a8-9c1fec678116

import Definitions.Def_Submission_ThreeSum_LightLocalCoverMatrix
import Definitions.Def_Submission_ThreeSum_LightLocalCoverSchedule
import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_LightLocalCoverTables

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverTables
open Light LocalHashMoments LocalCoverBounds GlobalEncoding LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
namespace Data
theorem _root_.solution {μ : ℕ → ℤ} {h maps hist0 hist1 matrixPtr : ℕ}
    (H : Data μ h maps hist0 hist1 matrixPtr) {j r : ℕ} (hj : j < rows h) (hr : r < localPrime h) :
    μ (hist0+j*localPrime h+r) = (LocalCoverMatrix.leftCount (candidate h j) h r : ℤ) ∧
    μ (hist1+j*localPrime h+r) = (LocalCoverMatrix.rightCount (candidate h j) h r : ℤ) :=
  (H j hj).2.1 r hr
end Data
end ThreeSum.LightLocalCoverTables
