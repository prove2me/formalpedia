-- Prove2me | solution 1 for ThreeSum.LightLocalCoverTables.Data.matrix_read
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:49:51.255938+00:00
-- url     : https://prove2.me/submissions/0d9adf97-1a49-4cc5-8c8d-684e1605999e

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
    (H : Data μ h maps hist0 hist1 matrixPtr) {j r : ℕ} (hj : j < rows h) (hr : r < cols h) :
    μ (matrixPtr+j*cols h+r) = (matrix h j r : ℤ) := (H j hj).2.2 r hr
end Data
end ThreeSum.LightLocalCoverTables
