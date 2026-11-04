-- Prove2me | solution 1 for ThreeSum.LightTernarySignedMatrix.row_keep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:26:01.372873+00:00
-- url     : https://prove2.me/submissions/a687c963-5248-4b86-9692-67352a01a64a

import Definitions.Def_Submission_ThreeSum_LightTernarySignedRow
import Definitions.Def_Submission_ThreeSum_LightTernarySignedMatrix

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernarySignedMatrix
open Light TernarySignedDigits TernarySignedReduction
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
namespace ThreeSum.LightTernarySignedMatrix
theorem _root_.solution {μ ν : ℕ → ℤ} {a dst J : ℕ} {f : Coordinate J → ℤ}
    (hrow : LightTernarySignedRow.Row μ a J f) (hkeep : Kept μ ν dst)
    (hsep : a+J+2 ≤ dst) : LightTernarySignedRow.Row ν a J f := by
  rcases hrow with ⟨hd,h0,h1⟩
  refine ⟨?_,(hkeep _ (by omega)).trans h0,(hkeep _ (by omega)).trans h1⟩
  intro j
  exact (hkeep _ (by omega)).trans (hd j)
end ThreeSum.LightTernarySignedMatrix
