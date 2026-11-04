-- Prove2me | solution 1 for ThreeSum.TernarySignedLayout.feature_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:25:49.516338+00:00
-- url     : https://prove2.me/submissions/2eea9fc9-d264-4c29-aa40-522efb8478b6

import Definitions.Def_Submission_ThreeSum_LightTernarySignedRow
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedLayout
open TernarySignedReduction
namespace ThreeSum.TernarySignedLayout
theorem _root_.solution {J U : ℕ} {f : Coordinate J→ℤ}
    (hf : ∀ k, |f k|≤(U : ℤ)) (i : ℕ) : |feature f i|≤(U : ℤ) := by
  unfold feature
  split_ifs <;> exact hf _
end ThreeSum.TernarySignedLayout
