-- Prove2me | solution 1 for ThreeSum.LightTernaryPredecessorTable.keptApart_refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:37:21.752874+00:00
-- url     : https://prove2.me/submissions/9250f512-0e0b-45c3-bc09-d2cecbc50d9e

import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessor
import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessorTable

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightTernaryPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace ThreeSum.LightTernaryPredecessorTable
theorem _root_.solution (μ : ℕ → ℤ) (dst stride n : ℕ) : KeptApart μ μ dst stride n :=
  fun _ _ => rfl
end ThreeSum.LightTernaryPredecessorTable
