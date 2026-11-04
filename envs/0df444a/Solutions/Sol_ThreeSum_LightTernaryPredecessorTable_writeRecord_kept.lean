-- Prove2me | solution 1 for ThreeSum.LightTernaryPredecessorTable.writeRecord_kept
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:38:00.01937+00:00
-- url     : https://prove2.me/submissions/bd0bbf92-9fe0-4d5f-9783-ff35b5dc0d75

import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessor
import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessorTable

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightTernaryPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace ThreeSum.LightTernaryPredecessorTable
theorem _root_.solution {μ : ℕ → ℤ} {dst stride n j : ℕ} {w k : ℤ} (hj : j<n) :
    KeptApart μ (writeRecord μ dst stride n j w k) dst stride n := by
  intro x hx
  unfold writeRecord
  rw [Function.update_of_ne (hx j hj).2,Function.update_of_ne (hx j hj).1]
end ThreeSum.LightTernaryPredecessorTable
