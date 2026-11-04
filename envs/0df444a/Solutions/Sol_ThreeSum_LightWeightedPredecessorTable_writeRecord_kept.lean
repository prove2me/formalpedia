-- Prove2me | solution 1 for ThreeSum.LightWeightedPredecessorTable.writeRecord_kept
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:30:25.2832+00:00
-- url     : https://prove2.me/submissions/66e06951-3d46-46de-a8d0-8c25090f0e65

import Definitions.Def_Submission_Weighted_Predecessor
import Definitions.Def_Submission_Weighted_PredecessorTable

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
namespace ThreeSum.LightWeightedPredecessorTable
theorem _root_.solution {μ : ℕ → ℤ} {dst stride n j : ℕ} {w k : ℤ} (hj : j<n) :
    KeptApart μ (writeRecord μ dst stride n j w k) dst stride n := by
  intro x hx
  unfold writeRecord
  rw [Function.update_of_ne (hx j hj).2,Function.update_of_ne (hx j hj).1]
end ThreeSum.LightWeightedPredecessorTable
