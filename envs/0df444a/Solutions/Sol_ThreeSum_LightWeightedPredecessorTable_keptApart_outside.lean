-- Prove2me | solution 1 for ThreeSum.LightWeightedPredecessorTable.keptApart_outside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:30:26.445543+00:00
-- url     : https://prove2.me/submissions/a4d66444-c313-440d-8966-2b68412246d7

import Definitions.Def_Submission_Weighted_Predecessor
import Definitions.Def_Submission_Weighted_PredecessorTable

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
namespace ThreeSum.LightWeightedPredecessorTable
theorem _root_.solution {μ ν : ℕ → ℤ} {dst stride n : ℕ}
    (hs : 0<stride) (H : KeptApart μ ν dst stride n) : SameOutside μ ν dst (2*stride*n) := by
  intro x hx
  rw [Nat.mul_assoc] at hx
  apply H
  intro j hj
  have hjn : stride*j<stride*n := Nat.mul_lt_mul_of_pos_left hj hs
  rcases hx with h | h <;> constructor <;> omega
end ThreeSum.LightWeightedPredecessorTable
