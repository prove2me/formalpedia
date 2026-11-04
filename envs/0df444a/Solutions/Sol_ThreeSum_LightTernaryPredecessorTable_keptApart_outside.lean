-- Prove2me | solution 1 for ThreeSum.LightTernaryPredecessorTable.keptApart_outside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:38:01.4112+00:00
-- url     : https://prove2.me/submissions/4837f43a-5ae0-4629-ba31-3ad0e36dab29

import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessor
import Definitions.Def_Submission_ThreeSum_LightTernaryPredecessorTable

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightTernaryPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace ThreeSum.LightTernaryPredecessorTable
theorem _root_.solution {μ ν : ℕ → ℤ} {dst stride n : ℕ}
    (hs : 0<stride) (H : KeptApart μ ν dst stride n) : SameOutside μ ν dst (2*stride*n) := by
  intro x hx
  rw [Nat.mul_assoc] at hx
  apply H
  intro j hj
  have hjn : stride*j<stride*n := Nat.mul_lt_mul_of_pos_left hj hs
  rcases hx with h | h <;> constructor <;> omega
end ThreeSum.LightTernaryPredecessorTable
