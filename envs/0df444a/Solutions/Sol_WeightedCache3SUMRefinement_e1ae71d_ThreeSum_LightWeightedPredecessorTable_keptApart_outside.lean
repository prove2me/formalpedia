-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessorTable.keptApart_outside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:11:22.150536+00:00
-- url     : https://prove2.me/submissions/9f07999d-631d-41fb-86b0-fc48cbcb1b0d

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Predecessor
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_PredecessorTable

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessorTable
open Light ThreeSum.LightSubsetAddress ThreeSum.LightWeightedPredecessor
set_option maxHeartbeats 3000000
set_option maxRecDepth 24000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessorTable
theorem _root_.solution {μ ν : ℕ → ℤ} {dst stride n : ℕ}
    (hs : 0<stride) (H : KeptApart μ ν dst stride n) : SameOutside μ ν dst (2*stride*n) := by
  intro x hx
  rw [Nat.mul_assoc] at hx
  apply H
  intro j hj
  have hjn : stride*j<stride*n := Nat.mul_lt_mul_of_pos_left hj hs
  rcases hx with h | h <;> constructor <;> omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedPredecessorTable
