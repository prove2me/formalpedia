-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingBall_card_ge_boundary_binomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/2ac79d80-a739-4f9c-b6b5-c48d239087a1

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingBall_card

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension radius : ℕ)
    (word : HammingWord dimension) :
    dimension.choose radius ≤ (hammingBall dimension radius word).card := by
  rw [hammingBall_card]
  apply Finset.single_le_sum
    (s := Finset.range (radius + 1))
    (f := fun distance => dimension.choose distance)
  · intro distance _
    exact Nat.zero_le _
  · simp
end TwoDegenerateGraphs
