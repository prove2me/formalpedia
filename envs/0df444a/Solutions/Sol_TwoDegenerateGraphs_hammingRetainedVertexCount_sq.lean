-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetainedVertexCount_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/5bbfc4dc-6f66-4d06-bed0-4b9685821bef

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open Classical
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    hammingRetainedVertexCount dimension retained ^ 2 =
      ∑ first : Bool × HammingWord dimension,
        ∑ second : Bool × HammingWord dimension,
          if first ∈ retained ∧ second ∈ retained then (1 : ℝ) else 0 := by
  classical
  unfold hammingRetainedVertexCount
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  by_cases hfirst : first ∈ retained <;>
    by_cases hsecond : second ∈ retained <;>
    simp [hfirst, hsecond]
end TwoDegenerateGraphs
