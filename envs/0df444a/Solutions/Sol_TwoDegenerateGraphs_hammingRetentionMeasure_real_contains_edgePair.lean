-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetentionMeasure_real_contains_edgePair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/1ed25426-9119-4d6a-aa35-6a02ec4f5b86

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_real_contains_finset

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension : ℕ)
    (firstLeft firstRight secondLeft secondRight : HammingWord dimension) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        (false, firstLeft) ∈ retained ∧
        (true, firstRight) ∈ retained ∧
        (false, secondLeft) ∈ retained ∧
        (true, secondRight) ∈ retained} =
      hammingRetentionProbability dimension ^
        (2 +
          (if firstLeft = secondLeft then 0 else 1) +
          (if firstRight = secondRight then 0 else 1)) := by
  classical
  let required : Finset (Bool × HammingWord dimension) :=
    {(false, firstLeft), (true, firstRight),
      (false, secondLeft), (true, secondRight)}
  have hevent :
      {retained : Set (Bool × HammingWord dimension) |
        (false, firstLeft) ∈ retained ∧
        (true, firstRight) ∈ retained ∧
        (false, secondLeft) ∈ retained ∧
        (true, secondRight) ∈ retained} =
      {retained : Set (Bool × HammingWord dimension) |
        ∀ vertex ∈ required, vertex ∈ retained} := by
    ext retained
    simp [required, and_left_comm]
  rw [hevent, hammingRetentionMeasure_real_contains_finset]
  by_cases hleft : firstLeft = secondLeft <;>
    by_cases hright : firstRight = secondRight
  · subst secondLeft
    subst secondRight
    simp [required]
  · subst secondLeft
    simp [required, hright]
  · subst secondRight
    simp [required, hleft]
  · simp [required, hleft, hright]
end TwoDegenerateGraphs
