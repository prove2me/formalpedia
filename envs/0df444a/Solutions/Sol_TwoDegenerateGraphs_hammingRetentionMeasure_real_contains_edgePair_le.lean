-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetentionMeasure_real_contains_edgePair_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/1e6dad37-b6aa-4c5b-89c4-65f4205fccac

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_real_contains_edgePair

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
        (true, secondRight) ∈ retained} ≤
      hammingRetentionProbability dimension ^ 4 +
        (if firstLeft = secondLeft then
          hammingRetentionProbability dimension ^ 3 else 0) +
        (if firstRight = secondRight then
          hammingRetentionProbability dimension ^ 3 else 0) +
        (if firstLeft = secondLeft ∧ firstRight = secondRight then
          hammingRetentionProbability dimension ^ 2 else 0) := by
  rw [hammingRetentionMeasure_real_contains_edgePair]
  have hnonnegative := (hammingRetentionProbability_pos dimension).le
  by_cases hleft : firstLeft = secondLeft <;>
    by_cases hright : firstRight = secondRight <;>
    simp only [hleft, hright, ↓reduceIte, add_zero, Nat.reduceAdd,
      and_self, and_false, and_true, le_add_iff_nonneg_left, ge_iff_le,
      Std.le_refl] <;>
    positivity
end TwoDegenerateGraphs
