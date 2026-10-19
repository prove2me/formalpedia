-- Prove2me | solution 1 for TwoDegenerateGraphs.manuscriptVertexCount_le_four_wordMean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/869ad57d-0150-4899-9cf9-00077b4e518e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension : ℕ)
    (hmean :
      1 ≤ hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ)) :
    (manuscriptVertexCount dimension : ℝ) ≤
      4 * (hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ)) := by
  have hargument :
      0 ≤ 3 * hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ) := by
    positivity [hammingRetentionProbability_pos dimension]
  have hceiling :
      (manuscriptVertexCount dimension : ℝ) <
        3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ) + 1 := by
    unfold manuscriptVertexCount
    exact Nat.ceil_lt_add_one hargument
  nlinarith
end TwoDegenerateGraphs
