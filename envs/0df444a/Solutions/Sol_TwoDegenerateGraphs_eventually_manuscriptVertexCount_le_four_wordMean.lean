-- Prove2me | solution 1 for TwoDegenerateGraphs.eventually_manuscriptVertexCount_le_four_wordMean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/41f5753a-4def-4f7f-b027-5ea4e3b37539

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionProbability_mul_wordCount_tendsto_atTop
import Theorems.Thm_TwoDegenerateGraphs_manuscriptVertexCount_le_four_wordMean

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution :
    ∀ᶠ dimension : ℕ in Filter.atTop,
      (manuscriptVertexCount dimension : ℝ) ≤
        4 * (hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
  have hlarge := Filter.tendsto_atTop.1
    hammingRetentionProbability_mul_wordCount_tendsto_atTop (1 : ℝ)
  filter_upwards [hlarge] with dimension hdimension
  exact manuscriptVertexCount_le_four_wordMean dimension hdimension
end TwoDegenerateGraphs
