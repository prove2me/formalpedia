-- Prove2me | solution 1 for TwoDegenerateGraphs.manuscriptVertexCount_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/d5022285-2a92-4fb4-b8f6-3db8492b0f8f

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionProbability_mul_wordCount_tendsto_atTop

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution :
    Filter.Tendsto manuscriptVertexCount Filter.atTop Filter.atTop := by
  have hscaled :
      Filter.Tendsto
        (fun dimension : ℕ =>
          3 * (hammingRetentionProbability dimension *
            ((2 ^ dimension : ℕ) : ℝ)))
        Filter.atTop Filter.atTop :=
    hammingRetentionProbability_mul_wordCount_tendsto_atTop.const_mul_atTop
      (by norm_num)
  have hceiling := tendsto_nat_ceil_atTop.comp hscaled
  apply hceiling.congr'
  filter_upwards [] with dimension
  change
    ⌈3 * (hammingRetentionProbability dimension *
      ((2 ^ dimension : ℕ) : ℝ))⌉₊ =
      manuscriptVertexCount dimension
  unfold manuscriptVertexCount
  congr 1
  ring
end TwoDegenerateGraphs
