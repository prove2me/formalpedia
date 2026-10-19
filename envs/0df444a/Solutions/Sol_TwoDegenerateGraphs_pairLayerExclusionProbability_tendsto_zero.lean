-- Prove2me | solution 1 for TwoDegenerateGraphs.pairLayerExclusionProbability_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/7df1c74f-3012-468c-bcd2-1fa97af88713

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_exp_neg_dimension_log_two

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (depth : ℕ) :
    Filter.Tendsto
      (fun dimension : ℕ =>
        (((2 * depth : ℕ) : ℝ)) *
          Real.exp (-(dimension : ℝ) * Real.log 2))
      Filter.atTop (nhds 0) := by
  have hgeometric :
      Filter.Tendsto
        (fun dimension : ℕ => (1 / 2 : ℝ) ^ dimension)
        Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simp_rw [exp_neg_dimension_log_two]
  simpa only [mul_zero] using
    hgeometric.const_mul (((2 * depth : ℕ) : ℝ))
end TwoDegenerateGraphs
