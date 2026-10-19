-- Prove2me | solution 1 for TwoDegenerateGraphs.eventually_manuscriptEntropyGap_dominates_power_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/87c6926c-d54d-4c71-abb8-5d079386f591

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_exp_mul_div_nat_succ_tendsto_atTop
import Theorems.Thm_TwoDegenerateGraphs_manuscriptEntropyGap_pos

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution :
    ∀ᶠ dimension : ℕ in Filter.atTop,
      2 * (4 : ℝ) ^ manuscriptExtremalPower ≤
        Real.exp (manuscriptEntropyGap * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ) := by
  exact Filter.tendsto_atTop.1
    (exp_mul_div_nat_succ_tendsto_atTop
      manuscriptEntropyGap manuscriptEntropyGap_pos)
    (2 * (4 : ℝ) ^ manuscriptExtremalPower)
end TwoDegenerateGraphs
