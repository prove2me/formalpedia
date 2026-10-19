-- Prove2me | solution 1 for TwoDegenerateGraphs.manuscriptHammingRadius_le_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/f6a41dfb-18e5-4c10-8cd6-c02db2d1f854

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_tau_lt_one_half
import Theorems.Thm_TwoDegenerateGraphs_manuscriptHammingRadius_le

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution (dimension : ℕ) :
    manuscriptHammingRadius dimension ≤ dimension := by
  have hradius := manuscriptHammingRadius_le dimension
  have hdimension : 0 ≤ (dimension : ℝ) := Nat.cast_nonneg dimension
  have htau := tau_lt_one_half
  have hreal :
      (manuscriptHammingRadius dimension : ℝ) ≤ (dimension : ℝ) := by
    nlinarith
  exact_mod_cast hreal
end TwoDegenerateGraphs
