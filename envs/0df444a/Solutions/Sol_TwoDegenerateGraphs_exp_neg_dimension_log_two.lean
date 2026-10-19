-- Prove2me | solution 1 for TwoDegenerateGraphs.exp_neg_dimension_log_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/4eb304ec-dd52-491e-8fca-64b29d69fdb2

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (dimension : ℕ) :
    Real.exp (-(dimension : ℝ) * Real.log 2) =
      ((1 / 2 : ℝ) ^ dimension) := by
  calc
    Real.exp (-(dimension : ℝ) * Real.log 2) =
        Real.exp (-((dimension : ℝ) * Real.log 2)) := by
          congr 1
          ring
    _ = (Real.exp ((dimension : ℝ) * Real.log 2))⁻¹ :=
      Real.exp_neg _
    _ = ((2 : ℝ) ^ dimension)⁻¹ := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    _ = ((1 / 2 : ℝ) ^ dimension) := by
      rw [← inv_pow]
      norm_num
end TwoDegenerateGraphs
