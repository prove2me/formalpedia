-- Prove2me | solution 1 for SpherePacking.log_add_choose_div_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/f44bd417-28bb-44a7-9e6a-c99a01ee5ad8

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open SpherePacking
noncomputable section
set_option autoImplicit false
open Filter Real
open scoped Nat Topology
namespace SpherePacking
theorem _root_.solution (a b n : ℕ) :
    Real.log (((a + b).choose a : ℝ)) / (n : ℝ) =
      Real.log ((a + b).factorial : ℝ) / (n : ℝ) -
        Real.log (a.factorial : ℝ) / (n : ℝ) -
        Real.log (b.factorial : ℝ) / (n : ℝ) := by
  rw [Nat.cast_add_choose ℝ]
  rw [Real.log_div (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  ring
end SpherePacking
