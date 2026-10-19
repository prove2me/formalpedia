-- Prove2me | solution 1 for SpherePacking.factorialLogError_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/73014512-c04d-458c-bdc3-4e3c14234507

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
theorem _root_.solution (n : ℕ) (hn : n ≠ 0) :
    factorialLogError n =
      Real.log (Stirling.stirlingSeq n) / (n : ℝ) +
        (1 / 2 : ℝ) * Real.log (2 * (n : ℝ)) / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have he : Real.exp (1 : ℝ) ≠ 0 := (Real.exp_pos 1).ne'
  have hst := Stirling.log_stirlingSeq_formula n
  rw [Real.log_div hn' he, Real.log_exp] at hst
  have hlog : Real.log ((n : ℝ) * 2) = Real.log (2 * (n : ℝ)) := by
    rw [mul_comm]
  unfold factorialLogError
  field_simp [hn']
  nlinarith [hst, hlog]
end SpherePacking
