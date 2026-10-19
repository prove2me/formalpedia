-- Prove2me | solution 1 for SpherePacking.scaled_log_factorial_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/78f40c40-fd94-4f9f-b015-4f10d8fcb1a3

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
theorem _root_.solution (m n : ℕ)
    (hm : m ≠ 0) (hn : n ≠ 0) :
    Real.log (m.factorial : ℝ) / (n : ℝ) -
        ((m : ℝ) / (n : ℝ)) * Real.log (n : ℝ) =
      ((m : ℝ) / (n : ℝ)) *
        (factorialLogError m + Real.log ((m : ℝ) / (n : ℝ)) - 1) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [Real.log_div hm' hn']
  unfold factorialLogError
  field_simp [hm', hn']
  ring_nf
end SpherePacking
