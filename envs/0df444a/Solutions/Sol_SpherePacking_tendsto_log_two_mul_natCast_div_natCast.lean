-- Prove2me | solution 1 for SpherePacking.tendsto_log_two_mul_natCast_div_natCast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/9382943e-9bbe-4795-990e-4096c529b035

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_tendsto_log_natCast_div_natCast

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open SpherePacking
noncomputable section
set_option autoImplicit false
open Filter Real
open scoped Nat Topology
namespace SpherePacking
theorem _root_.solution :
    Tendsto (fun n : ℕ =>
      Real.log (2 * (n : ℝ)) / (n : ℝ)) atTop (nhds 0) := by
  have hc := tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
  have hs := hc.add tendsto_log_natCast_div_natCast
  have heq :
      (fun n : ℕ =>
        Real.log 2 / (n : ℝ) + Real.log (n : ℝ) / (n : ℝ)) =ᶠ[atTop]
      (fun n : ℕ => Real.log (2 * (n : ℝ)) / (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    rw [Real.log_mul (by norm_num) hn', add_div]
  simpa using hs.congr' heq
end SpherePacking
