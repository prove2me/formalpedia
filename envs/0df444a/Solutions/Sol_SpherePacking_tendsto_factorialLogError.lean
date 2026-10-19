-- Prove2me | solution 1 for SpherePacking.tendsto_factorialLogError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/e455a04d-2d4c-4b35-8ca0-10e42870f0f7

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_tendsto_log_two_mul_natCast_div_natCast
import Theorems.Thm_SpherePacking_tendsto_log_stirlingSeq_div_natCast
import Theorems.Thm_SpherePacking_factorialLogError_eq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open SpherePacking
noncomputable section
set_option autoImplicit false
open Filter Real
open scoped Nat Topology
namespace SpherePacking
theorem _root_.solution :
    Tendsto factorialLogError atTop (nhds 0) := by
  have hhalf :=
    tendsto_log_two_mul_natCast_div_natCast.const_mul (1 / 2 : ℝ)
  have hsum := tendsto_log_stirlingSeq_div_natCast.add hhalf
  have heq :
      (fun n : ℕ =>
        Real.log (Stirling.stirlingSeq n) / (n : ℝ) +
          (1 / 2 : ℝ) * (Real.log (2 * (n : ℝ)) / (n : ℝ))) =ᶠ[atTop]
        factorialLogError := by
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    rw [factorialLogError_eq n hn]
    ring
  simpa using hsum.congr' heq
end SpherePacking
