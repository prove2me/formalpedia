-- Prove2me | solution 1 for SpherePacking.tendsto_log_stirlingSeq_div_natCast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/60eea659-5bb0-43d9-9b4d-eb3187bc7e00

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
theorem _root_.solution :
    Tendsto
      (fun n : ℕ => Real.log (Stirling.stirlingSeq n) / (n : ℝ))
      atTop (nhds 0) := by
  have hlog :
      Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n))
        atTop (nhds (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log (by positivity)).tendsto.comp
      Stirling.tendsto_stirlingSeq_sqrt_pi
  have hinv := tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)
  simpa [div_eq_mul_inv] using hlog.mul hinv
end SpherePacking
