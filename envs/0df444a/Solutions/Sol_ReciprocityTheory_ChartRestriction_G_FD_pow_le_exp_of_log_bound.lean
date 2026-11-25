-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.pow_le_exp_of_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:00:45.190573+00:00
-- url     : https://prove2.me/submissions/2e3b992a-8aa4-40b7-90fb-c3d97e68eaaa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CountingExponentialSumHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Finset
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution {K N w m : ℝ} (hK : 1 ≤ K) (hN : 1 ≤ N) (hw : 0 ≤ w)
    (hm : w + N * Real.log (2 * K * N) + N + 2 ≤ m) :
    (K * m) ^ N ≤ Real.exp (2 * m - w - 2) := by
  have hK0 : 0 < K := by linarith
  have hN0 : 0 < N := by linarith
  have hL : 0 ≤ Real.log (2 * K * N) := Real.log_nonneg (by nlinarith)
  have hNL : 0 ≤ N * Real.log (2 * K * N) := mul_nonneg hN0.le hL
  have hm0 : 0 < m := by linarith
  have hKm : 0 < K * m := mul_pos hK0 hm0
  have h1 : Real.log (K * m) = Real.log (2 * K * N) + Real.log (m / (2 * N)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have h2 : Real.log (m / (2 * N)) ≤ m / (2 * N) - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h3 : N * (m / (2 * N)) = m / 2 := by
    field_simp
  have h4 := mul_le_mul_of_nonneg_left h2 hN0.le
  rw [Real.rpow_def_of_pos hKm]
  apply Real.exp_le_exp.mpr
  rw [h1]
  nlinarith
end ReciprocityTheory.ChartRestriction.G.FD
