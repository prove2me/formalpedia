-- Prove2me | solution 2 for TaoFivePrimes.minor_arc_bound_theorem51_corrected
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T11:52:29.452611+00:00
-- url     : https://prove2.me/submissions/46ecb329-fa61-4c0f-bd00-8154d314203b

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Theorems.Thm_TaoFivePrimes_exp_sum_estimate_vaughan_modulus_two_source

open Finset

theorem solution
    (x alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (U V : ℝ) (hU1 : 1 < U) (hV1 : 1 < V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) :
    ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 2 x alpha‖ ≤
      0.5 * (x / q) * Real.log x * (Real.log (2 * U * V / q + 4) + 4)
        + 0.89 * (U * V + (5 / 2) * q) * (8 + Real.log q) * Real.log (2 * x)
      + (0.1 * x / Real.sqrt q + 0.39 * x / Real.sqrt (x / q))
          * Real.log (x / (U * V)) * Real.log (V * x / U)
      + (0.55 * x / Real.sqrt U + 1.1 * x / Real.sqrt V) * Real.log (x / U) := by
  have h := TaoFivePrimes.exp_sum_estimate_vaughan_modulus_two_source x alpha beta U V a q
    hq haq halpha hbeta hU40 hV40 hUx hVx hUV hUV2
  have hx0 : 0 < x := by linarith
  have hxl : 0 ≤ Real.log x := Real.log_nonneg (by nlinarith [hUV, hU40, hV40])
  have hV0 : 0 < Real.sqrt V := Real.sqrt_pos.mpr (by linarith)
  have hxu : (1 : ℝ) < x / U := by
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < U)]
    linarith
  have h3 : 0 ≤ (x / Real.sqrt V) * Real.log (x / U) :=
    mul_nonneg (div_nonneg hx0.le hV0.le) (Real.log_nonneg hxu.le)
  have hA1 : 0 ≤ (x / (q : ℝ)) * Real.log x :=
    mul_nonneg (div_nonneg hx0.le (by positivity)) hxl
  have hT3 : (0.1 * (x / Real.sqrt q) + 0.39 * (x / Real.sqrt (x / q)))
        * Real.log (x / (U * V)) * Real.log (V * x / U)
      = (0.1 * x / Real.sqrt q + 0.39 * x / Real.sqrt (x / q))
        * Real.log (x / (U * V)) * Real.log (V * x / U) := by
    ring
  have hkey :
      0.5 * (x / q) * Real.log x * (Real.log (2 * U * V / q + 4) + 4)
        + 0.89 * (U * V + (5 / 2) * q) * (8 + Real.log q) * Real.log (2 * x)
      + (0.1 * x / Real.sqrt q + 0.39 * x / Real.sqrt (x / q))
          * Real.log (x / (U * V)) * Real.log (V * x / U)
      + (0.55 * x / Real.sqrt U + 1.1 * x / Real.sqrt V) * Real.log (x / U)
      = (0.5 * (x / q) * Real.log x * Real.log (2 * U * V / q + 4)
        + 0.89 * (U * V + (5 / 2) * q) * (8 + Real.log q) * Real.log (2 * x)
      + (0.1 * (x / Real.sqrt q) + 0.39 * (x / Real.sqrt (x / q)))
          * Real.log (x / (U * V)) * Real.log (V * x / U)
      + (0.55 * (x / Real.sqrt U) + 0.78 * (x / Real.sqrt V)) * Real.log (x / U))
        + (2 * ((x / (q : ℝ)) * Real.log x)
          + 0.32 * ((x / Real.sqrt V) * Real.log (x / U))) := by
    rw [hT3]
    ring
  have hB : 0 ≤ 2 * ((x / (q : ℝ)) * Real.log x)
      + 0.32 * ((x / Real.sqrt V) * Real.log (x / U)) := by
    nlinarith [hA1, h3]
  rw [hkey]
  exact le_trans h (le_add_of_nonneg_right hB)
