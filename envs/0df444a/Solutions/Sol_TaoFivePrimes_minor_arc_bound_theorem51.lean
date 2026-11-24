-- Prove2me | solution 1 for TaoFivePrimes.minor_arc_bound_theorem51
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T11:52:28.869441+00:00
-- url     : https://prove2.me/submissions/9f7b588c-d554-4b8e-aa05-9c85cf13337b

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
      0.5 * (x / q) * Real.log x * Real.log (2 * U * V / q + 4)
        + 0.89 * (U * V + (5 / 2) * q) * (8 + Real.log q) * Real.log (2 * x)
      + (0.1 * x / Real.sqrt q + 0.39 * x / Real.sqrt (x / q))
          * Real.log (x / (U * V)) * Real.log (V * x / U)
      + (0.55 * x / Real.sqrt U + 0.78 * x / Real.sqrt V) * Real.log (x / U) := by
  convert TaoFivePrimes.exp_sum_estimate_vaughan_modulus_two_source x alpha beta U V a q
    hq haq halpha hbeta hU40 hV40 hUx hVx hUV hUV2 using 1
  ring
