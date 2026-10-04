-- Prove2me | solution 2 for TaoFivePrimes.exp_sum_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T15:46:13.320274+00:00
-- url     : https://prove2.me/submissions/f3877452-50a6-4ddb-9f2e-d5019b772eb0

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Theorems.Thm_TaoFivePrimes_minor_arc_bound_theorem51
import Theorems.Thm_TaoFivePrimes_exp_sum_estimate_from_minor_arc_bound

open Finset

theorem solution (x α β : ℝ) (a : ℤ) (q q₀ : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x / 100)
    (haq : Nat.Coprime a.natAbs q)
    (hα : 4 * α = (a : ℝ) / q + β)
    (hβ : |β| ≤ 1 / (q : ℝ) ^ 2)
    (hq₀ : ∀ p ∈ q₀.primeFactors, (p : ℝ) ≤ Real.sqrt x) :
    ‖TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 q₀ x α‖ ≤
      (0.14 * x / Real.sqrt q + 0.64 * x / Real.sqrt (x / q) + 0.15 * x ^ (4 / 5 : ℝ))
        * Real.log x * (Real.log x + 11.3) :=
  TaoFivePrimes.exp_sum_estimate_from_minor_arc_bound x α β a q q₀ hx hq hqx haq hα hβ hq₀
    (fun U V hU1 hV1 hUx hVx hUV hUV2 hU40 hV40 =>
      TaoFivePrimes.minor_arc_bound_theorem51 x α β a q (by omega) haq hα hβ
        U V hU1 hV1 hUx hVx hUV hUV2 hU40 hV40)
