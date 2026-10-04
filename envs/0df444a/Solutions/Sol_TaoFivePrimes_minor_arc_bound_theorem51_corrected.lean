-- Prove2me | solution 1 for TaoFivePrimes.minor_arc_bound_theorem51_corrected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T16:58:46.907151+00:00
-- url     : https://prove2.me/submissions/22e5ccc9-1c6c-476b-acec-ddabea317bd3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Definitions.Def_TaoFivePrimes_Theorem51Sums
import Theorems.Thm_TaoFivePrimes_theorem51_vaughan_split
import Theorems.Thm_TaoFivePrimes_theorem51_typeI_envelope_corrected
import Theorems.Thm_TaoFivePrimes_theorem51_typeII_envelope_corrected

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
  obtain ⟨c, hc, hsplit⟩ :=
    TaoFivePrimes.theorem51_vaughan_split x alpha U V hU40 hV40 hUx hVx hUV hUV2
  have h1 := TaoFivePrimes.theorem51_typeI_envelope_corrected x alpha beta a q hq haq halpha hbeta
    U V hU40 hV40 hUx hVx hUV hUV2 c hc
  have h2 := TaoFivePrimes.theorem51_typeII_envelope_corrected x alpha beta a q hq haq halpha hbeta
    U V hU40 hV40 hUx hVx hUV hUV2
  linarith
