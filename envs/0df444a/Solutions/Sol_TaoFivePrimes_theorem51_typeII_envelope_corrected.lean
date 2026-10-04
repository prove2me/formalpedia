-- Prove2me | solution 1 for TaoFivePrimes.theorem51_typeII_envelope_corrected
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T17:40:32.661856+00:00
-- url     : https://prove2.me/submissions/df763d27-cb2e-4063-90fc-91d33789953e

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums
import Theorems.Thm_TaoFivePrimes_typeII_dyadic_integration
import Theorems.Thm_TaoFivePrimes_theorem51_typeII_dyadic_envelope

open Finset MeasureTheory

theorem solution
    (x alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (U V : ℝ) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    TaoFivePrimes.theorem51TypeII x alpha U V ≤
      (0.1 * x / Real.sqrt q + 0.39 * x / Real.sqrt (x / q))
          * Real.log (x / (U * V)) * Real.log (V * x / U)
        + (0.55 * x / Real.sqrt U + 1.1 * x / Real.sqrt V) * Real.log (x / U) := by
  obtain ⟨G, hG0, hGsupp, hGint, hGb, hGle⟩ :=
    TaoFivePrimes.theorem51_typeII_dyadic_envelope x alpha beta a q hq haq halpha hbeta
      U V hU40 hV40 hUx hVx hUV hUV2
  have hx : (0:ℝ) < x := by nlinarith
  have hq' : (4:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hmain := TaoFivePrimes.typeII_dyadic_integration x (q:ℝ) U V G hx hq' hU40 hV40 hUV
    hG0 hGsupp hGint hGb
  linarith
