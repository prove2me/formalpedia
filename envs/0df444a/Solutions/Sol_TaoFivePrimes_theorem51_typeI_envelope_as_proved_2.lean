-- Prove2me | solution 2 for TaoFivePrimes.theorem51_typeI_envelope_as_proved
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-18T11:43:14.996001+00:00
-- url     : https://prove2.me/submissions/ac058566-fea6-4b0c-9568-8b0989bbf6cf

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums
import Theorems.Thm_TaoFivePrimes_theorem51_typeI_envelope_corrected

open Finset

theorem solution
    (x alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (U V : ℝ) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (c : ℕ → ℂ) (hc : ∀ d ∈ TaoFivePrimes.theorem51Divisors U V, ‖c d‖ ≤ 1) :
    TaoFivePrimes.theorem51TypeI x alpha U V c ≤
      (x / q) * Real.log x * (Real.log (2 * U * V / q + 4) + 4)
        + 1.78 * (U * V + (5 / 2) * q) * (8 + Real.log q) * Real.log (2 * x) := by
  have h := TaoFivePrimes.theorem51_typeI_envelope_corrected x alpha beta a q hq haq
    halpha hbeta U V hU40 hV40 hUx hVx hUV hUV2 c hc
  have h1 : 0 ≤ (x / q) * Real.log x * (Real.log (2 * U * V / q + 4) + 4) := by
    have hxq : 0 ≤ x / (q : ℝ) := div_nonneg (by linarith) (by positivity)
    have hl0 : 0 ≤ Real.log x := Real.log_nonneg (by nlinarith [hUV, hU40, hV40])
    have harg : 0 ≤ Real.log (2 * U * V / (q : ℝ) + 4) + 4 := by
      have hd : 0 ≤ 2 * U * V / (q : ℝ) := div_nonneg (by positivity) (by positivity)
      have : (1 : ℝ) ≤ 2 * U * V / (q : ℝ) + 4 := by linarith
      linarith [Real.log_nonneg this]
    positivity
  have h2 : 0 ≤ (U * V + (5 / 2) * (q : ℝ)) * (8 + Real.log (q : ℝ)) * Real.log (2 * x) := by
    have h8 : 0 ≤ 8 + Real.log (q : ℝ) := by
      have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
      linarith [Real.log_nonneg hq1]
    have hl2 : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by nlinarith [hUV, hU40, hV40])
    have huv : 0 ≤ U * V + (5 / 2) * (q : ℝ) := by
      have huvnn : 0 ≤ U * V := by nlinarith
      have hqnn : (0 : ℝ) ≤ (q : ℝ) := by positivity
      linarith
    positivity
  linarith
