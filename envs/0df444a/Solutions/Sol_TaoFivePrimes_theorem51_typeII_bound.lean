-- Prove2me | solution 1 for TaoFivePrimes.theorem51_typeII_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-12T18:22:29.115889+00:00
-- url     : https://prove2.me/submissions/13a21c90-5dd8-416e-82bb-7dc312825516

import Theorems.Thm_TaoFivePrimes_theorem51_scale_bound_signed
import Theorems.Thm_TaoFivePrimes_theorem51_typeII_of_scale_bound
import Mathlib

theorem solution
    (x alpha beta U V : ℝ) (a : ℤ) (q : ℕ)
    (hq : 4 ≤ q) (haq : Nat.Coprime a.natAbs q) (haunit : a.natAbs = 1)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2)
    (hUVq : U * V < (q : ℝ) - 1) :
    TaoFivePrimes.theorem51TypeII x alpha U V ≤
      (0.1 * (x / Real.sqrt q) + 0.39 * (x / Real.sqrt (x / q))) *
        Real.log (x / (U * V)) * Real.log (V * x / U) +
      (0.55 * (x / Real.sqrt U) + 0.78 * (x / Real.sqrt V)) *
        Real.log (x / U) := by
  apply TaoFivePrimes.theorem51_typeII_of_scale_bound x alpha beta U V a q
    hq haq haunit halpha hbeta hU40 hV40 hUx hVx hUV hUV2 hUVq
  intro W hVW hWU
  have hU : 0 < U := by linarith
  have hW : 0 < W := by linarith
  have hq100 : 100 ≤ q := by
    have hprod : 1600 ≤ U * V := by nlinarith
    have hreal : (100 : ℝ) ≤ q := by linarith
    exact_mod_cast hreal
  have hxW : 40 ≤ x / W := by
    apply (le_div_iff₀ hW).mpr
    have hh := (le_div_iff₀ hU).mp hWU
    nlinarith
  exact TaoFivePrimes.theorem51_scale_bound_signed x alpha beta U V W a q
    hq100 (by linarith) hxW haunit halpha hbeta
