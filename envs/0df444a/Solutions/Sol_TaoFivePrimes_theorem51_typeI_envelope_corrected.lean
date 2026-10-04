-- Prove2me | solution 1 for TaoFivePrimes.theorem51_typeI_envelope_corrected
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T17:47:50.472987+00:00
-- url     : https://prove2.me/submissions/54a0da72-08ff-4f1c-ac91-9220eb878d12

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums
import Theorems.Thm_TaoFivePrimes_theorem51_typeI_pointwise_envelope
import Theorems.Thm_TaoFivePrimes_theorem51_typeI_block_summation

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
      0.5 * (x / q) * Real.log x * (Real.log (2 * U * V / q + 4) + 4)
        + 0.89 * (U * V + (5 / 2) * q) * (8 + Real.log q) * Real.log (2 * x) := by
  have hx : (0:ℝ) < x := by nlinarith
  unfold TaoFivePrimes.theorem51TypeI
  refine TaoFivePrimes.theorem51_typeI_block_summation alpha beta a q hq haq halpha hbeta
    x U V hx hU40 hV40 hUV _ (fun d => norm_nonneg _) ?_
  intro d hd
  exact TaoFivePrimes.theorem51_typeI_pointwise_envelope x alpha U V hx hU40 hV40 hUx hVx
    hUV hUV2 c hc d hd
