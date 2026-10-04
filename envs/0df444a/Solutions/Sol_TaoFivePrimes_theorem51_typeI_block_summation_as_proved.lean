-- Prove2me | solution 1 for TaoFivePrimes.theorem51_typeI_block_summation_as_proved
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T18:35:44.284237+00:00
-- url     : https://prove2.me/submissions/5f46a9e2-adfd-4467-b072-c4c1daabf500
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums
import Theorems.Thm_TaoFivePrimes_vinogradov_lemma_if_form
import Theorems.Thm_TaoFivePrimes_theorem51_typeI_block_summation_from_vinogradov

open Finset

theorem solution
    (alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q) (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (x U V : ℝ) (hx : 0 < x) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUV : U * V ≤ x / 4)
    (W : ℕ → ℝ) (hW0 : ∀ d, 0 ≤ W d)
    (hWb : ∀ d ∈ TaoFivePrimes.theorem51Divisors U V,
        W d ≤ (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then
                  (1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)
                else min ((1 / 2) * (x / (d : ℝ)) * Real.log x
                    + 4 * Real.log 2 * Real.log (2 * x))
                  (4 * Real.log 2 * Real.log (2 * x)
                    / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|))) :
    (∑ d ∈ TaoFivePrimes.theorem51Divisors U V, W d)
      ≤ (x / q) * Real.log x * (Real.log (2 * U * V / q + 4) + 4)
        + 1.78 * (U * V + (5 / 2) * q) * (8 + Real.log q) * Real.log (2 * x) := by
  have hx6400 : (6400:ℝ) ≤ x := by nlinarith
  have hB0 : (0:ℝ) ≤ 4 * Real.log 2 * Real.log (2 * x) := by
    have h1 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h2 : (0:ℝ) ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
    positivity
  exact TaoFivePrimes.theorem51_typeI_block_summation_from_vinogradov alpha beta a q hq haq
    halpha hbeta x U V hx hU40 hV40 hUV
    (fun A' alpha' beta' theta' u v a' hA' h1 h2 h3 =>
      TaoFivePrimes.vinogradov_lemma_if_form (4 * Real.log 2 * Real.log (2 * x)) hB0 q
        (by omega) A' alpha' beta' theta' u v a' hA' h1 h2 h3)
    W hW0 hWb
