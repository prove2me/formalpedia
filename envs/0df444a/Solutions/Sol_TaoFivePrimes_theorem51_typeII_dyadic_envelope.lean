-- Prove2me | solution 1 for TaoFivePrimes.theorem51_typeII_dyadic_envelope
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T20:57:38.457207+00:00
-- url     : https://prove2.me/submissions/7c6b725a-b535-4653-8e94-19aeada398a1

import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51Sums
import Theorems.Thm_TaoFivePrimes_theorem51_typeII_dyadic_representation
import Theorems.Thm_TaoFivePrimes_theorem51_typeII_dyadic_block_bound

open MeasureTheory

theorem solution
    (x alpha beta : ℝ) (a : ℤ) (q : ℕ) (hq : 4 ≤ q)
    (haq : Nat.Coprime a.natAbs q)
    (halpha : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (U V : ℝ) (hU40 : 40 ≤ U) (hV40 : 40 ≤ V) (hUx : U < x) (hVx : V < x)
    (hUV : U * V ≤ x / 4) (hUV2 : x ≤ U * V ^ 2) :
    ∃ G : ℝ → ℝ,
      (∀ W, 0 ≤ G W) ∧
      (∀ W, W ∉ Set.Icc V (x / U) → G W = 0) ∧
      MeasureTheory.IntegrableOn (fun W => G W / W) (Set.Ioi 0) ∧
      (∀ W ∈ Set.Icc V (x / U),
        G W ≤ (1.1 / 8) * ((1 / (2 * Real.sqrt 2)) * (x / Real.sqrt (q : ℝ))
              + (1 / 2) * Real.sqrt (x * W) + x / Real.sqrt W
              + Real.sqrt 2 * Real.sqrt (x * (q : ℝ))) * Real.log W) ∧
      TaoFivePrimes.theorem51TypeII x alpha U V ≤ 4 * ∫ W in Set.Ioi (0:ℝ), G W / W := by
  have hx : (0:ℝ) < x := by nlinarith
  obtain ⟨hsupp, hint, hle⟩ :=
    TaoFivePrimes.theorem51_typeII_dyadic_representation x alpha U V hx hU40 hV40 hUx hVx
      hUV hUV2
  refine ⟨fun W => ‖∑' d : ℕ, ∑' w : ℕ,
            (if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
                ∧ x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W
                ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)
                * ((TaoFivePrimes.theorem51Centered V w : ℝ) : ℂ)
                * TaoFivePrimes.expCircle (alpha * d * w)
            else 0)‖, fun W => norm_nonneg _, hsupp, hint, ?_, hle⟩
  intro W hW
  exact TaoFivePrimes.theorem51_typeII_dyadic_block_bound x alpha beta a q hq haq halpha hbeta
    U V hU40 hV40 hUx hVx hUV hUV2 W hW
