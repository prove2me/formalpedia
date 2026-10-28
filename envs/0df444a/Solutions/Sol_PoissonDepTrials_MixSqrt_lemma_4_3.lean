-- Prove2me | solution 1 for PoissonDepTrials.MixSqrt.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:02:43.011387+00:00
-- url     : https://prove2.me/submissions/f7e0878b-3568-405b-a94a-6b45bb64689f

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting
import Theorems.Thm_PoissonDepTrials_MixInv_lemma_4_3


open MeasureTheory ProbabilityTheory
open PoissonDepTrials.MixSqrt


/-- Chen (1975), Lemma 4.3, p. 539, (4.5). Let `X_1, X_2, …` be a real sequence satisfying (4.1), and
`Y, T, Z` real random variables measurable `ℳ_{ab}, ℳ_{cd}, ℳ_{ee'}` with `c − b ≥ m`, `e − d ≥ m`.
For bounded Borel `g : ℝ → ℝ` and `f : ℝ² → ℝ`,
`|Ef(Y, Z)g(T) − Ef(Y, Z)Eg(T)| ≤ 4φ(m)‖f‖E|g(T)| + 2φ(m)‖g‖E|f(Y, Z')|`, where `Z'` is an independent
copy of `Z`, so `E|f(Y, Z')|` is the integral of `|f|` against the product of the laws of `Y`
and `Z`. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ)
    (m : ℕ) (hm : 1 ≤ m) (a b c d e e' : ℕ) (ha : 1 ≤ a) (hbc : b + m ≤ c) (hde : d + m ≤ e)
    (Y T Z : Ω → ℝ) (hY : Measurable[sigmaIcc X a b] Y) (hT : Measurable[sigmaIcc X c d] T)
    (hZ : Measurable[sigmaIcc X e e'] Z)
    (g : ℝ → ℝ) (hg : Measurable g) (Mg : ℝ) (hMg : ∀ x, |g x| ≤ Mg)
    (f : ℝ × ℝ → ℝ) (hf : Measurable f) (Mf : ℝ) (hMf : ∀ x, |f x| ≤ Mf) :
    |∫ ω, f (Y ω, Z ω) * g (T ω) ∂P - (∫ ω, f (Y ω, Z ω) ∂P) * ∫ ω, g (T ω) ∂P|
      ≤ 4 * φ m * Mf * ∫ ω, |g (T ω)| ∂P
        + 2 * φ m * Mg * ∫ x, |f x| ∂((P.map Y).prod (P.map Z)) :=
  PoissonDepTrials.MixInv.lemma_4_3 P X hXm φ hφ m hm a b c d e e' ha hbc hde Y T Z hY hT hZ g hg Mg hMg f hf Mf hMf
