-- Prove2me | solution 1 for PoissonDepTrials.MixSqrt.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:02:43.59398+00:00
-- url     : https://prove2.me/submissions/bd3c42a4-8a4d-4013-8479-d9673e64bf49

import Mathlib
import Definitions.Def_PoissonDepTrials_MixSqrt_Setting
import Theorems.Thm_PoissonDepTrials_MixInv_lemma_4_2


open MeasureTheory ProbabilityTheory
open PoissonDepTrials.MixSqrt


/-- Chen (1975), Lemma 4.2, p. 539, (4.4). Let `X_1, X_2, …` be a real sequence satisfying (4.1),
`Y` an `ℳ_{1k}`-measurable `ℝ^r`-valued and `Z` an `ℳ_{k+m,∞}`-measurable `ℝ^s`-valued random
vector, and `f` bounded by `M` and Borel. Then almost surely
`|E^Y f(Y, Z) − E^Y f(Y, Z')| ≤ 2‖f‖φ(m)`, where `E^Y f(Y, Z') = ∫ f(Y, z) dP_Z(z)` for an independent
copy `Z'` of `Z`. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ i, Measurable (X i)) (φ : ℕ → ℝ) (hφ : IbragimovMixing P X φ)
    (r s k m : ℕ) (hm : 1 ≤ m)
    (Y : Ω → (Fin r → ℝ)) (hY : Measurable[sigmaIcc X 1 k] Y)
    (Z : Ω → (Fin s → ℝ)) (hZ : Measurable[sigmaIci X (k + m)] Z)
    (f : (Fin r → ℝ) × (Fin s → ℝ) → ℝ) (hf : Measurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M) :
    ∀ᵐ ω ∂P, |(P[fun ω => f (Y ω, Z ω) | MeasurableSpace.comap Y inferInstance]) ω
      - ∫ z, f (Y ω, z) ∂(P.map Z)| ≤ 2 * M * φ m :=
  PoissonDepTrials.MixInv.lemma_4_2 P X hXm φ hφ r s k m hm Y hY Z hZ f hf M hM
