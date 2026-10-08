-- Prove2me | solution 1 for WassersteinDRO.Regularization.empirical_risk_computation
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-05T11:46:35.488814+00:00
-- url     : https://prove2.me/submissions/832b70ad-62a2-4f9d-ae9a-03d7aa88424a

import Mathlib
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution
import Definitions.Def_WassersteinDRO_Regularization_nominalRisk

set_option autoImplicit false

open MeasureTheory
open WassersteinDRO.Regularization

theorem solution {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E) (ℓ : E → ℝ) (hm : Measurable ℓ) :
    nominalRisk (empiricalDistribution ξhat) ℓ =
      (1 / (N : ℝ)) * Finset.sum Finset.univ (fun i => ℓ (ξhat i)) := by
  have hInt : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      Integrable ℓ (Measure.dirac (ξhat i)) :=
    fun i _ => integrable_dirac (by simp)
  have h1 : ((N : ENNReal)⁻¹).toReal = 1 / (N : ℝ) := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
  unfold nominalRisk empiricalDistribution
  rw [integral_smul_measure, integral_finsetSum_measure hInt, h1, smul_eq_mul]
  simp only [integral_dirac]

theorem WassersteinDRO.Regularization.empirical_risk_computation {E : Type*}
    [MeasurableSpace E] [MeasurableSingletonClass E]
    {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E) (ℓ : E → ℝ) (hm : Measurable ℓ) :
    nominalRisk (empiricalDistribution ξhat) ℓ =
      (1 / (N : ℝ)) * Finset.sum Finset.univ (fun i => ℓ (ξhat i)) :=
  solution hN ξhat ℓ hm
