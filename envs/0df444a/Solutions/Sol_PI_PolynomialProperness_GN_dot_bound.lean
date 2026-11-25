-- Prove2me | solution 1 for PI.PolynomialProperness.GN.dot_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:04:15.379539+00:00
-- url     : https://prove2.me/submissions/06dea4eb-8c2a-40f7-aea5-8392dca7cf07

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.GN
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt
namespace PI.PolynomialProperness.GN
theorem _root_.solution {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (v w : ι → ℂ) {E : ℝ}
    (hE : ∀ i j, ‖M i j‖ ≤ E) :
    ‖star w ⬝ᵥ (M *ᵥ v)‖ ≤ (∑ i, ‖w i‖) * (∑ j, ‖v j‖) * E := by
  simp only [dotProduct, mulVec, Pi.star_apply]
  calc ‖∑ i, star (w i) * ∑ j, M i j * v j‖ ≤ ∑ i, ‖w i‖ * ∑ j, ‖v j‖ * E := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [norm_mul, norm_star]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_left (hE i j) (norm_nonneg _)
    _ = (∑ i, ‖w i‖) * (∑ j, ‖v j‖) * E := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]; ring
end PI.PolynomialProperness.GN
