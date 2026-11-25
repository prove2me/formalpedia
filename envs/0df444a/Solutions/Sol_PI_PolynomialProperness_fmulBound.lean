-- Prove2me | solution 1 for PI.PolynomialProperness.fmulBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:37:28.882181+00:00
-- url     : https://prove2.me/submissions/334241f6-9f94-4ecd-8cbe-9793830fc4bc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Theorems.Thm_PI_PolynomialProperness_nsq_eq_norm
import Theorems.Thm_PI_PolynomialProperness_fmul_apply
import Theorems.Thm_PI_PolynomialProperness_GN_entry_le_mx


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness
namespace PI.PolynomialProperness
theorem _root_.solution : FmulBound := by
  intro k r z
  refine ⟨∑ i, (∑ a, ‖fvec k r z a i‖) ^ 2, fun c b => ?_⟩
  have h1 : ∀ i, ‖fmul k r z c b i‖ ≤ mx c * ∑ a, ‖fvec k r z a i‖ := by
    intro i
    rw [fmul_apply, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (GN.entry_le_mx c a b) (norm_nonneg _)
  rw [nsq_eq_norm]
  calc ∑ i, ‖fmul k r z c b i‖ ^ 2 ≤ ∑ i, (mx c * ∑ a, ‖fvec k r z a i‖) ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h1 i) 2
    _ = (∑ i, (∑ a, ‖fvec k r z a i‖) ^ 2) * mx c ^ 2 := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
end PI.PolynomialProperness
