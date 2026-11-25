-- Prove2me | solution 1 for PI.PolynomialProperness.nsq_mulVec_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:59:21.585824+00:00
-- url     : https://prove2.me/submissions/e2d330ac-5f89-470f-82e7-141f4df74268

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Theorems.Thm_PI_PolynomialProperness_nsq_eq_norm
import Theorems.Thm_PI_PolynomialProperness_GN_gN_sq


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
theorem _root_.solution {k r : ℕ} (g : B.Mat k r) (x : Fin (2 * r + k + 1) → ℂ) :
    nsq (g *ᵥ x) ≤ B.gN g ^ 2 * nsq x := by
  rw [GN.gN_sq]
  have h1 : ∀ i, ‖(g *ᵥ x) i‖ ^ 2 ≤ (∑ j, ‖g i j‖ ^ 2) * ∑ j, ‖x j‖ ^ 2 := by
    intro i
    have e : (g *ᵥ x) i = ∑ j, g i j * x j := rfl
    rw [e]
    have h2 : ‖∑ j, g i j * x j‖ ≤ ∑ j, ‖g i j‖ * ‖x j‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun j _ => norm_mul _ _
    calc ‖∑ j, g i j * x j‖ ^ 2 ≤ (∑ j, ‖g i j‖ * ‖x j‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ ≤ (∑ j, ‖g i j‖ ^ 2) * ∑ j, ‖x j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  rw [nsq_eq_norm, nsq_eq_norm]
  calc ∑ i, ‖(g *ᵥ x) i‖ ^ 2 ≤ ∑ i, (∑ j, ‖g i j‖ ^ 2) * ∑ j, ‖x j‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = GN.hs g * ∑ j, ‖x j‖ ^ 2 := by
        rw [← Finset.sum_mul]
        congr 1
        unfold GN.hs
        exact Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => (Complex.normSq_eq_norm_sq _).symm
end PI.PolynomialProperness
