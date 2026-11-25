-- Prove2me | solution 1 for PI.PolynomialProperness.zhatMove
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:28:30.952722+00:00
-- url     : https://prove2.me/submissions/a6cb34f8-bdd2-4a45-b1b1-6057c062f0ca

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_UnitriangularInversePolynomialBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_NsqMulVecLe
import Theorems.Thm_PI_PolynomialProperness_herm_sum_left
import Theorems.Thm_PI_PolynomialProperness_herm_sum_right
import Theorems.Thm_PI_PolynomialProperness_mulVec_fmul
import Theorems.Thm_PI_PolynomialProperness_GN_herm_mulVec
import Theorems.Thm_PI_PolynomialProperness_GN_mul_inv


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
theorem _root_.solution : ZhatMove := by
  intro k r z z' γ σ s' v u' hσ _ hv hu
  ext a b
  have hσi : σ * σ⁻¹ = 1 := GN.mul_inv hσ
  have key : ∀ x y : Fin (2 * r + k + 1) → ℂ,
      herm (Hpk k r) ((σ⁻¹ * γ * s') *ᵥ x) y = herm (Hpk k r) ((γ * s') *ᵥ x) (σ *ᵥ y) := by
    intro x y
    rw [← GN.herm_mulVec hσ, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hσi,
      Matrix.one_mul]
  show herm (Hpk k r) ((σ⁻¹ * γ * s') *ᵥ fvec k r z' b) (fvec k r z a) = _
  rw [key, hv a, ← mulVec_mulVec, hu b, mulVec_fmul]
  unfold fmul
  rw [herm_sum_right]
  simp only [herm_sum_left]
  simp only [mul_apply, conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  simp only [Zhat]
  ring
end PI.PolynomialProperness
