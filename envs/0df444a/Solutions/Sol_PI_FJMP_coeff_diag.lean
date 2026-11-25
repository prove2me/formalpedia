-- Prove2me | solution 1 for PI.FJMP.coeff_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:38:38.085359+00:00
-- url     : https://prove2.me/submissions/480f97ed-cd00-4e40-b493-4221ff7e9dee

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FJMP
open PI.FJM
variable {σ : Type*}
namespace PI.FJMP
theorem _root_.solution (T : Module.End ℂ (MvPolynomial σ ℂ)) (w : (σ →₀ ℕ) → ℂ)
    (hT : ∀ m, T (monomial m 1) = w m • monomial m 1) (P : MvPolynomial σ ℂ) (e : σ →₀ ℕ) :
    coeff e (T P) = w e * coeff e P := by
  classical
  refine MvPolynomial.induction_on' P (fun m a => ?_) (fun p q hp hq => ?_)
  · have h1 : monomial m a = a • monomial m (1 : ℂ) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [h1, map_smul, hT, smul_smul]
    simp only [coeff_smul, coeff_monomial, smul_eq_mul]
    by_cases h : m = e
    · subst h
      rw [if_pos rfl]
      ring
    · rw [if_neg h]
      ring
  · rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]
end PI.FJMP
