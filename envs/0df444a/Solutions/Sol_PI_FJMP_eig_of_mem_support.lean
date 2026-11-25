-- Prove2me | solution 1 for PI.FJMP.eig_of_mem_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:46:14.727798+00:00
-- url     : https://prove2.me/submissions/0633b4be-2aac-414d-9c65-37b94c36d0ee

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_MemLeftHighestWeightOfIsMinimalJointVector
import Theorems.Thm_PI_FJMP_coeff_diag

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
    (hT : ∀ m, T (monomial m 1) = w m • monomial m 1) (P : MvPolynomial σ ℂ) (c : ℂ) (hP : T P = c • P)
    (e : σ →₀ ℕ) (he : e ∈ P.support) : w e = c := by
  have h1 := coeff_diag T w hT P e
  rw [hP] at h1
  simp only [coeff_smul, smul_eq_mul] at h1
  exact (mul_right_cancel₀ (mem_support_iff.mp he) h1).symm
end PI.FJMP
