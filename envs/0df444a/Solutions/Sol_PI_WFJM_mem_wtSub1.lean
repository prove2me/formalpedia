-- Prove2me | solution 1 for PI.WFJM.mem_wtSub1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:34:52.934787+00:00
-- url     : https://prove2.me/submissions/ad1ea1a2-148d-4752-9259-7a74f65821ea

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_coeff_fockAct1_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM
open MvPolynomial
open PI.FJM
variable {p q r s : ℕ}
open MvPolynomial
namespace PI.WFJM
theorem _root_.solution (μ : Ix p q → ℚ) (P : Pol p q r s) :
    P ∈ wtSub (fockAct1 p q r s) μ ↔ ∀ m ∈ P.support, ∀ a, (wt1 m a : ℚ) + sh1 p q r s a = μ a := by
  simp only [FockH1Action.wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  constructor
  · intro h m hm a
    have hc := congrArg (coeff m) (h a)
    rw [coeff_fockAct1_diag, coeff_smul, smul_eq_mul] at hc
    exact_mod_cast mul_right_cancel₀ (MvPolynomial.mem_support_iff.mp hm) hc
  · intro h a
    ext m
    rw [coeff_fockAct1_diag, coeff_smul, smul_eq_mul]
    by_cases hm : m ∈ P.support
    · rw [h m hm a]
    · have h0 : coeff m P = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
      rw [h0, mul_zero, mul_zero]
end PI.WFJM
