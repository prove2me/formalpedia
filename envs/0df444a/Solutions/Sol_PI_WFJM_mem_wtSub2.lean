-- Prove2me | solution 1 for PI.WFJM.mem_wtSub2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:33:09.143935+00:00
-- url     : https://prove2.me/submissions/f06d6a44-6b7b-4120-90bf-58f775d58726

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_coeff_fockAct2_diag

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
theorem _root_.solution (μ : Ix r s → ℚ) (P : Pol p q r s) :
    P ∈ wtSub (fockAct2 p q r s) μ ↔ ∀ m ∈ P.support, ∀ c, (wt2 m c : ℚ) + sh2 p q r s c = μ c := by
  simp only [FockH1Action.wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  constructor
  · intro h m hm c
    have hc := congrArg (coeff m) (h c)
    rw [coeff_fockAct2_diag, coeff_smul, smul_eq_mul] at hc
    exact_mod_cast mul_right_cancel₀ (MvPolynomial.mem_support_iff.mp hm) hc
  · intro h c
    ext m
    rw [coeff_fockAct2_diag, coeff_smul, smul_eq_mul]
    by_cases hm : m ∈ P.support
    · rw [h m hm c]
    · have h0 : coeff m P = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
      rw [h0, mul_zero, mul_zero]
end PI.WFJM
