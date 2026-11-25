-- Prove2me | solution 1 for PI.WFJM.pderiv_X_mul_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:44.548505+00:00
-- url     : https://prove2.me/submissions/11d0d4d0-6657-4e63-a4a5-38d4cfa2f987

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_X_mul_pderiv_monomial

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
namespace PI.WFJM
theorem _root_.solution {σ : Type*} (i : σ) (α : σ →₀ ℕ) (c : ℂ) :
    pderiv i (X i * monomial α c) = (((α i : ℕ) : ℂ) + 1) • monomial α c := by
  classical
  have hX : pderiv i (X i : MvPolynomial σ ℂ) = 1 := by
    first
    | exact pderiv_X_self i
    | simp [pderiv_X]
  first
  | rw [Derivation.leibniz, hX, smul_eq_mul, smul_eq_mul, X_mul_pderiv_monomial, mul_one,
      add_smul, one_smul]
  | (simp only [Derivation.leibniz, hX, smul_eq_mul, X_mul_pderiv_monomial, mul_one]; module)
end PI.WFJM
