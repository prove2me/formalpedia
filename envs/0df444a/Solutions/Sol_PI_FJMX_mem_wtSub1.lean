-- Prove2me | solution 1 for PI.FJMX.mem_wtSub1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:44:56.863346+00:00
-- url     : https://prove2.me/submissions/2f55a6dc-9c8e-4459-b135-54f69dfbba11

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistPad
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_IsDiagonalBlockIndexRightOfPositiveRoot
import Theorems.Thm_PI_FJMX_leftAction_diagonal_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial FockH1Action PI.FJM
noncomputable section
open PI PI.FJMX
variable {p q r s : ℕ}
namespace PI.FJMX
theorem _root_.solution (hW : FormWt1) (P : Pol p q r s) (μ : Ix p q → ℚ)
    (h : ∀ x, ∃ W : ℤ, (W : ℚ) + sh1 p q r s x = μ x ∧ ∀ m, coeff m P ≠ 0 → wt1 m x = W) :
    P ∈ wtSub (fockAct1 p q r s) μ := by
  simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x
  obtain ⟨W, hWx, hm⟩ := h x
  rw [LinearMap.sub_apply, leftAction_diagonal_of hW P x W hm, hWx]
  simp
end PI.FJMX
