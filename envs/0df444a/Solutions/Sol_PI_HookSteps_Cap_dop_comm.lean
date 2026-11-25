-- Prove2me | solution 1 for PI.HookSteps.Cap.dop_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:42:24.811126+00:00
-- url     : https://prove2.me/submissions/7db610a8-a17e-4480-b8fd-7a9eff6df7ad

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliOps
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open PI PI.HookSteps PI.HookSteps.Cap
open MvPolynomial Finset
namespace PI.HookSteps.Cap
theorem _root_.solution (N : ℕ) (b t b' t' : Fin N) : Commute (dop N b t) (dop N b' t') := by
  have h : ⁅(pderiv (b, t) : Derivation ℚ (MvPolynomial (Fin N × Fin N) ℚ) (MvPolynomial (Fin N × Fin N) ℚ)),
      (pderiv (b', t') : Derivation ℚ (MvPolynomial (Fin N × Fin N) ℚ) (MvPolynomial (Fin N × Fin N) ℚ))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  apply LinearMap.ext; intro f
  have := congrArg (fun D : Derivation ℚ (MvPolynomial (Fin N × Fin N) ℚ)
    (MvPolynomial (Fin N × Fin N) ℚ) => D f) h
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at this
  simpa [dop, Module.End.mul_apply, sub_eq_zero] using this
end PI.HookSteps.Cap
