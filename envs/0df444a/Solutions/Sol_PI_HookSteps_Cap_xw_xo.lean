-- Prove2me | solution 1 for PI.HookSteps.Cap.xw_xo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:42:38.22113+00:00
-- url     : https://prove2.me/submissions/83625f90-ce42-4d41-8746-8bbd898ed135

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliOps
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_PI_HookSteps_Cap_xw_succ
import Theorems.Thm_PI_HookSteps_Cap_xw_zero
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
theorem _root_.solution (N : ℕ) : ∀ (k : ℕ) (r s : Fin k → Fin N),
    xw (xo N) r s = Algebra.lmul ℚ (MvPolynomial (Fin N × Fin N) ℚ) (∏ j, X (r j, s j)) := by
  intro k
  induction k with
  | zero =>
    intro r s
    rw [xw_zero]
    refine LinearMap.ext fun p => ?_
    simp
  | succ k ih =>
    intro r s
    rw [xw_succ, ih, Fin.prod_univ_succ, map_mul]
    rfl
end PI.HookSteps.Cap
