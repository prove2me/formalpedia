-- Prove2me | solution 1 for PI.HookSteps.factorial_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:02:15.998216+00:00
-- url     : https://prove2.me/submissions/2e65e4b9-4feb-412d-92f4-f36c7d7aa4ba

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DiagonalMonomialFactorial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_ProdFactorialLe
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
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookSteps
namespace PI.HookSteps
theorem _root_.solution (a k B : ℕ) (h : a + k ≤ B) : (a + k).factorial ≤ a.factorial * B ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (by omega)
    rw [← add_assoc, Nat.factorial_succ, pow_succ]
    calc (a + k + 1) * (a + k).factorial ≤ B * (a.factorial * B ^ k) :=
          Nat.mul_le_mul (by omega) ih'
      _ = a.factorial * (B ^ k * B) := by ring
end PI.HookSteps
