-- Prove2me | solution 1 for PI.HookSteps.Qn_last_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:45:05.991743+00:00
-- url     : https://prove2.me/submissions/8cad2c12-ec19-4a64-b480-5afdbd555bbe

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_HookNorm
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
theorem _root_.solution (n : ℕ) (ν : Fin (n + 1) → ℕ) (h : ν (Fin.last n) = 0) :
    Qn ν = (∏ i : Fin n, (ν (Fin.castSucc i) + (n - i))) * Qn (fun i : Fin n => ν (Fin.castSucc i)) := by
  unfold Qn
  rw [Fin.prod_univ_castSucc, h, ← Finset.prod_mul_distrib]
  have hl : (0 + (n + 1 - 1 - ((Fin.last n : Fin (n + 1)) : ℕ))).factorial = 1 := by
    simp
  rw [hl, mul_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi := i.isLt
  simp only [Fin.coe_castSucc]
  have e : ν (Fin.castSucc i) + (n + 1 - 1 - (i : ℕ)) = (ν (Fin.castSucc i) + (n - 1 - (i : ℕ))) + 1 := by omega
  rw [e, Nat.factorial_succ]
  congr 1
  omega
end PI.HookSteps
