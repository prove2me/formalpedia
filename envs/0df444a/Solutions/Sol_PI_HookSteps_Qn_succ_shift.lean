-- Prove2me | solution 1 for PI.HookSteps.Qn_succ_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:57:00.198985+00:00
-- url     : https://prove2.me/submissions/0744f8de-aeeb-47a6-9d5a-9189cfbd0e86

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_HookNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookSteps
namespace PI.HookSteps
theorem _root_.solution {N : ℕ} (μ : Fin N → ℕ) :
    Qn (fun i => μ i + 1) = (∏ i : Fin N, (μ i + N - i)) * Qn μ := by
  unfold Qn
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi := i.isLt
  have e : μ i + 1 + (N - 1 - (i : ℕ)) = (μ i + (N - 1 - (i : ℕ))) + 1 := by omega
  have e2 : μ i + N - (i : ℕ) = μ i + (N - 1 - (i : ℕ)) + 1 := by omega
  rw [e, e2, Nat.factorial_succ]
end PI.HookSteps
