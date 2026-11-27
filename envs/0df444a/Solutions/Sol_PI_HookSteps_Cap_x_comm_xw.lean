-- Prove2me | solution 1 for PI.HookSteps.Cap.x_comm_xw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:14:22.203611+00:00
-- url     : https://prove2.me/submissions/e50a48a9-48fb-4a3e-a1f2-7c694dd5f62f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliAbs
import Theorems.Thm_PI_HookSteps_Cap_xw_succ
import Theorems.Thm_PI_HookSteps_Cap_xw_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.HookSteps PI.HookSteps.Cap
open Finset
variable {𝒰 : Type} [Ring 𝒰] {I S : Type} [DecidableEq I] [Fintype S] [DecidableEq S]
namespace PI.HookSteps.Cap
theorem _root_.solution (x : I → S → 𝒰) (hxx : ∀ a s b t, x a s * x b t = x b t * x a s)
    {k : ℕ} (a : I) (t : S) (r : Fin k → I) (s : Fin k → S) :
    x a t * xw x r s = xw x r s * x a t := by
  induction k with
  | zero => rw [xw_zero, mul_one, one_mul]
  | succ k ih =>
    rw [xw_succ, ← mul_assoc, hxx a t (r 0) (s 0), mul_assoc (x (r 0) (s 0)) (x a t), ih,
      ← mul_assoc]
end PI.HookSteps.Cap
