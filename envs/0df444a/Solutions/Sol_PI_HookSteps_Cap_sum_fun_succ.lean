-- Prove2me | solution 1 for PI.HookSteps.Cap.sum_fun_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:42:35.437322+00:00
-- url     : https://prove2.me/submissions/e6d8c327-8071-4fe0-9e6b-b8624ab91850

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliAbs

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
theorem _root_.solution {M : Type} [AddCommMonoid M] {k : ℕ} (f : (Fin (k + 1) → S) → M) :
    ∑ s, f s = ∑ t : S, ∑ s : Fin k → S, f (Fin.cons t s) := by
  rw [← (Fin.consEquiv fun _ => S).sum_comp, Fintype.sum_prod_type]
  rfl
end PI.HookSteps.Cap
