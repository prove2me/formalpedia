-- Prove2me | solution 1 for PI.HookSteps.Cap.dw_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:43:41.406602+00:00
-- url     : https://prove2.me/submissions/4bda56f5-86ca-4bd5-9594-9571363ce549

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
theorem _root_.solution (d : I → S → 𝒰) {k : ℕ} (g : Fin (k + 1) → I) (s : Fin (k + 1) → S) :
    dw d g s = d (g 0) (s 0) * dw d (fun i => g i.succ) (fun i => s i.succ) := by
  unfold dw
  rw [List.ofFn_succ, List.prod_cons]
end PI.HookSteps.Cap
