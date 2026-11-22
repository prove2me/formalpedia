-- Prove2me | solution 1 for PI.HookSteps.Cap.xw_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:01:40.128501+00:00
-- url     : https://prove2.me/submissions/15dde2fb-2394-4444-bff9-2fe0d427cde9

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
theorem _root_.solution (x : I → S → 𝒰) {k : ℕ} (r : Fin (k + 1) → I) (s : Fin (k + 1) → S) :
    xw x r s = x (r 0) (s 0) * xw x (fun i => r i.succ) (fun i => s i.succ) := by
  unfold xw
  rw [List.ofFn_succ, List.prod_cons]
end PI.HookSteps.Cap
