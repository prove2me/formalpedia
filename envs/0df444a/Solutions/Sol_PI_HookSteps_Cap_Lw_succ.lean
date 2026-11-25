-- Prove2me | solution 1 for PI.HookSteps.Cap.Lw_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:06:47.418548+00:00
-- url     : https://prove2.me/submissions/b3706991-6001-4287-86ee-3a7f68f6991a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_CapelliMain
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
open Finset
variable {𝒰 : Type} [Ring 𝒰] {I S : Type} [DecidableEq I] [Fintype S] [DecidableEq S]
namespace PI.HookSteps.Cap
theorem _root_.solution (x d : I → S → 𝒰) {k : ℕ} (w g : Fin (k + 1) → I) :
    Lw x d w g = (Eop x d (w 0) (g 0) + if w 0 = g 0 then (k : 𝒰) else 0) *
      Lw x d (fun i => w i.succ) (fun i => g i.succ) := by
  unfold Lw
  rw [List.ofFn_succ, List.prod_cons]
  congr 1
  · simp
  · congr 2
    funext j
    split_ifs
    · push_cast [Fin.val_succ]
      abel
    · rfl
end PI.HookSteps.Cap
