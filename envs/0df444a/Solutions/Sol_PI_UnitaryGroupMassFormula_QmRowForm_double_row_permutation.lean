-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmRowForm.double_row_permutation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:03:39.06333+00:00
-- url     : https://prove2.me/submissions/2c7b6d35-c1c5-41c5-bb59-accaaf9225fd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowFormPermutationSplit_PermutedRowProductSplit
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmRowForm_perm_swap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmRowForm
namespace PI.UnitaryGroupMassFormula.QmRowForm
theorem _root_.solution : DblPerm := by
  intro A _ _ n t E hE a b x π
  rcases t with _ | m
  · have hx : x ∘ π = x := funext fun k => k.elim0
    rw [hx]
  · have hπ : π ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top π
    revert x
    induction hπ using Submonoid.closure_induction with
    | mem π h =>
      obtain ⟨i, rfl⟩ := h
      intro x
      exact perm_swap E hE a b x i
    | one =>
      intro x
      rfl
    | mul π1 π2 _ _ ih1 ih2 =>
      intro x
      have hc : x ∘ ⇑(π1 * π2) = (x ∘ ⇑π1) ∘ ⇑π2 := rfl
      rw [hc, ih2, ih1]
end PI.UnitaryGroupMassFormula.QmRowForm
