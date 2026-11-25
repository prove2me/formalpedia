-- Prove2me | solution 1 for PI.WFJM.Shape.getD_lneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:32.731005+00:00
-- url     : https://prove2.me/submissions/9dd72e5e-227b-4daa-aded-c1fa61f0c3b3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeFromFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM PI.WFJM.Shape
open PI.FJM
variable {n : ℕ}
namespace PI.WFJM.Shape
theorem _root_.solution {m : ℕ} (α : Fin m → ℕ) (t : ℕ) (ht : t < m) :
    (lneg α).getD t 0 = -(α ⟨m - 1 - t, by omega⟩ : ℤ) := by
  unfold lneg
  rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by simpa using ht)]
  simp [show m - 1 - t < m by omega]
end PI.WFJM.Shape
