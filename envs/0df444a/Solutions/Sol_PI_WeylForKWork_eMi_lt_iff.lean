-- Prove2me | solution 1 for PI.WeylForKWork.eMi_lt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:34:41.327605+00:00
-- url     : https://prove2.me/submissions/137e08fc-f737-4703-a0af-8af58b480449

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Formula
import Theorems.Thm_PI_WeylForKWork_eMi_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix Finset
variable {N : ℕ}
namespace PI.WeylForKWork
theorem _root_.solution (ε : Fin N → Bool) (i j : Fin (nMi ε)) : eMi ε i < eMi ε j ↔ i < j := by
  rw [eMi_eq, eMi_eq]
  exact ((sMinus ε).orderEmbOfFin rfl).lt_iff_lt
end PI.WeylForKWork
