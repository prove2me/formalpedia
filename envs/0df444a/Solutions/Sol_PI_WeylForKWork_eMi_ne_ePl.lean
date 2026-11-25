-- Prove2me | solution 1 for PI.WeylForKWork.eMi_ne_ePl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:16:53.320072+00:00
-- url     : https://prove2.me/submissions/cbed15db-27ed-4319-a771-a1b25f878ff1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Formula
import Theorems.Thm_PI_WeylForKWork_ePl_ne_eMi

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
theorem _root_.solution (ε : Fin N → Bool) (j : Fin (nMi ε)) (i : Fin (nPl ε)) : eMi ε j ≠ ePl ε i := by
  exact fun h => ePl_ne_eMi ε i j h.symm
end PI.WeylForKWork
