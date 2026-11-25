-- Prove2me | solution 1 for PI.WeylForKWork.minusBlock_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:15:41.204631+00:00
-- url     : https://prove2.me/submissions/2b0d3c97-2814-40bb-ae7a-084ca5415bf6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Blocks
import Theorems.Thm_PI_WeylForKWork_minusBlock_eq_blockReindex

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
open PI PI.UpqRep Matrix
variable {N : ℕ}
namespace PI.WeylForKWork
theorem _root_.solution (ε : Fin N → Bool) : iMi ε 1 = 1 := by
  rw [minusBlock_eq_blockReindex, Matrix.fromBlocks_one, map_one]
end PI.WeylForKWork
