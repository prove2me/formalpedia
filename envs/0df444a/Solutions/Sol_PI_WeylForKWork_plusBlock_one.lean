-- Prove2me | solution 1 for PI.WeylForKWork.plusBlock_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:31:03.155675+00:00
-- url     : https://prove2.me/submissions/6af67585-a4b9-4401-b299-999ba8a7c9fe

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Blocks
import Theorems.Thm_PI_WeylForKWork_plusBlock_eq_blockReindex

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
theorem _root_.solution (ε : Fin N → Bool) : iPl ε 1 = 1 := by
  rw [plusBlock_eq_blockReindex, Matrix.fromBlocks_one, map_one]
end PI.WeylForKWork
