-- Prove2me | solution 1 for PI.WeylForKWork.continuous_plusBlock
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:12:23.394088+00:00
-- url     : https://prove2.me/submissions/a07e8472-59c4-462c-b370-1bc97b227a02

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Blocks

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
theorem _root_.solution (ε : Fin N → Bool) : Continuous (iPl ε) := by
  unfold iPl
  exact (continuous_id.matrix_fromBlocks continuous_const continuous_const
    continuous_const).matrix_submatrix _ _
end PI.WeylForKWork
