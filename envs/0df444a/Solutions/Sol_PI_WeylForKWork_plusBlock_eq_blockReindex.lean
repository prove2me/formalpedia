-- Prove2me | solution 1 for PI.WeylForKWork.plusBlock_eq_blockReindex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:41.523501+00:00
-- url     : https://prove2.me/submissions/8aab7e34-6fb6-45af-889f-a6f44466badc

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
theorem _root_.solution (ε : Fin N → Bool) (h : Matrix (Fin (nPl ε)) (Fin (nPl ε)) ℂ) :
    iPl ε h = blR ε (fromBlocks h 0 0 1) := rfl
end PI.WeylForKWork
