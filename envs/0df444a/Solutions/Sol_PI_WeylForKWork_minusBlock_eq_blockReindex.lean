-- Prove2me | solution 1 for PI.WeylForKWork.minusBlock_eq_blockReindex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:37.132804+00:00
-- url     : https://prove2.me/submissions/ea7c6e70-4a7d-44e2-bc51-afa81c200cd0

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
theorem _root_.solution (ε : Fin N → Bool) (h : Matrix (Fin (nMi ε)) (Fin (nMi ε)) ℂ) :
    iMi ε h = blR ε (fromBlocks 1 0 0 h) := rfl
end PI.WeylForKWork
