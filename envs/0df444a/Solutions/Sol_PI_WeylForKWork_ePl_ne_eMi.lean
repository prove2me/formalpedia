-- Prove2me | solution 1 for PI.WeylForKWork.ePl_ne_eMi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:31.604692+00:00
-- url     : https://prove2.me/submissions/ff854e53-93e0-4bc4-b125-c495b3a70f29

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Formula

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
theorem _root_.solution (ε : Fin N → Bool) (i : Fin (nPl ε)) (j : Fin (nMi ε)) : ePl ε i ≠ eMi ε j := by
  intro h
  exact Sum.inl_ne_inr ((blk ε).injective h)
end PI.WeylForKWork
