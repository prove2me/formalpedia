-- Prove2me | solution 1 for PI.WeylForKWork.eMi_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:49:44.763803+00:00
-- url     : https://prove2.me/submissions/7cfc1cfd-3b73-4ff7-a967-620af2a01f13

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
theorem _root_.solution (ε : Fin N → Bool) (i j : Fin (nMi ε)) : eMi ε i = eMi ε j ↔ i = j := by
  show blk ε (Sum.inr i) = blk ε (Sum.inr j) ↔ i = j
  rw [(blk ε).injective.eq_iff, Sum.inr.injEq]
end PI.WeylForKWork
