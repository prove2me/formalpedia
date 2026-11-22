-- Prove2me | solution 1 for PI.WeylForKWork.ePl_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:50:51.644029+00:00
-- url     : https://prove2.me/submissions/19ecdb1e-8709-43ec-8b7a-cb9341ff9461

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
theorem _root_.solution (ε : Fin N → Bool) (i j : Fin (nPl ε)) : ePl ε i = ePl ε j ↔ i = j := by
  show blk ε (Sum.inl i) = blk ε (Sum.inl j) ↔ i = j
  rw [(blk ε).injective.eq_iff, Sum.inl.injEq]
end PI.WeylForKWork
