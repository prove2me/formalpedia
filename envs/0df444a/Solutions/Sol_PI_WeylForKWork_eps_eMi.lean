-- Prove2me | solution 1 for PI.WeylForKWork.eps_eMi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:48:51.74394+00:00
-- url     : https://prove2.me/submissions/c2058c41-0363-426f-a167-b0c43ed72e66

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
theorem _root_.solution (ε : Fin N → Bool) (j : Fin (nMi ε)) : ε (eMi ε j) = false := by
  exact Bool.eq_false_iff.2 (Subtype.prop (p := fun a => ¬ ε a = true) _)
end PI.WeylForKWork
