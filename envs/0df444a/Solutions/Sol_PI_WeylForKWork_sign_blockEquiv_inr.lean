-- Prove2me | solution 1 for PI.WeylForKWork.sign_blockEquiv_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:14:27.67235+00:00
-- url     : https://prove2.me/submissions/2eedf0f1-7c93-4f52-81ef-74573305960a

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
theorem _root_.solution (ε : Fin N → Bool) (j : Fin (nMi ε)) : ε (blk ε (Sum.inr j)) = false := by
  exact Bool.eq_false_iff.2 (Subtype.prop (p := fun a => ¬ ε a = true) _)
end PI.WeylForKWork
