-- Prove2me | solution 1 for PI.WeylForKWork.sign_blockEquiv_inl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:15:48.857615+00:00
-- url     : https://prove2.me/submissions/3b2c663a-46e7-4eda-b8b5-e54f960c66c2

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
theorem _root_.solution (ε : Fin N → Bool) (i : Fin (nPl ε)) : ε (blk ε (Sum.inl i)) = true := by
  exact Subtype.prop (p := fun a => ε a = true) _
end PI.WeylForKWork
