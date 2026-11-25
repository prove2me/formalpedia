-- Prove2me | solution 1 for PI.WeylForKWork.plusBlock_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:15:43.775854+00:00
-- url     : https://prove2.me/submissions/599a9d4b-0bac-436b-a004-8cf5fe80e68c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Blocks
import Theorems.Thm_PI_WeylForKWork_plusBlock_eq_blockReindex
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix
variable {N : ℕ}
namespace PI.WeylForKWork
theorem _root_.solution (ε : Fin N → Bool) (a b : Matrix (Fin (nPl ε)) (Fin (nPl ε)) ℂ) :
    iPl ε (a * b) = iPl ε a * iPl ε b := by
  rw [plusBlock_eq_blockReindex, plusBlock_eq_blockReindex, plusBlock_eq_blockReindex, ← map_mul, Matrix.fromBlocks_multiply]
  simp
end PI.WeylForKWork
