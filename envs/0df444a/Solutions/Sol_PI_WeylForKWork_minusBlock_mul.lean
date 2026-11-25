-- Prove2me | solution 1 for PI.WeylForKWork.minusBlock_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:15:38.369411+00:00
-- url     : https://prove2.me/submissions/d908e5ad-2474-431a-a633-734f79f032f3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Blocks
import Theorems.Thm_PI_WeylForKWork_minusBlock_eq_blockReindex
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
theorem _root_.solution (ε : Fin N → Bool) (a b : Matrix (Fin (nMi ε)) (Fin (nMi ε)) ℂ) :
    iMi ε (a * b) = iMi ε a * iMi ε b := by
  rw [minusBlock_eq_blockReindex, minusBlock_eq_blockReindex, minusBlock_eq_blockReindex, ← map_mul, Matrix.fromBlocks_multiply]
  simp
end PI.WeylForKWork
