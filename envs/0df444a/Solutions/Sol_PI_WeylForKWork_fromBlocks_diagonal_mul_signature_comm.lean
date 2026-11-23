-- Prove2me | solution 1 for PI.WeylForKWork.fromBlocks_diagonal_mul_signature_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:31.876806+00:00
-- url     : https://prove2.me/submissions/ab04908e-dea3-4620-be2f-ce39fe60d293

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Blocks
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
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
namespace PI.WeylForKWork
theorem _root_.solution (A : Matrix m m ℂ) (D : Matrix n n ℂ) :
    fromBlocks A 0 0 D * fromBlocks 1 0 0 (-1) = fromBlocks 1 0 0 (-1) * fromBlocks A 0 0 D := by
  simp [Matrix.fromBlocks_multiply]
end PI.WeylForKWork
