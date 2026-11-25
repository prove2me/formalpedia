-- Prove2me | solution 1 for PI.WeylForKWork.block_diagonal_torus_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:12:17.960439+00:00
-- url     : https://prove2.me/submissions/f989e00f-1543-4a7b-8362-4254aed3e100

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
namespace PI.WeylForKWork
theorem _root_.solution : BlockDiag := by
  intro N ε
  refine ⟨fun f => ?_, fun θ => ?_, fun θ => ?_⟩
  · rw [← Equiv.sum_comp (blk ε), Fintype.sum_sum_type]
    rfl
  · refine ⟨fun a => Sum.elim θ 0 ((blk ε).symm a), fun i => by simp [ePl], fun j => by simp [eMi], ?_⟩
    unfold iPl
    rw [← Matrix.diagonal_one, Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]
    congr 1
    funext a
    rcases h : (blk ε).symm a with i | j <;> simp [h]
  · refine ⟨fun a => Sum.elim 0 θ ((blk ε).symm a), fun i => by simp [ePl], fun j => by simp [eMi], ?_⟩
    unfold iMi
    rw [← Matrix.diagonal_one, Matrix.fromBlocks_diagonal, Matrix.submatrix_diagonal_equiv]
    congr 1
    funext a
    rcases h : (blk ε).symm a with i | j <;> simp [h]
end PI.WeylForKWork
