-- Prove2me | solution 1 for PI.WeylForKWork.signatureMatrix_eq_blockReindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:29:44.540471+00:00
-- url     : https://prove2.me/submissions/99f102f2-1715-4bec-9c50-7e26a75973a4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Blocks
import Theorems.Thm_PI_WeylForKWork_blR_apply
import Theorems.Thm_PI_WeylForKWork_sign_blockEquiv_inl
import Theorems.Thm_PI_WeylForKWork_sign_blockEquiv_inr
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
theorem _root_.solution (ε : Fin N → Bool) : Jm ε = blR ε (fromBlocks 1 0 0 (-1)) := by
  rw [blR_apply]
  ext a c
  obtain ⟨x, rfl⟩ := (blk ε).surjective a
  obtain ⟨y, rfl⟩ := (blk ε).surjective c
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, Jm, Matrix.diagonal_apply,
    (blk ε).injective.eq_iff]
  rcases x with i | j <;> rcases y with i' | j'
  · by_cases h : i = i' <;> simp [h, Matrix.one_apply, sign_blockEquiv_inl]
  · simp
  · simp
  · by_cases h : j = j' <;> simp [h, Matrix.one_apply, sign_blockEquiv_inr]
end PI.WeylForKWork
