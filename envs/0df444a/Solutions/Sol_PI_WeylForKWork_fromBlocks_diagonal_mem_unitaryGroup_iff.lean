-- Prove2me | solution 1 for PI.WeylForKWork.fromBlocks_diagonal_mem_unitaryGroup_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:18:09.028692+00:00
-- url     : https://prove2.me/submissions/f0bef6f4-c4b7-4bbc-96bf-1172edfdf8f9

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
    fromBlocks A 0 0 D ∈ unitaryGroup (m ⊕ n) ℂ ↔ A ∈ unitaryGroup m ℂ ∧ D ∈ unitaryGroup n ℂ := by
  have h1 : (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) = fromBlocks 1 0 0 1 := Matrix.fromBlocks_one.symm
  simp only [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, h1, Matrix.fromBlocks_inj]
  simp
end PI.WeylForKWork
